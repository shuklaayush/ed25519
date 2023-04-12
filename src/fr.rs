//! This module provides an implementation of the Ed25519 scalar field $\mathbb{F}_r$
//! where `r = 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed`

use core::convert::TryInto;
use core::fmt;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use ff::{Field, PrimeField};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

#[cfg(feature = "bits")]
use ff::{FieldBits, PrimeFieldBits};

use crate::util::{adc, mac, sbb};

/// Represents an element of the scalar field $\mathbb{F}_r$ of the Ed25519 elliptic
/// curve construction.
// The internal representation of this type is four 64-bit unsigned
// integers in little-endian order. Elements of Fr are always in
// Montgomery form; i.e., Fr(a) = aR mod r, with R = 2^256.
#[derive(Clone, Copy, Eq)]
pub struct Fr(pub(crate) [u64; 4]);

impl fmt::Debug for Fr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tmp = self.to_bytes();
        write!(f, "0x")?;
        for &b in tmp.iter().rev() {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

impl fmt::Display for Fr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl From<u64> for Fr {
    fn from(val: u64) -> Fr {
        Fr([val, 0, 0, 0]) * R2
    }
}

impl ConstantTimeEq for Fr {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0[0].ct_eq(&other.0[0])
            & self.0[1].ct_eq(&other.0[1])
            & self.0[2].ct_eq(&other.0[2])
            & self.0[3].ct_eq(&other.0[3])
    }
}

impl PartialEq for Fr {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        bool::from(self.ct_eq(other))
    }
}

impl ConditionallySelectable for Fr {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Fr([
            u64::conditional_select(&a.0[0], &b.0[0], choice),
            u64::conditional_select(&a.0[1], &b.0[1], choice),
            u64::conditional_select(&a.0[2], &b.0[2], choice),
            u64::conditional_select(&a.0[3], &b.0[3], choice),
        ])
    }
}

/// Constant representing the modulus
/// r = 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed
pub const MODULUS: Fr = Fr([
    0x5812_631a_5cf5_d3ed,
    0x14de_f9de_a2f7_9cd6,
    0x0000_0000_0000_0000,
    0x1000_0000_0000_0000,
]);

/// The modulus as u32 limbs.
#[cfg(not(target_pointer_width = "64"))]
const MODULUS_LIMBS_32: [u32; 8] = [
    0x5cf5_d3ed,
    0x5812_631a,
    0xa2f7_9cd6,
    0x14de_f9de,
    0x0000_0000,
    0x0000_0000,
    0x0000_0000,
    0x1000_0000,
];

// The number of bits needed to represent the modulus.
const MODULUS_BITS: u32 = 253;

// TODO
// GENERATOR = 6 (multiplicative generator of r-1 order, that is also quadratic nonresidue)
const GENERATOR: Fr = Fr([
    0x720b_1b19_d49e_a8f1,
    0xbf4a_a361_01f1_3a58,
    0x5fa8_cc96_8193_ccbb,
    0x0e70_cbdc_7dcc_f3ac,
]);

// TODO
// 2^S * t = MODULUS - 1 with t odd
const S: u32 = 1;

// TODO
// 2^S root of unity computed by GENERATOR^t
const ROOT_OF_UNITY: Fr = Fr([
    0xaa9f_02ab_1d61_24de,
    0xb352_4a64_6611_2932,
    0x7342_2612_15ac_260b,
    0x04d6_b87b_1da2_59e2,
]);

/// sqrt(-1) mod r = 2^((r - 1) / 4) mod r
const SQRT_MINUS_ONE: Fr = Fr::from_raw([
    0xbe8775dfebbe07d4,
    0x0ef0565342ce83fe,
    0x7d3d6d60abc1c27a,
    0x094a7310e07981e7,
]);

impl<'a> Neg for &'a Fr {
    type Output = Fr;

    #[inline]
    fn neg(self) -> Fr {
        self.neg()
    }
}

impl Neg for Fr {
    type Output = Fr;

    #[inline]
    fn neg(self) -> Fr {
        -&self
    }
}

impl<'a, 'b> Sub<&'b Fr> for &'a Fr {
    type Output = Fr;

    #[inline]
    fn sub(self, rhs: &'b Fr) -> Fr {
        self.sub(rhs)
    }
}

impl<'a, 'b> Add<&'b Fr> for &'a Fr {
    type Output = Fr;

    #[inline]
    fn add(self, rhs: &'b Fr) -> Fr {
        self.add(rhs)
    }
}

impl<'a, 'b> Mul<&'b Fr> for &'a Fr {
    type Output = Fr;

    #[inline]
    fn mul(self, rhs: &'b Fr) -> Fr {
        // Schoolbook multiplication

        self.mul(rhs)
    }
}

impl_binops_additive!(Fr, Fr);
impl_binops_multiplicative!(Fr, Fr);

/// INV = -(r^{-1} mod 2^64) mod 2^64
const INV: u64 = 0xd2b5_1da3_1254_7e1b;

/// R = 2^256 mod r
const R: Fr = Fr([
    0xd6ec_3174_8d98_951d,
    0xc6ef_5bf4_737d_cf70,
    0xffff_ffff_ffff_fffe,
    0x0fff_ffff_ffff_ffff,
]);

/// R^2 = 2^512 mod r
const R2: Fr = Fr([
    0xa406_11e3_449c_0f01,
    0xd00e_1ba7_6885_9347,
    0xceec_73d2_17f5_be65,
    0x0399_411b_7c30_9a3d,
]);

/// R^3 = 2^768 mod r
const R3: Fr = Fr([
    0x2a9e_4968_7b83_a2db,
    0x2783_24e6_aef7_f3ec,
    0x8065_dc6c_04ec_5b65,
    0x0e53_0b77_3599_cec7,
]);

impl Default for Fr {
    fn default() -> Self {
        Self::zero()
    }
}

impl Fr {
    /// Returns zero, the additive identity.
    #[inline]
    pub const fn zero() -> Fr {
        Fr([0, 0, 0, 0])
    }

    /// Returns one, the multiplicative identity.
    #[inline]
    pub const fn one() -> Fr {
        R
    }

    /// Doubles this field element.
    #[inline]
    pub const fn double(&self) -> Fr {
        self.add(self)
    }

    /// Attempts to convert a little-endian byte representation of
    /// a field element into an element of `Fr`, failing if the input
    /// is not canonical (is not smaller than r).
    pub fn from_bytes(bytes: &[u8; 32]) -> CtOption<Fr> {
        println!("{:?}", bytes);
        let mut tmp = Fr([0, 0, 0, 0]);

        tmp.0[0] = u64::from_le_bytes(bytes[0..8].try_into().unwrap());
        tmp.0[1] = u64::from_le_bytes(bytes[8..16].try_into().unwrap());
        tmp.0[2] = u64::from_le_bytes(bytes[16..24].try_into().unwrap());
        tmp.0[3] = u64::from_le_bytes(bytes[24..32].try_into().unwrap());

        // Try to subtract the modulus
        let (_, borrow) = sbb(tmp.0[0], MODULUS.0[0], 0);
        let (_, borrow) = sbb(tmp.0[1], MODULUS.0[1], borrow);
        let (_, borrow) = sbb(tmp.0[2], MODULUS.0[2], borrow);
        let (_, borrow) = sbb(tmp.0[3], MODULUS.0[3], borrow);

        // If the element is smaller than MODULUS then the
        // subtraction will underflow, producing a borrow value
        // of 0xffff...ffff. Otherwise, it'll be zero.
        let is_some = (borrow as u8) & 1;

        // Convert to Montgomery form by computing
        // (a.R^0 * R^2) / R = a.R
        tmp *= &R2;

        CtOption::new(tmp, Choice::from(is_some))
    }

    /// Converts an element of `Fr` into a byte representation in
    /// little-endian byte order.
    pub fn to_bytes(&self) -> [u8; 32] {
        // Turn into canonical form by computing
        // (a.R) / R = a
        let tmp = Fr::montgomery_reduce(self.0[0], self.0[1], self.0[2], self.0[3], 0, 0, 0, 0);

        let mut res = [0; 32];
        res[0..8].copy_from_slice(&tmp.0[0].to_le_bytes());
        res[8..16].copy_from_slice(&tmp.0[1].to_le_bytes());
        res[16..24].copy_from_slice(&tmp.0[2].to_le_bytes());
        res[24..32].copy_from_slice(&tmp.0[3].to_le_bytes());

        res
    }

    /// Converts a 512-bit little endian integer into
    /// an element of Fr by reducing modulo r.
    pub fn from_bytes_wide(bytes: &[u8; 64]) -> Fr {
        Fr::from_u512([
            u64::from_le_bytes(bytes[0..8].try_into().unwrap()),
            u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
            u64::from_le_bytes(bytes[16..24].try_into().unwrap()),
            u64::from_le_bytes(bytes[24..32].try_into().unwrap()),
            u64::from_le_bytes(bytes[32..40].try_into().unwrap()),
            u64::from_le_bytes(bytes[40..48].try_into().unwrap()),
            u64::from_le_bytes(bytes[48..56].try_into().unwrap()),
            u64::from_le_bytes(bytes[56..64].try_into().unwrap()),
        ])
    }

    fn from_u512(limbs: [u64; 8]) -> Fr {
        // We reduce an arbitrary 512-bit number by decomposing it into two 256-bit digits
        // with the higher bits multiplied by 2^256. Thus, we perform two reductions
        //
        // 1. the lower bits are multiplied by R^2, as normal
        // 2. the upper bits are multiplied by R^2 * 2^256 = R^3
        //
        // and computing their sum in the field. It remains to see that arbitrary 256-bit
        // numbers can be placed into Montgomery form safely using the reduction. The
        // reduction works so long as the product is less than R=2^256 multiplied by
        // the modulus. This holds because for any `c` smaller than the modulus, we have
        // that (2^256 - 1)*c is an acceptable product for the reduction. Therefore, the
        // reduction always works so long as `c` is in the field; in this case it is either the
        // constant `R2` or `R3`.
        let d0 = Fr([limbs[0], limbs[1], limbs[2], limbs[3]]);
        let d1 = Fr([limbs[4], limbs[5], limbs[6], limbs[7]]);
        // Convert to Montgomery form
        d0 * R2 + d1 * R3
    }

    /// Converts from an integer represented in little endian
    /// into its (congruent) `Fr` representation.
    pub const fn from_raw(val: [u64; 4]) -> Self {
        (&Fr(val)).mul(&R2)
    }

    /// Squares this element.
    #[inline]
    pub const fn square(&self) -> Fr {
        let (r1, carry) = mac(0, self.0[0], self.0[1], 0);
        let (r2, carry) = mac(0, self.0[0], self.0[2], carry);
        let (r3, r4) = mac(0, self.0[0], self.0[3], carry);

        let (r3, carry) = mac(r3, self.0[1], self.0[2], 0);
        let (r4, r5) = mac(r4, self.0[1], self.0[3], carry);

        let (r5, r6) = mac(r5, self.0[2], self.0[3], 0);

        let r7 = r6 >> 63;
        let r6 = (r6 << 1) | (r5 >> 63);
        let r5 = (r5 << 1) | (r4 >> 63);
        let r4 = (r4 << 1) | (r3 >> 63);
        let r3 = (r3 << 1) | (r2 >> 63);
        let r2 = (r2 << 1) | (r1 >> 63);
        let r1 = r1 << 1;

        let (r0, carry) = mac(0, self.0[0], self.0[0], 0);
        let (r1, carry) = adc(0, r1, carry);
        let (r2, carry) = mac(r2, self.0[1], self.0[1], carry);
        let (r3, carry) = adc(0, r3, carry);
        let (r4, carry) = mac(r4, self.0[2], self.0[2], carry);
        let (r5, carry) = adc(0, r5, carry);
        let (r6, carry) = mac(r6, self.0[3], self.0[3], carry);
        let (r7, _) = adc(0, r7, carry);

        Fr::montgomery_reduce(r0, r1, r2, r3, r4, r5, r6, r7)
    }

    /// Computes the square root of this element, if it exists.
    pub fn sqrt(&self) -> CtOption<Self> {
        // Because r = 5 (mod 8)
        // sqrt can be done with only one exponentiation and some checks,
        // via the computation of  
        //      = self^((r + 3) // 8) (mod r)
        //        OR
        //      = self^((r + 3) // 8) * sqrt(-1) (mod r) 
        //      = self^((r + 3) // 8) * (2^((r - 1) / 4)) (mod r)

        let x1 = self.pow(&[
            0xcb02_4c63_4b9e_ba7e,
            0x029b_df3b_d45e_f39a,
            0x0000_0000_0000_0000,
            0x0200_0000_0000_0000,
        ]);

        let choice1 = x1.square().ct_eq(&self);
        let choice2 = x1.square().ct_eq(&-self);

        let sqrt = Self::conditional_select(&x1, &(x1 * SQRT_MINUS_ONE), choice2);

        CtOption::new(sqrt, choice1 | choice2) // Only return Some if it's the square root.
    }

    /// Exponentiates `self` by `by`, where `by` is a
    /// little-endian order integer exponent.
    pub fn pow(&self, by: &[u64; 4]) -> Self {
        let mut res = Self::one();
        for e in by.iter().rev() {
            for i in (0..64).rev() {
                res = res.square();
                let mut tmp = res;
                tmp.mul_assign(self);
                res.conditional_assign(&tmp, (((*e >> i) & 0x1) as u8).into());
            }
        }
        res
    }

    /// Exponentiates `self` by `by`, where `by` is a
    /// little-endian order integer exponent.
    ///
    /// **This operation is variable time with respect
    /// to the exponent.** If the exponent is fixed,
    /// this operation is effectively constant time.
    pub fn pow_vartime(&self, by: &[u64; 4]) -> Self {
        let mut res = Self::one();
        for e in by.iter().rev() {
            for i in (0..64).rev() {
                res = res.square();

                if ((*e >> i) & 1) == 1 {
                    res.mul_assign(self);
                }
            }
        }
        res
    }

    /// Computes the multiplicative inverse of this element,
    /// failing if the element is zero.
    // TODO: Use https://github.com/kwantam/addchain
    pub fn invert(&self) -> CtOption<Self> {
        // Exponentiate by r - 2
        let t = self.pow_vartime(&[
            0x5812_631a_5cf5_d3eb,
            0x14de_f9de_a2f7_9cd6,
            0x0000_0000_0000_0000,
            0x1000_0000_0000_0000,
        ]);

        CtOption::new(t, !self.is_zero())
    }

    #[inline]
    #[allow(clippy::too_many_arguments)]
    const fn montgomery_reduce(
        r0: u64,
        r1: u64,
        r2: u64,
        r3: u64,
        r4: u64,
        r5: u64,
        r6: u64,
        r7: u64,
    ) -> Self {
        // The Montgomery reduction here is based on Algorithm 14.32 in
        // Handbook of Applied Cryptography
        // <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>.

        let k = r0.wrapping_mul(INV);
        let (_, carry) = mac(r0, k, MODULUS.0[0], 0);
        let (r1, carry) = mac(r1, k, MODULUS.0[1], carry);
        let (r2, carry) = mac(r2, k, MODULUS.0[2], carry);
        let (r3, carry) = mac(r3, k, MODULUS.0[3], carry);
        let (r4, carry2) = adc(r4, 0, carry);

        let k = r1.wrapping_mul(INV);
        let (_, carry) = mac(r1, k, MODULUS.0[0], 0);
        let (r2, carry) = mac(r2, k, MODULUS.0[1], carry);
        let (r3, carry) = mac(r3, k, MODULUS.0[2], carry);
        let (r4, carry) = mac(r4, k, MODULUS.0[3], carry);
        let (r5, carry2) = adc(r5, carry2, carry);

        let k = r2.wrapping_mul(INV);
        let (_, carry) = mac(r2, k, MODULUS.0[0], 0);
        let (r3, carry) = mac(r3, k, MODULUS.0[1], carry);
        let (r4, carry) = mac(r4, k, MODULUS.0[2], carry);
        let (r5, carry) = mac(r5, k, MODULUS.0[3], carry);
        let (r6, carry2) = adc(r6, carry2, carry);

        let k = r3.wrapping_mul(INV);
        let (_, carry) = mac(r3, k, MODULUS.0[0], 0);
        let (r4, carry) = mac(r4, k, MODULUS.0[1], carry);
        let (r5, carry) = mac(r5, k, MODULUS.0[2], carry);
        let (r6, carry) = mac(r6, k, MODULUS.0[3], carry);
        let (r7, _) = adc(r7, carry2, carry);

        // Result may be within MODULUS of the correct value
        (&Fr([r4, r5, r6, r7])).sub(&MODULUS)
    }

    /// Multiplies this element by another element
    #[inline]
    pub const fn mul(&self, rhs: &Self) -> Self {
        // Schoolbook multiplication

        let (r0, carry) = mac(0, self.0[0], rhs.0[0], 0);
        let (r1, carry) = mac(0, self.0[0], rhs.0[1], carry);
        let (r2, carry) = mac(0, self.0[0], rhs.0[2], carry);
        let (r3, r4) = mac(0, self.0[0], rhs.0[3], carry);

        let (r1, carry) = mac(r1, self.0[1], rhs.0[0], 0);
        let (r2, carry) = mac(r2, self.0[1], rhs.0[1], carry);
        let (r3, carry) = mac(r3, self.0[1], rhs.0[2], carry);
        let (r4, r5) = mac(r4, self.0[1], rhs.0[3], carry);

        let (r2, carry) = mac(r2, self.0[2], rhs.0[0], 0);
        let (r3, carry) = mac(r3, self.0[2], rhs.0[1], carry);
        let (r4, carry) = mac(r4, self.0[2], rhs.0[2], carry);
        let (r5, r6) = mac(r5, self.0[2], rhs.0[3], carry);

        let (r3, carry) = mac(r3, self.0[3], rhs.0[0], 0);
        let (r4, carry) = mac(r4, self.0[3], rhs.0[1], carry);
        let (r5, carry) = mac(r5, self.0[3], rhs.0[2], carry);
        let (r6, r7) = mac(r6, self.0[3], rhs.0[3], carry);

        Fr::montgomery_reduce(r0, r1, r2, r3, r4, r5, r6, r7)
    }

    /// Subtracts another element from this element.
    #[inline]
    pub const fn sub(&self, rhs: &Self) -> Self {
        let (d0, borrow) = sbb(self.0[0], rhs.0[0], 0);
        let (d1, borrow) = sbb(self.0[1], rhs.0[1], borrow);
        let (d2, borrow) = sbb(self.0[2], rhs.0[2], borrow);
        let (d3, borrow) = sbb(self.0[3], rhs.0[3], borrow);

        // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
        // borrow = 0x000...000. Thus, we use it as a mask to conditionally add the modulus.
        let (d0, carry) = adc(d0, MODULUS.0[0] & borrow, 0);
        let (d1, carry) = adc(d1, MODULUS.0[1] & borrow, carry);
        let (d2, carry) = adc(d2, MODULUS.0[2] & borrow, carry);
        let (d3, _) = adc(d3, MODULUS.0[3] & borrow, carry);

        Fr([d0, d1, d2, d3])
    }

    /// Adds this element to another element.
    #[inline]
    pub const fn add(&self, rhs: &Self) -> Self {
        let (d0, carry) = adc(self.0[0], rhs.0[0], 0);
        let (d1, carry) = adc(self.0[1], rhs.0[1], carry);
        let (d2, carry) = adc(self.0[2], rhs.0[2], carry);
        let (d3, _) = adc(self.0[3], rhs.0[3], carry);

        // Attempt to subtract the modulus, to ensure the value
        // is smaller than the modulus.
        (&Fr([d0, d1, d2, d3])).sub(&MODULUS)
    }

    /// Negates this element.
    #[inline]
    pub const fn neg(&self) -> Self {
        // Subtract `self` from `MODULUS` to negate. Ignore the final
        // borrow because it cannot underflow; self is guaranteed to
        // be in the field.
        let (d0, borrow) = sbb(MODULUS.0[0], self.0[0], 0);
        let (d1, borrow) = sbb(MODULUS.0[1], self.0[1], borrow);
        let (d2, borrow) = sbb(MODULUS.0[2], self.0[2], borrow);
        let (d3, _) = sbb(MODULUS.0[3], self.0[3], borrow);

        // `tmp` could be `MODULUS` if `self` was zero. Create a mask that is
        // zero if `self` was zero, and `u64::max_value()` if self was nonzero.
        let mask = (((self.0[0] | self.0[1] | self.0[2] | self.0[3]) == 0) as u64).wrapping_sub(1);

        Fr([d0 & mask, d1 & mask, d2 & mask, d3 & mask])
    }
}

impl From<Fr> for [u8; 32] {
    fn from(value: Fr) -> [u8; 32] {
        value.to_bytes()
    }
}

impl<'a> From<&'a Fr> for [u8; 32] {
    fn from(value: &'a Fr) -> [u8; 32] {
        value.to_bytes()
    }
}

impl Field for Fr {
    fn random(mut rng: impl RngCore) -> Self {
        let mut buf = [0; 64];
        rng.fill_bytes(&mut buf);
        Self::from_bytes_wide(&buf)
    }

    fn zero() -> Self {
        Self::zero()
    }

    fn one() -> Self {
        Self::one()
    }

    #[must_use]
    fn square(&self) -> Self {
        self.square()
    }

    #[must_use]
    fn double(&self) -> Self {
        self.double()
    }

    fn invert(&self) -> CtOption<Self> {
        self.invert()
    }

    fn sqrt(&self) -> CtOption<Self> {
        self.sqrt()
    }
}

impl PrimeField for Fr {
    type Repr = [u8; 32];

    fn from_repr(r: Self::Repr) -> CtOption<Self> {
        Self::from_bytes(&r)
    }

    fn to_repr(&self) -> Self::Repr {
        self.to_bytes()
    }

    fn is_odd(&self) -> Choice {
        Choice::from(self.to_bytes()[0] & 1)
    }

    const NUM_BITS: u32 = MODULUS_BITS;
    const CAPACITY: u32 = Self::NUM_BITS - 1;

    fn multiplicative_generator() -> Self {
        GENERATOR
    }

    const S: u32 = S;

    fn root_of_unity() -> Self {
        ROOT_OF_UNITY
    }
}

#[cfg(all(feature = "bits", not(target_pointer_width = "64")))]
type ReprBits = [u32; 8];

#[cfg(all(feature = "bits", target_pointer_width = "64"))]
type ReprBits = [u64; 4];

#[cfg(feature = "bits")]
impl PrimeFieldBits for Fr {
    type ReprBits = ReprBits;

    fn to_le_bits(&self) -> FieldBits<Self::ReprBits> {
        let bytes = self.to_bytes();

        #[cfg(not(target_pointer_width = "64"))]
        let limbs = [
            u32::from_le_bytes(bytes[0..4].try_into().unwrap()),
            u32::from_le_bytes(bytes[4..8].try_into().unwrap()),
            u32::from_le_bytes(bytes[8..12].try_into().unwrap()),
            u32::from_le_bytes(bytes[12..16].try_into().unwrap()),
            u32::from_le_bytes(bytes[16..20].try_into().unwrap()),
            u32::from_le_bytes(bytes[20..24].try_into().unwrap()),
            u32::from_le_bytes(bytes[24..28].try_into().unwrap()),
            u32::from_le_bytes(bytes[28..32].try_into().unwrap()),
        ];

        #[cfg(target_pointer_width = "64")]
        let limbs = [
            u64::from_le_bytes(bytes[0..8].try_into().unwrap()),
            u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
            u64::from_le_bytes(bytes[16..24].try_into().unwrap()),
            u64::from_le_bytes(bytes[24..32].try_into().unwrap()),
        ];

        FieldBits::new(limbs)
    }

    fn char_le_bits() -> FieldBits<Self::ReprBits> {
        #[cfg(not(target_pointer_width = "64"))]
        {
            FieldBits::new(MODULUS_LIMBS_32)
        }

        #[cfg(target_pointer_width = "64")]
        FieldBits::new(MODULUS.0)
    }
}

#[test]
fn test_inv() {
    // Compute -(r^{-1} mod 2^64) mod 2^64 by exponentiating
    // by totient(2**64) - 1

    let mut inv = 1u64;
    for _ in 0..63 {
        inv = inv.wrapping_mul(inv);
        inv = inv.wrapping_mul(MODULUS.0[0]);
    }
    inv = inv.wrapping_neg();

    assert_eq!(inv, INV);
}

#[test]
fn test_debug() {
    assert_eq!(
        format!("{:?}", Fr::zero()),
        "0x0000000000000000000000000000000000000000000000000000000000000000"
    );
    assert_eq!(
        format!("{:?}", Fr::one()),
        "0x0000000000000000000000000000000000000000000000000000000000000001"
    );
    assert_eq!(
        format!("{:?}", R2),
        "0x0ffffffffffffffffffffffffffffffec6ef5bf4737dcf70d6ec31748d98951d"
    );
}

#[test]
fn test_equality() {
    assert_eq!(Fr::zero(), Fr::zero());
    assert_eq!(Fr::one(), Fr::one());
    assert_eq!(R2, R2);

    assert!(Fr::zero() != Fr::one());
    assert!(Fr::one() != R2);
}

#[test]
fn test_to_bytes() {
    assert_eq!(
        Fr::zero().to_bytes(),
        [
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0
        ]
    );

    assert_eq!(
        Fr::one().to_bytes(),
        [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0
        ]
    );

    assert_eq!(
        R2.to_bytes(),
        [
            29, 149, 152, 141, 116, 49, 236, 214, 112, 207, 125, 115, 244, 91, 239, 198, 254, 255, 
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 15
        ]
    );

    assert_eq!(
        (-&Fr::one()).to_bytes(),
        [
            236, 211, 245, 92, 26, 99, 18, 88, 214, 156, 247, 162, 222, 249, 222, 20, 0, 0, 0, 0, 
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16
        ]
    );
}

#[test]
fn test_from_bytes() {
    assert_eq!(
        Fr::from_bytes(&[
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0
        ])
        .unwrap(),
        Fr::zero()
    );

    assert_eq!(
        Fr::from_bytes(&[
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0
        ])
        .unwrap(),
        Fr::one()
    );

    assert_eq!(
        Fr::from_bytes(&[
            29, 149, 152, 141, 116, 49, 236, 214, 112, 207, 125, 115, 244, 91, 239, 198, 254, 255, 
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 15
        ])
        .unwrap(),
        R2
    );

    // -1 should work
    assert!(bool::from(
        Fr::from_bytes(&[
            236, 211, 245, 92, 26, 99, 18, 88, 214, 156, 247, 162, 222, 249, 222, 20, 0, 0, 0, 0, 
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16
        ])
        .is_some()
    ));

    // modulus is invalid
    assert!(bool::from(
        Fr::from_bytes(&[
            237, 211, 245, 92, 26, 99, 18, 88, 214, 156, 247, 162, 222, 249, 222, 20, 0, 0, 0, 0, 
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16
        ])
        .is_none()
    ));

    // Anything larger than the modulus is invalid
    assert!(bool::from(
        Fr::from_bytes(&[
            238, 211, 245, 92, 26, 99, 18, 88, 214, 156, 247, 162, 222, 249, 222, 20, 0, 0, 0, 0, 
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16
        ])
        .is_none()
    ));

    assert!(bool::from(
        Fr::from_bytes(&[
            237, 211, 245, 92, 26, 99, 18, 88, 214, 156, 247, 162, 222, 249, 222, 20, 1, 0, 0, 0, 
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16
        ])
        .is_none()
    ));

    assert!(bool::from(
        Fr::from_bytes(&[
            237, 211, 245, 92, 26, 99, 18, 88, 214, 156, 247, 162, 222, 249, 222, 20, 0, 0, 0, 0, 
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17
        ])
        .is_none()
    ));
}

#[test]
fn test_from_u512_zero() {
    assert_eq!(
        Fr::zero(),
        Fr::from_u512([
            MODULUS.0[0],
            MODULUS.0[1],
            MODULUS.0[2],
            MODULUS.0[3],
            0,
            0,
            0,
            0
        ])
    );
}

#[test]
fn test_from_u512_r() {
    assert_eq!(R, Fr::from_u512([1, 0, 0, 0, 0, 0, 0, 0]));
}

#[test]
fn test_from_u512_r2() {
    assert_eq!(R2, Fr::from_u512([0, 0, 0, 0, 1, 0, 0, 0]));
}

#[test]
fn test_from_u512_max() {
    let max_u64 = 0xffff_ffff_ffff_ffff;
    assert_eq!(
        R3 - R,
        Fr::from_u512([max_u64, max_u64, max_u64, max_u64, max_u64, max_u64, max_u64, max_u64])
    );
}

#[test]
fn test_from_bytes_wide_r2() {
    assert_eq!(
        R2,
        Fr::from_bytes_wide(&[
            29, 149, 152, 141, 116, 49, 236, 214, 112, 207, 125, 115, 244, 91, 239, 198, 254, 255, 
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 15, 0, 0, 0, 0, 0, 0, 
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ])
    );
}

#[test]
fn test_from_bytes_wide_negative_one() {
    assert_eq!(
        -&Fr::one(),
        Fr::from_bytes_wide(&[
            236, 211, 245, 92, 26, 99, 18, 88, 214, 156, 247, 162, 222, 249, 222, 20, 0, 0, 0, 0, 
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ])
    );
}

#[test]
fn test_from_bytes_wide_maximum() {
    assert_eq!(
        Fr([
            0xabc4_7b0e_4ae0_e1ab,
            0x7572_c2d0_de71_c151,
            0x8065_dc6c_04ec_5b66,
            0x0e53_0b77_3599_cec7,
        ]),
        Fr::from_bytes_wide(&[0xff; 64])
    );
}

#[test]
fn test_zero() {
    assert_eq!(Fr::zero(), -&Fr::zero());
    assert_eq!(Fr::zero(), Fr::zero() + Fr::zero());
    assert_eq!(Fr::zero(), Fr::zero() - Fr::zero());
    assert_eq!(Fr::zero(), Fr::zero() * Fr::zero());
}

#[cfg(test)]
const LARGEST: Fr = Fr([
    0x5812_631a_5cf5_d3ec,
    0x14de_f9de_a2f7_9cd6,
    0x0000_0000_0000_0000,
    0x1000_0000_0000_0000,
]);

#[test]
fn test_addition() {
    let mut tmp = LARGEST;
    tmp += &LARGEST;

    assert_eq!(
        tmp,
        Fr([
            0x5812_631a_5cf5_d3eb,
            0x14de_f9de_a2f7_9cd6,
            0x0000_0000_0000_0000,
            0x1000_0000_0000_0000,
        ])
    );

    let mut tmp = LARGEST;
    tmp += &Fr([1, 0, 0, 0]);

    assert_eq!(tmp, Fr::zero());
}

#[test]
fn test_negation() {
    let tmp = -&LARGEST;

    assert_eq!(tmp, Fr([1, 0, 0, 0]));

    let tmp = -&Fr::zero();
    assert_eq!(tmp, Fr::zero());
    let tmp = -&Fr([1, 0, 0, 0]);
    assert_eq!(tmp, LARGEST);
}

#[test]
fn test_subtraction() {
    let mut tmp = LARGEST;
    tmp -= &LARGEST;

    assert_eq!(tmp, Fr::zero());

    let mut tmp = Fr::zero();
    tmp -= &LARGEST;

    let mut tmp2 = MODULUS;
    tmp2 -= &LARGEST;

    assert_eq!(tmp, tmp2);
}

#[test]
fn test_multiplication() {
    let mut cur = LARGEST;

    for _ in 0..100 {
        let mut tmp = cur;
        tmp *= &cur;

        let mut tmp2 = Fr::zero();
        for b in cur
            .to_bytes()
            .iter()
            .rev()
            .flat_map(|byte| (0..8).rev().map(move |i| ((byte >> i) & 1u8) == 1u8))
        {
            let tmp3 = tmp2;
            tmp2.add_assign(&tmp3);

            if b {
                tmp2.add_assign(&cur);
            }
        }

        assert_eq!(tmp, tmp2);

        cur.add_assign(&LARGEST);
    }
}

#[test]
fn test_squaring() {
    let mut cur = LARGEST;

    for _ in 0..100 {
        let mut tmp = cur;
        tmp = tmp.square();

        let mut tmp2 = Fr::zero();
        for b in cur
            .to_bytes()
            .iter()
            .rev()
            .flat_map(|byte| (0..8).rev().map(move |i| ((byte >> i) & 1u8) == 1u8))
        {
            let tmp3 = tmp2;
            tmp2.add_assign(&tmp3);

            if b {
                tmp2.add_assign(&cur);
            }
        }

        assert_eq!(tmp, tmp2);

        cur.add_assign(&LARGEST);
    }
}

#[test]
fn test_inversion() {
    assert!(bool::from(Fr::zero().invert().is_none()));
    assert_eq!(Fr::one().invert().unwrap(), Fr::one());
    assert_eq!((-&Fr::one()).invert().unwrap(), -&Fr::one());

    let mut tmp = R2;

    for _ in 0..100 {
        let mut tmp2 = tmp.invert().unwrap();
        tmp2.mul_assign(&tmp);

        assert_eq!(tmp2, Fr::one());

        tmp.add_assign(&R2);
    }
}

#[test]
fn test_invert_is_pow() {
    let r_minus_2 = [
        0x5812_631a_5cf5_d3eb,
        0x14de_f9de_a2f7_9cd6,
        0x0000_0000_0000_0000,
        0x1000_0000_0000_0000,
    ];

    let mut r1 = R;
    let mut r2 = R;
    let mut r3 = R;

    for _ in 0..100 {
        r1 = r1.invert().unwrap();
        r2 = r2.pow_vartime(&r_minus_2);
        r3 = r3.pow(&r_minus_2);

        assert_eq!(r1, r2);
        assert_eq!(r2, r3);
        // Add R so we check something different next time around
        r1.add_assign(&R);
        r2 = r1;
        r3 = r1;
    }
}

#[test]
fn test_sqrt() {
    let mut square = Fr([
        // r - 2
        0xd097_0e5e_d6f7_2cb5,
        0xa668_2093_ccc8_1082,
        0x0667_3b01_0134_3b00,
        0x0e7d_b4ea_6533_afa9,
    ]);

    let mut none_count = 0;

    for _ in 0..100 {
        let square_root = square.sqrt();
        if bool::from(square_root.is_none()) {
            none_count += 1;
        } else {
            assert_eq!(square_root.unwrap() * square_root.unwrap(), square);
        }
        square -= Fr::one();
    }

    assert_eq!(60, none_count);
}

#[test]
fn test_from_raw() {
    assert_eq!(
        Fr::from_raw([
            0xd6ec_3174_8d98_951c,
            0xc6ef_5bf4_737d_cf70,
            0xffff_ffff_ffff_fffe,
            0x0fff_ffff_ffff_ffff,
        ]),
        Fr::from_raw([0xffff_ffff_ffff_ffff; 4])
    );

    assert_eq!(Fr::from_raw(MODULUS.0), Fr::zero());

    assert_eq!(Fr::from_raw([1, 0, 0, 0]), R);
}