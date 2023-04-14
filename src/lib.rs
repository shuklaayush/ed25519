//! This crate provides an implementation of the **Ed25519** elliptic curve and its associated
//! field arithmetic. See [`README.md`](https://github.com/shuklaayush/ed25519/blob/master/README.md) for more details about Ed25519.
//!
//! # API
//!
//! * `AffinePoint` / `ExtendedPoint` which are implementations of Ed25519 group arithmetic
//! * `AffineNielsPoint` / `ExtendedNielsPoint` which are pre-processed Ed25519 points
//! * `Fq`, which is the base field of Ed25519
//! * `Fr`, which is the scalar field of Ed25519
//! * `batch_normalize` for converting many `ExtendedPoint`s into `AffinePoint`s efficiently.
//!
//! # Constant Time
//!
//! All operations are constant time unless explicitly noted; these functions will contain
//! "vartime" in their name and they will be documented as variable time.
//!
//! This crate uses the `subtle` crate to perform constant-time operations.

// TODO: Remove cofactor group and only keep functionality related to prime group
//       remove full generator etc.
// TODO: Uncomment
// #![no_std]
// Catch documentation errors caused by code changes.
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]
#![deny(unsafe_code)]
// This lint is described at
// https://rust-lang.github.io/rust-clippy/master/index.html#suspicious_arithmetic_impl
// In our library, some of the arithmetic will necessarily involve various binary
// operators, and so this lint is triggered unnecessarily.
#![allow(clippy::suspicious_arithmetic_impl)]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(test)]
#[macro_use]
extern crate std;

use bitvec::{order::Lsb0, view::AsBits};
use core::borrow::Borrow;
use core::fmt;
use core::iter::Sum;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use ff::{BatchInverter, Field};
use group::{
    cofactor::{CofactorCurve, CofactorCurveAffine, CofactorGroup},
    prime::{PrimeCurve, PrimeCurveAffine, PrimeGroup},
    Curve, Group, GroupEncoding,
};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

#[cfg(feature = "alloc")]
use group::WnafGroup;

#[macro_use]
mod util;

mod fq;
mod fr;
pub use fq::Fq;
pub use fr::Fr;

/// Represents an element of the base field $\mathbb{F}_q$ of the Ed25519 elliptic curve
/// construction.
pub type Base = Fq;

/// Represents an element of the scalar field $\mathbb{F}_r$ of the Ed25519 elliptic curve
/// construction.
pub type Scalar = Fr;

const FR_MODULUS_BYTES: [u8; 32] = [
    237, 211, 245, 92, 26, 99, 18, 88, 214, 156, 247, 162, 222, 249, 222, 20, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 16,
];

/// This represents a Ed25519 point in the affine `(u, v)`
/// coordinates.
#[derive(Clone, Copy, Debug, Eq)]
pub struct AffinePoint {
    u: Fq,
    v: Fq,
}

impl fmt::Display for AffinePoint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Neg for AffinePoint {
    type Output = AffinePoint;

    /// This computes the negation of a point `P = (u, v)`
    /// as `-P = (-u, v)`.
    #[inline]
    fn neg(self) -> AffinePoint {
        AffinePoint {
            u: -self.u,
            v: self.v,
        }
    }
}

impl ConstantTimeEq for AffinePoint {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.u.ct_eq(&other.u) & self.v.ct_eq(&other.v)
    }
}

impl PartialEq for AffinePoint {
    fn eq(&self, other: &Self) -> bool {
        bool::from(self.ct_eq(other))
    }
}

impl ConditionallySelectable for AffinePoint {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        AffinePoint {
            u: Fq::conditional_select(&a.u, &b.u, choice),
            v: Fq::conditional_select(&a.v, &b.v, choice),
        }
    }
}

/// This represents an extended point `(U, V, Z, T1, T2)`
/// with `Z` nonzero, corresponding to the affine point
/// `(U/Z, V/Z)`. We always have `T1 * T2 = UV/Z`.
///
/// You can do the following things with a point in this
/// form:
///
/// * Convert it into a point in the affine form.
/// * Add it to an `ExtendedPoint`, `AffineNielsPoint` or `ExtendedNielsPoint`.
/// * Double it using `double()`.
/// * Compare it with another extended point using `PartialEq` or `ct_eq()`.
#[derive(Clone, Copy, Debug, Eq)]
pub struct ExtendedPoint {
    u: Fq,
    v: Fq,
    z: Fq,
    t1: Fq,
    t2: Fq,
}

impl fmt::Display for ExtendedPoint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl ConstantTimeEq for ExtendedPoint {
    fn ct_eq(&self, other: &Self) -> Choice {
        // (u/z, v/z) = (u'/z', v'/z') is implied by
        //      (uz'z = u'z'z) and
        //      (vz'z = v'z'z)
        // as z and z' are always nonzero.

        (self.u * other.z).ct_eq(&(other.u * self.z))
            & (self.v * other.z).ct_eq(&(other.v * self.z))
    }
}

impl ConditionallySelectable for ExtendedPoint {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        ExtendedPoint {
            u: Fq::conditional_select(&a.u, &b.u, choice),
            v: Fq::conditional_select(&a.v, &b.v, choice),
            z: Fq::conditional_select(&a.z, &b.z, choice),
            t1: Fq::conditional_select(&a.t1, &b.t1, choice),
            t2: Fq::conditional_select(&a.t2, &b.t2, choice),
        }
    }
}

impl PartialEq for ExtendedPoint {
    fn eq(&self, other: &Self) -> bool {
        bool::from(self.ct_eq(other))
    }
}

impl<T> Sum<T> for ExtendedPoint
where
    T: Borrow<ExtendedPoint>,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(Self::identity(), |acc, item| acc + item.borrow())
    }
}

impl Neg for ExtendedPoint {
    type Output = ExtendedPoint;

    /// Computes the negation of a point `P = (U, V, Z, T)`
    /// as `-P = (-U, V, Z, -T1, T2)`. The choice of `T1`
    /// is made without loss of generality.
    #[inline]
    fn neg(self) -> ExtendedPoint {
        ExtendedPoint {
            u: -self.u,
            v: self.v,
            z: self.z,
            t1: -self.t1,
            t2: self.t2,
        }
    }
}

impl From<AffinePoint> for ExtendedPoint {
    /// Constructs an extended point (with `Z = 1`) from
    /// an affine point using the map `(u, v) => (u, v, 1, u, v)`.
    fn from(affine: AffinePoint) -> ExtendedPoint {
        ExtendedPoint {
            u: affine.u,
            v: affine.v,
            z: Fq::one(),
            t1: affine.u,
            t2: affine.v,
        }
    }
}

impl<'a> From<&'a ExtendedPoint> for AffinePoint {
    /// Constructs an affine point from an extended point
    /// using the map `(U, V, Z, T1, T2) => (U/Z, V/Z)`
    /// as Z is always nonzero. **This requires a field inversion
    /// and so it is recommended to perform these in a batch
    /// using [`batch_normalize`](crate::batch_normalize) instead.**
    fn from(extended: &'a ExtendedPoint) -> AffinePoint {
        // Z coordinate is always nonzero, so this is
        // its inverse.
        let zinv = extended.z.invert().unwrap();

        AffinePoint {
            u: extended.u * zinv,
            v: extended.v * zinv,
        }
    }
}

impl From<ExtendedPoint> for AffinePoint {
    fn from(extended: ExtendedPoint) -> AffinePoint {
        AffinePoint::from(&extended)
    }
}

/// This is a pre-processed version of an affine point `(u, v)`
/// in the form `(v + u, v - u, u * v * 2d)`. This can be added to an
/// [`ExtendedPoint`](crate::ExtendedPoint).
#[derive(Clone, Copy, Debug)]
pub struct AffineNielsPoint {
    v_plus_u: Fq,
    v_minus_u: Fq,
    t2d: Fq,
}

impl AffineNielsPoint {
    /// Constructs this point from the neutral element `(0, 1)`.
    pub const fn identity() -> Self {
        AffineNielsPoint {
            v_plus_u: Fq::one(),
            v_minus_u: Fq::one(),
            t2d: Fq::zero(),
        }
    }

    #[inline]
    fn multiply(&self, by: &[u8; 32]) -> ExtendedPoint {
        let zero = AffineNielsPoint::identity();

        let mut acc = ExtendedPoint::identity();

        // This is a simple double-and-add implementation of point
        // multiplication, moving from most significant to least
        // significant bit of the scalar.
        //
        // We skip the leading three bits because they're always
        // unset for Fr.
        for bit in by
            .as_bits::<Lsb0>()
            .iter()
            .rev()
            .skip(3)
            .map(|bit| Choice::from(if *bit { 1 } else { 0 }))
        {
            acc = acc.double();
            acc += AffineNielsPoint::conditional_select(&zero, &self, bit);
        }

        acc
    }

    /// Multiplies this point by the specific little-endian bit pattern in the
    /// given byte array, ignoring the highest four bits.
    pub fn multiply_bits(&self, by: &[u8; 32]) -> ExtendedPoint {
        self.multiply(by)
    }
}

impl<'a, 'b> Mul<&'b Fr> for &'a AffineNielsPoint {
    type Output = ExtendedPoint;

    fn mul(self, other: &'b Fr) -> ExtendedPoint {
        self.multiply(&other.to_bytes())
    }
}

impl_binops_multiplicative_mixed!(AffineNielsPoint, Fr, ExtendedPoint);

impl ConditionallySelectable for AffineNielsPoint {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        AffineNielsPoint {
            v_plus_u: Fq::conditional_select(&a.v_plus_u, &b.v_plus_u, choice),
            v_minus_u: Fq::conditional_select(&a.v_minus_u, &b.v_minus_u, choice),
            t2d: Fq::conditional_select(&a.t2d, &b.t2d, choice),
        }
    }
}

/// This is a pre-processed version of an extended point `(U, V, Z, T1, T2)`
/// in the form `(V + U, V - U, Z, T1 * T2 * 2d)`.
#[derive(Clone, Copy, Debug)]
pub struct ExtendedNielsPoint {
    v_plus_u: Fq,
    v_minus_u: Fq,
    z: Fq,
    t2d: Fq,
}

impl ConditionallySelectable for ExtendedNielsPoint {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        ExtendedNielsPoint {
            v_plus_u: Fq::conditional_select(&a.v_plus_u, &b.v_plus_u, choice),
            v_minus_u: Fq::conditional_select(&a.v_minus_u, &b.v_minus_u, choice),
            z: Fq::conditional_select(&a.z, &b.z, choice),
            t2d: Fq::conditional_select(&a.t2d, &b.t2d, choice),
        }
    }
}

impl ExtendedNielsPoint {
    /// Constructs this point from the neutral element `(0, 1)`.
    pub const fn identity() -> Self {
        ExtendedNielsPoint {
            v_plus_u: Fq::one(),
            v_minus_u: Fq::one(),
            z: Fq::one(),
            t2d: Fq::zero(),
        }
    }

    #[inline]
    fn multiply(&self, by: &[u8; 32]) -> ExtendedPoint {
        let zero = ExtendedNielsPoint::identity();

        let mut acc = ExtendedPoint::identity();

        // This is a simple double-and-add implementation of point
        // multiplication, moving from most significant to least
        // significant bit of the scalar.
        //
        // We skip the leading three bits because they're always
        // unset for Fr.
        for bit in by
            .iter()
            .rev()
            .flat_map(|byte| (0..8).rev().map(move |i| Choice::from((byte >> i) & 1u8)))
            .skip(3)
        {
            acc = acc.double();
            acc += ExtendedNielsPoint::conditional_select(&zero, &self, bit);
        }

        acc
    }

    /// Multiplies this point by the specific little-endian bit pattern in the
    /// given byte array, ignoring the highest four bits.
    pub fn multiply_bits(&self, by: &[u8; 32]) -> ExtendedPoint {
        self.multiply(by)
    }
}

impl<'a, 'b> Mul<&'b Fr> for &'a ExtendedNielsPoint {
    type Output = ExtendedPoint;

    fn mul(self, other: &'b Fr) -> ExtendedPoint {
        self.multiply(&other.to_bytes())
    }
}

impl_binops_multiplicative_mixed!(ExtendedNielsPoint, Fr, ExtendedPoint);

// `d = -(121665/121666)`
const EDWARDS_D: Fq = Fq::from_raw([
    0x75eb_4dca_1359_78a3,
    0x0070_0a4d_4141_d8ab,
    0x8cc7_4079_7779_e898,
    0x5203_6cee_2b6f_fe73,
]);

// `2*d`
const EDWARDS_D2: Fq = Fq::from_raw([
    0xebd6_9b94_26b2_f159,
    0x00e0_149a_8283_b156,
    0x198e_80f2_eef3_d130,
    0x2406_d9dc_56df_fce7,
]);

impl AffinePoint {
    /// Constructs the neutral element `(0, 1)`.
    pub const fn identity() -> Self {
        AffinePoint {
            u: Fq::zero(),
            v: Fq::one(),
        }
    }

    /// Determines if this point is the identity.
    pub fn is_identity(&self) -> Choice {
        ExtendedPoint::from(*self).is_identity()
    }

    /// Multiplies this point by the cofactor, producing an
    /// `ExtendedPoint`
    pub fn mul_by_cofactor(&self) -> ExtendedPoint {
        ExtendedPoint::from(*self).mul_by_cofactor()
    }

    /// Determines if this point is of small order.
    pub fn is_small_order(&self) -> Choice {
        ExtendedPoint::from(*self).is_small_order()
    }

    /// Determines if this point is torsion free and so is
    /// in the prime order subgroup.
    pub fn is_torsion_free(&self) -> Choice {
        ExtendedPoint::from(*self).is_torsion_free()
    }

    /// Determines if this point is prime order, or in other words that
    /// the smallest scalar multiplied by this point that produces the
    /// identity is `r`. This is equivalent to checking that the point
    /// is both torsion free and not the identity.
    pub fn is_prime_order(&self) -> Choice {
        let extended = ExtendedPoint::from(*self);
        extended.is_torsion_free() & (!extended.is_identity())
    }

    /// Converts this element into its byte representation.
    pub fn to_bytes(&self) -> [u8; 32] {
        let mut tmp = self.v.to_bytes();
        let u = self.u.to_bytes();

        // Encode the sign of the u-coordinate in the most
        // significant bit.
        tmp[31] |= u[0] << 7;

        tmp
    }

    /// Attempts to interpret a byte representation of an
    /// affine point, failing if the element is not on
    /// the curve or non-canonical.
    pub fn from_bytes(b: [u8; 32]) -> CtOption<Self> {
        Self::from_bytes_inner(b, 1.into())
    }

    /// Attempts to interpret a byte representation of an affine point, failing if the
    /// element is not on the curve.
    ///
    /// Most non-canonical encodings will also cause a failure. However, this API
    /// preserves (for use in consensus-critical protocols) a bug in the parsing code that
    /// caused two non-canonical encodings to be **silently** accepted:
    ///
    /// - (0, 1), which is the identity;
    /// - (0, -1), which is a point of order two.
    ///
    /// Each of these has a single non-canonical encoding in which the value of the sign
    /// bit is 1.
    ///
    /// See [ZIP 216](https://zips.z.cash/zip-0216) for a more detailed description of the
    /// bug, as well as its fix.
    // TODO: Remove?
    pub fn from_bytes_pre_zip216_compatibility(b: [u8; 32]) -> CtOption<Self> {
        Self::from_bytes_inner(b, 0.into())
    }

    fn from_bytes_inner(mut b: [u8; 32], zip_216_enabled: Choice) -> CtOption<Self> {
        // Grab the sign bit from the representation
        let sign = b[31] >> 7;

        // Mask away the sign bit
        b[31] &= 0b0111_1111;

        // Interpret what remains as the v-coordinate
        Fq::from_bytes(&b).and_then(|v| {
            // -u^2 + v^2 = 1 + d.u^2.v^2
            // -u^2 = 1 + d.u^2.v^2 - v^2    (rearrange)
            // -u^2 - d.u^2.v^2 = 1 - v^2    (rearrange)
            // u^2 + d.u^2.v^2 = v^2 - 1     (flip signs)
            // u^2 (1 + d.v^2) = v^2 - 1     (factor)
            // u^2 = (v^2 - 1) / (1 + d.v^2) (isolate u^2)
            // We know that (1 + d.v^2) is nonzero for all v:
            //   (1 + d.v^2) = 0
            //   d.v^2 = -1
            //   v^2 = -(1 / d)   No solutions, as -(1 / d) is not a square

            let v2 = v.square();

            ((v2 - Fq::one()) * ((Fq::one() + EDWARDS_D * v2).invert().unwrap_or(Fq::zero())))
                .sqrt()
                .and_then(|u| {
                    // Fix the sign of `u` if necessary
                    let flip_sign = Choice::from((u.to_bytes()[0] ^ sign) & 1);
                    let u_negated = -u;
                    let final_u = Fq::conditional_select(&u, &u_negated, flip_sign);

                    // If u == 0, flip_sign == sign_bit. We therefore want to reject the
                    // encoding as non-canonical if all of the following occur:
                    // - ZIP 216 is enabled
                    // - u == 0
                    // - flip_sign == true
                    let u_is_zero = u.ct_eq(&Fq::zero());
                    CtOption::new(
                        AffinePoint { u: final_u, v },
                        !(zip_216_enabled & u_is_zero & flip_sign),
                    )
                })
        })
    }

    /// Attempts to interpret a batch of byte representations of affine points.
    ///
    /// Returns None for each element if it is not on the curve, or is non-canonical
    /// according to ZIP 216.
    #[cfg(feature = "alloc")]
    pub fn batch_from_bytes(items: impl Iterator<Item = [u8; 32]>) -> Vec<CtOption<Self>> {
        use ff::BatchInvert;

        #[derive(Clone, Copy, Default)]
        struct Item {
            sign: u8,
            v: Fq,
            numerator: Fq,
            denominator: Fq,
        }

        impl ConditionallySelectable for Item {
            fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
                Item {
                    sign: u8::conditional_select(&a.sign, &b.sign, choice),
                    v: Fq::conditional_select(&a.v, &b.v, choice),
                    numerator: Fq::conditional_select(&a.numerator, &b.numerator, choice),
                    denominator: Fq::conditional_select(&a.denominator, &b.denominator, choice),
                }
            }
        }

        let items: Vec<_> = items
            .map(|mut b| {
                // Grab the sign bit from the representation
                let sign = b[31] >> 7;

                // Mask away the sign bit
                b[31] &= 0b0111_1111;

                // Interpret what remains as the v-coordinate
                Fq::from_bytes(&b).map(|v| {
                    // -u^2 + v^2 = 1 + d.u^2.v^2
                    // -u^2 = 1 + d.u^2.v^2 - v^2    (rearrange)
                    // -u^2 - d.u^2.v^2 = 1 - v^2    (rearrange)
                    // u^2 + d.u^2.v^2 = v^2 - 1     (flip signs)
                    // u^2 (1 + d.v^2) = v^2 - 1     (factor)
                    // u^2 = (v^2 - 1) / (1 + d.v^2) (isolate u^2)
                    // We know that (1 + d.v^2) is nonzero for all v:
                    //   (1 + d.v^2) = 0
                    //   d.v^2 = -1
                    //   v^2 = -(1 / d)   No solutions, as -(1 / d) is not a square

                    let v2 = v.square();

                    Item {
                        v,
                        sign,
                        numerator: (v2 - Fq::one()),
                        denominator: Fq::one() + EDWARDS_D * v2,
                    }
                })
            })
            .collect();

        let mut denominators: Vec<_> = items
            .iter()
            .map(|item| item.map(|item| item.denominator).unwrap_or(Fq::zero()))
            .collect();
        denominators.iter_mut().batch_invert();

        items
            .into_iter()
            .zip(denominators.into_iter())
            .map(|(item, inv_denominator)| {
                item.and_then(
                    |Item {
                         v, sign, numerator, ..
                     }| {
                        (numerator * inv_denominator).sqrt().and_then(|u| {
                            // Fix the sign of `u` if necessary
                            let flip_sign = Choice::from((u.to_bytes()[0] ^ sign) & 1);
                            let u_negated = -u;
                            let final_u = Fq::conditional_select(&u, &u_negated, flip_sign);

                            // If u == 0, flip_sign == sign_bit. We therefore want to reject the
                            // encoding as non-canonical if all of the following occur:
                            // - u == 0
                            // - flip_sign == true
                            let u_is_zero = u.ct_eq(&Fq::zero());
                            CtOption::new(AffinePoint { u: final_u, v }, !(u_is_zero & flip_sign))
                        })
                    },
                )
            })
            .collect()
    }

    /// Returns the `u`-coordinate of this point.
    pub fn get_u(&self) -> Fq {
        self.u
    }

    /// Returns the `v`-coordinate of this point.
    pub fn get_v(&self) -> Fq {
        self.v
    }

    /// Returns an `ExtendedPoint` for use in arithmetic operations.
    pub const fn to_extended(&self) -> ExtendedPoint {
        ExtendedPoint {
            u: self.u,
            v: self.v,
            z: Fq::one(),
            t1: self.u,
            t2: self.v,
        }
    }

    /// Performs a pre-processing step that produces an `AffineNielsPoint`
    /// for use in multiple additions.
    pub const fn to_niels(&self) -> AffineNielsPoint {
        AffineNielsPoint {
            v_plus_u: Fq::add(&self.v, &self.u),
            v_minus_u: Fq::sub(&self.v, &self.u),
            t2d: Fq::mul(&Fq::mul(&self.u, &self.v), &EDWARDS_D2),
        }
    }

    /// Constructs an AffinePoint given `u` and `v` without checking
    /// that the point is on the curve.
    pub const fn from_raw_unchecked(u: Fq, v: Fq) -> AffinePoint {
        AffinePoint { u, v }
    }

    /// This is only for debugging purposes and not
    /// exposed in the public API. Checks that this
    /// point is on the curve.
    #[cfg(test)]
    fn is_on_curve_vartime(&self) -> bool {
        let u2 = self.u.square();
        let v2 = self.v.square();

        v2 - u2 == Fq::one() + EDWARDS_D * u2 * v2
    }
}

impl ExtendedPoint {
    /// Constructs an extended point from the neutral element `(0, 1)`.
    pub const fn identity() -> Self {
        ExtendedPoint {
            u: Fq::zero(),
            v: Fq::one(),
            z: Fq::one(),
            t1: Fq::zero(),
            t2: Fq::zero(),
        }
    }

    /// Determines if this point is the identity.
    pub fn is_identity(&self) -> Choice {
        // If this point is the identity, then
        //     u = 0 * z = 0
        // and v = 1 * z = z
        self.u.ct_eq(&Fq::zero()) & self.v.ct_eq(&self.z)
    }

    /// Determines if this point is of small order.
    pub fn is_small_order(&self) -> Choice {
        // We only need to perform two doublings, since the 2-torsion
        // points are (0, 1) and (0, -1), and so we only need to check
        // that the u-coordinate of the result is zero to see if the
        // point is small order.
        self.double().double().u.ct_eq(&Fq::zero())
    }

    /// Determines if this point is torsion free and so is contained
    /// in the prime order subgroup.
    pub fn is_torsion_free(&self) -> Choice {
        self.multiply(&FR_MODULUS_BYTES).is_identity()
    }

    /// Determines if this point is prime order, or in other words that
    /// the smallest scalar multiplied by this point that produces the
    /// identity is `r`. This is equivalent to checking that the point
    /// is both torsion free and not the identity.
    pub fn is_prime_order(&self) -> Choice {
        self.is_torsion_free() & (!self.is_identity())
    }

    /// Multiplies this element by the cofactor `8`.
    pub fn mul_by_cofactor(&self) -> ExtendedPoint {
        self.double().double().double()
    }

    /// Performs a pre-processing step that produces an `ExtendedNielsPoint`
    /// for use in multiple additions.
    pub fn to_niels(&self) -> ExtendedNielsPoint {
        ExtendedNielsPoint {
            v_plus_u: self.v + self.u,
            v_minus_u: self.v - self.u,
            z: self.z,
            t2d: self.t1 * self.t2 * EDWARDS_D2,
        }
    }

    /// Computes the doubling of a point more efficiently than a point can
    /// be added to itself.
    pub fn double(&self) -> ExtendedPoint {
        // Doubling is more efficient (three multiplications, four squarings)
        // when we work within the projective coordinate space (U:Z, V:Z). We
        // rely on the most efficient formula, "dbl-2008-bbjlp", as described
        // in Section 6 of "Twisted Edwards Curves" by Bernstein et al.
        //
        // See <https://hyperelliptic.org/EFD/g1p/auto-twisted-projective.html#doubling-dbl-2008-bbjlp>
        // for more information.
        //
        // We differ from the literature in that we use (u, v) rather than
        // (x, y) coordinates. We also have the constant `a = -1` implied. Let
        // us rewrite the procedure of doubling (u, v, z) to produce (U, V, Z)
        // as follows:
        //
        // B = (u + v)^2
        // C = u^2
        // D = v^2
        // F = D - C
        // H = 2 * z^2
        // J = F - H
        // U = (B - C - D) * J
        // V = F * (- C - D)
        // Z = F * J
        //
        // If we compute K = D + C, we can rewrite this:
        //
        // B = (u + v)^2
        // C = u^2
        // D = v^2
        // F = D - C
        // K = D + C
        // H = 2 * z^2
        // J = F - H
        // U = (B - K) * J
        // V = F * (-K)
        // Z = F * J
        //
        // In order to avoid the unnecessary negation of K,
        // we will negate J, transforming the result into
        // an equivalent point with a negated z-coordinate.
        //
        // B = (u + v)^2
        // C = u^2
        // D = v^2
        // F = D - C
        // K = D + C
        // H = 2 * z^2
        // J = H - F
        // U = (B - K) * J
        // V = F * K
        // Z = F * J
        //
        // Let us rename some variables to simplify:
        //
        // UV2 = (u + v)^2
        // UU = u^2
        // VV = v^2
        // VVmUU = VV - UU
        // VVpUU = VV + UU
        // ZZ2 = 2 * z^2
        // J = ZZ2 - VVmUU
        // U = (UV2 - VVpUU) * J
        // V = VVmUU * VVpUU
        // Z = VVmUU * J
        //
        // We wish to obtain two factors of T = UV/Z.
        //
        // UV/Z = (UV2 - VVpUU) * (ZZ2 - VVmUU) * VVmUU * VVpUU / VVmUU / (ZZ2 - VVmUU)
        //      = (UV2 - VVpUU) * VVmUU * VVpUU / VVmUU
        //      = (UV2 - VVpUU) * VVpUU
        //
        // and so we have that T1 = (UV2 - VVpUU) and T2 = VVpUU.

        let uu = self.u.square();
        let vv = self.v.square();
        let zz2 = self.z.square().double();
        let uv2 = (self.u + self.v).square();
        let vv_plus_uu = vv + uu;
        let vv_minus_uu = vv - uu;

        // The remaining arithmetic is exactly the process of converting
        // from a completed point to an extended point.
        CompletedPoint {
            u: uv2 - vv_plus_uu,
            v: vv_plus_uu,
            z: vv_minus_uu,
            t: zz2 - vv_minus_uu,
        }
        .into_extended()
    }

    #[inline]
    fn multiply(self, by: &[u8; 32]) -> Self {
        self.to_niels().multiply(by)
    }

    /// Converts a batch of projective elements into affine elements.
    ///
    /// This function will panic if `p.len() != q.len()`.
    ///
    /// This costs 5 multiplications per element, and a field inversion.
    fn batch_normalize(p: &[Self], q: &mut [AffinePoint]) {
        assert_eq!(p.len(), q.len());

        for (p, q) in p.iter().zip(q.iter_mut()) {
            // We use the `u` field of `AffinePoint` to store the z-coordinate being
            // inverted, and the `v` field for scratch space.
            q.u = p.z;
        }

        BatchInverter::invert_with_internal_scratch(q, |q| &mut q.u, |q| &mut q.v);

        for (p, q) in p.iter().zip(q.iter_mut()).rev() {
            let tmp = q.u;

            // Set the coordinates to the correct value
            q.u = p.u * &tmp; // Multiply by 1/z
            q.v = p.v * &tmp; // Multiply by 1/z
        }
    }

    /// This is only for debugging purposes and not
    /// exposed in the public API. Checks that this
    /// point is on the curve.
    #[cfg(test)]
    fn is_on_curve_vartime(&self) -> bool {
        let affine = AffinePoint::from(*self);

        self.z != Fq::zero()
            && affine.is_on_curve_vartime()
            && (affine.u * affine.v * self.z == self.t1 * self.t2)
    }
}

impl<'a, 'b> Mul<&'b Fr> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    fn mul(self, other: &'b Fr) -> ExtendedPoint {
        self.multiply(&other.to_bytes())
    }
}

impl_binops_multiplicative!(ExtendedPoint, Fr);

impl<'a, 'b> Add<&'b ExtendedNielsPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn add(self, other: &'b ExtendedNielsPoint) -> ExtendedPoint {
        // We perform addition in the extended coordinates. Here we use
        // a formula presented by Hisil, Wong, Carter and Dawson in
        // "Twisted Edward Curves Revisited" which only requires 8M.
        //
        // A = (V1 - U1) * (V2 - U2)
        // B = (V1 + U1) * (V2 + U2)
        // C = 2d * T1 * T2
        // D = 2 * Z1 * Z2
        // E = B - A
        // F = D - C
        // G = D + C
        // H = B + A
        // U3 = E * F
        // Y3 = G * H
        // Z3 = F * G
        // T3 = E * H

        let a = (self.v - self.u) * other.v_minus_u;
        let b = (self.v + self.u) * other.v_plus_u;
        let c = self.t1 * self.t2 * other.t2d;
        let d = (self.z * other.z).double();

        // The remaining arithmetic is exactly the process of converting
        // from a completed point to an extended point.
        CompletedPoint {
            u: b - a,
            v: b + a,
            z: d + c,
            t: d - c,
        }
        .into_extended()
    }
}

impl<'a, 'b> Sub<&'b ExtendedNielsPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn sub(self, other: &'b ExtendedNielsPoint) -> ExtendedPoint {
        let a = (self.v - self.u) * other.v_plus_u;
        let b = (self.v + self.u) * other.v_minus_u;
        let c = self.t1 * self.t2 * other.t2d;
        let d = (self.z * other.z).double();

        CompletedPoint {
            u: b - a,
            v: b + a,
            z: d - c,
            t: d + c,
        }
        .into_extended()
    }
}

impl_binops_additive!(ExtendedPoint, ExtendedNielsPoint);

impl<'a, 'b> Add<&'b AffineNielsPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn add(self, other: &'b AffineNielsPoint) -> ExtendedPoint {
        // This is identical to the addition formula for `ExtendedNielsPoint`,
        // except we can assume that `other.z` is one, so that we perform
        // 7 multiplications.

        let a = (self.v - self.u) * other.v_minus_u;
        let b = (self.v + self.u) * other.v_plus_u;
        let c = self.t1 * self.t2 * other.t2d;
        let d = self.z.double();

        // The remaining arithmetic is exactly the process of converting
        // from a completed point to an extended point.
        CompletedPoint {
            u: b - a,
            v: b + a,
            z: d + c,
            t: d - c,
        }
        .into_extended()
    }
}

impl<'a, 'b> Sub<&'b AffineNielsPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn sub(self, other: &'b AffineNielsPoint) -> ExtendedPoint {
        let a = (self.v - self.u) * other.v_plus_u;
        let b = (self.v + self.u) * other.v_minus_u;
        let c = self.t1 * self.t2 * other.t2d;
        let d = self.z.double();

        CompletedPoint {
            u: b - a,
            v: b + a,
            z: d - c,
            t: d + c,
        }
        .into_extended()
    }
}

impl_binops_additive!(ExtendedPoint, AffineNielsPoint);

impl<'a, 'b> Add<&'b ExtendedPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[inline]
    fn add(self, other: &'b ExtendedPoint) -> ExtendedPoint {
        self + other.to_niels()
    }
}

impl<'a, 'b> Sub<&'b ExtendedPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[inline]
    fn sub(self, other: &'b ExtendedPoint) -> ExtendedPoint {
        self - other.to_niels()
    }
}

impl_binops_additive!(ExtendedPoint, ExtendedPoint);

impl<'a, 'b> Add<&'b AffinePoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[inline]
    fn add(self, other: &'b AffinePoint) -> ExtendedPoint {
        self + other.to_niels()
    }
}

impl<'a, 'b> Sub<&'b AffinePoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[inline]
    fn sub(self, other: &'b AffinePoint) -> ExtendedPoint {
        self - other.to_niels()
    }
}

impl_binops_additive!(ExtendedPoint, AffinePoint);

impl<'a, 'b> Add<&'b AffinePoint> for &'a AffinePoint {
    type Output = AffinePoint;

    #[inline]
    fn add(self, other: &'b AffinePoint) -> AffinePoint {
        (self.to_extended() + &other.to_extended()).into()
    }
}

impl<'a, 'b> Sub<&'b AffinePoint> for &'a AffinePoint {
    type Output = AffinePoint;

    #[inline]
    fn sub(self, other: &'b AffinePoint) -> AffinePoint {
        (self.to_extended() - &other.to_extended()).into()
    }
}

impl_binops_additive!(AffinePoint, AffinePoint);

/// This is a "completed" point produced during a point doubling or
/// addition routine. These points exist in the `(U:Z, V:T)` model
/// of the curve. This is not exposed in the API because it is
/// an implementation detail.
struct CompletedPoint {
    u: Fq,
    v: Fq,
    z: Fq,
    t: Fq,
}

impl CompletedPoint {
    /// This converts a completed point into an extended point by
    /// homogenizing:
    ///
    /// (u/z, v/t) = (u/z * t/t, v/t * z/z) = (ut/zt, vz/zt)
    ///
    /// The resulting T coordinate is utvz/zt = uv, and so
    /// T1 = u, T2 = v, without loss of generality.
    #[inline]
    fn into_extended(self) -> ExtendedPoint {
        ExtendedPoint {
            u: self.u * self.t,
            v: self.v * self.z,
            z: self.z * self.t,
            t1: self.u,
            t2: self.v,
        }
    }
}

impl Default for AffinePoint {
    /// Returns the identity.
    fn default() -> AffinePoint {
        AffinePoint::identity()
    }
}

impl Default for ExtendedPoint {
    /// Returns the identity.
    fn default() -> ExtendedPoint {
        ExtendedPoint::identity()
    }
}

/// This takes a mutable slice of `ExtendedPoint`s and "normalizes" them using
/// only a single inversion for the entire batch. This normalization results in
/// all of the points having a Z-coordinate of one. Further, an iterator is
/// returned which can be used to obtain `AffinePoint`s for each element in the
/// slice.
///
/// This costs 5 multiplications per element, and a field inversion.
pub fn batch_normalize<'a>(v: &'a mut [ExtendedPoint]) -> impl Iterator<Item = AffinePoint> + 'a {
    // We use the `t1` field of `ExtendedPoint` for scratch space.
    BatchInverter::invert_with_internal_scratch(v, |p| &mut p.z, |p| &mut p.t1);

    for p in v.iter_mut() {
        let mut q = *p;
        let tmp = q.z;

        // Set the coordinates to the correct value
        q.u *= &tmp; // Multiply by 1/z
        q.v *= &tmp; // Multiply by 1/z
        q.z = Fq::one(); // z-coordinate is now one
        q.t1 = q.u;
        q.t2 = q.v;

        *p = q;
    }

    // All extended points are now normalized, but the type
    // doesn't encode this fact. Let us offer affine points
    // to the caller.

    v.iter().map(|p| AffinePoint { u: p.u, v: p.v })
}

impl<'a, 'b> Mul<&'b Fr> for &'a AffinePoint {
    type Output = ExtendedPoint;

    fn mul(self, other: &'b Fr) -> ExtendedPoint {
        self.to_niels().multiply(&other.to_bytes())
    }
}

impl_binops_multiplicative_mixed!(AffinePoint, Fr, ExtendedPoint);

/// This represents a point in the prime-order subgroup of Ed25519, in affine
/// coordinates.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SubgroupPointAffine(AffinePoint);

impl From<SubgroupPointAffine> for AffinePoint {
    fn from(val: SubgroupPointAffine) -> AffinePoint {
        val.0
    }
}

impl<'a> From<&'a SubgroupPointAffine> for &'a AffinePoint {
    fn from(val: &'a SubgroupPointAffine) -> &'a AffinePoint {
        &val.0
    }
}

impl fmt::Display for SubgroupPointAffine {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl ConditionallySelectable for SubgroupPointAffine {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        SubgroupPointAffine(AffinePoint::conditional_select(&a.0, &b.0, choice))
    }
}

impl SubgroupPointAffine {
    /// Constructs an AffinePoint given `u` and `v` without checking that the point is on
    /// the curve or in the prime-order subgroup.
    ///
    /// This should only be used for hard-coding constants (e.g. fixed generators); in all
    /// other cases, use [`SubgroupPointAffine::from_bytes`] instead.
    ///
    /// [`SubgroupPointAffine::from_bytes`]: SubgroupPointAffine#impl-GroupEncoding
    pub const fn from_raw_unchecked(u: Fq, v: Fq) -> Self {
        SubgroupPointAffine(AffinePoint::from_raw_unchecked(u, v))
    }
}

impl<T> Sum<T> for SubgroupPointAffine
where
    T: Borrow<SubgroupPointAffine>,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(SubgroupPointAffine(AffinePoint::identity()), |acc, item| {
            acc + item.borrow()
        })
    }
}

impl Neg for SubgroupPointAffine {
    type Output = SubgroupPointAffine;

    #[inline]
    fn neg(self) -> SubgroupPointAffine {
        SubgroupPointAffine(-self.0)
    }
}

impl Neg for &SubgroupPointAffine {
    type Output = SubgroupPointAffine;

    #[inline]
    fn neg(self) -> SubgroupPointAffine {
        SubgroupPointAffine(-self.0)
    }
}

impl<'a, 'b> Add<&'b SubgroupPointAffine> for &'a AffinePoint {
    type Output = AffinePoint;

    #[inline]
    fn add(self, other: &'b SubgroupPointAffine) -> AffinePoint {
        self + &other.0
    }
}

impl<'a, 'b> Sub<&'b SubgroupPointAffine> for &'a AffinePoint {
    type Output = AffinePoint;

    #[inline]
    fn sub(self, other: &'b SubgroupPointAffine) -> AffinePoint {
        self - &other.0
    }
}

impl_binops_additive!(AffinePoint, SubgroupPointAffine);

impl<'a, 'b> Add<&'b SubgroupPointAffine> for &'a SubgroupPointAffine {
    type Output = SubgroupPointAffine;

    #[inline]
    fn add(self, other: &'b SubgroupPointAffine) -> SubgroupPointAffine {
        SubgroupPointAffine(self.0 + &other.0)
    }
}

impl<'a, 'b> Sub<&'b SubgroupPointAffine> for &'a SubgroupPointAffine {
    type Output = SubgroupPointAffine;

    #[inline]
    fn sub(self, other: &'b SubgroupPointAffine) -> SubgroupPointAffine {
        SubgroupPointAffine(self.0 - &other.0)
    }
}

impl_binops_additive!(SubgroupPointAffine, SubgroupPointAffine);

/// This represents a point in the prime-order subgroup of Ed25519, in extended
/// coordinates.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SubgroupPoint(ExtendedPoint);

impl From<SubgroupPoint> for ExtendedPoint {
    fn from(val: SubgroupPoint) -> ExtendedPoint {
        val.0
    }
}

impl<'a> From<&'a SubgroupPoint> for &'a ExtendedPoint {
    fn from(val: &'a SubgroupPoint) -> &'a ExtendedPoint {
        &val.0
    }
}

impl fmt::Display for SubgroupPoint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl ConditionallySelectable for SubgroupPoint {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        SubgroupPoint(ExtendedPoint::conditional_select(&a.0, &b.0, choice))
    }
}

impl SubgroupPoint {
    /// Constructs an AffinePoint given `u` and `v` without checking that the point is on
    /// the curve or in the prime-order subgroup.
    ///
    /// This should only be used for hard-coding constants (e.g. fixed generators); in all
    /// other cases, use [`SubgroupPoint::from_bytes`] instead.
    ///
    /// [`SubgroupPoint::from_bytes`]: SubgroupPoint#impl-GroupEncoding
    pub const fn from_raw_unchecked(u: Fq, v: Fq) -> Self {
        SubgroupPoint(AffinePoint::from_raw_unchecked(u, v).to_extended())
    }

    /// This takes a mutable slice of `ExtendedPoint`s and "normalizes" them using
    /// only a single inversion for the entire batch. This normalization results in
    /// all of the points having a Z-coordinate of one. Further, an iterator is
    /// returned which can be used to obtain `AffinePoint`s for each element in the
    /// slice.
    ///
    /// This costs 5 multiplications per element, and a field inversion.
    fn batch_normalize(p: &[Self], q: &mut [SubgroupPointAffine]) {
        assert_eq!(p.len(), q.len());

        for (p, q) in p.iter().zip(q.iter_mut()) {
            // We use the `u` field of `AffinePoint` to store the z-coordinate being
            // inverted, and the `v` field for scratch space.
            q.0.u = p.0.z;
        }

        BatchInverter::invert_with_internal_scratch(q, |q| &mut q.0.u, |q| &mut q.0.v);

        for (p, q) in p.iter().zip(q.iter_mut()).rev() {
            let tmp = q.0.u;

            // Set the coordinates to the correct value
            q.0.u = p.0.u * &tmp; // Multiply by 1/z
            q.0.v = p.0.v * &tmp; // Multiply by 1/z
        }
    }
}

impl<T> Sum<T> for SubgroupPoint
where
    T: Borrow<SubgroupPoint>,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(Self::identity(), |acc, item| acc + item.borrow())
    }
}

impl Neg for SubgroupPoint {
    type Output = SubgroupPoint;

    #[inline]
    fn neg(self) -> SubgroupPoint {
        SubgroupPoint(-self.0)
    }
}

impl Neg for &SubgroupPoint {
    type Output = SubgroupPoint;

    #[inline]
    fn neg(self) -> SubgroupPoint {
        SubgroupPoint(-self.0)
    }
}

impl<'a, 'b> Add<&'b SubgroupPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[inline]
    fn add(self, other: &'b SubgroupPoint) -> ExtendedPoint {
        self + &other.0
    }
}

impl<'a, 'b> Sub<&'b SubgroupPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    #[inline]
    fn sub(self, other: &'b SubgroupPoint) -> ExtendedPoint {
        self - &other.0
    }
}

impl_binops_additive!(ExtendedPoint, SubgroupPoint);

impl<'a, 'b> Add<&'b SubgroupPoint> for &'a SubgroupPoint {
    type Output = SubgroupPoint;

    #[inline]
    fn add(self, other: &'b SubgroupPoint) -> SubgroupPoint {
        SubgroupPoint(self.0 + &other.0)
    }
}

impl<'a, 'b> Sub<&'b SubgroupPoint> for &'a SubgroupPoint {
    type Output = SubgroupPoint;

    #[inline]
    fn sub(self, other: &'b SubgroupPoint) -> SubgroupPoint {
        SubgroupPoint(self.0 - &other.0)
    }
}

impl_binops_additive!(SubgroupPoint, SubgroupPoint);

impl<'a, 'b> Add<&'b SubgroupPointAffine> for &'a SubgroupPoint {
    type Output = SubgroupPoint;

    #[inline]
    fn add(self, other: &'b SubgroupPointAffine) -> SubgroupPoint {
        SubgroupPoint(self.0 + other.0)
    }
}

impl<'a, 'b> Sub<&'b SubgroupPointAffine> for &'a SubgroupPoint {
    type Output = SubgroupPoint;

    #[inline]
    fn sub(self, other: &'b SubgroupPointAffine) -> SubgroupPoint {
        SubgroupPoint(self.0 - other.0)
    }
}

impl_binops_additive!(SubgroupPoint, SubgroupPointAffine);

impl<'a, 'b> Mul<&'b Fr> for &'a SubgroupPoint {
    type Output = SubgroupPoint;

    fn mul(self, other: &'b Fr) -> SubgroupPoint {
        SubgroupPoint(self.0 * other)
    }
}

impl_binops_multiplicative!(SubgroupPoint, Fr);

impl<'a, 'b> Mul<&'b Fr> for &'a SubgroupPointAffine {
    type Output = SubgroupPoint;

    fn mul(self, other: &'b Fr) -> SubgroupPoint {
        SubgroupPoint(self.0 * other)
    }
}

impl_binops_multiplicative_mixed!(SubgroupPointAffine, Fr, SubgroupPoint);

impl From<SubgroupPointAffine> for SubgroupPoint {
    fn from(affine: SubgroupPointAffine) -> SubgroupPoint {
        SubgroupPoint(affine.0.to_extended())
    }
}

impl<'a> From<&'a SubgroupPoint> for SubgroupPointAffine {
    fn from(extended: &'a SubgroupPoint) -> SubgroupPointAffine {
        SubgroupPointAffine(extended.0.to_affine())
    }
}

impl From<SubgroupPoint> for SubgroupPointAffine {
    fn from(extended: SubgroupPoint) -> SubgroupPointAffine {
        SubgroupPointAffine::from(extended.to_affine())
    }
}

impl Group for ExtendedPoint {
    type Scalar = Fr;

    fn random(mut rng: impl RngCore) -> Self {
        loop {
            let v = Fq::random(&mut rng);
            let flip_sign = rng.next_u32() % 2 != 0;

            // See AffinePoint::from_bytes for details.
            let v2 = v.square();
            let p = ((v2 - Fq::one())
                * ((Fq::one() + EDWARDS_D * v2).invert().unwrap_or(Fq::zero())))
            .sqrt()
            .map(|u| AffinePoint {
                u: if flip_sign { -u } else { u },
                v,
            });

            if p.is_some().into() {
                let p = p.unwrap().to_curve();

                if bool::from(!p.is_identity()) {
                    return p;
                }
            }
        }
    }

    fn identity() -> Self {
        Self::identity()
    }

    fn generator() -> Self {
        AffinePoint::generator().into()
    }

    fn is_identity(&self) -> Choice {
        self.is_identity()
    }

    #[must_use]
    fn double(&self) -> Self {
        self.double()
    }
}

impl Group for SubgroupPoint {
    type Scalar = Fr;

    fn random(mut rng: impl RngCore) -> Self {
        loop {
            let p = ExtendedPoint::random(&mut rng).clear_cofactor();

            if bool::from(!p.is_identity()) {
                return p;
            }
        }
    }

    fn identity() -> Self {
        SubgroupPoint(ExtendedPoint::identity())
    }

    fn generator() -> Self {
        SubgroupPointAffine::generator().into()
    }

    fn is_identity(&self) -> Choice {
        self.0.is_identity()
    }

    #[must_use]
    fn double(&self) -> Self {
        SubgroupPoint(self.0.double())
    }
}

#[cfg(feature = "alloc")]
impl WnafGroup for ExtendedPoint {
    fn recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
        // Copied from bls12_381::g1, should be updated.
        const RECOMMENDATIONS: [usize; 12] =
            [1, 3, 7, 20, 43, 120, 273, 563, 1630, 3128, 7933, 62569];

        let mut ret = 4;
        for r in &RECOMMENDATIONS {
            if num_scalars > *r {
                ret += 1;
            } else {
                break;
            }
        }

        ret
    }
}

impl PrimeGroup for SubgroupPoint {}

impl CofactorGroup for ExtendedPoint {
    type Subgroup = SubgroupPoint;

    fn clear_cofactor(&self) -> Self::Subgroup {
        SubgroupPoint(self.mul_by_cofactor())
    }

    fn into_subgroup(self) -> CtOption<Self::Subgroup> {
        CtOption::new(SubgroupPoint(self), self.is_torsion_free())
    }

    fn is_torsion_free(&self) -> Choice {
        self.is_torsion_free()
    }
}

impl Curve for SubgroupPoint {
    type AffineRepr = SubgroupPointAffine;

    fn batch_normalize(p: &[Self], q: &mut [Self::AffineRepr]) {
        Self::batch_normalize(p, q);
    }

    fn to_affine(&self) -> Self::AffineRepr {
        SubgroupPointAffine(self.0.into())
    }
}

impl Curve for ExtendedPoint {
    type AffineRepr = AffinePoint;

    fn batch_normalize(p: &[Self], q: &mut [Self::AffineRepr]) {
        Self::batch_normalize(p, q);
    }

    fn to_affine(&self) -> Self::AffineRepr {
        self.into()
    }
}

impl PrimeCurve for SubgroupPoint {
    type Affine = SubgroupPointAffine;
}

impl CofactorCurve for ExtendedPoint {
    type Affine = AffinePoint;
}

impl CofactorCurveAffine for AffinePoint {
    type Scalar = Fr;
    type Curve = ExtendedPoint;

    fn identity() -> Self {
        Self::identity()
    }

    fn generator() -> Self {
        // The point with the lowest positive v-coordinate and positive u-coordinate.
        AffinePoint {
            u: Fq::from_raw([
                0xfef6_e61f_01ae_05e2,
                0x1c0d_964b_dd30_bc07,
                0xf448_af58_b1ef_2831,
                0x68fe_bfd4_2613_608e,
            ]),
            v: Fq::from_raw([
                0x0000_0000_0000_0003,
                0x0000_0000_0000_0000,
                0x0000_0000_0000_0000,
                0x0000_0000_0000_0000,
            ]),
        }
    }

    fn is_identity(&self) -> Choice {
        self.is_identity()
    }

    fn to_curve(&self) -> Self::Curve {
        (*self).into()
    }
}

impl PrimeCurveAffine for SubgroupPointAffine {
    type Scalar = Fr;
    type Curve = SubgroupPoint;

    fn identity() -> Self {
        SubgroupPointAffine(AffinePoint::identity())
    }

    fn generator() -> Self {
        SubgroupPointAffine(AffinePoint {
            u: Fq::from_raw([
                0xc956_2d60_8f25_d51a,
                0x692c_c760_9525_a7b2,
                0xc0a4_e231_fdd6_dc5c,
                0x2169_36d3_cd6e_53fe,
            ]),
            v: Fq::from_raw([
                0x6666_6666_6666_6658,
                0x6666_6666_6666_6666,
                0x6666_6666_6666_6666,
                0x6666_6666_6666_6666,
            ]),
        })
    }

    fn is_identity(&self) -> Choice {
        self.0.is_identity()
    }

    fn to_curve(&self) -> Self::Curve {
        (*self).into()
    }
}

impl GroupEncoding for ExtendedPoint {
    type Repr = [u8; 32];

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        AffinePoint::from_bytes(*bytes).map(Self::from)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        // We can't avoid curve checks when parsing a compressed encoding.
        AffinePoint::from_bytes(*bytes).map(Self::from)
    }

    fn to_bytes(&self) -> Self::Repr {
        AffinePoint::from(self).to_bytes()
    }
}

impl GroupEncoding for SubgroupPoint {
    type Repr = [u8; 32];

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        ExtendedPoint::from_bytes(bytes).and_then(|p| p.into_subgroup())
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        ExtendedPoint::from_bytes_unchecked(bytes).map(SubgroupPoint)
    }

    fn to_bytes(&self) -> Self::Repr {
        self.0.to_bytes()
    }
}

impl GroupEncoding for AffinePoint {
    type Repr = [u8; 32];

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_bytes(*bytes)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_bytes(*bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        self.to_bytes()
    }
}

impl GroupEncoding for SubgroupPointAffine {
    type Repr = [u8; 32];

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        AffinePoint::from_bytes(*bytes).map(SubgroupPointAffine)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_bytes(&*bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        self.0.to_bytes()
    }
}

#[test]
fn test_is_on_curve_var() {
    assert!(AffinePoint::identity().is_on_curve_vartime());
}

#[test]
fn test_d_is_non_quadratic_residue() {
    assert!(bool::from(EDWARDS_D.sqrt().is_none()));
    assert!(bool::from((-EDWARDS_D).sqrt().is_none()));
    assert!(bool::from((-EDWARDS_D).invert().unwrap().sqrt().is_none()));
}

#[test]
fn test_affine_niels_point_identity() {
    assert_eq!(
        AffineNielsPoint::identity().v_plus_u,
        AffinePoint::identity().to_niels().v_plus_u
    );
    assert_eq!(
        AffineNielsPoint::identity().v_minus_u,
        AffinePoint::identity().to_niels().v_minus_u
    );
    assert_eq!(
        AffineNielsPoint::identity().t2d,
        AffinePoint::identity().to_niels().t2d
    );
}

#[test]
fn test_extended_niels_point_identity() {
    assert_eq!(
        ExtendedNielsPoint::identity().v_plus_u,
        ExtendedPoint::identity().to_niels().v_plus_u
    );
    assert_eq!(
        ExtendedNielsPoint::identity().v_minus_u,
        ExtendedPoint::identity().to_niels().v_minus_u
    );
    assert_eq!(
        ExtendedNielsPoint::identity().z,
        ExtendedPoint::identity().to_niels().z
    );
    assert_eq!(
        ExtendedNielsPoint::identity().t2d,
        ExtendedPoint::identity().to_niels().t2d
    );
}

#[test]
fn test_assoc() {
    let p = ExtendedPoint::from(AffinePoint {
        u: Fq::from_raw([
            0x4eb5_31fa_487c_0f3e,
            0x1313_5118_1c90_b35e,
            0xdb9a_afaf_f32a_26f7,
            0x5e0c_b226_a2aa_bab4,
        ]),
        v: Fq::from_raw([
            0xbf09_6275_684b_b8c9,
            0xc7ba_2458_90af_256d,
            0x5911_9f3e_8638_0eb0,
            0x3793_de18_2f9f_b1d2,
        ]),
    })
    .mul_by_cofactor();
    assert!(p.is_on_curve_vartime());

    assert_eq!(
        (p * Fr::from(1000u64)) * Fr::from(3938u64),
        p * (Fr::from(1000u64) * Fr::from(3938u64)),
    );
}

#[test]
fn test_batch_normalize() {
    let mut p = ExtendedPoint::from(AffinePoint {
        u: Fq::from_raw([
            0x4eb5_31fa_487c_0f3e,
            0x1313_5118_1c90_b35e,
            0xdb9a_afaf_f32a_26f7,
            0x5e0c_b226_a2aa_bab4,
        ]),
        v: Fq::from_raw([
            0xbf09_6275_684b_b8c9,
            0xc7ba_2458_90af_256d,
            0x5911_9f3e_8638_0eb0,
            0x3793_de18_2f9f_b1d2,
        ]),
    })
    .mul_by_cofactor();

    let mut v = vec![];
    for _ in 0..10 {
        v.push(p);
        p = p.double();
    }

    for p in &v {
        assert!(p.is_on_curve_vartime());
    }

    let expected: std::vec::Vec<_> = v.iter().map(|p| AffinePoint::from(*p)).collect();
    let mut result0 = vec![AffinePoint::identity(); v.len()];
    ExtendedPoint::batch_normalize(&v, &mut result0);
    for i in 0..10 {
        assert!(expected[i] == result0[i]);
    }
    let result1: std::vec::Vec<_> = batch_normalize(&mut v).collect();
    for i in 0..10 {
        assert!(expected[i] == result1[i]);
        assert!(v[i].is_on_curve_vartime());
        assert!(AffinePoint::from(v[i]) == expected[i]);
    }
    let result2: std::vec::Vec<_> = batch_normalize(&mut v).collect();
    for i in 0..10 {
        assert!(expected[i] == result2[i]);
        assert!(v[i].is_on_curve_vartime());
        assert!(AffinePoint::from(v[i]) == expected[i]);
    }
}

#[cfg(test)]
const FULL_GENERATOR: AffinePoint = AffinePoint::from_raw_unchecked(
    Fq::from_raw([
        0xfef6_e61f_01ae_05e2,
        0x1c0d_964b_dd30_bc07,
        0xf448_af58_b1ef_2831,
        0x68fe_bfd4_2613_608e,
    ]),
    Fq::from_raw([
        0x0000_0000_0000_0003,
        0x0000_0000_0000_0000,
        0x0000_0000_0000_0000,
        0x0000_0000_0000_0000,
    ]),
);

#[cfg(test)]
const EIGHT_TORSION: [AffinePoint; 8] = [
    AffinePoint::from_raw_unchecked(
        Fq::from_raw([
            0xdea1_4646_c545_d14a,
            0x5c19_3c70_13e5_e238,
            0xe933_9932_38de_4abb,
            0x1fd5_b9a0_0639_4a28,
        ]),
        Fq::from_raw([
            0x4fd8_4d3d_706a_17c7,
            0x0f67_100d_760b_3cba,
            0xc6cc_392c_fa53_202a,
            0x7a03_ac92_77fd_c74e,
        ]),
    ),
    AffinePoint::from_raw_unchecked(
        Fq::from_raw([
            0x3b11_e4d8_b5f1_5f3d,
            0xd0bc_e7f9_52d0_1b87,
            0xd4b2_ff66_c204_2858,
            0x547c_db7f_b03e_20f4,
        ]),
        Fq::from_raw([0x0, 0x0, 0x0, 0x0]),
    ),
    AffinePoint::from_raw_unchecked(
        Fq::from_raw([
            0xdea1_4646_c545_d14a,
            0x5c19_3c70_13e5_e238,
            0xe933_9932_38de_4abb,
            0x1fd5_b9a0_0639_4a28,
        ]),
        Fq::from_raw([
            0xb027_b2c2_8f95_e826,
            0xf098_eff2_89f4_c345,
            0x3933_c6d3_05ac_dfd5,
            0x05fc_536d_8802_38b1,
        ]),
    ),
    AffinePoint::from_raw_unchecked(
        Fq::from_raw([0x0, 0x0, 0x0, 0x0]),
        Fq::from_raw([
            0xffff_ffff_ffff_ffec,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
            0x7fff_ffff_ffff_ffff,
        ]),
    ),
    AffinePoint::from_raw_unchecked(
        Fq::from_raw([
            0x215e_b9b9_3aba_2ea3,
            0xa3e6_c38f_ec1a_1dc7,
            0x16cc_66cd_c721_b544,
            0x602a_465f_f9c6_b5d7,
        ]),
        Fq::from_raw([
            0xb027_b2c2_8f95_e826,
            0xf098_eff2_89f4_c345,
            0x3933_c6d3_05ac_dfd5,
            0x05fc_536d_8802_38b1,
        ]),
    ),
    AffinePoint::from_raw_unchecked(
        Fq::from_raw([
            0xc4ee_1b27_4a0e_a0b0,
            0x2f43_1806_ad2f_e478,
            0x2b4d_0099_3dfb_d7a7,
            0x2b83_2480_4fc1_df0b,
        ]),
        Fq::from_raw([0x0, 0x0, 0x0, 0x0]),
    ),
    AffinePoint::from_raw_unchecked(
        Fq::from_raw([
            0x215e_b9b9_3aba_2ea3,
            0xa3e6_c38f_ec1a_1dc7,
            0x16cc_66cd_c721_b544,
            0x602a_465f_f9c6_b5d7,
        ]),
        Fq::from_raw([
            0x4fd8_4d3d_706a_17c7,
            0x0f67_100d_760b_3cba,
            0xc6cc_392c_fa53_202a,
            0x7a03_ac92_77fd_c74e,
        ]),
    ),
    AffinePoint::from_raw_unchecked(
        Fq::from_raw([0x0, 0x0, 0x0, 0x0]),
        Fq::from_raw([0x1, 0x0, 0x0, 0x0]),
    ),
];

#[test]
fn find_eight_torsion() {
    let g = ExtendedPoint::from(FULL_GENERATOR);
    assert!(!bool::from(g.is_small_order()));
    let g = g.multiply(&FR_MODULUS_BYTES);
    assert!(bool::from(g.is_small_order()));

    let mut cur = g;

    for (i, point) in EIGHT_TORSION.iter().enumerate() {
        let tmp = AffinePoint::from(cur);
        if &tmp != point {
            panic!("{}th torsion point should be {:?}", i, tmp);
        }

        cur += &g;
    }
}

#[test]
fn find_curve_generator() {
    let mut trial_bytes = [0; 32];
    for _ in 0..255 {
        let a = AffinePoint::from_bytes(trial_bytes);
        if bool::from(a.is_some()) {
            let a = a.unwrap();
            assert!(a.is_on_curve_vartime());
            let b = ExtendedPoint::from(a);
            let b = b.multiply(&FR_MODULUS_BYTES);
            assert!(bool::from(b.is_small_order()));
            let b = b.double();
            assert!(bool::from(b.is_small_order()));
            let b = b.double();
            assert!(bool::from(b.is_small_order()));
            if !bool::from(b.is_identity()) {
                let b = b.double();
                assert!(bool::from(b.is_small_order()));
                assert!(bool::from(b.is_identity()));
                assert_eq!(FULL_GENERATOR, a);
                assert_eq!(AffinePoint::generator(), a);
                assert!(bool::from(a.mul_by_cofactor().is_torsion_free()));
                return;
            }
        }

        trial_bytes[0] += 1;
    }

    panic!("should have found a generator of the curve");
}

#[test]
fn test_small_order() {
    for point in EIGHT_TORSION.iter() {
        assert!(bool::from(point.is_small_order()));
    }
}

#[test]
fn test_is_identity() {
    let a = EIGHT_TORSION[0].mul_by_cofactor();
    let b = EIGHT_TORSION[1].mul_by_cofactor();

    assert_eq!(a.u, b.u);
    assert_eq!(a.v, a.z);
    assert_eq!(b.v, b.z);
    assert!(a.v != b.v);
    assert!(a.z != b.z);

    assert!(bool::from(a.is_identity()));
    assert!(bool::from(b.is_identity()));

    for point in EIGHT_TORSION.iter() {
        assert!(bool::from(point.mul_by_cofactor().is_identity()));
    }
}

#[test]
fn test_mul_consistency() {
    let a = Fr([
        0x21e6_1211_d993_4f2e,
        0xa52c_058a_693c_3e07,
        0x9ccb_77bf_b12d_6360,
        0x07df_2470_ec94_398e,
    ]);
    let b = Fr([
        0x0333_6d1c_be19_dbe0,
        0x0153_618f_6156_a536,
        0x2604_c9e1_fc3c_6b15,
        0x04ae_581c_eb02_8720,
    ]);
    let c = Fr([
        0x25ed14d69372d06d,
        0xb0bd217bfd62f8c6,
        0xe33379990c2bfc55,
        0x0efa9973698a5168,
    ]);
    assert_eq!(a * b, c);
    let p = ExtendedPoint::from(AffinePoint {
        u: Fq::from_raw([
            0x4eb5_31fa_487c_0f3e,
            0x1313_5118_1c90_b35e,
            0xdb9a_afaf_f32a_26f7,
            0x5e0c_b226_a2aa_bab4,
        ]),
        v: Fq::from_raw([
            0xbf09_6275_684b_b8c9,
            0xc7ba_2458_90af_256d,
            0x5911_9f3e_8638_0eb0,
            0x3793_de18_2f9f_b1d2,
        ]),
    })
    .mul_by_cofactor();
    assert_eq!(p * c, (p * a) * b);

    // Test Mul implemented on ExtendedNielsPoint
    assert_eq!(p * c, (p.to_niels() * a) * b);
    assert_eq!(p.to_niels() * c, (p * a) * b);
    assert_eq!(p.to_niels() * c, (p.to_niels() * a) * b);

    // Test Mul implemented on AffineNielsPoint
    let p_affine_niels = AffinePoint::from(p).to_niels();
    assert_eq!(p * c, (p_affine_niels * a) * b);
    assert_eq!(p_affine_niels * c, (p * a) * b);
    assert_eq!(p_affine_niels * c, (p_affine_niels * a) * b);
}

#[test]
fn test_serialization_consistency() {
    let gen = FULL_GENERATOR.mul_by_cofactor();
    let mut p = gen;

    let v = vec![
        [
            128, 75, 145, 22, 45, 198, 54, 22, 139, 5, 170, 18, 242, 181, 255, 137, 122, 40, 252,
            206, 239, 186, 26, 12, 180, 90, 21, 7, 5, 105, 101, 21,
        ],
        [
            22, 68, 255, 19, 37, 194, 164, 164, 48, 73, 83, 157, 104, 113, 11, 139, 33, 1, 168,
            164, 43, 168, 127, 60, 211, 246, 247, 205, 114, 207, 207, 214,
        ],
        [
            26, 40, 198, 173, 58, 13, 240, 71, 152, 52, 118, 63, 62, 216, 93, 123, 150, 24, 85, 19,
            53, 240, 76, 19, 15, 35, 80, 0, 15, 242, 193, 79,
        ],
        [
            106, 49, 41, 77, 198, 110, 86, 106, 68, 215, 196, 172, 17, 99, 136, 147, 90, 79, 111,
            101, 55, 21, 75, 114, 201, 128, 58, 183, 207, 171, 131, 142,
        ],
        [
            83, 204, 47, 184, 47, 109, 146, 188, 16, 242, 89, 9, 152, 30, 220, 138, 96, 67, 31,
            217, 136, 187, 85, 238, 76, 255, 225, 214, 179, 213, 1, 19,
        ],
        [
            85, 234, 237, 136, 90, 166, 166, 118, 121, 156, 143, 148, 213, 183, 191, 0, 84, 207,
            210, 139, 167, 195, 89, 95, 72, 3, 178, 17, 196, 121, 15, 143,
        ],
        [
            179, 158, 36, 69, 163, 189, 43, 63, 214, 185, 184, 26, 122, 196, 124, 19, 20, 28, 15,
            174, 146, 143, 70, 71, 180, 82, 52, 217, 92, 188, 101, 198,
        ],
        [
            193, 167, 156, 153, 111, 189, 85, 216, 104, 222, 181, 74, 90, 71, 10, 252, 30, 111,
            213, 141, 50, 36, 111, 216, 246, 140, 99, 136, 108, 49, 28, 223,
        ],
        [
            255, 133, 189, 60, 50, 207, 110, 210, 92, 78, 175, 87, 218, 236, 87, 30, 163, 235, 54,
            44, 208, 179, 5, 76, 119, 41, 162, 210, 135, 233, 10, 30,
        ],
        [
            52, 88, 181, 170, 33, 179, 46, 231, 217, 188, 221, 113, 13, 57, 101, 186, 226, 45, 241,
            53, 213, 133, 169, 8, 107, 177, 22, 199, 23, 60, 98, 56,
        ],
        [
            25, 187, 217, 108, 38, 227, 219, 178, 39, 209, 185, 63, 196, 61, 115, 108, 178, 88,
            208, 100, 159, 88, 255, 176, 185, 181, 237, 22, 184, 161, 157, 201,
        ],
        [
            147, 23, 254, 240, 237, 224, 210, 124, 223, 229, 174, 125, 47, 234, 119, 27, 31, 138,
            225, 206, 222, 189, 153, 87, 186, 54, 27, 111, 231, 7, 51, 86,
        ],
        [
            82, 142, 113, 30, 167, 184, 63, 24, 254, 226, 48, 33, 119, 226, 107, 229, 22, 207, 237,
            139, 65, 142, 252, 197, 254, 39, 172, 106, 135, 151, 105, 64,
        ],
        [
            218, 137, 44, 241, 123, 52, 21, 229, 155, 197, 164, 81, 83, 201, 207, 249, 177, 50, 0,
            163, 209, 173, 175, 26, 186, 194, 39, 192, 213, 248, 4, 244,
        ],
        [
            31, 122, 52, 88, 131, 49, 13, 108, 251, 172, 7, 23, 101, 48, 0, 50, 218, 192, 124, 215,
            31, 9, 75, 45, 74, 10, 206, 10, 4, 242, 162, 209,
        ],
        [
            16, 72, 34, 66, 5, 147, 51, 4, 108, 81, 162, 153, 158, 139, 223, 120, 163, 49, 93, 41,
            186, 79, 14, 188, 60, 19, 186, 31, 114, 138, 70, 172,
        ],
    ];

    let batched = AffinePoint::batch_from_bytes(v.iter().cloned());

    for (expected_serialized, batch_deserialized) in v.into_iter().zip(batched.into_iter()) {
        assert!(p.is_on_curve_vartime());
        let affine = AffinePoint::from(p);
        let serialized = affine.to_bytes();
        let deserialized = AffinePoint::from_bytes(serialized).unwrap();
        assert_eq!(affine, deserialized);
        assert_eq!(affine, batch_deserialized.unwrap());
        assert_eq!(expected_serialized, serialized);
        p += gen;
    }
}

#[test]
fn test_zip_216() {
    const NON_CANONICAL_ENCODINGS: [[u8; 32]; 2] = [
        // (0, 1) with sign bit set to 1.
        [
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x80,
        ],
        // (0, -1) with sign bit set to 1.
        [
            0xec, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff,
        ],
    ];

    for b in &NON_CANONICAL_ENCODINGS {
        {
            let mut encoding = *b;

            // The normal API should reject the non-canonical encoding.
            assert!(bool::from(AffinePoint::from_bytes(encoding).is_none()));

            // If we clear the sign bit of the non-canonical encoding, it should be
            // accepted by the normal API.
            encoding[31] &= 0b0111_1111;
            assert!(bool::from(AffinePoint::from_bytes(encoding).is_some()));
        }

        {
            // The bug-preserving API should accept the non-canonical encoding, and the
            // resulting point should serialize to a different (canonical) encoding.
            let parsed = AffinePoint::from_bytes_pre_zip216_compatibility(*b).unwrap();
            let mut encoded = parsed.to_bytes();
            assert_ne!(b, &encoded);

            // If we set the sign bit of the serialized encoding, it should match the
            // non-canonical encoding.
            encoded[31] |= 0b1000_0000;
            assert_eq!(b, &encoded);
        }
    }
}
