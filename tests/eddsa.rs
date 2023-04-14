use group::{cofactor::CofactorGroup, prime::PrimeCurveAffine, Group, GroupEncoding};
use rand_core::{RngCore, SeedableRng};
use rand_xorshift::XorShiftRng;
use sha2::{Digest, Sha512};
use subtle::Choice;

use ed25519::*;

fn hash_to_fr(hash: Sha512) -> Fr {
    let mut output = [0u8; 64];
    output.copy_from_slice(hash.finalize().as_slice());
    Fr::from_bytes_wide(&output)
}

fn seed_to_key(seed: [u8; 32]) -> (Fr, [u8; 32], [u8; 32]) {
    // Expand the seed to a 64-byte array with SHA512.
    let h = Sha512::digest(&seed[..]);

    // Convert the low half to a scalar with Ed25519 "clamping"
    let s = {
        let mut scalar_bytes = [0u8; 32];
        scalar_bytes[..].copy_from_slice(&h.as_slice()[0..32]);
        // Clear the lowest three bits to make the scalar a multiple of 8
        scalar_bytes[0] &= 248;
        // Clear highest bit
        scalar_bytes[31] &= 127;
        // Set second highest bit to 1
        scalar_bytes[31] |= 64;

        let mut scalar_bytes_wide = [0u8; 64];
        scalar_bytes_wide[0..32].copy_from_slice(&scalar_bytes);

        Fr::from_bytes_wide(&scalar_bytes_wide)
    };

    // Extract and cache the high half.
    let prefix = {
        let mut prefix = [0u8; 32];
        prefix[..].copy_from_slice(&h.as_slice()[32..64]);
        prefix
    };

    // Compute the public key as A = [s]B.
    // TODO: Allow reverse multiplication operation
    let A = SubgroupPoint::generator() * &s;

    let A_bytes = A.to_bytes();

    (s, prefix, A_bytes)
}

fn sign(s: Fr, prefix: [u8; 32], A_bytes: [u8; 32], msg: &[u8]) -> ([u8; 32], [u8; 32]) {
    let r = hash_to_fr(Sha512::default().chain(&prefix[..]).chain(msg));

    let R_bytes = (SubgroupPoint::generator() * &r).to_bytes();

    let k = hash_to_fr(
        Sha512::default()
            .chain(&R_bytes[..])
            .chain(&A_bytes[..])
            .chain(msg),
    );

    let s_bytes = (r + s * k).to_bytes();

    (s_bytes, R_bytes)
}

fn verify(s_bytes: [u8; 32], R_bytes: [u8; 32], A_bytes: [u8; 32], msg: &[u8]) -> Choice {
    let k = hash_to_fr(
        Sha512::default()
            .chain(&R_bytes[..])
            .chain(&A_bytes[..])
            .chain(msg),
    );
    verify_prehashed(s_bytes, R_bytes, A_bytes, k)
}

fn verify_prehashed(s_bytes: [u8; 32], R_bytes: [u8; 32], A_bytes: [u8; 32], k: Fr) -> Choice {
    // `s_bytes` MUST represent an integer less than the prime `l`.
    let s = Fr::from_bytes(&s_bytes).unwrap();
    // `R_bytes` MUST be an encoding of a point on the twisted Edwards form of Curve25519.
    let R = ExtendedPoint::from_bytes(&R_bytes).unwrap();
    // `A_bytes` MUST be an encoding of a point on the twisted Edwards form of Curve25519.
    let A = ExtendedPoint::from_bytes(&A_bytes).unwrap();

    //       [8][s]B = [8]R + [8][k]A
    // <=>   [8]R = [8][s]B - [8][k]A
    // <=>   0 = [8](R - ([s]B - [k]A))
    // <=>   0 = [8](R - R')  where R' = [s]B - [k]A
    let R_prime = ExtendedPoint::from(SubgroupPoint::generator()) * s - A * k;

    (R - R_prime).clear_cofactor().is_identity()
}

#[test]
fn eddsa_example() {
    let mut rng = XorShiftRng::from_seed([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]);

    let B = SubgroupPointAffine::generator();

    for _ in 0..1000 {
        // Generate a key pair
        let mut seed = [0u8; 32];
        rng.fill_bytes(&mut seed[..]);

        let (s, prefix, A_bytes) = seed_to_key(seed);

        // Generate a valid signature
        // Suppose `m` is the message
        let msg = b"test message";

        let (s_bytes, R_bytes) = sign(s, prefix, A_bytes, msg);

        // Verify the signature
        assert!(bool::from(verify(s_bytes, R_bytes, A_bytes, msg)));
    }
}

#[test]
fn test_vector_1() {
    let secret_key = [
        0x9d, 0x61, 0xb1, 0x9d, 0xef, 0xfd, 0x5a, 0x60, 0xba, 0x84, 0x4a, 0xf4, 0x92, 0xec, 0x2c,
        0xc4, 0x44, 0x49, 0xc5, 0x69, 0x7b, 0x32, 0x69, 0x19, 0x70, 0x3b, 0xac, 0x03, 0x1c, 0xae,
        0x7f, 0x60,
    ];
    let public_key = [
        0xd7, 0x5a, 0x98, 0x01, 0x82, 0xb1, 0x0a, 0xb7, 0xd5, 0x4b, 0xfe, 0xd3, 0xc9, 0x64, 0x07,
        0x3a, 0x0e, 0xe1, 0x72, 0xf3, 0xda, 0xa6, 0x23, 0x25, 0xaf, 0x02, 0x1a, 0x68, 0xf7, 0x07,
        0x51, 0x1a,
    ];
    let message = b"";
    let signature = [
        0xe5, 0x56, 0x43, 0x00, 0xc3, 0x60, 0xac, 0x72, 0x90, 0x86, 0xe2, 0xcc, 0x80, 0x6e, 0x82,
        0x8a, 0x84, 0x87, 0x7f, 0x1e, 0xb8, 0xe5, 0xd9, 0x74, 0xd8, 0x73, 0xe0, 0x65, 0x22, 0x49,
        0x01, 0x55, 0x5f, 0xb8, 0x82, 0x15, 0x90, 0xa3, 0x3b, 0xac, 0xc6, 0x1e, 0x39, 0x70, 0x1c,
        0xf9, 0xb4, 0x6b, 0xd2, 0x5b, 0xf5, 0xf0, 0x59, 0x5b, 0xbe, 0x24, 0x65, 0x51, 0x41, 0x43,
        0x8e, 0x7a, 0x10, 0x0b,
    ];

    let (s, prefix, A_bytes) = seed_to_key(secret_key);
    assert_eq!(A_bytes, public_key);

    let (s_bytes, R_bytes) = sign(s, prefix, A_bytes, message);

    let signature_bytes = {
        let mut sig = [0u8; 64];
        sig[..32].copy_from_slice(&R_bytes);
        sig[32..].copy_from_slice(&s_bytes);
        sig
    };

    assert_eq!(signature_bytes, signature);

    assert!(bool::from(verify(s_bytes, R_bytes, A_bytes, message)));
}

#[test]
fn test_vector_2() {
    let secret_key = [
        0x4c, 0xcd, 0x08, 0x9b, 0x28, 0xff, 0x96, 0xda, 0x9d, 0xb6, 0xc3, 0x46, 0xec, 0x11, 0x4e,
        0x0f, 0x5b, 0x8a, 0x31, 0x9f, 0x35, 0xab, 0xa6, 0x24, 0xda, 0x8c, 0xf6, 0xed, 0x4f, 0xb8,
        0xa6, 0xfb,
    ];
    let public_key = [
        0x3d, 0x40, 0x17, 0xc3, 0xe8, 0x43, 0x89, 0x5a, 0x92, 0xb7, 0x0a, 0xa7, 0x4d, 0x1b, 0x7e,
        0xbc, 0x9c, 0x98, 0x2c, 0xcf, 0x2e, 0xc4, 0x96, 0x8c, 0xc0, 0xcd, 0x55, 0xf1, 0x2a, 0xf4,
        0x66, 0x0c,
    ];
    let message: [u8; 1] = [0x72];
    let signature = [
        0x92, 0xa0, 0x09, 0xa9, 0xf0, 0xd4, 0xca, 0xb8, 0x72, 0x0e, 0x82, 0x0b, 0x5f, 0x64, 0x25,
        0x40, 0xa2, 0xb2, 0x7b, 0x54, 0x16, 0x50, 0x3f, 0x8f, 0xb3, 0x76, 0x22, 0x23, 0xeb, 0xdb,
        0x69, 0xda, 0x08, 0x5a, 0xc1, 0xe4, 0x3e, 0x15, 0x99, 0x6e, 0x45, 0x8f, 0x36, 0x13, 0xd0,
        0xf1, 0x1d, 0x8c, 0x38, 0x7b, 0x2e, 0xae, 0xb4, 0x30, 0x2a, 0xee, 0xb0, 0x0d, 0x29, 0x16,
        0x12, 0xbb, 0x0c, 0x00,
    ];

    let (s, prefix, A_bytes) = seed_to_key(secret_key);
    assert_eq!(A_bytes, public_key);

    let (s_bytes, R_bytes) = sign(s, prefix, A_bytes, &message);

    let signature_bytes = {
        let mut sig = [0u8; 64];
        sig[..32].copy_from_slice(&R_bytes);
        sig[32..].copy_from_slice(&s_bytes);
        sig
    };

    assert_eq!(signature_bytes, signature);

    assert!(bool::from(verify(s_bytes, R_bytes, A_bytes, &message)));
}
