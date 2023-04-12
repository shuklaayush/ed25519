# ed25519

This is a pure Rust implementation of the Ed25519 elliptic curve group and its associated fields.

* **This implementation has not been reviewed or audited. Use at your own risk.**
* This implementation targets Rust `1.60` or later.
* All operations are constant time unless explicitly noted.
* This implementation does not require the Rust standard library.

## Curve Description

Ed25519 is the [twisted Edwards curve](https://en.wikipedia.org/wiki/Twisted_Edwards_curve) `-u^2 + v^2 = 1 + d.u^2.v^2` of rational points over `GF(q)` with a subgroup of prime order `r` and cofactor `8`.

```
q = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed
r = 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed
d = -(121665/121666)
```

Ed25519 is birationally equivalent to a [Montgomery curve](https://en.wikipedia.org/wiki/Montgomery_curve) `y^2 = x^3 + Ax^2 + x` over the same field with `A = 40962`. The Montgomery curve and its quadratic twist have small cofactors `8` and `4`, respectively.

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.