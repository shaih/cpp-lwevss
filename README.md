# cpp-lwevss
C++ implementation of VSS using LWE encryption and proofs, as described in the article:

[Practical Non-interactive Publicly Verifiable Secret Sharing with Thousands of Parties](https://eprint.iacr.org/2021/1397), by Craig Gentry and Shai Halevi and Vadim Lyubashevsky, [Cryptology ePrint Archive](https://eprint.iacr.org): Report 2021/1397.

This implementation was written mostly by [Shai Halevi](https://alum.mit.edu/www/shaih).
It is a proof-of-concept and **is not suitable for use in production**.
The code is documented internally, and we made some effort to separate out performance-sensitive parts so they can be optimized on their own.

### Structure

This is a cmake project, but the directory structure tries to mimic Go conventions to some extent. Different subdirectories of `src` correspond roughly to what the Go packages would be. Current subdirectories are:

+ `25519` - wrapper around libsodium, namespace CRV25519. Provide classes `Point` and `Scalar`. See `point25519.hpp`, `scalar25519.hpp` in the include directory.

+ `algebra` - wrapper around NTL, namespace ALGEBRA. Should make using packages other than NTL in the future a little easier. See `algebra.hpp` in the include directory.

+ `dlproofs` - implementation of [Bulletproofs](https://crypto.stanford.edu/bulletproofs/)-like proofs, namespace DLPROOFS. Provides proofs for linear and quadratic constraints, as well as proving the norm-squared (mod P) of a vector. See `constraints.hpp` `pedersen.hpp` `bulletproof.hpp` in the includes directory.

* `tools` - currently contains only tools related to Shamir secret sharing, namespace TOOLS. See `shamir.hpp` in the includes directory.

+ `regev` - implementation of Regev encryption and proofs related to it, namespace REGEVENC. See `regevEnc.hpp` and `regevProofs.hpp` in the includes directory.

+ `libmerlin` - Henry de Valence's one-file "C" implementation of Merlin transcripts. Taken (with minor fixes) from https://github.com/hdevalence/libmerlin (commit 4bf6228), but separated the "c" and "h" files to different directories. A C++ wrapper found in `merlin.hpp` in the include directory.

### Dependencies

* [libsodium](https://github.com/jedisct1/libsodium) for implementation of arithmetic over Curve25519

* [NTL](https://libntl.org/) and [GMP](https://gmplib.org/) underlying operations for Regev encryption

### License

This implementation is provided under the MIT license

