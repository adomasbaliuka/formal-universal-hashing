# Universal hashing in LEAN4
[![Lean Action CI](https://github.com/adomasbaliuka/formal-universal-hashing/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/adomasbaliuka/formal-universal-hashing/actions/workflows/lean_action_ci.yml)

This is a work in progress which may be merged into or become a dependency for [formal-qkd](https://github.com/adomasbaliuka/formal-qkd).

Contributions are very welcome!

> [!CAUTION]
> :warning: **Under no circumstances should this be used for applications relating to cybersecurity.** :warning:
> 
> This resource is made for educational and research purposes. It has not been reviewed by security experts and no claims relating to cybersecurity can be made about it or about other projects which use it.

# Background

This project develops definitions and [formal proofs](https://en.wikipedia.org/wiki/Formal_proof) (using the [LEAN4 proof assistant](https://en.wikipedia.org/wiki/Lean_(proof_assistant))) about [universal hashing](https://en.wikipedia.org/wiki/Universal_hashing).

Universal hashing refers to randomly selecting a hash function from a family of functions, or alternatively, using hash functions with a seed, to achieve certain properties concerning hash collisions.
Such functions can be used in hash tables, randomized algorithms and various cryptographic applications including [Wegman-Carter authentication](https://doi.org/10.1016/0022-0000(81)90033-7).

Definitions of universal hashing and related properties are not always consistent across the literature.
This repository aims to provide definitions and theorems about universal hashing  

# Roadmap

- [ ] Definitions of universal hashing
  + [x] Universal-2
  + [ ] Strongly-universal-n
  + [ ] ε-almost strongly universal
  + [ ] XOR-universal
- [ ] Proofs and implementations
  + [x] Proof: "all functions" is a universal-2 hash family
  + [x] Proof: matrix-vector multiplication mod 2 using "all binary matrices" is universal-2
  + [x] Proof: matrix-vector multiplication mod 2 using "binary [Toeplitz matrices](https://en.wikipedia.org/wiki/Toeplitz_matrix)" is universal-2
  + [ ] Fast implementation of binary Toeplitz matrix-vector multiplication

# Acknowledgements

Many thanks to the [Mathlib](https://mathlib.org/) community for developing the LEAN4 mathematics library. It serves as a foundation for this project.

This project is developed with the help of artificial inteligence.
In particular, [Aristotle by Harmonic](https://aristotle.harmonic.fun) created the first working version of many proofs.
For use with artificial inteligence, a system such as LEAN4 has the significant advantage of much reduced work in reviewing the output, due to proofs being checked by the LEAN4 kernel.
