# Universal hashing in LEAN4
[![Lean Action CI](https://github.com/adomasbaliuka/formal-universal-hashing/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/adomasbaliuka/formal-universal-hashing/actions/workflows/lean_action_ci.yml)

This is a work in progress related to [formal-qkd](https://github.com/adomasbaliuka/formal-qkd).

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

# Documentation

See [Preliminary, auto-generated API-docs](https://adomasbaliuka.github.io/formal-universal-hashing/docs/)

# Roadmap

- [ ] Definitions of universal hashing
  + [x] Universal-2 (e.g. [Carter, Wegman 1979](https://doi.org/10.1016/0022-0000(79)90044-8))
  + [x] Strongly-universal
  + [x] Strongly-universal-n (e.g. [Wegman, Carter 1981](https://doi.org/10.1016/0022-0000(81)90033-7))
  + [x] ε-almost universal-2
  + [x] ε-almost strongly universal-2
  + [ ] XOR-universal
  + [ ] ε-almost-Δ-universal (e.g. [Halevi, Krawczyk 2006](https://doi.org/10.1007/BFb0052345))
- [ ] Proofs
  + [x] "all functions" is universal-2 (toy example)
  + [x] "matrix-vector multiplication mod 2 using all binary matrices" is universal-2 (toy example)
  + [x] "matrix-vector multiplication mod 2 using binary [Toeplitz matrices](https://en.wikipedia.org/wiki/Toeplitz_matrix)" is universal-2
  + [x] `mx + n mod p` (for prime `p` and `m, n < p` ) is universal-2.
    (a version of family $H_1$ from [Carter, Wegman 1979](https://doi.org/10.1016/0022-0000(79)90044-8))
- [ ] Implementations 
  + [x] number-theoretic-transform-based fast binary Toeplitz matrix-vector multiplication 
        (`n` bits to `m` bits, only implemented for `m + n - 1 < 2 ^ 29`)
  + [ ] `mx + n mod p` using Schönhage–Strassen algorithm (maybe no need, can just use native `Nat`, which uses GMP?)

# Acknowledgements

Many thanks to the [Mathlib](https://mathlib.org/) community for developing the LEAN4 mathematics library which serves as a foundation for this project.

Thanks to [Harmonic](https://aristotle.harmonic.fun) for free API access to their proving tools.

# AI Use

This project is developed with the help of artificial intelligence.
In particular,

- [Aristotle by Harmonic](https://aristotle.harmonic.fun) created the first working version of many proofs.
- Claude code is used in the process of refactoring proofs.

For use with artificial intelligence, a system such as LEAN4 has the significant advantage of much reduced work in reviewing the output, due to proofs being checked by the LEAN4 kernel.
Nevertheless, care must be taken that the AI does not run mallicious code, does not formalize the wrong thing and does not "cheat" in proofs (cheating can be prevented by using [Comparator](https://github.com/leanprover/comparator)).

To address these issues,

- All definitions (especially of e.g. universality-properties) are either written without AI or carefully reviewed manually.
- Statements of main theorems (`public` and/or mentioned in section docstrings) are also carefully reviewed manually
- Proofs are not always human-reviewed in detail as long as they look reasonable.
  They are refactored to conform to Mathlib conventions and to be more readable than raw AI output.
