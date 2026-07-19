/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import UniversalHashing.BinConvolution.ConvolutionDefs

/-!
# Unit tests for `ConvolutionDefs`

Executable sanity checks for the NTT-based circular convolution
`circularConvolutionGf2` against the brute-force specification
`BitVec.circConvolutionBruteforce`.

The `#guard` commands run at elaboration time, so building this library
(`lake test`, which CI runs via `lean-action`) executes the tests; any failure
is a build error.

This file is deliberately NOT a `module`: `#guard` executes imported code
during elaboration, which in a `module` file would require `meta import`s of
every executed dependency. A plain file has no such phase split.
-/

set_option linter.hashCommand false

-- Known-answer test: convolution of small inputs, against a hand-computed result.
#guard 0b1111 == circularConvolutionGf2 (0b1100) (0b1010#4)

-- The brute-force specification agrees with the same hand-computed result.
#guard 0b1111 == BitVec.circConvolutionBruteforce 0b1100 0b1010#4

-- NTT implementation agrees with the brute-force specification on a
-- 101-bit input (odd length, exercises the zero-padding path).
#guard
  let a := 0b11000010010010#101
  let b := 0b01010101001001#101
  circularConvolutionGf2 a b == BitVec.circConvolutionBruteforce a b
