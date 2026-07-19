/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import UniversalHashing.ToeplitzNTT

/-!
# Unit tests for `ToeplitzNTT`

Exhaustive checks (over all seeds and inputs) that the NTT-based Toeplitz hash
`toeplitzHashNTT` agrees with the school-book `toeplitzHash` for small dimensions,
complementing the general theorem `toeplitzHashNTT_eq_toeplitzHash`.

Note that compiled calls to `toeplitzHashNTT` run `toeplitzHashNTTFast` (via the
`@[csimp]` theorem `toeplitzHashNTT_eq_fast`), so these tests exercise the fast
implementation's compiled code paths.
-/

set_option linter.hashCommand false

/-- Exhaustive agreement check of `toeplitzHashNTT m n` with `toeplitzHash m n`
over all `2 ^ (m + n - 1)` seeds and `2 ^ n` inputs. -/
def toeplitzNTTAgrees (m n : ℕ) : Bool :=
  (List.range (2 ^ (m + n - 1))).all fun p ↦
    (List.range (2 ^ n)).all fun xv ↦
      let param : BitVec (m + n - 1) := BitVec.ofNat _ p
      let x : BitVec n := BitVec.ofNat _ xv
      toeplitzHashNTT m n param x
        == BitVec.ofFnLE fun i : Fin m ↦
          decide (toeplitzHash m n param.toZMod2Fun x.toZMod2Fun i = 1)

-- The 3×4 example
#guard toeplitzNTTAgrees 3 4

-- Transposed shape.
#guard toeplitzNTTAgrees 4 3

-- Degenerate and small shapes.
#guard toeplitzNTTAgrees 1 1
#guard toeplitzNTTAgrees 1 5
#guard toeplitzNTTAgrees 5 1
#guard toeplitzNTTAgrees 4 4
#guard toeplitzNTTAgrees 0 0
