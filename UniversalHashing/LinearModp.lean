/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import UniversalHashing.Basic

/-! # Carter–Wegman-style universal hash family.

  ``h_{a,b}(x) = a * x + b  (mod p),``

Main result: `linearHashFamily.universal2`
-/




section LinearFamily

variable (p : ℕ) [Fact p.Prime]

/-- Index type: pairs (a, b) in (ZMod p)² with a ≠ 0. -/
abbrev LinearIndex : Type :=
  {ab : (ZMod p) × (ZMod p) // ab.1 ≠ 0}

/-- Linear family over ZMod p:

  ``h_{a,b}(x) = a * x + b  (mod p),``

This is a special case of
family ``H_1`` in [Wegman, Carter 1979](https://doi.org/10.1016/0022-0000(79)90044-8)).

where:
* `p` is prime,
* `a ≠ 0` in `ZMod p`,
* `(a, b)` is chosen uniformly from (ZMod p)² with a ≠ 0.
-/
def linearHashFamily : HashFamily (LinearIndex p) (ZMod p) (ZMod p) :=
  fun i x ↦ i.val.1 * x + i.val.2

-- TODO rename
/-- Hash family ``H_1`` in [Wegman, Carter 1979](https://doi.org/10.1016/0022-0000(79)90044-8)).

    ``h_{a,b}(x) = a * x + b  (mod p),``

where:
* `p` is prime,
* `a ≠ 0` in `ZMod p`,
* `(a, b)` is chosen uniformly from (ZMod p)² with a ≠ 0.
* x < a

Note that `x` is automatically cast to ℕ and then to `ZMod p`, which involves a modulo operation.
The family is universal-2 for `a < p`.
-/
def generalLinearHashFamily (a : Nat) :
    HashFamily (LinearIndex p) (Fin a) (ZMod p) := fun i x ↦
  i.val.1 * (x : ZMod p) + i.val.2

/- Universality of the `linearHashFamily` -/
theorem linearHashFamily.universal2 :
    (linearHashFamily p).universal2 := by
  intro x y hxy
  have h_set : {i : LinearIndex p | linearHashFamily p i x = linearHashFamily p i y}
        = {i : LinearIndex p | i.val.1 * (x - y) = 0} := by
    simp [mul_sub, sub_eq_zero, linearHashFamily]
  simp_all only [ne_eq, mul_eq_zero, sub_eq_zero, or_false, Set.ext_iff, Set.mem_setOf_eq,
    Subtype.forall, iff_false, Prod.forall, Set.setOf_false, Fintype.card_eq_zero, ZMod.card,
    zero_mul, Fintype.card_subtype_compl, Fintype.card_prod, zero_le]

/-- Universality of the `generalLinearHashFamily`, where inputs can be restricted. -/
theorem generalLinearHashFamily.universal2 {a : Nat} (alep : a ≤ p) :
    (generalLinearHashFamily p a).universal2 := by
  intro x y hxy
  convert linearHashFamily.universal2 p (show (x : ZMod p) ≠ y from ?_) using 1
  · rfl
  simp_all only [ne_eq, Fin.ext_iff, ZMod.natCast_eq_natCast_iff']
  rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] <;> contrapose! hxy
    <;> linarith [Fin.is_lt x, Fin.is_lt y]

/--
Counterexample: `linearHashFamily` is NOT strongly universal.
Proof by explicit computation for ``p = 2``.
-/
example : ¬ (linearHashFamily 2).stronglyUniversal2 := by
  unfold HashFamily.stronglyUniversal2 linearHashFamily
  push Not
  use 3, 4
  constructor
  · decide
  · use 1, 2
    simp only [ne_eq, Fintype.card_subtype_compl, Fintype.card_prod, ZMod.card, Nat.reduceMul,
      Nat.cast_ofNat]
    rw [show Fintype.card {x : ZMod 2 × ZMod 2 // x.1 = 0} = 2 by decide]
    simp only [Nat.reduceSub, Nat.cast_ofNat]
    have : Fintype.card { i : LinearIndex 2
      // i.val.1 * 3 + i.val.2 = 1 ∧ i.val.1 * 4 + i.val.2 = 2 } = 1 := by decide
    rw [this]
    norm_num

end LinearFamily
