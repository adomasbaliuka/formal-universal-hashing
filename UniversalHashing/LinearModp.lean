/-
  Carter–Wegman-style universal hash family.

  Main result: `linearHashFamily.universal2`
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import UniversalHashing.Basic

section LinearFamily

variable (p : ℕ) [Fact p.Prime]

/-- Index type: pairs (a, b) in (ZMod p)² with a ≠ 0. -/
abbrev LinearIndex : Type :=
  { ab : (ZMod p) × (ZMod p) // ab.1 ≠ 0 }

instance inst_fintypeLinearIndex : Fintype (LinearIndex p) := by
  unfold LinearIndex
  infer_instance

instance decidableEq_fintypeLinearIndex : DecidableEq (LinearIndex p) := by
  unfold LinearIndex
  infer_instance

/-
  Linear family over ZMod p:

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
/-
  Hash family ``H_1`` in [Wegman, Carter 1979](https://doi.org/10.1016/0022-0000(79)90044-8)).

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
  refine fun x y hxy => ?_;
  -- The set of pairs (a, b) where a * x + b = a * y + b is exactly the set where a = 0.
  have h_set : {i : LinearIndex p | linearHashFamily p i x = linearHashFamily p i y}
        = {i : LinearIndex p | i.val.1 * (x - y) = 0} := by
    simp  [mul_sub, sub_eq_zero, linearHashFamily]
  simp_all [Set.ext_iff]
  simp_all [sub_eq_zero]
  unfold probUniform
  simp_all only [Fintype.card_eq_zero, CharP.cast_eq_zero, Fintype.card_subtype_compl,
    Fintype.card_prod, ZMod.card, zero_div, inv_nonneg, Nat.cast_nonneg]

/- Universality of the `generalLinearHashFamily`, where inputs can be restricted. -/
theorem generalLinearHashFamily.universal2 {a : Nat} (alep : a ≤ p) :
    (generalLinearHashFamily p a).universal2 := by
  -- Let's choose any two distinct inputs, say x and y.
  intro x y hxy
  by_contra h_contra
  -- Since $x \neq y$, we have $x \neq y$ in $\mathbb{Z}/p\mathbb{Z}$.
  have hxy_ne : (x.val : ZMod p) ≠ (y.val : ZMod p) := by
    simp_all [Fin.ext_iff, ZMod.natCast_eq_natCast_iff']
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] <;> omega
  refine h_contra ?_
  convert ( linearHashFamily.universal2 p ) hxy_ne using 1

/- Counterexample: `linearHashFamily` is NOT strongly universal.
Proof by explicit computation for ``p = 2``.
-/
example : ¬ (linearHashFamily 2).stronglyUniversal := by
  simp [linearHashFamily, HashFamily.stronglyUniversal]
  simp [probUniform]
  use 3, 4
  constructor
  · decide
  · use 1, 2
    rw [show Fintype.card { x : ZMod 2 × ZMod 2 // x.1 = 0 } = 2 by decide]
    simp only [Nat.reduceSub, Nat.cast_ofNat]
    have : Fintype.card { i : LinearIndex 2
      // i.val.1 * 3 + i.val.2 = 1 ∧ i.val.1 * 4 + i.val.2 = 2 } = 1 := by decide
    rw [this]
    norm_num

end LinearFamily
