/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace

public import UniversalHashing.Basic
public import UniversalHashing.DeltaUniversal
public import UniversalHashing.ToeplitzGeneral


/-!
This module defines a universal-2 hash by vector matrix multiplication with Toeplitz matrices.

Toeplitz matrices are defined in `ToeplitzGeneral.lean`.

Main results:
* `toeplitzModp_mulVec_isUniversal2` / `toeplitzHash.universal2`: matrix-vector
  multiplication with random Toeplitz matrices (over `ZMod p` / binary) is universal-2.
* `toeplitzModp_mulVec_deltaUniversal2` / `toeplitzHash.deltaUniversal2`: it is moreover
  **perfectly Δ-universal** (XOR-universal in the binary case): each difference value is
  attained with probability exactly `1 / |Output|`; `toeplitzHash.almostDeltaUniversal2`
  gives the resulting optimal-`ε` A∆U₂ statement.
* A counterexample showing `toeplitzHash` is **not** strongly universal
  (consistent with Δ-universality: `T · 0 = 0` always, so outputs are not uniform,
  but differences are).
-/

@[expose] public section


open scoped Nat

/--
Multiplication (mod p) by a random Toeplitz matrix is a **perfectly Δ-universal** hash
family: for distinct inputs `x ≠ y`, every difference value `b` is attained with
probability exactly `1 / p^m`.

By linearity the difference collapses to a single product, `M x − M y = M (x − y)`,
and for `d ≠ 0` the map `M ↦ M d` is a surjective linear map, so all its fibers are
translates of each other and have equal size.
-/
theorem toeplitzModp_mulVec_deltaUniversal2 (m n p : ℕ) [NeZero m] [NeZero n]
    [hp : Fact (Nat.Prime p)] :
    HashFamily.deltaUniversal2
      (fun (M : ToeplitzMatrix m n (ZMod p)) (v : Fin n → ZMod p) ↦ M.val.mulVec v) := by
  intro x y hxy b
  -- All fibers of `M ↦ M.val.mulVec (x - y)` have the same size as the kernel fiber.
  have hfib : ∀ c : Fin m → ZMod p,
      (Finset.univ.filter
        (fun M : ToeplitzMatrix m n (ZMod p) ↦ M.val.mulVec (x - y) = c)).card
      = (Finset.univ.filter
        (fun M : ToeplitzMatrix m n (ZMod p) ↦ M.val.mulVec (x - y) = 0)).card := by
    intro c
    obtain ⟨M, hM⟩ := toeplitz_mulVec_surjective (sub_ne_zero_of_ne hxy) c
    rw [Finset.card_filter, Finset.card_filter]
    apply Finset.sum_bij (fun M' _ ↦ ⟨M'.val - M.val, toeplitzSub M' M⟩)
    · intros
      simp_all only [ne_eq, Finset.mem_univ]
    · simp only [Finset.mem_univ, forall_const]
      intro _ _ h
      apply Subtype.ext
      simpa using congr_arg Subtype.val h
    · intro b' hb'
      use ⟨b'.val + M.val, by
        intro i i' j j' hij
        simp_all only [ne_eq, Matrix.IsToeplitz, Finset.mem_univ, Matrix.add_apply]
        apply congr_arg₂ (· + ·) (b'.2 (by aesop)) (M.2 (by aesop))⟩
      aesop
    · simp_all [sub_eq_iff_eq_add, Matrix.sub_mulVec]
  -- Summing the fibers over all values covers the whole seed space.
  have h_total :
      (Finset.univ : Finset (ToeplitzMatrix m n (ZMod p))).card
      = ∑ c : Fin m → ZMod p, (Finset.univ.filter
          (fun M : ToeplitzMatrix m n (ZMod p) ↦ M.val.mulVec (x - y) = c)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_fiberwise]
  have hcard : Fintype.card (ToeplitzMatrix m n (ZMod p))
      = Fintype.card (Fin m → ZMod p) * (Finset.univ.filter
          (fun M : ToeplitzMatrix m n (ZMod p) ↦ M.val.mulVec (x - y) = 0)).card := by
    rw [← Finset.card_univ, h_total, Finset.sum_congr rfl fun c _ ↦ hfib c]
    simp [Finset.sum_const, Finset.card_univ]
  have hseed_ne : Fintype.card (ToeplitzMatrix m n (ZMod p)) ≠ 0 :=
    @Fintype.card_ne_zero _ _ ⟨ToeplitzMatrix.from_params 0⟩
  have hfib_ne : ((Finset.univ.filter
      (fun M : ToeplitzMatrix m n (ZMod p) ↦ M.val.mulVec (x - y) = 0)).card : ℚ) ≠ 0 := by
    have := hseed_ne
    rw [hcard] at this
    exact_mod_cast right_ne_zero_of_mul this
  -- Rewrite the difference as a single matrix-vector product and compute.
  unfold probUniform
  rw [Fintype.card_subtype,
    Finset.filter_congr (fun M _ ↦ by rw [← Matrix.mulVec_sub]),
    hfib b, hcard]
  push_cast
  rw [mul_comm, div_mul_eq_div_div, div_self hfib_ne, one_div]

/--
Multiplication (mod p) by a random Toeplitz matrix is a universal-2 hash family.
Follows from perfect Δ-universality (`toeplitzModp_mulVec_deltaUniversal2`), of which
universal-2 is the `b = 0` special case.
-/
theorem toeplitzModp_mulVec_isUniversal2 (m n p : ℕ) [NeZero m] [NeZero n]
    [Fact (Nat.Prime p)] :
    HashFamily.universal2
      (fun (M : ToeplitzMatrix m n (ZMod p)) (v : Fin n → ZMod p) ↦ M.val.mulVec v) := by
  haveI : Nonempty (ToeplitzMatrix m n (ZMod p)) := ⟨ToeplitzMatrix.from_params 0⟩
  rw [HashFamily.universal2_iff_probUniform]
  exact HashFamily.almostUniversal2_of_almostDeltaUniversal2 _
    (HashFamily.almostDeltaUniversal2_of_deltaUniversal2 _
      (toeplitzModp_mulVec_deltaUniversal2 m n p))

/-- Toeplitz hash, expressed using only bit vectors. -/
def toeplitzHash (m n : ℕ) :
    (HashFamily (Fin (m + n - 1) → ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2))
    := fun param v ↦
  (ToeplitzMatrix.from_params param).val.mulVec v

/--
`toeplitzHash` is **perfectly Δ-universal** (XOR-universal): for distinct inputs,
every difference value is attained with probability exactly `1 / 2^m`.
Transported from `toeplitzModp_mulVec_deltaUniversal2` along the seed bijection
`ToeplitzMatrix.equiv_params`.
-/
theorem toeplitzHash.deltaUniversal2 (m n : ℕ) [NeZero m] [NeZero n] :
    (toeplitzHash m n).deltaUniversal2 := by
  intro x y hxy b
  exact (probUniform_comp_equiv ToeplitzMatrix.equiv_params.symm
      (fun M : BinToeplitzMatrix m n ↦ M.val.mulVec x - M.val.mulVec y = b)).trans
    (toeplitzModp_mulVec_deltaUniversal2 m n 2 hxy b)

/--
`toeplitzHash` is `(1 / 2^m)`-almost-Δ-universal — with the optimal parameter, since
`toeplitzHash.deltaUniversal2` attains the bound with equality.
-/
theorem toeplitzHash.almostDeltaUniversal2 (m n : ℕ) [NeZero m] [NeZero n] :
    (toeplitzHash m n).almostDeltaUniversal2
      ((1 : ℚ) / Fintype.card (Fin m → ZMod 2)) :=
  HashFamily.almostDeltaUniversal2_of_deltaUniversal2 _ (toeplitzHash.deltaUniversal2 m n)

/--
`toeplitzHash` is universal-2: the `b = 0` special case of `toeplitzHash.deltaUniversal2`.
-/
theorem toeplitzHash.universal2 (m n : ℕ) [NeZero m] [NeZero n] :
    (toeplitzHash m n).universal2 := by
  rw [HashFamily.universal2_iff_probUniform]
  exact HashFamily.almostUniversal2_of_almostDeltaUniversal2 _
    (toeplitzHash.almostDeltaUniversal2 m n)

theorem Nat.ne_rat_ge1_of_lt1 (n : ℕ) (q : ℚ) (nne0 : n > 0) (qlt1 : q < 1) : n ≠ q := by aesop

/-- Counterexample: `toeplitzHash` is **NOT** in general strongly universal.
Proof by explicit computation, mapping two-bit vectors to 1-bit vectors.
-/
example : ¬ (toeplitzHash 2 1).stronglyUniversal2 := by
  simp only [toeplitzHash, HashFamily.stronglyUniversal2]
  push Not
  use 0, 1
  refine ⟨not_eq_of_beq_eq_false rfl, ?_⟩
  simp only [Nat.reduceAdd, Nat.add_one_sub_one, Fintype.card_pi, ZMod.card, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Nat.reducePow, Nat.cast_ofNat, ne_eq]
  norm_num
  use 0, 1
  refine Nat.ne_rat_ge1_of_lt1 ?_ (1/4) ?_ ?_
  · decide
  · norm_num

end
