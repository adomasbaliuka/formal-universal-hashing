/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Tactic.Linarith.Frontend

/-! # Toeplitz Matrices
This module defines Toeplitz matrices, i.e., matrices with constant diagonals.
-/

open scoped Nat

section DefToeplitz

/-- A (finite) m×n matrix is ***Toeplitz** if all diagonals are constant. -/
def Matrix.IsToeplitz {m n : ℕ} {α : Type*} (M : Matrix (Fin m) (Fin n) α) : Prop :=
  ∀ {i i': Fin m}, ∀ {j j' : Fin n},
  i.val + j'.val = j.val + i'.val
  → M i j = M i' j'

instance decidablePredMatrixIsToeplitz {m n : ℕ} {α : Type*} [DecidableEq α] :
    DecidablePred (fun M : Matrix (Fin m) (Fin n) α ↦ M.IsToeplitz) := by
  unfold Matrix.IsToeplitz
  infer_instance

/--
The type of (finite-size) Toeplitz matrices
-/
def ToeplitzMatrix (m n : ℕ) (α : Type*) := {M : Matrix (Fin m) (Fin n) α // M.IsToeplitz}

/--
The type of binary Toeplitz matrices, equipped with a Fintype instance.
-/
abbrev BinToeplitzMatrix (m n : ℕ) := ToeplitzMatrix m n (ZMod 2)

protected theorem Matrix.IsToeplitz.add {R : Type*} [Add R] {m n : ℕ}
    {M M' : Matrix (Fin m) (Fin n) R}
    (hM : M.IsToeplitz) (hM' : M'.IsToeplitz) : (M + M').IsToeplitz :=
  fun {i i' j j'} hij => by simp only [Matrix.add_apply, hM hij, hM' hij]

protected theorem Matrix.IsToeplitz.sub {R : Type*} [Sub R] {m n : ℕ}
    {M M' : Matrix (Fin m) (Fin n) R}
    (hM : M.IsToeplitz) (hM' : M'.IsToeplitz) : (M - M').IsToeplitz :=
  fun {i i' j j'} hij => by simp only [Matrix.sub_apply, hM hij, hM' hij]

theorem toeplitzAdd {R : Type*} [AddMonoid R] {m n : ℕ} (M M' : ToeplitzMatrix m n R) :
    (M.val + M'.val).IsToeplitz :=
  Matrix.IsToeplitz.add M.property M'.property

theorem toeplitzSub {R : Type*} [AddGroup R] {m n : ℕ} (M M' : ToeplitzMatrix m n R) :
    (M.val - M'.val).IsToeplitz :=
  Matrix.IsToeplitz.sub M.property M'.property

end DefToeplitz

/--
Extract the defining parameters (diagonal entries) of a Toeplitz matrix.
-/
def ToeplitzMatrix.to_params {F : Type*} {m n : ℕ} [NeZero m] [NeZero n]
    (M : ToeplitzMatrix m n F) :
    Fin (m + n - 1) → F :=
  fun k =>
    if h : k < n then
      M.val 0 ⟨n - 1 - k, by omega⟩
    else
      M.val ⟨k - (n - 1), by omega⟩ 0

/--
Construct a Toeplitz matrix from its defining parameters (diagonal entries).
-/
def ToeplitzMatrix.from_params {F : Type*} {m n : ℕ} (v : Fin (m + n - 1) → F) :
    ToeplitzMatrix m n F :=
  ⟨Matrix.of (fun i j ↦ v ⟨i.val + (n - 1) - j.val, by grind⟩),
   by
    intros i i' j j' hij
    simp only [Matrix.of_apply]
    grind⟩

/--
A Toeplitz matrix is uniquely represented by a parameter vector (containing diagonal entries).
-/
def ToeplitzMatrix.equiv_params {F : Type*} {m n : ℕ} [NeZero m] [NeZero n]
    : ToeplitzMatrix m n F ≃ (Fin (m + n - 1) → F) where
  toFun := ToeplitzMatrix.to_params
  invFun := ToeplitzMatrix.from_params
  left_inv := by
    intro M
    simp only [from_params, to_params]
    apply Subtype.ext
    ext i j
    simp only [Matrix.of_apply]
    split_ifs <;> simp_all only [Nat.sub_sub] <;> apply M.prop
    · change (0 : ℕ) + j.val = n - (1 + (i.val + (n - 1) - j.val)) + i.val
      omega
    · change i.val + (n - 1) - (j.val + (n - 1)) + j.val = (0 : ℕ) + i.val
      omega
  right_inv := by
    intro v
    ext x
    simp only [to_params, from_params, Matrix.of_apply, Fin.coe_ofNat_eq_mod,
      Nat.zero_mod, zero_add, tsub_zero]
    split_ifs
    · apply congr_arg
      ext
      apply Nat.sub_sub_self
      apply Nat.le_sub_one_of_lt
      linarith
    · exact congr_arg _ (Fin.ext <| by norm_num; omega)

/-- Note: instance computable but slow.
For actually computing cardinality, use `card_ToeplitzMatrix` instead. -/
instance inst_Fintype_ToeplitzMatrix {F : Type*} [Fintype F] [DecidableEq F] {m n : ℕ} :
    Fintype (ToeplitzMatrix m n F) := by
  unfold ToeplitzMatrix Matrix.IsToeplitz
  infer_instance

/--
The number of `m x n` Toeplitz matrices with `Fintype` entries is `(EntryType.card) ^ (m + n - 1)`.
-/
theorem card_ToeplitzMatrix {F : Type*} [Fintype F] [DecidableEq F] {m n : ℕ} [NeZero m] [NeZero n]
    : Fintype.card (ToeplitzMatrix m n F) = (Fintype.card F) ^ (m + n - 1) := by
  have h_card : Fintype.card (ToeplitzMatrix m n F) = Fintype.card (Fin (m + n - 1) → F) := by
    exact Fintype.card_congr <| ToeplitzMatrix.equiv_params
  simp_all only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_BinToeplitzMatrix (m n : ℕ) [NeZero m] [NeZero n] :
    Fintype.card (BinToeplitzMatrix m n) = 2 ^ (m + n - 1) := card_ToeplitzMatrix

/-! # Surjectivity of Toeplitz matrix-vector multiplication
`M ↦ M * v` is surjective for `v ≠ 0`.
-/

/-- The diagonal indicator matrix (1 on diagonal k, 0 elsewhere) is Toeplitz. -/
theorem isToeplitz_diag {m n : ℕ} {F : Type*} [Zero F] [One F] (k : ℕ) :
    Matrix.IsToeplitz
      (Matrix.of (fun i j ↦ if i.val + (n - 1) - j.val = k then (1 : F) else 0) :
      Matrix (Fin m) (Fin n) F) := by
  intro i i' j j' hij
  simp only [Matrix.of_apply, show i.val + (n - 1) - j.val = i'.val + (n - 1) - j'.val by omega]

/-- A finite Finsupp linear combination of Toeplitz matrices is Toeplitz. -/
theorem isToeplitz_finsupp_linear_combination {F : Type*} [CommRing F] {m n : ℕ}
    (f : ToeplitzMatrix m n F →₀ F) :
    Matrix.IsToeplitz
      (Matrix.of (fun i j ↦ ∑ M ∈ f.support, f M * M.val i j) :
      Matrix (Fin m) (Fin n) F) := by
  intro i i' j j' hij
  simp only [Matrix.of_apply]
  exact Finset.sum_congr rfl fun M _ ↦ by rw [M.2 hij]

/-- Every linear functional on `Fin m → R` is represented by dot product with some vector. -/
theorem linearMap_eq_dotProduct {R : Type*} [CommSemiring R] {m : ℕ} (w : (Fin m → R) →ₗ[R] R) :
    ∃ v : Fin m → R, ∀ x : Fin m → R, w x = v ⬝ᵥ x := by
  use fun i ↦ w (Pi.single i 1)
  intro x
  convert w.pi_apply_eq_sum_univ x using 1
  simp only [dotProduct, mul_comm, smul_eq_mul]
  apply Finset.sum_congr rfl
  intros
  congr
  ext
  aesop

/-- If a submodule of `Fin m → F` is proper, there is a nonzero vector orthogonal to it. -/
theorem exists_dotProduct_annihilating {F : Type*} [Field F] {m : ℕ}
    {S : Submodule F (Fin m → F)} (hS : S ≠ ⊤) :
    ∃ v : Fin m → F, v ≠ 0 ∧ ∀ x ∈ S, v ⬝ᵥ x = 0 := by
  obtain ⟨y, hy⟩ : ∃ y : Fin m → F, y ∉ S := by simpa [Submodule.eq_top_iff'] using hS
  obtain ⟨w, hw₁, hw₂⟩ := Submodule.exists_le_ker_of_notMem hy
  obtain ⟨v, hv⟩ := linearMap_eq_dotProduct w
  use v
  exact ⟨fun h ↦ hw₁ (by simp [hv y, h]),
    fun x hx ↦ (hv x).symm.trans (LinearMap.mem_ker.mp (hw₂ hx))⟩

/-- The k-th coefficient of `(∑ wᵢ Xⁱ)(∑ uⱼ X^(n-1-j))` equals the dot product of `w`
    with the Toeplitz diagonal-k indicator matrix applied to `u`. -/
theorem toeplitz_poly_coeff {F : Type*} [Field F] {m n : ℕ}
    (w : Fin m → F) (u : Fin n → F) (k : ℕ) :
    Polynomial.coeff
        ((∑ i : Fin m, w i • (Polynomial.X : Polynomial F) ^ i.val) *
         (∑ j : Fin n, u j • Polynomial.X ^ (n - 1 - j.val))) k =
    w ⬝ᵥ (Matrix.of (fun i j ↦ if i.val + (n - 1) - j.val = k then (1 : F) else 0) :
        Matrix (Fin m) (Fin n) F).mulVec u := by
  simp only [Finset.sum_mul, Algebra.smul_mul_assoc, Polynomial.finsetSum_coeff,
    Polynomial.coeff_smul, Polynomial.coeff_mul, Polynomial.coeff_X_pow, smul_eq_mul, mul_ite,
    mul_one, mul_zero, ite_mul, one_mul, zero_mul, dotProduct, Matrix.mulVec, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one,
    Finset.sum_ite_eq', Finset.mem_range, mul_ite, mul_zero]
  split_ifs <;> simp_all only [Finset.mem_univ, mul_eq_mul_left_iff, not_lt, zero_eq_mul]
  · grind
  · exact Or.inr (Finset.sum_eq_zero fun j hj ↦ if_neg <| by omega)

/-- If all exponents in a finite sum `∑ cᵢ • X^(eᵢ)` are bounded by `B`,
    the sum has degree at most `B`. -/
theorem natDegree_finset_sum_smul_pow_le {F : Type*} [CommSemiring F] {ι : Type*}
    {s : Finset ι} (c : ι → F) (e : ι → ℕ) {B : ℕ} (hB : ∀ i ∈ s, e i ≤ B) :
    (∑ i ∈ s, c i • (Polynomial.X : Polynomial F) ^ e i).natDegree ≤ B :=
  (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun i hi ↦
    (Polynomial.natDegree_smul_le _ _).trans (Polynomial.natDegree_pow_le.trans
      ((Nat.mul_le_mul_left _ Polynomial.natDegree_X_le).trans (by linarith [hB i hi]))))

/-- Degree bound: a weighted sum of monomials `∑ c i • X^i` for `i : Fin m`
    has degree at most `m - 1`. -/
theorem natDegree_sum_smul_pow_le {F : Type*} [CommSemiring F] {m : ℕ} (c : Fin m → F) :
    (∑ i : Fin m, c i • (Polynomial.X : Polynomial F) ^ i.val).natDegree ≤ m - 1 :=
  natDegree_finset_sum_smul_pow_le c _ (by omega)

/-- Degree bound: a weighted sum of monomials `∑ c j • X^(n-1-j)` for `j : Fin n`
    has degree at most `n - 1`. -/
theorem natDegree_sum_smul_pow_rev_le {F : Type*} [CommSemiring F] {n : ℕ} (c : Fin n → F) :
    (∑ j : Fin n, c j • (Polynomial.X : Polynomial F) ^ (n - 1 - j.val)).natDegree ≤ n - 1 :=
  natDegree_finset_sum_smul_pow_le c _ (by omega)

/-- Multiplication by a nonzero vector is surjective from Toeplitz parameters to the output
    space. -/
theorem toeplitz_mulVec_surjective {F : Type*} [Field F] {m n : ℕ} [NeZero m] [NeZero n]
    {u : Fin n → F} (hu : u ≠ 0) :
    Function.Surjective (fun M : ToeplitzMatrix m n F ↦ M.val.mulVec u) := by
  by_contra h_not_surjective
  have h_span_ne_top : Submodule.span F
      (Set.range (fun M : ToeplitzMatrix m n F ↦ M.val.mulVec u)) ≠ ⊤ := by
    intro heq
    apply h_not_surjective fun x ↦ ?_
    have hx : x ∈ Submodule.span F (Set.range (fun M : ToeplitzMatrix m n F ↦ M.val.mulVec u)) :=
      heq ▸ Submodule.mem_top
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hx
    obtain ⟨f, hf⟩ := hx
    use ⟨Matrix.of (fun i j ↦ ∑ M ∈ f.support, f M * M.val i j),
      isToeplitz_finsupp_linear_combination f⟩
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ← hf, Finset.sum_mul, Finsupp.sum,
      Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul]
    exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ ↦ by rw [Finset.mul_sum]; ac_rfl)
  obtain ⟨w, hw_ne, hw_ann⟩ := exists_dotProduct_annihilating h_span_ne_top
  have h_matrix : ∀ k : Fin (m + n - 1), w ⬝ᵥ (
        Matrix.of (fun i j ↦ if i.val + (n - 1) - j.val = k.val then 1 else 0) :
        Matrix (Fin m) (Fin n) F).mulVec u = 0 :=
    fun k ↦ hw_ann _ (Submodule.subset_span
      (Set.mem_range_self (⟨_, isToeplitz_diag k.val⟩ : ToeplitzMatrix m n F)))
  set P : Polynomial F := ∑ i : Fin m, w i • Polynomial.X ^ (i.val)
  set Q : Polynomial F := ∑ j : Fin n, u j • Polynomial.X ^ (n - 1 - j.val)
  have h_poly_zero : P * Q = 0 := by
    ext k; by_cases hk : k < m + n - 1 <;>
      simp_all only [ne_eq, Polynomial.coeff_zero, not_lt, tsub_le_iff_right]
    · rw [toeplitz_poly_coeff w u k, h_matrix ⟨k, hk⟩]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
      apply lt_of_le_of_lt Polynomial.natDegree_mul_le
      linarith [Nat.sub_add_cancel (NeZero.pos m), Nat.sub_add_cancel (NeZero.pos n),
          natDegree_sum_smul_pow_le w, natDegree_sum_smul_pow_rev_le u]
  simp_all only [ne_eq, Polynomial.coeff_zero, mul_eq_zero, Polynomial.ext_iff]
  rcases h_poly_zero with h | h
  · simp +zetaDelta only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
        Polynomial.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero] at *
    exact hw_ne (funext fun i ↦ by simpa [Fin.val_inj] using h i)
  · simp +zetaDelta only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
        Polynomial.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero] at *
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
    specialize h (n - 1 - i)
    simp_all only [Pi.zero_apply, ne_eq, Finset.sum_ite, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_eq_single i] at h <;> simp_all only [not_true_eq_false, Finset.mem_filter,
      Finset.mem_univ, true_and, ne_eq, Fin.ext_iff, and_self, implies_true]
    intro j hj₁ hj₂
    rw [tsub_right_inj] at hj₁ <;> omega
