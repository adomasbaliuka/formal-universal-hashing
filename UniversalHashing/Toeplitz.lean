/-
This module defines Toeplitz matrices, i.e., matrices with constant diagonals.

Main result: `binToeplitz_mulVec_isUniversal2` shows that matrix-vector multiplication
with (binary) Toeplitz matrices is universal-2.
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace

import UniversalHashing.Basic

open scoped Nat

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

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

/-
The type of (finite-size) Toeplitz matrices
-/
def ToeplitzMatrix (m n : ℕ) (α : Type*) := {M : Matrix (Fin m) (Fin n) α // M.IsToeplitz}

/-
The type of binary Toeplitz matrices, equipped with a Fintype instance.
-/
abbrev BinToeplitzMatrix (m n : ℕ) := ToeplitzMatrix m n (ZMod 2)

/- The binary matrix ``\begin{pmatrix}  1 & 0 \\ 1 & 1 \end{pmatrix}`` is Toeplitz. -/
example : !![(1 : ZMod 2), 0,
              1,           1].IsToeplitz := by
  intro i j
  fin_cases i; fin_cases j
  repeat simp_all
  decide

/- The binary matrix ``\begin{pmatrix}  0 & 1 \\ 1 & 1 \end{pmatrix}`` is **NOT** Toeplitz
 because the main diagonal is not constant.-/
example : ¬ !![(0 : ZMod 2), 1;
                1,           1].IsToeplitz := by
  intro h
  have : !![(0 : ZMod 2), 1; 1, 1] 0 0 = 1 :=
      calc !![(0 : ZMod 2), 1; 1, 1] 0 0
      _ = !![(0 : ZMod 2), 1; 1, 1] 1 1 := by
          apply h
          simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.mod_succ, zero_add]
      _ = 1 := by dsimp
  have : !![(0 : ZMod 2), 1; 1, 1] 0 0 = 0 := by dsimp
  contradiction

theorem toeplitzAdd {R : Type*} [AddMonoid R] {m n : ℕ} (M M' : ToeplitzMatrix m n R) :
    (M.val + M'.val).IsToeplitz := by
  intros i i' j j' hij
  have hM : M.val i j = M.val i' j' := by
    apply M.property; exact hij
  have hM' : M'.val i j = M'.val i' j' := by
    apply M'.property; exact hij
  simp only [Matrix.add_apply, hM, hM']

theorem toeplitzSub {R : Type*} [AddGroup R] {m n : ℕ} (M M' : ToeplitzMatrix m n R) :
    (M.val - M'.val).IsToeplitz := by
  intros i i' j j' hij
  have hM : M.val i j = M.val i' j' := by
    apply M.property; exact hij
  have hM' : M'.val i j = M'.val i' j' := by
    apply M'.property; exact hij
  simp only [Matrix.sub_apply, hM, hM']

end DefToeplitz
section

/-
Extract the defining parameters (diagonal entries) of a Toeplitz matrix.
-/
def ToeplitzMatrix.to_params {F : Type*} {m n : ℕ} [NeZero m] [NeZero n]
    (M : ToeplitzMatrix m n F) :
    Fin (m + n - 1) → F :=
  fun k =>
    if h : k < n then
      M.val 0 ⟨n - 1 - k, lt_of_le_of_lt (Nat.sub_le _ _ ) (Nat.pred_lt ( NeZero.ne n))⟩
    else
      M.val ⟨k - (n - 1), by omega⟩ 0

/-
Construct a Toeplitz matrix from its defining parameters (diagonal entries).
-/
def ToeplitzMatrix.from_params {F : Type*} {m n : ℕ} (v : Fin (m + n - 1) → F)
    : ToeplitzMatrix m n F :=
  ⟨Matrix.of (fun i j ↦ v ⟨i.val + (n - 1) - j.val, by grind⟩),
   by
    intros i i' j j' hij
    simp only [Matrix.of_apply]
    grind⟩

/-
A Toeplitz matrix is uniquely represented by a parameter vector (containing diagonal entries).
-/
def ToeplitzMatrix.equiv_params {F : Type*} {m n : ℕ} [NeZero m] [NeZero n]
    : ToeplitzMatrix m n F ≃ (Fin (m + n - 1) → F) where
  toFun := ToeplitzMatrix.to_params
  invFun := ToeplitzMatrix.from_params
  left_inv := by
    intro M
    simp only [from_params, to_params]
    refine Subtype.eq ?_
    ext i j
    simp only [Matrix.of_apply]
    split_ifs <;> simp_all [Nat.sub_sub]
    · convert M.prop using 1
      rotate_left
      · exact ⟨0, NeZero.pos m⟩
      · exact i
      · exact ⟨n - (1 + (i + (n - 1) - j)), by omega⟩
      · exact j
      · simp at *
        exact Or.inl (by omega)
    · convert M.prop using 1
      rotate_left
      · exact ⟨i + (n - 1 ) - (j + ( n - 1)), by omega⟩
      · exact ⟨i, by linarith [Fin.is_lt i]⟩
      · exact 0
      · exact j
      simp only [add_comm, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.eta,
        Classical.imp_iff_left_iff]
      exact Or.inl (by omega)
  right_inv := by
    intro v; ext x; simp only [to_params, from_params, Matrix.of_apply, Fin.coe_ofNat_eq_mod,
      Nat.zero_mod, zero_add, tsub_zero]
    split_ifs <;> try omega
    · apply congr_arg
      apply Fin.ext
      apply Nat.sub_sub_self
      apply Nat.le_sub_one_of_lt
      linarith [Fin.is_lt x]
    · exact congr_arg _ (Fin.ext <| by norm_num; omega)

/- Note: instance computable but slow.
For actually computing cardinality, use `card_ToeplitzMatrix` instead. -/
instance inst_Fintype_ToeplitzMatrix {F : Type*} [Fintype F] [DecidableEq F] {m n : ℕ} :
    Fintype (ToeplitzMatrix m n F) := by
  unfold ToeplitzMatrix Matrix.IsToeplitz
  infer_instance

/-
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

-- TODO rename
theorem toeplitz_mulVec_surjective.extracted_1_6 {m n : ℕ}
    {u : Fin n → ZMod 2}
    (w : Fin m → ZMod 2)
    (hw : ∀ (p : Fin (m + n - 1) → ZMod 2), w ⬝ᵥ (ToeplitzMatrix.from_params p).val.mulVec u = 0)
    (k : Fin (m + n - 1)) :
    ∑ i : Fin m, ∑ j : Fin n, w i * u j * (if i.val + (n - 1) - j.val = k.val then 1 else 0) = 0
    := by
  specialize hw (fun l => if l = k then 1 else 0)
  unfold ToeplitzMatrix.from_params at hw; simp_all [Matrix.mulVec, dotProduct]
  convert hw using 1
  simp only [Fin.ext_iff, Finset.mul_sum _ _ _, mul_ite, mul_zero]

/-- The linear map sending Toeplitz parameters to matrix-vector products with `u`. -/
def ToeplitzMatrix.mulVecLinearMap {F : Type*} [Semiring F] {m n : ℕ} (u : Fin n → F) :
    (Fin (m + n - 1) → F) →ₗ[F] (Fin m → F) where
  toFun := fun p => (ToeplitzMatrix.from_params p).val.mulVec u
  map_add' := by
    intro x y; ext i
    simp [Matrix.mulVec, dotProduct, ToeplitzMatrix.from_params, add_mul]
    rw [← Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp [funext_iff, Matrix.mulVec, dotProduct, ToeplitzMatrix.from_params]
    intro i
    simp [Finset.mul_sum, mul_assoc]

/-- If a linear map into `Fin m → 𝕜` is not surjective, there is a nonzero vector
    orthogonal to its image. -/
lemma not_surjective_has_annihilator {m : ℕ} [NeZero m] {V : Type*} {𝕜 : Type*} [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (f : V →ₗ[𝕜] (Fin m → 𝕜)) (hf : ¬Function.Surjective f) :
    ∃ w : Fin m → 𝕜, w ≠ 0 ∧ ∀ v, w ⬝ᵥ f v = 0 := by
  -- The range of f is a proper subspace.
  have h_proper : LinearMap.range f ≠ ⊤ := by
    rw [Ne, LinearMap.range_eq_top]
    intro h_surj
    apply hf
    intro y
    obtain ⟨x, hx⟩ := h_surj y
    exact ⟨x, hx⟩
  -- Pick a vector outside the range.
  obtain ⟨x, hx⟩ : ∃ x : Fin m → 𝕜, x ∉ LinearMap.range f :=
    not_forall.mp fun h => h_proper <| eq_top_iff.mpr fun x _ => h x
  -- Get a nonzero linear functional vanishing on the range.
  obtain ⟨φ, hφ_wx, hφ_range⟩ := Submodule.exists_le_ker_of_notMem hx
  -- Represent φ as dot product with some vector w'.
  obtain ⟨w, hw⟩ : ∃ w : Fin m → 𝕜, ∀ y : Fin m → 𝕜, φ y = w ⬝ᵥ y := by
    use fun i => φ (Pi.single i 1)
    intro y
    erw [φ.pi_apply_eq_sum_univ]
    simp only [dotProduct, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]; congr; ext j; aesop
  refine ⟨w, fun h => hφ_wx (by simp [h, hw]), fun v => ?_⟩
  have hmem : f v ∈ LinearMap.range f := LinearMap.mem_range.mpr ⟨v, rfl⟩
  have := LinearMap.mem_ker.mp (hφ_range hmem)
  simpa [hw] using this

/-- If `w ≠ 0` and `u ≠ 0`, the diagonal sums cannot all be zero: there exists a diagonal index
    `k` at which `∑ i ∑ j, w i * u j * (if i+(n-1)-j = k then 1 else 0) ≠ 0`. -/
lemma toeplitz_diag_sum_not_all_zero {m n : ℕ} [NeZero m]
    (w : Fin m → ZMod 2) (u : Fin n → ZMod 2) (hw : w ≠ 0) (hu : u ≠ 0) :
    ∃ k : Fin (m + n - 1),
      ∑ i : Fin m, ∑ j : Fin n,
        w i * u j * (if i.val + (n - 1) - j.val = k.val then 1 else 0) ≠ 0 := by
  -- Let k be the smallest index in w that is non-zero.
  obtain ⟨k, hk_ne, hk_min⟩ : ∃ k : Fin m, w k ≠ 0 ∧ ∀ j : Fin m, j < k → w j = 0 := by
    set s := Finset.univ.filter (fun i : Fin m => w i ≠ 0) with hs_def
    have hS_nonempty : s.Nonempty := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    refine ⟨s.min' hS_nonempty,
            (Finset.mem_filter.mp (s.min'_mem hS_nonempty)).2,
            fun j hj => Classical.not_not.1 fun hj' => ?_⟩
    exact absurd hj (Finset.min'_le s j
      (hs_def ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩) |>.not_gt)
  -- Let l be the largest index in u that is non-zero.
  obtain ⟨l, hl_ne, hl_max⟩ : ∃ l : Fin n, u l ≠ 0 ∧ ∀ j : Fin n, j > l → u j = 0 := by
    obtain ⟨l, hl⟩ : ∃ l : Fin n, u l ≠ 0 :=
      Function.ne_iff.mp hu |>.imp fun x hx => by simpa using hx
    set s := Finset.univ.filter (fun j : Fin n => u j ≠ 0) with hs_def
    have hS_nonempty : s.Nonempty :=
      ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩⟩
    refine ⟨s.max' hS_nonempty,
            (Finset.mem_filter.mp (s.max'_mem hS_nonempty)).2,
            fun j hj => Classical.not_not.1 fun hj' => ?_⟩
    exact absurd hj (Finset.le_max' s j
      (hs_def ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩) |>.not_gt)
  -- The witness is the diagonal index k + (n-1) - l.
  refine ⟨⟨k.val + (n - 1) - l.val, by omega⟩, ?_⟩
  rw [Finset.sum_eq_single k]
  · -- Inner sum: only j = l contributes.
    rw [Finset.sum_eq_single l]
    · simp_all +decide
    · intro j _ hj_ne
      -- The if-condition k+(n-1)-j = k+(n-1)-l forces j = l, contradicting hj_ne.
      have hne : k.val + (n - 1) - j.val ≠ k.val + (n - 1) - l.val := by
        intro h; apply hj_ne; apply Fin.ext; omega
      simp [hne]
    · simp_all +decide
  · -- Terms with b ≠ k vanish: w b = 0 (since b < k by minimality) or the if fails.
    intro b _ hb_ne
    rw [Finset.sum_eq_zero]
    intro j _
    simp_all [Fin.ext_iff]
    grind
  · simp_all

/-
Multiplication by a non-zero vector is a surjective map
from the space of Toeplitz parameters to the output space.
-/
theorem toeplitz_mulVec_surjective (m : ℕ) {n : ℕ} [NeZero m]
    {u : Fin n → ZMod 2} (hu : u ≠ 0) :
    Function.Surjective (fun (p : Fin (m + n - 1) → ZMod 2) =>
        (ToeplitzMatrix.from_params p).val.mulVec u) := by
  by_contra h_not_surjective
  obtain ⟨w, hw_ne, hw_zero⟩ :=
    not_surjective_has_annihilator (ToeplitzMatrix.mulVecLinearMap u) h_not_surjective
  obtain ⟨k, hk⟩ := toeplitz_diag_sum_not_all_zero w u hw_ne hu
  exact hk (toeplitz_mulVec_surjective.extracted_1_6 w hw_zero k)

theorem surjective_toeplitz_mulVec_of_ne_zero (m : ℕ) {n : ℕ} [NeZero m] [NeZero n]
    {v : Fin n → ZMod 2} (h_nonzero : v ≠ 0) :
    Function.Surjective (fun (M : BinToeplitzMatrix m n) ↦ M.val.mulVec v) := by
  convert toeplitz_mulVec_surjective m h_nonzero using 1
  constructor <;> intro h
  · exact toeplitz_mulVec_surjective m h_nonzero
  · intro x
    obtain ⟨p, hp⟩ := h x
    grind

/-
Main result:
Multiplication by a random binary Toeplitz matrix is a universal-2 hash family.
-/
theorem binToeplitz_mulVec_isUniversal2 (m n : ℕ) [NeZero m] [NeZero n] :
    HashFamily.universal2 (fun (M : BinToeplitzMatrix m n) (v : Fin n → ZMod 2) => M.val.mulVec v)
    := by
  intro v w hvw
  -- Since the map is surjective, the number of matrices M such that
  -- M.mulVec v = 0
  -- is at most the total number of matrices divided by the size of the codomain.
  have h_card :
        (Finset.univ.filter (fun M : BinToeplitzMatrix m n => M.val.mulVec (v - w) = 0)).card
        ≤ Fintype.card (BinToeplitzMatrix m n) / Fintype.card (Fin m → ZMod 2) := by
    have : ∀ y : Fin m → ZMod 2,
        (Finset.univ.filter (fun M : BinToeplitzMatrix m n => M.val.mulVec (v - w) = y)).card
        = (Finset.univ.filter (fun M : BinToeplitzMatrix m n => M.val.mulVec (v - w) = 0)).card
        := by
      intro y
      obtain ⟨M, hM⟩ := surjective_toeplitz_mulVec_of_ne_zero m (sub_ne_zero_of_ne hvw) y
      rw [Finset.card_filter, Finset.card_filter]
      apply Finset.sum_bij (fun M' _ => ⟨M'.val - M.val, toeplitzSub M' M⟩)
      · intros
        simp_all only [ne_eq, Finset.mem_univ]
      · simp only [Finset.mem_univ, forall_const]
        intro _ _ h
        apply Subtype.ext
        simpa using congr_arg Subtype.val h
      · intro b hb
        use ⟨b.val + M.val, by
          intro i i' j j' hij
          simp_all only [ne_eq, Matrix.IsToeplitz, Finset.mem_univ, Matrix.add_apply]
          apply congr_arg₂ (· + ·) (b.2 (by aesop) ) ( M.2 (by aesop))⟩
        aesop
      · simp_all [sub_eq_iff_eq_add, Matrix.sub_mulVec]
    have h_card :
        (Finset.univ : Finset (BinToeplitzMatrix m n)).card
         = ∑ y : Fin m → ZMod 2, (Finset.univ.filter (fun M : BinToeplitzMatrix m n
            => M.val.mulVec (v - w) = y)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_fiberwise]
    simp_all only [ne_eq, Finset.card_univ, Finset.sum_const, Fintype.card_pi, ZMod.card,
        Finset.prod_const, Fintype.card_fin, smul_eq_mul, Nat.pow_eq_zero, OfNat.ofNat_ne_zero,
        false_and, not_false_eq_true, mul_div_cancel_left₀, le_refl]
  rw [Nat.le_div_iff_mul_le] at h_card <;> norm_num [Fintype.card_pi] at *
  simp_all only [Matrix.mulVec_sub, sub_eq_iff_eq_add, zero_add]
  exact h_card

/- Toeplitz hash, expressed using only bit vectors. -/
def toeplitzHash (m n : ℕ) :
    (HashFamily (Fin (m + n - 1) → ZMod 2) (Fin n → ZMod 2) (Fin m → ZMod 2))
    := fun param v ↦
  (ToeplitzMatrix.from_params param).val.mulVec v

theorem toeplitzHash.universal2 (m n : ℕ) [NeZero m] [NeZero n] :
    (toeplitzHash m n).universal2 := by
  have bij : (ToeplitzMatrix.from_params (m:=m) (n:=n) (F:=ZMod 2)).Bijective :=
    ToeplitzMatrix.equiv_params.symm.bijective
  have : toeplitzHash m n
    = (fun (M : BinToeplitzMatrix m n) v ↦ M.val.mulVec v) ∘ ToeplitzMatrix.from_params := rfl
  have := (HashFamily.universal2_of_comp_bijective
    (fun (M : BinToeplitzMatrix m n) v ↦ M.val.mulVec v) bij)
  simp_all [binToeplitz_mulVec_isUniversal2, Multiset.bijective_iff_map_univ_eq_univ]

theorem Nat.ne_rat_ge1_of_lt1 (n : ℕ) (q : ℚ) (nne0 : n > 0) (qlt1 : q < 1) : n ≠ q := by aesop

/- Counterexample: `toeplitzHash` is **NOT** in general strongly universal.
Proof by explicit computation, mapping two-bit vectors to 1-bit vectors.
-/
example : ¬ (toeplitzHash 2 1).stronglyUniversal2 := by
  simp only [toeplitzHash, HashFamily.stronglyUniversal2]
  push_neg
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
