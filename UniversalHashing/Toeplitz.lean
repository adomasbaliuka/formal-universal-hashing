/-
This module defines Toeplitz matrices, i.e., matrices with constant diagonals.

Main result: `toeplitz_mulVec_isUniversal2` shows that matrix-vector multiplication
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

noncomputable section DefToeplitz

/-- A (finite) m×n matrix is ***Toeplitz** if all diagonals are constant. -/
def Matrix.IsToeplitz {m n : ℕ} {α : Type*} (M : Matrix (Fin m) (Fin n) α) : Prop :=
  ∀ {i i': Fin m}, ∀ {j j' : Fin n}, i.val + j'.val = j.val + i'.val → M i j = M i' j'

/-
The type of (finite-size) Toeplitz matrices
-/
def ToeplitzMatrix (m n : ℕ) (α : Type*) := { M : Matrix (Fin m) (Fin n) α // M.IsToeplitz }

/-
The type of binary Toeplitz matrices, equipped with a Fintype instance.
-/
def BinToeplitzMatrix (m n : ℕ) := ToeplitzMatrix m n (ZMod 2)

/- Note: do not use for computing cardinality, use `BinToeplitzMatrix.equiv_params` instead. -/
instance inst_Fintype_BinToeplitzMatrix {m n : ℕ} : Fintype (BinToeplitzMatrix m n) := by
  unfold BinToeplitzMatrix ToeplitzMatrix Matrix.IsToeplitz
  infer_instance

/- The binary matrix ``\begin{pmatrix}  1 & 0 \\ 1 & 1 \end{pmatrix}`` is Toeplitz. -/
example : !![(1 : ZMod 2), 0;
              1,           1].IsToeplitz := by
  intro i j
  fin_cases i <;> fin_cases j
  repeat simp_all

/- The binary matrix ``\begin{pmatrix}  0 & 1 \\ 1 & 1 \end{pmatrix}`` is NOT Toeplitz
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

end DefToeplitz
section

lemma toeplitzAdd {m n : ℕ} (M M' : BinToeplitzMatrix m n) : (M.val + M'.val).IsToeplitz := by
    intros i i' j j' hij
    have hM : M.val i j = M.val i' j' := by
      apply M.property; exact hij
    have hM' : M'.val i j = M'.val i' j' := by
      apply M'.property; exact hij
    simp only [Matrix.add_apply, hM, hM']

lemma toeplitzSub {m n : ℕ} (M M' : BinToeplitzMatrix m n) : (M.val - M'.val).IsToeplitz := by
  intros i i' j j' hij
  have hM : M.val i j = M.val i' j' := by
    apply M.property; exact hij
  have hM' : M'.val i j = M'.val i' j' := by
    apply M'.property; exact hij
  simp only [Matrix.sub_apply, hM, hM']

/-
Extract the defining parameters of a Toeplitz matrix.
-/
def BinToeplitzMatrix.to_params {m n : ℕ} [NeZero m] [NeZero n] (M : BinToeplitzMatrix m n)
    : Fin (m + n - 1) → ZMod 2 :=
  fun k =>
    if h : k < n then
      M.val 0 ⟨n - 1 - k, by
        exact lt_of_le_of_lt ( Nat.sub_le _ _ ) ( Nat.pred_lt ( NeZero.ne n ) )⟩
    else
      M.val ⟨k - (n - 1), by
        omega⟩ 0

/-
Construct a Toeplitz matrix from its defining parameters.
-/
def BinToeplitzMatrix.from_params {m n : ℕ} (v : Fin (m + n - 1) → ZMod 2)
    : BinToeplitzMatrix m n :=
  ⟨Matrix.of (fun i j =>
    let k := i.val + (n - 1) - j.val
    if h : k < m + n - 1 then v ⟨k, h⟩ else 0),
   by
     intros i i' j j' hij
     simp
     rw [show ( i : ℕ ) + ( n - 1 ) - j = i' + ( n - 1 ) - j' by omega]⟩

/-
The type of Toeplitz matrices is equivalent to the type of parameter vectors.
-/
def BinToeplitzMatrix.equiv_params {m n : ℕ} [NeZero m] [NeZero n]
    : BinToeplitzMatrix m n ≃ (Fin (m + n - 1) → ZMod 2) where
  toFun := BinToeplitzMatrix.to_params
  invFun := BinToeplitzMatrix.from_params
  left_inv := by
    -- To show that `from_params` is the left inverse of `to_params`,
    -- we need to show that applying `from_params` to the parameters obtained from `to_params`
    -- reconstructs the original matrix.
    intro M
    simp only [from_params, to_params]
    refine Subtype.eq ?_
    ext i j
    simp only [Matrix.of_apply]
    split_ifs <;> simp_all [Nat.sub_sub]
    · convert M.2 using 1
      rotate_left
      · exact ⟨0, NeZero.pos m⟩
      · exact i
      · exact ⟨n - ( 1 + ( i + ( n - 1 ) - j ) ), by omega⟩
      · exact j
      · simp +zetaDelta at *
        exact Or.inl ( by omega )
    · convert M.2 using 1
      rotate_left
      · exact ⟨i + ( n - 1 ) - ( j + ( n - 1 ) ), by omega⟩
      · exact ⟨i, by linarith [Fin.is_lt i]⟩
      · exact 0
      · exact j
      simp only [add_comm, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.eta,
        Classical.imp_iff_left_iff]
      exact Or.inl ( by omega )
    · omega
  right_inv := by
    intro v; ext x; simp only [to_params, from_params, Matrix.of_apply, Fin.coe_ofNat_eq_mod,
      Nat.zero_mod, zero_add, tsub_zero]
    split_ifs <;> try omega
    · apply congr_arg
      apply Fin.ext
      apply Nat.sub_sub_self
      apply Nat.le_sub_one_of_lt
      linarith [Fin.is_lt x]
    · exact congr_arg _ ( Fin.ext <| by norm_num; omega )

/-
The number of m x n Toeplitz matrices is 2^(m+n-1).
-/
lemma card_BinToeplitzMatrix {m n : ℕ} [NeZero m] [NeZero n]
    : Fintype.card (BinToeplitzMatrix m n) = 2 ^ (m + n - 1) := by
  have h_card : Fintype.card (BinToeplitzMatrix m n) = Fintype.card (Fin (m + n - 1) → ZMod 2) := by
    exact Fintype.card_congr <| BinToeplitzMatrix.equiv_params
  simp_all only [Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]


lemma toeplitz_mulVec_surjective.extracted_1_6 {m n : ℕ}
    {u : Fin n → ZMod 2}
    (w : Fin m → ZMod 2)
    (hw : ∀ (p : Fin (m + n - 1) → ZMod 2), w ⬝ᵥ (BinToeplitzMatrix.from_params p).val.mulVec u = 0)
    (k : Fin (m + n - 1)) :
    ∑ i : Fin m, ∑ j : Fin n, w i * u j * (if i.val + (n - 1) - j.val = k.val then 1 else 0) = 0
    := by
  specialize hw (fun l => if l = k then 1 else 0)
  unfold BinToeplitzMatrix.from_params at hw; simp_all [Matrix.mulVec, dotProduct]
  convert hw using 1
  simp only [Fin.ext_iff, dite_eq_ite, Finset.mul_sum _ _ _, mul_ite, mul_zero]
  exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by
    split_ifs <;> norm_num ; omega

/-
Multiplication by a non-zero vector is a surjective map
from the space of Toeplitz parameters to the output space.
-/
lemma toeplitz_mulVec_surjective {m n : ℕ} [NeZero m] [NeZero n]
    {u : Fin n → ZMod 2} (hu : u ≠ 0) :
    Function.Surjective (fun (p : Fin (m + n - 1) → ZMod 2) =>
        (BinToeplitzMatrix.from_params p).val.mulVec u) := by
  -- For any $c \in \mathbb{F}_2^m$, we need to find $p \in \mathbb{F}_2^{m+n-1}$
  -- such that $(BinToeplitzMatrix.from_params p).mulVec u = c$.
  intro c
  by_contra h_contra
  -- There exists a non-zero vector $w \in \mathbb{F}_2^m$
  -- such that $w^T (M(p) u) = 0$ for all $p$.
  obtain ⟨w, hw_ne_zero, hw⟩ : ∃ w : Fin m → ZMod 2, w ≠ 0 ∧ ∀ p :
      Fin (m + n - 1) → ZMod 2, w ⬝ᵥ (BinToeplitzMatrix.from_params p).val.mulVec u = 0 := by
    -- Let $S$ be the subspace of $\mathbb{F}_2^m$
    -- spanned by the vectors $(BinToeplitzMatrix.from_params p).mulVec u$ for all $p$.
    set S : Submodule (ZMod 2) (Fin m → ZMod 2) := Submodule.span (ZMod 2)
      (Set.range (fun p : Fin (m + n - 1) → ZMod 2
          => (BinToeplitzMatrix.from_params p).val.mulVec u))
    -- Since $c \notin S$, there exists a linear functional $f$ on $\mathbb{F}_2^m$
    -- such that $f(c) \neq 0$ and $f(s) = 0$ for all $s \in S$.
    obtain ⟨f, hf⟩ : ∃ f : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2, f c ≠ 0 ∧ ∀ s ∈ S, f s = 0 := by
      have h_not_in_S : c ∉ S := by
        intro hc
        rw [Finsupp.mem_span_range_iff_exists_finsupp] at hc
        obtain ⟨p, rfl⟩ := hc
        refine h_contra ⟨p.sum fun i a => a • i, ?_⟩
        ext i
        simp only [Matrix.mulVec, dotProduct, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul]
        simp only [Finset.mul_sum _ _ _, mul_left_comm]
        simp only [BinToeplitzMatrix.from_params, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.of_apply, dite_mul, zero_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> simp [*, mul_comm, mul_left_comm,
          Finset.mul_sum _ _ _]
      exact Submodule.exists_le_ker_of_notMem h_not_in_S
    -- Let $w$ be the vector corresponding to the linear functional $f$.
    obtain ⟨w, hw⟩ : ∃ w : Fin m → ZMod 2, ∀ v : Fin m → ZMod 2, f v = w ⬝ᵥ v := by
      use fun i => f (Pi.single i 1)
      intro v; rw [f.pi_apply_eq_sum_univ] ; simp only [smul_eq_mul, dotProduct]
      exact Finset.sum_congr rfl fun i _ => by
        rw [mul_comm] ; congr; ext j
        simp_all only [ne_eq, not_exists, Finset.mem_univ, S]
        obtain ⟨left, right⟩ := hf
        split
        next h =>
          subst h
          simp_all only [Pi.single_eq_same]
        next h => simp_all only [ne_eq, not_false_eq_true, Pi.single_eq_of_ne']
    simp_all only [ne_eq, not_exists, S]
    obtain ⟨left, right⟩ := hf
    apply Exists.intro
    · apply And.intro
      on_goal 1 => apply Aesop.BuiltinRules.not_intro
      on_goal 1 => intro a
      on_goal 2 => intro p
      on_goal 2 => apply right
      · simp_all only [zero_dotProduct, not_true_eq_false]
      · apply Submodule.mem_span_of_mem
        simp_all only [Set.mem_range, exists_apply_eq_apply]
  -- Let $W(x) = \sum_{i=0}^{m-1} w_i x^i$ and $U_{rev}(x) = \sum_{j=0}^{n-1} u_j x^{n-1-j}$.
  set W : Polynomial (ZMod 2) := Finset.sum Finset.univ fun i => w i • Polynomial.X ^ i.val
  set U_rev : Polynomial (ZMod 2) :=
      Finset.sum Finset.univ fun j => u j • Polynomial.X ^ (n - 1 - j.val)
  -- Since $W(x) * U_{rev}(x) = 0$, and $U_{rev}(x) \neq 0$, it follows that $W(x) = 0$.
  have h_W_zero : W * U_rev = 0 := by
    ext k
    by_cases hk : k < m + n - 1
    · simp +zetaDelta at *
      -- Let $k = i-j$. The coefficient of $p_k$ is $\sum_{i-j=k} w_i u_j$.
      convert (toeplitz_mulVec_surjective.extracted_1_6 w hw) ⟨k, hk⟩ using 1
      simp only [Finset.sum_mul, Algebra.smul_mul_assoc, Polynomial.finset_sum_coeff,
        Polynomial.coeff_smul, Polynomial.coeff_mul, Polynomial.coeff_X_pow, smul_eq_mul, mul_ite,
        mul_one, mul_zero, ite_mul, one_mul, zero_mul]
      simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.mul_sum _ _ _]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.sum_sigma']
      refine Finset.sum_bij ( fun x hx => x.snd ) ?_ ?_ ?_ ?_ <;> simp
      · intros; omega
      · intro a₁ a a_1 a_2 a₂ a_3 a_4 a_5 a_6
        subst a
        simp_all only [Finset.mem_univ]
        obtain ⟨fst, snd⟩ := a₁
        obtain ⟨fst_1, snd_1⟩ := a₂
        obtain ⟨fst, snd_2⟩ := fst
        obtain ⟨fst_1, snd_3⟩ := fst_1
        subst a_6 a_4 a_1
        simp_all only
      · intro j hj
        rw [← hj, Nat.add_sub_assoc ( Nat.le_sub_one_of_lt ( Fin.is_lt j ) )]
    · simp +zetaDelta at *
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
      refine lt_of_le_of_lt ( Polynomial.natDegree_mul_le .. ) ?_
      refine lt_of_le_of_lt ( add_le_add ( Polynomial.natDegree_sum_le _ _ )
          ( Polynomial.natDegree_sum_le _ _ ) ) ?_
      apply lt_of_le_of_lt
      · refine add_le_add (b:=m-1) (d:=n-1) ( Finset.sup_le ?g1 ) ( Finset.sup_le ?g2 )
        · intro i hi
          apply le_trans ( Polynomial.natDegree_smul_le _ _ )
          simpa using Nat.le_sub_one_of_lt ( Fin.is_lt i )
        · exact fun i _ => le_trans ( Polynomial.natDegree_smul_le _ _ ) ( by simp  )
      · linarith [Nat.sub_add_cancel ( NeZero.pos m ), Nat.sub_add_cancel ( NeZero.pos n )]
  -- Since $U_{rev}(x) \neq 0$, it follows that $W(x) = 0$.
  have h_U_rev_ne_zero : U_rev ≠ 0 := by
    intro H; simp_all [Polynomial.ext_iff]
    simp +zetaDelta at *
    -- Since $u \neq 0$, there exists some $j$ such that $u_j \neq 0$.
    obtain ⟨j, hj⟩ : ∃ j : Fin n, u j ≠ 0 := by
      exact Function.ne_iff.mp hu
    specialize H ( n - 1 - j.val ) ; simp_all [Finset.sum_ite]
    rw [Finset.sum_eq_single j] at H <;> simp_all [Fin.ext_iff]
    intro k hk₁ hk₂
    apply False.elim
    apply hk₂
    rw [tsub_right_inj] at hk₁ <;> linarith [
          Fin.is_lt j, Fin.is_lt k, Nat.sub_add_cancel ( show 1 ≤ n from NeZero.pos n )]
  simp_all [Polynomial.ext_iff]
  simp +zetaDelta at *
  exact hw_ne_zero <| funext fun i => by simpa [Fin.val_inj] using h_W_zero i


/-
Define the index set for diagonals of a Toeplitz matrix and its equivalence to Fin.
-/
def ZIdx (m n : ℕ) : Type := {z : ℤ // z ∈ Set.Icc (1 - (n : ℤ)) ((m : ℤ) - 1)}

def ZIdx_equiv_Fin {m n : ℕ} [NeZero m] [NeZero n] : Fin (m + n - 1) ≃ ZIdx m n where
  toFun := fun k => ⟨(k : ℤ) + 1 - n, by
  have one_le_m_plus_n :  1 ≤ m + n := by linarith [NeZero.pos m, NeZero.pos n]
  constructor <;> linarith [Fin.is_lt k, Nat.sub_add_cancel one_le_m_plus_n]⟩
  invFun := fun z => ⟨(z.val + n - 1).toNat, by
    convert z.property.2 using 1
    cases m <;> cases n <;> simp_all
    constructor <;> intros <;> omega⟩
  left_inv := by
    intro k
    simp_all only [sub_add_cancel, add_sub_cancel_right, Int.toNat_natCast, Fin.eta]
  right_inv := by
    intro k
    -- By definition of ZIdx, we know that k.val is in the interval [-m, n].
    obtain ⟨hk₁, hk₂⟩ := k.2
    exact Subtype.ext <| by norm_num; omega

/-
The cardinality of the index set is m + n - 1.
-/
instance instFintypeZIdx {m n : ℕ} : Fintype (ZIdx m n) :=
  inferInstanceAs (Fintype (Set.Icc (1 - (n : ℤ)) ((m : ℤ) - 1)))

lemma card_ZIdx {m n : ℕ} [NeZero m] [NeZero n] : Fintype.card (ZIdx m n) = m + n - 1 := by
  simp only [ZIdx, Set.mem_Icc, tsub_le_iff_right, Finset.mem_Icc, implies_true,
    Fintype.card_ofFinset, Int.card_Icc, sub_add_cancel]
  omega

/-
Define subtraction of indices to get a diagonal index.
-/
instance instHSubZIdx {m n : ℕ} [NeZero m] [NeZero n] : HSub (Fin m) (Fin n) (ZIdx m n) where
  hSub := fun i j => ⟨(i : ℤ) - j, by
    rw [Set.mem_Icc]
    constructor
    · have hj : (j : ℤ) ≤ n - 1 := by
        have := j.is_lt
        linarith
      have hi : 0 ≤ (i : ℤ) := Int.natCast_nonneg i
      linarith
    · have hi : (i : ℤ) ≤ m - 1 := by
        have := i.is_lt
        linarith
      have hj : 0 ≤ (j : ℤ) := Int.natCast_nonneg j
      linarith⟩

/-
A matrix is Toeplitz if and only if its entries depend only on the difference of indices.
-/
lemma Matrix.IsToeplitzIffExistsDefiningVector {m n : ℕ} [NeZero m] [NeZero n] {R : Type*}
   [Nonempty R] (M : Matrix (Fin m) (Fin n) R) :
    M.IsToeplitz ↔ ∃ (a : ZIdx m n → R), ∀ (i : Fin m) (j : Fin n), M i j = a (i - j) := by
  constructor <;> intro hM
  · -- Define `a(k)` by looking at a representative entry.
    have h_def : ∀ k : ℤ, k ∈ Set.Icc (1 - (n : ℤ)) ((m : ℤ) - 1) →
        ∃ x : R, ∀ i : Fin m, ∀ j : Fin n, i.val - j.val = k → M i j = x := by
      intro k hk
      by_cases hk_nonneg : 0 ≤ k
      · use M ⟨Int.toNat k, by
          linarith [Int.toNat_of_nonneg hk_nonneg, hk.2]⟩ ⟨0, by
          exact NeZero.pos n⟩
        generalize_proofs at *
        intro i j a
        subst a
        simp_all only [Set.mem_Icc, tsub_le_iff_right, Int.sub_nonneg, Nat.cast_le, Int.toNat_sub',
          Int.toNat_natCast, Fin.mk_zero']
        obtain ⟨left, right⟩ := hk
        apply hM
        simp_all only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, add_tsub_cancel_of_le]
      · use M ⟨0, NeZero.pos m⟩ ⟨Int.toNat (-k), by
          linarith [Int.toNat_of_nonneg ( by linarith : 0 ≤ -k ), hk.1, hk.2]⟩
        generalize_proofs at *
        intro i j hij
        have h_eq : i.val + (-k).toNat = j.val + 0 := by
          omega
        exact hM h_eq
    choose! a ha using h_def
    refine ⟨fun k => a ( k.val ), fun i j => ?_⟩
    convert ha _ _ _ _ _
    · simp_all only [Set.mem_Icc, tsub_le_iff_right, and_imp, Subtype.coe_prop]
    · exact rfl
  · obtain ⟨a, ha⟩ := hM
    intro i i' j j' hij
    have h_eq : (i : ℤ) - j = (i' : ℤ) - j' := by
      linarith [Fin.is_lt i, Fin.is_lt i', Fin.is_lt j, Fin.is_lt j']
    -- Since $i - j = i' - j'$ in the integers, their representatives in $ZIdx m n$ are the same.
    have h_eq_ZIdx : (i - j : ZIdx m n) = (i' - j' : ZIdx m n) := by
      exact Subtype.ext h_eq
    rw [ha i j, ha i' j', h_eq_ZIdx]

lemma surjective_toeplitz_mulVec_of_ne_zero {m n : ℕ} [inst : NeZero m]
    (mlen : m ≤ n) {v : Fin n → ZMod 2} (h_nonzero : v ≠ 0) :
    Function.Surjective (fun (M : BinToeplitzMatrix m n) => M.val.mulVec v) := by
  -- Since $v - w$ is non-zero, we can apply `toeplitz_mulVec_surjective`.
  convert toeplitz_mulVec_surjective h_nonzero using 1
  rotate_left
  · exact m
  · assumption
  · exact NeZero.of_ge mlen
  constructor <;> intro h
  · convert toeplitz_mulVec_surjective h_nonzero using 1
    · assumption
    · exact NeZero.of_ge mlen
  · intro x
    obtain ⟨p, hp⟩ := h x
    grind

/-
Main result:
Multiplication by a random binary Toeplitz matrix is a universal-2 hash family.
-/
theorem toeplitz_mulVec_isUniversal2 {m n : ℕ} [NeZero m] (mlen : m ≤ n) :
    IsUniversal2 (fun (M : BinToeplitzMatrix m n) (v : Fin n → ZMod 2) => M.val.mulVec v) := by
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
      obtain ⟨M, hM⟩ := surjective_toeplitz_mulVec_of_ne_zero mlen (sub_ne_zero_of_ne hvw) y
      rw [Finset.card_filter, Finset.card_filter]
      have := 0
      apply Finset.sum_bij (fun M' _ => ⟨M'.val - M.val, toeplitzSub M' M⟩)
      · intros
        simp_all only [ne_eq, Finset.mem_univ]
      · simp only [Finset.mem_univ, forall_const]
        intro a₁ a₂ h
        apply Subtype.ext
        simpa using congr_arg Subtype.val h
      · intro b hb
        use ⟨ b.val + M.val, by
          intro i i' j j' hij; simp_all [Matrix.IsToeplitz]
          apply congr_arg₂ ( · + · ) ( b.2 ( by aesop ) ) ( M.2 ( by aesop ) ) ⟩ ; aesop
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
  simp_all [sub_eq_iff_eq_add, Matrix.mulVec_sub]

end
