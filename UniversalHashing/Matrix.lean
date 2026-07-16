/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

import UniversalHashing.Basic

/-!
Proof that Binary Matrix-vector multiplication (using all matrices) is a Universal-2 hash function:
`matrix_mulVec_isUniversal2`

(This family is very big and therefore not useful in practice)
-/

section GenericField


open scoped BigOperators
open LinearMap

variable {𝕜 : Type*} [Field 𝕜]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-- Given a vector `v`, the linear map mapping a matrix `M` to `M *ᵥ v`. -/
def mulVecMat (m : Type*) [Fintype m] [DecidableEq m] (v : n → 𝕜) :
    Matrix m n 𝕜 →ₗ[𝕜] (m → 𝕜) where
  toFun := fun M ↦ M.mulVec v
  map_add' := fun x y ↦ Matrix.add_mulVec x y v
  map_smul' := fun x m ↦ Matrix.smul_mulVec x m v

theorem mulVecMat_surjective (m : Type*) [Fintype m] [DecidableEq m] {v : n → 𝕜} (vne0 : v ≠ 0) :
    Function.Surjective (mulVecMat m v) := by
  intro w
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp vne0
  classical
  use Matrix.of (fun j k ↦ if k = i then (w j) / (v i) else 0)
  ext j
  calc (fun j_1 ↦ if j_1 = i then (w j) / (v i) else 0) ⬝ᵥ v
    _ = ∑ i_1, (fun j_1 ↦ if j_1 = i then (w j) / (v i) else 0) i_1 * v i_1 := rfl
    _ =  (w j / v i) * v i := by simp_all only [
        ne_eq, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    _ = w j := by simp_all only [
        ne_eq, isUnit_iff_ne_zero, not_false_eq_true, IsUnit.div_mul_cancel]

/-- `finrank` of the kernel of `M ↦ M.mulVec v` for nonzero `v`. -/
theorem finrank_ker_mulVecLin (m : Type*) [Fintype m] [DecidableEq m]
    {v : n → 𝕜} (hv : v ≠ 0) :
    Fintype.card m + Module.finrank 𝕜 (LinearMap.ker (mulVecMat m v))
      = Fintype.card m * Fintype.card n := by
  have := LinearMap.finrank_range_add_finrank_ker (mulVecMat m v)
  have rank_range := rank_range_of_surjective (mulVecMat m v) (mulVecMat_surjective m hv)
  simp only [←Module.finrank_eq_rank', Nat.cast_inj] at rank_range
  rw [rank_range, Module.finrank_matrix 𝕜 𝕜 m n] at this
  simp_all only [ne_eq, Module.finrank_fintype_fun_eq_card, Module.finrank_self, mul_one]

end GenericField

section ZModp

open FiniteDimensional Module

theorem card_eq_two_pow_finrank (p : ℕ) [Fact p.Prime] (V : Type*)
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V] [Fintype V] :
    Fintype.card V = p ^ finrank (ZMod p) V := by
  let b := Module.finBasis (ZMod p) V
  have h₁ : Fintype.card V = Fintype.card (Fin (finrank (ZMod p) V) → (ZMod p)) := by
    simpa using Fintype.card_congr (b.equivFun.toEquiv)
  have h₂ : Fintype.card (Fin (finrank (ZMod p) V) → (ZMod p)) = p ^ finrank (ZMod p) V := by
    simp only [Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact h₁.trans h₂

/--
There are `2 ^ (m * n)` binary mxn matrices.
-/
theorem h_card_matrices (p : ℕ) [Fact p.Prime] (m n : ℕ) :
    Fintype.card (Matrix (Fin m) (Fin n) (ZMod p)) = p ^ (m * n) := by
  simp only [Matrix]
  have hn : Fintype.card (Fin n → ZMod p) = p ^ n := by
    simp [Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hm : Fintype.card (Fin m → Fin n → ZMod p) = (p ^ n) ^ m := by
    simp [Fintype.card_pi, hn, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact hm.trans (by ring)

theorem finrank_matrix (p : ℕ) [Fact p.Prime] (m n : ℕ) :
    finrank (ZMod p) (Matrix (Fin m) (Fin n) (ZMod p)) = m * n := by
  simp_all [Module.finrank_matrix, Fintype.card_fin, finrank_self, mul_one]

theorem card_in_range_eq_card_ker (p : ℕ) [Fact p.Prime] (m n : ℕ) (v : Fin n → ZMod p) :
    ∀ w ∈ Set.range (fun M : Matrix (Fin m) (Fin n) (ZMod p) ↦ M.mulVec v),
      Fintype.card {M : Matrix (Fin m) (Fin n) (ZMod p) | M.mulVec v = w}
      = Fintype.card {M : Matrix (Fin m) (Fin n) (ZMod p) | M.mulVec v = 0} := by
  rintro _ ⟨M, rfl⟩
  rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card_filter, Finset.card_filter]
  apply Finset.sum_bij (fun N _ ↦ N - M) (by simp) (by simp)
  · exact fun b _ ↦ ⟨b + M, Finset.mem_univ _, by simp⟩
  · simp [sub_eq_zero, Matrix.sub_mulVec]

theorem mulVecMat_ZModp_card_ker {p : ℕ} [Fact p.Prime] (m : ℕ) {n : ℕ} (v : Fin n → ZMod p) :
    Fintype.card {M : Matrix (Fin m) (Fin n) (ZMod p) | M.mulVec v = 0}
    * Fintype.card (Set.range fun M : Matrix (Fin m) (Fin n) (ZMod p) ↦ M.mulVec v)
    = p ^ (m * n)
    := by
  have h_orbit_stabilizer :
      ∑ w ∈ Finset.image (fun M : Matrix (Fin m) (Fin n) (ZMod p) ↦ M.mulVec v) Finset.univ,
      Fintype.card {M : Matrix (Fin m) (Fin n) (ZMod p) | M.mulVec v = w} = p ^ (m * n) := by
    rw [Finset.sum_image' 1]
    · norm_num [h_card_matrices]
    · simp [Fintype.card_subtype]
  have : ∑ x ∈ Finset.image (fun M  : Matrix (Fin m) (Fin n) (ZMod p) ↦ M.mulVec v) Finset.univ,
        Fintype.card {M : Matrix (Fin m) (Fin n) (ZMod p) | M.mulVec v = x}
       = ∑ x ∈ Finset.image (fun M  : Matrix (Fin m) (Fin n) (ZMod p) ↦ M.mulVec v) Finset.univ,
        Fintype.card {M : Matrix (Fin m) (Fin n) (ZMod p) | M.mulVec v = 0} := by
   apply Finset.sum_congr rfl
   intro x hx
   exact (fun a ↦ card_in_range_eq_card_ker p m n v x a)
     <| (Finset.mem_image.mp hx |> fun ⟨M, _, hM⟩ ↦ hM ▸ Set.mem_range_self M)
  rw [← h_orbit_stabilizer, this]
  simp only [Set.coe_setOf, Fintype.card_ofFinset, mul_comm, Finset.sum_const, smul_eq_mul,
    mul_eq_mul_right_iff]
  exact Or.inl (congr_arg Finset.card <| by ext; simp [Function.comp])

theorem card_ker_pow_dim {p : ℕ} [Fact p.Prime] (a : ℕ) {b : ℕ} {v : Fin b → ZMod p} (hv : v ≠ 0) :
    Fintype.card {M : Matrix (Fin a) (Fin b) (ZMod p) | M.mulVec v = 0} = p ^ (a * (b - 1)) := by
  have := mulVecMat_ZModp_card_ker a v
  have h_range : Set.range (fun M : Matrix (Fin a) (Fin b) (ZMod p) ↦ M.mulVec v) = Set.univ :=
    Set.eq_univ_of_forall (show Function.Surjective (mulVecMat (Fin a) v)
      from mulVecMat_surjective (Fin a) hv)
  rcases b with (_ | b)
  · simp_all
  · simp_all only [ne_eq, Fintype.card_setUniv, Set.coe_setOf, Fintype.card_pi, ZMod.card,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, add_tsub_cancel_right]
    have card_vec : Fintype.card (Fin a → ZMod p) = p ^ a := by simp_all only [Fintype.card_pi,
      ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hpow : p ^ (a * (b + 1)) = p ^ a * p ^ (a * b) := by ring
    have pne0 : p ≠ 0 := Ne.symm (NeZero.ne' p)
    simp only [mul_comm, hpow, mul_eq_mul_left_iff, Nat.pow_eq_zero, ne_eq] at this
    cases this
    · simp_all
    · tauto

/-- Hash by matrix-times-vector modulo q -/
def matHash (q m n : ℕ) :
    HashFamily (Matrix (Fin m) (Fin n) (ZMod q)) (Fin n → ZMod q) (Fin m → ZMod q) := fun M v ↦
  M.mulVec v

/--
Matrix-vector multiplication (using all matrices modulo `p`) is Universal2.
-/
theorem matHash_universal2 (p : ℕ) [Fact p.Prime] (a b : ℕ) :
    HashFamily.universal2 (matHash p a b) := by
  intro x y hxy
  -- Let $v = x - y$. Since $x \neq y$, $v \neq 0$.
  set v : Fin b → ZMod p := x - y
  have hv_ne_zero : v ≠ 0 := sub_ne_zero_of_ne hxy
  -- The number of matrices $M$ such that $Mv = 0$ is $2^{a(b-1)}$.
  have h_card_ker : Fintype.card {M : Matrix (Fin a) (Fin b) (ZMod p) | M.mulVec v = 0}
      = p ^ (a * (b - 1)) := by
    exact card_ker_pow_dim a hv_ne_zero
  rcases b with (_ | b)
  · simp_all only [ne_eq, Matrix.empty_sub_empty, Matrix.zero_empty, not_true_eq_false, v]
  · convert Nat.mul_le_mul_right (p ^ a) h_card_ker.le using 1
    · have hset : {s : Matrix (Fin a) (Fin (b + 1)) (ZMod p) | s.mulVec x = s.mulVec y}
          = {M | M.mulVec v = 0} := by
        ext M
        constructor
        · intro h
          change M.mulVec (x - y) = 0
          rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr h
        · intro h
          change M.mulVec x = M.mulVec y
          have hh : M.mulVec (x - y) = 0 := h
          rw [Matrix.mulVec_sub] at hh; exact sub_eq_zero.mp hh
      simp only [matHash, Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
      congr 1
      apply Fintype.card_congr
      exact { toFun := fun ⟨s, hs⟩ => ⟨s, hset ▸ hs⟩
              invFun := fun ⟨M, hM⟩ => ⟨M, hset.symm ▸ hM⟩
              left_inv := fun _ => Subtype.ext rfl
              right_inv := fun _ => Subtype.ext rfl }
    · erw [Fintype.card_pi]
      norm_num [pow_mul]
      ring_nf

/--
Counterexample:
Binary Matrix-vector multiplication (using binary matrices) is **not** strongly-Universal-2.
-/
theorem matHash_not_strongly_universal_n (a b : ℕ) (ha : a > 0) (hb : b > 0) :
    ¬ HashFamily.stronglyUniversal_n 2 (matHash 2 a b) := by
  simp only [HashFamily.stronglyUniversal_n, matHash, Function.Injective, Fin.forall_fin_two,
    Fin.isValue, imp_self, zero_ne_one, imp_false, true_and, one_ne_zero, and_true,
    Fintype.card_subtype, Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, and_imp, not_forall]
  refine ⟨fun i ↦ if i = 0 then 0 else fun _ ↦ 1,
      (by simp [funext_iff, Fin.pos_iff_nonempty.mp hb]),
      (by simp [funext_iff, Fin.pos_iff_nonempty.mp hb]), ?_⟩
  simp only [funext_iff]
  use fun i ↦ if i = 0 then fun _ ↦ 1 else fun _ ↦ 0
  norm_num [Fintype.card_subtype]
  cases a <;> cases b <;> norm_num [Fintype.card_pi] at *
  ring_nf
  simp_all

end ZModp
