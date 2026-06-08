/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib
/-!
# DFT Algebraic Lemmas

This file contains the algebraic identities needed for the NTT correctness proof,
in particular the Danielson-Lanczos (butterfly) splitting identity and the
recursive DFT definition.
-/


section DFTAlgebra

variable {R : Type*} [CommRing R]

/-- The DFT of a sequence `a : Fin N → R` with respect to a root of unity `ω` at index `k`. -/
noncomputable def dft (N : ℕ) (ω : R) (a : Fin N → R) (k : ℕ) : R :=
  ∑ j : Fin N, a j * ω ^ (j.val * k)

-- /-
-- Factoring a constant out of the DFT: if each input element is multiplied by `c`,
--     the DFT is multiplied by `c`.
-- -/
-- theorem dft_const_factor (N : ℕ) (ω c : R) (a : Fin N → R) (k : ℕ) :
--     dft N ω (fun j => c * a j) k = c * dft N ω a k := by
--   unfold dft; simp +decide [ mul_assoc, Finset.mul_sum _ _ _ ] ;

/-
The Danielson-Lanczos splitting identity:
    The DFT of a sequence of length 2N can be split into DFTs of its even and odd parts.

    Σ_{j=0}^{2N-1} a_j · ω^(j·k) =
      Σ_{j=0}^{N-1} a_{2j} · (ω²)^(j·k) + ω^k · Σ_{j=0}^{N-1} a_{2j+1} · (ω²)^(j·k)
-/
theorem dft_danielson_lanczos (N : ℕ) (ω : R) (a : Fin (2 * N) → R) (k : ℕ) :
    dft (2 * N) ω a k =
      dft N (ω ^ 2) (fun j => a ⟨2 * j.val, by omega⟩) k +
      ω ^ k * dft N (ω ^ 2) (fun j => a ⟨2 * j.val + 1, by omega⟩) k := by
  unfold dft;
  simp only [mul_comm, Finset.mul_sum _ _ _];
  rw [ show ( Finset.univ : Finset ( Fin ( 2 * N ) ) ) =
      Finset.image ( fun x : Fin N => ⟨ 2 * x, by linarith [ Fin.is_lt x ] ⟩ ) Finset.univ ∪
      Finset.image ( fun x : Fin N => ⟨ 2 * x + 1, by linarith [ Fin.is_lt x ] ⟩ )
        Finset.univ from ?_, Finset.sum_union ];
  · rw [ Finset.sum_image, Finset.sum_image ] <;> simp only [mul_comm];
    · exact congrArg₂ ( · + · )
          ( Finset.sum_congr rfl fun _ _ => by ring ) ( Finset.sum_congr rfl fun _ _ => by ring );
    · exact fun x y h => by simp only [Fin.ext_iff] at h ⊢; omega
    · exact fun x y h => by simp only [Fin.ext_iff] at h ⊢; omega
  · norm_num [ Finset.disjoint_right ];
    exact fun a x => ne_of_apply_ne ( fun n => n % 2 ) ( by norm_num [ Nat.add_mod, Nat.mul_mod ] );
  · ext ⟨ x, hx ⟩ ;
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_image, true_iff, true_and];
    rcases Nat.even_or_odd' x with ⟨ c, rfl | rfl ⟩ <;> [ left; right ] <;>
      exact ⟨ ⟨ c, by linarith ⟩, rfl ⟩

/-
The second-half Danielson-Lanczos identity:
    When ω^N = -1, the DFT at index k+N uses subtraction instead of addition.

    Σ_{j=0}^{2N-1} a_j · ω^(j·(k+N)) =
      Σ_{j=0}^{N-1} a_{2j} · (ω²)^(j·k) - ω^k · Σ_{j=0}^{N-1} a_{2j+1} · (ω²)^(j·k)
-/
theorem dft_danielson_lanczos_second_half (N : ℕ) (ω : R)
    (hω : ω ^ N = -1) (a : Fin (2 * N) → R) (k : ℕ) :
    dft (2 * N) ω a (k + N) =
      dft N (ω ^ 2) (fun j => a ⟨2 * j.val, by omega⟩) k -
      ω ^ k * dft N (ω ^ 2) (fun j => a ⟨2 * j.val + 1, by omega⟩) k := by
  simp_all only [dft_danielson_lanczos, mul_comm, pow_add, mul_neg, mul_one, neg_mul,
    sub_eq_add_neg]
  unfold dft
  simp only [pow_mul', pow_add, mul_comm, Finset.mul_sum]
  simp_all only [pow_right_comm, even_two, Even.neg_pow, one_pow, one_mul]

/-- Recursive Cooley-Tukey DFT on sequences of length `2^n`. This mirrors the structure
    of the butterfly algorithm: recursively split into even/odd halves, compute smaller DFTs,
    then combine using twiddle factors. -/
noncomputable def ref_ntt {R : Type*} [CommRing R] :
    (n : ℕ) → (ω : R) → (a : Fin (2 ^ n) → R) → (Fin (2 ^ n) → R)
  | 0, _, a => a
  | n + 1, ω, a =>
    let even_dft := ref_ntt n (ω ^ 2) (fun j => a ⟨2 * j.val, by omega⟩)
    let odd_dft := ref_ntt n (ω ^ 2) (fun j => a ⟨2 * j.val + 1, by omega⟩)
    fun k =>
      if h : k.val < 2 ^ n then
        even_dft ⟨k.val, h⟩ + ω ^ k.val * odd_dft ⟨k.val, h⟩
      else
        even_dft ⟨k.val - 2 ^ n, by omega⟩ -
          ω ^ (k.val - 2 ^ n) * odd_dft ⟨k.val - 2 ^ n, by omega⟩

/-
The recursive Cooley-Tukey DFT computes the same sum as the mathematical DFT definition.
    For `n ≥ 1`, the hypothesis `ω ^ (2^(n-1)) = -1` ensures that ω is a primitive 2^n-th root
    of unity, which is needed for the butterfly combination step.
-/
theorem ref_ntt_eq_dft (n : ℕ) (ω : R)
    (hω : n = 0 ∨ ω ^ 2 ^ (n - 1) = -1)
    (a : Fin (2 ^ n) → R) (k : Fin (2 ^ n)) :
    ref_ntt n ω a k = dft (2 ^ n) ω a k.val := by
  induction n generalizing ω with
  | zero => fin_cases k ; simp +decide [ dft, ref_ntt ];
  | succ n ih =>
    simp only [ ref_ntt, dft ];
    split_ifs with h;
    · convert dft_danielson_lanczos ( 2 ^ n ) ω
          ( fun j => a ( ⟨ j.val, by omega ⟩ : Fin ( 2 ^ ( n + 1 ) ) ) ) k.val using 1;
      · rw [ dft_danielson_lanczos ];
        · rcases n with ( _ | n )
          · simp only [ih _ (Or.inl rfl)]
          · simp only [ih _ (Or.inr (by
              have h := hω.resolve_left (by omega)
              simp only [Nat.add_sub_cancel]
              rw [← pow_mul, show 2 * 2 ^ n = 2 ^ (n + 1) from by ring]
              exact h))]
      · convert dft_danielson_lanczos ( 2 ^ n ) ω
            ( fun j => a ( ⟨ j.val, by omega ⟩ : Fin ( 2 ^ ( n + 1 ) ) ) ) k.val using 1;
        refine Finset.sum_bij
            ( fun j _ => ⟨ j, by linarith [ Fin.is_lt j, pow_succ' 2 n ] ⟩ ) ?_ ?_ ?_ ?_ <;>
            simp only [Finset.mem_univ, implies_true, Fin.mk.injEq, Fin.eta]
        · exact fun a₁ _ a₂ _ h => Fin.ext h
        · exact fun b _ =>
            ⟨ ⟨ b, by linarith [ Fin.is_lt b, pow_succ' 2 n ] ⟩, trivial, rfl ⟩
    · rw [ ih, ih ];
      · convert dft_danielson_lanczos_second_half ( 2 ^ n ) ω
              ( hω.resolve_left ( by positivity ) )
              ( fun j => a ⟨ j.val, by linarith [ Fin.is_lt j, pow_succ' 2 n ] ⟩ )
              ( k.val - 2 ^ n ) using 1;
        · convert dft_danielson_lanczos_second_half ( 2 ^ n ) ω
                ( hω.resolve_left ( by positivity ) )
                ( fun j => a ⟨ j.val, by linarith [ Fin.is_lt j, pow_succ' 2 n ] ⟩ )
                ( k.val - 2 ^ n ) |> Eq.symm using 1;
        · convert dft_danielson_lanczos_second_half ( 2 ^ n ) ω
                ( hω.resolve_left ( by positivity ) )
                ( fun j => a ⟨ j.val, by linarith [ Fin.is_lt j, pow_succ' 2 n ] ⟩ )
                ( k.val - 2 ^ n ) using 1;
          rw [ Nat.sub_add_cancel ( le_of_not_gt h ) ];
          refine Finset.sum_bij
              ( fun j _ => ⟨ j, by linarith [ Fin.is_lt j, pow_succ' 2 n ] ⟩ ) ?_ ?_ ?_ ?_ <;>
              simp only [Finset.mem_univ, implies_true, Fin.mk.injEq, Fin.eta]
          · exact fun a₁ _ a₂ _ h => Fin.ext h
          · exact fun b _ =>
            ⟨ ⟨ b, by linarith [ Fin.is_lt b, pow_succ' 2 n ] ⟩, trivial, rfl ⟩
      · cases n <;> simp_all +decide [ pow_succ', pow_mul ];
      · cases n <;> simp_all +decide [ pow_succ', pow_mul ]

-- /-
-- The DFT of a single-element sequence is just the element itself.
-- -/
-- theorem dft_size_one (ω : R) (a : Fin 1 → R) (k : ℕ) :
--     dft 1 ω a k = a ⟨0, by omega⟩ := by
--   unfold dft;
--   simp +decide [ Fin.eq_zero ]

-- /-
-- The DFT of a two-element sequence with a primitive 2nd root of unity (ω = -1).
-- -/
-- theorem dft_size_two (a : Fin 2 → R) :
--     dft 2 (-1 : R) a 0 = a ⟨0, by omega⟩ + a ⟨1, by omega⟩ ∧
--     dft 2 (-1 : R) a 1 = a ⟨0, by omega⟩ - a ⟨1, by omega⟩ := by
--   unfold dft;
--   simp +decide [ Fin.sum_univ_succ, sub_eq_add_neg ]

-- /-
-- Radix-4 Danielson-Lanczos splitting identity:
--     The DFT of a sequence of length 4s splits into four DFTs of length s,
--     corresponding to residues 0, 1, 2, 3 mod 4.
-- -/
-- theorem dft_danielson_lanczos_radix4 (s : ℕ) (ω : R)
--     (g : Fin (4 * s) → R) (j2 : ℕ) :
--     dft (4 * s) ω g j2 =
--       dft s (ω ^ 4) (fun q => g ⟨4 * q.val, by omega⟩) j2 +
--       ω ^ j2 * dft s (ω ^ 4) (fun q => g ⟨4 * q.val + 1, by omega⟩) j2 +
--       ω ^ (2 * j2) * dft s (ω ^ 4) (fun q => g ⟨4 * q.val + 2, by omega⟩) j2 +
--       ω ^ (3 * j2) * dft s (ω ^ 4) (fun q => g ⟨4 * q.val + 3, by omega⟩) j2 := by
--   simp only [dft]
--   have step1 : ∑ j : Fin (4 * s), g j * ω ^ (j.val * j2) =
--       ∑ qr : Fin s × Fin 4,
--         g ⟨4 * qr.1.val + qr.2.val, by have := qr.1.isLt; have := qr.2.isLt; omega⟩ *
--         ω ^ ((4 * qr.1.val + qr.2.val) * j2) := by
--     symm
--     apply Finset.sum_nbij (fun (qr : Fin s × Fin 4) =>
--       (⟨4 * qr.1.val + qr.2.val, by have := qr.1.isLt; have := qr.2.isLt; omega⟩ :
--         Fin (4 * s)))
--     · intro _ _; simp
--     · intro ⟨q1, r1⟩ _ ⟨q2, r2⟩ _ h
--       simp only [Fin.mk.injEq] at h
--       have hr1 := r1.isLt; have hr2 := r2.isLt
--       simp only [Prod.mk.injEq, Fin.ext_iff]; constructor <;> omega
--     · intro ⟨j, hj⟩ _
--       simp only [Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and]
--       exact ⟨(⟨j / 4, by omega⟩, ⟨j % 4, Nat.mod_lt _ (by omega)⟩),
--              by simp [Fin.ext_iff]; omega⟩
--     · intro ⟨q, r⟩ _; rfl
--   rw [step1, Fintype.sum_prod_type]
--   simp only [Fin.sum_univ_four]
--   simp only [show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
--              show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl,
--              Nat.add_zero]
--   simp only [Finset.sum_add_distrib, Finset.mul_sum]
--   congr 1
--   · congr 1
--     · congr 1
--       · apply Finset.sum_congr rfl; intro q _
--         rw [show 4 * q.val * j2 = 4 * (q.val * j2) by ring, pow_mul ω 4 (q.val * j2)]
--       · apply Finset.sum_congr rfl; intro q _
--         rw [show (4 * q.val + 1) * j2 = j2 + 4 * (q.val * j2) by ring,
--             pow_add, pow_mul ω 4 (q.val * j2)]; ring
--     · apply Finset.sum_congr rfl; intro q _
--       rw [show (4 * q.val + 2) * j2 = 2 * j2 + 4 * (q.val * j2) by ring,
--           pow_add, pow_mul ω 4 (q.val * j2)]; ring
--   · apply Finset.sum_congr rfl; intro q _
--     rw [show (4 * q.val + 3) * j2 = 3 * j2 + 4 * (q.val * j2) by ring,
--         pow_add, pow_mul ω 4 (q.val * j2)]; ring

-- /-
-- DFT with permuted input equals DFT with permuted indices.
-- -/
-- theorem dft_permute (N : ℕ) (ω : R) (a : Fin N → R) (σ : Equiv.Perm (Fin N))
--     (hω : ω ^ N = 1) (k : ℕ) :
--     dft N ω (a ∘ σ) k = ∑ j : Fin N, a (σ j) * ω ^ (j.val * k) := by
--   unfold dft; aesop;

end DFTAlgebra
