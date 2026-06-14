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
  unfold dft
  simp only [mul_comm, Finset.mul_sum _ _ _]
  rw [show (Finset.univ : Finset (Fin (2 * N))) =
      Finset.image (fun x : Fin N => ⟨2 * x, by linarith [Fin.is_lt x]⟩) Finset.univ ∪
      Finset.image (fun x : Fin N => ⟨2 * x + 1, by linarith [Fin.is_lt x]⟩)
        Finset.univ from ?_, Finset.sum_union]
  · rw [Finset.sum_image, Finset.sum_image] <;> simp only [mul_comm]
    · exact congrArg₂ (· + ·)
          (Finset.sum_congr rfl fun _ _ => by ring) (Finset.sum_congr rfl fun _ _ => by ring)
    · exact fun x y h => by simp only [Fin.ext_iff] at h ⊢; omega
    · exact fun x y h => by simp only [Fin.ext_iff] at h ⊢; omega
  · norm_num [Finset.disjoint_right]
    exact fun a x => ne_of_apply_ne (fun n => n % 2) (by norm_num [Nat.add_mod, Nat.mul_mod])
  · ext ⟨x, hx⟩ 
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_image, true_iff, true_and]
    rcases Nat.even_or_odd' x with ⟨c, rfl | rfl⟩ <;> [left; right] <;>
      exact ⟨⟨c, by linarith⟩, rfl⟩

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
  | zero => simp only [dft, ref_ntt, Fin.fin_one_eq_zero, Fin.val_zero, mul_zero,
      pow_zero, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
  | succ n ih =>
    simp only [ref_ntt, dft]
    split_ifs with h
    · convert dft_danielson_lanczos (2 ^ n) ω
          (fun j => a (⟨j.val, by omega⟩ : Fin (2 ^ (n + 1)))) k.val using 1
      · rw [dft_danielson_lanczos]
        · rcases n with (_ | n)
          · simp only [ih _ (Or.inl rfl)]
          · simp only [ih _ (Or.inr (by
              have h := hω.resolve_left (by omega)
              simp only [Nat.add_sub_cancel]
              rw [← pow_mul, (by ring : 2 * 2 ^ n = 2 ^ (n + 1))]
              exact h))]
      · convert dft_danielson_lanczos (2 ^ n) ω
            (fun j => a (⟨j.val, by omega⟩ : Fin (2 ^ (n + 1)))) k.val using 1
        refine Finset.sum_bij
            (fun j _ => ⟨j, by linarith [Fin.is_lt j, pow_succ' 2 n]⟩) ?_ ?_ ?_ ?_ <;>
            simp only [Finset.mem_univ, implies_true, Fin.mk.injEq, Fin.eta]
        · exact fun a₁ _ a₂ _ h => Fin.ext h
        · exact fun b _ =>
            ⟨⟨b, by linarith [Fin.is_lt b, pow_succ' 2 n]⟩, trivial, rfl⟩
    · rw [ih, ih]
      · convert dft_danielson_lanczos_second_half (2 ^ n) ω
              (hω.resolve_left (by positivity))
              (fun j => a ⟨j.val, by linarith [Fin.is_lt j, pow_succ' 2 n]⟩)
              (k.val - 2 ^ n) using 1
        · convert dft_danielson_lanczos_second_half (2 ^ n) ω
                (hω.resolve_left (by positivity))
                (fun j => a ⟨j.val, by linarith [Fin.is_lt j, pow_succ' 2 n]⟩)
                (k.val - 2 ^ n) |> Eq.symm using 1
        · convert dft_danielson_lanczos_second_half (2 ^ n) ω
                (hω.resolve_left (by positivity))
                (fun j => a ⟨j.val, by linarith [Fin.is_lt j, pow_succ' 2 n]⟩)
                (k.val - 2 ^ n) using 1
          rw [Nat.sub_add_cancel (le_of_not_gt h)]
          refine Finset.sum_bij
              (fun j _ => ⟨j, by linarith [Fin.is_lt j, pow_succ' 2 n]⟩) ?_ ?_ ?_ ?_ <;>
              simp only [Finset.mem_univ, implies_true, Fin.mk.injEq, Fin.eta]
          · exact fun a₁ _ a₂ _ h => Fin.ext h
          · exact fun b _ =>
            ⟨⟨b, by linarith [Fin.is_lt b, pow_succ' 2 n]⟩, trivial, rfl⟩
      · cases n <;> simp_all [pow_succ', pow_mul]
      · cases n <;> simp_all [pow_succ', pow_mul]

end DFTAlgebra
