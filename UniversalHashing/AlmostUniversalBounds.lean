/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import UniversalHashing.AlmostUniversal
import UniversalHashing.Util
/-!
# Bounds for ε-Almost Universal Hashing

## Main results

* `HashFamily.card_seed_lb_of_almostStronglyUniversal2`:
  Every uniform ε-ASU₂ family (i.e. `HashFamily.uniform H ∧ H.almostStronglyUniversal2 ε`) satisfies
  `|Seed| ≥ 1 + |Input| (|Output| − 1)² / (|Output| ε (|Input| − 1) + |Output| − |Input|)`.
  *[S94, Theorem 4.3]*
* `HashFamily.card_seed_lb_of_stronglyUniversal2`:
  Every strongly-universal₂ family satisfies `|Seed| ≥ 1 + |Input| (|Output| − 1)`.
  *[S94, Corollary 4.4]*
* `HashFamily.exists_collision_lb`:
  For any hash family with `|Input| > |Output|`, some pair of distinct inputs has collision
  probability at least `(|Input| − |Output|) / (|Output| (|Input| − 1))`.
  *[S94, Theorem 3.1]*
* `HashFamily.almostUniversal2_comp`:
  Composing an ε₁-AU₂ family with an ε₂-AU₂ family yields an `(ε₁ + ε₂)`-AU₂ family.
  *[S94, Theorem 5.4]*

-/


section StinsonBoundHelpers

variable {Seed Input Output : Type*} [Fintype Seed] [Fintype Input] [Fintype Output]
  [DecidableEq Output] [Nonempty Seed]

/-- The number of inputs on which two seeds agree. -/
private def coincidence (H : HashFamily Seed Input Output) (s t : Seed) : ℕ :=
  Fintype.card {x // H s x = H t x}

open Finset

/-- The sum of coincidences over all pairs of seeds (including s=t) is determined by the
uniformity. -/
private theorem sum_coincidence_eq
    (H : HashFamily Seed Input Output)
    (h_unif : ∀ x a, probUniform (fun s => H s x = a) = 1 / Fintype.card Output) :
    ∑ s, ∑ t, (coincidence H s t : ℚ) =
    Fintype.card Input * (Fintype.card Seed)^2 / Fintype.card Output := by
  have h_per_input (x : Input) : ∑ s : Seed, ∑ t : Seed, (if H s x = H t x then 1 else 0 : ℚ) =
      (Fintype.card Seed : ℚ) ^ 2 / (Fintype.card Output : ℚ) := by
    have h_sq_eq : ∑ s : Seed, ∑ t : Seed, (if H s x = H t x then 1 else 0 : ℚ) =
        ∑ a : Output, (∑ s : Seed, (if H s x = a then 1 else 0 : ℚ)) ^ 2 := by
      have h_agree (s : Seed) : ∑ t : Seed, (if H s x = H t x then 1 else 0 : ℚ) =
          ∑ a : Output,
          (if H s x = a then (∑ t : Seed, (if H t x = a then 1 else 0 : ℚ)) else 0) := by
        simp_all [eq_comm]
      simp only [h_agree, pow_two, Finset.mul_sum, sum_mul]
      rw [Finset.sum_comm]
      congr; ext; congr; ext; aesop
    simp_all [probUniform, div_eq_iff, Fintype.card_subtype]
    by_cases h : Fintype.card Output = 0 <;>
      simp [h, sq, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv]
  simp_all only [coincidence, one_div, Finset.sum_boole]
  have h_swap : ∑ x : Seed, ∑ y : Seed, (∑ i : Input, (if H x i = H y i then 1 else 0 : ℚ)) =
      ∑ i : Input, ∑ x : Seed, ∑ y : Seed, (if H x i = H y i then 1 else 0 : ℚ) :=
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)).symm
  simp_all only [Fintype.card_subtype, Finset.sum_boole, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

end StinsonBoundHelpers

/-- Per-pair version of the Fubini reordering: C(s,t)·(C(s,t)−1) as a double sum over inputs. -/
private lemma card_mul_pred_eq_off_diag_sum {Seed Input Output : Type*}
  [Fintype Input]
  [DecidableEq Input] [DecidableEq Output] [Nontrivial Input]
  (H : HashFamily Seed Input Output) (s t : Seed) :
    (Fintype.card {x : Input // H s x = H t x} *
        (Fintype.card {x : Input // H s x = H t x} - 1) : ℚ) =
    ∑ x : Input, ∑ y : Input,
    (if x ≠ y ∧ H s x = H t x ∧ H s y = H t y then 1 else 0 : ℚ) := by
  have h_fubini : (Fintype.card {x : Input // H s x = H t x} *
      (Fintype.card {x : Input // H s x = H t x} - 1) : ℚ) =
      ∑ x ∈ Finset.univ.filter (fun x => H s x = H t x),
      ∑ y ∈ Finset.univ.filter (fun x => H s x = H t x),
      (if x ≠ y then 1 else 0 : ℚ) := by
    simp only [ne_eq, ite_not, Finset.sum_ite, Finset.sum_const_zero, Finset.filter_ne,
      Finset.sum_const, nsmul_eq_mul, mul_one, zero_add, Fintype.card_subtype]
    rw [Finset.sum_congr rfl fun x hx => by rw [Finset.card_erase_of_mem hx]]
    simp only [mul_sub, mul_one, Finset.sum_const, nsmul_eq_mul]
    cases Finset.card (Finset.filter (fun x => H s x = H t x) Finset.univ) <;> simp; ring
  simp_all only [ne_eq, Finset.sum_boole]
  simp only [Finset.filter_filter, and_comm, and_assoc]
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun x _ => by split_ifs <;> simp [*, Finset.filter_and]

/-- Rewrites a double-seed coincidence indicator sum as a sum of products of per-output counts.
`∑ s ∑ t [H s x = H t x ∧ H s y = H t y] = ∑ a ∑ b (∑ s [H s x = a ∧ H s y = b])²` -/
private lemma sum_indicator_factor {Seed Input Output : Type*}
    [Fintype Seed] [Fintype Output] [DecidableEq Output]
    (H : HashFamily Seed Input Output) (x y : Input) :
    (∑ s : Seed, ∑ t : Seed, (if H s x = H t x ∧ H s y = H t y then 1 else 0 : ℚ)) =
    ∑ a : Output, ∑ b : Output,
      (∑ s : Seed, if H s x = a ∧ H s y = b then 1 else 0 : ℚ) *
      (∑ t : Seed, if H t x = a ∧ H t y = b then 1 else 0 : ℚ) := by
  have h_sum (s t : Seed) : (if H s x = H t x ∧ H s y = H t y then 1 else 0 : ℚ) =
      ∑ a : Output, ∑ b : Output, (if H s x = a ∧ H s y = b then 1 else 0 : ℚ) *
      (if H t x = a ∧ H t y = b then 1 else 0 : ℚ) := by
    by_cases h : H s x = H t x ∧ H s y = H t y
    · rw [Finset.sum_eq_single (H s x)] <;> aesop
    · rw [Finset.sum_eq_zero]
      · aesop
      · intro a _; rw [Finset.sum_eq_zero]; aesop
  simp only [h_sum, Finset.mul_sum, Finset.sum_mul]
  simp only [← Finset.sum_product']; ring_nf
  refine Finset.sum_bij (fun a _ => (a.2.2.1, a.2.2.2, a.2.1, a.1)) ?_ ?_ ?_ ?_ <;> simp

section StinsonBoundHelpers2

variable {Seed Input Output : Type*} [Fintype Seed] [Fintype Input] [Fintype Output]
  [DecidableEq Output] [Nonempty Seed] [Nontrivial Input]

open Fintype Finset

private theorem sum_coincidence_mul_pred_le
    (H : HashFamily Seed Input Output)
    {ε : ℚ}
    (h_asu : H.almostStronglyUniversal2 ε) :
    ∑ s, ∑ t, (coincidence H s t * (coincidence H s t - 1) : ℚ) ≤
    Fintype.card Input * (Fintype.card Input - 1) * ε *
    (Fintype.card Seed)^2 / Fintype.card Output := by
  classical
  have h_prob (x y : Input) (hxy : x ≠ y) :
      (∑ s : Seed, (∑ t : Seed, (if H s x = H t x ∧ H s y = H t y then 1 else 0) : ℚ)) ≤
      ε * (Fintype.card Seed)^2 / Fintype.card Output := by
    have h_div :
        (∑ s : Seed, (∑ t : Seed, (if H s x = H t x ∧ H s y = H t y then 1 else 0) : ℚ)) =
        ((Fintype.card Seed : ℚ) ^ 2) *
        (∑ a : Output, (∑ b : Output,
          (probUniform (fun s => H s x = a ∧ H s y = b)) ^ 2 : ℚ)) := by
      have h_count (a b : Output) :
          ∑ s : Seed, (if H s x = a ∧ H s y = b then 1 else 0 : ℚ) =
          (Fintype.card Seed : ℚ) * probUniform (fun s => H s x = a ∧ H s y = b) := by
        simp only [probUniform, Fintype.card_subtype, Finset.sum_boole]
        field_simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]
      rw [sum_indicator_factor]
      simp_rw [h_count,
        show ∀ a b : ℚ, a * b * (a * b) = a ^ 2 * b ^ 2 by intros; ring,
        ← Finset.mul_sum]
    have h_bound (a b : Output) : (probUniform (fun s => H s x = a ∧ H s y = b)) ^ 2 ≤
        (ε / Fintype.card Output) * (probUniform (fun s => H s x = a ∧ H s y = b)) := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (h_asu hxy a b)
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have h_sum_bound : (∑ a : Output, (∑ b : Output,
        (probUniform (fun s => H s x = a ∧ H s y = b)) : ℚ)) = 1 := by
      have h_count_total : (∑ a : Output, (∑ b : Output,
          (Fintype.card {s : Seed // H s x = a ∧ H s y = b}) : ℚ)) = (Fintype.card Seed : ℚ) := by
        simp only [Fintype.card_subtype]
        rw_mod_cast [← Finset.sum_product']
        simp only [card_filter]
        rw [Finset.sum_comm]
        simp only [univ_product_univ, sum_boole, Nat.cast_id]
        rw [Finset.sum_congr rfl fun _ _ =>
          Finset.card_eq_one.mpr ⟨( H ‹_› x, H ‹_› y ), by aesop⟩]
        simp [Finset.card_univ]
      convert congr_arg ( fun x : ℚ => x / Fintype.card Seed ) h_count_total using 1
      · simp [probUniform, Finset.sum_div]
      · rw [div_self ( Nat.cast_ne_zero.mpr Fintype.card_ne_zero )]
    have h_sum_bound2 : (∑ a : Output, (∑ b : Output,
        (probUniform (fun s => H s x = a ∧ H s y = b)) ^ 2 : ℚ)) ≤
        (ε / Fintype.card Output) * (∑ a : Output, (∑ b : Output,
          (probUniform (fun s => H s x = a ∧ H s y = b)) : ℚ)) := by
      simpa only [Finset.mul_sum] using
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => h_bound a b
    simp_all only [ne_eq, sum_boole, mul_one, mul_div_assoc, ge_iff_le]
    exact (mul_le_mul_of_nonneg_left h_sum_bound2 (sq_nonneg _)).trans_eq (by ring)
  have h_fubini : ∑ s : Seed, ∑ t : Seed,
      (Fintype.card {x : Input // H s x = H t x} *
        (Fintype.card {x : Input // H s x = H t x} - 1) : ℚ) =
      ∑ x : Input, ∑ y : Input, ∑ s : Seed, ∑ t : Seed,
      (if x ≠ y ∧ H s x = H t x ∧ H s y = H t y then 1 else 0 : ℚ) := by
    simp only [card_mul_pred_eq_off_diag_sum H, ← Finset.sum_product']
    refine Finset.sum_nbij (fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1)) ?_ ?_ ?_ ?_
    · intro a _; exact Finset.mem_univ _
    · rintro ⟨a1, a2, b1, b2⟩ _ ⟨c1, c2, d1, d2⟩ _; simp [Prod.mk.injEq]; tauto
    · rintro ⟨b1, b2, a1, a2⟩ _; exact ⟨⟨a1, a2, b1, b2⟩, Finset.mem_univ _, rfl⟩
    · intro a _; rfl
  have h_sum_bound : ∑ x : Input, ∑ y : Input, ∑ s : Seed, ∑ t : Seed,
      (if x ≠ y ∧ H s x = H t x ∧ H s y = H t y then 1 else 0 : ℚ) ≤
      ∑ x : Input, ∑ y : Input,
      (if x ≠ y then ε * (Fintype.card Seed)^2 / Fintype.card Output else 0 : ℚ) := by
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro y _
    rcases eq_or_ne x y with rfl | hxy
    · simp only [ne_eq, not_true, false_and, ite_false, Finset.sum_const_zero, le_refl]
    · rw [if_pos hxy]
      simp_rw [and_iff_right hxy]
      exact h_prob x y hxy
  convert h_fubini.le.trans h_sum_bound using 1
  · rfl
  · rfl
  norm_num [Finset.sum_ite, Finset.filter_ne, Finset.filter_ne']
  ring_nf!
  rw [Nat.cast_pred Fintype.card_pos]
  ring

end StinsonBoundHelpers2

open Real

private lemma cauchy_schwarz_count {Seed Input Output : Type*}
    [Fintype Input] [Fintype Output] [DecidableEq Output] [Nonempty Input]
    (H : HashFamily Seed Input Output) (s : Seed) :
    ∑ a : Output, (Fintype.card {x : Input | H s x = a} : ℚ) ^ 2 ≥
    (Fintype.card Input : ℚ) ^ 2 / (Fintype.card Output : ℚ) := by
  have h_cs : (∑ a : Output, (Fintype.card {x : Input | H s x = a} : ℚ)) ^ 2 ≤
      (Fintype.card Output : ℚ) *
      ∑ a : Output, (Fintype.card {x : Input | H s x = a} : ℚ) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ 1
      (fun a => (Fintype.card { x : Input | H s x = a } : ℚ))
  have h_sum_card : ∑ a : Output, (Fintype.card {x : Input | H s x = a} : ℚ) =
      Fintype.card Input := by exact_mod_cast sum_fiber_card (H s)
  exact div_le_iff₀' (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr
      ⟨H s (Classical.arbitrary Input)⟩)) |>.2
    (by simpa only [h_sum_card] using h_cs)

/-- The collision probability on a product seed space factors over the first coordinate:
`Pr_{s₁×s₂}[P] = (∑ s₁, Pr_{s₂}[P s₁]) / |S₁|`. -/
private lemma probUniform_prod {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    (P : S₁ → S₂ → Prop) [∀ s₁ s₂, Decidable (P s₁ s₂)] :
    (Fintype.card {s : S₁ × S₂ // P s.1 s.2} : ℚ) / Fintype.card (S₁ × S₂) =
    (∑ s₁ : S₁, (Fintype.card {s₂ : S₂ // P s₁ s₂} : ℚ) / Fintype.card S₂) /
    Fintype.card S₁ := by
  simp only [Fintype.card_subtype, Fintype.card_prod, Nat.cast_mul, Finset.sum_div]
  rw [Finset.card_filter]
  erw [Finset.sum_product]
  simp [div_eq_mul_inv, mul_comm, Finset.mul_sum, mul_left_comm]

/-- Cauchy-Schwarz inequality for double sums: lifts `Finset.sum_mul_sq_le_sq_mul_sq`
from a product index to an iterated double sum. -/
private lemma double_sum_cauchy_schwarz {α : Type*} [Fintype α] (u v : α → α → ℝ) :
    (∑ s : α, ∑ t : α, u s t * v s t) ^ 2 ≤
    (∑ s : α, ∑ t : α, u s t ^ 2) * (∑ s : α, ∑ t : α, v s t ^ 2) := by
  simpa only [← Finset.sum_product', Finset.univ_product_univ] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun p : α × α => u p.1 p.2) (fun p : α × α => v p.1 p.2)

section SeedInputOutputFuture

variable {Seed Input Output : Type*}
  [Fintype Seed] [Fintype Input] [Fintype Output]
  [DecidableEq Output]

private theorem helper_ineq_of_almostStronglyUniversal2
    [Nonempty Seed] [Nontrivial Input]
    {ε : ℚ} {H : HashFamily Seed Input Output}
    (h_unif : HashFamily.uniform H)
    (h_asu : H.almostStronglyUniversal2 ε) :
    let I := Fintype.card Input
    let S := Fintype.card Seed
    let O := Fintype.card Output
    (I * (S : ℚ) * ((S : ℚ) / (O : ℚ) - 1)) ^ 2
    ≤
    (S : ℚ) * ((S : ℚ) - 1) * ((I * (S : ℚ) * ((S : ℚ) / (O : ℚ) - 1)) + (I * (I - 1) * ε *
      (S : ℚ) ^ 2 / (O : ℚ) - (S : ℚ) * (I * (I - 1)))) := by
  classical
  set C : Seed → Seed → ℕ := fun s t => Fintype.card {x : Input // H s x = H t x}
  have h_sum_C : ∑ s : Seed, ∑ t : Seed, (C s t : ℚ) =
      (Fintype.card Input : ℚ) * (Fintype.card Seed : ℚ)^2 / (Fintype.card Output : ℚ) :=
    sum_coincidence_eq H h_unif
  have h_sum_C_sq : ∑ s : Seed, ∑ t : Seed, (C s t * (C s t - 1) : ℚ) ≤
      (Fintype.card Input : ℚ) * (Fintype.card Input - 1) * ε *
      (Fintype.card Seed : ℚ)^2 / (Fintype.card Output : ℚ) :=
    sum_coincidence_mul_pred_le H h_asu
  have h_cauchy_schwarz :
      (∑ s : Seed, ∑ t : Seed, (C s t : ℚ) - ∑ s : Seed, (C s s : ℚ))^2 ≤
      (∑ s : Seed, ∑ t : Seed, (1 : ℚ) - ∑ s : Seed, (1 : ℚ)) *
      (∑ s : Seed, ∑ t : Seed, (C s t : ℚ)^2 - ∑ s : Seed, (C s s : ℚ)^2) := by
    convert double_sum_cauchy_schwarz
        (fun s t : Seed => if s = t then (0 : ℝ) else 1)
        (fun s t : Seed => if s = t then 0 else (C s t : ℝ)) using 1
    norm_num [Finset.sum_ite, Finset.filter_ne]
    rw [Nat.cast_pred Fintype.card_pos]
    norm_cast
    norm_num [Int.subNatNat_eq_coe]
    ring_nf
  have h_C_diag (s : Seed) : C s s = Fintype.card Input :=
    (Fintype.card_congr (Equiv.subtypeEquivRight fun _ => eq_self_iff_true _)).trans
      Fintype.card_subtype_true
  have h_sum_C_diag : ∑ s : Seed, (C s s : ℚ) =
      (Fintype.card Input : ℚ) * (Fintype.card Seed : ℚ) := by
    simp only [h_C_diag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have h_sum_C_diag_sq : ∑ s : Seed, (C s s : ℚ)^2 =
      (Fintype.card Input : ℚ)^2 * (Fintype.card Seed : ℚ) := by
    simp only [h_C_diag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have h_sum_C_sq_def : ∑ s : Seed, ∑ t : Seed, (C s t : ℚ)^2 =
      ∑ s : Seed, ∑ t : Seed, (C s t : ℚ) * ((C s t : ℚ) - 1) +
      ∑ s : Seed, ∑ t : Seed, (C s t : ℚ) := by
    simp only [sq, mul_sub, mul_one, Finset.sum_sub_distrib, sub_add_cancel]
  convert h_cauchy_schwarz.trans _ using 1
  · rfl
  · norm_num [h_sum_C, h_sum_C_diag, h_sum_C_diag_sq, h_sum_C_sq_def]
    ring
  · norm_num [h_sum_C, h_sum_C_diag, h_sum_C_diag_sq, h_sum_C_sq_def]
    convert mul_le_mul_of_nonneg_left
        ( add_le_add_right h_sum_C_sq
          ( ( Fintype.card Input : ℚ ) * ( Fintype.card Seed : ℚ ) *
            ( ( Fintype.card Seed : ℚ ) / ( Fintype.card Output : ℚ ) - 1 ) -
            ( Fintype.card Seed : ℚ ) *
              ( ( Fintype.card Input : ℚ ) * ( ( Fintype.card Input : ℚ ) - 1 ) ) ) )
        ( show ( 0 : ℚ ) ≤ ( Fintype.card Seed : ℚ ) * ( Fintype.card Seed - 1 ) by
          exact mul_nonneg ( Nat.cast_nonneg _ )
            (sub_nonneg.mpr (Nat.one_le_cast.mpr Fintype.card_pos))) using 1 <;>
      first | rfl | ring


/--
Every uniform ε-ASU₂ hash family
(i.e. `HashFamily.uniform H ∧ H.almostStronglyUniversal2 ε`) satisfies
`|Seed| ≥ 1 + |Input|·(|Output|−1)² / (|Output|·ε·(|Input|−1) + |Output| − |Input|)`.

*[S94, Theorem 4.3]*
-/
theorem HashFamily.card_seed_lb_of_almostStronglyUniversal2
    [Nonempty Seed] [Nontrivial Input]
    {ε : ℚ} (H : HashFamily Seed Input Output)
    (h_unif : HashFamily.uniform H)
    (hH : H.almostStronglyUniversal2 ε) :
    1 + (Fintype.card Input * (Fintype.card Output - 1) ^ 2 : ℚ) /
        (Fintype.card Output * ε * (Fintype.card Input - 1) +
         Fintype.card Output - Fintype.card Input) ≤
    Fintype.card Seed := by
  classical
  by_cases hv : Fintype.card Output = 1 ∨
      (Fintype.card Output * ε * (Fintype.card Input - 1) +
        Fintype.card Output - Fintype.card Input) ≤ 0 ∨
      (Fintype.card Seed : ℚ) ≤ 1
  · rcases hv with hv | hv | hv
    · rw [show Fintype.card Output = 1 from
          Fintype.card_eq_one_iff.mpr (Fintype.card_eq_one_iff.mp hv)]
      simp only [Nat.cast_one, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero, one_mul, zero_div, add_zero, Nat.one_le_cast]
      exact Fintype.card_pos
    · have hdiv : (Fintype.card Input * (Fintype.card Output - 1) ^ 2 : ℚ) /
          (Fintype.card Output * ε * (Fintype.card Input - 1) +
            Fintype.card Output - Fintype.card Input) ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      linarith [show (1 : ℚ) ≤ Fintype.card Seed from by exact_mod_cast Fintype.card_pos]
    · cases hv.eq_or_lt
      · rcases isEmpty_or_nonempty Output with h | h <;>
          simp_all [Fintype.card_eq_one_iff]
        simp only [HashFamily.uniform] at h_unif
        have hSeq1 : Fintype.card Seed = 1 :=
          Fintype.card_eq_one_iff.mpr ‹∃ x : Seed, ∀ y : Seed, y = x›
        have key := h_unif (Classical.arbitrary Input) (Classical.arbitrary Output)
        simp only [probUniform, hSeq1, Nat.cast_one, div_one, one_div] at key
        rw [inv_eq_one_div, eq_div_iff] at key <;> norm_cast at * <;> aesop
      · simp_all [Fintype.card_le_one_iff]
  · push Not at hv
    have hOpos : (0 : ℚ) < Fintype.card Output := by
      by_contra hle
      push Not at hle
      have hO0 : (Fintype.card Output : ℚ) = 0 := le_antisymm hle (Nat.cast_nonneg _)
      linarith [hv.2.1, show Fintype.card Output * ε * ((Fintype.card Input : ℚ) - 1) +
          Fintype.card Output - Fintype.card Input ≤ 0 by
        simp only [hO0, zero_mul, zero_add]
        linarith [show (1 : ℚ) < Fintype.card Input from by exact_mod_cast Fintype.one_lt_card]]
    have h_stinson_algebra :
        (Fintype.card Input * ((Fintype.card Seed : ℚ) - (Fintype.card Output : ℚ))^2) ≤
        ((Fintype.card Seed : ℚ) - 1) *
        ((Fintype.card Seed : ℚ) * (Fintype.card Output : ℚ) * (1 + (Fintype.card Input - 1) * ε) -
          (Fintype.card Input : ℚ) * (Fintype.card Output : ℚ)^2) := by
      have h_subst := helper_ineq_of_almostStronglyUniversal2 h_unif hH
      field_simp [mul_comm, mul_assoc, mul_left_comm] at h_subst ⊢
      linarith
    have hb : (1 : ℚ) < Fintype.card Seed := by exact_mod_cast hv.2.2
    have hD := hv.2.1
    linarith [(div_le_iff₀ hD).mpr (show Fintype.card Input * (Fintype.card Output - 1 : ℚ) ^ 2 ≤
        (Fintype.card Seed - 1) * (Fintype.card Output * ε * (Fintype.card Input - 1) +
          Fintype.card Output - Fintype.card Input) by
      nlinarith [h_stinson_algebra, sq_nonneg ((Fintype.card Seed : ℚ) - Fintype.card Output)])]

/--
Every strongly-universal₂ hash family satisfies `|Seed| ≥ 1 + |Input| · (|Output| − 1)`.

*[S94, Corollary 4.4]*
-/
theorem HashFamily.card_seed_lb_of_stronglyUniversal2
    [Nonempty Seed] [Nontrivial Input]
    (H : HashFamily Seed Input Output)
    (hH : H.stronglyUniversal2) :
    1 + Fintype.card Input * (Fintype.card Output - 1) ≤ Fintype.card Seed := by
  classical
  have hlb := card_seed_lb_of_almostStronglyUniversal2 H
    (HashFamily.uniform_of_stronglyUniversal2 H hH)
    (almostStronglyUniversal2_of_stronglyUniversal2 H hH)
  by_cases hO2 : 2 ≤ Fintype.card Output
  · have hOpos : (Fintype.card Output : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hO1pos : (Fintype.card Output : ℚ) - 1 ≠ 0 := by
      exact sub_ne_zero_of_ne (by exact_mod_cast (by omega : Fintype.card Output ≠ 1))
    have hdenom : Fintype.card Output * (1 / (Fintype.card Output : ℚ)) *
        ((Fintype.card Input : ℚ) - 1) + Fintype.card Output - Fintype.card Input =
        Fintype.card Output - 1 := by
      rw [mul_one_div_cancel hOpos]; ring
    have hle : (1 : ℚ) + (Fintype.card Input : ℚ) * (Fintype.card Output - 1 : ℕ) ≤
        Fintype.card Seed := by
      rw [Nat.cast_sub (by omega)]
      exact (show (1 : ℚ) + Fintype.card Input * (Fintype.card Output - 1) ^ 2 /
          (Fintype.card Output * (1 / Fintype.card Output) * (Fintype.card Input - 1) +
            Fintype.card Output - Fintype.card Input) =
          1 + Fintype.card Input * (Fintype.card Output - 1) by
        rw [hdenom, sq, mul_div_assoc, mul_div_assoc, div_self hO1pos, mul_one]) ▸ hlb
    exact_mod_cast hle
  · simp only [show Fintype.card Output - 1 = 0 from by omega, Nat.mul_zero, Nat.add_zero]
    exact Fintype.card_pos

private lemma total_collision_count_eq [DecidableEq Input]
    (H : HashFamily Seed Input Output) :
    ∑ x : Input, ∑ y ∈ Finset.univ.erase x,
      (Fintype.card {s : Seed | H s x = H s y} : ℚ) =
    ∑ s : Seed, ∑ a : Output,
      (Fintype.card {x : Input | H s x = a} : ℚ) *
      (Fintype.card {x : Input | H s x = a} - 1) := by
  have h_per_seed (s : Seed) :
      ∑ x : Input, ∑ y ∈ Finset.univ.erase x, (if H s x = H s y then 1 else 0 : ℚ) =
      ∑ a : Output,
        (Fintype.card {x : Input | H s x = a} : ℚ) *
        (Fintype.card {x : Input | H s x = a} - 1) := by
    have h_rearrange :
        ∑ x : Input, ∑ y ∈ Finset.univ.erase x, (if H s x = H s y then 1 else 0 : ℚ) =
        ∑ a : Output,
          ∑ x ∈ Finset.filter (fun x => H s x = a) Finset.univ,
          ∑ y ∈ Finset.filter (fun y => H s y = a) Finset.univ,
          (if x ≠ y then 1 else 0 : ℚ) := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      simp [Finset.sum_ite, Finset.filter_ne, eq_comm, Finset.filter_erase]
    simp_all only [Finset.sum_boole, ne_eq, ite_not, Finset.sum_ite, Finset.sum_const_zero,
      Finset.filter_ne, Finset.sum_const, Finset.card_erase_of_mem, nsmul_eq_mul, mul_one, zero_add,
      Set.coe_setOf, Fintype.card_subtype]
    exact Finset.sum_congr rfl fun x _ => by
      cases Finset.card (Finset.filter (fun y => H s y = x) Finset.univ) <;> simp
  rw [← Finset.sum_congr rfl fun s _ => h_per_seed s, Finset.sum_comm,
    Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)]
  simp [Fintype.card_subtype]

/--
For any hash family, when `|Input| > |Output|`,
some pair of distinct inputs has collision probability at least
`(|Input| − |Output|) / (|Output| · (|Input| − 1))`.

This gives the optimality threshold: no family can be ε-AU for ε below this value.

*[S94, Theorem 3.1]*
-/
theorem HashFamily.exists_collision_lb
    [Nonempty Seed]
    (H : HashFamily Seed Input Output)
    (hlt : Fintype.card Output < Fintype.card Input) :
    ∃ x y : Input, x ≠ y ∧
      (Fintype.card Input - Fintype.card Output : ℚ) /
        (Fintype.card Output * (Fintype.card Input - 1)) ≤
      probUniform (fun s ↦ H s x = H s y) := by
  classical
  by_contra! h_contra
  set c : Input → Input → ℕ := fun x y => Fintype.card {s : Seed | H s x = H s y}
  set εN : ℚ := (Fintype.card Input - Fintype.card Output) /
    ((Fintype.card Output) * ((Fintype.card Input) - 1))
  have h_per_pair (x : Input) (y : Input) (hy : y ∈ Finset.univ.erase x) :
      (c x y : ℚ) < εN * (Fintype.card Seed) := by
    rw [← div_lt_iff₀ (Nat.cast_pos.mpr <| Fintype.card_pos_iff.mpr ⟨Classical.arbitrary Seed⟩)]
    exact h_contra x y (Ne.symm (Finset.ne_of_mem_erase hy))
  haveI : Nonempty Input := Fintype.card_pos_iff.mp (by omega)
  have hOutPos : Fintype.card Output > 0 :=
    Fintype.card_pos_iff.mpr ⟨H (Classical.arbitrary Seed) (Classical.arbitrary Input)⟩
  have h_per_x (x : Input) :
      ∑ y ∈ Finset.univ.erase x, (c x y : ℚ) <
      εN * (Fintype.card Input - 1) * (Fintype.card Seed) := by
    convert Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp <| ?_) (h_per_pair x) using 1 <;>
        norm_num [Finset.card_erase_of_mem (Finset.mem_univ x)]
    · rfl
    · rw [Nat.cast_sub ( by linarith )] ; ring
    · linarith
  have h_sum_lt :
      ∑ x : Input, ∑ y ∈ Finset.univ.erase x, (c x y : ℚ) <
      εN * (Fintype.card Input * (Fintype.card Input - 1)) * (Fintype.card Seed) := by
    convert Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun x _ => h_per_x x using 1
    · rfl
    · norm_num; ring
  have h_cauchy_schwarz_sum :
      ∑ s : Seed, ∑ a : Output, (Fintype.card {x : Input | H s x = a} : ℚ)^2 ≥
      (Fintype.card Input : ℚ)^2 / (Fintype.card Output : ℚ) * (Fintype.card Seed : ℚ) :=
    le_trans (by simp [mul_comm]) (Finset.sum_le_sum fun s _ => cauchy_schwarz_count H s)
  have h_sum_expand :
      ∑ s : Seed, ∑ a : Output,
        (Fintype.card {x : Input | H s x = a} : ℚ) *
        ((Fintype.card {x : Input | H s x = a} : ℚ) - 1) =
      ∑ s : Seed, ∑ a : Output, (Fintype.card {x : Input | H s x = a} : ℚ)^2 -
      ∑ s : Seed, ∑ a : Output, (Fintype.card {x : Input | H s x = a} : ℚ) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, pow_two]
  have h_sum_per_seed (s : Seed) :
      ∑ a : Output, (Fintype.card {x : Input | H s x = a} : ℚ) = (Fintype.card Input : ℚ) := by
    exact_mod_cast sum_fiber_card (H s)
  have h_sum_total :
      ∑ s : Seed, ∑ a : Output, (Fintype.card {x : Input | H s x = a} : ℚ) =
      (Fintype.card Input : ℚ) * (Fintype.card Seed : ℚ) :=
    (Finset.sum_congr rfl fun _ _ => h_sum_per_seed _).trans (by simp [Finset.card_univ, mul_comm])
  have h_lb :
      (Fintype.card Input : ℚ)^2 / (Fintype.card Output : ℚ) * (Fintype.card Seed : ℚ) -
      (Fintype.card Input : ℚ) * (Fintype.card Seed : ℚ) <
      εN * (Fintype.card Input * (Fintype.card Input - 1)) * (Fintype.card Seed) := by
    linarith [total_collision_count_eq H]
  rw [div_mul_eq_mul_div, div_sub', div_lt_iff₀] at h_lb <;> norm_num at *
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
        lt_div_iff₀] at h_lb
    · exact h_lb.not_ge (le_of_sub_nonneg (by ring_nf; positivity))
    · exact mul_pos (Nat.cast_pos.mpr hOutPos)
        (sub_pos.mpr (Nat.one_lt_cast.mpr (lt_of_le_of_lt (by omega) hlt)))
  · contrapose! h_lb
    simp_all only [nonpos_iff_eq_zero, CharP.cast_eq_zero, sub_zero, zero_mul, div_zero,
      le_refl, εN]
  · exact fun h => absurd h (Nat.cast_ne_zero.mpr hOutPos.ne')

end SeedInputOutputFuture

/--
Composing an ε₁-AU family with an ε₂-AU family yields an `(ε₁ + ε₂)`-AU family.

Given `H₁ : Seed₁ → Input → Middle` and `H₂ : Seed₂ → Middle → Output`,
the family `fun (s₁, s₂) x ↦ H₂ s₂ (H₁ s₁ x)` is `(ε₁ + ε₂)`-AU.

*[S94, Theorem 5.4]*
-/
theorem HashFamily.almostUniversal2_comp
    {Input Output : Type*} [DecidableEq Output]
    {Seed₁ Seed₂ Middle : Type*}
    [Fintype Seed₁] [Fintype Seed₂] [DecidableEq Middle]
    {ε₁ ε₂ : ℚ}
    (hε₂ : 0 ≤ ε₂)
    {H₁ : HashFamily Seed₁ Input Middle}
    {H₂ : HashFamily Seed₂ Middle Output}
    (h₁ : H₁.almostUniversal2 ε₁)
    (h₂ : H₂.almostUniversal2 ε₂) :
    HashFamily.almostUniversal2 (ε₁ + ε₂)
      (fun (s : Seed₁ × Seed₂) x ↦ H₂ s.2 (H₁ s.1 x)) := by
  intro x y hxy
  have h_per_s₁ (s₁ : Seed₁) :
        (Fintype.card {s₂ : Seed₂ // H₂ s₂ (H₁ s₁ x) = H₂ s₂ (H₁ s₁ y)}) /
        (Fintype.card Seed₂ : ℚ) ≤ if H₁ s₁ x = H₁ s₁ y then 1 else ε₂ := by
    split_ifs with h
    · simp_all only [almostUniversal2, ne_eq, Fintype.card_subtype_true]
      exact div_self_le_one _
    · exact_mod_cast h₂ h
  have h_composition :
      (Fintype.card {s : Seed₁ × Seed₂ // H₂ s.2 (H₁ s.1 x) = H₂ s.2 (H₁ s.1 y)}) /
      (Fintype.card (Seed₁ × Seed₂) : ℚ) ≤
      (Fintype.card {s₁ : Seed₁ // H₁ s₁ x = H₁ s₁ y}) / (Fintype.card Seed₁ : ℚ) +
      (Fintype.card {s₁ : Seed₁ // H₁ s₁ x ≠ H₁ s₁ y}) / (Fintype.card Seed₁ : ℚ) * ε₂ := by
    rw [probUniform_prod (fun s₁ s₂ => H₂ s₂ (H₁ s₁ x) = H₂ s₂ (H₁ s₁ y)),
        Fintype.card_subtype, Fintype.card_subtype]
    refine (div_le_div_of_nonneg_right (Finset.sum_le_sum fun s₁ _ ↦ h_per_s₁ s₁)
      (Nat.cast_nonneg _)).trans ?_
    simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one, ne_eq]
    ring_nf
    norm_num
  convert h_composition.trans (add_le_add (h₁ hxy)
      (mul_le_of_le_one_left hε₂
      (div_le_one_of_le₀ (mod_cast Fintype.card_subtype_le _) (Nat.cast_nonneg _)))) using 1
  · rfl
  · rfl
