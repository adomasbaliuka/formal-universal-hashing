/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module

public import UniversalHashing.Basic
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star


/-!
# ε-Almost Universal Hashing

This file proves things about
- `ε`-almost-universal₂ (ε-AU₂), see `HashFamily.almostUniversal2`
- `ε`-almost-strongly-universal₂ (ε-ASU₂), see `HashFamily.almostStronglyUniversal2`
- uniformity, see `HashFamily.uniform`

These are relaxations of `HashFamily.universal2` and
`HashFamily.stronglyUniversal2` where equality/bounds are replaced by `ε`.
The definitions are in `UniversalHashing.Basic`.

## Main results

* `HashFamily.universal2_iff_probUniform` (in `Basic`):
  `universal2 ↔ almostUniversal2 (1 / |Output|)`.
* `HashFamily.almostUniversal2_mono`: ε-AU₂ is monotone in `ε`.
* `HashFamily.almostStronglyUniversal2_mono`: ε-ASU₂ is monotone in `ε`.
* `HashFamily.almostUniversal2_of_almostStronglyUniversal2`:
  `almostStronglyUniversal2 ε` implies `almostUniversal2 ε`.
* `HashFamily.stronglyUniversal2_iff_almostStronglyUniversal2`:
  `stronglyUniversal2 ↔ almostStronglyUniversal2 (1 / |Output|)`.
* `HashFamily.almostStronglyUniversal2_of_stronglyUniversal2`:
  `stronglyUniversal2` implies `almostStronglyUniversal2 (1 / |Output|)`.
* `HashFamily.uniform_of_stronglyUniversal2`:
  `stronglyUniversal2` implies `uniform`.
* `HashFamily.almostStronglyUniversal2_eps_lower_bound`:
  `almostStronglyUniversal2 ε` implies `1 / |Output| ≤ ε`.

## References

* [bibak_kapron_srinivasan_toth2015]:
  "On an almost-universal hash function family with applications to authentication
  and secrecy codes" by Khodakhast Bibak, Bruce M. Kapron, Venkatesh Srinivasan
  and László Tóth.
* [stinson1994]: "Universal hashing and authentication codes" by Stinson, D. R.

-/

@[expose] public section

section SeedInputOutput

variable {Seed Input Output : Type*}
  [Fintype Seed] [Fintype Output]
  [DecidableEq Output]

omit [Fintype Output] in
theorem HashFamily.almostUniversal2_mono
    {ε₁ ε₂ : ℚ} (hε : ε₁ ≤ ε₂) (H : HashFamily Seed Input Output)
    (h : H.almostUniversal2 ε₁) : H.almostUniversal2 ε₂ :=
  fun _ _ hxy ↦ (h hxy).trans hε

theorem HashFamily.almostStronglyUniversal2_mono
    {ε₁ ε₂ : ℚ} (hε : ε₁ ≤ ε₂) (H : HashFamily Seed Input Output)
    (h : H.almostStronglyUniversal2 ε₁) : H.almostStronglyUniversal2 ε₂ :=
  fun _ _ hxy a b ↦ (h hxy a b).trans (by gcongr)

theorem HashFamily.almostUniversal2_of_almostStronglyUniversal2
    [Nonempty Seed]
    {ε : ℚ} (H : HashFamily Seed Input Output)
    (h : H.almostStronglyUniversal2 ε) :
    H.almostUniversal2 ε := by
  intro x y hxy
  have h_sum :
      (∑ a : Output, Fintype.card {s : Seed // H s x = a ∧ H s y = a}) ≤ ε * Fintype.card Seed := by
    convert Finset.sum_le_sum fun b hb =>
      show (Fintype.card {s : Seed // H s x = b ∧ H s y = b} : ℚ)
      ≤ ε * Fintype.card Seed / Fintype.card Output from ?_ using 1
    · rfl
    · rw [Nat.cast_sum]
    · have : Nonempty Output := Nonempty.intro (H (‹Nonempty Seed›.some) x)
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_ne_zero, mul_div_cancel₀]
    · have := h hxy b b
      rw [probUniform, div_le_iff₀ (Nat.cast_pos.mpr <| Fintype.card_pos)] at this
      rwa [div_mul_eq_mul_div] at this
  convert div_le_div_of_nonneg_right h_sum (Nat.cast_nonneg (Fintype.card Seed)) using 1
  · rfl
  · simp only [probUniform, Fintype.card_subtype, Nat.cast_sum, Finset.card_filter]
    rw_mod_cast [← Finset.sum_comm]
    congr! 2
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Finset.sum_eq_single (H i x)] <;> aesop
  · rw [mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

theorem HashFamily.almostStronglyUniversal2_of_stronglyUniversal2
    [Nonempty Seed]
    (H : HashFamily Seed Input Output)
    (hsu : H.stronglyUniversal2) :
    H.almostStronglyUniversal2 ((1 : ℚ) / Fintype.card Output) := by
  intro x y hxy a b
  rw [HashFamily.stronglyUniversal2_iff_probUniform] at hsu
  rw [hsu hxy a b, div_div, sq]

/--
`stronglyUniversal2` is equivalent to `almostStronglyUniversal2 (1 / |Output|)`.
Since `1 / |Output|` is the minimum possible ε for any ε-ASU₂ family
(see `almostStronglyUniversal2_eps_lower_bound`), this characterizes strongly universal
families as exactly those achieving the tightest possible near-independence bound.
-/
theorem HashFamily.stronglyUniversal2_iff_almostStronglyUniversal2
    [Nonempty Seed]
    (H : HashFamily Seed Input Output) :
    H.stronglyUniversal2 ↔ H.almostStronglyUniversal2 ((1 : ℚ) / Fintype.card Output) := by
  refine ⟨almostStronglyUniversal2_of_stronglyUniversal2 H, fun h x y hxy a b ↦ ?_⟩
  have h_sum : ∑ a : Output, ∑ b : Output,
      (Fintype.card {i : Seed | H i x = a ∧ H i y = b} : ℚ) = (Fintype.card Seed : ℚ) := by
    simp only [Fintype.card_subtype]
    rw_mod_cast [← Finset.sum_product']
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    simp only [Finset.univ_product_univ, Set.mem_setOf_eq, Finset.sum_boole, Nat.cast_id]
    rw [Finset.sum_congr rfl fun s _ =>
      Finset.card_eq_one.mpr ⟨(H s x, H s y), by aesop⟩]
    simp
  have h_term : ∀ a b : Output,
      (Fintype.card {i : Seed | H i x = a ∧ H i y = b} : ℚ) ≤
      (Fintype.card Seed) / (Fintype.card Output)^2 := by
    intro a b
    specialize h hxy a b
    simp_all only [ne_eq, Set.coe_setOf, probUniform, one_div]
    rw [div_le_iff₀ (Nat.cast_pos.mpr <| Fintype.card_pos)] at h
    exact h.trans_eq (by ring)
  contrapose! h_sum
  refine ne_of_lt ((Finset.sum_lt_sum
      (fun i _ ↦ Finset.sum_le_sum fun j _ ↦ h_term i j) ?_).trans_eq ?_)
  · use a, Finset.mem_univ a
    exact Finset.sum_lt_sum (fun j _ ↦ h_term a j)
        ⟨b, Finset.mem_univ b, (h_term a b).lt_of_ne h_sum⟩
  · simp only [sq, div_eq_mul_inv, mul_inv_rev, mul_left_comm,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    by_cases hcard : Fintype.card Output = 0
    · haveI : Nonempty Output := ⟨a⟩; exact absurd hcard Fintype.card_ne_zero
    · field_simp [show (Fintype.card Output : ℚ) ≠ 0 from Nat.cast_ne_zero.mpr hcard]

theorem HashFamily.uniform_of_stronglyUniversal2
    [Nonempty Seed] [Nontrivial Input]
    (H : HashFamily Seed Input Output)
    (hsu : H.stronglyUniversal2) :
    H.uniform := by
  intro x a
  obtain ⟨y, hy⟩ := exists_ne x
  have h_sum : ∑ b : Output, Fintype.card {s : Seed // H s x = a ∧ H s y = b} =
      Fintype.card {s : Seed // H s x = a} :=
    Fintype.card_sigma.symm.trans <| Fintype.card_congr
      ⟨fun ⟨_, s, h1, _⟩ => ⟨s, h1⟩, fun ⟨s, h1⟩ => ⟨H s y, s, h1, rfl⟩,
       fun ⟨_, _, _, rfl⟩ => rfl, fun _ => rfl⟩
  have h_eq : Fintype.card {s : Seed // H s x = a} =
      (Fintype.card Seed : ℚ) / Fintype.card Output := by
    haveI : Nonempty Output := ⟨a⟩
    have : ∀ b : Output, Fintype.card {s : Seed // H s x = a ∧ H s y = b} =
        (Fintype.card Seed : ℚ) / ((Fintype.card Output) ^ 2 : ℚ) :=
      fun b ↦ hsu (Ne.symm hy) a b
    simp_all [← h_sum, sq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [Fintype.card_ne_zero]
  simp only [probUniform, h_eq]
  field_simp

theorem HashFamily.almostStronglyUniversal2_eps_lower_bound
    [Nonempty Seed] [Nontrivial Input]
    {ε : ℚ} (H : HashFamily Seed Input Output)
    (h : H.almostStronglyUniversal2 ε) :
    (1 : ℚ) / Fintype.card Output ≤ ε := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne Input
  have h_sum : ∑ a : Output, ∑ b : Output,
      (Fintype.card {s : Seed | H s x = a ∧ H s y = b}) = Fintype.card Seed := by
    simp only [Fintype.card_eq_sum_ones, Finset.sum_sigma']
    refine Finset.sum_bij (fun s _ ↦ s.2.2) (by simp) ?_
      (by intro b _; exact ⟨⟨H b x, H b y, ⟨b, rfl, rfl⟩⟩, Finset.mem_univ _, rfl⟩) (by simp)
    simp only [Set.coe_setOf, Set.mem_setOf_eq]
    aesop
  have h_sum_le : ∑ a : Output, ∑ b : Output,
      (Fintype.card {s : Seed | H s x = a ∧ H s y = b}) ≤
      Fintype.card Output ^ 2 * (ε / Fintype.card Output) * Fintype.card Seed := by
    have h_bound : ∀ a b : Output,
        (Fintype.card {s : Seed | H s x = a ∧ H s y = b}) ≤
        (ε / Fintype.card Output) * Fintype.card Seed := by
      intro a b
      have := h hxy a b
      simp_all only [ne_eq, Set.coe_setOf, probUniform, ge_iff_le]
      rwa [div_le_iff₀ (Nat.cast_pos.mpr <| Fintype.card_pos)] at this
    push_cast [sq, mul_assoc]
    exact le_trans
      (Finset.sum_le_sum fun _ _ ↦ Finset.sum_le_sum fun _ _ ↦ h_bound _ _)
      (by simp)
  by_cases hcard : Fintype.card Output = 0 <;> simp_all [sq, mul_assoc, div_eq_mul_inv]
  field_simp at h_sum_le ⊢
  exact le_of_mul_le_mul_left
    (by rw [mul_one, ← mul_assoc]; exact h_sum_le)
    (Nat.cast_pos.mpr Fintype.card_pos)

end SeedInputOutput

end
