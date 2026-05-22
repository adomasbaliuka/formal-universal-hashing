import UniversalHashing.Basic
import Mathlib.Tactic

/-!
# ε-Almost Universal Hashing

This file defines the notions
- `ε`-almost-universal₂ (ε-AU₂)
- `ε`-almost-strongly-universal₂ (ε-ASU₂)

These are relaxations of `HashFamily.universal2` and
`HashFamily.stronglyUniversal2` where equality/bounds are replaced by `ε`.

## Main definitions

* `HashFamily.almostUniversal2 ε H`: H is `ε`-almost-universal₂ (ε-AU₂) if
  for all distinct `x ≠ y`:
  `Pr_{s}[H s x = H s y] ≤ ε`.

* `HashFamily.uniform H`: H is **uniform** if for all hash inputs `x` and outputs `a`,
  `Pr_{s}[H s x = a] = 1 / |Output|`.

* `HashFamily.almostStronglyUniversal2 ε H`: H is `ε`-almost-strongly-universal₂ (ε-ASU₂) if
  for all distinct inputs `x ≠ y` and all outputs `a b`:
  `Pr_{s}[H s x = a ∧ H s y = b] ≤ ε / |Output|`.
  See ([BKST15] Definition 1.1).
  Note: some papers use a different definition which furthermore requires uniformity,
  e.g., [S94]. We do not.

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

* [BKST15]
  @misc{cryptoeprint:2015/1187,
      author = {Khodakhast Bibak and Bruce M. Kapron and Venkatesh Srinivasan and László Tóth},
      title = {On an almost-universal hash function family with applications to
      authentication and secrecy codes},
      howpublished = {Cryptology {ePrint} Archive, Paper 2015/1187},
      year = {2015},
      url = {https://eprint.iacr.org/2015/1187}
  }

* [S94]
  @Article{Stinson1994,
    author={Stinson, D. R.},
    title={Universal hashing and authentication codes},
    journal={Designs, Codes and Cryptography},
    year={1994},
    month={Jul},
    day={01},
    volume={4},
    number={3},
    pages={369-380},
    issn={1573-7586},
    doi={10.1007/BF01388651},
    url={https://doi.org/10.1007/BF01388651}
  }

-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

section SeedInputOutput

variable {Seed Input Output : Type*}
  [Fintype Seed] [Fintype Output]
  [DecidableEq Output]

/--
A hash family is **ε-almost-universal₂ (ε-AU₂)** with parameter `ε : ℚ` if for any two
distinct inputs `x` and `y`, the probability over a uniform random seed of a collision is
at most `ε`:

  `Pr_{s}[H s x = H s y] ≤ ε`

`HashFamily.universal2` is the special case `ε = 1 / |Output|`; see
`HashFamily.universal2_iff_probUniform`.

*Definition 1.1 in* [BKST15].
-/
def HashFamily.almostUniversal2 (ε : ℚ) (H : HashFamily Seed Input Output) : Prop :=
  ∀ ⦃x y : Input⦄, x ≠ y →
    probUniform (fun s ↦ H s x = H s y) ≤ ε

/--
A hash family is **ε-almost-strongly-universal₂ (ε-ASU₂)** with parameter `ε : ℚ` if
for every pair of distinct inputs `x ≠ y` and all outputs `a, b`:

  `Pr_{s}[H s x = a ∧ H s y = b] ≤ ε / |Output|`

`HashFamily.stronglyUniversal2` is the special case `ε = 1 / |Output|` where the bound is tight;
see `HashFamily.stronglyUniversal2_iff_almostStronglyUniversal2`.

*Definition 1.1 in* [BKST15]. This is the prevalent definition in modern literature.

### Relationship to alternative definitions

[S94] additionally requires **uniformity** `Pr_{s}[H s x = a] = 1 / |Output|`
(see `HashFamily.uniform`), i.e., the conjunction `H.uniform ∧ H.almostStronglyUniversal2 ε`.

The uniformity condition is motivated by Wegman–Carter MACs, where it ensures that
observing a tag `(m, t)` reveals no information about the key.
The two definitions coincide when `ε = 1 / |Output|` (the strongly-universal case):
the joint bound then forces all marginals to equal `1 / |Output|`, implying uniformity.
-/
def HashFamily.almostStronglyUniversal2 (ε : ℚ) (H : HashFamily Seed Input Output) : Prop :=
  ∀ ⦃x y : Input⦄, x ≠ y → ∀ (a b : Output),
    probUniform (fun s ↦ H s x = a ∧ H s y = b) ≤ ε / Fintype.card Output

/--
A hash family is **uniform** if every input maps to every output with equal probability:

  `Pr_{s}[H s x = a] = 1 / |Output|`

[S94] defines ε-ASU₂ as the conjunction
`H.uniform ∧ H.almostStronglyUniversal2 ε`; see `HashFamily.almostStronglyUniversal2` for
a discussion of the two definitions and when they coincide.
-/
def HashFamily.uniform (H : HashFamily Seed Input Output) : Prop :=
  ∀ (x : Input) (a : Output),
    probUniform (fun s ↦ H s x = a) = (1 : ℚ) / Fintype.card Output

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
    · rw [Nat.cast_sum]
    · have : Nonempty Output := Nonempty.intro (H (‹Nonempty Seed›.some) x)
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_ne_zero, mul_div_cancel₀]
    · have := h hxy b b
      rw [probUniform, div_le_iff₀ (Nat.cast_pos.mpr <| Fintype.card_pos)] at this
      rwa [div_mul_eq_mul_div] at this
  convert div_le_div_of_nonneg_right h_sum (Nat.cast_nonneg (Fintype.card Seed)) using 1
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
    by_cases hcard : Fintype.card Output = 0 <;> simp_all [sq]

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

theorem HashFamily.eps_ge_inv_card_of_almostStronglyUniversal2
    [Nonempty Seed] [Nontrivial Input]
    {ε : ℚ} {H : HashFamily Seed Input Output}
    (h : H.almostStronglyUniversal2 ε) :
    (1 : ℚ) / Fintype.card Output ≤ ε := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne Input
  have h_sum : ∑ a : Output, ∑ b : Output,
      (Fintype.card {s : Seed | H s x = a ∧ H s y = b}) = Fintype.card Seed := by
    simp only [Fintype.card_eq_sum_ones, Finset.sum_sigma']
    refine Finset.sum_bij (fun s _ ↦ s.2.2) (by simp) ?_ (by simp) (by simp)
    simp only [Set.coe_setOf, Finset.univ_sigma_univ, Finset.mem_univ, Set.mem_setOf_eq,
    forall_const]
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
  field_simp at h_sum_le ⊢; exact h_sum_le

end SeedInputOutput
