/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module

public import UniversalHashing.Basic
public import UniversalHashing.LinearModp
public import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.LinearCombination

/-! # Theorems from the universal-hashing literature

Theorems from the papers reviewed in `doc-report.md` (repository root) that are
statable with the definitions in `UniversalHashing.Basic`; each statement cites its
source.

Contents:
* the one-time-pad upgrade: padding a Δ-universal family with a uniform additive pad
  yields a strongly universal family (`stronglyUniversal2_pad`,
  `almostStronglyUniversal2_pad`, `uniform_pad`);
* the optimality bound `ε ≥ 1/|Output|` for ε-A∆U families
  (`almostDeltaUniversal2_eps_lower_bound`);
* Krawczyk's characterization of ε-otp-security for ⊕-linear families:
  `balanced ε ↔ almostDeltaUniversal2 ε` (`additive_balanced_iff_almostDeltaUniversal2`);
* the Wiese–Boche collision-flat hierarchy: ASU₂ → ACFU₂ → AU₂
  (`almostCollisionFlatUniversal2_of_almostStronglyUniversal2`,
  `almostUniversal2_of_almostCollisionFlatUniversal2`);
* Stinson's Composition 2 and Cartesian-product constructions
  (`almostStronglyUniversal2_comp`, `uniform_comp`, `almostUniversal2_pi`);
* the multiplicative and MMH\* families over `ZMod p`, their Δ-universality
  (`multHashFamily.deltaUniversal2`, `mmhStar.deltaUniversal2`) and the strongly
  universal padded versions;
* the correspondence between error-correcting codes and almost-universal families
  (`codeHashFamily.almostUniversal2`, `hammingDist_ge_of_almostUniversal2`);
* sharpenings for the affine family `linearHashFamily`.
-/

@[expose] public section

/-! ## The one-time-pad upgrade

Extending the seed of a Δ-universal family by a uniform additive pad produces a
strongly universal family. This is the mechanism behind Wegman–Carter authentication:
implicit in [Wegman, Carter 1981] and [Krawczyk 1994, Theorem 5]; used explicitly in
[Abidin, Larsson 2012].
-/

section Pad

variable {Seed Input Output : Type*}
  [Fintype Seed] [Fintype Output] [DecidableEq Output] [AddCommGroup Output]

/-- Padded events over a pair of inputs are counted by the difference event: the pad
is determined by the first output value. -/
private lemma card_pad (H : HashFamily Seed Input Output) (x y : Input) (a b : Output) :
    Fintype.card {sc : Seed × Output // H sc.1 x + sc.2 = a ∧ H sc.1 y + sc.2 = b}
      = Fintype.card {s : Seed // H s x - H s y = a - b} :=
  Fintype.card_congr
    { toFun := fun sc ↦ ⟨sc.val.1, by
        obtain ⟨h1, h2⟩ := sc.prop
        simpa using congrArg₂ (· - ·) h1 h2⟩
      invFun := fun s ↦ ⟨(s.val, a - H s.val x), by
        refine ⟨by rw [add_comm, sub_add_cancel], ?_⟩
        have hy : H s.val y + (a - H s.val x) = a - (H s.val x - H s.val y) := by abel
        rw [hy, s.prop]; abel⟩
      left_inv := fun sc ↦ by
        apply Subtype.ext
        change (sc.val.1, a - H sc.val.1 x) = sc.val
        refine Prod.ext_iff.mpr ⟨rfl, ?_⟩
        change a - H sc.val.1 x = sc.val.2
        exact (eq_sub_of_add_eq' sc.prop.1).symm
      right_inv := fun s ↦ rfl }

/--
Padding any hash family with a uniform additive pad makes it uniform:
`Pr_{(s,b)}[H s x + b = a] = 1 / |Output|`, with no hypothesis on `H` beyond a
nonempty seed space.
-/
theorem HashFamily.uniform_pad [Nonempty Seed] (H : HashFamily Seed Input Output) :
    HashFamily.uniform (fun (s : Seed × Output) x ↦ H s.1 x + s.2) := by
  intro x a
  have hcard : Fintype.card {sc : Seed × Output // H sc.1 x + sc.2 = a}
      = Fintype.card Seed :=
    Fintype.card_congr
      { toFun := fun sc ↦ sc.val.1
        invFun := fun s ↦ ⟨(s, a - H s x), by rw [add_comm, sub_add_cancel]⟩
        left_inv := fun sc ↦ by
          apply Subtype.ext
          change (sc.val.1, a - H sc.val.1 x) = sc.val
          refine Prod.ext_iff.mpr ⟨rfl, ?_⟩
          change a - H sc.val.1 x = sc.val.2
          exact (eq_sub_of_add_eq' sc.prop).symm
        right_inv := fun s ↦ rfl }
  have hS : (0 : ℚ) < Fintype.card Seed := by exact_mod_cast Fintype.card_pos
  have hK : (0 : ℚ) < Fintype.card Output := by exact_mod_cast Fintype.card_pos
  rw [probUniform, hcard, Fintype.card_prod]
  push_cast
  rw [div_eq_div_iff (by positivity) hK.ne']
  ring

/--
**The one-time-pad upgrade** (perfect version): if `H` is perfectly Δ-universal, then
the padded family `(s, b) ↦ x ↦ H s x + b` is strongly universal.
In particular (with `toeplitzHash.deltaUniversal2`) padded Toeplitz hashing is strongly
universal, complementing the counterexample showing unpadded `toeplitzHash` is not.
-/
theorem HashFamily.stronglyUniversal2_pad (H : HashFamily Seed Input Output)
    (h : H.deltaUniversal2) :
    HashFamily.stronglyUniversal2 (fun (s : Seed × Output) x ↦ H s.1 x + s.2) := by
  intro x y hxy a b
  have hd := h hxy (a - b)
  rw [probUniform] at hd
  have hK : (0 : ℚ) < Fintype.card Output := by exact_mod_cast Fintype.card_pos
  have hS : (Fintype.card Seed : ℚ) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hd
    exact (one_div_pos.mpr hK).ne' hd.symm
  rw [card_pad H x y a b, Fintype.card_prod]
  push_cast
  rw [div_eq_div_iff hS hK.ne'] at hd
  rw [sq, eq_div_iff (by positivity)]
  linear_combination (Fintype.card Output : ℚ) * hd

/--
The one-time-pad upgrade, almost-version: if `H` is ε-A∆U, then the padded family is
ε-ASU (and uniform, by `HashFamily.uniform_pad`).
-/
theorem HashFamily.almostStronglyUniversal2_pad {ε : ℚ} (H : HashFamily Seed Input Output)
    (h : H.almostDeltaUniversal2 ε) :
    HashFamily.almostStronglyUniversal2 ε (fun (s : Seed × Output) x ↦ H s.1 x + s.2) := by
  intro x y hxy a b
  have hd := h hxy (a - b)
  rw [probUniform] at hd
  have hK : (0 : ℚ) < Fintype.card Output := by exact_mod_cast Fintype.card_pos
  rw [probUniform, card_pad H x y a b, Fintype.card_prod]
  push_cast
  rcases eq_or_ne (Fintype.card Seed : ℚ) 0 with hS | hS
  · have hε : 0 ≤ ε := by
      rw [hS, div_zero] at hd
      exact hd
    rw [hS, zero_mul, div_zero]
    exact div_nonneg hε hK.le
  · rw [← div_div]
    exact div_le_div_of_nonneg_right hd (Nat.cast_nonneg _)

/--
No family can be ε-A∆U for `ε < 1/|Output|`: for fixed distinct inputs the difference
probabilities sum to 1 over `b : Output`. The Δ-analogue of
`HashFamily.almostStronglyUniversal2_eps_lower_bound`; the side condition
`1/|R| ≤ ε` appears in [BKST15, Definition 1.1].
-/
theorem HashFamily.almostDeltaUniversal2_eps_lower_bound
    [Nonempty Seed] [Nontrivial Input]
    {ε : ℚ} (H : HashFamily Seed Input Output)
    (h : H.almostDeltaUniversal2 ε) :
    (1 : ℚ) / Fintype.card Output ≤ ε := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne Input
  have h_sum : ∑ b : Output, Fintype.card {s : Seed // H s x - H s y = b}
      = Fintype.card Seed :=
    Fintype.card_sigma.symm.trans <| Fintype.card_congr
      ⟨fun ⟨_, s, _⟩ ↦ s, fun s ↦ ⟨H s x - H s y, s, rfl⟩,
       fun ⟨_, _, rfl⟩ ↦ rfl, fun _ ↦ rfl⟩
  have hS : (0 : ℚ) < Fintype.card Seed := by exact_mod_cast Fintype.card_pos
  have hK : (0 : ℚ) < Fintype.card Output := by exact_mod_cast Fintype.card_pos
  have hb : ∀ b : Output,
      (Fintype.card {s : Seed // H s x - H s y = b} : ℚ) ≤ ε * Fintype.card Seed := by
    intro b
    have := h hxy b
    rwa [probUniform, div_le_iff₀ hS] at this
  have hle : (Fintype.card Seed : ℚ)
      ≤ Fintype.card Output * (ε * Fintype.card Seed) := by
    calc (Fintype.card Seed : ℚ)
        = ∑ b : Output, (Fintype.card {s : Seed // H s x - H s y = b} : ℚ) := by
          exact_mod_cast h_sum.symm
      _ ≤ ∑ _b : Output, ε * Fintype.card Seed := Finset.sum_le_sum fun b _ ↦ hb b
      _ = Fintype.card Output * (ε * Fintype.card Seed) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [div_le_iff₀ hK]
  nlinarith [hle, hS]

end Pad

/-! ## Additive families: balancedness ↔ Δ-universality ([Krawczyk 1994]) -/

section Additive

variable {Seed Input Output : Type*}
  [Fintype Seed] [Fintype Output] [DecidableEq Output]
  [AddCommGroup Input] [AddCommGroup Output]

omit [Fintype Seed] [Fintype Output] [DecidableEq Output] in
/-- An additive family sends `0` to `0`. -/
theorem HashFamily.additive.map_zero {H : HashFamily Seed Input Output}
    (hadd : H.additive) (s : Seed) : H s 0 = 0 := by
  simpa using (hadd s 0 0).symm

omit [Fintype Seed] [Fintype Output] [DecidableEq Output] in
/-- An additive family sends differences to differences. -/
theorem HashFamily.additive.map_sub {H : HashFamily Seed Input Output}
    (hadd : H.additive) (s : Seed) (x y : Input) : H s (x - y) = H s x - H s y := by
  have := hadd s (x - y) y
  rw [sub_add_cancel] at this
  rw [this]
  abel

omit [Fintype Output] in
/--
**[Krawczyk 1994, Theorem 6]**: an additive (⊕-linear) family is `ε`-balanced if and
only if it is `ε`-almost-Δ-universal. Combined with [Krawczyk 1994, Theorem 5] — which
identifies ε-A∆U with ε-otp-security — this is the standard route to proving
one-time-pad authentication security for linear families such as Toeplitz hashing.
-/
theorem HashFamily.additive_balanced_iff_almostDeltaUniversal2
    {ε : ℚ} {H : HashFamily Seed Input Output} (hadd : H.additive) :
    H.balanced ε ↔ H.almostDeltaUniversal2 ε := by
  constructor
  · intro hbal x y hxy b
    calc probUniform (fun s ↦ H s x - H s y = b)
        = probUniform (fun s ↦ H s (x - y) = b) :=
          probUniform_congr fun s ↦ by rw [hadd.map_sub s x y]
      _ ≤ ε := hbal (sub_ne_zero_of_ne hxy) b
  · intro hau x hx c
    calc probUniform (fun s ↦ H s x = c)
        = probUniform (fun s ↦ H s x - H s 0 = c) :=
          probUniform_congr fun s ↦ by rw [hadd.map_zero s, sub_zero]
      _ ≤ ε := hau hx c

end Additive

/-! ## Collision-flat universality ([Wiese, Boche 2024]) -/

section ACFU

variable {Seed Input Output : Type*}
  [Fintype Seed] [Fintype Output] [DecidableEq Output]

/--
**[Wiese, Boche 2024, Lemma 1.2(2)]**: every uniform `ε`-ASU₂ family is `ε`-ACFU₂ —
the collision-flatness condition is the diagonal case `a = b` of the ASU₂ bound.
-/
theorem HashFamily.almostCollisionFlatUniversal2_of_almostStronglyUniversal2
    {ε : ℚ} {H : HashFamily Seed Input Output}
    (hu : H.uniform) (h : H.almostStronglyUniversal2 ε) :
    HashFamily.almostCollisionFlatUniversal2 ε H :=
  ⟨hu, fun _ _ hxy a ↦ h hxy a a⟩

/--
**[Wiese, Boche 2024, Lemma 1.2(1)]**: every `ε`-ACFU₂ family is `ε`-AU₂ — summing the
collision-flatness bound over the `|Output|` possible collision values.

(`Nonempty Output` corresponds to the nontriviality assumption `2 ≤ |A|` of the paper;
with no outputs at all the seed space is empty too and `ε` is unconstrained.)
-/
theorem HashFamily.almostUniversal2_of_almostCollisionFlatUniversal2
    [Nonempty Output] {ε : ℚ} {H : HashFamily Seed Input Output}
    (h : HashFamily.almostCollisionFlatUniversal2 ε H) :
    H.almostUniversal2 ε := by
  intro x y hxy
  have hK : (0 : ℚ) < Fintype.card Output := by exact_mod_cast Fintype.card_pos
  -- Partition the collision event by the value at which the collision occurs.
  have h_sum : ∑ a : Output, Fintype.card {s : Seed // H s x = a ∧ H s y = a}
      = Fintype.card {s : Seed // H s x = H s y} :=
    Fintype.card_sigma.symm.trans <| Fintype.card_congr
      ⟨fun p ↦ ⟨p.2.val, p.2.prop.1.trans p.2.prop.2.symm⟩,
       fun s ↦ ⟨H s.val x, s.val, rfl, s.prop.symm⟩,
       fun p ↦ by
         obtain ⟨a, s, h1, h2⟩ := p
         cases h1
         rfl,
       fun s ↦ rfl⟩
  have key : probUniform (fun s ↦ H s x = H s y)
      = ∑ a : Output, probUniform (fun s ↦ H s x = a ∧ H s y = a) := by
    unfold probUniform
    rw [← Finset.sum_div]
    congr 1
    exact_mod_cast h_sum.symm
  rw [key]
  calc ∑ a : Output, probUniform (fun s ↦ H s x = a ∧ H s y = a)
      ≤ ∑ _a : Output, ε / Fintype.card Output :=
        Finset.sum_le_sum fun a _ ↦ h.2 hxy a
    _ = ε := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

end ACFU

/-! ## Composition and product constructions ([S94] = Stinson 1994) -/

section Comp

variable {Input Output : Type*} [Fintype Output] [DecidableEq Output]
  {Seed₁ Seed₂ Middle : Type*}
  [Fintype Seed₁] [Fintype Seed₂] [DecidableEq Middle]
  {H₁ : HashFamily Seed₁ Input Middle}
  {H₂ : HashFamily Seed₂ Middle Output}

omit [DecidableEq Middle] in
/--
Composition with a uniform outer family (independent seeds) is uniform,
regardless of the inner family. The uniformity half of [S94, Theorem 5.5].
-/
theorem HashFamily.uniform_comp [Nonempty Seed₁] (h₂u : H₂.uniform) :
    HashFamily.uniform (fun (s : Seed₁ × Seed₂) x ↦ H₂ s.2 (H₁ s.1 x)) := by
  intro x a
  rw [probUniform, probUniform_prod (fun s₁ s₂ ↦ H₂ s₂ (H₁ s₁ x) = a)]
  have hin : ∀ s₁ : Seed₁,
      (Fintype.card {s₂ : Seed₂ // H₂ s₂ (H₁ s₁ x) = a} : ℚ) / Fintype.card Seed₂
        = 1 / Fintype.card Output := by
    intro s₁
    have := h₂u (H₁ s₁ x) a
    rwa [probUniform] at this
  have hS₁ : (Fintype.card Seed₁ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Finset.sum_congr rfl fun s₁ _ ↦ hin s₁, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_comm, mul_div_assoc, div_self hS₁, mul_one]

/--
**Composition 2** [S94, Theorem 5.5]: composing an `ε₁`-AU family with a uniform
`ε₂`-ASU family (independent seeds) yields an `(ε₁ + ε₂)`-ASU family. (Together with
`HashFamily.uniform_comp` this gives the full S94 statement, whose ε-ASU notion
includes uniformity.) Companion to the proven `HashFamily.almostUniversal2_comp`
[S94, Theorem 5.4]; this is the composition theorem used for key-length-efficient
authentication in [Abidin, Larsson 2012].
-/
theorem HashFamily.almostStronglyUniversal2_comp {ε₁ ε₂ : ℚ}
    (hε₂ : 0 ≤ ε₂)
    (h₁ : H₁.almostUniversal2 ε₁)
    (h₂u : H₂.uniform)
    (h₂ : H₂.almostStronglyUniversal2 ε₂) :
    HashFamily.almostStronglyUniversal2 (ε₁ + ε₂)
      (fun (s : Seed₁ × Seed₂) x ↦ H₂ s.2 (H₁ s.1 x)) := by
  intro x y hxy a b
  haveI : Nonempty Output := ⟨a⟩
  have hK : (0 : ℚ) < Fintype.card Output := by exact_mod_cast Fintype.card_pos
  -- Bound the inner probability for each fixed `s₁`, by whether `H₁` collides on it.
  have h_per_s₁ (s₁ : Seed₁) :
      (Fintype.card {s₂ : Seed₂ // H₂ s₂ (H₁ s₁ x) = a ∧ H₂ s₂ (H₁ s₁ y) = b} : ℚ) /
        Fintype.card Seed₂
      ≤ if H₁ s₁ x = H₁ s₁ y then (1 : ℚ) / Fintype.card Output
        else ε₂ / (Fintype.card Output : ℚ) := by
    split_ifs with hcol
    · have hu := h₂u (H₁ s₁ x) a
      rw [probUniform] at hu
      rw [← hu]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast Fintype.card_subtype_mono _ _ fun s₂ hs ↦ And.left hs
    · have := h₂ hcol a b
      rwa [probUniform] at this
  -- Split the product-seed probability by the collision behaviour of `s₁`.
  have h_comp :
      probUniform (fun s : Seed₁ × Seed₂ ↦
          H₂ s.2 (H₁ s.1 x) = a ∧ H₂ s.2 (H₁ s.1 y) = b)
      ≤ ((Finset.univ.filter (fun s₁ : Seed₁ ↦ H₁ s₁ x = H₁ s₁ y)).card : ℚ)
            / Fintype.card Seed₁ * (1 / Fintype.card Output)
        + ((Finset.univ.filter (fun s₁ : Seed₁ ↦ ¬ H₁ s₁ x = H₁ s₁ y)).card : ℚ)
            / Fintype.card Seed₁ * (ε₂ / Fintype.card Output) := by
    rw [probUniform,
      probUniform_prod (fun s₁ s₂ ↦ H₂ s₂ (H₁ s₁ x) = a ∧ H₂ s₂ (H₁ s₁ y) = b)]
    refine (div_le_div_of_nonneg_right (Finset.sum_le_sum fun s₁ _ ↦ h_per_s₁ s₁)
      (Nat.cast_nonneg _)).trans ?_
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    apply le_of_eq
    ring
  refine h_comp.trans ?_
  have hPcoll : ((Finset.univ.filter (fun s₁ : Seed₁ ↦ H₁ s₁ x = H₁ s₁ y)).card : ℚ)
      / Fintype.card Seed₁ ≤ ε₁ := by
    have := h₁ hxy
    rwa [probUniform, Fintype.card_subtype] at this
  have hPncoll : ((Finset.univ.filter (fun s₁ : Seed₁ ↦ ¬ H₁ s₁ x = H₁ s₁ y)).card : ℚ)
      / Fintype.card Seed₁ ≤ 1 :=
    div_le_one_of_le₀ (mod_cast Finset.card_filter_le _ _) (Nat.cast_nonneg _)
  calc _ ≤ ε₁ * (1 / Fintype.card Output) + 1 * (ε₂ / Fintype.card Output) :=
        add_le_add
          (mul_le_mul_of_nonneg_right hPcoll (by positivity))
          (mul_le_mul_of_nonneg_right hPncoll (div_nonneg hε₂ hK.le))
    _ = (ε₁ + ε₂) / Fintype.card Output := by ring

end Comp

/--
**Cartesian product** [S94, Theorem 5.3]: applying an `ε`-AU family coordinatewise
(with a shared seed) to `i`-tuples is still `ε`-AU.
-/
theorem HashFamily.almostUniversal2_pi
    {Seed Input Output : Type*} [Fintype Seed] [DecidableEq Output]
    {ε : ℚ} {H : HashFamily Seed Input Output}
    (h : H.almostUniversal2 ε) (i : ℕ) :
    HashFamily.almostUniversal2 ε
      (fun s (x : Fin i → Input) (j : Fin i) ↦ H s (x j)) := by
  intro x y hxy
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
  refine le_trans ?_ (h hj)
  unfold probUniform
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Fintype.card_subtype_mono _ _ fun s hs ↦ congrFun hs j

/-! ## Multiplicative and multilinear families over `ZMod p`

The multiplicative family `a ↦ (x ↦ a*x)` and its multilinear generalization MMH\*
are perfectly Δ-universal; padding them (`HashFamily.stronglyUniversal2_pad`) yields
the classical strongly universal families.
-/

section Multilinear

variable (p : ℕ) [Fact p.Prime]

/-- The multiplicative family `h_a(x) = a * x` over `ZMod p`, with `a` unrestricted. -/
def multHashFamily : HashFamily (ZMod p) (ZMod p) (ZMod p) :=
  fun a x ↦ a * x

/--
The multiplicative family is perfectly Δ-universal: for `x ≠ y` the map
`a ↦ a * (x - y)` is an additive bijection of `ZMod p`.
-/
theorem multHashFamily.deltaUniversal2 : (multHashFamily p).deltaUniversal2 := by
  intro x y hxy b
  rw [probUniform_congr (q := fun a : ZMod p ↦ a * (x - y) = b)
    (fun a ↦ by simp [multHashFamily, mul_sub])]
  refine probUniform_eq_of_additive_surjective (fun s t ↦ by ring) ?_ b
  intro c
  exact ⟨c / (x - y), by field_simp [sub_ne_zero_of_ne hxy]⟩

/--
**The affine family is strongly universal** [Carter, Wegman 1979, family H₁]:
`h_{a,b}(x) = a*x + b` with *unrestricted* `a` (contrast `linearHashFamily`, which
requires `a ≠ 0` and is therefore collision-free but not Δ-flat, see
`linearHashFamily.not_deltaUniversal2`). Obtained from `multHashFamily` by the
one-time-pad upgrade.
-/
theorem multHashFamily.stronglyUniversal2_pad :
    HashFamily.stronglyUniversal2
      (fun (s : ZMod p × ZMod p) x ↦ multHashFamily p s.1 x + s.2) :=
  HashFamily.stronglyUniversal2_pad _ (multHashFamily.deltaUniversal2 p)

/--
**MMH\*** (Multilinear Modular Hashing) [Halevi, Krawczyk 1997; BKST15, Definition 1.2]:
the key `x ∈ (ZMod p)^k` hashes a message `m ∈ (ZMod p)^k` to the dot product
`∑ i, m i * x i` modulo `p`.
-/
def mmhStar (k : ℕ) : HashFamily (Fin k → ZMod p) (Fin k → ZMod p) (ZMod p) :=
  fun x m ↦ ∑ i, m i * x i

/--
**[BKST15, Theorem 1.3]** (Halevi–Krawczyk): MMH\* is a Δ-universal family of hash
functions. For `m ≠ m'` the difference map `x ↦ ∑ i, (m i - m' i) * x i` is a nonzero
linear functional, hence a surjective additive map, so all its fibers are equinumerous.
-/
theorem mmhStar.deltaUniversal2 (k : ℕ) : (mmhStar p k).deltaUniversal2 := by
  intro m m' hmm b
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hmm
  have haj : m j - m' j ≠ 0 := sub_ne_zero_of_ne hj
  rw [probUniform_congr (q := fun x : Fin k → ZMod p ↦ ∑ i, (m i - m' i) * x i = b)
    (fun x ↦ by simp [mmhStar, sub_mul, Finset.sum_sub_distrib])]
  refine probUniform_eq_of_additive_surjective
    (fun s t ↦ by simp [mul_add, Finset.sum_add_distrib]) ?_ b
  intro c
  refine ⟨Pi.single j (c / (m j - m' j)), ?_⟩
  change ∑ i, (m i - m' i) * (Pi.single j (c / (m j - m' j)) : Fin k → ZMod p) i = c
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
    (fun i _ hij ↦ by rw [Pi.single_eq_of_ne hij, mul_zero]), Pi.single_eq_same]
  field_simp

/--
MMH\* with a one-time pad is strongly universal — the standard Wegman–Carter
message-authentication construction.
-/
theorem mmhStar.stronglyUniversal2_pad (k : ℕ) :
    HashFamily.stronglyUniversal2
      (fun (s : (Fin k → ZMod p) × ZMod p) m ↦ mmhStar p k s.1 m + s.2) :=
  HashFamily.stronglyUniversal2_pad _ (mmhStar.deltaUniversal2 p k)

end Multilinear

/-! ## Error-correcting codes and almost-universal families

A code with large minimum distance is exactly an almost-universal hash family: hash a
message by reading off one (randomly chosen) coordinate of its codeword. Distinct
messages then collide precisely on the coordinates where their codewords agree.
See [Stinson, *Universal hash families and the leftover hash lemma*, Theorem 2.1];
the connection goes back to [Bierbrauer–Johansson–Kabatianskii–Smeets 1993].
-/

section Codes

/--
The hash family induced by an encoding: the seed selects a coordinate, and a message
is hashed to the symbol of its codeword at that coordinate.
-/
def codeHashFamily {Message ι α : Type*} (enc : Message → (ι → α)) :
    HashFamily ι Message α :=
  fun i x ↦ enc x i

/--
**[Stinson, LHL survey, Theorem 2.1]** (one direction): an encoding whose minimum
distance is at least `d` induces a `(1 - d/n)`-almost-universal family, where
`n = |ι|` is the code length. For a `(n, K, d, q)` code this is exactly the
`(1 − d/n)`-AU`(n; K, q)` family of the paper.
-/
theorem codeHashFamily.almostUniversal2 {Message ι α : Type*}
    [Fintype ι] [DecidableEq α] {d : ℕ} (enc : Message → (ι → α))
    (hd : ∀ ⦃x y : Message⦄, x ≠ y → d ≤ hammingDist (enc x) (enc y)) :
    (codeHashFamily enc).almostUniversal2 (1 - (d : ℚ) / Fintype.card ι) := by
  intro x y hxy
  rw [probUniform]
  -- Capture the agreement count exactly as it appears in the goal, so that the
  -- partition identity below shares its `Decidable` instance.
  set A := Fintype.card {i // codeHashFamily enc i x = codeHashFamily enc i y} with hA
  -- Agreements and disagreements partition the coordinates.
  have hcard : (A : ℚ) + hammingDist (enc x) (enc y) = Fintype.card ι := by
    rw [hA]
    classical
    simp only [codeHashFamily, hammingDist, Fintype.card_subtype]
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun i ↦ enc x i = enc y i)
  have hdle : (d : ℚ) ≤ hammingDist (enc x) (enc y) := by exact_mod_cast hd hxy
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · -- No coordinates: the probability is `0/0 = 0`, and the bound is `1`.
    have hd0 : (d : ℚ) = 0 := by
      have hle : (hammingDist (enc x) (enc y) : ℚ) ≤ 0 := by
        have := hammingDist_le_card_fintype (x := enc x) (y := enc y)
        rw [h0] at this
        exact_mod_cast this
      have : (0 : ℚ) ≤ d := Nat.cast_nonneg _
      linarith
    rw [h0, Nat.cast_zero, div_zero, hd0, zero_div, sub_zero]
    norm_num
  · have hn : (0 : ℚ) < Fintype.card ι := by exact_mod_cast hpos
    rw [div_le_iff₀ hn]
    have hrhs : (1 - (d : ℚ) / Fintype.card ι) * Fintype.card ι = Fintype.card ι - d := by
      field_simp
    rw [hrhs]
    linarith

/--
**[Stinson, LHL survey, Theorem 2.1]** (converse direction): an `ε`-almost-universal
family is a code of minimum distance at least `(1 - ε)·n`, where the codeword of a
message `x` records its hash under every seed and `n = |Seed|` is the number of seeds.
-/
theorem hammingDist_ge_of_almostUniversal2 {Seed Input Output : Type*}
    [Fintype Seed] [DecidableEq Output] {ε : ℚ} {H : HashFamily Seed Input Output}
    (h : H.almostUniversal2 ε) ⦃x y : Input⦄ (hxy : x ≠ y) :
    (1 - ε) * Fintype.card Seed ≤ hammingDist (fun s ↦ H s x) (fun s ↦ H s y) := by
  rcases Nat.eq_zero_or_pos (Fintype.card Seed) with h0 | hpos
  · haveI : IsEmpty Seed := Fintype.card_eq_zero_iff.mp h0
    rw [h0]
    simp [hammingDist]
  · have hn : (0 : ℚ) < Fintype.card Seed := by exact_mod_cast hpos
    have hcoll := h hxy
    rw [probUniform, div_le_iff₀ hn] at hcoll
    set A := Fintype.card {s // H s x = H s y} with hA
    have hcard : (A : ℚ) + hammingDist (fun s ↦ H s x) (fun s ↦ H s y)
        = Fintype.card Seed := by
      rw [hA]
      classical
      simp only [hammingDist, Fintype.card_subtype]
      exact_mod_cast Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun s ↦ H s x = H s y)
    nlinarith [hcard, hcoll]

end Codes

/-! ## Sharpenings for the affine family `linearHashFamily`

`linearHashFamily p` is `h_{a,b}(x) = a*x + b` with `a ≠ 0`. Only `universal2` is
currently proven (`linearHashFamily.universal2`); the following classical facts are
strictly sharper. (Cf. [Carter, Wegman 1979, family H₁]; the exact collision-freeness
and Δ-behaviour of the `a ≠ 0` variant are folklore.)
-/

section LinearModp

variable (p : ℕ) [Fact p.Prime]

/--
With `a ≠ 0`, the map `x ↦ a*x + b` is injective, so distinct inputs *never* collide:
the family is `0`-AU — the strongest possible collision bound, sharper than
`linearHashFamily.universal2`.
-/
theorem linearHashFamily.almostUniversal2_zero :
    (linearHashFamily p).almostUniversal2 0 := by
  intro x y hxy
  have : IsEmpty {i : LinearIndex p // linearHashFamily p i x = linearHashFamily p i y} := by
    refine ⟨fun i ↦ i.val.prop ?_⟩
    have hi := i.prop
    have hz : i.val.val.1 * (x - y) = 0 := by
      simp only [linearHashFamily] at hi
      linear_combination hi
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h (sub_ne_zero_of_ne hxy)
  rw [probUniform, Fintype.card_eq_zero, Nat.cast_zero, zero_div]

/-- `linearHashFamily` is uniform: the pad `b` alone equidistributes every output. -/
theorem linearHashFamily.uniform :
    (linearHashFamily p).uniform := by
  intro x a
  have h2 : (2 : ℕ) ≤ p := (Fact.out : p.Prime).two_le
  have hcard : Fintype.card {i : LinearIndex p // linearHashFamily p i x = a}
      = Fintype.card {a' : ZMod p // a' ≠ 0} :=
    Fintype.card_congr
      { toFun := fun i ↦ ⟨i.val.val.1, i.val.prop⟩
        invFun := fun a' ↦ ⟨⟨(a'.val, a - a'.val * x), a'.prop⟩, by
          change a'.val * x + (a - a'.val * x) = a
          ring⟩
        left_inv := fun i ↦ by
          apply Subtype.ext
          apply Subtype.ext
          change (i.val.val.1, a - i.val.val.1 * x) = i.val.val
          refine Prod.ext_iff.mpr ⟨rfl, ?_⟩
          change a - i.val.val.1 * x = i.val.val.2
          have hi : i.val.val.1 * x + i.val.val.2 = a := i.prop
          linear_combination -hi
        right_inv := fun a' ↦ rfl }
  have hseed : Fintype.card (LinearIndex p)
      = Fintype.card {a' : ZMod p // a' ≠ 0} * p := by
    rw [Fintype.card_congr
      (show LinearIndex p ≃ {a' : ZMod p // a' ≠ 0} × ZMod p from
        { toFun := fun i ↦ (⟨i.val.1, i.prop⟩, i.val.2)
          invFun := fun v ↦ ⟨(v.1.val, v.2), v.1.prop⟩
          left_inv := fun i ↦ rfl
          right_inv := fun v ↦ rfl })]
    simp [ZMod.card]
  have hne : Fintype.card {a' : ZMod p // a' ≠ 0} = p - 1 := by
    simp [Fintype.card_subtype_compl, ZMod.card]
  rw [probUniform, hcard, hseed, hne, ZMod.card]
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h2
    linarith
  have hp0 : (0 : ℚ) < (p : ℚ) := by positivity
  push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
  rw [div_eq_div_iff (by positivity) hp0.ne']
  ring

/--
`linearHashFamily` is `1/(p-1)`-A∆U: for `x ≠ y` and `c ≠ 0` the difference
`h(x) - h(y) = a*(x - y)` hits `c` for exactly one of the `p - 1` values of `a`
(and never hits `c = 0`).
-/
theorem linearHashFamily.almostDeltaUniversal2 :
    (linearHashFamily p).almostDeltaUniversal2 ((1 : ℚ) / ((p : ℚ) - 1)) := by
  intro x y hxy c
  have h2 : (2 : ℕ) ≤ p := (Fact.out : p.Prime).two_le
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h2
    linarith
  have hd : x - y ≠ 0 := sub_ne_zero_of_ne hxy
  rcases eq_or_ne c 0 with rfl | hc
  · -- The difference `a * (x - y)` is never `0` since `a ≠ 0`.
    have : IsEmpty {i : LinearIndex p //
        linearHashFamily p i x - linearHashFamily p i y = 0} := by
      refine ⟨fun i ↦ i.val.prop ?_⟩
      have hi := i.prop
      have hz : i.val.val.1 * (x - y) = 0 := by
        simp only [linearHashFamily] at hi
        linear_combination hi
      rcases mul_eq_zero.mp hz with h | h
      · exact h
      · exact absurd h hd
    rw [probUniform, Fintype.card_eq_zero, Nat.cast_zero, zero_div]
    positivity
  · -- `a` is determined as `c / (x - y)`; `b` is free.
    have hcard : Fintype.card {i : LinearIndex p //
        linearHashFamily p i x - linearHashFamily p i y = c} = p := by
      rw [Fintype.card_congr
        (show {i : LinearIndex p //
            linearHashFamily p i x - linearHashFamily p i y = c} ≃ ZMod p from
          { toFun := fun i ↦ i.val.val.2
            invFun := fun b ↦ ⟨⟨(c * (x - y)⁻¹, b), mul_ne_zero hc (inv_ne_zero hd)⟩, by
              change c * (x - y)⁻¹ * x + b - (c * (x - y)⁻¹ * y + b) = c
              field_simp
              ring⟩
            left_inv := fun i ↦ by
              apply Subtype.ext
              apply Subtype.ext
              change (c * (x - y)⁻¹, i.val.val.2) = i.val.val
              have hi : i.val.val.1 * x + i.val.val.2
                  - (i.val.val.1 * y + i.val.val.2) = c := i.prop
              have ha : i.val.val.1 * (x - y) = c := by linear_combination hi
              refine Prod.ext_iff.mpr ⟨?_, rfl⟩
              change c * (x - y)⁻¹ = i.val.val.1
              rw [← div_eq_mul_inv, div_eq_iff hd]
              exact ha.symm
            right_inv := fun b ↦ rfl }), ZMod.card]
    have hseed : Fintype.card (LinearIndex p)
        = Fintype.card {a' : ZMod p // a' ≠ 0} * p := by
      rw [Fintype.card_congr
        (show LinearIndex p ≃ {a' : ZMod p // a' ≠ 0} × ZMod p from
          { toFun := fun i ↦ (⟨i.val.1, i.prop⟩, i.val.2)
            invFun := fun v ↦ ⟨(v.1.val, v.2), v.1.prop⟩
            left_inv := fun i ↦ rfl
            right_inv := fun v ↦ rfl })]
      simp [ZMod.card]
    have hne : Fintype.card {a' : ZMod p // a' ≠ 0} = p - 1 := by
      simp [Fintype.card_subtype_compl, ZMod.card]
    rw [probUniform, hcard, hseed, hne]
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
    rw [div_le_div_iff₀ (by positivity) hp1]
    ring_nf
    nlinarith [hp1]

/--
`linearHashFamily` is **not** perfectly Δ-universal: differences never hit `0`
(probability `0 ≠ 1/p`). Restricting to `a ≠ 0` trades Δ-flatness for
collision-freeness.
-/
theorem linearHashFamily.not_deltaUniversal2 :
    ¬ (linearHashFamily p).deltaUniversal2 := by
  intro h
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have hd := h (show (1 : ZMod p) ≠ 0 from one_ne_zero) 0
  have hempty : IsEmpty {i : LinearIndex p //
      linearHashFamily p i 1 - linearHashFamily p i 0 = 0} := by
    refine ⟨fun i ↦ i.val.prop ?_⟩
    have hi := i.prop
    simp only [linearHashFamily] at hi
    linear_combination hi
  rw [probUniform, Fintype.card_eq_zero, Nat.cast_zero, zero_div] at hd
  have hK : (0 : ℚ) < Fintype.card (ZMod p) := by exact_mod_cast Fintype.card_pos
  exact (one_div_pos.mpr hK).ne' hd.symm

end LinearModp

end
