import UniversalHashing.Basic

/-!
The hash family "all functions" has all properties we define.
It is completely impractical for pretty much all use-cases (due to being too big).

This file just proves those statements for the sake if illustrating this fact and adding confidence
that the definitions are correct.
-/

set_option relaxedAutoImplicit false

section

variable {Seed Input Output : Type*}
  [Fintype Seed] [Fintype Input] [Fintype Output]
  [DecidableEq Input] [DecidableEq Output]

/-- "All functions" as a hash family is strongly-universal-n for any n."-/
theorem all_functions_strongly_universal_n (n : ℕ) :
    HashFamily.stronglyUniversal_n n (fun (s : Input → Output) (i : Input) => s i) := by
  intro
  rename_i a ha
  intro ha_inj b
  have h_card : Fintype.card {f : Input → Output // ∀ j, f (ha j) = b j}
      = Fintype.card (Output) ^ (Fintype.card Input - n) := by
    have h_card : Fintype.card {f : Input → Output // ∀ j, f (ha j) = b j}
        = Fintype.card {f : {x : Input // x ∉ Set.range ha} → Output // True} := by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      refine Finset.card_bij (fun f hf => fun x => f x) ?_ ?_ ?_
      · intros
        simp_all only [Finset.filter_true, Finset.mem_univ]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff, Subtype.forall,
          Set.mem_range, not_exists]
        intro a₁ ha₁ a₂ ha₂ h x; by_cases hx : ∃ j, ha j = x <;> aesop
      · intro f hf
        refine ⟨fun x => if hx : x ∈ Set.range ha
            then b (Classical.choose hx)
            else f ⟨x, hx⟩, ?_, ?_⟩
        <;> simp [ha_inj.eq_iff]
        grind
    simp_all [Fintype.card_subtype]
    have : Finset.filter (fun x => ∀ j : Fin n, ¬ha j = x) Finset.univ
      = Finset.univ \ Finset.image ha Finset.univ := by
      ext; simp [Finset.mem_sdiff, Finset.mem_image]
    rw [this, Finset.card_sdiff]
    simp only [Finset.card_univ, Finset.inter_univ, Finset.card_image_of_injective _ ha_inj,
      Fintype.card_fin]
  by_cases h : Fintype.card Output = 0 <;> simp_all only [Nat.cast_pow, CharP.cast_eq_zero,
      Fintype.card_pi, Finset.prod_const, Finset.card_univ]
  · cases n <;> simp_all [Fintype.card_eq_zero_iff]
    exact absurd (Fintype.card_pos_iff.mpr ⟨b 0⟩) (by simp)
  · rw [eq_div_iff (by positivity), ← pow_add, Nat.sub_add_cancel]
    simpa using Fintype.card_le_of_injective ha ha_inj

/-- "all functions" is a universal2 family. -/
example [Inhabited Input] [Inhabited Output] :
    HashFamily.universal2 (fun (s : Input → Output) (i : Input) => s i) := by
  apply HashFamily.universal2_of_stronglyUniversal2
  exact (HashFamily.stronglyUniversal2_stronglyUniversal_n_2
    (fun (s : Input → Output) (i : Input) => s i)).mpr (all_functions_strongly_universal_n 2)

end
