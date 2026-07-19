/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module

public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Tactic.LinearCombinationPrime
public import UniversalHashing.BinConvolution.ConvolutionHelpers.NextPow2Lemmas
public import UniversalHashing.BinConvolution.ConvolutionHelpers.DFTLemmas
public import UniversalHashing.BinConvolution.ConvolutionHelpers.MontgomeryLemmas
public import UniversalHashing.BinConvolution.ConvolutionHelpers.RootTableLemmas
public import UniversalHashing.BinConvolution.ConvolutionHelpers.NttBoundLemmas
public import UniversalHashing.BinConvolution.ConvolutionHelpers.Radix4ForwardLemmas
public import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpers
public import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpersForward
public import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpersPreproc
public import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpersInvFull
public import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpersInvPreproc
-- `import all` (not plain `import`) is required: `Nat.isPowerOfTwo` is an unexposed
-- core `def` unfolding to `∃ ...`, so inside a `module` file `rcases`/`obtain` cannot
-- destructure an `isPowerOfTwo` hypothesis ("not an inductive datatype") without access
-- to core's private scope. Do not "tidy" this into a plain `import`.
import all Init.Data.Nat.Power2.Basic


/-! Correctness proofs for the NTT-based binary convolution pipeline. -/

@[expose] public section


/-
  Level 3d – outerLoop correctness: the radix-4 (+ optional radix-2) passes compute ref_ntt.

  Loop invariant (maintained at each pass with stride `len`): for each group b < m/(2·len)
  and output k < 2·len, the element at position b·(2·len) + k equals the DFT of the group's
  input subsequence at frequency k.  Formally, defining

      ω_L = primRoot^((mod64-1)/L)    (primitive L-th root of unity)
      stride(q) = m / 2^q            (distance between consecutive group inputs in v)
      start_b(q, b) = σ_{n-q}(b)     (bit-reversal of group index at level q)

  the invariant at level q (group size L = 2^q) is:

      a[b · L + k] = dft L ω_L (fun j => toMont(v[start_b(q,b) + j · stride(q)])) k.val

  Initial state (q=0, after toMont + bitRevLoop): a[b] = toMont(v[σ_n(b)]) ✓
  (1-point DFT of a single element is the element itself.)

  Step from q to q+1 (each radix4Middle pass, Δq = 2):  butterfly4 applies two
  Danielson–Lanczos levels simultaneously; the twiddle factors come from ntt_roots_correct.
  Step from q=0 to q=1 (optional radix2Pass, Δq = 1): radix2Pass_ZMod_pair.

  Termination (q = n, group size m, single group b=0): σ_{n-n} = id, stride = 1, so
      a[k] = dft m ω_m (fun j => toMont(v[j])) k.val = ref_ntt n ω f (Fin.cast hm_eq k).
-/
/-- Shared parity computation for the forward and inverse outer-loop proofs.
From the starting stride `start ∈ {2, 4}` (it is `4` iff `log₂ m` is odd), derive that
`start = 2^(start_q + 1)` and that `n - start_q` is even, where `start_q = if … then 1 else 0`. -/
private lemma outerLoop_parity_facts (m n : ℕ) (hm_eq : m = 2 ^ n) (hn : n < 64)
    (start : UInt64)
    (hstart : start = if nttInplace.go 64 m 0 &&& 1 != 0 then 4 else 2) :
    start.toNat = 2 ^ ((if nttInplace.go 64 m 0 &&& 1 != 0 then 1 else 0) + 1)
      ∧ Even (n - (if nttInplace.go 64 m 0 &&& 1 != 0 then 1 else 0)) := by
  refine ⟨?_, ?_⟩
  · rw [hstart]; split_ifs with hp <;> simp_all
  · split_ifs with hp
    · -- `start_q = 1`: `log₂ m` is odd, so `n` is odd and `n - 1` is even
      rcases Nat.even_or_odd n with he | ⟨k, hk⟩
      · exact absurd (go_parity_even_nat m n hm_eq hn he) (by simp_all)
      · rw [hk]; ring_nf; exact ⟨k, by omega⟩
    · -- `start_q = 0`: `log₂ m` is even, so `n` is even
      simp only [Nat.sub_zero]
      rcases Nat.even_or_odd n with he | ho
      · exact he
      · exact absurd (Ne.symm (go_parity_odd_nat m n hm_eq hn ho)) (by simp_all)

lemma ntt_outerLoop_computes_ref_ntt {m : ℕ} (n : ℕ)
    (hm_eq : m = 2 ^ n)
    (h_dvd : 2 ^ n ∣ mod64.toNat - 1)
    (v : Vector UInt32 m) (hv_bound : v.all (· < mod32))
    (roots : Vector UInt32 m) (hroots : ntt_roots_correct m roots)
    (hroots_bnd : roots.all (· < mod32))
    -- `a_in` is the array entering outerLoop: toMont + bitRevLoop + optional radix2Pass.
    -- `start` is the starting stride: 2 if log2(m) is even, 4 if log2(m) is odd.
    -- The input is characterised by matching the NTT preprocessing steps exactly.
    (a_in : Vector UInt32 m)
    (ha_in : a_in =
        let a1 := bitRevLoop (m - 1) 0 (v.map toMont) 0
        if nttInplace.go 64 m 0 &&& 1 != 0 then radix2Pass (m / 2) 0 a1 else a1)
    (start : UInt64)
    (hstart : start = if nttInplace.go 64 m 0 &&& 1 != 0 then 4 else 2) :
    let ω : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / m)
    ∀ k : Fin m,
      ((nttInplace.outerLoop false roots a_in start 64)[k.val].toNat : ZMod mod32.toNat) =
      ref_ntt n ω
        (fun j : Fin (2 ^ n) => ((toMont v[Fin.cast hm_eq.symm j]).toNat : ZMod mod32.toNat))
        (Fin.cast hm_eq k) := by
  -- Use the decomposed proof from OuterLoopHelpers.
  have hn : n < 64 := n_lt_64_of_pow2_nat m n hm_eq (hm_eq ▸ h_dvd)
  simp only
  intro k
  -- Step 1: The preprocessing establishes the initial loop invariant.
  have h_preproc := preprocessing_establishes_inv n hm_eq (hm_eq ▸ h_dvd) v hv_bound roots hroots
  simp only at h_preproc
  obtain ⟨hle, hinv⟩ := h_preproc
  -- Steps 2–4: derive `start_q`, `start = 2^(start_q+1)`, and `Even (n - start_q)` (shared helper).
  set parity := (nttInplace.go 64 m 0 &&& 1 != 0)
  set start_q := (if parity then 1 else 0)
  obtain ⟨hstart_val, hq_even⟩ := outerLoop_parity_facts m n hm_eq hn start hstart
  -- Step 5: Show ha_in matches the preprocessing output.
  have ha_in_eq : a_in = (if parity then radix2Pass (m / 2) 0
      (bitRevLoop (m - 1) 0 (v.map toMont) 0)
    else bitRevLoop (m - 1) 0 (v.map toMont) 0) := by
    rw [ha_in]
  -- Step 6: Apply the generalized outerLoop correctness.
  have hfuel : n ≤ start_q + 2 * 64 := by omega
  rw [ha_in_eq]
  exact outerLoop_from_inv n start_q hm_eq v roots hroots hroots_bnd h_dvd _ hle hinv
    start hstart_val hq_even 64 hfuel k

/-
  Level 3e – the forward NTT computes `ref_ntt` on the Montgomery-encoded input.
  This decomposes nttInplace into preprocessing (toMont + bitRevLoop) and the outerLoop,
  then delegates the outerLoop correctness to ntt_outerLoop_computes_ref_ntt.
-/
lemma ntt_inplace_forward_eq_ref_ntt {m : ℕ} (n : ℕ)
    (hm_eq : m = 2 ^ n)
    (h_dvd : 2 ^ n ∣ mod64.toNat - 1)
    (v : Vector UInt32 m) (hv_bound : v.all (· < mod32))
    (roots : Vector UInt32 m) (hroots : ntt_roots_correct m roots)
    (hroots_bnd : roots.all (· < mod32)) :
    let ω : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / m)
    ∀ k : Fin m,
      ((nttInplace v false roots)[k.val].toNat : ZMod mod32.toNat) =
      ref_ntt n ω
        (fun j : Fin (2 ^ n) => ((toMont v[Fin.cast hm_eq.symm j]).toNat : ZMod mod32.toNat))
        (Fin.cast hm_eq k) := by
  simp only
  intro k
  -- Step 1: unfold nttInplace for the forward case (inverse = false).
  unfold nttInplace
  simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  -- Step 2: name the intermediate arrays, mirroring ntt_inplace_output_bound.
  set a1 := v.map toMont with ha1_def
  set a2 := bitRevLoop (m - 1) 0 a1 0 with ha2_def
  set k_par := nttInplace.go 64 m 0 with hk_par_def
  set a3 := (if k_par &&& 1 != 0 then (radix2Pass (m / 2) 0 a2, (4 : UInt64))
             else (a2, (2 : UInt64))).1 with ha3_def
  set start := (if k_par &&& 1 != 0 then (radix2Pass (m / 2) 0 a2, (4 : UInt64))
                else (a2, (2 : UInt64))).2 with hstart_def
  -- Step 3: apply the outerLoop correctness lemma.
  -- We need to show a3 and start match the ha_in / hstart hypotheses.
  have ha3_eq : a3 =
      let a1' := bitRevLoop (m - 1) 0 (v.map toMont) 0
      if nttInplace.go 64 m 0 &&& 1 != 0 then radix2Pass (m / 2) 0 a1' else a1' := by
    simp only [ha3_def, ha2_def, ha1_def, hk_par_def]
    split_ifs <;> rfl
  have hstart_eq : start = if nttInplace.go 64 m 0 &&& 1 != 0 then 4 else 2 := by
    simp only [hstart_def, hk_par_def]
    split_ifs <;> rfl
  exact ntt_outerLoop_computes_ref_ntt n hm_eq h_dvd v hv_bound roots hroots hroots_bnd
    a3 ha3_eq start hstart_eq k

/-- The core FFT correctness lemma: `nttInplace v false roots` computes the DFT of the
    Montgomery-encoded input `v.map toMont`.  That is, for each output index `k`,
    `result[k] = Σ_j (toMont (v[j])) · ω^(j·k)` in `ZMod mod32.toNat`. -/
lemma ntt_computes_dft_of_montv {m : ℕ}
    (v : Vector UInt32 m)
    (hm_pow2 : Nat.isPowerOfTwo m)
    (hm_dvd : m ∣ mod64.toNat - 1)
    (hv_bound : v.all (· < mod32))
    (roots : Vector UInt32 m)
    (hroots : ntt_roots_correct m roots)
    (hroots_bnd : roots.all (· < mod32)) :
    let ω : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / m)
    let result := nttInplace v false roots
    ∀ k : Fin result.size, (result[k].toNat : ZMod mod32.toNat) =
      ∑ j : Fin m,
        ((toMont (v[j.val])).toNat : ZMod mod32.toNat) * ω ^ (j.val * k.val) := by
  -- Extract n with m = 2^n from the power-of-two hypothesis.
  obtain ⟨n, hm_eq⟩ := hm_pow2
  simp only
  intro k
  set ω : ZMod mod32.toNat :=
    (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / m) with hω_def
  -- Step 1: ω satisfies the primitivity condition needed for ref_ntt_eq_dft.
  have hω_prim : n = 0 ∨ ω ^ 2 ^ (n - 1) = -1 :=
    ω_is_primitive_half_nat m n hm_eq hm_dvd
  -- Step 2: the iterative algorithm computes ref_ntt at each output index.
  -- Fin.cast hm_eq.symm : Fin (2^n) → Fin m carries j to a valid index for v.
  -- Fin.cast hm_eq      : Fin m → Fin (2^n) carries k to an output index.
  have h_ref : ((nttInplace v false roots)[k.val].toNat : ZMod mod32.toNat) =
      ref_ntt n ω
        (fun j : Fin (2 ^ n) => ((toMont v[Fin.cast hm_eq.symm j]).toNat : ZMod mod32.toNat))
        (Fin.cast hm_eq k) :=
    ntt_inplace_forward_eq_ref_ntt n hm_eq (hm_eq ▸ hm_dvd) v hv_bound roots hroots hroots_bnd k
  -- Step 3: ref_ntt n ω f k = dft (2^n) ω f k.val  (Danielson–Lanczos recursion,
  --         proved in DFTLemmas.lean).
  have h_dft :=
    ref_ntt_eq_dft n ω hω_prim
      (fun j : Fin (2 ^ n) => ((toMont v[Fin.cast hm_eq.symm j]).toNat : ZMod mod32.toNat))
      (Fin.cast hm_eq k)
  -- Steps 4+5: chain via Eq.trans (works under definitional equality for `let result`).
  refine h_ref.trans (h_dft.trans ?_)
  -- Goal: dft (2^n) ω (fun j => (toMont v[Fin.cast hm_eq.symm j]).toNat) (Fin.cast hm_eq k).val
  --     = ∑ j : Fin m, (toMont v[j.val]).toNat * ω ^ (j.val * k.val)
  simp only [dft]
  -- Step 5: reindex via finCongr hm_eq.symm : Fin (2^n) ≃ Fin m.
  -- The original goal ∑ Fin(2^n), A = ∑ Fin(m), B matches sum_equiv's output directly.
  -- apply (not exact) unifies with the goal first so AddCommMonoid is resolved.
  -- All vals are preserved definitionally, so the body proof is rfl.
  apply Finset.sum_equiv (finCongr hm_eq.symm)
  · intro _; exact ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩
  · intro _ _; rfl

/-
Forward NTT correctness with a parametric root table:
    given `ntt_roots_correct`, `nttInplace v false roots` computes
    `result[k] = R · Σ_j v[j] · ω^(j·k)` in `ZMod mod32.toNat`,
    where R = montR1 comes from the `toMont` preprocessing step applied to each entry.
    The Montgomery factor R appears because `toMont` maps `v[j]` to `v[j] · R mod p`
    before the butterfly passes, and the butterflies preserve this scaling.
-/
lemma ntt_inplace_forward_from_roots {m : ℕ}
    (v : Vector UInt32 m)
    (hm_pow2 : Nat.isPowerOfTwo m)
    (hm_dvd : m ∣ mod64.toNat - 1)
    (hv_bound : v.all (· < mod32))
    (roots : Vector UInt32 m)
    (hroots : ntt_roots_correct m roots)
    (hroots_bnd : roots.all (· < mod32)) :
    let ω : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / m)
    let result := nttInplace v false roots
    ∀ k : Fin result.size, (result[k].toNat : ZMod mod32.toNat) =
      (montR1.toNat : ZMod mod32.toNat) * ∑ j : Fin m,
          (v[j.val].toNat : ZMod mod32.toNat) * ω ^ (j.val * k.val) := by
  -- The proof follows from two key lemmas:
  -- 1. ntt_computes_dft_of_montv: result[k] = Σ_j toMont(v[j]) * ω^(j*k)
  -- 2. to_mont_dft_factor: Σ_j toMont(v[j]) * ω^(j*k) = R * Σ_j v[j] * ω^(j*k)
  -- Apply the ntt_computes_dft_of_montv lemma to get the result in terms of the sum of
  -- toMont(v[j]) * ω^(j*k).
  have h1 := ntt_computes_dft_of_montv v hm_pow2 hm_dvd hv_bound roots hroots
    hroots_bnd
  convert h1 using 1
  rw [to_mont_dft_factor]
  exact hv_bound

/-
Forward NTT: `result[k] = R · Σ_j input[j] · ω^(j·k)`  in ZMod p,
where R = montR1 = 2^32 mod mod64 is the Montgomery factor.
Requires: m is a power of 2 dividing mod64.toNat - 1, and all input values < mod32.
-/
theorem ntt_inplace_forward_spec {m : ℕ}
    (v : Vector UInt32 m)
    (hm_pow2 : Nat.isPowerOfTwo m)
    (hm_dvd : m ∣ mod64.toNat - 1)
    (hv_bound : v.all (· < mod32))
    :
    let ω : ZMod mod32.toNat := (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / m)
    let result := nttInplace v false (ensureRoots m)
    ∀ k : Fin result.size, (result[k].toNat : ZMod mod32.toNat) =
      (montR1.toNat : ZMod mod32.toNat) * ∑ j : Fin m,
          (v[j.val].toNat : ZMod mod32.toNat) * ω ^ (j.val * k.val) :=
  ntt_inplace_forward_from_roots v hm_pow2 hm_dvd hv_bound
    (ensureRoots m) (ensure_roots_ntt_correct hm_pow2 hm_dvd)
    (ensure_roots_bound_nat m (Nat.lt_of_le_of_lt (Nat.le_of_dvd (by decide) hm_dvd) (by decide)))

/-
  Analog of `ntt_outerLoop_computes_ref_ntt` for the inverse NTT.
  Given the right preprocessing input, `outerLoop true` computes `ref_ntt n ω⁻¹` on the
  original input `v` (no Montgomery encoding).
-/
lemma ntt_outerLoop_inv_computes_ref_ntt {m : ℕ} (n : ℕ)
    (hm_eq : m = 2 ^ n)
    (h_dvd : 2 ^ n ∣ mod64.toNat - 1)
    (v : Vector UInt32 m) (hv_bound : v.all (· < mod32))
    (roots : Vector UInt32 m) (hroots : ntt_roots_correct m roots)
    (hroots_bnd : roots.all (· < mod32))
    (a_in : Vector UInt32 m)
    (ha_in : a_in =
        let a1 := bitRevLoop (m - 1) 0 v 0
        if nttInplace.go 64 m 0 &&& 1 != 0 then radix2Pass (m / 2) 0 a1 else a1)
    (start : UInt64)
    (hstart : start = if nttInplace.go 64 m 0 &&& 1 != 0 then 4 else 2) :
    let ω : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / m)
    ∀ k : Fin m,
      ((nttInplace.outerLoop true roots a_in start 64)[k.val].toNat : ZMod mod32.toNat) =
      ref_ntt n ω⁻¹
        (fun j : Fin (2 ^ n) => ((v[Fin.cast hm_eq.symm j]).toNat : ZMod mod32.toNat))
        (Fin.cast hm_eq k) := by
  have hn : n < 64 := n_lt_64_of_pow2_nat m n hm_eq (hm_eq ▸ h_dvd)
  simp only
  intro k
  have h_preproc := preprocessing_establishes_inv_inverse n hm_eq (hm_eq ▸ h_dvd) v hv_bound
  simp only at h_preproc
  obtain ⟨hle, hinv⟩ := h_preproc
  set parity := (nttInplace.go 64 m 0 &&& 1 != 0)
  set start_q := (if parity then 1 else 0)
  obtain ⟨hstart_val, hq_even⟩ := outerLoop_parity_facts m n hm_eq hn start hstart
  have ha_in_eq : a_in = (if parity then radix2Pass (m / 2) 0
      (bitRevLoop (m - 1) 0 v 0)
    else bitRevLoop (m - 1) 0 v 0) := by
    rw [ha_in]
  have hfuel : n ≤ start_q + 2 * 64 := by omega
  rw [ha_in_eq]
  exact outerLoop_from_inv_inverse n start_q hm_eq v roots hroots hroots_bnd h_dvd _ hle hinv
    start hstart_val hq_even 64 hfuel k

-- Helper: (powModU64 m (p-2) p).toUInt32 = m⁻¹ in ZMod mod32, proved in a small context.
private lemma inv_n_ZMod_eq {m : ℕ} (n : ℕ) (hm_eq : m = 2 ^ n)
    (hm_dvd : m ∣ mod64.toNat - 1) :
    ((powModU64 m.toUInt64 (mod64 - 2) mod64).toUInt32.toNat : ZMod mod32.toNat) =
    (m : ZMod mod32.toNat)⁻¹ := by
  have h_dvd : 2 ^ n ∣ mod64.toNat - 1 := hm_eq ▸ hm_dvd
  have hn : n < 64 := n_lt_64_of_pow2_nat m n hm_eq hm_dvd
  have hm_small : m < 2 ^ 64 := hm_eq ▸ Nat.pow_lt_pow_right (by norm_num) hn
  have hm_toNat : m.toUInt64.toNat = m := nat_toUInt64_faithful m hm_small
  have h_powmod := powmod_correct m.toUInt64 (mod64 - 2) mod64 (by decide) (by decide)
  have h_lt32 : (powModU64 m.toUInt64 (mod64 - 2) mod64).toNat < 2 ^ 32 := by
    rw [h_powmod, hm_toNat]; exact lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  rw [UInt64_toUInt32_toNat _ h_lt32, h_powmod, hm_toNat,
      (by decide : (mod64 - 2 : UInt64).toNat = mod64.toNat - 2)]
  have hm_ne : (m : ZMod mod32.toNat) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, hm_eq]
    intro h_dvd_p
    have h1 : 2 ^ n ≤ mod64.toNat - 1 := Nat.le_of_dvd (by decide) h_dvd
    have h2 : mod32.toNat ≤ 2 ^ n := Nat.le_of_dvd (Nat.two_pow_pos n) h_dvd_p
    have h_mod_eq : mod64.toNat = mod32.toNat := mod32_eq_mod
    omega
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  rw [show m ^ (mod64.toNat - 2) % mod64.toNat = m ^ (mod32.toNat - 2) % mod32.toNat from by
    rw [mod32_eq_mod]]
  simp only [Nat.cast_pow, ZMod.natCast_mod]
  rw [mul_comm, ← pow_succ]
  norm_num [mod32]
  exact ZMod.pow_card_sub_one_eq_one hm_ne

-- Master helper: converts the unfolded DFT sum (Fin (2^n)-indexed, using Fin.cast for v)
-- directly to the theorem's target RHS sum (Fin m-indexed, using Nat for v).
-- Uses kval : ℕ to avoid Fin type mismatch between the large proof's k and Fin m.
-- Body closes by rfl: Fin.cast and finCongr are definitionally equal, and
-- Vector's Fin- and Nat-indexed GetElem are definitionally equal (proof irrelevance).
private lemma inv_sum_total {m : ℕ} (n : ℕ) (hm_eq : m = 2 ^ n)
    (v : Vector UInt32 m) (ω : ZMod mod32.toNat) (kval : ℕ) :
    ∑ x : Fin (2 ^ n),
        ((v[Fin.cast hm_eq.symm x]).toNat : ZMod mod32.toNat) * ω⁻¹ ^ (x.val * kval) =
    ∑ j : Fin m, (v[j.val].toNat : ZMod mod32.toNat) * (ω⁻¹) ^ (j.val * kval) := by
  apply Finset.sum_equiv (finCongr hm_eq.symm)
  · intro _; exact ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩
  · intro x _; rfl

-- Helper lemma: proves ref_ntt = dft for inverse NTT in a small context,
-- avoiding the whnf timeout that occurs inside the large ntt_inplace_inverse_correct proof.
private lemma ref_ntt_inv_eq_dft {m : ℕ} (n : ℕ)
    (hm_eq : m = 2 ^ n)
    (v : Vector UInt32 m)
    (ω : ZMod mod32.toNat)
    (hω : n = 0 ∨ ω⁻¹ ^ 2 ^ (n - 1) = -1)
    (k : Fin (2 ^ n)) :
    ref_ntt n ω⁻¹
        (fun j : Fin (2 ^ n) => ((v[Fin.cast hm_eq.symm j]).toNat : ZMod mod32.toNat)) k =
    dft (2 ^ n) ω⁻¹
        (fun j : Fin (2 ^ n) => ((v[Fin.cast hm_eq.symm j]).toNat : ZMod mod32.toNat)) k.val :=
  ref_ntt_eq_dft n ω⁻¹ hω _ _

/-
Inverse NTT: `result[k] = R⁻¹ · m⁻¹ · Σ_j input[j] · (ω⁻¹)^(j·k)` in ZMod p,
where R⁻¹ = montR1⁻¹ is the inverse Montgomery factor.
The R⁻¹ factor arises because the final `montMul(·, n⁻¹)` step
multiplies by n⁻¹ in plain domain, introducing an R⁻¹ from Montgomery reduction.
Requires: m is a power of 2 dividing mod64.toNat - 1, and all input values < mod32.
-/

theorem ntt_inplace_inverse_correct {m : ℕ}
    (v : Vector UInt32 m)
    (hm_pow2 : Nat.isPowerOfTwo m)
    (hm_dvd : m ∣ mod64.toNat - 1)
    (hv_bound : v.all (· < mod32))
    :
    let ω : ZMod mod32.toNat := (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / m)
    let result := nttInplace v true (ensureRoots m)
    ∀ k : Fin result.size, (result[k].toNat : ZMod mod32.toNat) =
      (montR1.toNat : ZMod mod32.toNat)⁻¹ * (m : ZMod mod32.toNat)⁻¹ * ∑ j : Fin m,
        (v[j.val].toNat : ZMod mod32.toNat) * (ω⁻¹) ^ (j.val * k.val) := by
  obtain ⟨n, hm_eq⟩ := hm_pow2
  simp only
  intro k
  set ω : ZMod mod32.toNat :=
    (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / m) with hω_def
  have h_dvd : 2 ^ n ∣ mod64.toNat - 1 := hm_eq ▸ hm_dvd
  have hn : n < 64 := n_lt_64_of_pow2_nat m n hm_eq hm_dvd
  have hm_small : m < 2 ^ 64 := hm_eq ▸ Nat.pow_lt_pow_right (by norm_num) hn
  have hm_toNat : m.toUInt64.toNat = m := nat_toUInt64_faithful m hm_small
  -- Step 1: unfold nttInplace for inverse = true.
  unfold nttInplace
  simp only [Bool.not_true, ↓reduceIte]
  -- Name intermediate computations.
  set a2 := bitRevLoop (m - 1) 0 v 0 with ha2_def
  set k_par := nttInplace.go 64 m 0 with hk_par_def
  set a3 := (if k_par &&& 1 != 0 then (radix2Pass (m / 2) 0 a2, (4 : UInt64))
             else (a2, (2 : UInt64))).1 with ha3_def
  set start := (if k_par &&& 1 != 0 then (radix2Pass (m / 2) 0 a2, (4 : UInt64))
                else (a2, (2 : UInt64))).2 with hstart_def
  -- The result is (outerLoop ... a3 start 64).map (fun x => montMul x inv_n).
  simp only [Bool.false_eq_true, ite_false, Fin.getElem_fin, Vector.getElem_map]
  -- Step 2: show outerLoop computes ref_ntt n ω⁻¹ of the original input.
  have hroots := ensure_roots_ntt_correct ⟨n, hm_eq⟩ hm_dvd
  have hroots_bnd : (ensureRoots m).all (· < mod32) :=
    ensure_roots_bound_nat m (hm_eq ▸ Nat.pow_lt_pow_right (by norm_num) hn)
  have ha3_eq : a3 =
      let a1' := bitRevLoop (m - 1) 0 v 0
      if nttInplace.go 64 m 0 &&& 1 != 0 then radix2Pass (m / 2) 0 a1' else a1' := by
    simp only [ha3_def, ha2_def, hk_par_def]; split_ifs <;> rfl
  have hstart_eq : start = if nttInplace.go 64 m 0 &&& 1 != 0 then 4 else 2 := by
    simp only [hstart_def, hk_par_def]; split_ifs <;> rfl
  have h_a4 : ∀ k' : Fin m,
      ((nttInplace.outerLoop true (ensureRoots m) a3 start 64)[k'.val].toNat :
          ZMod mod32.toNat) =
      ref_ntt n ω⁻¹
        (fun j : Fin (2 ^ n) => ((v[Fin.cast hm_eq.symm j]).toNat : ZMod mod32.toNat))
        (Fin.cast hm_eq k') :=
    ntt_outerLoop_inv_computes_ref_ntt n hm_eq h_dvd v hv_bound (ensureRoots m)
      hroots hroots_bnd a3 ha3_eq start hstart_eq
  -- Step 3: bounds for mont_mul_ZMod.
  have ha3_bound : a3.all (· < mod32) := by
    rw [ha3_def]; split_ifs
    · exact radix2Pass_bound _ _ _ (bitRevLoop_bound _ _ _ _ hv_bound)
    · exact bitRevLoop_bound _ _ _ _ hv_bound
  have ha4_bound : (nttInplace.outerLoop true (ensureRoots m) a3 start 64).all (· < mod32) := by
    suffices h : ∀ (a : Vector UInt32 m) (len : UInt64) (fuel : ℕ),
        a.all (· < mod32) →
        (nttInplace.outerLoop true (ensureRoots m) a len fuel).all (· < mod32) from
      h a3 start 64 ha3_bound
    intro a len fuel ha
    induction fuel generalizing a len with
    | zero => simp only [nttInplace.outerLoop, ha]
    | succ f ih =>
      simp only [nttInplace.outerLoop]; split_ifs with hcond
      · exact ha
      · exact ih _ _ (radix4Middle_bound _ _ _ _ _ _ _ ha)
  have ha4_k_bnd :
      (nttInplace.outerLoop true (ensureRoots m) a3 start 64)[k.val].toNat <
          mod32.toNat :=
    vector_all_lt_getElem _ k ha4_bound
  have hinv_n_bnd : (powModU64 m.toUInt64 (mod64 - 2) mod64).toUInt32.toNat < mod32.toNat := by
    have h1 := powmod_correct m.toUInt64 (mod64 - 2) mod64 (by decide) (by decide)
    have h_lt : (powModU64 m.toUInt64 (mod64 - 2) mod64).toNat < mod64.toNat := by
      rw [h1, hm_toNat]; exact Nat.mod_lt _ (by decide)
    have h_lt32 : (powModU64 m.toUInt64 (mod64 - 2) mod64).toNat < 2 ^ 32 :=
      lt_of_lt_of_le h_lt (by decide)
    rw [UInt64_toUInt32_toNat _ h_lt32]
    exact lt_of_lt_of_le h_lt (by decide)
  -- Step 4: apply mont_mul_ZMod to the final scaling step.
  rw [mont_mul_ZMod _ _ ha4_k_bnd hinv_n_bnd]
  -- Step 5: substitute the outerLoop result and convert ref_ntt to DFT sum.
  rw [h_a4 k]
  have hω_inv_prim : n = 0 ∨ (ω⁻¹) ^ 2 ^ (n - 1) = -1 := by
    rcases ω_is_primitive_half_nat m n hm_eq hm_dvd with hn0 | hω_half
    · left; exact hn0
    · right; rw [inv_pow, hω_half, ← neg_inv, inv_one]
  -- Use the helper lemma (proved in a small context to avoid whnf timeout).
  rw [ref_ntt_inv_eq_dft n hm_eq v ω hω_inv_prim (Fin.cast hm_eq k)]
  -- Step 6: relate inv_n.toNat to m⁻¹ in ZMod (delegated to helper).
  have h_invn_ZMod := inv_n_ZMod_eq n hm_eq hm_dvd
  -- Step 7: relate 2^32 to montR1 in ZMod.
  have h_R1 : (montR1.toNat : ZMod mod32.toNat) = 2 ^ 32 := MONT_R1_ZMod
  -- Step 8: unfold dft, normalize the Fin.cast in the exponent, reindex via helper, close by ring.
  simp only [dft]
  -- Normalize (Fin.cast hm_eq k).val to k.val so the sum atom matches the theorem's RHS.
  rw [show (Fin.cast hm_eq k).val = k.val from rfl]
  rw [h_invn_ZMod, h_R1, inv_sum_total n hm_eq v ω k.val]
  ring

/-!
#  ──  Top-level ─────────────────────────────────────────────────────────────────
-/

section TopLevel

/-!
## Proof of circular_convolution_gf2_correct

Proof outline:
1. The guard `m < 2 * n` is vacuous when `2 * n` fits in UInt64 (from `next_pow2_ge`).
2. The NTT pipeline computes `result[k]` = the k-th value of the integer-valued LINEAR
   convolution of the 0/1 embeddings of `a` and `b` (Montgomery factors cancel: forward
   NTT maps input to Montgomery domain, inverse NTT maps back out).
3. Folding: `result[i] + result[i+n]` = the integer-valued CIRCULAR convolution at index i
   (valid because fa, fb have support in [0,n) and m ≥ 2n prevents aliasing).
4. Bit-0 of the folded sum equals the GF(2) circular convolution bit.
-/

/-- Integer-valued circular convolution: count (mod 2 will give GF(2) result). -/
def int_circ_conv {n : ℕ} (a b : BitVec n) (i : Fin n) : ℕ :=
  ∑ j : Fin n,
    (if a.getLsb j then 1 else 0) * (if b.getLsb (i - j) then 1 else 0)

/-- The integer-valued linear convolution of the 0/1 embeddings at index k. -/
def int_lin_conv {n : ℕ} (a b : BitVec n) (k : ℕ) : ℕ :=
  ∑ j : Fin n,
    if h : j.val ≤ k ∧ k - j.val < n
    then (if a.getLsb j then 1 else 0) * (if b.getLsb ⟨k - j.val, h.2⟩ then 1 else 0)
    else 0

/-
Folding the linear convolution at i and i+n gives the circular convolution at i.
    Valid because inputs have support in [0,n) and m ≥ 2n prevents wrap-around.
    Concretely: for j ≤ i, the term at i contributes and i+n is out of range.
    For j > i, the term at i is out of range and the i+n term wraps to (i - j) mod n.
-/
theorem lin_conv_fold_eq_circ_conv {n : ℕ} (a b : BitVec n) (i : Fin n) :
    int_lin_conv a b i.val + int_lin_conv a b (i.val + n) = int_circ_conv a b i := by
  unfold int_lin_conv int_circ_conv
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl]
  intro j _
  by_cases hle : j.val ≤ i.val
  · -- j ≤ i: first term a[j]*b[i-j] contributes; second (i+n-j ≥ n) vanishes
    have h1 : j.val ≤ i.val ∧ i.val - j.val < n := ⟨hle, by omega⟩
    have h2 : ¬(j.val ≤ i.val + n ∧ i.val + n - j.val < n) := by omega
    simp only [dif_pos h1, dif_neg h2, add_zero]
    -- (i - j : Fin n).val = (n - j + i) % n = (i - j + n) % n = i - j
    have hfin : (i - j : Fin n) = ⟨i.val - j.val, h1.2⟩ := by
      apply Fin.ext; simp only [Fin.val_sub]
      have heq : n - j.val + i.val = i.val - j.val + n := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt h1.2]
    simp only [hfin]
  · -- j > i: first term vanishes; second a[j]*b[i+n-j] wraps to (i-j) mod n
    have h1 : ¬(j.val ≤ i.val ∧ i.val - j.val < n) := by omega
    have h2 : j.val ≤ i.val + n ∧ i.val + n - j.val < n := ⟨by omega, by omega⟩
    simp only [dif_neg h1, dif_pos h2, zero_add]
    -- (i - j : Fin n).val = (n - j + i) % n = i + n - j (since < n)
    have hfin : (i - j : Fin n) = ⟨i.val + n - j.val, h2.2⟩ := by
      apply Fin.ext; simp only [Fin.val_sub]
      have heq : n - j.val + i.val = i.val + n - j.val := by omega
      rw [heq, Nat.mod_eq_of_lt h2.2]
    simp only [hfin]

/-- Integer circular convolution of two UInt32 vectors.
    `(fa ⊛_m fb)[k] = Σ_j fa[j] * fb[(k - j) mod m]`
    This is what the NTT pipeline computes internally (modulo mod32). -/
def vec_circ_conv {m : ℕ} (fa fb : Vector UInt32 m) (k : Fin m) : ℕ :=
  ∑ j : Fin m,
    (fa.get j).toNat * (fb.get ⟨(k.val + m - j.val) % m, Nat.mod_lt _ j.pos⟩).toNat

/-
For 0/1-valued zero-padded inputs (characterised by hfa/hfb) and m ≥ 2n,
    the m-point circular convolution equals the integer linear convolution at every index.
    No wrap-around occurs because m ≥ 2n: for j < n and (k - j) < n both are in [0, n),
    so (k - j) mod m = k - j, matching int_lin_conv; all other cross-terms vanish.
-/
theorem vec_circ_conv_zero_padded {n m : ℕ} (a b : BitVec n)
    (hm : 2 * n ≤ m) (k : Fin m)
    (fa fb : Vector UInt32 m)
    (hfa : ∀ i : Fin m, (fa.get i).toNat =
      if h : i.val < n then if a.getLsb ⟨i.val, h⟩ then 1 else 0 else 0)
    (hfb : ∀ i : Fin m, (fb.get i).toNat =
      if h : i.val < n then if b.getLsb ⟨i.val, h⟩ then 1 else 0 else 0) :
    vec_circ_conv fa fb k = int_lin_conv a b k.val := by
  unfold vec_circ_conv int_lin_conv
  rw [← Finset.sum_subset
    (Finset.subset_univ (Finset.filter (fun x : Fin m => x.val < n) Finset.univ))]
  · refine Finset.sum_bij
      (fun x hx => ⟨x, by linarith [Fin.is_lt x, Finset.mem_filter.mp hx]⟩)
      ?_ ?_ ?_ ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, implies_true]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.mk.injEq]
      exact fun i hi j hj hij => Fin.ext hij
    · simp only [Finset.mem_univ, Finset.mem_filter, true_and, forall_const]
      exact fun i => ⟨⟨i, by linarith [Fin.is_lt i]⟩, by simp⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hfa, BitVec.getLsb_eq_getElem,
      Fin.getElem_fin, hfb, mul_dite, mul_ite, mul_one, mul_zero, Fin.val_fin_le]
      intro i hi
      split_ifs <;> norm_num
      · rename_i h₁ h₂ h₃ h₄ h₅
        contrapose! h₅
        convert h₂ using 2
        rw [Nat.mod_eq_sub_mod]
        · rw [Nat.mod_eq_of_lt] <;> omega
        · omega
      · rename_i h₁ h₂ h₃ h₄
        contrapose! h₄
        constructor
        · exact Nat.le_of_not_lt fun h => by
            have := Nat.mod_eq_of_lt (by omega : (k : ℕ) + m - i < m)
            omega
        · by_cases h₅ : (k : ℕ) < i
          · omega
          · rw [Nat.mod_eq_sub_mod] at h₁
            · rw [Nat.mod_eq_of_lt] at h₁ <;> omega
            · omega
      · rename_i h₁ h₂ h₃ h₄ h₅
        convert h₂ _
        convert h₄ using 2
        rw [Nat.mod_eq_sub_mod]
        · rw [Nat.mod_eq_of_lt]
          · omega
          · omega
        · omega
      · rw [Nat.mod_eq_sub_mod] at *
        · rw [Nat.mod_eq_of_lt] at * <;> omega
        · omega
  · aesop

/-- `ω = primRoot ^ ((p-1)/m)` is a primitive `m`-th root of unity in `ZMod p`.

Apply `IsPrimitiveRoot.pow_of_dvd` to the primitive `(p-1)`-th root `primRoot`
(`prim_root_PRIM_ROOT`) with divisor `d = (p-1)/m`; it yields a primitive `((p-1)/d)`-th
root, leaving three side goals: the order `(p-1)/d = m`, that `d ≠ 0`, and that `d ∣ (p-1)`. -/
theorem omega_is_prim_root {m : ℕ}
    (hm_pow2 : Nat.isPowerOfTwo m)
    (hm_dvd : m ∣ mod64.toNat - 1) :
    IsPrimitiveRoot ((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / m)) m := by
  obtain ⟨k, hk⟩ := hm_dvd
  have hroot : IsPrimitiveRoot (primRoot.toNat : ZMod mod32.toNat) (mod64.toNat - 1) := by
    have h := prim_root_PRIM_ROOT
    rwa [mod32_eq_mod] at h
  convert IsPrimitiveRoot.pow_of_dvd hroot _ _ using 1
  · -- order matches: `m = (p-1) / ((p-1)/m)`
    rw [Nat.div_div_self] <;> norm_num [hk]
    exact ⟨by rintro rfl; simp only [Nat.zero_mul] at hk; exact absurd hk (by decide),
           by rintro rfl; simp only [mul_zero] at hk; exact absurd hk (by decide)⟩
  · -- divisor is nonzero: `(p-1)/m ≠ 0`
    rw [hk, Nat.mul_div_cancel_left] <;> norm_num
    · rintro rfl; simp only [Nat.mul_zero] at hk; exact absurd hk (by decide)
    · cases hm_pow2 ; aesop
  · -- divisor divides `p-1`: `(p-1)/m ∣ (p-1)`
    exact Nat.div_dvd_of_dvd (hk.symm ▸ dvd_mul_right _ _)

/-
m > 1 when it's a power of 2 dividing p-1 and the NTT has a meaningful size.
    Since isPowerOfTwo m means m ≥ 1, and m divides p-1 = 3*2^30,
    we need m ≥ 2. But actually isPowerOfTwo guarantees m ≥ 1.
    We handle the m=1 case: if m=1 then the statement is vacuous (Fin 1 has one element
    and the circular convolution is trivial).
-/
theorem m_gt_one_of_pow2_dvd {m : ℕ}
    (hm_dvd : m ∣ mod64.toNat - 1)
    (hm_ne : m ≠ 1) :
    1 < m := by
  exact lt_of_le_of_ne
    (Nat.pos_of_ne_zero (by rintro h; subst h; exact absurd hm_dvd (by decide)))
    (Ne.symm hm_ne)

/-
NTT orthogonality: sum of ω^(j*c) over j in Fin m equals m if c ≡ 0 (mod m), else 0.
-/
theorem ntt_orthogonality (m : ℕ)
    (ω : ZMod mod32.toNat) (hω : IsPrimitiveRoot ω m) (c : ℕ) :
    ∑ j : Fin m, ω ^ (j.val * c) =
      if c % m = 0 then (m : ZMod mod32.toNat) else 0 := by
  split_ifs <;> simp_all only [pow_mul']
  · rw [← Nat.mod_add_div c m, ‹c % m = 0›] ; simp [pow_mul, hω.pow_eq_one] 
  · have h_geom_sum : ∑ x ∈ Finset.range m, (ω ^ c) ^ x = 0 := by
      have h_geom_sum : (ω ^ c) ^ m = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
      have h_geom_sum : (ω ^ c) ≠ 1 := by
        exact fun h => ‹¬c % m = 0› (Nat.mod_eq_zero_of_dvd <| hω.2 c h)
      exact (by rw [geom_sum_eq] <;> aesop)
    rwa [Finset.sum_range] at h_geom_sum

/-
The montMul operation in ZMod: (montMul a b : ZMod p) = a * b * R⁻¹.
    More precisely, (montMul a b).toNat cast to ZMod equals
    a.toNat * b.toNat * (montR1.toNat : ZMod p)⁻¹ in ZMod p.
-/
theorem mont_mul_zmod (a b : UInt32)
    (ha : a.toNat < mod32.toNat) (hb : b.toNat < mod32.toNat) :
    (montMul a b).toNat = ((a.toNat : ZMod mod32.toNat) * b.toNat *
      (montR1.toNat : ZMod mod32.toNat)⁻¹).val := by
  have h_mod : (montMul a b).toNat * 2 ^ 32 ≡ a.toNat * b.toNat [MOD mod32.toNat] := by
    exact mont_mul_correct a b ha hb |>.2
  have h_mod : (montMul a b).toNat * (montR1.toNat : ZMod mod32.toNat) = a.toNat * b.toNat := by
    simpa [← ZMod.natCast_eq_natCast_iff,
      show montR1.toNat = 2 ^ 32 % mod32.toNat from by decide, ZMod.natCast_mod] using h_mod
  simp only [← h_mod]
  rw [mul_assoc, mul_inv_cancel₀, mul_one]
  · exact Eq.symm (ZMod.val_cast_of_lt (mont_mul_correct a b ha hb |>.1))
  · rw [Ne.eq_def, ZMod.natCast_eq_zero_iff] ; decide

/-
The prod vector has all elements < mod32.
-/
theorem prod_bound {m : ℕ}
    (FA FB : Vector UInt32 m)
    (hFA : FA.all (· < mod32)) (hFB : FB.all (· < mod32)) :
    ((FA.zip FB).map (fun xy => montMul xy.1 xy.2)).all (· < mod32) := by
  rw [Vector.all_eq_true] at *
  intro i hi
  specialize hFA i hi
  specialize hFB i hi
  simp_all only [Vector.getElem_map, Vector.getElem_zip,
      decide_eq_true_eq, UInt32.lt_iff_toNat_lt]
  have := mont_mul_correct FA[i] FB[i] hFA hFB; aesop

/-
m cast to ZMod mod32.toNat is nonzero when m divides p-1 (and 1 < m).
-/
theorem m_ne_zero_zmod (m : ℕ) (hm : 1 < m) (hm_dvd : m ∣ mod32.toNat - 1) :
    (m : ZMod mod32.toNat) ≠ 0 := by
  rw [Ne.eq_def, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt hm.le
    (Nat.lt_of_le_of_lt (Nat.le_of_dvd (Nat.sub_pos_of_lt (by decide)) hm_dvd)
      (Nat.sub_lt (by decide) (by decide)))

/-
DFT convolution theorem: inverse DFT of pointwise product of two DFTs
    equals the circular convolution.
-/
theorem dft_convolution_theorem (m : ℕ) (hm : 1 < m)
    (ω : ZMod mod32.toNat) (hω : IsPrimitiveRoot ω m)
    (hm_dvd : m ∣ mod32.toNat - 1)
    (f g : Fin m → ZMod mod32.toNat) (k : Fin m) :
    (m : ZMod mod32.toNat)⁻¹ * ∑ j : Fin m,
      (∑ i : Fin m, f i * ω ^ (i.val * j.val)) *
      (∑ l : Fin m, g l * ω ^ (l.val * j.val)) *
      (ω⁻¹) ^ (j.val * k.val) =
    ∑ i : Fin m, f i * g ⟨(k.val + m - i.val) % m, Nat.mod_lt _ (by omega)⟩ := by
  generalize_proofs at *; (
  -- Step 1: Replace (ω⁻¹)^(j*k) with ω^((m-1)*j*k) using inv_eq_pow_pred.
  have h1 : ∀ j : Fin m, ω⁻¹ ^ (j.val * k.val) = ω ^ ((m - 1) * j.val * k.val) := by
    intro j
    have h_inv_pow : ω⁻¹ = ω ^ (m - 1) := by
      rw [inv_eq_of_mul_eq_one_right]
      have := hω.pow_eq_one
      rcases m with (_ | _ | m) <;>
        first | omega | simp_all only [pow_succ', Nat.add_sub_cancel]
    rw [h_inv_pow]
    ring
  -- Step 2: Distribute the product of sums using Finset.mul_sum and Finset.sum_mul.
  have h2 : ∑ j : Fin m, (∑ i : Fin m, f i * ω ^ (i.val * j.val)) *
      (∑ l : Fin m, g l * ω ^ (l.val * j.val)) * ω ^ ((m - 1) * j.val * k.val) =
      ∑ i : Fin m, ∑ l : Fin m, f i * g l *
      ∑ j : Fin m, ω ^ (j.val * (i.val + l.val + k.val * (m - 1))) := by
    simp only [Finset.sum_mul _ _ _, Finset.mul_sum]
    ring_nf
    exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans
        (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring))
  -- Step 3: Apply ntt_orthogonality for the inner sum.
  have h3 : ∀ i l : Fin m, ∑ j : Fin m, ω ^ (j.val * (i.val + l.val + k.val * (m - 1))) =
      if (i.val + l.val + k.val * (m - 1)) % m = 0 then (m : ZMod mod32.toNat) else 0 := by
    intro i l
    convert ntt_orthogonality m ω hω (i + l + k * (m - 1)) using 1
  -- For each i, the sum over l selects the unique l = (k+m-i)%m with i+l ≡ k (mod m).
  have h4 : ∀ i : Fin m,
      ∑ l : Fin m, f i * g l *
        (if (i.val + l.val + k.val * (m - 1)) % m = 0 then (m : ZMod mod32.toNat) else 0) =
      f i * g ⟨(k.val + m - i.val) % m, Nat.mod_lt _ (Nat.zero_lt_of_lt hm)⟩ *
        (m : ZMod mod32.toNat) := by
    intro i
    have h_unique_l : ∀ l : Fin m,
        (i.val + l.val + k.val * (m - 1)) % m = 0 ↔ l.val = (k.val + m - i.val) % m := by
      intro l
      constructor
      · intro h
        have h_mod : (i.val + l.val + k.val * (m - 1)) % m = 0 := by
          exact h
        have h_eq : l.val ≡ (k.val + m - i.val) [MOD m] := by
          have h_eq : (i.val + l.val + k.val * (m - 1)) ≡ 0 [MOD m] := by
            exact h_mod
          generalize_proofs at *
          simp_all only [inv_pow, mul_ite, mul_zero, ← ZMod.natCast_eq_natCast_iff,
            Nat.cast_add, Nat.cast_mul, Nat.cast_zero,
            Nat.cast_sub (by linarith [Fin.is_lt i, Fin.is_lt k] : (i : ℕ) ≤ k + m),
            CharP.cast_eq_zero, add_zero]
          simp_all only [Nat.cast_sub (by linarith : 1 ≤ m),
            CharP.cast_eq_zero, Nat.cast_one, zero_sub, mul_neg, mul_one]
          linear_combination' h_eq
        exact (by rw [← h_eq, Nat.mod_eq_of_lt (Fin.is_lt l)])
      · intro h
        have h_mod : (i.val + l.val + k.val * (m - 1)) % m = 0 := by
          simp only [h, ← ZMod.val_natCast, Nat.cast_add, Nat.cast_mul, ZMod.val_eq_zero]
          simp only [Nat.cast_sub (by linarith [Fin.is_lt i, Fin.is_lt k] : (i : ℕ) ≤ k + m),
            Nat.cast_add, CharP.cast_eq_zero, add_zero, Nat.cast_sub (hm.le : 1 ≤ m),
            Nat.cast_one, zero_sub, mul_neg, mul_one]
          ring_nf
          cases m <;> aesop
        exact h_mod
    generalize_proofs at *
    rw [Finset.sum_eq_single ⟨(k + m - i) % m, by assumption⟩] <;>
      simp +contextual only [h_unique_l, Finset.mem_univ, ne_eq, mul_ite, mul_zero,
        ite_eq_left_iff, ite_eq_right_iff, zero_eq_mul, mul_eq_zero, forall_const,
        not_true_eq_false, IsEmpty.forall_iff]
    · exact fun h => False.elim <| h <| h_unique_l ⟨_, by assumption⟩ |>.2 rfl
    · exact fun l hl hl' => False.elim <| hl <| Fin.ext hl'
  simp_all only []
  rw [← Finset.sum_mul _ _ _, inv_mul_eq_div,
    mul_div_cancel_right₀ _ (by exact m_ne_zero_zmod m hm hm_dvd)])

/-
The NTT pipeline (2 forward NTTs, pointwise montMul, 1 inverse NTT) computes the
    m-point circular convolution of the input vectors, taken modulo mod32.
    Proof ingredients: forward NTT spec (result = R × DFT of input, where R = montR1)
    montMul(FA[k], FB[k]) cancels one R factor giving R × DFT(fa)[k] × DFT(fb)[k]
    inverse NTT spec (scales by m⁻¹) combined with NTT orthogonality (Σ_k ω^(ck) = m·δ_{c,0})
    gives R × circ_conv[j]; the final montMul(·, m⁻¹) in nttInplace removes the R factor.
-/
theorem ntt_pipeline_computes_circ_conv {m : ℕ}
    (fa fb : Vector UInt32 m) (k : Fin m)
    (hm_pow2 : Nat.isPowerOfTwo m)
    (hm_dvd : m ∣ mod64.toNat - 1)
    (hfa_bound : fa.all fun x ↦ x < mod32)
    (hfb_bound : fb.all fun x ↦ x < mod32)
    :
    let FA     := nttInplace fa false (ensureRoots m)
    let FB     := nttInplace fb false (ensureRoots m)
    let prod   := (FA.zip FB).map (fun xy => montMul xy.1 xy.2)
    let result := nttInplace prod true (ensureRoots m)
    result[k].toNat = (vec_circ_conv fa fb k) % mod32.toNat := by
  intro FA FB prod result
  -- Bounds
  have hFA_bound : FA.all (· < mod32) := ntt_inplace_output_bound fa false _ hfa_bound
  have hFB_bound : FB.all (· < mod32) := ntt_inplace_output_bound fb false _ hfb_bound
  have hprod_bound : prod.all (· < mod32) := prod_bound FA FB hFA_bound hFB_bound
  have hresult_bound : result.all (· < mod32) := ntt_inplace_output_bound prod true _ hprod_bound
  -- result[k] < mod32
  have hresult_lt : result[k].toNat < mod32.toNat := vector_all_lt_getElem _ k hresult_bound
  set ω : ZMod mod32.toNat := (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / m)
  set R : ZMod mod32.toNat := (montR1.toNat : ZMod mod32.toNat)
  -- Helper: get pointwise bounds from Vector.all bounds
  have hFA_pw : ∀ j : Fin m, FA[j].toNat < mod32.toNat :=
    fun j => vector_all_lt_getElem _ j hFA_bound
  have hFB_pw : ∀ j : Fin m, FB[j].toNat < mod32.toNat :=
    fun j => vector_all_lt_getElem _ j hFB_bound
  -- Step 1: Forward NTT specs
  have hFA_spec : ∀ j : Fin m, (FA[j].toNat : ZMod mod32.toNat) =
      R * ∑ i : Fin m, (fa[i].toNat : ZMod mod32.toNat) * ω ^ (i.val * j.val) :=
    ntt_inplace_forward_spec fa hm_pow2 hm_dvd hfa_bound
  have hFB_spec : ∀ j : Fin m, (FB[j].toNat : ZMod mod32.toNat) =
      R * ∑ i : Fin m, (fb[i].toNat : ZMod mod32.toNat) * ω ^ (i.val * j.val) :=
    ntt_inplace_forward_spec fb hm_pow2 hm_dvd hfb_bound
  -- R ≠ 0: mod32 ∤ montR1.toNat since mod32 > montR1.toNat
  have hR_ne : R ≠ 0 := by
    change (montR1.toNat : ZMod mod32.toNat) ≠ 0
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact absurd (Nat.le_of_dvd (by decide) h) (by decide)
  -- Step 2: prod[j] = montMul(FA[j], FB[j]), and its ZMod value
  have hprod_eq : ∀ j : Fin m, prod[j] = montMul FA[j] FB[j] := by
    intro j; simp [prod, Vector.getElem_map, Vector.getElem_zip]
  have hprod_zmod : ∀ j : Fin m, (prod[j].toNat : ZMod mod32.toNat) =
      R * (∑ i : Fin m, (fa[i].toNat : ZMod mod32.toNat) * ω ^ (i.val * j.val)) *
          (∑ i : Fin m, (fb[i].toNat : ZMod mod32.toNat) * ω ^ (i.val * j.val)) := by
    intro j
    rw [hprod_eq j]
    have hmm := mont_mul_zmod FA[j] FB[j] (hFA_pw j) (hFB_pw j)
    rw [show ((montMul FA[j] FB[j]).toNat : ZMod mod32.toNat) =
        (FA[j].toNat : ZMod mod32.toNat) * (FB[j].toNat : ZMod mod32.toNat) * R⁻¹ from by
      rw [hmm, ZMod.natCast_val, ZMod.cast_id', Function.id_def],
      hFA_spec j, hFB_spec j, mul_assoc (R * _),
      show (R * ∑ i : Fin m, (fb[i].toNat : ZMod mod32.toNat) * ω ^ (i.val * j.val)) * R⁻¹ =
          ∑ i : Fin m, (fb[i].toNat : ZMod mod32.toNat) * ω ^ (i.val * j.val) from by
        rw [mul_comm R, mul_assoc, mul_inv_cancel₀ hR_ne, mul_one]]
  -- Step 3: Inverse NTT spec applied to result
  have hresult_spec : (result[k].toNat : ZMod mod32.toNat) = R⁻¹ * (m : ZMod mod32.toNat)⁻¹ *
      ∑ j : Fin m, (prod[j].toNat : ZMod mod32.toNat) * (ω⁻¹) ^ (j.val * k.val) :=
    ntt_inplace_inverse_correct prod hm_pow2 hm_dvd hprod_bound k
  have hR_cancel : R * R⁻¹ = 1 := mul_inv_cancel₀ hR_ne
  -- Step 4: Substitute prod ZMod values and cancel R * R⁻¹ = 1
  have hresult_conv : (result[k].toNat : ZMod mod32.toNat) =
      (m : ZMod mod32.toNat)⁻¹ * ∑ j : Fin m,
        (∑ i : Fin m, (fa[i].toNat : ZMod mod32.toNat) * ω ^ (i.val * j.val)) *
        (∑ i : Fin m, (fb[i].toNat : ZMod mod32.toNat) * ω ^ (i.val * j.val)) *
        (ω⁻¹) ^ (j.val * k.val) := by
    rw [hresult_spec, mul_assoc, mul_left_comm]
    rw [Finset.mul_sum _ _ _]
    rw [Finset.sum_congr rfl]
    intros
    rw [hprod_zmod]
    simp only [← mul_assoc, inv_mul_cancel₀ hR_ne, one_mul]
  -- Step 5: Apply DFT convolution theorem
  have hω : IsPrimitiveRoot ω m := omega_is_prim_root hm_pow2 hm_dvd
  have hzmod : (result[k].toNat : ZMod mod32.toNat) =
      (vec_circ_conv fa fb k : ZMod mod32.toNat) := by
    by_cases hm : m = 1
    · unfold vec_circ_conv
      simp only [Fin.getElem_fin, hm, Nat.cast_sum, Nat.cast_mul]
      rw [Finset.sum_eq_single ⟨0, by linarith⟩] <;>
        simp only [tsub_zero, Nat.add_mod_right, Finset.mem_univ, ne_eq,
          mul_eq_zero, forall_const, not_true_eq_false, IsEmpty.forall_iff]
      · simp only [Fin.getElem_fin] at hresult_conv
        convert hresult_conv using 1
        rw [Finset.sum_eq_single ⟨0, by linarith⟩] <;>
          simp only [hm, Nat.cast_one, inv_one, mul_zero, pow_zero,
            mul_one, zero_mul, one_mul, Finset.mem_univ, ne_eq, inv_pow, mul_eq_zero,
            inv_eq_zero, pow_eq_zero_iff', not_or, forall_const, not_true_eq_false,
            IsEmpty.forall_iff]
        · rw [Finset.sum_eq_single ⟨0, by linarith⟩,
            Finset.sum_eq_single ⟨0, by linarith⟩] <;>
          simp only [Finset.mem_univ, ne_eq, forall_const, not_true_eq_false,
            IsEmpty.forall_iff]
          · norm_num [Nat.mod_one]
            rfl
          · exact fun b h => absurd (Fin.ext (by have := b.isLt; omega)) h
          · exact fun b h => absurd (Fin.ext (by have := b.isLt; omega)) h
        · exact fun j hj => False.elim <| hj <| Fin.ext <| by linarith [Fin.is_lt j]
      · exact fun b h => absurd (Fin.ext (by have := b.isLt; omega)) h
    · convert dft_convolution_theorem m
        (m_gt_one_of_pow2_dvd (mod32_eq_mod ▸ hm_dvd) hm) ω hω
        (mod32_eq_mod ▸ hm_dvd) (fun i => (fa[i].toNat : ZMod mod32.toNat))
        (fun i => (fb[i].toNat : ZMod mod32.toNat)) k using 1
      unfold vec_circ_conv; push_cast; rfl
  -- Lift from ZMod to Nat
  have hmod_eq := (ZMod.natCast_eq_natCast_iff _ _ _).mp hzmod
  rw [Nat.ModEq] at hmod_eq
  rw [← hmod_eq, Nat.mod_eq_of_lt hresult_lt]

/-
The circular convolution of 0/1-valued vectors with n nonzero entries is at most n.
    With n < mod32.toNat (guaranteed when the NTT size m | (p−1) = 3·2^30, so m ≤ 2^30
    and n ≤ m/2 < p), the % mod32 in ntt_pipeline_computes_circ_conv is the identity.

requires zero-padding of fa (values 0 for i ≥ n).
Since at most n terms of fa are nonzero and each product ≤ 1, the sum ≤ n < mod32.
-/
theorem vec_circ_conv_lt_mod {n m : ℕ}
    (hm : 2 * n ≤ m) (hn : n < mod32.toNat)
    (fa fb : Vector UInt32 m) (k : Fin m)
    (hfa : ∀ i : Fin m, (fa.get i).toNat ≤ 1 ∧ (n ≤ i.val → (fa.get i).toNat = 0))
    (hfb : ∀ i : Fin m, (fb.get i).toNat ≤ 1) :
    vec_circ_conv fa fb k < mod32.toNat := by
  refine lt_of_le_of_lt
    (Finset.sum_le_sum (g := fun i => if i.val < n then 1 else 0) fun i _ => ?_) ?_
  · split_ifs with hi
    · exact Nat.mul_le_mul (hfa i |>.1) (hfb _)
    · simp only [(hfa i).2 (Nat.le_of_not_lt hi), Nat.zero_mul, Nat.zero_le]
  · simp only [Finset.sum_boole, Nat.cast_id] at *
    refine lt_of_le_of_lt ?_ hn
    refine (Finset.card_eq_of_bijective (fun i hi => ⟨i, by linarith⟩) ?_ ?_ ?_).le
    · aesop
    · intro i h; simp [h]
    · intro i j hi hj h; simp only [Fin.mk.injEq] at h; exact h

/-- The NTT pipeline result at index k equals the integer linear convolution at k.
    Key insight: forward NTT converts inputs to Montgomery domain (× R); inverse NTT
    converts back (× R⁻¹), so the net Montgomery factor is 1 and results are plain integers.
    Also uses the NTT convolution theorem: pointwise product in frequency domain =
    circular convolution in time domain (= linear convolution here, due to zero-padding). -/
theorem ntt_pipeline_eq_lin_conv {n : ℕ} (a b : BitVec n)
    (hn_mod : n < mod32.toNat)
    (hm_dvd : (Nat.nextPowerOfTwo (2 * n)) ∣ mod64.toNat - 1) :
    let m := Nat.nextPowerOfTwo (2 * n)
    let roots : Vector UInt32 m := ensureRoots m
    let fa : Vector UInt32 m := .ofFn fun i ↦
      if h : i.val < n then if a.getLsb ⟨i.val, h⟩ then 1 else 0 else 0
    let fb : Vector UInt32 m := .ofFn fun i ↦
      if h : i.val < n then if b.getLsb ⟨i.val, h⟩ then 1 else 0 else 0
    let FA := nttInplace fa false roots
    let FB := nttInplace fb false roots
    let result := nttInplace (FA.zip FB |>.map (fun xy ↦ montMul xy.1 xy.2)) true roots
    ∀ k : Fin m, result[k].toNat = int_lin_conv a b k.val
    := by ------------------------------------------------------------------------------------------
  intro m roots fa fb FA FB result k
  have hmn : 2 * n ≤ m := nextPow2_nat_ge (2 * n)
  -- n < mod32.toNat is provided as a hypothesis
  -- fa and fb are the 0/1 embeddings of a and b (by their let-definitions)
  have hfa_spec : ∀ i : Fin m, (fa.get i).toNat =
      if h : i.val < n then if a.getLsb ⟨i.val, h⟩ then 1 else 0 else 0 := by
    intro i
    have hfa_def : fa = .ofFn (fun j : Fin m ↦
        if h : j.val < n then if a.getLsb ⟨j.val, h⟩ then 1 else 0 else 0) := rfl
    rw [hfa_def, Vector.get_ofFn]; split_ifs <;> simp
  have hfb_spec : ∀ i : Fin m, (fb.get i).toNat =
      if h : i.val < n then if b.getLsb ⟨i.val, h⟩ then 1 else 0 else 0 := by
    intro i
    have hfb_def : fb = .ofFn (fun j : Fin m ↦
        if h : j.val < n then if b.getLsb ⟨j.val, h⟩ then 1 else 0 else 0) := rfl
    rw [hfb_def, Vector.get_ofFn]; split_ifs <;> simp
  -- fa and fb have values ≤ 1 (by case-splitting on the 0/1 embedding)
  have hfa_01 : ∀ i : Fin m, (fa.get i).toNat ≤ 1 := by
    intro i; rw [hfa_spec]; split_ifs <;> simp
  have hfb_01 : ∀ i : Fin m, (fb.get i).toNat ≤ 1 := by
    intro i; rw [hfb_spec]; split_ifs <;> simp
  -- Step 1: NTT pipeline gives circular convolution % mod32
  -- (roots is definitionally ensureRoots m, so result equals the pipeline term)
  have hm_pow2 : Nat.isPowerOfTwo m := Nat.isPowerOfTwo_nextPowerOfTwo (2 * n)
  have hfa_bound : ∀ i : Fin m, (fa.get i).toNat < mod32.toNat := by
    intro i; have := hfa_01 i; have : mod32.toNat = 3221225473 := rfl; omega
  have hfb_bound : ∀ i : Fin m, (fb.get i).toNat < mod32.toNat := by
    intro i; have := hfb_01 i; have : mod32.toNat = 3221225473 := rfl; omega
  have hcirc : result[k].toNat = vec_circ_conv fa fb k % mod32.toNat :=
    ntt_pipeline_computes_circ_conv fa fb k hm_pow2 hm_dvd
      (by rw [Vector.all_eq_true]; intro i hi; simp only [decide_eq_true_eq]
          exact UInt32.lt_iff_toNat_lt.mpr
            (by have := hfa_bound ⟨i, hi⟩; simp only [Vector.get] at this; exact this))
      (by rw [Vector.all_eq_true]; intro i hi; simp only [decide_eq_true_eq]
          exact UInt32.lt_iff_toNat_lt.mpr
            (by have := hfb_bound ⟨i, hi⟩; simp only [Vector.get] at this; exact this))
  -- Step 2: zero-padded circular convolution equals integer linear convolution
  have heq : vec_circ_conv fa fb k = int_lin_conv a b k.val :=
    vec_circ_conv_zero_padded a b hmn k fa fb hfa_spec hfb_spec
  -- Step 3: circular convolution value < mod32 so % is the identity
  have hfa_zp : ∀ i : Fin m, (fa.get i).toNat ≤ 1 ∧ (n ≤ i.val → (fa.get i).toNat = 0) := by
    intro i
    constructor
    · exact hfa_01 i
    · intro hi; rw [hfa_spec]; simp [show ¬(i.val < n) from by omega]
  have hlt : vec_circ_conv fa fb k < mod32.toNat :=
    vec_circ_conv_lt_mod hmn hn_mod fa fb k hfa_zp hfb_01
  -- Conclude: result[k] = circ_conv % mod32 = circ_conv = lin_conv
  rw [hcirc, heq]
  exact Nat.mod_eq_of_lt (heq ▸ hlt)

/-
The GF(2) Bool sum `∑ j, a[j] * b[i-j]` (XOR of ANDs) equals the parity of
    the integer sum `int_circ_conv`: Bool addition is XOR, Bool mul is AND, and
    `true` counts as 1, so the Bool fold and the integer count have the same parity.
-/
theorem bool_sum_eq_int_parity {n : ℕ} (a b : BitVec n) (i : Fin n) :
    (∑ j : Fin n, a[j] * b[i - j] : Bool) = ((int_circ_conv a b i) % 2 == 1) := by
  unfold int_circ_conv
  simp only [Fin.getElem_fin, BitVec.getLsb_eq_getElem, mul_ite, mul_one, mul_zero,
    Finset.sum_ite, Bool.not_eq_true, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_filter]
  rw [Finset.sum_filter, Finset.sum_nat_mod]
  induction (Finset.univ : Finset (Fin n)) using Finset.induction with
  | empty => rfl
  | insert j fs _ ih =>
    simp_all only [not_false_eq_true, Finset.sum_insert, Nat.mod_add_mod]
    cases a[↑j] <;> cases b[↑(i - j)] <;> simp +decide only [↓reduceIte, zero_add, add_eq_right]
    cases Nat.mod_two_eq_zero_or_one
        (∑ x ∈ fs, (if b[↑(i - x)] = true then if a[↑x] = true then 1 else 0 else 0) % 2) <;>
      simp only [Nat.add_mod, Nat.mod_succ, dvd_refl, Nat.mod_mod_of_dvd]
    · aesop
    · simp_all +decide only [Fin.getElem_fin, BEq.rfl, Nat.mod_succ, Nat.reduceAdd, Nat.mod_self,
        Nat.reduceBEq]

/-
Bit 0 of a UInt32 sum equals parity of the Nat sum.
    UInt32 addition wraps mod 2^32, but bit 0 of (a + b) mod 2^32 = (a + b) mod 2.
-/
theorem uint32_sum_bit0 (u v : UInt32) :
    ((u + v) &&& 1 == 1) = ((u.toNat + v.toNat) % 2 == 1) := by
  cases Nat.mod_two_eq_zero_or_one (u.toNat + v.toNat) <;>
    simp only [Nat.add_mod, dvd_refl, Nat.mod_mod_of_dvd, Nat.reduceBEq,
      beq_eq_false_iff_ne, ne_eq, BEq.rfl, beq_iff_eq, *] at *
  · exact ne_of_apply_ne (fun x => x.toNat) (by
      simp only [UInt32.toNat_and, UInt32.toNat_add, Nat.reducePow, Nat.add_mod,
        UInt32.toNat_mod_size, UInt32.reduceToNat, Nat.and_one_is_mod, Nat.reduceDvd,
        Nat.mod_mod_of_dvd, dvd_refl, ne_eq, Nat.mod_two_not_eq_one] ; omega)
  · cases Nat.mod_two_eq_zero_or_one u.toNat <;>
      cases Nat.mod_two_eq_zero_or_one v.toNat <;> simp_all +decide only []
    · rw [← UInt32.toNat_inj]
      simp only [UInt32.toNat_and, UInt32.toNat_add, UInt32.reduceToNat, Nat.and_one_is_mod]
      omega
    · simp_all only [← UInt32.toNat_inj, UInt32.toNat_and, UInt32.toNat_add, Nat.reducePow,
        Nat.add_mod, UInt32.toNat_mod_size, UInt32.reduceToNat, Nat.and_one_is_mod, Nat.reduceDvd,
        Nat.mod_mod_of_dvd, add_zero, Nat.mod_succ]

/-- Correctness theorem for NTT-based implementation. -/
theorem circular_convolution_gf2_correct' {n : ℕ} (a b : BitVec n)
    (hn_mod : n < mod32.toNat)
    (hm_dvd : (Nat.nextPowerOfTwo (2 * n)) ∣ mod64.toNat - 1) :
    circularConvolutionGf2 a b = BitVec.circConvolutionBruteforce a b := by
  -- Unfold both sides and eliminate the dif guard in one shot, then go pointwise.
  simp only [circularConvolutionGf2, BitVec.circConvolutionBruteforce]
  congr 1; funext i
  -- Name the NTT intermediate values (matching those in circularConvolutionGf2).
  set m      := Nat.nextPowerOfTwo (2 * n)
  set roots  : Vector UInt32 m := ensureRoots m
  set fa     : Vector UInt32 m := .ofFn fun j ↦
    if h : j.val < n then if a.getLsb ⟨j.val, h⟩ then 1 else 0 else 0
  set fb     : Vector UInt32 m := .ofFn fun j ↦
    if h : j.val < n then if b.getLsb ⟨j.val, h⟩ then 1 else 0 else 0
  set FA     := nttInplace fa false roots
  set FB     := nttInplace fb false roots
  set result := nttInplace (FA.zip FB |>.map (fun xy ↦ montMul xy.1 xy.2)) true roots
  have hm_ge : 2 * n ≤ m := nextPow2_nat_ge (2 * n)
  -- Step 1: NTT pipeline gives the integer linear convolution at each index.
  -- (ntt_pipeline_eq_lin_conv states this for Fin-indexed result; we need Nat indexing here.)
  have hlin := ntt_pipeline_eq_lin_conv a b hn_mod hm_dvd
  -- Step 2: result.get i + result.get (i+n) = int_circ_conv a b i.
  -- Uses hlin (converts to int_lin_conv) and lin_conv_fold_eq_circ_conv (folds to circ_conv).
  -- (Vector.get and getElem are definitionally equal; proof-term alignment is boilerplate.)
  have hfold : (result.get ⟨i.val, by omega⟩).toNat +
               (result.get ⟨i.val + n, by omega⟩).toNat = int_circ_conv a b i := by
    -- Type-ascribe h1 and h2 using the set-bound `result` so linarith can unify.
    -- hlin's let-bound `result` equals our `set result` definitionally.
    have h1 : (result.get ⟨i.val, by omega⟩).toNat = int_lin_conv a b i.val :=
      hlin ⟨i.val, by omega⟩
    have h2 : (result.get ⟨i.val + n, by omega⟩).toNat = int_lin_conv a b (i.val + n) :=
      hlin ⟨i.val + n, by omega⟩
    linarith [lin_conv_fold_eq_circ_conv a b i]
  -- Step 3: bit 0 of the UInt32 sum equals the parity of the integer sum.
  have hbit : ((result.get ⟨i.val, by omega⟩ + result.get ⟨i.val + n, by omega⟩) &&& 1 == 1)
            = (int_circ_conv a b i % 2 == 1) := by
    rw [uint32_sum_bit0, hfold]
  -- Step 4: parity of the integer sum equals the GF(2) Bool sum.
  rw [hbit, ← bool_sum_eq_int_parity a b i]

end TopLevel

theorem pow2_divides_MOD_sub_one (n : ℕ) (hn : n < 2 ^ 29) :
    (Nat.nextPowerOfTwo (2 * n)) ∣ mod64.toNat - 1 := by
  have : mod64.toNat - 1 = 3 * 2 ^ 30 := by decide
  set P2n := Nat.nextPowerOfTwo (2 * n) with hP2n
  rw [this]
  have : Nat.isPowerOfTwo P2n := by
    exact Nat.isPowerOfTwo_nextPowerOfTwo (2 * n)
  obtain ⟨m, hm⟩ := this
  have hP2n_le : P2n ≤ 2 ^ 30 := by
    rw [hP2n]
    apply nextPow2_nat_le
    · omega
  have : m ≤ 30 := by
    by_contra h
    push Not at h
    have : 2 ^ 31 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
    omega
  have : P2n ∣ 2 ^ 30 := by
    rw [hm]
    exact Nat.pow_dvd_pow_iff_le_right'.mpr this
  exact Nat.dvd_mul_left_of_dvd this 3

end
