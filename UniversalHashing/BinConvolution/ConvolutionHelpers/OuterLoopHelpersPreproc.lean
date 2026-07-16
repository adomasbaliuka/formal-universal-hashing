/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib.Data.Nat.Bitwise
import UniversalHashing.BinConvolution.ConvolutionHelpers.DFTLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.NttBoundLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.Radix4ForwardLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpers
import UniversalHashing.BinConvolution.ConvolutionHelpers.OuterLoopHelpersForward



/-!
# Bit-reversal and preprocessing invariant

Bit-reversal permutation lemmas and `preprocessing_establishes_inv`, split out from
`OuterLoopHelpersForward` to keep per-file elaboration memory bounded.
-/

/-! ### Bit-reversal helper lemmas -/

@[simp] lemma bitRev_zero (n : ℕ) : bitRev n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bitRev, ih, Nat.zero_mod, mul_zero, Nat.add_zero]

/-- `bitRev (n+1) (2^n*b + c) = 2 * bitRev n c + b` when `b ≤ 1` and `c < 2^n`. -/
lemma bitRev_msb (n b c : ℕ) (hb : b ≤ 1) (hc : c < 2 ^ n) :
    bitRev (n + 1) (2 ^ n * b + c) = 2 * bitRev n c + b := by
  induction n generalizing b c with
  | zero =>
    interval_cases c
    interval_cases b <;> decide
  | succ n ih =>
    have hmod : (2 ^ (n + 1) * b + c) % 2 = c % 2 := by
      have h_pow_even : 2 ^ (n + 1) * b % 2 = 0 := by
        have : 2 ^ (n + 1) * b = (2 ^ n * b) * 2 := by ring
        rw [this, Nat.mul_mod_left]
      omega
    have hdiv : (2 ^ (n + 1) * b + c) / 2 = 2 ^ n * b + c / 2 := by
      have hrw : 2 ^ (n + 1) * b = 2 * (2 ^ n * b) := by ring
      rw [hrw, (by ring : 2 * (2 ^ n * b) + c = c + (2 ^ n * b) * 2)]
      rw [Nat.add_mul_div_right _ _ (by norm_num : (0 : ℕ) < 2)]
      omega
    rw [bitRev, hmod, hdiv]
    have hc' : c / 2 < 2 ^ n := by
      have : c < 2 * 2 ^ n := by linarith [(by ring : 2 ^ (n + 1) = 2 * 2 ^ n)]
      omega
    rw [ih b (c / 2) hb hc']
    rw [show bitRev (n + 1) c = 2 ^ n * (c % 2) + bitRev n (c / 2) from rfl]
    ring

/-- Bit reversal is an involution on `[0, 2^n)`. -/
lemma bitRev_invol (n x : ℕ) (hx : x < 2 ^ n) : bitRev n (bitRev n x) = x := by
  induction n generalizing x with
  | zero => interval_cases x; rfl
  | succ n ih =>
    have hstep : bitRev (n + 1) x = 2 ^ n * (x % 2) + bitRev n (x / 2) := rfl
    rw [hstep]
    have hxmod : x % 2 ≤ 1 := by omega
    have hbR : bitRev n (x / 2) < 2 ^ n := bitRev_lt n (x / 2)
    rw [bitRev_msb n (x % 2) (bitRev n (x / 2)) hxmod hbR]
    have hxdiv : x / 2 < 2 ^ n := by
      have : x < 2 * 2 ^ n := by linarith [(by ring : 2 ^ (n + 1) = 2 * 2 ^ n)]
      omega
    rw [ih (x / 2) hxdiv]
    omega

/-- `(2^n * b + c) AND 2^n = 2^n * b` for `b ≤ 1` and `c < 2^n`. -/
lemma and_two_pow_decompose (n b c : ℕ) (hb : b ≤ 1) (hc : c < 2 ^ n) :
    (2 ^ n * b + c) &&& 2 ^ n = 2 ^ n * b := by
  rw [Nat.and_two_pow]
  rw [Nat.testBit_two_pow_mul_add b hc]
  simp only [lt_self_iff_false, ↓reduceIte, tsub_self, Nat.testBit_zero]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h0 | h1
  · subst h0; simp
  · subst h1; simp

/-- `(2^n * b + c) XOR 2^n = 2^n * (1 - b) + c` for `b ≤ 1` and `c < 2^n`. -/
lemma xor_two_pow_decompose (n b c : ℕ) (hb : b ≤ 1) (hc : c < 2 ^ n) :
    (2 ^ n * b + c) ^^^ 2 ^ n = 2 ^ n * (1 - b) + c := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add b hc,
      Nat.testBit_two_pow_mul_add (1 - b) hc, Nat.testBit_two_pow]
  by_cases hi : i < n
  · have hne : ¬ n = i := by omega
    simp only [if_pos hi, decide_eq_false_iff_not.mpr hne, Bool.xor_false]
  · push Not at hi
    by_cases hi' : i = n
    · subst hi'
      simp only [lt_self_iff_false, ↓reduceIte, tsub_self, Nat.testBit_zero, decide_true,
        Bool.bne_true]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h0 | h1
      · subst h0; simp
      · subst h1; simp
    · have hi'' : n < i := lt_of_le_of_ne hi (Ne.symm hi')
      have hne : ¬ i < n := by omega
      have hne2 : ¬ n = i := fun e => hi' e.symm
      simp only [hne, hne2, ↓reduceIte, decide_false, Bool.xor_false]
      have hb_test : ∀ k : ℕ, k ≤ 1 → k.testBit (i - n) = false := by
        intro k hk
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with h0 | h1
        · subst h0; exact Nat.zero_testBit _
        · subst h1
          have : ¬ Nat.testBit 1 (i - n) = true := by
            rw [Nat.testBit_one_eq_true_iff_self_eq_zero]; omega
          exact Bool.not_eq_true _ |>.mp this
      rw [hb_test b hb, hb_test (1 - b) (by omega)]

/-- `bitRevNext f j bit` correctly increments the bit-reversed counter `j` of width `n`,
provided fuel `f ≥ n - 1`. -/
lemma bitRevNext_spec (n : ℕ) (i : ℕ) (hn1 : 1 ≤ n) (hn64 : n ≤ 64)
    (hi : i + 1 < 2 ^ n) (f : ℕ) (hf : n - 1 ≤ f)
    (j bit : ℕ) (hj : j = bitRev n i) (hbit : bit = 2 ^ (n - 1)) :
    bitRevNext f j bit = bitRev n (i + 1) := by
  induction n generalizing i j bit f with
  | zero => omega
  | succ n ih =>
    have hj' : j = 2 ^ n * (i % 2) + bitRev n (i / 2) := by rw [hj]; rfl
    have hbit' : bit = 2 ^ n := by rw [hbit]; simp
    have hbn : bitRev n (i / 2) < 2 ^ n := bitRev_lt _ _
    have hidiv : i / 2 < 2 ^ n := by
      have : i < 2 * 2 ^ n := by linarith [(by ring : 2 ^ (n + 1) = 2 * 2 ^ n)]
      omega
    by_cases hbit0 : i % 2 = 0
    · have h_and_zero : j &&& bit = 0 := by
        rw [hj', hbit0, mul_zero, zero_add, hbit']
        rw [Nat.and_two_pow, Nat.testBit_lt_two_pow hbn]; simp
      have h_xor : j ^^^ bit = 2 ^ n + bitRev n (i / 2) := by
        rw [hj', hbit0, mul_zero, zero_add, hbit']
        rw [(by ring : bitRev n (i / 2) = 2 ^ n * 0 + bitRev n (i / 2)),
            xor_two_pow_decompose n 0 (bitRev n (i / 2)) (by norm_num) hbn]
        ring
      have hgoal : j ^^^ bit = bitRev (n + 1) (i + 1) := by
        rw [h_xor, bitRev]
        have h1 : (i + 1) % 2 = 1 := by omega
        have h2 : (i + 1) / 2 = i / 2 := by omega
        rw [h1, h2]; ring
      cases f with
      | zero => simp only [bitRevNext, hgoal]
      | succ f' =>
        simp only [bitRevNext]
        rw [(by simp [h_and_zero] : (j &&& bit == 0) = true)]
        exact hgoal
    · have hbit1 : i % 2 = 1 := by omega
      have hn_pos : 1 ≤ n := by
        by_contra hcontra
        push Not at hcontra
        interval_cases n
        omega
      have h_and_eq : j &&& bit = 2 ^ n := by
        rw [hj', hbit', hbit1, mul_one]
        rw [(by ring : 2 ^ n + bitRev n (i / 2) = 2 ^ n * 1 + bitRev n (i / 2))]
        rw [and_two_pow_decompose n 1 (bitRev n (i / 2)) (by norm_num) hbn]
        ring
      have h_and_ne : j &&& bit ≠ 0 := by
        rw [h_and_eq]; exact (Nat.two_pow_pos n).ne'
      have h_xor : j ^^^ bit = bitRev n (i / 2) := by
        rw [hj', hbit', hbit1, mul_one]
        rw [(by ring : 2 ^ n + bitRev n (i / 2) = 2 ^ n * 1 + bitRev n (i / 2))]
        rw [xor_two_pow_decompose n 1 (bitRev n (i / 2)) (by norm_num) hbn]
        simp
      cases f with
      | zero => omega
      | succ f' =>
        have step : bitRevNext (f' + 1) j bit = bitRevNext f' (j ^^^ bit) (bit >>> 1) := by
          simp only [bitRevNext]
          rw [(by simp [h_and_ne] : (j &&& bit == 0) = false)]
          simp
        rw [step]
        have hbit'' : bit >>> 1 = 2 ^ (n - 1) := by
          rw [hbit', Nat.shiftRight_eq_div_pow, pow_one]
          rcases n with _ | n'
          · omega
          · simp only [pow_succ, Nat.succ_sub_one, Nat.mul_div_cancel _ two_pos]
        have hidiv1 : i / 2 + 1 < 2 ^ n := by
          have : i + 1 < 2 * 2 ^ n := by linarith [(by ring : 2 ^ (n + 1) = 2 * 2 ^ n)]
          omega
        have hres := ih (i / 2) hn_pos (by omega) hidiv1 f' (by omega)
          (j ^^^ bit) (bit >>> 1) h_xor hbit''
        rw [hres, bitRev]
        have h1 : (i + 1) % 2 = 0 := by omega
        have h2 : (i + 1) / 2 = i / 2 + 1 := by omega
        rw [h1, h2]; ring

/-- The invariant maintained by `bitRevLoop`: after `step` iterations starting from the
    identity (with the `i` counter at `step` and the bit-reversed counter at `bitRev n step`),
    position `p` holds either `v0[bitRev n p]` (when `p` or its mirror has been processed)
    or `v0[p]` (when neither has been processed). -/
def bitRevLoop_inv_pred (n step : ℕ) (v0 a : Vector UInt32 (2 ^ n)) : Prop :=
  ∀ (p : ℕ) (hp : p < 2 ^ n),
    if p ≤ step ∨ bitRev n p ≤ step
    then a[p]'hp = v0[bitRev n p]'(bitRev_lt n p)
    else a[p]'hp = v0[p]'hp

/-- One step of `bitRevLoop` maintains the bit-reversal invariant. -/
private lemma bitRevLoop_step {N : ℕ}
    (v0 v_cur : Vector UInt32 (2 ^ N))
    (step : ℕ) (hstep1 : step + 1 < 2 ^ N)
    (hinv : bitRevLoop_inv_pred N step v0 v_cur) :
    let j' := bitRev N (step + 1)
    let hj' : j' < 2 ^ N := bitRev_lt N (step + 1)
    bitRevLoop_inv_pred N (step + 1) v0
      (if step + 1 < j' then
        (v_cur.set (step + 1) (v_cur[j']'hj') hstep1).set j' (v_cur[step + 1]'hstep1) hj'
       else v_cur) := by
  intro j' hj'
  have hjp_inv : bitRev N j' = step + 1 := bitRev_invol N (step + 1) hstep1
  intro p hp
  -- Helper: from hinv, for any q < 2^N, we know what v_cur[q] is at step
  have h_cur_at : ∀ (q : ℕ) (hq : q < 2 ^ N),
      (q ≤ step ∨ bitRev N q ≤ step → v_cur[q]'hq = v0[bitRev N q]'(bitRev_lt N q)) ∧
      (¬ (q ≤ step ∨ bitRev N q ≤ step) → v_cur[q]'hq = v0[q]'hq) := by
    intro q hq
    have h := hinv q hq
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rw [if_pos hc] at h; exact h
    · rw [if_neg hc] at h; exact h
  by_cases hswap : step + 1 < j'
  · -- Swap case
    rw [if_pos hswap]
    by_cases hp_jp : p = j'
    · subst hp_jp
      rw [Vector.getElem_set_self]
      have hcond : j' ≤ step + 1 ∨ bitRev N j' ≤ step + 1 := by
        right; rw [hjp_inv]
      rw [if_pos hcond]
      -- Goal: v_cur[step+1] = v0[bitRev N j']
      have hcond_old : ¬ (step + 1 ≤ step ∨ bitRev N (step + 1) ≤ step) := by
        push Not
        exact ⟨by omega, by omega⟩
      have h_eq := (h_cur_at (step + 1) hstep1).2 hcond_old
      rw [h_eq]
      -- Goal: v0[step+1] = v0[bitRev N j']; bitRev N j' = step+1
      congr 1
      omega
    · -- p ≠ j'
      rw [Vector.getElem_set_ne _ _ (Ne.symm hp_jp)]
      by_cases hp_step1 : p = step + 1
      · subst hp_step1
        rw [Vector.getElem_set_self]
        have hcond : step + 1 ≤ step + 1 ∨ bitRev N (step + 1) ≤ step + 1 := Or.inl (by omega)
        rw [if_pos hcond]
        -- Goal: v_cur[j'] = v0[bitRev N (step+1)]
        have hcond_old : ¬ (j' ≤ step ∨ bitRev N j' ≤ step) := by
          push Not
          refine ⟨by omega, ?_⟩
          rw [hjp_inv]; omega
        have h_eq := (h_cur_at j' hj').2 hcond_old
        rw [h_eq]
      · -- p ≠ j' ∧ p ≠ step+1
        rw [Vector.getElem_set_ne _ _ (Ne.symm hp_step1)]
        by_cases hc1 : p ≤ step + 1 ∨ bitRev N p ≤ step + 1
        · rw [if_pos hc1]
          have hc1' : p ≤ step ∨ bitRev N p ≤ step := by
            rcases hc1 with h1 | h2
            · left; omega
            · by_cases heq : bitRev N p = step + 1
              · exfalso; apply hp_jp
                have := bitRev_invol N p hp
                rw [heq] at this
                exact this.symm
              · right; omega
          exact (h_cur_at p hp).1 hc1'
        · rw [if_neg hc1]
          have hc1_old : ¬ (p ≤ step ∨ bitRev N p ≤ step) := by
            push Not at hc1 ⊢
            exact ⟨by omega, by omega⟩
          exact (h_cur_at p hp).2 hc1_old
  · -- No-swap case: j' ≤ step+1
    rw [if_neg hswap]
    push Not at hswap
    by_cases hc1 : p ≤ step + 1 ∨ bitRev N p ≤ step + 1
    · rw [if_pos hc1]
      by_cases hc_old : p ≤ step ∨ bitRev N p ≤ step
      · exact (h_cur_at p hp).1 hc_old
      · push Not at hc_old
        rcases hc1 with hp1 | hbp1
        · have hpeq : p = step + 1 := by omega
          subst hpeq
          rcases Nat.lt_or_ge j' (step + 1) with hjps | hjps
          · -- j' ≤ step, so cond at step is true via bitRev branch
            have hcs : bitRev N (step + 1) ≤ step := by omega
            exact (h_cur_at (step + 1) hstep1).1 (Or.inr hcs)
          · -- j' = step+1, fixed point
            have hjp_eq : j' = step + 1 := by omega
            have hcs' : ¬ (step + 1 ≤ step ∨ bitRev N (step + 1) ≤ step) := by
              push Not
              refine ⟨by omega, ?_⟩
              omega
            have h_eq := (h_cur_at (step + 1) hstep1).2 hcs'
            rw [h_eq]
            congr 1
            omega
        · -- bitRev N p = step+1 (since ≤ step+1 but not ≤ step)
          have hbpeq : bitRev N p = step + 1 := by omega
          have hp_eq : p = j' := by
            have := bitRev_invol N p hp
            rw [hbpeq] at this
            exact this.symm
          subst hp_eq
          have hjp_eq : j' = step + 1 := by
            obtain ⟨h1, _⟩ := hc_old
            omega
          have hcs' : ¬ (j' ≤ step ∨ bitRev N j' ≤ step) := by
            push Not
            refine ⟨by omega, ?_⟩
            rw [hjp_inv]; omega
          have h_eq := (h_cur_at j' hj').2 hcs'
          rw [h_eq]
          congr 1
          rw [hjp_inv, hjp_eq]
    · rw [if_neg hc1]
      have hc1_old : ¬ (p ≤ step ∨ bitRev N p ≤ step) := by
        push Not at hc1 ⊢
        exact ⟨by omega, by omega⟩
      exact (h_cur_at p hp).2 hc1_old

/-- Induction over `bitRevLoop`: applying `k` steps starting from `step` (with the
    bit-reversed counter at `bitRev N step`) maintains the invariant. -/
private lemma bitRevLoop_main {N : ℕ} (hN1 : 1 ≤ N) (hN64 : N ≤ 64)
    (v0 : Vector UInt32 (2 ^ N))
    (k step : ℕ) (hstepk : step + k < 2 ^ N)
    (j : ℕ) (hj : j = bitRev N step)
    (v_cur : Vector UInt32 (2 ^ N))
    (hinv : bitRevLoop_inv_pred N step v0 v_cur) :
    bitRevLoop_inv_pred N (step + k) v0 (bitRevLoop k step v_cur j) := by
  induction k generalizing step v_cur j with
  | zero =>
    simp only [Nat.add_zero]
    unfold bitRevLoop
    exact hinv
  | succ k' ih =>
    have hstep1 : step + 1 < 2 ^ N := by
      have : step + (k' + 1) < 2 ^ N := hstepk; omega
    have h_half : (2 ^ N : ℕ) / 2 = 2 ^ (N - 1) := by
      cases N with
      | zero => omega
      | succ N' =>
        simp only [Nat.succ_sub_one, pow_succ]
        exact Nat.mul_div_cancel _ (by norm_num)
    have hj'_eq : bitRevNext 64 j (2 ^ N / 2) = bitRev N (step + 1) := by
      rw [h_half]
      exact bitRevNext_spec N step hN1 hN64 hstep1 64 (by omega) j (2 ^ (N - 1)) hj rfl
    have hjp_lt : bitRev N (step + 1) < 2 ^ N := bitRev_lt N (step + 1)
    have h_j'_lt : bitRevNext 64 j (2 ^ N / 2) < 2 ^ N := hj'_eq ▸ hjp_lt
    have h_step := bitRevLoop_step v0 v_cur step hstep1 hinv
    simp only at h_step
    have h_arith : step + (k' + 1) = (step + 1) + k' := by omega
    rw [h_arith]
    apply ih (step + 1) (by omega) (bitRevNext 64 j (2 ^ N / 2)) hj'_eq
    -- Goal: bitRevLoop_inv_pred N (step + 1) v0 (inner vector from bitRevLoop body)
    by_cases h1 : step + 1 < bitRevNext 64 j (2 ^ N / 2)
    · have h1' : step + 1 < bitRev N (step + 1) := hj'_eq ▸ h1
      rw [if_pos h1'] at h_step
      simp only [dif_pos hstep1, dif_pos h_j'_lt, h1, if_true]
      -- Replace bitRevNext 64 j (2^N/2) with bitRev N (step+1); simp handles dependent proofs
      simp only [hj'_eq]
      exact h_step
    · have h1' : ¬ step + 1 < bitRev N (step + 1) := hj'_eq ▸ h1
      rw [if_neg h1'] at h_step
      simp only [h1, if_false]
      exact h_step

/-- The main correctness theorem for `bitRevLoop`: starting from the identity, after running
    `2^N - 1` steps, position `p` holds `v[bitRev N p]`. -/
lemma bitRevLoop_spec {N : ℕ} (hN64 : N < 64)
    (v : Vector UInt32 (2 ^ N)) (p : ℕ) (hp : p < 2 ^ N) :
    (bitRevLoop (2 ^ N - 1) 0 v 0)[p]'hp =
      v[bitRev N p]'(bitRev_lt N p) := by
  by_cases hN : N = 0
  · subst hN
    -- 2^0 = 1, p = 0, bitRev 0 0 = 0
    simp only [pow_zero] at hp
    interval_cases p
    -- bitRevLoop with k=0 returns v
    change (bitRevLoop 0 0 v 0)[0] = v[bitRev 0 0]
    unfold bitRevLoop
    simp only [bitRev]
  · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    have h2Npos : 0 < 2 ^ N := Nat.two_pow_pos N
    -- Initial invariant at step 0
    have h_init : bitRevLoop_inv_pred N 0 v v := by
      intro q hq
      by_cases hq0 : q = 0
      · subst hq0
        simp only [bitRev_zero, le_refl, true_or, if_true]
      · have hcond : ¬ (q ≤ 0 ∨ bitRev N q ≤ 0) := by
          push Not
          refine ⟨by omega, ?_⟩
          -- bitRev N q ≠ 0 because q ≠ 0 and bitRev is an involution
          by_contra h_le_zero
          have h_eq_zero : bitRev N q = 0 := by omega
          have h_invol := bitRev_invol N q hq
          rw [h_eq_zero] at h_invol
          simp at h_invol
          exact hq0 h_invol.symm
        simp only [hcond, if_false]
    -- j = 0 = bitRev N 0
    have hj0 : (0 : ℕ) = bitRev N 0 := (bitRev_zero N).symm
    -- Apply bitRevLoop_main with k = 2^N - 1, step = 0, j = 0
    have h_total : bitRevLoop_inv_pred N (0 + (2 ^ N - 1)) v
        (bitRevLoop (2 ^ N - 1) 0 v 0) :=
      bitRevLoop_main hN1 hN64.le v (2 ^ N - 1) 0 (by omega) 0 hj0 v h_init
    -- After step 2^N - 1: p < 2^N = (2^N - 1) + 1 → p ≤ 2^N - 1
    have h_cond : p ≤ 0 + (2 ^ N - 1) ∨ bitRev N p ≤ 0 + (2 ^ N - 1) := by
      left; omega
    have h_res := h_total p hp
    simp only [h_cond, if_true] at h_res
    exact h_res

/-- Helper: convert `bitRevLoop` spec from `Vector UInt32 (2^n)` to `Vector UInt32 m`. -/
lemma bitRevLoop_spec_m {m : ℕ} (n : ℕ) (hm_eq : m = 2 ^ n) (hn64 : n < 64)
    (v : Vector UInt32 m) (p : ℕ) (hp : p < m)
    (hbr_lt : bitRev n p < m) :
    (bitRevLoop (m - 1) 0 v 0)[p]'hp =
      v[bitRev n p]'hbr_lt := by
  revert v hp hbr_lt
  rw [hm_eq]
  intro v hp hbr_lt
  exact bitRevLoop_spec hn64 v p hp

lemma preprocessing_establishes_inv {m : ℕ} (n : ℕ)
    (hm_eq : m = 2 ^ n)
    (h_dvd : m ∣ mod64.toNat - 1)
    (v : Vector UInt32 m) (hv_bound : v.all (· < mod32))
    (roots : Vector UInt32 m) (_hroots : ntt_roots_correct m roots) :
    let a1 := bitRevLoop (m - 1) 0 (v.map toMont) 0
    let parity := nttInplace.go 64 m 0 &&& 1 != 0
    let a_in := if parity then radix2Pass (m / 2) 0 a1 else a1
    let start_q := if parity then 1 else 0
    ∃ hle : start_q ≤ n,
      outerLoop_inv n start_q hle hm_eq v a_in := by
  have hn64 : n < 64 := n_lt_64_of_pow2_nat m n hm_eq h_dvd
  set a1 := bitRevLoop (m - 1) 0 (v.map toMont) 0 with ha1_def
  -- bound on a1
  have ha1_bound : a1.all (· < mod32) := by
    rw [ha1_def]
    exact bitRevLoop_bound _ _ _ _ (vector_map_to_mont_bound v hv_bound)
  -- Key spec: a1[p] = (v.map toMont)[bitRev n p] for p < m
  have ha1_spec : ∀ (p : ℕ) (hp : p < m),
      a1[p]'hp = (v.map toMont)[bitRev n p]'(by rw [hm_eq]; exact bitRev_lt n p) := by
    intro p hp
    rw [ha1_def]
    exact bitRevLoop_spec_m n hm_eq hn64 (v.map toMont) p hp
      (by rw [hm_eq]; exact bitRev_lt n p)
  -- The form a1[p] = toMont v[bitRev n p] (after getElem_map)
  have ha1_spec' : ∀ (p : ℕ) (hp : p < m),
      a1[p]'hp = toMont (v[bitRev n p]'(by rw [hm_eq]; exact bitRev_lt n p)) := by
    intro p hp
    rw [ha1_spec p hp]
    rw [Vector.getElem_map]
  -- Case split on parity
  by_cases hpar : nttInplace.go 64 m 0 &&& 1 != 0
  · -- Odd case: n is odd, start_q = 1
    have hn_odd : Odd n := by
      by_contra h
      rw [Nat.not_odd_iff_even] at h
      have := go_parity_even_nat m n hm_eq hn64 h
      simp_all
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h => by
      subst h; rcases hn_odd with ⟨k, hk⟩; omega)
    -- Use refine with explicit value, then prove parity-conditional bits
    have hpar_val : (if (nttInplace.go 64 m 0 &&& 1 != 0) = true then 1 else 0) = 1 := by
      rw [if_pos hpar]
    have hpar_val_b : (nttInplace.go 64 m 0 &&& 1 != 0) = true := hpar
    -- We want to show ∃ hle, outerLoop_inv n (if .. then 1 else 0) hle ..
    -- Goal: ∃ hle : 1 ≤ n, outerLoop_inv n 1 hle hm_eq v (radix2Pass _ 0 a1)
    change ∃ hle, outerLoop_inv n
      (if (nttInplace.go 64 m 0 &&& 1 != 0) = true then 1 else 0) hle hm_eq v
      (if (nttInplace.go 64 m 0 &&& 1 != 0) = true then radix2Pass (m / 2) 0 a1 else a1)
    rw [if_pos hpar_val_b, if_pos hpar_val_b]
    refine ⟨hn1, ?_, ?_⟩
    · -- Bound
      exact radix2Pass_bound _ _ _ ha1_bound
    · -- Value correctness for q = 1
      intro b r hb idx hidx
      have hr : r.val = 0 ∨ r.val = 1 := by
        have := r.isLt; omega
      -- idx = b * 2 + r.val
      -- Bounds
      have h_pow_eq : 2 * 2 ^ (n - 1) = 2 ^ n := by
        rw [(by ring : (2 : ℕ) * 2 ^ (n - 1) = 2 ^ (n - 1 + 1))]
        congr 1; omega
      have h2b1_lt : 2 * b + 1 < m := by
        rw [hm_eq]; have hb' : b < 2 ^ (n - 1) := hb; omega
      have h2b_lt : 2 * b < m := by omega
      have hbRb_lt : bitRev (n - 1) b < 2 ^ (n - 1) := bitRev_lt (n - 1) b
      have hbRb_idx_lt : bitRev (n - 1) b < m := by
        rw [hm_eq]; have : 2 ^ (n - 1) ≤ 2 ^ n :=
          Nat.pow_le_pow_right (by norm_num) (by omega); omega
      have hbRb1_idx_lt : 2 ^ (n - 1) + bitRev (n - 1) b < m := by
        rw [hm_eq]; omega
      -- bitRev n (2b) and bitRev n (2b+1)
      have hbR_2b : bitRev n (2 * b) = bitRev (n - 1) b := by
        conv_lhs => rw [(by omega : n = (n - 1) + 1)]
        simp only [bitRev_succ]
        have hmod : (2 * b) % 2 = 0 := by omega
        have hdiv : (2 * b) / 2 = b := by omega
        rw [hmod, hdiv]; ring
      have hbR_2b1 : bitRev n (2 * b + 1) = 2 ^ (n - 1) + bitRev (n - 1) b := by
        conv_lhs => rw [(by omega : n = (n - 1) + 1)]
        simp only [bitRev_succ]
        have hmod : (2 * b + 1) % 2 = 1 := by omega
        have hdiv : (2 * b + 1) / 2 = b := by omega
        rw [hmod, hdiv]; ring
      -- Convert a1[2b] and a1[2b+1] to toMont v[...]
      have ha1_2b : (a1[2 * b]'h2b_lt).toNat =
          (toMont (v[bitRev (n - 1) b]'hbRb_idx_lt)).toNat := by
        rw [ha1_spec' (2 * b) h2b_lt]
        rw [getElem_congr_idx (c := v) hbR_2b]
      have ha1_2b1 : (a1[2 * b + 1]'h2b1_lt).toNat =
          (toMont (v[2 ^ (n - 1) + bitRev (n - 1) b]'hbRb1_idx_lt)).toNat := by
        rw [ha1_spec' (2 * b + 1) h2b1_lt]
        rw [getElem_congr_idx (c := v) hbR_2b1]
      -- ntt_sub_input n 1 hn1 hm_eq v b ⟨0, _⟩ = toMont v[bitRev (n-1) b]
      have h_input_0 : (ntt_sub_input n 1 hn1 hm_eq v b) ⟨0, by norm_num⟩ =
          ((toMont (v[bitRev (n - 1) b]'hbRb_idx_lt)).toNat : ZMod mod32.toNat) := by
        unfold ntt_sub_input
        simp only [Fin.cast]
        congr 3
        change v[(2 ^ (n - 1) * 0 + bitRev (n - 1) b)]'_ = v[bitRev (n - 1) b]'hbRb_idx_lt
        exact getElem_congr_idx (by ring : 2 ^ (n - 1) * 0 + bitRev (n - 1) b = bitRev (n - 1) b)
      have h_input_1 : (ntt_sub_input n 1 hn1 hm_eq v b) ⟨1, by norm_num⟩ =
          ((toMont (v[2 ^ (n - 1) + bitRev (n - 1) b]'hbRb1_idx_lt)).toNat : ZMod mod32.toNat) := by
        unfold ntt_sub_input
        simp only [Fin.cast]
        congr 3
        change v[(2 ^ (n - 1) * 1 + bitRev (n - 1) b)]'_ =
          v[2 ^ (n - 1) + bitRev (n - 1) b]'hbRb1_idx_lt
        exact getElem_congr_idx
          (by ring : 2 ^ (n - 1) * 1 + bitRev (n - 1) b = 2 ^ (n - 1) + bitRev (n - 1) b)
      -- Compute ref_ntt 1 ω input r based on r
      rcases hr with hr0 | hr1
      · -- r.val = 0
        have hrr : r = ⟨0, by norm_num⟩ := Fin.ext hr0
        have h_ref : ref_ntt 1
            ((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ 1))
            (ntt_sub_input n 1 hn1 hm_eq v b) r =
            (ntt_sub_input n 1 hn1 hm_eq v b) ⟨0, by norm_num⟩ +
            (ntt_sub_input n 1 hn1 hm_eq v b) ⟨1, by norm_num⟩ := by
          rw [hrr]; simp only [ref_ntt]; simp
        rw [h_ref, h_input_0, h_input_1, ← ha1_2b, ← ha1_2b1]
        have hpair := (radix2Pass_ZMod_pair a1 ha1_bound b h2b1_lt).1
        have hidx_eq : idx = 2 * b := by
          change b * 2 ^ 1 + r.val = 2 * b
          rw [hr0]; ring
        rw [show ((radix2Pass (m / 2) 0 a1)[idx]'hidx).toNat =
            ((radix2Pass (m / 2) 0 a1).get ⟨2 * b, by omega⟩).toNat from by
          congr 1; exact getElem_congr_idx hidx_eq]
        exact hpair
      · -- r.val = 1
        have hrr : r = ⟨1, by norm_num⟩ := Fin.ext hr1
        have h_ref : ref_ntt 1
            ((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ 1))
            (ntt_sub_input n 1 hn1 hm_eq v b) r =
            (ntt_sub_input n 1 hn1 hm_eq v b) ⟨0, by norm_num⟩ -
            (ntt_sub_input n 1 hn1 hm_eq v b) ⟨1, by norm_num⟩ := by
          rw [hrr]; simp only [ref_ntt]; simp
        rw [h_ref, h_input_0, h_input_1, ← ha1_2b, ← ha1_2b1]
        have hpair := (radix2Pass_ZMod_pair a1 ha1_bound b h2b1_lt).2
        have hidx_eq : idx = 2 * b + 1 := by
          change b * 2 ^ 1 + r.val = 2 * b + 1
          rw [hr1]; ring
        rw [show ((radix2Pass (m / 2) 0 a1)[idx]'hidx).toNat =
            ((radix2Pass (m / 2) 0 a1).get ⟨2 * b + 1, h2b1_lt⟩).toNat from by
          congr 1; exact getElem_congr_idx hidx_eq]
        exact hpair
  · -- Even case: n is even, start_q = 0
    change ∃ hle, outerLoop_inv n
      (if (nttInplace.go 64 m 0 &&& 1 != 0) = true then 1 else 0) hle hm_eq v
      (if (nttInplace.go 64 m 0 &&& 1 != 0) = true then radix2Pass (m / 2) 0 a1 else a1)
    rw [if_neg hpar, if_neg hpar]
    refine ⟨Nat.zero_le n, ha1_bound, ?_⟩
    intro b r hb idx hidx
    -- r : Fin 1, r.val = 0
    have hr0 : r.val = 0 := by have := r.isLt; omega
    have hidx_b : idx = b := by
      change b * 2 ^ 0 + r.val = b
      rw [hr0]; ring
    have hbRb_lt : bitRev n b < 2 ^ n := bitRev_lt n b
    have hbRb_idx_lt : bitRev n b < m := by rw [hm_eq]; exact hbRb_lt
    -- ref_ntt 0 ω a r = a r
    have h_ref : ref_ntt 0
        ((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ 0))
        (ntt_sub_input n 0 (Nat.zero_le n) hm_eq v b) r =
        (ntt_sub_input n 0 (Nat.zero_le n) hm_eq v b) r := rfl
    rw [h_ref]
    -- ntt_sub_input n 0 _ hm_eq v b r = toMont v[bitRev n b]
    have h_input : (ntt_sub_input n 0 (Nat.zero_le n) hm_eq v b) r =
        ((toMont (v[bitRev n b]'hbRb_idx_lt)).toNat : ZMod mod32.toNat) := by
      unfold ntt_sub_input
      simp only [Fin.cast]
      congr 3
      change v[(2 ^ n * r.val + bitRev n b)]'_ = v[bitRev n b]'hbRb_idx_lt
      exact getElem_congr_idx (by rw [hr0]; ring)
    rw [h_input]
    have h_ax := ha1_spec' idx hidx
    have h_a1 : (a1[idx]'hidx).toNat =
        (toMont (v[bitRev n b]'hbRb_idx_lt)).toNat := by
      rw [h_ax]
      have heq : bitRev n idx = bitRev n b := by rw [hidx_b]
      rw [getElem_congr_idx (c := v) heq]
    rw [h_a1]
