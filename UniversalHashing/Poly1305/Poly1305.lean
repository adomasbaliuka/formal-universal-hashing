import Mathlib
import UniversalHashing.Poly1305.Poly1305Prime
import UniversalHashing.DeltaUniversal
/-!
# Poly1305

This file formalizes some properties of the Poly1305 universal hash, see
"The Poly1305-AES message-authentication code" by Daniel J. Bernstein (2005).

## Overview

Poly1305 evaluates a message polynomial modulo the prime `p = 2^130 - 5`.
A message `m` (a byte string of length `ℓ`) is split into `q = ⌈ℓ/16⌉` chunks,
each chunk padded with a `1`-bit to produce coefficients `c₁, …, c_q ∈ {1, …, 2^129}`.
The message polynomial is `m̄(x) = c₁x^q + c₂x^(q-1) + ⋯ + c_q·x`.
The hash function is `Hr(m) = (m̄(r) mod p) mod 2^128`.


## Main results

* `Poly1305.differential_probability_bound` : Theorem 3.3 — for distinct messages
  `m ≠ m'` of at most `L` bytes, and any target difference `g`, the number of
  keys `r` in `ZMod P` such that `Hr(m) = Hr(m') + g` is at most `8⌈L/16⌉`

-/

namespace Poly1305

open Polynomial Finset BigOperators

/-! ## The Poly1305 prime -/

/-- The Poly1305 prime: `p = 2^130 - 5`. -/
def P : ℕ := 2 ^ 130 - 5

lemma P_val : P = 2 ^ 130 - 5 := rfl

lemma P_pos : 0 < P := by unfold P; omega

lemma P_gt_one : 1 < P := by unfold P; omega

/-- `2^129 < P`, ensuring all message coefficients are nonzero mod `P`. -/
lemma two_pow_129_lt_P : 2 ^ 129 < P := by unfold P; omega

/-- `P < 2^131`, used in the target-set cardinality bound. -/
lemma P_lt_two_pow_131 : P < 2 ^ 131 := by unfold P; omega

/-- `P < 4 * 2^128`, equivalent form useful for counting. -/
lemma P_lt_four_mul_two_pow_128 : P < 4 * 2 ^ 128 := by unfold P; ring_nf; omega

/-- **Theorem 3.1** (Bernstein 2005): `2^130 - 5` is prime. -/
theorem P_prime : Nat.Prime P := Poly1305Prime.P_prime

instance : Fact (Nat.Prime P) := ⟨P_prime⟩

/-! ## Message encoding -/

/-- A byte: a value in `{0, 1, …, 255}`. -/
abbrev Byte := Fin 256

/-- A message: a finite sequence of bytes. -/
abbrev Message := List Byte

/-- Number of 16-byte blocks: `⌈ℓ/16⌉`. -/
def numBlocks (m : Message) : ℕ := (m.length + 15) / 16

/-- Convert a list of bytes to its unsigned little-endian value:
`b₀ + 256·b₁ + 256²·b₂ + ⋯` -/
def littleEndianVal : List Byte → ℕ
  | [] => 0
  | b :: bs => b.val + 256 * littleEndianVal bs

/-- The Poly1305 coefficient for a chunk of bytes:
the little-endian value plus `2^(8·length)` (the padding bit).
For a chunk of `j` bytes (`1 ≤ j ≤ 16`), the result is in `{2^8, …, 2^129 - 1}`. -/
def chunkCoeff (chunk : List Byte) : ℕ :=
  littleEndianVal chunk + 2 ^ (8 * chunk.length)

/-- Extract the `i`-th 16-byte chunk of a message (0-indexed).
The last chunk may have fewer than 16 bytes. -/
def getChunk (m : Message) (i : ℕ) : List Byte :=
  (m.drop (16 * i)).take 16

/-- The list of Poly1305 coefficients `[c₁, c₂, …, c_q]` for a message. -/
def msgCoeffs (m : Message) : List ℕ :=
  (List.range (numBlocks m)).map (fun i ↦ chunkCoeff (getChunk m i))

@[simp] lemma msgCoeffs_length (m : Message) :
    (msgCoeffs m).length = numBlocks m := by
  simp [msgCoeffs]

/-- The message polynomial over `ZMod P`:
`m̄(x) = c₁·x^q + c₂·x^(q-1) + ⋯ + c_q·x`,
where `q = numBlocks m`. -/
noncomputable def msgPoly (m : Message) : Polynomial (ZMod P) :=
  let cs := msgCoeffs m
  let q := numBlocks m
  ∑ i ∈ range q,
    Polynomial.monomial (q - i) ((cs.getD i 0 : ℕ) : ZMod P)

/-- The Poly1305 hash function:
`Hr(m) = (m̄(r) mod p) mod 2^128`. -/
noncomputable def Hr (r : ZMod P) (m : Message) : ZMod (2 ^ 128) :=
  ((Polynomial.eval r (msgPoly m)).val : ZMod (2 ^ 128))

-- TODO add computable versions as well (these are noncomputable because Mathlib polynomials are...)

/-! ## Properties of the coefficient encoding -/

/-
The little-endian value of a list of bytes is less than `256^length`.
-/
lemma littleEndianVal_lt (bs : List Byte) :
    littleEndianVal bs < 256 ^ bs.length := by
  induction bs with
  | nil => decide +revert
  | cons b bs ih =>
    simp only [littleEndianVal, List.length_cons, pow_succ]
    linarith [Fin.is_lt b]

/-
A chunk of length ≤ 16 has coefficient at most `2^129 - 1`.
-/
lemma chunkCoeff_le_two_pow_129_sub_one (chunk : List Byte) (h : chunk.length ≤ 16) :
    chunkCoeff chunk ≤ 2 ^ 129 - 1 := by
  interval_cases _ : chunk.length <;> simp_all only [chunkCoeff]
  all_goals (have := littleEndianVal_lt chunk
             norm_num [‹chunk.length = _›] at this ⊢
             linarith)

/-
A nonempty chunk has coefficient ≥ 1.
-/
lemma chunkCoeff_pos (chunk : List Byte) (_ : chunk ≠ []) :
    1 ≤ chunkCoeff chunk := by
  exact le_add_of_nonneg_of_le ( Nat.zero_le _ ) ( Nat.one_le_pow _ _ ( by decide ) )

/-
Each coefficient in `msgCoeffs` is less than `P`.
-/
lemma msgCoeffs_lt_P (m : Message) (c : ℕ) (hc : c ∈ msgCoeffs m) :
    c < P := by
  obtain ⟨ i, hi ⟩ := List.mem_map.mp hc
  refine hi.2 ▸ lt_of_le_of_lt (chunkCoeff_le_two_pow_129_sub_one _ ?_) ?_
  · unfold getChunk; aesop
  · exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) two_pow_129_lt_P

/-
Each coefficient of a nonempty message is positive.
-/
lemma msgCoeffs_pos (m : Message) (c : ℕ) (hc : c ∈ msgCoeffs m) :
    1 ≤ c := by
  obtain ⟨ i, hi, rfl ⟩ := List.mem_map.mp hc
  by_cases h : getChunk m i = [] <;> simp_all +decide only [List.mem_range, chunkCoeff]
  exact Nat.one_le_iff_ne_zero.mpr ( by positivity )

/-
Each coefficient is nonzero in `ZMod P`.
-/
lemma msgCoeffs_ne_zero_mod (m : Message) (c : ℕ) (hc : c ∈ msgCoeffs m) :
    (c : ZMod P) ≠ 0 := by
  rw [Ne.eq_def, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt ( msgCoeffs_pos m c hc ) ( msgCoeffs_lt_P m c hc )

/-! ## Properties of the message polynomial -/

/-- The message polynomial of an empty message is zero. -/
@[simp] lemma msgPoly_nil : msgPoly ([] : Message) = 0 := by
  simp [msgPoly, numBlocks]

/-
The degree of the message polynomial is at most `numBlocks m`.
-/
lemma msgPoly_natDegree_le (m : Message) :
    (msgPoly m).natDegree ≤ numBlocks m := by
  -- The degree of a monomial is its exponent.
  have h_deg_monomial : ∀ i ∈ Finset.range (numBlocks m),
      Polynomial.natDegree
        (Polynomial.monomial (numBlocks m - i) ((msgCoeffs m).getD i 0 : ZMod P))
        ≤ numBlocks m := by
    aesop
  exact le_trans ( Polynomial.natDegree_sum_le _ _ ) ( Finset.sup_le h_deg_monomial )

/-
`numBlocks` is monotone in the length parameter.
-/
lemma numBlocks_le_of_length_le (m : Message) (L : ℕ) (h : m.length ≤ L) :
    numBlocks m ≤ (L + 15) / 16 := by
  exact Nat.div_le_div_right ( by linarith )

/-! ## Theorem 3.2: Injectivity of the encoding -/

/-
The little-endian encoding of bytes is injective.
-/
lemma littleEndianVal_injective (bs bs' : List Byte)
    (hlen : bs.length = bs'.length) (hval : littleEndianVal bs = littleEndianVal bs') :
    bs = bs' := by
  induction bs generalizing bs' with
  | nil =>
    cases bs' with
    | nil => simp_all
    | cons b' bs' => simp_all
  | cons b bs ih =>
    cases bs' with
    | nil => simp_all
    | cons b' bs' =>
      simp_all only [List.cons.injEq]
      have h_val_eq : b.val + 256 * littleEndianVal bs = b'.val + 256 * littleEndianVal bs' :=
        hval
      grind

/-
Two chunks with the same `chunkCoeff` and equal lengths must be identical.
-/
lemma chunkCoeff_injective (c c' : List Byte)
    (hlen : c.length = c'.length) (hval : chunkCoeff c = chunkCoeff c') :
    c = c' := by
  -- Apply the.Injectivity of `littleEndianVal` to conclude that `c = c'`.
  apply littleEndianVal_injective
  · exact hlen
  · unfold chunkCoeff at hval; aesop

/-
`getChunk` is well-behaved: retrieving chunk `i` and reconstructing gives the original.
-/
lemma getChunk_length (m : Message) (i : ℕ) (hi : i < numBlocks m) :
    1 ≤ (getChunk m i).length ∧ (getChunk m i).length ≤ 16 := by
  unfold getChunk
  simp +zetaDelta only [List.length_take, List.length_drop, le_inf_iff, Nat.one_le_ofNat,
    true_and, inf_le_left, and_true] at *
  unfold numBlocks at hi; omega

/-
The length of the last chunk determines the message length mod 16.
-/
lemma getChunk_last_length (m : Message) (hm : m ≠ []) :
    (getChunk m (numBlocks m - 1)).length =
    if m.length % 16 = 0 then 16 else m.length % 16 := by
  unfold getChunk; split_ifs
  · unfold numBlocks
    rw [List.length_take]
    rw [show 16 * ((List.length m + 15) / 16 - 1) = List.length m - 16 from by omega,
        List.length_drop]
    rw [Nat.sub_sub_self
        (Nat.le_of_dvd (List.length_pos_iff.mpr hm) (Nat.dvd_of_mod_eq_zero ‹_›))]
    norm_num
  · rw [List.length_take, List.length_drop]
    unfold numBlocks; omega

/-
The message length is recoverable from `numBlocks` and the last chunk's coefficient.
-/
lemma length_determined_by_coeffs (m m' : Message) (hq : numBlocks m = numBlocks m')
    (hcoeffs : ∀ i < numBlocks m, (msgCoeffs m).getD i 0 = (msgCoeffs m').getD i 0) :
    m.length = m'.length := by
  by_cases hm : m = [] <;> by_cases hm' : m' = []
    <;> simp_all only [numBlocks, List.length_nil, zero_add, Nat.reduceDiv,
          not_lt_zero, msgCoeffs, List.range_zero, List.map_nil,
          List.getD_eq_getElem?_getD, getElem?_pos, Option.getD_some,
          List.length_map, List.length_range, List.getElem_map, List.getElem_range,
          List.getElem?_map, Nat.div_eq_zero_iff, List.length_eq_zero_iff]
  · omega
  · grind
  · have h_last_chunk_length :
          (getChunk m (numBlocks m - 1)).length =
          (getChunk m' (numBlocks m' - 1)).length := by
      have h_last_chunk_length :
          ∀ c c' : List Byte, chunkCoeff c = chunkCoeff c' → c.length = c'.length := by
        intros c c' h_eq
        have h_exp : 2 ^ (8 * c.length) ≤ chunkCoeff c ∧
            chunkCoeff c < 2 ^ (8 * c.length + 1) := by
          have h_exp : littleEndianVal c < 2 ^ (8 * c.length) := by
            convert littleEndianVal_lt c using 1 ; norm_num [pow_mul]
          unfold chunkCoeff; simp_all [pow_succ']
          linarith
        have h_exp' : 2 ^ (8 * c'.length) ≤ chunkCoeff c' ∧
            chunkCoeff c' < 2 ^ (8 * c'.length + 1) := by
          have h_exp' : 2 ^ (8 * c'.length) ≤ chunkCoeff c' ∧
              chunkCoeff c' < 2 ^ (8 * c'.length + 1) := by
            have h_exp' : littleEndianVal c' < 2 ^ (8 * c'.length) := by
              convert littleEndianVal_lt c' using 1 ; ring_nf
              norm_num [pow_mul']
            exact ⟨Nat.le_add_left _ _, by
              rw [pow_succ']
              linarith [show chunkCoeff c' = littleEndianVal c' + 2 ^ (8 * c'.length) from rfl]⟩
          exact h_exp'
        exact le_antisymm
          (le_of_not_gt fun h ↦ by
            linarith [pow_le_pow_right₀ (show 1 ≤ 2 by decide)
              (show 8 * c.length ≥ 8 * c'.length + 1 by linarith)])
          (le_of_not_gt fun h ↦ by
            linarith [pow_le_pow_right₀ (show 1 ≤ 2 by decide)
              (show 8 * c'.length ≥ 8 * c.length + 1 by linarith)])
      convert h_last_chunk_length _ _ ( hcoeffs _ _ ) using 1
      · unfold numBlocks; aesop
      · exact hq ▸ Nat.pred_lt (ne_bot_of_gt (Nat.div_pos
          (Nat.le_of_not_lt fun h ↦ by
            rcases m with (_ | ⟨_, _ | m⟩) <;> simp_all +arith)
          (by decide)))
    unfold getChunk at *
    unfold numBlocks at *; simp_all [Nat.add_div]
    split_ifs at * <;> omega

/-
Messages with equal coefficient lists are equal.
-/
lemma msg_eq_of_coeffs_eq (m m' : Message)
    (hq : numBlocks m = numBlocks m')
    (hcoeffs : ∀ i < numBlocks m,
      (msgCoeffs m).getD i 0 = (msgCoeffs m').getD i 0) :
    m = m' := by
  -- By length_determined_by_coeffs, m.length = m'.length.
  have h_len : m.length = m'.length :=
    length_determined_by_coeffs m m' hq hcoeffs
  -- By chunkCoeff_injective, getChunk m i = getChunk m' i for all i < numBlocks m.
  have h_chunks_eq : ∀ i < numBlocks m, getChunk m i = getChunk m' i := by
    intro i hi
    apply chunkCoeff_injective
    · unfold getChunk; aesop
    · grind +locals
  -- By definition of `getChunk`, we can reconstruct the original message from its chunks.
  have h_reconstruct :
      m = List.flatten (List.map (fun i ↦ getChunk m i) (List.range (numBlocks m))) ∧
      m' = List.flatten (List.map (fun i ↦ getChunk m' i) (List.range (numBlocks m'))) := by
    have h_reconstruct :
        ∀ (L : List Byte) (n : ℕ),
        List.flatten (List.map (fun i ↦ L.drop (16 * i) |>.take 16) (List.range n)) =
        L.take (16 * n) := by
      intro L n
      induction n with
      | zero => simp_all
      | succ n ih =>
        simp_all only [List.getD_eq_getElem?_getD, msgCoeffs_length,
          getElem?_pos, Option.getD_some, List.range_succ, List.map_append,
          List.map_cons, List.map_nil, List.flatten_append, List.flatten_cons,
          List.flatten_nil, List.append_nil, Nat.mul_succ]
        rw [List.take_add]
    simp_all only [List.getD_eq_getElem?_getD, msgCoeffs_length, getElem?_pos,
      Option.getD_some, getChunk, List.take_self_eq_iff, and_self, ge_iff_le]
    unfold numBlocks; omega
  rw [h_reconstruct.1, h_reconstruct.2, hq]
  rw [List.map_congr_left
    fun i hi ↦ h_chunks_eq i <| by simpa [hq] using List.mem_range.mp hi]

/-
**Theorem 3.2** (Bernstein 2005): If the polynomial `m̄' - m̄` equals a constant
`u` modulo `p`, then the messages are identical.

The proof proceeds as follows: if `m̄' - m̄ = C u` as polynomials over `ZMod P`,
then all non-constant coefficients are zero mod `P`. Since each coefficient `cᵢ`
is in `{1, …, 2^129}` and `2^129 < P`, equal coefficients mod `P` means equal
coefficients over `ℤ`. From equal coefficients, `q = q'` (the number of blocks)
and then the message bytes are recoverable.
-/
theorem encoding_injective (m m' : Message) (u : ZMod P) :
    msgPoly m' - msgPoly m = Polynomial.C u → m = m' := by
  intro h_eq
  have h_blocks : numBlocks m = numBlocks m' := by
    by_contra h_contra
    -- Without loss of generality, assume `numBlocks m < numBlocks m'`.
    wlog h_wlog : numBlocks m < numBlocks m' generalizing m m' u
    · exact this m' m (-u)
          (by simpa [sub_eq_iff_eq_add] using by linear_combination' h_eq.symm)
          (Ne.symm h_contra) (lt_of_le_of_ne (le_of_not_gt h_wlog) (Ne.symm h_contra))
    · -- The coefficient of `x^(numBlocks m')` in `msgPoly m'` is nonzero mod `P`.
      have h_coeff_m' : (msgPoly m').coeff (numBlocks m') ≠ 0 := by
        unfold msgPoly; simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
        rw [Finset.sum_eq_single 0] <;>
          simp_all only [tsub_zero, ↓reduceIte, List.getD_eq_getElem?_getD, ne_eq,
            mem_range, ite_eq_right_iff]
        · convert msgCoeffs_ne_zero_mod m' _ _
          cases h : numBlocks m' <;> aesop
        · intros; omega
        · intro h; omega
      replace h_eq := congr_arg (fun p ↦ p.coeff (numBlocks m')) h_eq
      simp_all only [Polynomial.coeff_sub, Polynomial.coeff_C, sub_eq_iff_eq_add]
      simp_all only [ne_eq]
      split_ifs at h_coeff_m' <;> simp_all only [Nat.not_lt_zero, zero_add, if_false]
      exact h_coeff_m' (Polynomial.coeff_eq_zero_of_natDegree_lt <| by
        linarith [msgPoly_natDegree_le m])
  have h_coeffs : ∀ i < numBlocks m, (msgCoeffs m).getD i 0 = (msgCoeffs m').getD i 0 := by
    -- By comparing coefficients, each coefficient of `m'` equals that of `m`.
    intros i hi
    have h_coeff_eq : (msgCoeffs m').getD i 0 ≡ (msgCoeffs m).getD i 0 [MOD P] := by
      replace h_eq :=
        congr_arg (fun f ↦ Polynomial.coeff f (numBlocks m' - i)) h_eq
      simp_all only [List.getD_eq_getElem?_getD]
      simp_all only [msgPoly, Polynomial.coeff_sub,
        Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
      rw [Finset.sum_eq_single i, Finset.sum_eq_single i] at h_eq
        <;> simp_all only [Polynomial.coeff_C, mem_range, ne_eq,
          List.getD_eq_getElem?_getD, ite_eq_right_iff, not_true, false_implies, if_true]
      · rw [if_neg (Nat.sub_ne_zero_of_lt hi)] at h_eq
        exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp (sub_eq_zero.mp h_eq)
      · intros; omega
      · intros; omega
    -- Both coefficients are < P so they are equal as natural numbers.
    have h_coeff_range : (msgCoeffs m).getD i 0 < P ∧ (msgCoeffs m').getD i 0 < P := by
      have h_coeff_range : ∀ m : Message, ∀ c ∈ msgCoeffs m, c < P :=
        msgCoeffs_lt_P
      exact ⟨
        h_coeff_range m _ <| by
          rw [List.getD_eq_getElem]; exact List.getElem_mem <| by aesop,
        h_coeff_range m' _ <| by
          rw [List.getD_eq_getElem]; exact List.getElem_mem <| by aesop⟩
    exact Nat.mod_eq_of_lt h_coeff_range.1 ▸ Nat.mod_eq_of_lt h_coeff_range.2 ▸ h_coeff_eq.symm
  exact msg_eq_of_coeffs_eq m m' h_blocks h_coeffs

/-- Distinct messages give distinct message polynomials. -/
theorem msgPoly_injective : Function.Injective (@msgPoly) := by
  intro m m' h
  exact encoding_injective m m' 0 (by rw [map_zero, sub_eq_zero]; exact h.symm)

/-- For distinct messages and any constant, the shifted difference polynomial is nonzero.
This is the contrapositive of Theorem 3.2. -/
theorem diff_poly_ne_zero (m m' : Message) (hne : m ≠ m') (u : ZMod P) :
    msgPoly m' - msgPoly m - Polynomial.C u ≠ 0 := by
  intro h
  apply hne
  exact encoding_injective m m' u (sub_eq_zero.mp h)

/-! ## Polynomial root counting -/

section FiniteField

variable (K : Type*)

/-
A nonzero polynomial over a field has at most `natDegree` roots.
We state a version counting the elements of a filter set.
-/
lemma card_roots_filter_le [Field K] [Fintype K] [DecidableEq K]
    {f : Polynomial K} (hf : f ≠ 0) :
    (univ.filter (fun r ↦ Polynomial.IsRoot f r)).card ≤ f.natDegree := by
  refine le_trans ?_ (Polynomial.card_roots' f)
  convert Multiset.toFinset_card_le _
  all_goals try infer_instance
  ext
  simp_all only [ne_eq, IsRoot.def, mem_filter, mem_univ, true_and,
    Multiset.mem_toFinset, mem_roots', not_false_eq_true]

/-
The number of `r` with `f(r) = t` is at most `natDegree f`,
provided `f - C t ≠ 0`.
-/
lemma card_preimage_le [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) (t : K) (hf : f - Polynomial.C t ≠ 0) :
    (univ.filter (fun r ↦ Polynomial.eval r f = t)).card ≤ f.natDegree := by
  have := @card_roots_filter_le (K := K) (by infer_instance) (by infer_instance)
      (by infer_instance) (f:=f - Polynomial.C t) hf
  simp_all [Polynomial.IsRoot, sub_eq_zero]

/-
Union bound for polynomial preimages: the number of `r` such that
`f(r) ∈ S` is at most `|S| * natDegree(f)`, provided `f - C t ≠ 0` for all `t ∈ S`.
-/
lemma card_eval_mem_filter_le [Field K] [Fintype K] [DecidableEq K]
    (f : Polynomial K) (S : Finset K)
    (hf : ∀ t ∈ S, f - Polynomial.C t ≠ 0) :
    (univ.filter (fun r ↦ Polynomial.eval r f ∈ S)).card ≤ S.card * f.natDegree := by
  have h_incl :
      (Finset.univ.filter (fun r ↦ f.eval r ∈ S)) ⊆
      Finset.biUnion S (fun t ↦ Finset.univ.filter (fun r ↦ f.eval r = t)) := by
    grind
  apply le_trans (Finset.card_le_card h_incl)
  apply le_trans Finset.card_biUnion_le
  apply Finset.sum_le_card_nsmul
  intro t ht
  apply card_preimage_le
  exact hf t ht

end FiniteField

/-! ## Theorem 3.3: Differential probability bound -/

/-
The number of elements `t : ZMod P` whose canonical representative is congruent
to a given `g` modulo `2^128`. Since `P = 2^130 - 5 < 4 · 2^128`, there are
at most 4 such values. (The paper needs 8 because of the sign ambiguity in
the difference of two representatives, i.e., both `v` and `v - P` must be considered.)
-/
lemma card_val_fiber_le (g : ZMod (2 ^ 128)) :
    (univ.filter (fun t : ZMod P ↦ (t.val : ZMod (2 ^ 128)) = g)).card ≤ 4 := by
  have h_target_card :
      ∀ t : ZMod P, t.val = g → ∃ n ∈ ({0, 1, 2, 3} : Finset ℕ),
      t.val = g.val + n * 2 ^ 128 := by
    intros t ht
    have h_eq : t.val % 2 ^ 128 = g.val := by
      aesop
    have h_eq : t.val < 4 * 2 ^ 128 :=
      lt_of_lt_of_le (ZMod.val_lt t) (le_of_lt P_lt_four_mul_two_pow_128)
    exact ⟨t.val / 2 ^ 128, by norm_num; omega,
      by linarith [Nat.mod_add_div t.val (2 ^ 128)]⟩
  -- At most 4 values of `n` in `{0,1,2,3}` → at most 4 values of `t`.
  have h_target_card :
      (Finset.univ.filter (fun t : ZMod P ↦ t.val = g)).card ≤
      (Finset.image (fun n : ℕ ↦ g.val + n * 2 ^ 128)
        ({0, 1, 2, 3} : Finset ℕ)).card := by
    have h_target_card :
        Finset.image (fun t : ZMod P ↦ t.val)
          (Finset.univ.filter (fun t : ZMod P ↦ t.val = g)) ⊆
        Finset.image (fun n : ℕ ↦ g.val + n * 2 ^ 128)
          ({0, 1, 2, 3} : Finset ℕ) := by
      intro x hx; aesop
    apply le_trans _ (Finset.card_le_card h_target_card)
    rw [Finset.card_image_of_injective _
      fun x y hxy ↦ by
        simpa [ZMod.natCast_eq_zero_iff] using
          congr_arg (fun n : ℕ ↦ n : ℕ → ZMod P) hxy]
  exact h_target_card.trans ( Finset.card_image_le.trans ( by norm_num ) )

/-
For a condition involving the *difference* of two `val`s, the relevant target set
has at most 8 elements. This accounts for the fact that `val(a) - val(b)` and
`val(a - b)` may differ by `P`, giving two residue classes mod `2^128`.
-/
lemma card_diff_targets_le_8 (g : ZMod (2 ^ 128)) :
    (univ.filter (fun t : ZMod P ↦
      (t.val : ZMod (2 ^ 128)) = g ∨
      (t.val : ZMod (2 ^ 128)) = g + (P : ZMod (2 ^ 128)))).card ≤ 8 := by
  have h_card :
      (Finset.univ.filter (fun t : ZMod P ↦
        (t.val : ZMod (2 ^ 128)) = g)).card ≤ 4 ∧
      (Finset.univ.filter (fun t : ZMod P ↦
        (t.val : ZMod (2 ^ 128)) = g + (P : ZMod (2 ^ 128)))).card ≤ 4 :=
    ⟨card_val_fiber_le g, card_val_fiber_le _⟩
  simpa only [Finset.filter_or] using
    le_trans (Finset.card_union_le _ _) (add_le_add h_card.1 h_card.2)

/-
Key inclusion: the condition `Hr r m = Hr r m' + g` implies that `eval r f`
(where `f = msgPoly m - msgPoly m'`) has its val in one of two residue classes
mod `2^128`. This is because `val(a - b)` equals either `a.val - b.val` or
`a.val - b.val + P`, depending on sign.
-/
lemma Hr_eq_implies_eval_in_targets (r : ZMod P) (m m' : Message)
    (g : ZMod (2 ^ 128)) (h : Hr r m = Hr r m' + g) :
    let t := Polynomial.eval r (msgPoly m - msgPoly m')
    (t.val : ZMod (2 ^ 128)) = g ∨
    (t.val : ZMod (2 ^ 128)) = g + (P : ZMod (2 ^ 128)) := by
  by_contra h_contra
  -- Let $a = eval r (msgPoly m)$ and $b = eval r (msgPoly m')$ in $ZMod P$.
  set a := eval r (msgPoly m)
  set b := eval r (msgPoly m')
  have ht :
      (a - b).val = (a.val : ℤ) - (b.val : ℤ) ∨
      (a - b).val = (a.val : ℤ) - (b.val : ℤ) + P := by
    have ht : (a - b).val = (a.val - b.val : ℤ) % P := by
      haveI := Fact.mk (show Nat.Prime P from Fact.out)
      simp [← ZMod.val_intCast]
    have ht_cases :
        (a.val - b.val : ℤ) % P =
        if (a.val - b.val : ℤ) < 0 then
          (a.val - b.val : ℤ) + P
        else (a.val - b.val : ℤ) := by
      split_ifs
      · rw [Int.emod_eq_add_self_emod]
        rw [Int.emod_eq_of_lt] <;>
          linarith [show (a.val : ℤ) < P from mod_cast a.val_lt,
                    show (b.val : ℤ) < P from mod_cast b.val_lt]
      · rw [Int.emod_eq_of_lt] <;>
          linarith [show (a.val : ℤ) < P from mod_cast ZMod.val_lt a,
                    show (b.val : ℤ) < P from mod_cast ZMod.val_lt b]
    split_ifs at ht_cases <;> simp_all
  have h_cong : (a.val : ℤ) - (b.val : ℤ) ≡ g.val [ZMOD 2 ^ 128] := by
    have h_cong : (a.val : ZMod (2 ^ 128)) = (b.val : ZMod (2 ^ 128)) + g := by
      convert h using 1
    erw [← ZMod.intCast_eq_intCast_iff]; aesop
  have h_cong_t :
      (a - b).val ≡ g.val [ZMOD 2 ^ 128] ∨
      (a - b).val ≡ g.val + P [ZMOD 2 ^ 128] :=
    Or.imp (fun h ↦ by simpa [h] using h_cong)
           (fun h ↦ by simpa [h] using h_cong.add_right P) ht
  norm_cast at *
  simp_all only [Nat.ModEq, not_or]
  exact h_contra.1 <| by
    simpa [← ZMod.natCast_eq_natCast_iff'] using
      h_cong_t.resolve_right <| by
        simpa [← ZMod.natCast_eq_natCast_iff'] using h_contra.2

/-
The degree of `msgPoly m - msgPoly m'` is at most `max(numBlocks m, numBlocks m')`.
-/
lemma natDegree_msgPoly_sub_le (m m' : Message) :
    (msgPoly m - msgPoly m').natDegree ≤ max (numBlocks m) (numBlocks m') := by
  exact le_trans (Polynomial.natDegree_sub_le _ _)
    (max_le_max (msgPoly_natDegree_le m) (msgPoly_natDegree_le m'))

/-
**Theorem 3.3** (Bernstein 2005). For distinct messages `m, m'` of at most `L` bytes,
and any target difference `g`, the number of keys `r : ZMod P` such that
`Hr(m) = Hr(m') + g` is at most `8 · ⌈L/16⌉`.

**Proof sketch**: Let `f = msgPoly m - msgPoly m'`. By `Hr_eq_implies_eval_in_targets`,
the bad set `{r | Hr r m = Hr r m' + g}` is contained in `{r | eval r f ∈ T}` where
`T` has at most 8 elements (by `card_diff_targets_le_8`). For each `t ∈ T`,
the polynomial `f - C t` is nonzero (by `diff_poly_ne_zero`), so it has at most
`natDegree(f) ≤ ⌈L/16⌉` roots. The union bound gives `≤ 8 · ⌈L/16⌉`.
-/
theorem differential_probability_bound (m m' : Message) (hne : m ≠ m')
    (L : ℕ) (hm : m.length ≤ L) (hm' : m'.length ≤ L)
    (g : ZMod (2 ^ 128)) :
    (univ.filter (fun r : ZMod P ↦ Hr r m = Hr r m' + g)).card
      ≤ 8 * ((L + 15) / 16) := by
  -- Let `f = msgPoly m - msgPoly m'`. Define the target set:
  set f := msgPoly m - msgPoly m'
  set T := Finset.univ.filter (fun t : ZMod P ↦ t.val = g ∨ t.val = g + P)
  have h_subset :
      (Finset.univ.filter (fun r : ZMod P ↦ Hr r m = Hr r m' + g)) ⊆
      (Finset.univ.filter (fun r : ZMod P ↦ f.eval r ∈ T)) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    simp only [T, f, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Hr_eq_implies_eval_in_targets r m m' g hr
  have h_card :
      (Finset.univ.filter (fun r : ZMod P ↦ f.eval r ∈ T)).card ≤
      T.card * f.natDegree := by
    apply card_eval_mem_filter_le
    exact fun t a ↦ diff_poly_ne_zero m' m (id (Ne.symm hne)) t
  have hT_card : T.card ≤ 8 := by
    convert card_diff_targets_le_8 g using 1
  have h_deg : f.natDegree ≤ max (numBlocks m) (numBlocks m') :=
    natDegree_msgPoly_sub_le m m'
  have h_max_blocks : max (numBlocks m) (numBlocks m') ≤ (L + 15) / 16 :=
    max_le (numBlocks_le_of_length_le m L hm) (numBlocks_le_of_length_le m' L hm')
  exact le_trans (Finset.card_le_card h_subset)
    (h_card.trans (Nat.mul_le_mul hT_card (h_deg.trans h_max_blocks)))

/-- Alternative form of `differential_probability_bound` using rational ceiling `⌈(L : ℚ) / 16⌉₊`
instead of integer division `(L + 15) / 16`. The two expressions are equal. -/
theorem differential_probability_bound_ceil (m m' : Message) (hne : m ≠ m')
    (L : ℕ) (hm : m.length ≤ L) (hm' : m'.length ≤ L)
    (g : ZMod (2 ^ 128)) :
    (univ.filter (fun r : ZMod P ↦ Hr r m = Hr r m' + g)).card
      ≤ 8 * ⌈(L : ℚ) / 16⌉₊ := by
  have ceil_eq : (L + 15) / 16 = ⌈(L : ℚ) / 16⌉₊ := by
    apply le_antisymm
    · have hle : L ≤ ⌈(L : ℚ) / 16⌉₊ * 16 := by
        have h : (L : ℚ) ≤ ⌈(L : ℚ) / 16⌉₊ * 16 := by
          have := Nat.le_ceil ((L : ℚ) / 16)
          calc (L : ℚ) = (L : ℚ) / 16 * 16 := by ring
            _ ≤ ⌈(L : ℚ) / 16⌉₊ * 16 := by gcongr
        exact_mod_cast h
      omega
    · rw [Nat.ceil_le]
      have : (L : ℚ) ≤ ↑((L + 15) / 16) * 16 := by
        exact_mod_cast show L ≤ (L + 15) / 16 * 16 by omega
      linarith
  rw [← ceil_eq]
  exact differential_probability_bound m m' hne L hm hm' g

/-- **Corollary**: The differential probability for a uniformly random key from
a set of `2^106` valid keys is at most `8 ⌈ L / 16 ⌉ / 2^106`. -/
theorem differential_probability_corollary (m m' : Message) (hne : m ≠ m')
    (L : ℕ) (hm : m.length ≤ L) (hm' : m'.length ≤ L)
    (g : ZMod (2 ^ 128))
    (R : Finset (ZMod P)) :
    (R.filter (fun r ↦ Hr r m = Hr r m' + g)).card ≤ 8 * ((L + 15) / 16) := by
  calc (R.filter (fun r ↦ Hr r m = Hr r m' + g)).card
      ≤ (univ.filter (fun r : ZMod P ↦ Hr r m = Hr r m' + g)).card :=
        card_le_card (filter_subset_filter _ (subset_univ _))
    _ ≤ 8 * ((L + 15) / 16) :=
        differential_probability_bound m m' hne L hm hm' g

/-- Poly1305, restricted to messages of at most `L` bytes, is
`8 · ⌈L/16⌉ / P`-almost-Δ-universal₂ over `ZMod (2 ^ 128)`.

The key space is `ZMod P` with the uniform distribution.  The bound
`8 · ⌈L/16⌉ / P` is astronomically small in practice (e.g. ≈ 2⁻¹¹¹ for 1 MB
messages).  The proof follows from `differential_probability_bound` (Theorem 3.3):
for distinct messages the bad-key count is at most `8 · ⌈L/16⌉`, so dividing by
`|ZMod P| = P` gives the probability bound. -/
theorem almostDeltaUniversal2 (L : ℕ) :
    let ε : ℚ := (8 * ((L + 15) / 16 : ℕ) : ℚ) / (P : ℚ)
    HashFamily.almostDeltaUniversal2 ε
      (fun (r : ZMod P) (m : {m : Message // m.length ≤ L}) ↦ Hr r m.val) := by
  intro ε x y hne b
  have hneq : x.1 ≠ y.1 := fun h ↦ hne (Subtype.ext h)
  simp only [probUniform, ZMod.card]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hconv : Finset.univ.filter (fun i : ZMod P ↦ Hr i x.1 - Hr i y.1 = b) =
               Finset.univ.filter (fun i : ZMod P ↦ Hr i x.1 = Hr i y.1 + b) := by
    ext r; simp [sub_eq_iff_eq_add, add_comm]
  have hcard_eq : Fintype.card { i : ZMod P // Hr i x.1 - Hr i y.1 = b } =
                  (Finset.univ.filter (fun i : ZMod P ↦ Hr i x.1 = Hr i y.1 + b)).card := by
    rw [Fintype.card_subtype, hconv]
  rw [hcard_eq]
  exact_mod_cast differential_probability_bound x.1 y.1 hneq L x.2 y.2 b

end Poly1305
