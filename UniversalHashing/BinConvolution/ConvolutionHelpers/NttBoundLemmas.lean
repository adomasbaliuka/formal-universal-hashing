/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib.Data.ZMod.Defs
import UniversalHashing.BinConvolution.ConvolutionHelpers.MontgomeryLemmas
import UniversalHashing.BinConvolution.ConvolutionDefs

/-!
#  ── Bit-reversal
-/

/-  `addMod32` and `subMod32` preserve the `< mod32` bound. -/
theorem addmod32_lt (a b : UInt32)
    (ha : a.toNat < mod32.toNat) (hb : b.toNat < mod32.toNat) :
    (addMod32 a b).toNat < mod32.toNat := by
  rw [addmod32_correct a b ha hb]; exact Nat.mod_lt _ (by decide)

theorem submod32_lt (a b : UInt32)
    (ha : a.toNat < mod32.toNat) (hb : b.toNat < mod32.toNat) :
    (subMod32 a b).toNat < mod32.toNat := by
  rw [submod32_correct a b ha hb]; exact Nat.mod_lt _ (by decide)

/-  `toMont` preserves `< mod32` when the input is bounded. -/
theorem to_mont_lt (a : UInt32) (ha : a.toNat < mod32.toNat) :
    (toMont a).toNat < mod32.toNat := (to_mont_correct a ha).1

/-
Generalized u-bound: when a < mod64 and b < 2^32 (any UInt32).
-/
theorem mont_mul_nat_u_bound_left (a b : ℕ)
    (ha : a < mod32.toNat) (hb : b < 2 ^ 32) :
    let T := a * b
    let m := (T % 2 ^ 32 * montPprime.toNat) % 2 ^ 32
    (T + m * mod64.toNat) / 2 ^ 32 < 2 * mod64.toNat := by
      have h_bound : a * b < mod64.toNat * 2 ^ 32 := by
        gcongr
        exact ha
      exact Nat.div_lt_of_lt_mul <| by
        nlinarith [
          show (a * b % 2 ^ 32 * montPprime.toNat % 2 ^ 32) < 2 ^ 32 by
            exact Nat.mod_lt _ (by decide),
          show mod64.toNat = 3221225473 by rfl] 

/-
UInt64 product doesn't overflow when a < mod32 and b is any UInt32.
-/
theorem mont_T_toNat_left (a b : UInt32)
    (ha : a.toNat < mod32.toNat) :
    (a.toUInt64 * b.toUInt64).toNat = a.toNat * b.toNat := by
      norm_num [UInt64.toNat_mul]
      have ha32 : a.toNat ≤ 4294967295 :=
        Nat.le_of_lt_succ (lt_of_lt_of_le ha (by decide))
      have hb32 : b.toNat ≤ 4294967295 :=
        Nat.le_of_lt_succ (lt_of_lt_of_le b.toNat_lt (by decide))
      exact lt_of_le_of_lt (Nat.mul_le_mul_right _ ha32) (by linarith [hb32])

/-
Step 4 (left-bounded): u = (a*b + m*mod64) / 2^32 when only a < mod32.
-/
theorem mont_u_toNat_left (a b : UInt32)
    (ha : a.toNat < mod32.toNat) :
    let T := a.toUInt64 * b.toUInt64
    let m := T.toUInt32 * montPprime
    let mp := m.toUInt64 * mod64
    let lo := T.toUInt32.toUInt64 + mp.toUInt32.toUInt64
    let u := (T >>> 32) + (mp >>> 32) + (lo >>> 32)
    u.toNat = (a.toNat * b.toNat + m.toNat * mod64.toNat) / 2^32 := by
      have h_div_add_carry : ∀ (T_nat mp_nat : ℕ),
          T_nat < 2^64 → mp_nat < 2^64 →
          T_nat / 2^32 + mp_nat / 2^32 + (T_nat % 2^32 + mp_nat % 2^32) / 2^32 =
          (T_nat + mp_nat) / 2^32 := by omega
      convert h_div_add_carry _ _ _ _ using 1
      · simp +zetaDelta only [
            UInt64.toUInt32_mul, UInt32.toUInt32_toUInt64, UInt32.toUInt64_mul,
            UInt64.toUInt64_toUInt32, UInt64.toNat_add, UInt64.toNat_shiftRight,
            UInt64.toNat_mul, UInt32.toNat_toUInt64, Nat.reducePow, UInt64.reduceToNat,
            Nat.reduceMod, UInt64.toNat_mod, Nat.reduceDvd, Nat.mod_mod_of_dvd,
            Nat.mod_mul_mod, dvd_refl, Nat.mul_mod_mod, Nat.mod_add_mod,
            UInt32.toNat_mul] at *
        rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
        · omega
        · exact lt_of_le_of_lt
              (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))))
              (by decide)
        · have ha32 : a.toNat ≤ 4294967295 :=
            Nat.le_of_lt_succ (by linarith [show mod32.toNat = 3221225473 by rfl])
          have hb32 : b.toNat ≤ 4294967295 :=
            Nat.le_of_lt_succ (by linarith [show b.toNat < 2^32 by exact b.toNat_lt])
          exact lt_of_le_of_lt (Nat.mul_le_mul_right _ ha32) (by linarith [hb32])
        · omega
      · have ha32 : a.toNat < 2 ^ 32 := lt_of_lt_of_le ha (by decide)
        exact lt_of_le_of_lt
              (Nat.mul_le_mul_left _ (Nat.le_of_lt_succ (show b.toNat < 2 ^ 32 from
                  b.toNat_lt)))
              (by linarith [ha32])
      · exact lt_of_lt_of_le
            (Nat.mul_lt_mul_of_pos_right (UInt32.toNat_lt _) (by decide))
            (by decide)

/-
The UInt32 montMul equals montMulNat on toNat (left-bounded version).
-/
theorem mont_mul_eq_nat_left (a b : UInt32)
    (ha : a.toNat < mod32.toNat) :
    (montMul a b).toNat = montMulNat a.toNat b.toNat := by
      unfold montMulNat
      rw [montMul]
      rw [mont_cond_sub_mod]
      · rw [mont_u_toNat_left _ _ ha]
        rw [mont_m_toNat a b]
      · rw [mont_u_toNat_left a b ha]
        rw [mont_m_toNat a b]
        exact mont_mul_nat_u_bound_left _ _ ha (by exact b.toNat_lt)

/-  `montMul a b < mod32` whenever the **left** argument `a` is bounded.
    Proof: the intermediate value `u` satisfies `u < 2 * mod64`, so the
    conditional subtraction leaves the result in `[0, mod64)`. -/
theorem mont_mul_lt_of_left (a b : UInt32) (ha : a.toNat < mod32.toNat) :
    (montMul a b).toNat < mod32.toNat := by
  rw [mont_mul_eq_nat_left a b ha]
  exact mont_mul_nat_bound a.toNat b.toNat

/-
`montMul` is commutative since it only depends on the product a*b.
-/
theorem mont_mul_comm (a b : UInt32) : montMul a b = montMul b a := by
  unfold montMul; simp only [mul_comm]

/-  `montMul a b < mod32` whenever the **right** argument `b` is bounded. -/
theorem mont_mul_lt_of_right (a b : UInt32) (hb : b.toNat < mod32.toNat) :
    (montMul a b).toNat < mod32.toNat := by
  rw [mont_mul_comm]; exact mont_mul_lt_of_left b a hb

/-
Helper: `bitRevLoop` is a pure permutation and preserves the element bound.
-/
theorem bitRevLoop_bound {n : ℕ} (k i : ℕ)
    (v : Vector UInt32 n) (j : ℕ) (hv : v.all (· < mod32)) :
    (bitRevLoop k i v j).all (· < mod32) := by
      have h_bitRevLoop :
          ∀ (k : ℕ) (i : ℕ) (v : Vector UInt32 n) (j : ℕ),
          v.all (fun x => decide (x < mod32)) = true →
          (bitRevLoop k i v j).all (fun x => decide (x < mod32)) = true := by
        intro k i v j hv
        induction k generalizing i v j with
        | zero => unfold bitRevLoop; simp_all [Vector.all_eq_true]
        | succ k ih =>
          unfold bitRevLoop; simp only [Vector.all_eq_true, decide_eq_true_eq] at *
          convert ih (i + 1) _ _ _ using 1
          generalize_proofs at *; (
          intro i hi; split_ifs <;> simp_all only [Vector.getElem_set] 
          · split_ifs <;> simp_all [Vector.get]
          · split_ifs <;> simp_all +decide
          · split_ifs <;> simp_all +decide)
      generalize_proofs at *; (
      exact h_bitRevLoop k i v j hv)

/-
Setting one element of a bounded vector to a bounded value preserves the all-bound.
-/
theorem vector_all_lt_set {n : ℕ} (v : Vector UInt32 n) (i : ℕ) (h : i < n)
    (x : UInt32) (hv : v.all (· < mod32)) (hx : x.toNat < mod32.toNat) :
    (v.set i x h).all (· < mod32) := by
  simp_all only [Vector.set]
  simp_all only [Vector.all_eq_true, decide_eq_true_eq,
                Array.all_eq_true', Array.toList_set, Array.mem_def, Vector.all_mk]
  intro y hy; rw [List.mem_iff_get] at hy; obtain ⟨j, hj⟩ := hy
  by_cases hi : j = ⟨i, by aesop⟩ <;>
    simp_all only [List.get_eq_getElem, List.getElem_set, if_true]
  · exact hx
  · aesop

theorem vector_all_lt_getElem {n : ℕ} (v : Vector UInt32 n) (j : Fin n)
    (hv : v.all (· < mod32)) : (v.get j).toNat < mod32.toNat :=
  UInt32.lt_iff_toNat_lt.mp
    (by simpa [decide_eq_true_eq] using (Vector.all_eq_true.mp hv) j.val j.isLt)

/-  Helper: `radix2Pass` applies `addMod32`/`subMod32` in-place and preserves the bound. -/
theorem radix2Pass_bound {n : ℕ} (k i : ℕ) (v : Vector UInt32 n)
    (hv : v.all (· < mod32)) :
    (radix2Pass k i v).all (· < mod32) := by
  induction k generalizing i v with
  | zero => exact hv
  | succ k ih =>
    simp only [radix2Pass]
    apply ih
    split_ifs with h1 h2
    · -- Positions lo = 2*i and hi = 2*i+1 are both in bounds; apply addMod32 then subMod32.
      have helo := vector_all_lt_getElem v ⟨2 * i, h1⟩ hv
      have hehi := vector_all_lt_getElem v ⟨2 * i + 1, h2⟩ hv
      have hv1 : (v.set (2 * i) (addMod32 (v.get ⟨2 * i, h1⟩) (v.get ⟨2 * i + 1, h2⟩)) h1).all
          (· < mod32) :=
        vector_all_lt_set _ _ _ _ hv (addmod32_lt _ _ helo hehi)
      exact vector_all_lt_set _ _ _ _ hv1 (submod32_lt _ _ helo hehi)
    · exact hv
    · exact hv

/-  Helper: one pass of the outer radix-4 loop preserves the element bound.
    Each butterfly uses `addMod32`, `subMod32`, and `montMul` with the left
    argument taken from the data vector (bounded), so all outputs are < mod32. -/
/- Conditional set preserves bound. -/
theorem vector_all_lt_dite_set {n : ℕ} (v : Vector UInt32 n)
    (idx : ℕ) (x : UInt32) (hv : v.all (· < mod32))
    (hx : x.toNat < mod32.toNat) :
    (if h : idx < n then v.set idx x h else v).all (· < mod32) := by
  split_ifs with h
  · exact vector_all_lt_set _ _ _ _ hv hx
  · exact hv

/-
Getting an element from a bounded vector gives a bounded value, or 0 (which is bounded).
-/
theorem vector_get_lt_of_all {n : ℕ} (v : Vector UInt32 n)
    (idx : ℕ) (hv : v.all (· < mod32)) :
    (if h' : idx < n then v.get ⟨idx, h'⟩ else 0).toNat < mod32.toNat := by
  split_ifs with h'
  · exact UInt32.lt_iff_toNat_lt.mp (by simpa using (Vector.all_eq_true.mp hv) _ h')
  · exact by decide

theorem butterfly4_bound {n : ℕ}
    (a : Vector UInt32 n) (inverse : Bool) (roots : Vector UInt32 n)
    (s len i2 j2 : ℕ) (hv : a.all (· < mod32)) :
    (butterfly4 a inverse roots s len i2 j2).all (· < mod32) := by
      apply vector_all_lt_dite_set
      · apply vector_all_lt_dite_set
        · apply vector_all_lt_dite_set
          · apply vector_all_lt_dite_set
            · exact hv
            · apply addmod32_lt
              · apply addmod32_lt
                · exact vector_get_lt_of_all a (i2 + j2) hv
                · apply mont_mul_lt_of_left
                  exact vector_get_lt_of_all a (i2 + j2 + s) hv
              · apply mont_mul_lt_of_right
                apply addmod32_lt
                · exact vector_get_lt_of_all a (i2 + len + j2) hv
                · apply mont_mul_lt_of_left
                  apply vector_get_lt_of_all; assumption
          · apply submod32_lt
            · apply addmod32_lt
              · exact vector_get_lt_of_all a (i2 + j2) hv
              · apply mont_mul_lt_of_left
                exact vector_get_lt_of_all a (i2 + j2 + s) hv
            · apply mont_mul_lt_of_right
              apply addmod32_lt
              · exact vector_get_lt_of_all a (i2 + len + j2) hv
              · apply mont_mul_lt_of_left
                apply vector_get_lt_of_all; assumption
        · apply addmod32_lt
          · apply submod32_lt
            · apply vector_get_lt_of_all; assumption
            · apply mont_mul_lt_of_left; apply vector_get_lt_of_all; assumption
          · exact mont_mul_lt_of_right _ _ (submod32_lt _ _ (by
              exact vector_get_lt_of_all a (i2 + len + j2) hv) (by
              apply mont_mul_lt_of_left
              apply vector_get_lt_of_all; assumption))
      · apply submod32_lt
        · apply submod32_lt
          · exact vector_get_lt_of_all a (i2 + j2) hv
          · apply mont_mul_lt_of_left
            exact vector_get_lt_of_all a (i2 + j2 + s) hv
        · exact mont_mul_lt_of_right _ _ (submod32_lt _ _ (by
            exact vector_get_lt_of_all a (i2 + len + j2) hv) (by
            apply mont_mul_lt_of_left
            apply vector_get_lt_of_all; assumption))

theorem radix4Inner_bound {n : ℕ}
    (inverse : Bool) (roots : Vector UInt32 n) (s len i2 : ℕ)
    (k j2 : ℕ) (v : Vector UInt32 n) (hv : v.all (· < mod32)) :
    (radix4Inner inverse roots s len i2 k j2 v).all (· < mod32) := by
      induction k generalizing j2 v with
      | zero => exact hv
      | succ k ih => exact ih _ _ (butterfly4_bound _ _ _ _ _ _ _ hv)

theorem radix4Middle_bound {n : ℕ} (inverse : Bool) (roots : Vector UInt32 n)
    (s len : ℕ) (k b : ℕ) (v : Vector UInt32 n) (hv : v.all (· < mod32)) :
    (radix4Middle inverse roots s len k b v).all (· < mod32) := by
      convert hv using 1
      induction k generalizing b v with
      | zero => rfl
      | succ k ih =>
        convert ih (b + 1) _ _ using 1
        · rw [radix4Inner_bound inverse roots s len
            (b * 2 * len) s 0 v hv]
          exact hv
        · convert radix4Inner_bound inverse roots s len
            (b * 2 * len) s 0 v hv using 1

/-- All outputs of nttInplace are < mod32. -/
theorem ntt_inplace_output_bound {m : ℕ}
    (v : Vector UInt32 m) (inverse : Bool)
    (roots : Vector UInt32 m)
    (hv_bound : v.all (· < mod32)) :
    (nttInplace v inverse roots).all (· < mod32) := by
  unfold nttInplace
  -- Step 1: after the toMont map (forward) or identity (inverse), bound is preserved.
  have ha1 : (if !inverse then v.map toMont else v).all (· < mod32) := by
    split_ifs with h
    · rw [Vector.all_eq_true]
      intro i hi
      simp only [decide_eq_true_eq, Vector.getElem_map]
      have hvi : v[i].toNat < mod32.toNat := vector_all_lt_getElem v ⟨i, hi⟩ hv_bound
      exact UInt32.lt_iff_toNat_lt.mpr (to_mont_lt v[i] hvi)
    · exact hv_bound
  set a1 := if !inverse then v.map toMont else v with ha1_def
  -- Step 2: bitRevLoop is a permutation; bound is preserved.
  have ha2 : (bitRevLoop (m - 1) 0 a1 0).all (· < mod32) :=
    bitRevLoop_bound _ _ _ _ ha1
  set a2 := bitRevLoop (m - 1) 0 a1 0 with ha2_def
  -- Step 3: the optional radix2Pass (and its identity alternative) preserves the bound.
  set k := nttInplace.go 64 m 0
  have ha3 : (if k &&& 1 != 0 then (radix2Pass (m / 2) 0 a2, (4 : UInt64))
              else (a2, (2 : UInt64))).1.all (· < mod32) := by
    split_ifs
    · exact radix2Pass_bound _ _ _ ha2
    · exact ha2
  set a3 := (if k &&& 1 != 0 then (radix2Pass (m / 2) 0 a2, (4 : UInt64))
             else (a2, (2 : UInt64))).1
  set start := (if k &&& 1 != 0 then (radix2Pass (m / 2) 0 a2, (4 : UInt64))
                else (a2, (2 : UInt64))).2
  -- Step 4: the outer radix-4 loop preserves the bound (proved by induction via helper).
  have ha4 : (nttInplace.outerLoop inverse roots a3 start 64).all (· < mod32) := by
    suffices h : ∀ (a : Vector UInt32 m) (len : UInt64) (fuel : ℕ),
        a.all (· < mod32) → (nttInplace.outerLoop inverse roots a len fuel).all (· < mod32) from
      h a3 start 64 ha3
    intro a len fuel ha
    induction fuel generalizing a len with
    | zero => simp only [nttInplace.outerLoop, ha]
    | succ f ih =>
      simp only [nttInplace.outerLoop]
      split_ifs with hcond
      · exact ha
      · exact ih _ _ (radix4Middle_bound _ _ _ _ _ _ _ ha)
  set a4 := nttInplace.outerLoop inverse roots a3 start 64
  -- Step 5: the final inverse scaling (or identity) preserves the bound.
  split_ifs with hinv
  · rw [Vector.all_eq_true]
    intro i hi
    simp only [decide_eq_true_eq, Vector.getElem_map]
    have ha4i : a4[i].toNat < mod32.toNat := vector_all_lt_getElem a4 ⟨i, hi⟩ ha4
    exact UInt32.lt_iff_toNat_lt.mpr (mont_mul_lt_of_left a4[i] _ ha4i)
  · exact ha4

/-!
#  ── NTT forward correctness ───────────────────────────────────────────────────

Helper lemmas decompose the proof by function:
  Level 1 – arithmetic primitives in ZMod
  Level 2 – root-table correctness (ensureRoots)
  Level 3 – algorithm permutation (bitRevLoop)
  Level 4 – full forward-NTT correctness given a correct root table
The main theorem follows from levels 2 + 4.
-/

private lemma two_ne_zero_ZMod : (2 : ZMod mod32.toNat) ≠ 0 := by decide

lemma two_pow32_ne_zero_ZMod : (2 : ZMod mod32.toNat) ^ 32 ≠ 0 :=
  pow_ne_zero _ two_ne_zero_ZMod

lemma prim_root_ne_zero_ZMod : (primRoot.toNat : ZMod mod32.toNat) ≠ 0 := by decide

lemma mont_r1_ne_zero_ZMod : (montR1.toNat : ZMod mod32.toNat) ≠ 0 :=
  MONT_R1_ZMod ▸ two_pow32_ne_zero_ZMod

/-- `addMod32 a b` computes addition in `ZMod mod32.toNat`. -/
lemma addmod32_ZMod (a b : UInt32)
    (ha : a.toNat < mod32.toNat) (hb : b.toNat < mod32.toNat) :
    ((addMod32 a b).toNat : ZMod mod32.toNat) =
      (a.toNat : ZMod mod32.toNat) + b.toNat := by
  rw [addmod32_correct a b ha hb, ZMod.natCast_mod, Nat.cast_add]

/-- `subMod32 a b` computes subtraction in `ZMod mod32.toNat`. -/
lemma submod32_ZMod (a b : UInt32)
    (ha : a.toNat < mod32.toNat) (hb : b.toNat < mod32.toNat) :
    ((subMod32 a b).toNat : ZMod mod32.toNat) =
      (a.toNat : ZMod mod32.toNat) - b.toNat := by
  rw [submod32_correct a b ha hb, ZMod.natCast_mod]
  push_cast [(by omega : b.toNat ≤ a.toNat + mod32.toNat)]
  simp

/-- `montMul a b` computes `a · b · R⁻¹ mod p` in `ZMod mod32.toNat`, where R = 2^32. -/
lemma mont_mul_ZMod (a b : UInt32)
    (ha : a.toNat < mod32.toNat) (hb : b.toNat < mod32.toNat) :
    ((montMul a b).toNat : ZMod mod32.toNat) =
      (a.toNat : ZMod mod32.toNat) * b.toNat * (2 ^ 32 : ZMod mod32.toNat)⁻¹ := by
  have hcorr := (mont_mul_correct a b ha hb).2
  have h2_ne : (2 : ZMod mod32.toNat)^32 ≠ 0 := two_pow32_ne_zero_ZMod
  have h_zmod : ((montMul a b).toNat : ZMod mod32.toNat) * 2^32 =
      (a.toNat : ZMod mod32.toNat) * b.toNat := by
    have h := congr_arg (Nat.cast (R := ZMod mod32.toNat)) hcorr
    simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
    exact h
  apply mul_right_cancel₀ h2_ne
  rw [mul_assoc, inv_mul_cancel₀ h2_ne, mul_one]
  exact h_zmod

/-- `toMont a` maps `a` into the Montgomery domain: it computes `a · R mod p`
    in `ZMod mod32.toNat`, where R = 2^32 ≡ montR1 (mod p). -/
lemma to_mont_ZMod (a : UInt32) (ha : a.toNat < mod32.toNat) :
    ((toMont a).toNat : ZMod mod32.toNat) =
      (a.toNat : ZMod mod32.toNat) * (montR1.toNat : ZMod mod32.toNat) := by
  have hcorr := (to_mont_correct a ha).2
  have h2_ne : (2 : ZMod mod32.toNat)^32 ≠ 0 := two_pow32_ne_zero_ZMod
  have h_zmod : ((toMont a).toNat : ZMod mod32.toNat) * 2^32 =
      (a.toNat : ZMod mod32.toNat) * 2^64 := by
    have h := congr_arg (Nat.cast (R := ZMod mod32.toNat)) hcorr
    simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
    exact h
  have hMONT_R1 : (montR1.toNat : ZMod mod32.toNat) = 2^32 := by
    have : montR1.toNat = 2^32 % mod32.toNat := by decide
    rw [this, ZMod.natCast_mod]; norm_num
  rw [hMONT_R1]
  apply mul_right_cancel₀ h2_ne
  rw [h_zmod]; ring

