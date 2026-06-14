/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Batteries.Data.Vector.Lemmas
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Tactic.Ring.RingNF
import UniversalHashing.BinConvolution.ConvolutionHelpers.Radix4ForwardLemmas
import UniversalHashing.BinConvolution.ConvolutionDefs

/-
  Level 3g – butterfly4 inverse: structural and ZMod-level correctness.

  The inverse butterfly uses negated twiddles: instead of `roots[s+j2]` for t1 it uses
  `mod32 - roots[2*s - j2]` (when `j2 > 0`) which equals `-roots[2*s - j2]` in ZMod
  (and similarly for t2, t3). Since `mod64 = 3*2^30 + 1`, we have
  `primRoot^{(mod64-1)/2} = -1` in ZMod mod64, so the negated twiddle equals
  `ω^{(mod64-1)/len * (len - j2)} * R` where `ω = primRoot`.
-/

/-- Negation of a `UInt32 < mod32` in `ZMod mod32.toNat`:
    `(mod32 - r).toNat ≡ -r` (mod `mod32`). -/
lemma neg_root_zmod (r : UInt32) (hr : r.toNat < mod32.toNat) :
    ((mod32 - r).toNat : ZMod mod32.toNat) = -(r.toNat : ZMod mod32.toNat) := by
  have h1 : mod32.toNat = 3221225473 := by decide
  by_cases hpos : 0 < r.toNat
  · have heq : (mod32 - r).toNat = mod32.toNat - r.toNat := by
      rw [UInt32.toNat_sub]; omega
    rw [heq]
    have hle : r.toNat ≤ mod32.toNat := le_of_lt hr
    rw [Nat.cast_sub hle, ZMod.natCast_self, zero_sub]
  · push Not at hpos
    have hr_zero : r.toNat = 0 := Nat.le_zero.mp hpos
    have heq : (mod32 - r).toNat = mod32.toNat := by
      have hr_eq : r = 0 := UInt32.toNat_inj.mp (by rw [hr_zero]; rfl)
      rw [hr_eq, sub_zero]
    rw [heq, hr_zero]
    simp

/-- Key Nat arithmetic identity: when `len = 2 * s` and `2 * len ∣ m`,
    `m / len * (s - j2) + m / 2 = m / len * (len - j2)` (for `j2 < s`).
    This is what makes the inverse twiddle computation work for `t1`, `t2`. -/
lemma twiddle_neg_exp_identity (m len s j2 : ℕ)
    (hlen : len = 2 * s) (hdvd : 2 * len ∣ m) (hj2 : j2 < s) :
    m / len * (s - j2) + m / 2 = m / len * (len - j2) := by
  obtain ⟨k, hk⟩ := hdvd
  subst hk
  rw [hlen]
  have h1 : 2 * (2 * s) * k / (2 * s) = 2 * k := by
    rw [show 2 * (2 * s) * k = (2 * s) * (2 * k) by ring]
    exact Nat.mul_div_cancel_left _ (by omega : 0 < 2 * s)
  have h2 : 2 * (2 * s) * k / 2 = (2 * s) * k := by
    rw [show 2 * (2 * s) * k = 2 * ((2 * s) * k) by ring]
    exact Nat.mul_div_cancel_left _ (by omega : 0 < 2)
  rw [h1, h2]
  have hsj2 : j2 ≤ s := le_of_lt hj2
  have h2sj2 : j2 ≤ 2 * s := by omega
  rw [Nat.mul_sub, Nat.mul_sub]
  have hkj2_le1 : 2 * k * j2 ≤ 2 * k * s := Nat.mul_le_mul_left _ hsj2
  have hkj2_le2 : 2 * k * j2 ≤ 2 * k * (2 * s) := Nat.mul_le_mul_left _ h2sj2
  have hkkk : 2 * k * (2 * s) = 2 * k * s + 2 * s * k := by ring
  omega

/-- Variant Nat arithmetic identity for the `t2` twiddle (with `len' = 2*len, s' = len`):
    when `2 * len ∣ m` and `2 ∣ m`,
    `m / (2 * len) * (len - j2) + m / 2 = m / (2 * len) * (2 * len - j2)`
    for `j2 ≤ len`. -/
lemma twiddle_neg_exp_identity_t2 (m len j2 : ℕ)
    (hdvd : 2 * len ∣ m) (h2_dvd : 2 ∣ m) (hj2 : j2 ≤ len) :
    m / (2 * len) * (len - j2) + m / 2 = m / (2 * len) * (2 * len - j2) := by
  obtain ⟨k, hk⟩ := hdvd
  subst hk
  by_cases hlen_pos : len > 0
  · have h1 : 2 * len * k / (2 * len) = k :=
      Nat.mul_div_cancel_left _ (by omega : 0 < 2 * len)
    have h2 : 2 * len * k / 2 = len * k := by
      rw [show 2 * len * k = 2 * (len * k) by ring]
      exact Nat.mul_div_cancel_left _ (by omega : 0 < 2)
    rw [h1, h2, Nat.mul_sub, Nat.mul_sub]
    have h2lk : k * j2 ≤ k * (2 * len) := Nat.mul_le_mul_left _ (by omega)
    have hlk : k * j2 ≤ k * len := Nat.mul_le_mul_left _ hj2
    have h_2l : k * (2 * len) = k * len + len * k := by ring
    omega
  · push Not at hlen_pos
    obtain rfl : len = 0 := by omega
    simp_all

/-- Key Nat arithmetic identity for the `t3` twiddle: when `len = 2 * s` and `2 * len ∣ m`,
    `m / (2 * len) * (s - j2) + m / 2 = m / (2 * len) * (2 * len - s - j2)`. -/
lemma twiddle_neg_exp_identity_t3 (m len s j2 : ℕ)
    (hlen : len = 2 * s) (hdvd : 2 * len ∣ m) (hj2 : j2 < s) :
    m / (2 * len) * (s - j2) + m / 2 = m / (2 * len) * (2 * len - s - j2) := by
  obtain ⟨k, hk⟩ := hdvd
  subst hk
  rw [hlen]
  have h1 : 2 * (2 * s) * k / (2 * (2 * s)) = k :=
    Nat.mul_div_cancel_left _ (by omega : 0 < 2 * (2 * s))
  have h2 : 2 * (2 * s) * k / 2 = (2 * s) * k := by
    rw [show 2 * (2 * s) * k = 2 * ((2 * s) * k) by ring]
    exact Nat.mul_div_cancel_left _ (by omega : 0 < 2)
  rw [h1, h2]
  have hsj2 : j2 ≤ s := le_of_lt hj2
  have h3 : 2 * (2 * s) - s - j2 = 3 * s - j2 := by omega
  rw [h3, Nat.mul_sub k s j2, Nat.mul_sub k (3 * s) j2]
  have hkj2 : k * j2 ≤ k * s := Nat.mul_le_mul_left _ hsj2
  have hk3s : k * j2 ≤ k * (3 * s) := Nat.mul_le_mul_left _ (by omega)
  have h_k3s : k * (3 * s) = k * s + 2 * s * k := by ring
  omega

-- Shared expansion: unfolds butterfly4 (inverse) into the explicit Vector.set chain once,
-- absorbing the expensive simp only [butterfly4, ...] cost for all four getElem_posX lemmas.
private lemma butterfly4_inverse_expand {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N) :
    butterfly4 a true roots s len i2 j2 =
      let t1 : UInt32 :=
        if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0 else roots.getD s 0
      let t2 : UInt32 :=
        if j2 > 0 then mod32 - roots.getD (2 * len - j2) 0 else roots.getD len 0
      let t3 : UInt32 := mod32 - roots.getD (2 * len - j2 - s) 0
      let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
      let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
      let P  := addMod32 (a[i2 + j2]'hbnd0) aB
      let Rv := addMod32 (a[i2 + len + j2]'hbnd2) aD
      let Q  := subMod32 (a[i2 + j2]'hbnd0) aB
      let Sv := subMod32 (a[i2 + len + j2]'hbnd2) aD
      let t2R := montMul t2 Rv
      let t3S := montMul t3 Sv
      ((((a.set (i2 + j2) (addMod32 P t2R) hbnd0).set
               (i2 + len + j2) (subMod32 P t2R) hbnd2).set
               (i2 + j2 + s) (addMod32 Q t3S) hbnd1).set
               (i2 + len + j2 + s) (subMod32 Q t3S) hbnd3) := by
  simp only [butterfly4, Bool.not_true, Bool.false_eq_true, ite_false,
    dif_pos hbnd0, dif_pos hbnd1, dif_pos hbnd2, dif_pos hbnd3,
    Vector.get_eq_getElem]

-- Structural: what `butterfly4` returns at position `(i2 + j2)` for `inverse=true`.
lemma butterfly4_inverse_getElem_pos0 {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (hne10 : i2 + j2 + s ≠ i2 + j2)
    (hne20 : i2 + len + j2 ≠ i2 + j2)
    (hne30 : i2 + len + j2 + s ≠ i2 + j2) :
    let t1 : UInt32 :=
      if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0 else roots.getD s 0
    let t2 : UInt32 :=
      if j2 > 0 then mod32 - roots.getD (2 * len - j2) 0 else roots.getD len 0
    let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
    let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
    let P := addMod32 (a[i2 + j2]'hbnd0) aB
    let R_v := addMod32 (a[i2 + len + j2]'hbnd2) aD
    let t2R := montMul t2 R_v
    (butterfly4 a true roots s len i2 j2)[i2 + j2]'hbnd0 = addMod32 P t2R := by
  rw [butterfly4_inverse_expand roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3]
  simp only []
  rw [Vector.getElem_set, if_neg hne30, Vector.getElem_set, if_neg hne10,
      Vector.getElem_set, if_neg hne20, Vector.getElem_set_self]

-- Structural: what `butterfly4` returns at position `(i2 + len + j2)` for `inverse=true`.
lemma butterfly4_inverse_getElem_pos2 {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (hne12 : i2 + j2 + s ≠ i2 + len + j2)
    (hne32 : i2 + len + j2 + s ≠ i2 + len + j2) :
    let t1 : UInt32 :=
      if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0 else roots.getD s 0
    let t2 : UInt32 :=
      if j2 > 0 then mod32 - roots.getD (2 * len - j2) 0 else roots.getD len 0
    let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
    let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
    let P := addMod32 (a[i2 + j2]'hbnd0) aB
    let R_v := addMod32 (a[i2 + len + j2]'hbnd2) aD
    let t2R := montMul t2 R_v
    (butterfly4 a true roots s len i2 j2)[i2 + len + j2]'hbnd2 = subMod32 P t2R := by
  rw [butterfly4_inverse_expand roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3]
  simp only []
  rw [Vector.getElem_set, if_neg hne32, Vector.getElem_set, if_neg hne12,
      Vector.getElem_set_self]

-- Structural: what `butterfly4` returns at position `(i2 + j2 + s)` for `inverse=true`.
lemma butterfly4_inverse_getElem_pos1 {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N)
    (hne31 : i2 + len + j2 + s ≠ i2 + j2 + s) :
    let t1 : UInt32 :=
      if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0 else roots.getD s 0
    let t3 : UInt32 := mod32 - roots.getD (2 * len - j2 - s) 0
    let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
    let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
    let Q := subMod32 (a[i2 + j2]'hbnd0) aB
    let S_v := subMod32 (a[i2 + len + j2]'hbnd2) aD
    let t3S := montMul t3 S_v
    (butterfly4 a true roots s len i2 j2)[i2 + j2 + s]'hbnd1 = addMod32 Q t3S := by
  rw [butterfly4_inverse_expand roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3]
  simp only []
  rw [Vector.getElem_set, if_neg hne31, Vector.getElem_set_self]

-- Structural: what `butterfly4` returns at position `(i2 + len + j2 + s)` for `inverse=true`.
lemma butterfly4_inverse_getElem_pos3 {N : ℕ}
    (roots a : Vector UInt32 N) (s len i2 j2 : ℕ)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N) :
    let t1 : UInt32 :=
      if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0 else roots.getD s 0
    let t3 : UInt32 := mod32 - roots.getD (2 * len - j2 - s) 0
    let aB := montMul (a[i2 + j2 + s]'hbnd1) t1
    let aD := montMul (a[i2 + len + j2 + s]'hbnd3) t1
    let Q := subMod32 (a[i2 + j2]'hbnd0) aB
    let S_v := subMod32 (a[i2 + len + j2]'hbnd2) aD
    let t3S := montMul t3 S_v
    (butterfly4 a true roots s len i2 j2)[i2 + len + j2 + s]'hbnd3 = subMod32 Q t3S := by
  rw [butterfly4_inverse_expand roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3]
  simp only []
  rw [Vector.getElem_set_self]

/-- Helper: a root value at a valid NTT index is `< mod32`, and its negation `mod32 - r`
    is also `< mod32` (because ω^e * R is nonzero in `ZMod mod32.toNat`). -/
lemma inverse_twiddle_bound {N : ℕ} (roots : Vector UInt32 N)
    (hroots : ntt_roots_correct N roots) (hroots_bnd : roots.all (· < mod32))
    (len' j' : ℕ) (h2 : 2 ≤ len') (hdvd : len' ∣ N) (hj' : j' < len' / 2)
    (idx : ℕ) (hidx : idx < N) (heq : idx = len' / 2 + j') :
    (mod32 - roots[idx]'hidx).toNat < mod32.toNat := by
  have hroot_lt : (roots[idx]'hidx).toNat < mod32.toNat := by
    rw [Vector.all_eq_true] at hroots_bnd
    exact UInt32.lt_iff_toNat_lt.mp (by simpa using hroots_bnd _ hidx)
  have hroot_val := ntt_roots_correct_at roots hroots len' j' idx h2 hdvd hj' hidx heq
  have hne : ((roots[idx]'hidx).toNat : ZMod mod32.toNat) ≠ 0 := by
    rw [hroot_val]
    have hp : (primRoot.toNat : ZMod mod32.toNat) ≠ 0 := prim_root_ne_zero_ZMod
    have hR : (montR1.toNat : ZMod mod32.toNat) ≠ 0 := mont_r1_ne_zero_ZMod
    exact mul_ne_zero (pow_ne_zero _ hp) hR
  have hpos : (roots[idx]'hidx).toNat > 0 := by
    by_contra h
    push Not at h
    have : (roots[idx]'hidx).toNat = 0 := Nat.le_zero.mp h
    rw [this] at hne; simp at hne
  have h1 : mod32.toNat = 3221225473 := by decide
  rw [UInt32.toNat_sub]
  omega

-- Helper: ZMod value of inverse `t1` twiddle.
lemma inverse_t1_zmod {N : ℕ} (roots : Vector UInt32 N)
    (hroots : ntt_roots_correct N roots) (hroots_bnd : roots.all (· < mod32))
    (s len j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hN_dvd : N ∣ mod64.toNat - 1)
    (hj2 : j2 < s)
    (h_idx_pos : 2 * s - j2 < N)
    (h_idx_pos_eq : 2 * s - j2 = s + (s - j2))
    (h_idx_zero : s < N) :
    ((if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0
      else roots.getD s 0).toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2))
        * (montR1.toNat : ZMod mod32.toNat) := by
  by_cases hj2_pos : j2 > 0
  · rw [if_pos hj2_pos]
    rw [vector_getD_eq_getElem roots _ h_idx_pos 0]
    have hroots_bnd_at : (roots[2 * s - j2]'h_idx_pos).toNat < mod32.toNat := by
      rw [Vector.all_eq_true] at hroots_bnd
      exact UInt32.lt_iff_toNat_lt.mp (by simpa using hroots_bnd _ h_idx_pos)
    rw [neg_root_zmod _ hroots_bnd_at]
    have h_root_val : ((roots[2 * s - j2]'h_idx_pos).toNat : ZMod mod32.toNat) =
        (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (s - j2))
          * (montR1.toNat : ZMod mod32.toNat) := by
      apply ntt_roots_correct_at roots hroots len (s - j2) (2 * s - j2)
      · omega
      · exact dvd_of_mul_left_dvd hlen_dvd
      · omega
      · rw [hlen,
          show 2 * s / 2 = s from Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]
        omega
    rw [h_root_val]
    have h_neg : -((primRoot.toNat : ZMod mod32.toNat) ^
          ((mod64.toNat - 1) / len * (s - j2)) * (montR1.toNat : ZMod mod32.toNat))
        = (primRoot.toNat : ZMod mod32.toNat) ^
          ((mod64.toNat - 1) / len * (s - j2) + (mod64.toNat - 1) / 2)
          * (montR1.toNat : ZMod mod32.toNat) := by
      rw [pow_add, prim_root_half_eq_neg_one]; ring
    rw [h_neg, twiddle_neg_exp_identity (mod64.toNat - 1) len s j2 hlen
      (dvd_trans hlen_dvd hN_dvd) hj2]
  · rw [if_neg hj2_pos]
    have hj2_zero : j2 = 0 := by omega
    rw [vector_getD_eq_getElem roots _ h_idx_zero 0]
    have h_root_val : ((roots[s]'h_idx_zero).toNat : ZMod mod32.toNat) =
        (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * 0)
          * (montR1.toNat : ZMod mod32.toNat) := by
      apply ntt_roots_correct_at roots hroots len 0 s
      · omega
      · exact dvd_of_mul_left_dvd hlen_dvd
      · omega
      · rw [hlen,
          show 2 * s / 2 = s from Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]
        omega
    rw [h_root_val, hj2_zero]
    have h_len_dvd : len ∣ mod64.toNat - 1 :=
      dvd_trans (dvd_of_mul_left_dvd hlen_dvd) hN_dvd
    have hprim_pow : (primRoot.toNat : ZMod mod32.toNat) ^ (mod64.toNat - 1) = 1 := by
      rw [mod32_eq_mod]; exact ZMod.pow_card_sub_one_eq_one prim_root_ne_zero_ZMod
    rw [(by omega : len - 0 = len), mul_zero, pow_zero,
        (Nat.div_mul_cancel h_len_dvd : (mod64.toNat - 1) / len * len = mod64.toNat - 1),
        hprim_pow, one_mul]

-- Helper: ZMod value of inverse `t2` twiddle.
lemma inverse_t2_zmod {N : ℕ} (roots : Vector UInt32 N)
    (hroots : ntt_roots_correct N roots) (hroots_bnd : roots.all (· < mod32))
    (s len j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hN_dvd : N ∣ mod64.toNat - 1)
    (hj2 : j2 < s)
    (h_idx_pos : j2 > 0 → 2 * len - j2 < N)
    (h_idx_pos_eq : 2 * len - j2 = len + (len - j2))
    (h_idx_zero : len < N) :
    ((if j2 > 0 then mod32 - roots.getD (2 * len - j2) 0
      else roots.getD len 0).toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - j2)) * (montR1.toNat : ZMod mod32.toNat) := by
  have hlen_pos : len > 0 := by omega
  by_cases hj2_pos : j2 > 0
  · rw [if_pos hj2_pos]
    have h_idx_pos' := h_idx_pos hj2_pos
    rw [vector_getD_eq_getElem roots _ h_idx_pos' 0]
    have hroots_bnd_at : (roots[2 * len - j2]'h_idx_pos').toNat < mod32.toNat := by
      rw [Vector.all_eq_true] at hroots_bnd
      exact UInt32.lt_iff_toNat_lt.mp (by simpa using hroots_bnd _ h_idx_pos')
    rw [neg_root_zmod _ hroots_bnd_at]
    have h_root_val : ((roots[2 * len - j2]'h_idx_pos').toNat : ZMod mod32.toNat) =
        (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * (len - j2))
          * (montR1.toNat : ZMod mod32.toNat) := by
      apply ntt_roots_correct_at roots hroots (2 * len) (len - j2) (2 * len - j2)
      · omega
      · exact hlen_dvd
      · omega
      · rw [show 2 * len / 2 = len from
              Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]
        omega
    rw [h_root_val]
    have h_neg : -((primRoot.toNat : ZMod mod32.toNat) ^
          ((mod64.toNat - 1) / (2 * len) * (len - j2))
          * (montR1.toNat : ZMod mod32.toNat))
        = (primRoot.toNat : ZMod mod32.toNat) ^
          ((mod64.toNat - 1) / (2 * len) * (len - j2) + (mod64.toNat - 1) / 2)
          * (montR1.toNat : ZMod mod32.toNat) := by
      rw [pow_add, prim_root_half_eq_neg_one]; ring
    rw [h_neg, twiddle_neg_exp_identity_t2 (mod64.toNat - 1) len j2
      (dvd_trans hlen_dvd hN_dvd) (by decide) (by omega)]
  · rw [if_neg hj2_pos]
    have hj2_zero : j2 = 0 := by omega
    rw [vector_getD_eq_getElem roots _ h_idx_zero 0]
    have h_root_val : ((roots[len]'h_idx_zero).toNat : ZMod mod32.toNat) =
        (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * 0)
          * (montR1.toNat : ZMod mod32.toNat) := by
      apply ntt_roots_correct_at roots hroots (2 * len) 0 len
      · omega
      · exact hlen_dvd
      · omega
      · rw [show 2 * len / 2 = len from
              Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]
        omega
    rw [h_root_val, hj2_zero]
    have h_dvd : 2 * len ∣ mod64.toNat - 1 := dvd_trans hlen_dvd hN_dvd
    have hprim_pow : (primRoot.toNat : ZMod mod32.toNat) ^ (mod64.toNat - 1) = 1 := by
      rw [mod32_eq_mod]; exact ZMod.pow_card_sub_one_eq_one prim_root_ne_zero_ZMod
    rw [(by omega : 2 * len - 0 = 2 * len), mul_zero, pow_zero,
        (Nat.div_mul_cancel h_dvd : (mod64.toNat - 1) / (2 * len) * (2 * len) = mod64.toNat - 1),
        hprim_pow, one_mul]

-- Helper: ZMod value of inverse `t3` twiddle (always negated, no j2 case split).
lemma inverse_t3_zmod {N : ℕ} (roots : Vector UInt32 N)
    (hroots : ntt_roots_correct N roots) (hroots_bnd : roots.all (· < mod32))
    (s len j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hN_dvd : N ∣ mod64.toNat - 1)
    (hj2 : j2 < s)
    (h_idx : 2 * len - j2 - s < N)
    (h_idx_eq : 2 * len - j2 - s = len + (s - j2)) :
    ((mod32 - roots.getD (2 * len - j2 - s) 0).toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - s - j2)) * (montR1.toNat : ZMod mod32.toNat) := by
  rw [vector_getD_eq_getElem roots _ h_idx 0]
  have hroots_bnd_at : (roots[2 * len - j2 - s]'h_idx).toNat < mod32.toNat := by
    rw [Vector.all_eq_true] at hroots_bnd
    exact UInt32.lt_iff_toNat_lt.mp (by simpa using hroots_bnd _ h_idx)
  rw [neg_root_zmod _ hroots_bnd_at]
  have hlen_pos : len > 0 := by omega
  have h_root_val : ((roots[2 * len - j2 - s]'h_idx).toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * (s - j2))
        * (montR1.toNat : ZMod mod32.toNat) := by
    apply ntt_roots_correct_at roots hroots (2 * len) (s - j2) (2 * len - j2 - s)
    · omega
    · exact hlen_dvd
    · rw [show 2 * len / 2 = len from
            Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]
      omega
    · rw [show 2 * len / 2 = len from
            Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]
      omega
  rw [h_root_val]
  have h_neg : -((primRoot.toNat : ZMod mod32.toNat) ^
        ((mod64.toNat - 1) / (2 * len) * (s - j2))
        * (montR1.toNat : ZMod mod32.toNat))
      = (primRoot.toNat : ZMod mod32.toNat) ^
        ((mod64.toNat - 1) / (2 * len) * (s - j2) + (mod64.toNat - 1) / 2)
        * (montR1.toNat : ZMod mod32.toNat) := by
    rw [pow_add, prim_root_half_eq_neg_one]; ring
  rw [h_neg, twiddle_neg_exp_identity_t3 (mod64.toNat - 1) len s j2
    hlen (dvd_trans hlen_dvd hN_dvd) hj2]

/-- Helper: bound on inverse t1 value: `t1.toNat < mod32.toNat`. -/
lemma inverse_t1_bound {N : ℕ} (roots : Vector UInt32 N)
    (hroots : ntt_roots_correct N roots) (hroots_bnd : roots.all (· < mod32))
    (s len j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N)
    (hj2 : j2 < s)
    (h_idx_pos : 2 * s - j2 < N)
    (h_idx_pos_eq : 2 * s - j2 = s + (s - j2))
    (h_idx_zero : s < N) :
    (if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0
      else roots.getD s 0).toNat < mod32.toNat := by
  by_cases hj2_pos : j2 > 0
  · rw [if_pos hj2_pos]
    rw [vector_getD_eq_getElem roots _ h_idx_pos 0]
    apply inverse_twiddle_bound roots hroots hroots_bnd len (s - j2)
      (by omega) (dvd_of_mul_left_dvd hlen_dvd) (by omega) _ h_idx_pos
    rw [hlen,
      show 2 * s / 2 = s from Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]
    omega
  · rw [if_neg hj2_pos]
    rw [vector_getD_eq_getElem roots _ h_idx_zero 0]
    rw [Vector.all_eq_true] at hroots_bnd
    exact UInt32.lt_iff_toNat_lt.mp (by simpa using hroots_bnd _ h_idx_zero)

/-- Helper: bound on inverse t2 value: `t2.toNat < mod32.toNat`. -/
lemma inverse_t2_bound {N : ℕ} (roots : Vector UInt32 N)
    (hroots : ntt_roots_correct N roots) (hroots_bnd : roots.all (· < mod32))
    (len j2 : ℕ) (hlen_pos : len > 0)
    (hlen_dvd : 2 * len ∣ N)
    (hj2 : j2 < len)
    (h_idx_pos : j2 > 0 → 2 * len - j2 < N)
    (h_idx_pos_eq : 2 * len - j2 = len + (len - j2))
    (h_idx_zero : len < N) :
    (if j2 > 0 then mod32 - roots.getD (2 * len - j2) 0
      else roots.getD len 0).toNat < mod32.toNat := by
  by_cases hj2_pos : j2 > 0
  · rw [if_pos hj2_pos]
    have h_idx_pos' := h_idx_pos hj2_pos
    rw [vector_getD_eq_getElem roots _ h_idx_pos' 0]
    apply inverse_twiddle_bound roots hroots hroots_bnd (2 * len) (len - j2)
      (by omega) hlen_dvd _ _ h_idx_pos'
    · rw [show 2 * len / 2 = len from
        Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]; omega
    · rw [show 2 * len / 2 = len from
        Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]; omega
  · rw [if_neg hj2_pos]
    rw [vector_getD_eq_getElem roots _ h_idx_zero 0]
    rw [Vector.all_eq_true] at hroots_bnd
    exact UInt32.lt_iff_toNat_lt.mp (by simpa using hroots_bnd _ h_idx_zero)

/-- Helper: bound on inverse t3 value: `t3.toNat < mod32.toNat`. -/
lemma inverse_t3_bound {N : ℕ} (roots : Vector UInt32 N)
    (hroots : ntt_roots_correct N roots) (hroots_bnd : roots.all (· < mod32))
    (s len j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N)
    (hj2 : j2 < s)
    (h_idx : 2 * len - j2 - s < N)
    (h_idx_eq : 2 * len - j2 - s = len + (s - j2)) :
    (mod32 - roots.getD (2 * len - j2 - s) 0).toNat < mod32.toNat := by
  rw [vector_getD_eq_getElem roots _ h_idx 0]
  have hlen_pos : len > 0 := by omega
  apply inverse_twiddle_bound roots hroots hroots_bnd (2 * len) (s - j2)
    (by omega) hlen_dvd _ _ h_idx
  · rw [show 2 * len / 2 = len from
      Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]; omega
  · rw [show 2 * len / 2 = len from
      Nat.mul_div_cancel_left _ (by norm_num : (2 : ℕ) > 0)]; omega

private lemma uint64_two_mul_sub (x j2 : UInt64)
    (hj2 : j2.toNat < x.toNat) (h2x : 2 * x.toNat < 2 ^ 64) :
    (2 * x - j2).toNat = x.toNat + (x.toNat - j2.toNat) := by
  rw [UInt64.toNat_sub, UInt64.toNat_mul]
  have h2 : (2 : UInt64).toNat = 2 := by decide
  rw [h2, Nat.mod_eq_of_lt h2x]
  rw [show 2 ^ 64 - j2.toNat + 2 * x.toNat = 2 ^ 64 + (x.toNat + (x.toNat - j2.toNat)) by omega]
  rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

-- The ZMod correctness proof for inverse butterfly4 at position 0 requires many rewrites.
lemma butterfly4_inverse_ZMod_pos0 {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hN_dvd : N ∣ mod64.toNat - 1)
    (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N) :
    ((butterfly4 a true roots s len i2 j2)[i2 + j2]'hbnd0).toNat =
    (((a[i2 + j2]'hbnd0).toNat : ZMod mod32.toNat) +
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2)) *
        (a[i2 + j2 + s]'hbnd1).toNat +
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - j2)) *
        ((a[i2 + len + j2]'hbnd2).toNat +
          (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2)) *
            (a[i2 + len + j2 + s]'hbnd3).toNat) : ZMod mod32.toNat) := by
  have hs_pos : s > 0 := by omega
  have hlen_pos : len > 0 := by omega
  have hN_pos : N > 0 := by omega
  have h2len_le : 2 * len ≤ N := Nat.le_of_dvd hN_pos hlen_dvd
  have h_idx_2s_minus : 2 * s - j2 < N := by omega
  have h_idx_2s_minus_eq : 2 * s - j2 = s + (s - j2) := by omega
  have h_idx_2len_minus_eq : 2 * len - j2 = len + (len - j2) := by omega
  have h_idx_s : s < N := by omega
  have h_idx_len : len < N := by omega
  have hne10 : i2 + j2 + s ≠ i2 + j2 := by omega
  have hne20 : i2 + len + j2 ≠ i2 + j2 := by omega
  have hne30 : i2 + len + j2 + s ≠ i2 + j2 := by omega
  rw [butterfly4_inverse_getElem_pos0 roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3 hne10 hne20 hne30]
  set t1 : UInt32 :=
    if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0 else roots.getD s 0 with ht1_def
  set t2 : UInt32 :=
    if j2 > 0 then mod32 - roots.getD (2 * len - j2) 0 else roots.getD len 0 with ht2_def
  have ht1_bnd : t1.toNat < mod32.toNat := by
    rw [ht1_def]
    exact inverse_t1_bound roots hroots hroots_bnd s len j2 hlen hlen_dvd hj2
      h_idx_2s_minus h_idx_2s_minus_eq h_idx_s
  have h_idx_2len_minus_cond : j2 > 0 → 2 * len - j2 < N := by intro; omega
  have ht2_bnd : t2.toNat < mod32.toNat := by
    rw [ht2_def]
    exact inverse_t2_bound roots hroots hroots_bnd len j2 hlen_pos hlen_dvd (by omega)
      h_idx_2len_minus_cond h_idx_2len_minus_eq h_idx_len
  have ht1_zmod : (t1.toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2))
        * (montR1.toNat : ZMod mod32.toNat) := by
    rw [ht1_def]
    exact inverse_t1_zmod roots hroots hroots_bnd s len j2 hlen hlen_dvd hN_dvd hj2
      h_idx_2s_minus h_idx_2s_minus_eq h_idx_s
  have ht2_zmod : (t2.toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - j2)) * (montR1.toNat : ZMod mod32.toNat) := by
    rw [ht2_def]
    exact inverse_t2_zmod roots hroots hroots_bnd s len j2 hlen hlen_dvd hN_dvd hj2
      h_idx_2len_minus_cond h_idx_2len_minus_eq h_idx_len
  have h_a_all : ∀ idx (hidx : idx < N), (a[idx]'hidx).toNat < mod32.toNat := by
    rw [Vector.all_eq_true] at ha
    intro idx hidx
    exact UInt32.lt_iff_toNat_lt.mp (by simpa using ha _ hidx)
  have ha0 := h_a_all _ hbnd0
  have ha1 := h_a_all _ hbnd1
  have ha2 := h_a_all _ hbnd2
  have ha3 := h_a_all _ hbnd3
  have h_mont_a1_t1 := mont_mul_lt_of_left (a[i2 + j2 + s]'hbnd1) t1 ha1
  have h_mont_a3_t1 := mont_mul_lt_of_left (a[i2 + len + j2 + s]'hbnd3) t1 ha3
  have h_P_bnd := addmod32_lt _ _ ha0 h_mont_a1_t1
  have h_R_bnd := addmod32_lt _ _ ha2 h_mont_a3_t1
  have h_t2R_bnd := mont_mul_lt_of_right t2 _ h_R_bnd
  rw [addmod32_ZMod _ _ h_P_bnd h_t2R_bnd,
      addmod32_ZMod _ _ ha0 h_mont_a1_t1,
      mont_mul_ZMod _ _ ha1 ht1_bnd,
      mont_mul_ZMod _ _ ht2_bnd h_R_bnd,
      addmod32_ZMod _ _ ha2 h_mont_a3_t1,
      mont_mul_ZMod _ _ ha3 ht1_bnd,
      ht1_zmod, ht2_zmod,
      MONT_R1_ZMod]
  simp only [mul_assoc, mul_inv_cancel₀ two_pow32_ne_zero_ZMod, mul_one,
    mul_comm ((2 : ZMod mod32.toNat) ^ 32) _]
  ring

-- The ZMod correctness proof for inverse butterfly4 at position 2 requires many rewrites.
lemma butterfly4_inverse_ZMod_pos2 {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hN_dvd : N ∣ mod64.toNat - 1)
    (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N) :
    ((butterfly4 a true roots s len i2 j2)[i2 + len + j2]'hbnd2).toNat =
    (((a[i2 + j2]'hbnd0).toNat : ZMod mod32.toNat) +
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2)) *
        (a[i2 + j2 + s]'hbnd1).toNat -
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - j2)) *
        ((a[i2 + len + j2]'hbnd2).toNat +
          (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2)) *
            (a[i2 + len + j2 + s]'hbnd3).toNat) : ZMod mod32.toNat) := by
  have hs_pos : s > 0 := by omega
  have hlen_pos : len > 0 := by omega
  have hN_pos : N > 0 := by omega
  have h2len_le : 2 * len ≤ N := Nat.le_of_dvd hN_pos hlen_dvd
  have h_idx_2s_minus : 2 * s - j2 < N := by omega
  have h_idx_2s_minus_eq : 2 * s - j2 = s + (s - j2) := by omega
  have h_idx_2len_minus_eq : 2 * len - j2 = len + (len - j2) := by omega
  have h_idx_2len_minus_cond : j2 > 0 → 2 * len - j2 < N := by intro; omega
  have h_idx_s : s < N := by omega
  have h_idx_len : len < N := by omega
  have hne12 : i2 + j2 + s ≠ i2 + len + j2 := by omega
  have hne32 : i2 + len + j2 + s ≠ i2 + len + j2 := by omega
  rw [butterfly4_inverse_getElem_pos2 roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3 hne12 hne32]
  set t1 : UInt32 :=
    if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0 else roots.getD s 0 with ht1_def
  set t2 : UInt32 :=
    if j2 > 0 then mod32 - roots.getD (2 * len - j2) 0 else roots.getD len 0 with ht2_def
  have ht1_bnd : t1.toNat < mod32.toNat := by
    rw [ht1_def]
    exact inverse_t1_bound roots hroots hroots_bnd s len j2 hlen hlen_dvd hj2
      h_idx_2s_minus h_idx_2s_minus_eq h_idx_s
  have ht2_bnd : t2.toNat < mod32.toNat := by
    rw [ht2_def]
    exact inverse_t2_bound roots hroots hroots_bnd len j2 hlen_pos hlen_dvd (by omega)
      h_idx_2len_minus_cond h_idx_2len_minus_eq h_idx_len
  have ht1_zmod : (t1.toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2))
        * (montR1.toNat : ZMod mod32.toNat) := by
    rw [ht1_def]
    exact inverse_t1_zmod roots hroots hroots_bnd s len j2 hlen hlen_dvd hN_dvd hj2
      h_idx_2s_minus h_idx_2s_minus_eq h_idx_s
  have ht2_zmod : (t2.toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - j2)) * (montR1.toNat : ZMod mod32.toNat) := by
    rw [ht2_def]
    exact inverse_t2_zmod roots hroots hroots_bnd s len j2 hlen hlen_dvd hN_dvd hj2
      h_idx_2len_minus_cond h_idx_2len_minus_eq h_idx_len
  have h_a_all : ∀ idx (hidx : idx < N), (a[idx]'hidx).toNat < mod32.toNat := by
    rw [Vector.all_eq_true] at ha
    intro idx hidx
    exact UInt32.lt_iff_toNat_lt.mp (by simpa using ha _ hidx)
  have ha0 := h_a_all _ hbnd0
  have ha1 := h_a_all _ hbnd1
  have ha2 := h_a_all _ hbnd2
  have ha3 := h_a_all _ hbnd3
  have h_mont_a1_t1 := mont_mul_lt_of_left (a[i2 + j2 + s]'hbnd1) t1 ha1
  have h_mont_a3_t1 := mont_mul_lt_of_left (a[i2 + len + j2 + s]'hbnd3) t1 ha3
  have h_P_bnd := addmod32_lt _ _ ha0 h_mont_a1_t1
  have h_R_bnd := addmod32_lt _ _ ha2 h_mont_a3_t1
  have h_t2R_bnd := mont_mul_lt_of_right t2 _ h_R_bnd
  rw [submod32_ZMod _ _ h_P_bnd h_t2R_bnd,
      addmod32_ZMod _ _ ha0 h_mont_a1_t1,
      mont_mul_ZMod _ _ ha1 ht1_bnd,
      mont_mul_ZMod _ _ ht2_bnd h_R_bnd,
      addmod32_ZMod _ _ ha2 h_mont_a3_t1,
      mont_mul_ZMod _ _ ha3 ht1_bnd,
      ht1_zmod, ht2_zmod,
      MONT_R1_ZMod]
  simp only [mul_assoc, mul_inv_cancel₀ two_pow32_ne_zero_ZMod, mul_one,
    mul_comm ((2 : ZMod mod32.toNat) ^ 32) _]
  ring

-- The ZMod correctness proof for inverse butterfly4 at position 1 requires many rewrites.
lemma butterfly4_inverse_ZMod_pos1 {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hN_dvd : N ∣ mod64.toNat - 1)
    (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N) :
    ((butterfly4 a true roots s len i2 j2)[i2 + j2 + s]'hbnd1).toNat =
    (((a[i2 + j2]'hbnd0).toNat : ZMod mod32.toNat) -
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2)) *
        (a[i2 + j2 + s]'hbnd1).toNat +
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - s - j2)) *
        ((a[i2 + len + j2]'hbnd2).toNat -
          (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2)) *
            (a[i2 + len + j2 + s]'hbnd3).toNat) : ZMod mod32.toNat) := by
  have hs_pos : s > 0 := by omega
  have hlen_pos : len > 0 := by omega
  have hN_pos : N > 0 := by omega
  have h2len_le : 2 * len ≤ N := Nat.le_of_dvd hN_pos hlen_dvd
  have h_idx_2s_minus : 2 * s - j2 < N := by omega
  have h_idx_2s_minus_eq : 2 * s - j2 = s + (s - j2) := by omega
  have h_idx_2len_minus_s_eq : 2 * len - j2 - s = len + (s - j2) := by omega
  have h_idx_2len_minus_s : 2 * len - j2 - s < N := by omega
  have h_idx_s : s < N := by omega
  have hne31 : i2 + len + j2 + s ≠ i2 + j2 + s := by omega
  rw [butterfly4_inverse_getElem_pos1 roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3 hne31]
  set t1 : UInt32 :=
    if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0 else roots.getD s 0 with ht1_def
  set t3 : UInt32 := mod32 - roots.getD (2 * len - j2 - s) 0 with ht3_def
  have ht1_bnd : t1.toNat < mod32.toNat := by
    rw [ht1_def]
    exact inverse_t1_bound roots hroots hroots_bnd s len j2 hlen hlen_dvd hj2
      h_idx_2s_minus h_idx_2s_minus_eq h_idx_s
  have ht3_bnd : t3.toNat < mod32.toNat := by
    rw [ht3_def]
    exact inverse_t3_bound roots hroots hroots_bnd s len j2 hlen hlen_dvd hj2
      h_idx_2len_minus_s h_idx_2len_minus_s_eq
  have ht1_zmod : (t1.toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2))
        * (montR1.toNat : ZMod mod32.toNat) := by
    rw [ht1_def]
    exact inverse_t1_zmod roots hroots hroots_bnd s len j2 hlen hlen_dvd hN_dvd hj2
      h_idx_2s_minus h_idx_2s_minus_eq h_idx_s
  have ht3_zmod : (t3.toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - s - j2)) * (montR1.toNat : ZMod mod32.toNat) := by
    rw [ht3_def]
    exact inverse_t3_zmod roots hroots hroots_bnd s len j2 hlen hlen_dvd hN_dvd hj2
      h_idx_2len_minus_s h_idx_2len_minus_s_eq
  have h_a_all : ∀ idx (hidx : idx < N), (a[idx]'hidx).toNat < mod32.toNat := by
    rw [Vector.all_eq_true] at ha
    intro idx hidx
    exact UInt32.lt_iff_toNat_lt.mp (by simpa using ha _ hidx)
  have ha0 := h_a_all _ hbnd0
  have ha1 := h_a_all _ hbnd1
  have ha2 := h_a_all _ hbnd2
  have ha3 := h_a_all _ hbnd3
  have h_mont_a1_t1 := mont_mul_lt_of_left (a[i2 + j2 + s]'hbnd1) t1 ha1
  have h_mont_a3_t1 := mont_mul_lt_of_left (a[i2 + len + j2 + s]'hbnd3) t1 ha3
  have h_Q_bnd := submod32_lt _ _ ha0 h_mont_a1_t1
  have h_S_bnd := submod32_lt _ _ ha2 h_mont_a3_t1
  have h_t3S_bnd := mont_mul_lt_of_right t3 _ h_S_bnd
  rw [addmod32_ZMod _ _ h_Q_bnd h_t3S_bnd,
      submod32_ZMod _ _ ha0 h_mont_a1_t1,
      mont_mul_ZMod _ _ ha1 ht1_bnd,
      mont_mul_ZMod _ _ ht3_bnd h_S_bnd,
      submod32_ZMod _ _ ha2 h_mont_a3_t1,
      mont_mul_ZMod _ _ ha3 ht1_bnd,
      ht1_zmod, ht3_zmod,
      MONT_R1_ZMod]
  simp only [mul_assoc, mul_inv_cancel₀ two_pow32_ne_zero_ZMod, mul_one,
    mul_comm ((2 : ZMod mod32.toNat) ^ 32) _]
  ring

-- The ZMod correctness proof for inverse butterfly4 at position 3 requires many rewrites.
lemma butterfly4_inverse_ZMod_pos3 {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hN_dvd : N ∣ mod64.toNat - 1)
    (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N) :
    ((butterfly4 a true roots s len i2 j2)[i2 + len + j2 + s]'hbnd3).toNat =
    (((a[i2 + j2]'hbnd0).toNat : ZMod mod32.toNat) -
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2)) *
        (a[i2 + j2 + s]'hbnd1).toNat -
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - s - j2)) *
        ((a[i2 + len + j2]'hbnd2).toNat -
          (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2)) *
            (a[i2 + len + j2 + s]'hbnd3).toNat) : ZMod mod32.toNat) := by
  have hs_pos : s > 0 := by omega
  have hlen_pos : len > 0 := by omega
  have hN_pos : N > 0 := by omega
  have h2len_le : 2 * len ≤ N := Nat.le_of_dvd hN_pos hlen_dvd
  have h_idx_2s_minus : 2 * s - j2 < N := by omega
  have h_idx_2s_minus_eq : 2 * s - j2 = s + (s - j2) := by omega
  have h_idx_2len_minus_s_eq : 2 * len - j2 - s = len + (s - j2) := by omega
  have h_idx_2len_minus_s : 2 * len - j2 - s < N := by omega
  have h_idx_s : s < N := by omega
  rw [butterfly4_inverse_getElem_pos3 roots a s len i2 j2 hbnd0 hbnd1 hbnd2 hbnd3]
  set t1 : UInt32 :=
    if j2 > 0 then mod32 - roots.getD (2 * s - j2) 0 else roots.getD s 0 with ht1_def
  set t3 : UInt32 := mod32 - roots.getD (2 * len - j2 - s) 0 with ht3_def
  have ht1_bnd : t1.toNat < mod32.toNat := by
    rw [ht1_def]
    exact inverse_t1_bound roots hroots hroots_bnd s len j2 hlen hlen_dvd hj2
      h_idx_2s_minus h_idx_2s_minus_eq h_idx_s
  have ht3_bnd : t3.toNat < mod32.toNat := by
    rw [ht3_def]
    exact inverse_t3_bound roots hroots hroots_bnd s len j2 hlen hlen_dvd hj2
      h_idx_2len_minus_s h_idx_2len_minus_s_eq
  have ht1_zmod : (t1.toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2))
        * (montR1.toNat : ZMod mod32.toNat) := by
    rw [ht1_def]
    exact inverse_t1_zmod roots hroots hroots_bnd s len j2 hlen hlen_dvd hN_dvd hj2
      h_idx_2s_minus h_idx_2s_minus_eq h_idx_s
  have ht3_zmod : (t3.toNat : ZMod mod32.toNat) =
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - s - j2)) * (montR1.toNat : ZMod mod32.toNat) := by
    rw [ht3_def]
    exact inverse_t3_zmod roots hroots hroots_bnd s len j2 hlen hlen_dvd hN_dvd hj2
      h_idx_2len_minus_s h_idx_2len_minus_s_eq
  have h_a_all : ∀ idx (hidx : idx < N), (a[idx]'hidx).toNat < mod32.toNat := by
    rw [Vector.all_eq_true] at ha
    intro idx hidx
    exact UInt32.lt_iff_toNat_lt.mp (by simpa using ha _ hidx)
  have ha0 := h_a_all _ hbnd0
  have ha1 := h_a_all _ hbnd1
  have ha2 := h_a_all _ hbnd2
  have ha3 := h_a_all _ hbnd3
  have h_mont_a1_t1 := mont_mul_lt_of_left (a[i2 + j2 + s]'hbnd1) t1 ha1
  have h_mont_a3_t1 := mont_mul_lt_of_left (a[i2 + len + j2 + s]'hbnd3) t1 ha3
  have h_Q_bnd := submod32_lt _ _ ha0 h_mont_a1_t1
  have h_S_bnd := submod32_lt _ _ ha2 h_mont_a3_t1
  have h_t3S_bnd := mont_mul_lt_of_right t3 _ h_S_bnd
  rw [submod32_ZMod _ _ h_Q_bnd h_t3S_bnd,
      submod32_ZMod _ _ ha0 h_mont_a1_t1,
      mont_mul_ZMod _ _ ha1 ht1_bnd,
      mont_mul_ZMod _ _ ht3_bnd h_S_bnd,
      submod32_ZMod _ _ ha2 h_mont_a3_t1,
      mont_mul_ZMod _ _ ha3 ht1_bnd,
      ht1_zmod, ht3_zmod,
      MONT_R1_ZMod]
  simp only [mul_assoc, mul_inv_cancel₀ two_pow32_ne_zero_ZMod, mul_one,
    mul_comm ((2 : ZMod mod32.toNat) ^ 32) _]
  ring

/-- Bundle the four inverse-butterfly position results into a single conjunction,
    mirroring `butterfly4_forward_ZMod_combined`. -/
lemma butterfly4_inverse_ZMod_combined {N : ℕ}
    (roots : Vector UInt32 N) (a : Vector UInt32 N)
    (ha : a.all (· < mod32)) (hroots : ntt_roots_correct N roots)
    (hroots_bnd : roots.all (· < mod32))
    (s len i2 j2 : ℕ) (hlen : len = 2 * s)
    (hlen_dvd : 2 * len ∣ N) (hN_dvd : N ∣ mod64.toNat - 1)
    (hj2 : j2 < s)
    (hbnd0 : i2 + j2 < N) (hbnd1 : i2 + j2 + s < N)
    (hbnd2 : i2 + len + j2 < N) (hbnd3 : i2 + len + j2 + s < N) :
    let τ₁ : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / len * (len - j2))
    let τ₂ : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) * (2 * len - j2))
    let τ₃ : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / (2 * len) *
        (2 * len - s - j2))
    let r  := butterfly4 a true roots s len i2 j2
    let A₀ := ((a[(i2 + j2)]'hbnd0).toNat       : ZMod mod32.toNat)
    let A₁ := ((a[(i2 + j2 + s)]'hbnd1).toNat   : ZMod mod32.toNat)
    let A₂ := ((a[(i2 + len + j2)]'hbnd2).toNat : ZMod mod32.toNat)
    let A₃ := ((a[(i2 + len + j2 + s)]'hbnd3).toNat : ZMod mod32.toNat)
    ((r[(i2 + j2)]'hbnd0).toNat           : ZMod mod32.toNat) =
        A₀ + τ₁ * A₁ + τ₂ * (A₂ + τ₁ * A₃) ∧
    ((r[(i2 + len + j2)]'hbnd2).toNat     : ZMod mod32.toNat) =
        A₀ + τ₁ * A₁ - τ₂ * (A₂ + τ₁ * A₃) ∧
    ((r[(i2 + j2 + s)]'hbnd1).toNat       : ZMod mod32.toNat) =
        A₀ - τ₁ * A₁ + τ₃ * (A₂ - τ₁ * A₃) ∧
    ((r[(i2 + len + j2 + s)]'hbnd3).toNat : ZMod mod32.toNat) =
        A₀ - τ₁ * A₁ - τ₃ * (A₂ - τ₁ * A₃) := by
  simp only []
  exact ⟨butterfly4_inverse_ZMod_pos0 roots a ha hroots hroots_bnd s len i2 j2 hlen hlen_dvd
    hN_dvd hj2 hbnd0 hbnd1 hbnd2 hbnd3,
  butterfly4_inverse_ZMod_pos2 roots a ha hroots hroots_bnd s len i2 j2 hlen hlen_dvd
    hN_dvd hj2 hbnd0 hbnd1 hbnd2 hbnd3,
  butterfly4_inverse_ZMod_pos1 roots a ha hroots hroots_bnd s len i2 j2 hlen hlen_dvd
    hN_dvd hj2 hbnd0 hbnd1 hbnd2 hbnd3,
  butterfly4_inverse_ZMod_pos3 roots a ha hroots hroots_bnd s len i2 j2 hlen hlen_dvd
    hN_dvd hj2 hbnd0 hbnd1 hbnd2 hbnd3⟩
