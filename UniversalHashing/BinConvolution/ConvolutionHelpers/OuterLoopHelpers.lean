/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import UniversalHashing.BinConvolution.ConvolutionHelpers.DFTLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.RootTableLemmas
import UniversalHashing.BinConvolution.ConvolutionHelpers.NttBoundLemmas


/-!
# Helper lemmas for `ntt_outerLoop_computes_ref_ntt`
-/


/-- ℕ-variant: if `m = 2^n` and `m ∣ mod64.toNat - 1`, then `n < 64`. -/
lemma n_lt_64_of_pow2_nat (m n : ℕ) (hm : m = 2 ^ n) (hm_dvd : m ∣ mod64.toNat - 1) :
    n < 64 := by
  have hm_le : m ≤ mod64.toNat - 1 := Nat.le_of_dvd (by decide) hm_dvd
  have hm_lt : m < 2^64 := Nat.lt_of_le_of_lt hm_le (by decide)
  have h2n_lt : 2^n < 2^64 := hm ▸ hm_lt
  exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2n_lt

/-- `rootsInner` preserves boundedness of the underlying vector. -/
lemma rootsInner_preserves_bound {n : ℕ} (wm : UInt32) (halfLen : ℕ)
    (k i : ℕ) (v : Vector UInt32 n) (hv : v.all (· < mod32)) :
    (rootsInner wm halfLen k i v).all (· < mod32) := by
  induction k generalizing v i with
  | zero => exact hv
  | succ k ih =>
    rw [show rootsInner wm halfLen (k + 1) i v =
          rootsInner wm halfLen k (i + 1)
            (if hs : halfLen + i < n then
              if _ : halfLen + i + 1 < n then
                v.set (halfLen + i + 1) (montMul (v.get ⟨halfLen + i, hs⟩) wm)
              else v
            else v) from rfl]
    apply ih
    split_ifs with hs hd
    · rw [Vector.all_eq_true] at *
      intro j hj
      simp only [decide_eq_true_eq]
      rw [Vector.getElem_set]
      split_ifs with hjk
      · apply mont_mul_lt_of_left
        have := hv (halfLen + i) hs
        exact show v[halfLen + i].toNat < mod32.toNat from
          UInt32.lt_iff_toNat_lt.mp (by simpa using this)
      · have := hv j hj
        simpa using this
    · exact hv
    · exact hv

/-- `ensureRoots.outer` preserves boundedness. -/
lemma outer_preserves_bound (n : ℕ) (v : Vector UInt32 n) (hn : 0 < n)
    (len : UInt64) (f : ℕ) (hv : v.all (· < mod32)) :
    (ensureRoots.outer n v len hn f).all (· < mod32) := by
  induction f generalizing v len with
  | zero => simp only [ensureRoots.outer, hv]
  | succ f ih =>
    rw [ensureRoots.outer]
    split_ifs with hgt
    · exact hv
    · apply ih
      apply rootsInner_preserves_bound
      rw [Vector.all_eq_true] at *
      intro j hj
      simp only [decide_eq_true_eq]
      rw [Vector.getElem_set]
      split_ifs with hjk
      · decide
      · have := hv j hj
        simpa using this

/-- All entries of `ensureRoots m` are strictly below `mod32`. -/
lemma ensure_roots_bound {m : UInt64} :
    (ensureRoots m.toNat).all (· < mod32) := by
  unfold ensureRoots
  split_ifs with hm
  · simp
  · apply outer_preserves_bound
    rw [Vector.all_eq_true]
    intro i hi
    simp only [decide_eq_true_eq, Vector.getElem_replicate]
    decide

/-- ℕ-variant of `ensure_roots_bound`: all entries of `ensureRoots m` are < mod32. -/
lemma ensure_roots_bound_nat (m : ℕ) (hm : m < 2 ^ 64) :
    (ensureRoots m).all (· < mod32) := by
  have h : m.toUInt64.toNat = m := nat_toUInt64_faithful m hm
  rw [← h]; exact ensure_roots_bound

lemma outerLoop_returns_gt {m : ℕ} (inverse : Bool)
    (roots a : Vector UInt32 m)
    (len : UInt64) (fuel : ℕ) (h : len.toNat * 2 > m) :
    nttInplace.outerLoop inverse roots a len fuel = a := by
  induction fuel with
  | zero => simp only [nttInplace.outerLoop]
  | succ f ih => simp only [nttInplace.outerLoop, h, ↓reduceIte]

lemma go_computes_log2 (m : UInt64) (n : ℕ) (hm : m.toNat = 2 ^ n) (hn : n < 64) :
    (nttInplace.go 64 m.toNat 0).toNat = n := by
  have h_ind : ∀ n : ℕ, n < 64 → (nttInplace.go 64 (2 ^ n) 0).toNat = n := by
    decide
  rw [hm]
  exact h_ind n hn

/-- ℕ-variant: if `m = 2^n` and `n` is even, then `nttInplace.go 64 m 0 &&& 1 = 0`. -/
lemma go_parity_even_nat (m n : ℕ) (hm : m = 2 ^ n) (hn : n < 64) (hne : Even n) :
    nttInplace.go 64 m 0 &&& 1 = 0 := by
  have h_ind : ∀ k : ℕ, k < 64 → Even k → nttInplace.go 64 (2 ^ k) 0 &&& 1 = 0 := by
    decide
  rw [hm]; exact h_ind n hn hne

/-- ℕ-variant: if `m = 2^n` and `n` is odd, then `nttInplace.go 64 m 0 &&& 1 ≠ 0`. -/
lemma go_parity_odd_nat (m n : ℕ) (hm : m = 2 ^ n) (hn : n < 64) (hno : Odd n) :
    nttInplace.go 64 m 0 &&& 1 ≠ 0 := by
  have h_ind : ∀ k : ℕ, k < 64 → Odd k → nttInplace.go 64 (2 ^ k) 0 &&& 1 ≠ 0 := by
    decide
  rw [hm]; exact h_ind n hn hno

/-- `bitRev w x` reverses the lowest `w` bits of `x`. -/
def bitRev : ℕ → ℕ → ℕ
  | 0, _ => 0
  | w + 1, x => 2 ^ w * (x % 2) + bitRev w (x / 2)

@[simp] lemma bitRev_zero_width (x : ℕ) : bitRev 0 x = 0 := rfl
@[simp] lemma bitRev_succ (w x : ℕ) :
    bitRev (w + 1) x = 2 ^ w * (x % 2) + bitRev w (x / 2) := rfl

lemma bitRev_lt (w x : ℕ) : bitRev w x < 2 ^ w := by
  induction w generalizing x with
  | zero => simp only [bitRev]; norm_num
  | succ w ih =>
    simp only [bitRev]
    have h2 : bitRev w (x / 2) < 2 ^ w := ih (x / 2)
    have hmod : x % 2 = 0 ∨ x % 2 = 1 := by omega
    cases hmod with
    | inl h => rw [h]; simp; linarith [(by ring : 2 ^ (w+1) = 2 * 2^w)]
    | inr h => rw [h]; simp; linarith [(by ring : 2 ^ (w+1) = 2 * 2^w)]

lemma bitRev_index_lt (n q : ℕ) (hq : q ≤ n) (j : Fin (2 ^ q)) (b : ℕ) :
    2 ^ (n - q) * j.val + bitRev (n - q) b < 2 ^ n := by
  have h1 : bitRev (n - q) b < 2 ^ (n - q) := bitRev_lt (n - q) b
  have h2 : j.val < 2 ^ q := j.isLt
  have h3 : 2 ^ (n - q) * 2 ^ q = 2 ^ n := by
    rw [← pow_add]; congr 1; omega
  nlinarith [Nat.two_pow_pos (n - q)]

noncomputable def ntt_sub_input {m : ℕ} (n q : ℕ) (hq : q ≤ n)
    (hm_eq : m = 2 ^ n)
    (v : Vector UInt32 m) (b : ℕ) : Fin (2 ^ q) → ZMod mod32.toNat :=
  fun j =>
    let idx : Fin (2 ^ n) :=
      ⟨2 ^ (n - q) * j.val + bitRev (n - q) b, bitRev_index_lt n q hq j b⟩
    ((toMont (v[Fin.cast hm_eq.symm idx])).toNat : ZMod mod32.toNat)

def outerLoop_inv {m : ℕ} (n q : ℕ) (hq : q ≤ n) (hm_eq : m = 2 ^ n)
    (v : Vector UInt32 m)
    (a : Vector UInt32 m) : Prop :=
  a.all (· < mod32) ∧
  ∀ (b : ℕ) (r : Fin (2 ^ q)),
    b < 2 ^ (n - q) →
    let idx := b * 2 ^ q + r.val
    ∀ hidx : idx < m,
      ((a[idx]'hidx).toNat : ZMod mod32.toNat) =
        ref_ntt q
          ((primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / 2 ^ q))
          (ntt_sub_input n q hq hm_eq v b) r

lemma inv_at_n_implies_ref_ntt {m : ℕ} (n : ℕ)
    (hm_eq : m = 2 ^ n)
    (v : Vector UInt32 m)
    (a : Vector UInt32 m)
    (hinv : outerLoop_inv n n (le_refl n) hm_eq v a) :
    let ω : ZMod mod32.toNat :=
      (primRoot.toNat : ZMod mod32.toNat) ^ ((mod64.toNat - 1) / m)
    ∀ k : Fin m,
      ((a[k.val]).toNat : ZMod mod32.toNat) =
        ref_ntt n ω
          (fun j : Fin (2 ^ n) => ((toMont (v[Fin.cast hm_eq.symm j])).toNat : ZMod mod32.toNat))
          (Fin.cast hm_eq k) := by
  have hthis := hinv.2 0
  simp only [Nat.sub_self, pow_zero, Nat.zero_mul, Nat.zero_add, hm_eq,
             show (0:ℕ) < 1 from Nat.one_pos, forall_const,
             Fin.is_lt, forall_prop_of_true] at hthis ⊢
  convert hthis using 1
  constructor <;> intro h r <;>
    specialize h ⟨r, by linarith [Fin.is_lt r, hm_eq]⟩ <;>
    simp_all only [Fin.getElem_fin, Fin.val_cast]
  unfold ntt_sub_input; simp [Fin.cast]


/-- When the block count is 0 (which happens when `len` is large enough relative to `m`
or when `len = 0`), `radix4Middle` does nothing. -/
@[simp] lemma radix4Middle_zero_blocks {n : ℕ} (inverse : Bool) (roots : Vector UInt32 n)
    (s len : ℕ) (b : ℕ) (a : Vector UInt32 n) :
    radix4Middle inverse roots s len 0 b a = a := by
  simp only [radix4Middle]

/-- Nat version of outerLoop_len_not_gt. -/
lemma outerLoop_len_not_gt_nat {m : ℕ} (n q : ℕ)
    (hm_eq : m = 2 ^ n) (hq2 : q + 2 ≤ n)
    (len : UInt64) (hlen : len.toNat = 2 ^ (q + 1)) :
    ¬(len.toNat * 2 > m) := by
  rw [hm_eq, hlen, (by ring : 2 ^ (q + 1) * 2 = 2 ^ (q + 2))]
  exact Nat.not_lt.mpr (Nat.pow_le_pow_right (by norm_num) hq2)

/-- Helper: the toMont mapping preserves the overall bound. -/
lemma vector_map_to_mont_bound {m : ℕ} (v : Vector UInt32 m) (hv : v.all (· < mod32)) :
    (v.map toMont).all (· < mod32) := by
  rw [Vector.all_eq_true] at *
  intro i hi
  simp only [Vector.getElem_map]
  have h := hv i hi
  simp only [decide_eq_true_eq] at h ⊢
  exact to_mont_lt _ h

/-
The outerLoop is a no-op when `len` is either 0 or a large power of 2 exceeding `m`.
Specifically, when `len.toNat = 2^k` with `k > n` (and `k < 64`), or when `len.toNat = 0`,
the block count `m.toNat / (2 * len.toNat)` is always 0, so the loop does nothing.
-/
lemma outerLoop_noop_pow2 {m : ℕ} (inverse : Bool) (roots a : Vector UInt32 m)
    (len : UInt64) (fuel : ℕ) (n : ℕ) (hm_eq : m = 2 ^ n)
    (h : (∃ k, len.toNat = 2 ^ k ∧ n < k ∧ k < 64) ∨ len.toNat = 0) :
    nttInplace.outerLoop inverse roots a len fuel = a := by
  induction fuel generalizing len a with
  | zero => unfold nttInplace.outerLoop; aesop
  | succ fuel ih =>
    by_cases hlen : len.toNat = 0
    · unfold nttInplace.outerLoop
      have : len = 0 := by exact Eq.symm ((fun {a b} ↦ UInt64.toNat_inj.mp) (id (Eq.symm hlen)))
      rw [this]
      aesop
    · obtain ⟨k, hk₁, hk₂, hk₃⟩ := h.resolve_right hlen
      by_cases hk₄ : k + 1 < 64
      · have h_len_mul_two : (len * 2).toNat = 2 ^ (k + 1) := by
          have hk_le : k ≤ 62 := by omega
          have hlt : 2 ^ k * 2 < UInt64.size :=
            Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 2 (Nat.pow_le_pow_right (by decide) hk_le))
              (by decide)
          rw [UInt64.toNat_mul, show (2 : UInt64).toNat = 2 from rfl, hk₁,
              Nat.mod_eq_of_lt hlt, pow_succ]
        have h_len_mul_two_gt_m : (len * 2).toNat > m := by
          exact h_len_mul_two.symm ▸ hm_eq.symm ▸
            pow_lt_pow_right₀ (by decide) (by linarith)
        have h' : len.toNat * 2 > m := by
          rw [hk₁, hm_eq, ← pow_succ]
          exact pow_lt_pow_right₀ (by decide) (by linarith)
        exact outerLoop_returns_gt inverse roots a len (fuel + 1) h'
      · have hk_eq : k = 63 := by omega
        subst hk_eq
        exact outerLoop_returns_gt inverse roots a len (fuel + 1) (by
          simp only [hk₁, hm_eq]
          exact lt_of_lt_of_le (pow_lt_pow_right₀ (by decide) hk₂) (by norm_num))

/-! ### bitRev radix-4 decomposition -/

lemma bitRev_four_mul_add_one (w b : ℕ) :
    bitRev (w + 2) (4 * b + 1) = 2 ^ (w + 1) + bitRev w b := by
      rw [show 4 * b + 1 = 2 * (2 * b) + 1 by ring]
      simp [Nat.add_mod, Nat.pow_succ']; ring_nf
      norm_num [show 1 + b * 4 = 2 * (b * 2) + 1 by ring, Nat.add_div]

/-! ### ntt_sub_input stride-4 relations -/

private lemma pow2q2_eq (q : ℕ) : 2 ^ (q + 2) = 4 * 2 ^ q := by
  rw [(by omega : q + 2 = 2 + q), pow_add]; norm_num

lemma fin_4mul_lt (q : ℕ) (j : Fin (2 ^ q)) : 4 * j.val < 2 ^ (q + 2) := by
  nlinarith [j.isLt, pow2q2_eq q]
lemma fin_4mul1_lt (q : ℕ) (j : Fin (2 ^ q)) : 4 * j.val + 1 < 2 ^ (q + 2) := by
  nlinarith [j.isLt, pow2q2_eq q]
lemma fin_4mul2_lt (q : ℕ) (j : Fin (2 ^ q)) : 4 * j.val + 2 < 2 ^ (q + 2) := by
  nlinarith [j.isLt, pow2q2_eq q]
lemma fin_4mul3_lt (q : ℕ) (j : Fin (2 ^ q)) : 4 * j.val + 3 < 2 ^ (q + 2) := by
  nlinarith [j.isLt, pow2q2_eq q]
lemma pow2q_lt_q2 (q j2 : ℕ) (hj2 : j2 < 2 ^ q) : j2 < 2 ^ (q + 2) := by
  nlinarith [pow2q2_eq q]
lemma pow2q_add_q_lt_q2 (q j2 : ℕ) (hj2 : j2 < 2 ^ q) : j2 + 2 ^ q < 2 ^ (q + 2) := by
  nlinarith [pow2q2_eq q]
lemma pow2q_add_q1_lt_q2 (q j2 : ℕ) (hj2 : j2 < 2 ^ q) : j2 + 2 ^ (q + 1) < 2 ^ (q + 2) := by
  have h1 : 2 ^ (q + 1) = 2 * 2 ^ q := by
    rw [(by omega : q + 1 = 1 + q), pow_add]; norm_num
  nlinarith [pow2q2_eq q]
lemma pow2q_add_q_q1_lt_q2 (q j2 : ℕ) (hj2 : j2 < 2 ^ q) :
    j2 + 2 ^ q + 2 ^ (q + 1) < 2 ^ (q + 2) := by
  have h1 : 2 ^ (q + 1) = 2 * 2 ^ q := by
    rw [(by omega : q + 1 = 1 + q), pow_add]; norm_num
  nlinarith [pow2q2_eq q]

lemma ntt_sub_input_block_0 {m : ℕ} (n q : ℕ) (hq2 : q + 2 ≤ n)
    (hm_eq : m = 2 ^ n) (v : Vector UInt32 m)
    (b : ℕ) (hb : b < 2 ^ (n - q - 2)) (j : Fin (2 ^ q)) :
    ntt_sub_input n q (by omega) hm_eq v (4 * b) j =
    ntt_sub_input n (q + 2) hq2 hm_eq v b ⟨4 * j.val, fin_4mul_lt q j⟩ := by
      unfold ntt_sub_input
      -- The two low bits of `4 * b` are zero, so its bit-reversal at width `n - q`
      -- equals the bit-reversal of `b` at width `n - q - 2`.
      have h_bitRev : bitRev (n - q) (4 * b) = bitRev (n - q - 2) b := by
        rcases k : n - q with (_ | _ | k) <;>
          simp_all [Nat.pow_succ', Nat.mul_assoc]
        grind
      -- Since the indices are the same, the elements at those indices are the same.
      have h_index_eq :
          2 ^ (n - q) * j.val + bitRev (n - q) (4 * b) =
          2 ^ (n - (q + 2)) * (4 * j.val) + bitRev (n - (q + 2)) b := by
        rw [h_bitRev, show n - q = n - (q + 2) + 2 by omega]; ring_nf
        norm_num
      simp only [h_index_eq]

lemma ntt_sub_input_block_1 {m : ℕ} (n q : ℕ) (hq2 : q + 2 ≤ n)
    (hm_eq : m = 2 ^ n) (v : Vector UInt32 m)
    (b : ℕ) (j : Fin (2 ^ q)) :
    ntt_sub_input n q (by omega) hm_eq v (4 * b + 1) j =
    ntt_sub_input n (q + 2) hq2 hm_eq v b ⟨4 * j.val + 2, fin_4mul2_lt q j⟩ := by
      -- LHS index: `2^(n-q) * j + bitRev(n-q, 4*b + 1)`.
      have h_index_lhs :
          2 ^ (n - q) * j.val + bitRev (n - q) (4 * b + 1) =
          2 ^ (n - (q + 2)) * (4 * j.val + 2) + bitRev (n - (q + 2)) b := by
        rw [show n - q = n - (q + 2) + 2 by omega, bitRev_four_mul_add_one]; ring
      unfold ntt_sub_input
      simp only [h_index_lhs]

lemma ntt_sub_input_block_2 {m : ℕ} (n q : ℕ) (hq2 : q + 2 ≤ n)
    (hm_eq : m = 2 ^ n) (v : Vector UInt32 m)
    (b : ℕ) (j : Fin (2 ^ q)) :
    ntt_sub_input n q (by omega) hm_eq v (4 * b + 2) j =
    ntt_sub_input n (q + 2) hq2 hm_eq v b ⟨4 * j.val + 1, fin_4mul1_lt q j⟩ := by
      unfold ntt_sub_input
      -- The expressions are equal by simplifying exponents.
      have h_exp : n - q = n - (q + 2) + 2 := by
        omega
      simp only [h_exp]
      norm_num [show 4 * b = 2 * (2 * b) by ring, Nat.add_div]; ring_nf

lemma ntt_sub_input_block_3 {m : ℕ} (n q : ℕ) (hq2 : q + 2 ≤ n)
    (hm_eq : m = 2 ^ n) (v : Vector UInt32 m)
    (b : ℕ) (hb : b < 2 ^ (n - q - 2)) (j : Fin (2 ^ q)) :
    ntt_sub_input n q (by omega) hm_eq v (4 * b + 3) j =
    ntt_sub_input n (q + 2) hq2 hm_eq v b ⟨4 * j.val + 3, fin_4mul3_lt q j⟩ := by
      unfold ntt_sub_input
      have h_bitRev :
          bitRev (n - q) (4 * b + 3) =
          2 ^ (n - q - 1) + 2 ^ (n - q - 2) + bitRev (n - q - 2) b := by
        rcases n' : n - q with (_ | _ | n') <;>
          simp_all [Nat.pow_succ']
        · omega
        · omega
        · norm_num [Nat.add_mod, Nat.add_div, Nat.mul_mod, Nat.mul_div_assoc, Nat.mul_comm]; ring
      -- By simplifying the exponents, we can see that the two indices are equal.
      have h_exp :
          2 ^ (n - q) * j.val + 2 ^ (n - q - 1) + 2 ^ (n - q - 2) =
          2 ^ (n - (q + 2)) * (4 * j.val + 3) := by
        rw [show n - q = n - (q + 2) + 2 by omega]; ring_nf
        norm_num [Nat.add_comm 2, pow_add]; ring
      grind

/-! ### ref_ntt radix-4 unfolding -/

/-
Unfolding `ref_ntt (q+2)` twice gives a radix-4 formula at position j2 < 2^q (quadrant 0).
-/
lemma ref_ntt_radix4_q0 {R : Type*} [CommRing R] (q : ℕ) (ω : R)
    (f : Fin (2 ^ (q + 2)) → R) (j2 : ℕ) (hj2 : j2 < 2 ^ q) :
    ref_ntt (q + 2) ω f ⟨j2, pow2q_lt_q2 q j2 hj2⟩ =
      (ref_ntt q (ω ^ 4)
          (fun j : Fin (2 ^ q) => f ⟨4 * j.val, fin_4mul_lt q j⟩) ⟨j2, hj2⟩ +
       (ω ^ 2) ^ j2 * ref_ntt q (ω ^ 4)
          (fun j : Fin (2 ^ q) => f ⟨4 * j.val + 2, fin_4mul2_lt q j⟩) ⟨j2, hj2⟩) +
      ω ^ j2 * (ref_ntt q (ω ^ 4)
          (fun j : Fin (2 ^ q) => f ⟨4 * j.val + 1, fin_4mul1_lt q j⟩) ⟨j2, hj2⟩ +
       (ω ^ 2) ^ j2 * ref_ntt q (ω ^ 4)
          (fun j : Fin (2 ^ q) => f ⟨4 * j.val + 3, fin_4mul3_lt q j⟩) ⟨j2, hj2⟩) := by
         -- For q+2, unfold ref_ntt once to get the dif_pos condition.
         simp only [ref_ntt] at *
         simp only [pow_succ'] at *
         simp only [pow_zero, mul_one, mul_left_comm, mul_comm]
         split_ifs <;> try omega
         ring_nf

/-
Quadrant 1: position j2 + 2^q.
-/
lemma ref_ntt_radix4_q1 {R : Type*} [CommRing R] (q : ℕ) (ω : R)
    (f : Fin (2 ^ (q + 2)) → R) (j2 : ℕ) (hj2 : j2 < 2 ^ q) :
    ref_ntt (q + 2) ω f ⟨j2 + 2 ^ q, pow2q_add_q_lt_q2 q j2 hj2⟩ =
      (ref_ntt q (ω ^ 4)
          (fun j : Fin (2 ^ q) => f ⟨4 * j.val, fin_4mul_lt q j⟩) ⟨j2, hj2⟩ -
       (ω ^ 2) ^ j2 * ref_ntt q (ω ^ 4)
          (fun j : Fin (2 ^ q) => f ⟨4 * j.val + 2, fin_4mul2_lt q j⟩) ⟨j2, hj2⟩) +
      ω ^ (j2 + 2 ^ q) * (ref_ntt q (ω ^ 4)
          (fun j : Fin (2 ^ q) => f ⟨4 * j.val + 1, fin_4mul1_lt q j⟩) ⟨j2, hj2⟩ -
       (ω ^ 2) ^ j2 * ref_ntt q (ω ^ 4)
          (fun j : Fin (2 ^ q) => f ⟨4 * j.val + 3, fin_4mul3_lt q j⟩) ⟨j2, hj2⟩) := by
         simp only [ref_ntt]
         simp [pow_succ', mul_left_comm, mul_comm]
         simp [show 2 * 2 ^ q = 2 ^ q + 2 ^ q by ring, hj2]
         ring_nf

/-- Quadrant 2: position j2 + 2^(q+1). -/
lemma ref_ntt_radix4_q2 {R : Type*} [CommRing R] (q : ℕ) (ω : R)
    (f : Fin (2 ^ (q + 2)) → R) (j2 : ℕ) (hj2 : j2 < 2 ^ q) :
    ref_ntt (q + 2) ω f ⟨j2 + 2 ^ (q + 1), pow2q_add_q1_lt_q2 q j2 hj2⟩ =
      (ref_ntt q (ω ^ 4)
          (fun j : Fin (2 ^ q) => f ⟨4 * j.val, fin_4mul_lt q j⟩) ⟨j2, hj2⟩ +
       (ω ^ 2) ^ j2 * ref_ntt q (ω ^ 4)
          (fun j : Fin (2 ^ q) => f ⟨4 * j.val + 2, fin_4mul2_lt q j⟩) ⟨j2, hj2⟩) -
      ω ^ j2 * (ref_ntt q (ω ^ 4)
          (fun j : Fin (2 ^ q) => f ⟨4 * j.val + 1, fin_4mul1_lt q j⟩) ⟨j2, hj2⟩ +
       (ω ^ 2) ^ j2 * ref_ntt q (ω ^ 4)
          (fun j : Fin (2 ^ q) => f ⟨4 * j.val + 3, fin_4mul3_lt q j⟩) ⟨j2, hj2⟩) := by
  simp only [ref_ntt]
  simp_all [Nat.pow_succ']
  ring_nf at *

/-
Quadrant 3: position j2 + 2^q + 2^(q+1).
-/
lemma ref_ntt_radix4_q3 {R : Type*} [CommRing R] (q : ℕ) (ω : R)
    (f : Fin (2 ^ (q + 2)) → R) (j2 : ℕ) (hj2 : j2 < 2 ^ q) :
    ref_ntt (q + 2) ω f ⟨j2 + 2 ^ q + 2 ^ (q + 1), pow2q_add_q_q1_lt_q2 q j2 hj2⟩ =
      (ref_ntt q (ω ^ 4)
          (fun j : Fin (2 ^ q) => f ⟨4 * j.val, fin_4mul_lt q j⟩) ⟨j2, hj2⟩ -
       (ω ^ 2) ^ j2 * ref_ntt q (ω ^ 4)
          (fun j : Fin (2 ^ q) => f ⟨4 * j.val + 2, fin_4mul2_lt q j⟩) ⟨j2, hj2⟩) -
      ω ^ (j2 + 2 ^ q) * (ref_ntt q (ω ^ 4)
          (fun j : Fin (2 ^ q) => f ⟨4 * j.val + 1, fin_4mul1_lt q j⟩) ⟨j2, hj2⟩ -
       (ω ^ 2) ^ j2 * ref_ntt q (ω ^ 4)
          (fun j : Fin (2 ^ q) => f ⟨4 * j.val + 3, fin_4mul3_lt q j⟩) ⟨j2, hj2⟩) := by
         simp only [ref_ntt]
         simp_all [Nat.pow_succ']
         ring_nf at *

/-- Position arithmetic for block `b'`, with ℕ size bound `m`. -/
lemma ntt_block_pos_arith_nat {m : ℕ} (n q : ℕ) (hq2 : q + 2 ≤ n)
    (hm_eq : m = 2 ^ n) (hn64 : n < 64)
    (len : UInt64) (hlen : len.toNat = 2 ^ (q + 1))
    (b' j2' : ℕ) (hb' : b' < 2 ^ (n - q - 2)) (hj2' : j2' < 2 ^ q) :
    let s := len >>> 1
    let i2' := (b' * 2 * len.toNat).toUInt64
    i2'.toNat = b' * 2 ^ (q + 2) ∧
    (i2' + j2'.toUInt64).toNat = b' * 2 ^ (q + 2) + j2' ∧
    (i2' + j2'.toUInt64 + s).toNat = b' * 2 ^ (q + 2) + j2' + 2 ^ q ∧
    (i2' + len + j2'.toUInt64).toNat = b' * 2 ^ (q + 2) + j2' + 2 ^ (q + 1) ∧
    (i2' + len + j2'.toUInt64 + s).toNat = b' * 2 ^ (q + 2) + j2' + 2 ^ (q + 1) + 2 ^ q ∧
    (i2' + j2'.toUInt64).toNat < m ∧
    (i2' + j2'.toUInt64 + s).toNat < m ∧
    (i2' + len + j2'.toUInt64).toNat < m ∧
    (i2' + len + j2'.toUInt64 + s).toNat < m := by
  have hs_eq : (len >>> 1).toNat = 2 ^ q := by
    simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, hlen, Nat.pow_succ',
               (by decide : (1 : UInt64).toNat % 64 = 1), pow_one]; omega
  have hb'_i2_lt : b' * 2 ^ (q + 2) < 2 ^ n := by
    have : b' * 2 ^ (q + 2) < 2 ^ (n - q - 2) * 2 ^ (q + 2) := by
      nlinarith [Nat.two_pow_pos (q + 2), hb']
    rw [show (2 : ℕ) ^ (n - q - 2) * 2 ^ (q + 2) = 2 ^ n from by
      rw [← pow_add]; congr 1; omega] at this
    exact this
  have hb'_i2_lt_64 : b' * 2 ^ (q + 2) < 2 ^ 64 :=
    lt_of_lt_of_le hb'_i2_lt (Nat.pow_le_pow_right (by decide) (by omega))
  have hb'_i2_toNat : ((b' * 2 * len.toNat).toUInt64).toNat = b' * 2 ^ (q + 2) := by
    have h1 : b' * 2 * len.toNat = b' * 2 ^ (q + 2) := by rw [hlen]; ring
    rw [h1]; exact nat_toUInt64_faithful _ hb'_i2_lt_64
  have hj2'_u_toNat : (j2'.toUInt64).toNat = j2' := by
    apply nat_toUInt64_faithful
    exact lt_of_lt_of_le (lt_of_lt_of_le hj2' (Nat.pow_le_pow_right (by decide)
      (show q ≤ n by omega))) (Nat.pow_le_pow_right (by decide) (by omega))
  have hbexpand : (b' + 1) * 2 ^ (q + 2) = b' * 2 ^ (q + 2) + 2 ^ (q + 2) := by ring
  have hbp1' : (b' + 1) * 2 ^ (q + 2) ≤ 2 ^ n := by
    calc (b' + 1) * 2 ^ (q + 2) ≤ 2 ^ (n - q - 2) * 2 ^ (q + 2) := Nat.mul_le_mul_right _ hb'
      _ = 2 ^ n := by rw [← pow_add]; congr 1; omega
  have hpow_e : 2 ^ (q + 2) = 2 ^ q + 2 ^ q + 2 ^ q + 2 ^ q := by ring
  have hpow1 : 2 ^ (q + 1) = 2 ^ q + 2 ^ q := by ring
  simp only
  have h_pow_lt : ∀ x : ℕ, x < 2 ^ n → x < 2 ^ 64 :=
    fun x hx => lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))
  have h_first : ((b' * 2 * len.toNat).toUInt64 + j2'.toUInt64).toNat = b' * 2 ^ (q + 2) + j2' := by
    rw [UInt64.toNat_add, hb'_i2_toNat, hj2'_u_toNat]
    exact Nat.mod_eq_of_lt (h_pow_lt _ (by omega))
  have hrw : (b' * 2 * len.toNat).toUInt64 + len + j2'.toUInt64 =
      ((b' * 2 * len.toNat).toUInt64 + j2'.toUInt64) + len := by abel
  have h_third : ((b' * 2 * len.toNat).toUInt64 + len + j2'.toUInt64).toNat =
      b' * 2 ^ (q + 2) + j2' + 2 ^ (q + 1) := by
    rw [hrw, UInt64.toNat_add, h_first, hlen]
    exact Nat.mod_eq_of_lt (h_pow_lt _ (by omega))
  have h_ijs : ((b' * 2 * len.toNat).toUInt64 + j2'.toUInt64 + (len >>> 1)).toNat =
      b' * 2 ^ (q + 2) + j2' + 2 ^ q := by
    rw [UInt64.toNat_add, h_first, hs_eq]
    exact Nat.mod_eq_of_lt (h_pow_lt _ (by omega))
  have h_ljs : ((b' * 2 * len.toNat).toUInt64 + len + j2'.toUInt64 + (len >>> 1)).toNat =
      b' * 2 ^ (q + 2) + j2' + 2 ^ (q + 1) + 2 ^ q := by
    have : (b' * 2 * len.toNat).toUInt64 + len + j2'.toUInt64 + (len >>> 1) =
        ((b' * 2 * len.toNat).toUInt64 + len + j2'.toUInt64) + (len >>> 1) := by abel
    rw [this, UInt64.toNat_add, h_third, hs_eq]
    exact Nat.mod_eq_of_lt (h_pow_lt _ (by omega))
  refine ⟨hb'_i2_toNat, h_first, h_ijs, h_third, h_ljs, ?_, ?_, ?_, ?_⟩
  · rw [h_first, hm_eq]; omega
  · rw [h_ijs, hm_eq]; omega
  · rw [h_third, hm_eq]; omega
  · rw [h_ljs, hm_eq]; omega

lemma radix4Middle_comp {N : ℕ} (inverse : Bool) (roots : Vector UInt32 N) (s len : ℕ)
    (k1 k2 b_start : ℕ) (a : Vector UInt32 N) :
    radix4Middle inverse roots s len (k1 + k2) b_start a =
    radix4Middle inverse roots s len k2 (b_start + k1)
      (radix4Middle inverse roots s len k1 b_start a) := by
  induction k1 generalizing b_start a with
  | zero => simp only [radix4Middle, Nat.zero_add, Nat.add_zero]
  | succ k1 ih =>
    have heq : k1.succ + k2 = (k1 + k2).succ := by omega
    conv_lhs => rw [heq]
    change radix4Middle inverse roots s len (k1 + k2) (b_start + 1)
      (radix4Inner inverse roots s len (b_start * 2 * len) s 0 a) = _
    rw [ih (b_start + 1)]
    change _ = radix4Middle inverse roots s len k2 (b_start + k1.succ)
      (radix4Middle inverse roots s len k1 (b_start + 1)
        (radix4Inner inverse roots s len (b_start * 2 * len) s 0 a))
    congr 1; omega

/-- Butterfly at j2 ≠ j2nat does not touch any of the four block positions for j2nat.
    Isolated so omega runs in minimal context (avoids slow hypothesis scanning). -/
lemma radix4_block_ne_pos (q b j2 j2nat : ℕ)
    (hj2 : j2 < 2 ^ q) (hj2_lt : j2nat < 2 ^ q) (hj2_ne : j2 ≠ j2nat)
    (posval : ℕ)
    (hpos : posval = b * 2 ^ (q + 2) + j2nat ∨
            posval = b * 2 ^ (q + 2) + j2nat + 2 ^ q ∨
            posval = b * 2 ^ (q + 2) + j2nat + 2 ^ (q + 1) ∨
            posval = b * 2 ^ (q + 2) + j2nat + 2 ^ (q + 1) + 2 ^ q) :
    b * 2 ^ (q + 2) + j2 ≠ posval ∧
    b * 2 ^ (q + 2) + j2 + 2 ^ q ≠ posval ∧
    b * 2 ^ (q + 2) + j2 + 2 ^ (q + 1) ≠ posval ∧
    b * 2 ^ (q + 2) + j2 + 2 ^ (q + 1) + 2 ^ q ≠ posval := by
  have hpow_e : 2 ^ (q + 2) = 2 ^ q + 2 ^ q + 2 ^ q + 2 ^ q := by ring
  have hpow1 : 2 ^ (q + 1) = 2 ^ q + 2 ^ q := by ring
  rcases hpos with h | h | h | h <;> subst h <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
