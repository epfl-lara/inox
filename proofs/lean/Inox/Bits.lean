/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Signed

/-!
# The bitwise operators, the shifts and the casts of the bit-vectors

The semantics defines the conjunction, the disjunction and the exclusive disjunction of two
bit-vectors by recursion on their bits, and Logos by those of `BitVec`. A shift of the semantics
is by the amount cut at the width, and that of Logos by the amount, and the arithmetic shift of
Logos is by the cases of the top bit. This file proves that they agree on the values of a width,
and so do the casts with the extraction and the two extensions that Inox prints for them.
-/

namespace Inox.Bridge

open Eo
open SmtEval
open Smtm
open Inox.Semantics

/-! The bitwise operators, on the naturals. -/

theorem and_bits (A B : Nat) : A &&& B = 2 * (A / 2 &&& B / 2) + A % 2 * (B % 2) := by
  have h1 : (A &&& B) / 2 = A / 2 &&& B / 2 := by
    simpa [Nat.shiftRight_eq_div_pow] using Nat.shiftRight_and_distrib (a := A) (b := B) (i := 1)
  have h2 : (A &&& B) % 2 = A % 2 * (B % 2) := by
    have := Nat.and_mod_two_pow (a := A) (b := B) (n := 1)
    rw [Nat.pow_one] at this; rw [this]
    rcases Nat.mod_two_eq_zero_or_one A with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one B with h' | h' <;> simp [h, h']
  omega

theorem or_bits (A B : Nat) :
    A ||| B = 2 * (A / 2 ||| B / 2) + (A % 2 + B % 2 - A % 2 * (B % 2)) := by
  have h1 : (A ||| B) / 2 = A / 2 ||| B / 2 := by
    simpa [Nat.shiftRight_eq_div_pow] using Nat.shiftRight_or_distrib (a := A) (b := B) (i := 1)
  have h2 : (A ||| B) % 2 = A % 2 + B % 2 - A % 2 * (B % 2) := by
    have := Nat.or_mod_two_pow (a := A) (b := B) (n := 1)
    rw [Nat.pow_one] at this; rw [this]
    rcases Nat.mod_two_eq_zero_or_one A with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one B with h' | h' <;> simp [h, h']
  omega

theorem xor_bits (A B : Nat) : A ^^^ B = 2 * (A / 2 ^^^ B / 2) + (A % 2 + B % 2) % 2 := by
  have h1 : (A ^^^ B) / 2 = A / 2 ^^^ B / 2 := by
    simpa [Nat.shiftRight_eq_div_pow] using Nat.shiftRight_xor_distrib (a := A) (b := B) (i := 1)
  have h2 : (A ^^^ B) % 2 = (A % 2 + B % 2) % 2 := by
    have := Nat.xor_mod_two_pow (a := A) (b := B) (n := 1)
    rw [Nat.pow_one] at this; rw [this]
    rcases Nat.mod_two_eq_zero_or_one A with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one B with h' | h' <;> simp [h, h']
  omega

theorem bit_and_nat : ∀ (n A B : Nat), A = n → bit_and A B = ((A &&& B : Nat) : Int) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A B hA
    unfold bit_and
    split
    · rename_i h
      rcases h with h | h
      · have : A = 0 := by omega
        subst this; simp
      · have : B = 0 := by omega
        subst this; simp
    · rename_i h
      have h2 : ((A : Int) / 2) = ((A / 2 : Nat) : Int) := by omega
      have h3 : ((B : Int) / 2) = ((B / 2 : Nat) : Int) := by omega
      rw [h2, h3, ih (A / 2) (by omega) _ _ rfl]
      conv_rhs => rw [and_bits]
      simp only [bit]; push_cast; rfl

theorem bit_or_nat : ∀ (n A B : Nat), A = n → bit_or A B = ((A ||| B : Nat) : Int) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A B hA
    unfold bit_or
    split
    · have : A = 0 := by omega
      subst this; simp
    · split
      · have : B = 0 := by omega
        subst this; simp
      · have h2 : ((A : Int) / 2) = ((A / 2 : Nat) : Int) := by omega
        have h3 : ((B : Int) / 2) = ((B / 2 : Nat) : Int) := by omega
        rw [h2, h3, ih (A / 2) (by omega) _ _ rfl]
        conv_rhs => rw [or_bits]
        have hle : A % 2 * (B % 2) ≤ A % 2 + B % 2 := by
          rcases Nat.mod_two_eq_zero_or_one A with h | h <;>
            rcases Nat.mod_two_eq_zero_or_one B with h' | h' <;> simp [h, h']
        simp only [bit]; push_cast [Nat.cast_sub hle]; rfl

theorem bit_xor_nat : ∀ (n A B : Nat), A = n → bit_xor A B = ((A ^^^ B : Nat) : Int) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A B hA
    unfold bit_xor
    split
    · have : A = 0 := by omega
      subst this; simp
    · split
      · have : B = 0 := by omega
        subst this; simp
      · have h2 : ((A : Int) / 2) = ((A / 2 : Nat) : Int) := by omega
        have h3 : ((B : Int) / 2) = ((B / 2 : Nat) : Int) := by omega
        rw [h2, h3, ih (A / 2) (by omega) _ _ rfl]
        conv_rhs => rw [xor_bits]
        simp only [bit]; push_cast; rfl

/-- A bit-vector of a width is a natural under the power of the width. -/
theorem bv_nat {w x : Int} (hx0 : 0 ≤ x) (hx : x < 2 ^ w.toNat) :
    ∃ X : Nat, x = X ∧ X < 2 ^ w.toNat := by
  obtain ⟨X, rfl⟩ := Int.eq_ofNat_of_zero_le hx0
  exact ⟨X, rfl, by exact_mod_cast hx⟩

theorem toInt_emod {n : Nat} (b : BitVec n) : b.toInt % 2 ^ n = b.toNat := by
  have h : (2 : Int) ^ n = ((2 ^ n : Nat) : Int) := by push_cast; rfl
  rw [BitVec.toInt_eq_toNat_bmod, h, Int.bmod_emod]
  exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast b.isLt)

theorem ofInt_toNat {n X : Nat} (h : X < 2 ^ n) : (BitVec.ofInt n (X : Int)).toNat = X := by
  simp [Nat.mod_eq_of_lt h]

/-- The conjunction of Logos is that of the semantics, which is a value of the width. -/
theorem bvand_eq {w x y : Int} (hw : 0 < w) (hx0 : 0 ≤ x) (hx : x < 2 ^ w.toNat) (hy0 : 0 ≤ y)
    (hy : y < 2 ^ w.toNat) : 0 ≤ bit_and x y ∧ bit_and x y < 2 ^ w.toNat ∧
      __smtx_model_eval_bvand (.Binary w x) (.Binary w y) = .Binary w (bit_and x y) := by
  obtain ⟨X, rfl, hX⟩ := bv_nat hx0 hx
  obtain ⟨Y, rfl, hY⟩ := bv_nat hy0 hy
  have hlt : X &&& Y < 2 ^ w.toNat := Nat.and_lt_two_pow _ hY
  rw [bit_and_nat _ X Y rfl]
  refine ⟨by omega, by exact_mod_cast hlt, ?_⟩
  simp only [__smtx_model_eval_bvand, native_mod_total, native_binary_and, native_ite, native_zeq,
    native_piand, int_pow2_eq (Int.le_of_lt hw), decide_eq_false (show ¬ w = 0 by omega),
    Bool.false_eq_true, ↓reduceIte]
  rw [toInt_emod, BitVec.toNat_and, ofInt_toNat hX, ofInt_toNat hY]

/-- The disjunction of Logos is that of the semantics, which is a value of the width. -/
theorem bvor_eq {w x y : Int} (hw : 0 < w) (hx0 : 0 ≤ x) (hx : x < 2 ^ w.toNat) (hy0 : 0 ≤ y)
    (hy : y < 2 ^ w.toNat) : 0 ≤ bit_or x y ∧ bit_or x y < 2 ^ w.toNat ∧
      __smtx_model_eval_bvor (.Binary w x) (.Binary w y) = .Binary w (bit_or x y) := by
  obtain ⟨X, rfl, hX⟩ := bv_nat hx0 hx
  obtain ⟨Y, rfl, hY⟩ := bv_nat hy0 hy
  have hlt : X ||| Y < 2 ^ w.toNat := Nat.or_lt_two_pow hX hY
  rw [bit_or_nat _ X Y rfl]
  refine ⟨by omega, by exact_mod_cast hlt, ?_⟩
  simp only [__smtx_model_eval_bvor, native_mod_total, native_binary_or, native_ite, native_zeq,
    impl_native_pior, int_pow2_eq (Int.le_of_lt hw), decide_eq_false (show ¬ w = 0 by omega),
    Bool.false_eq_true, ↓reduceIte]
  rw [toInt_emod, BitVec.toNat_or, ofInt_toNat hX, ofInt_toNat hY]

/-- The exclusive disjunction of Logos is that of the semantics, a value of the width. -/
theorem bvxor_eq {w x y : Int} (hw : 0 < w) (hx0 : 0 ≤ x) (hx : x < 2 ^ w.toNat) (hy0 : 0 ≤ y)
    (hy : y < 2 ^ w.toNat) : 0 ≤ bit_xor x y ∧ bit_xor x y < 2 ^ w.toNat ∧
      __smtx_model_eval_bvxor (.Binary w x) (.Binary w y) = .Binary w (bit_xor x y) := by
  obtain ⟨X, rfl, hX⟩ := bv_nat hx0 hx
  obtain ⟨Y, rfl, hY⟩ := bv_nat hy0 hy
  have hlt : X ^^^ Y < 2 ^ w.toNat := Nat.xor_lt_two_pow hX hY
  rw [bit_xor_nat _ X Y rfl]
  refine ⟨by omega, by exact_mod_cast hlt, ?_⟩
  simp only [__smtx_model_eval_bvxor, native_mod_total, native_binary_xor, native_ite,
    native_zeq, impl_native_pixor, int_pow2_eq (Int.le_of_lt hw),
    decide_eq_false (show ¬ w = 0 by omega), Bool.false_eq_true, ↓reduceIte]
  rw [toInt_emod, BitVec.toNat_xor, ofInt_toNat hX, ofInt_toNat hY]

/-! The shifts. The amount is a bit-vector of the width, that the semantics cuts at the width. -/

theorem pow_le_pow {a b : Int} (h : a ≤ b) : (2 : Int) ^ a.toNat ≤ 2 ^ b.toNat :=
  pow_le_pow_right₀ (by decide) (by omega)

theorem pow_dvd {a b : Int} (h : a ≤ b) : (2 : Int) ^ a.toNat ∣ 2 ^ b.toNat :=
  pow_dvd_pow 2 (by omega)

/-- The power of the cut amount divides as that of the amount. -/
theorem shift_div {w n y : Int} (hw : 0 < w) (hn0 : 0 ≤ n) (hn : n < 2 ^ w.toNat)
    (hy0 : 0 ≤ y) : n / pow2 (shift_amount w y) = n / 2 ^ y.toNat := by
  unfold shift_amount
  split
  · rename_i h
    rw [pow2_eq (Int.le_of_lt hw), Int.ediv_eq_zero_of_lt hn0 hn,
      Int.ediv_eq_zero_of_lt hn0 (Int.lt_of_lt_of_le hn (pow_le_pow h))]
  · rw [pow2_eq hy0]

/-- The power of the cut amount multiplies as that of the amount, in the width. -/
theorem shift_mul {w x y : Int} (hw : 0 < w) (hy0 : 0 ≤ y) :
    x * pow2 (shift_amount w y) % 2 ^ w.toNat = x * 2 ^ y.toNat % 2 ^ w.toNat := by
  unfold shift_amount
  split
  · rename_i h
    rw [pow2_eq (Int.le_of_lt hw), Int.emod_eq_zero_of_dvd (Dvd.dvd.mul_left (dvd_refl _) x),
      Int.emod_eq_zero_of_dvd (Dvd.dvd.mul_left (pow_dvd h) x)]
  · rw [pow2_eq hy0]

theorem bvshl_eq {D : List Data} {s : Bool} {w x y : Int} (hw : 0 < w) (hy0 : 0 ≤ y) :
    __smtx_model_eval_bvshl (.Binary w x) (.Binary w y) =
      trV D (bv s w (x * pow2 (shift_amount w y))) := by
  rw [trV_bvmk hw, shift_mul hw hy0]
  simp only [__smtx_model_eval_bvshl, native_mod_total, native_zmult,
    int_pow2_eq (Int.le_of_lt hw), int_pow2_eq hy0]

theorem lshr_range {w x k : Int} (hx0 : 0 ≤ x) (hx : x < 2 ^ w.toNat) (hk : 0 < k) :
    0 ≤ x / k ∧ x / k < 2 ^ w.toNat :=
  ⟨Int.ediv_nonneg hx0 (Int.le_of_lt hk),
    Int.lt_of_le_of_lt (Int.ediv_le_self _ hx0) hx⟩

theorem pow2_pos (n : Int) : 0 < pow2 n := by
  by_cases h : 0 ≤ n
  · rw [pow2_eq h]; exact two_pow_pos _
  · unfold pow2; rw [dif_pos (by omega)]; decide

theorem bvlshr_eq {w x y : Int} (hw : 0 < w) (hx0 : 0 ≤ x) (hx : x < 2 ^ w.toNat)
    (hy0 : 0 ≤ y) : __smtx_model_eval_bvlshr (.Binary w x) (.Binary w y) =
      .Binary w (x / pow2 (shift_amount w y)) := by
  have h := lshr_range hx0 hx (two_pow_pos y.toNat)
  rw [shift_div hw hx0 hx hy0]
  simp only [__smtx_model_eval_bvlshr, native_mod_total, native_div_total,
    int_pow2_eq (Int.le_of_lt hw), int_pow2_eq hy0]
  rw [Int.emod_eq_of_lt h.1 h.2]

/-- The quotient of an opposite, rounded down. -/
theorem neg_succ_ediv {n k : Int} (hk : 0 < k) : (-(n + 1)) / k = -(n / k) - 1 := by
  have h1 := Int.emod_nonneg n (Int.ne_of_gt hk)
  have h2 := Int.emod_lt_of_pos n hk
  have h3 := Int.emod_add_mul_ediv n k
  rw [Int.ediv_eq_iff_of_pos hk]
  constructor <;> nlinarith

/-- The top bit of a bit-vector is clear when it is under half the power of its width. -/
theorem msb_clear {w x : Int} (hw : 0 < w) (hx0 : 0 ≤ x) (hx : x < 2 ^ w.toNat) :
    __smtx_model_eval_eq
        (__smtx_model_eval_extract (.Numeral (native_zplus w (native_zneg 1)))
          (.Numeral (native_zplus w (native_zneg 1))) (.Binary w x)) (.Binary 1 0) =
      .Boolean (!decide (2 ^ (w - 1).toNat ≤ x)) := by
  have hH : (0 : Int) < 2 ^ (w - 1).toNat := Int.pow_pos (by decide)
  rw [pow_half hw] at hx
  have hw1 : w + -1 + 1 + -(w + -1) = 1 := by omega
  have hq : x / 2 ^ (w - 1).toNat = if 2 ^ (w - 1).toNat ≤ x then 1 else 0 := by
    split
    · rw [Int.ediv_eq_iff_of_pos hH]; omega
    · rw [Int.ediv_eq_iff_of_pos hH]; omega
  simp only [__smtx_model_eval_extract, __smtx_model_eval_eq, native_veq,
    native_binary_extract, native_div_total, native_mod_total, native_zplus, native_zneg]
  rw [hw1, int_pow2_eq (show (0 : Int) ≤ w + -1 by omega),
    int_pow2_eq (show (0 : Int) ≤ 1 by decide), show w + -1 = w - 1 by omega, hq]
  by_cases h : 2 ^ (w - 1).toNat ≤ x
  · rw [if_pos h, decide_eq_true h]; simp
  · rw [if_neg h, decide_eq_false h]; simp

/-- The arithmetic shift of Logos, by the cases of the top bit, is the quotient of the signed
reading of the semantics. -/
theorem bvashr_eq {D : List Data} {s : Bool} {w x y : Int} (hw : 0 < w) (hx0 : 0 ≤ x)
    (hx : x < 2 ^ w.toNat) (hy0 : 0 ≤ y) :
    __smtx_model_eval_bvashr (.Binary w x) (.Binary w y) =
      trV D (bv s w (twos w x / pow2 (shift_amount w y))) := by
  have hk := pow2_pos (shift_amount w y)
  have hP := pow2_eq (Int.le_of_lt hw)
  have hH := pow2_eq (show (0 : Int) ≤ w - 1 by omega)
  rw [trV_bvmk hw]
  unfold __smtx_model_eval_bvashr
  simp only [__smtx_bv_sizeof_value, __smtx_model_eval__, native_zplus, native_zneg]
  have hm := msb_clear hw hx0 hx
  simp only [native_zplus, native_zneg] at hm
  rw [hm]
  by_cases h : 2 ^ (w - 1).toNat ≤ x
  · have hn0 : 0 ≤ 2 ^ w.toNat - 1 - x := by omega
    have hn : 2 ^ w.toNat - 1 - x < 2 ^ w.toNat := by omega
    have hr := lshr_range hn0 hn hk
    have hnot : (2 ^ w.toNat + -(x + 1)) % 2 ^ w.toNat = 2 ^ w.toNat - 1 - x := by
      rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
    have hnot' : (2 ^ w.toNat + -((2 ^ w.toNat - 1 - x) / pow2 (shift_amount w y) + 1)) %
        2 ^ w.toNat = 2 ^ w.toNat - 1 - (2 ^ w.toNat - 1 - x) / pow2 (shift_amount w y) := by
      rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
    have hsem : twos w x / pow2 (shift_amount w y) % 2 ^ w.toNat =
        2 ^ w.toNat - 1 - (2 ^ w.toNat - 1 - x) / pow2 (shift_amount w y) := by
      rw [twos, dif_pos (by rw [hH]; exact h), hP,
        show x - 2 ^ w.toNat = -((2 ^ w.toNat - 1 - x) + 1) by ring, neg_succ_ediv hk,
        show -((2 ^ w.toNat - 1 - x) / pow2 (shift_amount w y)) - 1 =
          (2 ^ w.toNat - 1 - (2 ^ w.toNat - 1 - x) / pow2 (shift_amount w y)) +
            2 ^ w.toNat * (-1) by ring, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (by omega) (by omega)]
    rw [hsem]
    simp only [decide_eq_true h, Bool.not_true, __smtx_model_eval_ite, __smtx_model_eval_bvnot,
      native_mod_total, native_binary_not, native_zplus, native_zneg,
      int_pow2_eq (Int.le_of_lt hw), hnot, bvlshr_eq hw hn0 hn hy0, hnot']
  · have hr := lshr_range hx0 hx hk
    rw [twos, dif_neg (by rw [hH]; exact h), Int.emod_eq_of_lt hr.1 hr.2]
    simp only [decide_eq_false h, Bool.not_false, __smtx_model_eval_ite,
      bvlshr_eq hw hx0 hx hy0]

/-! The casts. Inox prints a narrowing as the extraction of the low bits, and a widening as the
extension by the sign of a signed bit-vector, and by zeros of an unsigned one. -/

theorem twos_emod {w v x : Int} (hw : 0 ≤ w) (hvw : v ≤ w) :
    twos w x % 2 ^ v.toNat = x % 2 ^ v.toNat := by
  unfold twos
  split
  · obtain ⟨c, hc⟩ := pow_dvd hvw
    rw [pow2_eq hw, hc, Int.sub_mul_emod_self_left]
  · rfl

theorem extract_eq {D : List Data} {s : Bool} {w v x : Int} (hv : 0 < v) (hvw : v ≤ w) :
    __smtx_model_eval_extract (.Numeral (v - 1)) (.Numeral 0) (.Binary w x) =
      trV D (bv s v (bv_int s w x)) := by
  have hb : bv_int s w x % 2 ^ v.toNat = x % 2 ^ v.toNat := by
    unfold bv_int; split
    · exact twos_emod (by omega) hvw
    · rfl
  rw [trV_bvmk hv, hb]
  simp only [__smtx_model_eval_extract, native_mod_total, native_binary_extract,
    native_div_total, native_zplus, native_zneg, show v - 1 + 1 + -0 = v by omega,
    int_pow2_eq (Int.le_of_lt hv), int_pow2_eq (Int.le_refl 0)]
  simp

theorem zero_extend_eq {D : List Data} {w v x : Int} (hw : 0 < w) (hx0 : 0 ≤ x)
    (hx : x < 2 ^ w.toNat) (hwv : w ≤ v) :
    __smtx_model_eval_zero_extend (.Numeral (v - w)) (.Binary w x) =
      trV D (bv false v (bv_int false w x)) := by
  rw [trV_bvmk (by omega)]
  simp only [bv_int, Bool.false_eq_true, ↓reduceDIte, __smtx_model_eval_zero_extend,
    native_zplus, show v - w + w = v by omega]
  rw [Int.emod_eq_of_lt hx0 (Int.lt_of_lt_of_le hx (pow_le_pow hwv))]

theorem uts_eq {w x : Int} (hw : 0 < w) (hx0 : 0 ≤ x) (hx : x < 2 ^ w.toNat) :
    native_binary_uts w x = twos w x := by
  have hH : (0 : Int) < 2 ^ (w - 1).toNat := Int.pow_pos (by decide)
  rw [pow_half hw] at hx
  simp only [native_binary_uts, native_zplus, native_zmult, native_zneg, native_mod_total,
    show w + -1 = w - 1 by omega, int_pow2_eq (show (0 : Int) ≤ w - 1 by omega), twos,
    pow2_eq (show (0 : Int) ≤ w - 1 by omega), pow2_eq (Int.le_of_lt hw), pow_half hw]
  split
  · rw [show x = (x - 2 ^ (w - 1).toNat) + 2 ^ (w - 1).toNat * 1 by ring,
      Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    ring
  · rw [Int.emod_eq_of_lt hx0 (by omega)]; ring

theorem sign_extend_eq {D : List Data} {w v x : Int} (hw : 0 < w) (hx0 : 0 ≤ x)
    (hx : x < 2 ^ w.toNat) (hwv : w ≤ v) :
    __smtx_model_eval_sign_extend (.Numeral (v - w)) (.Binary w x) =
      trV D (bv true v (bv_int true w x)) := by
  rw [trV_bvmk (by omega)]
  simp only [bv_int, ↓reduceDIte, __smtx_model_eval_sign_extend, native_zplus,
    native_mod_total, show v - w + w = v by omega, int_pow2_eq (show (0 : Int) ≤ v by omega),
    uts_eq hw hx0 hx]

end Inox.Bridge
