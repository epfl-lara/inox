/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Data

/-!
# The signed operators of the bit-vectors

A bit-vector of the semantics is its unsigned integer, with a sign that says how the division,
the remainder, the modulo and the comparisons read it (`bv_int`, which is `twos` when signed).
Logos defines the signed operators of SMT-LIB from the unsigned ones, by the cases of the top
bits of the operands. This module proves that the two agree on the values of a width.
-/

namespace Inox.Bridge

open Eo
open SmtEval
open Smtm
open Inox.Semantics

/-- A power of two is twice the one before. -/
theorem pow_half {w : Int} (hw : 0 < w) : (2 : Int) ^ w.toNat = 2 * 2 ^ (w - 1).toNat := by
  have : w.toNat = (w - 1).toNat + 1 := by omega
  rw [this, Int.pow_succ, Int.mul_comm]

theorem neg_emod {P x : Int} (hx0 : 0 < x) (hx : x ≤ P) : (-x) % P = P - x := by
  rw [show -x = (P - x) + P * (-1) by ring, Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt (by omega) (by omega)]

/-- The top bit of a bit-vector is set when it is at least half the power of its width. -/
theorem msb_eq {w x : Int} (hw : 0 < w) (hx0 : 0 ≤ x) (hx : x < 2 ^ w.toNat) :
    __smtx_model_eval_eq
        (__smtx_model_eval_extract (.Numeral (native_zplus w (native_zneg 1)))
          (.Numeral (native_zplus w (native_zneg 1))) (.Binary w x)) (.Binary 1 1) =
      .Boolean (decide (2 ^ (w - 1).toNat ≤ x)) := by
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

/-! The signed division, on the integers: `P` is the power of the width. -/

theorem ediv_small {P a b : Int} (ha : 0 ≤ a) (haP : a < P) (hb : 0 < b) : a / b % P = a / b :=
  Int.emod_eq_of_lt (Int.ediv_nonneg ha (Int.le_of_lt hb))
    (Int.lt_of_le_of_lt (Int.ediv_le_self b ha) haP)

theorem sdiv_pp {P x y : Int} (hx0 : 0 ≤ x) (hy : y ≠ 0) :
    (if y = 0 then P + -1 else x / y) % P = tdiv x y % P := by
  simp [tdiv, hx0, hy]

theorem sdiv_p0 {P x y : Int} (hy : y = 0) :
    (if y = 0 then P + -1 else x / y) % P = (0 - 1) % P := by
  rw [if_pos hy, show (0 : Int) - 1 = (P + -1) + P * (-1) by ring, Int.add_mul_emod_self_left]

theorem sdiv_np {P x y : Int} (hx0 : 0 < x) (hx : x < P) (hy0 : 0 < y) :
    -((if y = 0 then P + -1 else (P - x) / y) % P) % P = tdiv (x - P) y % P := by
  rw [if_neg (by omega), ediv_small (by omega) (by omega) hy0]
  simp only [tdiv, show ¬ (0 : Int) ≤ x - P by omega, ↓reduceDIte]
  rw [show (0 : Int) - (x - P) = P - x by ring, Int.zero_sub]

theorem sdiv_n0 {P x y : Int} (hP : 1 < P) (hy : y = 0) :
    -((if y = 0 then P + -1 else x / y) % P) % P = 1 % P := by
  rw [if_pos hy, show (P + -1) % P = P + -1 from Int.emod_eq_of_lt (by omega) (by omega),
    show -(P + -1) = 1 + P * (-1) by ring, Int.add_mul_emod_self_left]

theorem sdiv_pn {P x y : Int} (hx0 : 0 ≤ x) (hx : x < P) (hy : y < P) :
    -((if P - y = 0 then P + -1 else x / (P - y)) % P) % P = tdiv x (y - P) % P := by
  rw [if_neg (by omega), ediv_small hx0 hx (by omega)]
  simp only [tdiv, hx0, ↓reduceDIte]
  rw [show y - P = -(P - y) by ring, Int.ediv_neg]

theorem sdiv_nn {P x y : Int} (hx0 : 0 < x) (hx : x < P) (hy : y < P) :
    (if P - y = 0 then P + -1 else (P - x) / (P - y)) % P = tdiv (x - P) (y - P) % P := by
  rw [if_neg (by omega)]
  simp only [tdiv, show ¬ (0 : Int) ≤ x - P by omega, ↓reduceDIte]
  rw [show (0 : Int) - (x - P) = P - x by ring, show y - P = -(P - y) by ring, Int.ediv_neg,
    Int.zero_sub, Int.neg_neg]

theorem bvsdiv_eq {D : List Data} {w x y : Int} {v : Value} (hw : 0 < w) (hx0 : 0 ≤ x)
    (hx : x < 2 ^ w.toNat) (hy0 : 0 ≤ y) (hy : y < 2 ^ w.toNat)
    (h : arith_div (.BVV true w x) (.BVV true w y) = .Ok v) :
    HasV D v (.BVType true w) ∧
      __smtx_model_eval_bvsdiv (.Binary w x) (.Binary w y) = trV D v := by
  have hH : (0 : Int) < 2 ^ (w - 1).toNat := Int.pow_pos (by decide)
  have hp2 := pow2_eq (Int.le_of_lt hw)
  have hp1 := pow2_eq (show (0 : Int) ≤ w - 1 by omega)
  simp only [arith_div, same_bv, decide_true, Bool.and_self, ↓reduceDIte, bv_int, twos, hp1,
    hp2] at h
  simp only [__smtx_model_eval_bvsdiv, __smtx_bv_sizeof_value, __smtx_model_eval__,
    msb_eq hw hx0 hx, msb_eq hw hy0 hy, __smtx_model_eval_not, __smtx_model_eval_and, native_not,
    native_and]
  rw [pow_half hw] at hx hy h
  by_cases hxn : 2 ^ (w - 1).toNat ≤ x <;> by_cases hyn : 2 ^ (w - 1).toNat ≤ y <;>
    simp only [hxn, hyn, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.and_self,
      Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, __smtx_model_eval_ite,
      ↓reduceIte, ↓reduceDIte] at h ⊢
  all_goals
    split at h <;>
    (simp only [Result.Ok.injEq] at h; subst h; refine ⟨hasV_bvmk hw _, ?_⟩
     rw [trV_bvmk hw]
     simp only [__smtx_model_eval_bvneg, __smtx_model_eval_bvudiv, native_mod_total, native_zneg,
       native_ite, native_zeq, native_binary_max, native_div_total, native_zplus,
       int_pow2_eq (Int.le_of_lt hw), pow_half hw]
     congr 1
     generalize (2 : Int) ^ (w - 1).toNat = H at *
     rename_i hz
     have ex : 0 < x → -x % (2 * H) = 2 * H - x := fun h => neg_emod h (by omega)
     have ey : 0 < y → -y % (2 * H) = 2 * H - y := fun h => neg_emod h (by omega)
     try rw [ex (by omega)]
     try rw [ey (by omega)]
     simp only [decide_eq_true_eq]
     first
       | omega
       | exact sdiv_pp hx0 hz
       | exact sdiv_p0 hz
       | exact sdiv_np (by omega) hx (by omega)
       | (rw [dif_neg (by omega)]; exact sdiv_n0 (by omega) hz)
       | exact sdiv_pn hx0 hx hy
       | exact sdiv_nn (by omega) hx hy)

/-! The signed remainder. -/

theorem emod_small {P a b : Int} (hb : 0 < b) (hbP : b ≤ P) : a % b % P = a % b :=
  Int.emod_eq_of_lt (Int.emod_nonneg _ (by omega))
    (Int.lt_of_lt_of_le (Int.emod_lt_of_pos _ hb) hbP)

theorem srem_pp {P x y : Int} (hx0 : 0 ≤ x) (hy : y ≠ 0) :
    (if y = 0 then x else x % y) % P = trem x y % P := by
  simp only [if_neg hy, trem, tdiv, hx0, ↓reduceDIte]
  congr 1
  rw [Int.emod_def]

theorem srem_p0 {P x y : Int} (hx0 : 0 ≤ x) (hx : x < P) (hy : y = 0) :
    (if y = 0 then x else x % y) % P = x := by
  rw [if_pos hy, Int.emod_eq_of_lt hx0 hx]

theorem srem_np {P x y : Int} (hx0 : 0 < x) (hx : x < P) (hy0 : 0 < y) (hy : y < P) :
    -((if y = 0 then P - x else (P - x) % y) % P) % P = trem (x - P) y % P := by
  rw [if_neg (by omega), emod_small hy0 (by omega)]
  simp only [trem, tdiv, show ¬ (0 : Int) ≤ x - P by omega, ↓reduceDIte]
  congr 1
  rw [show (0 : Int) - (x - P) = P - x by ring, Int.emod_def]
  ring

theorem srem_n0 {P x y : Int} (hx0 : 0 < x) (hx : x < P) (hy : y = 0) :
    -((if y = 0 then P - x else (P - x) % y) % P) % P = x := by
  rw [if_pos hy, show (P - x) % P = P - x from Int.emod_eq_of_lt (by omega) (by omega),
    show -(P - x) = x + P * (-1) by ring, Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt (by omega) hx]

theorem srem_pn {P x y : Int} (hx0 : 0 ≤ x) (hy : y < P) :
    (if P - y = 0 then x else x % (P - y)) % P = trem x (y - P) % P := by
  rw [if_neg (by omega)]
  simp only [trem, tdiv, hx0, ↓reduceDIte]
  congr 1
  rw [show y - P = -(P - y) by ring, Int.ediv_neg, Int.emod_def]
  ring

theorem srem_nn {P x y : Int} (hx0 : 0 < x) (hx : x < P) (hy0 : 0 < y) (hy : y < P) :
    -((if P - y = 0 then P - x else (P - x) % (P - y)) % P) % P = trem (x - P) (y - P) % P := by
  rw [if_neg (by omega), emod_small (by omega) (by omega)]
  simp only [trem, tdiv, show ¬ (0 : Int) ≤ x - P by omega, ↓reduceDIte]
  congr 1
  rw [show (0 : Int) - (x - P) = P - x by ring, show y - P = -(P - y) by ring, Int.ediv_neg,
    Int.emod_def]
  ring

theorem bvsrem_eq {D : List Data} {w x y : Int} {v : Value} (hw : 0 < w) (hx0 : 0 ≤ x)
    (hx : x < 2 ^ w.toNat) (hy0 : 0 ≤ y) (hy : y < 2 ^ w.toNat)
    (h : arith_rem (.BVV true w x) (.BVV true w y) = .Ok v) :
    HasV D v (.BVType true w) ∧
      __smtx_model_eval_bvsrem (.Binary w x) (.Binary w y) = trV D v := by
  have hH : (0 : Int) < 2 ^ (w - 1).toNat := Int.pow_pos (by decide)
  have hp2 := pow2_eq (Int.le_of_lt hw)
  have hp1 := pow2_eq (show (0 : Int) ≤ w - 1 by omega)
  have hxT : HasV D (.BVV true w x) (.BVType true w) := hasV_bv_of hw hx0 hx
  simp only [arith_rem, same_bv, decide_true, Bool.and_self, ↓reduceDIte, bv_int, twos, hp1,
    hp2] at h
  simp only [__smtx_model_eval_bvsrem, __smtx_bv_sizeof_value, __smtx_model_eval__,
    msb_eq hw hx0 hx, msb_eq hw hy0 hy, __smtx_model_eval_not, __smtx_model_eval_and, native_not,
    native_and]
  rw [pow_half hw] at hx hy h
  by_cases hxn : 2 ^ (w - 1).toNat ≤ x <;> by_cases hyn : 2 ^ (w - 1).toNat ≤ y <;>
    simp only [hxn, hyn, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.and_self,
      Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, __smtx_model_eval_ite,
      ↓reduceIte, ↓reduceDIte] at h ⊢
  all_goals
    split at h <;>
    (simp only [Result.Ok.injEq] at h; subst h
     refine ⟨by first | exact hxT | exact hasV_bvmk hw _, ?_⟩
     try rw [trV_bvmk hw]
     simp only [__smtx_model_eval_bvneg, __smtx_model_eval_bvurem, native_mod_total, native_zneg,
       native_ite, native_zeq, int_pow2_eq (Int.le_of_lt hw), pow_half hw, trV]
     congr 1
     generalize (2 : Int) ^ (w - 1).toNat = H at *
     rename_i hz
     have ex : 0 < x → -x % (2 * H) = 2 * H - x := fun h => neg_emod h (by omega)
     have ey : 0 < y → -y % (2 * H) = 2 * H - y := fun h => neg_emod h (by omega)
     try rw [ex (by omega)]
     try rw [ey (by omega)]
     simp only [decide_eq_true_eq]
     first
       | omega
       | exact srem_pp hx0 hz
       | exact srem_p0 hx0 hx hz
       | exact srem_np (by omega) hx (by omega) hy
       | exact srem_n0 (by omega) hx hz
       | exact srem_pn hx0 hy
       | exact srem_nn (by omega) hx (by omega) hy)

/-! The signed modulo. -/

theorem ite_boolean (b : Bool) (a c : SmtValue) :
    __smtx_model_eval_ite (.Boolean b) a c = if b = true then a else c := by
  cases b <;> simp [__smtx_model_eval_ite]

theorem neg_emod_zero {a b : Int} (h : a % b = 0) : (-a) % b = 0 :=
  Int.emod_eq_zero_of_dvd (Int.dvd_neg.mpr (Int.dvd_of_emod_eq_zero h))

theorem neg_emod_pos {a b : Int} (hb : 0 < b) (h : a % b ≠ 0) : (-a) % b = b - a % b := by
  have h0 := Int.emod_nonneg a (Int.ne_of_gt hb)
  have h1 := Int.emod_lt_of_pos a hb
  rw [show -a = (b - a % b) + b * (-(a / b) - 1) by
    have := Int.emod_def a b; rw [this]; ring]
  rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]

theorem smod_pp {P x y : Int} (hy0 : 0 ≤ y) (hy : y ≠ 0) :
    (if (if y = 0 then x else x % y) % P = 0 then (if y = 0 then x else x % y) % P
      else (if y = 0 then x else x % y) % P) =
      (if y < 0 ∧ ¬x % y = 0 then x % y + y else x % y) % P := by
  rw [ite_self, if_neg hy, if_neg (by omega)]

theorem smod_p0 {P x y : Int} (hx0 : 0 ≤ x) (hx : x < P) (hy : y = 0) :
    (if (if y = 0 then x else x % y) % P = 0 then (if y = 0 then x else x % y) % P
      else (if y = 0 then x else x % y) % P) = x := by
  rw [ite_self, if_pos hy, Int.emod_eq_of_lt hx0 hx]

theorem smod_np {P x y : Int} (hx0 : 0 < x) (hx : x < P) (hy0 : 0 < y) (hy : y < P) :
    (if (if y = 0 then P - x else (P - x) % y) % P = 0 then
        (if y = 0 then P - x else (P - x) % y) % P
      else (-((if y = 0 then P - x else (P - x) % y) % P) % P + y) % P) =
      (if y < 0 ∧ ¬(x - P) % y = 0 then (x - P) % y + y else (x - P) % y) % P := by
  rw [if_neg (show ¬ y = 0 by omega), emod_small hy0 (by omega),
    if_neg (show ¬(y < 0 ∧ ¬(x - P) % y = 0) from fun h => by omega),
    show x - P = -(P - x) by ring]
  by_cases hU : (P - x) % y = 0
  · rw [if_pos hU, neg_emod_zero hU, hU]; simp
  · rw [if_neg hU, neg_emod_pos hy0 hU, Int.emod_add_emod]
    congr 1; ring

theorem smod_n0 {P x y : Int} (hx0 : 0 < x) (hx : x < P) (hy : y = 0) :
    (if (if y = 0 then P - x else (P - x) % y) % P = 0 then
        (if y = 0 then P - x else (P - x) % y) % P
      else (-((if y = 0 then P - x else (P - x) % y) % P) % P + y) % P) = x := by
  have h1 : (P - x) % P = P - x := Int.emod_eq_of_lt (by omega) (by omega)
  rw [if_pos hy, h1, if_neg (by omega), hy, Int.add_zero, Int.emod_emod,
    show -(P - x) = x + P * (-1) by ring, Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt (by omega) hx]

theorem smod_pn {P x y : Int} (hy0 : 0 < y) (hy : y < P) :
    (if (if P - y = 0 then x else x % (P - y)) % P = 0 then
        (if P - y = 0 then x else x % (P - y)) % P
      else ((if P - y = 0 then x else x % (P - y)) % P + y) % P) =
      (if y - P < 0 ∧ ¬x % (y - P) = 0 then x % (y - P) + (y - P) else x % (y - P)) % P := by
  rw [if_neg (show ¬ P - y = 0 by omega), emod_small (by omega) (by omega),
    show y - P = -(P - y) by ring, Int.emod_neg]
  by_cases hU : x % (P - y) = 0
  · rw [if_pos hU, if_neg (fun h => h.2 hU), hU]; simp
  · rw [if_neg hU, if_pos ⟨by omega, hU⟩,
      show x % (P - y) + -(P - y) = (x % (P - y) + y) + P * (-1) by ring,
      Int.add_mul_emod_self_left]

theorem smod_nn {P x y : Int} (hx0 : 0 < x) (hx : x < P) (hy0 : 0 < y) (hy : y < P) :
    (if (if P - y = 0 then P - x else (P - x) % (P - y)) % P = 0 then
        (if P - y = 0 then P - x else (P - x) % (P - y)) % P
      else -((if P - y = 0 then P - x else (P - x) % (P - y)) % P) % P) =
      (if y - P < 0 ∧ ¬(x - P) % (y - P) = 0 then (x - P) % (y - P) + (y - P)
        else (x - P) % (y - P)) % P := by
  rw [if_neg (show ¬ P - y = 0 by omega), emod_small (by omega) (by omega),
    show y - P = -(P - y) by ring, Int.emod_neg, show x - P = -(P - x) by ring]
  by_cases hU : (P - x) % (P - y) = 0
  · rw [if_pos hU, neg_emod_zero hU, if_neg (fun h => h.2 rfl), hU]; simp
  · have := Int.emod_lt_of_pos (P - x) (show 0 < P - y by omega)
    rw [if_neg hU, neg_emod_pos (by omega) hU, if_pos ⟨by omega, by omega⟩]
    congr 1; ring

theorem bvsmod_eq {D : List Data} {w x y : Int} {v : Value} (hw : 0 < w) (hx0 : 0 ≤ x)
    (hx : x < 2 ^ w.toNat) (hy0 : 0 ≤ y) (hy : y < 2 ^ w.toNat)
    (h : arith_mod (.BVV true w x) (.BVV true w y) = .Ok v) :
    HasV D v (.BVType true w) ∧
      __smtx_model_eval_bvsmod (.Binary w x) (.Binary w y) = trV D v := by
  have hH : (0 : Int) < 2 ^ (w - 1).toNat := Int.pow_pos (by decide)
  have hp2 := pow2_eq (Int.le_of_lt hw)
  have hp1 := pow2_eq (show (0 : Int) ≤ w - 1 by omega)
  have hxT : HasV D (.BVV true w x) (.BVType true w) := hasV_bv_of hw hx0 hx
  simp only [arith_mod, same_bv, decide_true, Bool.and_self, ↓reduceDIte, bv_int, twos, hp1,
    hp2] at h
  simp only [__smtx_model_eval_bvsmod, __smtx_bv_sizeof_value, __smtx_model_eval__,
    msb_eq hw hx0 hx, msb_eq hw hy0 hy, __smtx_model_eval_not, __smtx_model_eval_and, native_not,
    native_and]
  rw [pow_half hw] at hx hy h
  by_cases hxn : 2 ^ (w - 1).toNat ≤ x <;> by_cases hyn : 2 ^ (w - 1).toNat ≤ y <;>
    simp only [hxn, hyn, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.and_self,
      Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, ite_boolean,
      Bool.false_eq_true, ↓reduceIte, ↓reduceDIte] at h ⊢
  all_goals
    split at h <;>
    (simp only [Result.Ok.injEq] at h; subst h
     refine ⟨by first | exact hxT | exact hasV_bvmk hw _, ?_⟩
     try rw [trV_bvmk hw]
     simp only [__smtx_model_eval_bvneg, __smtx_model_eval_bvurem, __smtx_model_eval_bvadd,
       __smtx_model_eval_eq, native_veq, native_mod_total, native_zneg, native_zplus,
       native_ite, native_zeq, int_pow2_eq (Int.le_of_lt hw), pow_half hw, trV,
       SmtValue.Binary.injEq, true_and, ite_boolean, decide_eq_true_eq, dite_eq_ite]
     try rw [← apply_ite (SmtValue.Binary w)]
     congr 1
     generalize (2 : Int) ^ (w - 1).toNat = H at *
     rename_i hz
     have ex : 0 < x → -x % (2 * H) = 2 * H - x := fun h => neg_emod h (by omega)
     have ey : 0 < y → -y % (2 * H) = 2 * H - y := fun h => neg_emod h (by omega)
     try rw [ex (by omega)]
     try rw [ey (by omega)]
     first
       | omega
       | exact smod_pp hy0 hz
       | exact smod_p0 hx0 hx hz
       | exact smod_np (by omega) hx (by omega) hy
       | exact smod_n0 (by omega) hx hz
       | exact smod_pn (by omega) hy
       | exact smod_nn (by omega) hx (by omega) hy)

/-! The signed comparisons. -/

theorem bvsgt_eq {w x y : Int} (hw : 0 < w) (hx0 : 0 ≤ x) (hx : x < 2 ^ w.toNat) (hy0 : 0 ≤ y)
    (hy : y < 2 ^ w.toNat) :
    __smtx_model_eval_bvsgt (.Binary w x) (.Binary w y) =
      .Boolean (decide (twos w y < twos w x)) := by
  have hH : (0 : Int) < 2 ^ (w - 1).toNat := Int.pow_pos (by decide)
  simp only [__smtx_model_eval_bvsgt, __smtx_bv_sizeof_value, __smtx_model_eval__,
    msb_eq hw hx0 hx, msb_eq hw hy0 hy, __smtx_model_eval_not, __smtx_model_eval_and,
    __smtx_model_eval_bvugt, native_not, native_and, native_zlt, twos, pow2_eq (Int.le_of_lt hw),
    pow2_eq (show (0 : Int) ≤ w - 1 by omega)]
  simp only [__smtx_model_eval_or, __smtx_model_eval_eq, __smtx_model_eval_and, native_veq,
    native_or, native_and]
  rw [pow_half hw] at hx hy ⊢
  congr 1
  generalize (2 : Int) ^ (w - 1).toNat = H at *
  by_cases hxn : H ≤ x <;> by_cases hyn : H ≤ y <;> simp [hxn, hyn] <;> omega

theorem bvsge_eq {w x y : Int} (hw : 0 < w) (hx0 : 0 ≤ x) (hx : x < 2 ^ w.toNat) (hy0 : 0 ≤ y)
    (hy : y < 2 ^ w.toNat) :
    __smtx_model_eval_bvsge (.Binary w x) (.Binary w y) =
      .Boolean (!decide (twos w x < twos w y)) := by
  have hH : (0 : Int) < 2 ^ (w - 1).toNat := Int.pow_pos (by decide)
  rw [__smtx_model_eval_bvsge, bvsgt_eq hw hx0 hx hy0 hy]
  simp only [__smtx_model_eval_or, __smtx_model_eval_eq, native_veq, native_or, twos,
    pow2_eq (Int.le_of_lt hw), pow2_eq (show (0 : Int) ≤ w - 1 by omega),
    SmtValue.Binary.injEq, true_and]
  rw [pow_half hw] at hx hy ⊢
  congr 1
  generalize (2 : Int) ^ (w - 1).toNat = H at *
  by_cases hxn : H ≤ x <;> by_cases hyn : H ≤ y <;>
    simp only [hxn, hyn, ↓reduceDIte, ↓reduceIte] <;>
    (rw [Bool.eq_iff_iff]
     simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
     rw [show (@Eq native_Int x y) = (@Eq Int x y) from rfl]
     omega)

end Inox.Bridge
