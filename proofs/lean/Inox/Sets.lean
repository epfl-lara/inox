/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.SetMaps

/-!
# The sets of Logos, from lists

A set of the semantics is the list of its elements, in the order of their insertion. A set of
Logos is a map to the Booleans whose entries are sorted by an order on the values, and which has
no entry of the default, so that two sets with the same elements are the same value. This module
builds the set of Logos of a list of values, by inserting them one at a time, and proves that it
is canonical, that its members are those of the list, and that it depends only on them.
-/

namespace Inox.Bridge

open Eo
open SmtEval
open Smtm

/-- The set of the values `ws`, of elements of the sort `A`. -/
noncomputable def setOf (A : SmtType) : List SmtValue → SmtMap
  | [] => .default A (.Boolean false)
  | w :: ws => __smtx_map_update_aux (.Boolean false) (setOf A ws) w (.Boolean true)

theorem setOf_default (A : SmtType) : ∀ ws : List SmtValue,
    __smtx_map_get_default (setOf A ws) = .Boolean false
  | [] => rfl
  | w :: ws => by
    rw [setOf, map_update_aux_get_default]; exact setOf_default A ws

theorem setOf_leaf (A : SmtType) : ∀ ws : List SmtValue,
    smt_map_default_leaf (setOf A ws) = .default A (.Boolean false)
  | [] => rfl
  | w :: ws => by
    rw [setOf, map_update_aux_default_leaf]; exact setOf_leaf A ws

theorem setOf_canonical (uc : SmtUSortDom) (A : SmtType) : ∀ ws : List SmtValue,
    (∀ w ∈ ws, __smtx_value_canonical uc w = true) →
    __smtx_map_canonical uc (setOf A ws) = true
  | [], _ => set_empty_map_canonical A
  | w :: ws, h => by
    have ih := setOf_canonical uc A ws fun x hx => h x (.tail _ hx)
    have := map_update_aux_canonical (uc := uc) (m := setOf A ws) (i := w)
      (e := .Boolean true) ih (h w (.head _)) rfl
    rwa [setOf_default] at this

/-- The members of the set of a list are the values of the list. -/
theorem setOf_lookup (uc : SmtUSortDom) (A : SmtType) : ∀ (ws : List SmtValue) (x : SmtValue),
    (∀ w ∈ ws, __smtx_value_canonical uc w = true) →
    __smtx_map_lookup (setOf A ws) x = .Boolean (decide (x ∈ ws))
  | [], x, _ => by simp [setOf, __smtx_map_lookup]
  | w :: ws, x, h => by
    have hc := setOf_canonical uc A ws fun y hy => h y (.tail _ hy)
    have ih := setOf_lookup uc A ws x fun y hy => h y (.tail _ hy)
    by_cases hwx : w = x
    · subst hwx
      have := map_lookup_update_aux_same (uc := uc) (m := setOf A ws) (i := w)
        (e := .Boolean true) hc
      rw [setOf_default] at this
      simp [setOf, this]
    · have := map_lookup_update_aux_other (uc := uc) (m := setOf A ws) (i := w) (j := x)
        (e := .Boolean true) hc (by simp [native_veq, hwx])
      rw [setOf_default] at this
      rw [setOf, this, ih]
      simp [Ne.symm hwx]

/-- Two lists with the same values have the same set. -/
theorem setOf_ext (uc : SmtUSortDom) (A : SmtType) {ws ws' : List SmtValue}
    (h : ∀ w ∈ ws, __smtx_value_canonical uc w = true)
    (h' : ∀ w ∈ ws', __smtx_value_canonical uc w = true) (hm : ∀ x, x ∈ ws ↔ x ∈ ws') :
    setOf A ws = setOf A ws' :=
  map_ext_of_lookup_eq (setOf_canonical uc A ws h) (setOf_canonical uc A ws' h')
    (by rw [setOf_leaf, setOf_leaf]) fun x => by
      rw [setOf_lookup uc A ws x h, setOf_lookup uc A ws' x h']
      simp [hm x]

theorem setOf_typeof (A : SmtType) : ∀ ws : List SmtValue,
    (∀ w ∈ ws, __smtx_typeof_value w = A) →
    __smtx_typeof_map_value (setOf A ws) = .Map A .Bool
  | [], _ => rfl
  | w :: ws, h =>
    map_update_aux_typed (setOf_typeof A ws fun x hx => h x (.tail _ hx)) rfl (h w (.head _)) rfl

/-- The value of the set of a list is canonical. -/
theorem setOf_value_canonical (uc : SmtUSortDom) (A : SmtType) (ws : List SmtValue)
    (h : ∀ w ∈ ws, __smtx_value_canonical uc w = true) :
    __smtx_value_canonical uc (.Set (setOf A ws)) = true := by
  simp [__smtx_value_canonical, native_and, native_veq, setOf_canonical uc A ws h,
    setOf_default]

/-! The operators of the sets of Logos, on the sets of lists. -/

theorem op_rec_leaf (b : Bool) : ∀ (m1 m2 acc : SmtMap),
    smt_map_default_leaf (__smtx_set_op_rec b m1 m2 acc) = smt_map_default_leaf acc
  | .default _ _, _, _ => rfl
  | .cons e _ m1, m2, acc => by
    rw [__smtx_set_op_rec, op_rec_leaf b m1 m2]
    simp only [native_ite]
    split
    · rw [map_update_aux_default_leaf]
    · rfl

theorem singleton_eq (x : SmtValue) :
    __smtx_model_eval_set_singleton x = .Set (setOf (__smtx_typeof_value x) [x]) := by
  simp [__smtx_model_eval_set_singleton, setOf, __smtx_map_update_aux,
    __smtx_map_update_aux_no_default, native_ite, native_veq]

theorem lookup_true_iff (uc : SmtUSortDom) (A : SmtType) (ws : List SmtValue) (x : SmtValue)
    (h : ∀ w ∈ ws, __smtx_value_canonical uc w = true) :
    native_veq (__smtx_map_lookup (setOf A ws) x) (.Boolean true) = decide (x ∈ ws) := by
  rw [setOf_lookup uc A ws x h]; simp [native_veq]

/-- The union of the sets of two lists is the set of the two lists. -/
theorem union_eq (uc : SmtUSortDom) (A : SmtType) {xs ys : List SmtValue}
    (hx : ∀ w ∈ xs, __smtx_value_canonical uc w = true ∧ __smtx_typeof_value w = A)
    (hy : ∀ w ∈ ys, __smtx_value_canonical uc w = true ∧ __smtx_typeof_value w = A) :
    __smtx_model_eval_set_union (.Set (setOf A xs)) (.Set (setOf A ys)) =
      .Set (setOf A (xs ++ ys)) := by
  have hxc := fun w hw => (hx w hw).1
  have hyc := fun w hw => (hy w hw).1
  have hxyc : ∀ w ∈ xs ++ ys, __smtx_value_canonical uc w = true := fun w hw =>
    (List.mem_append.mp hw).elim (hxc w) (hyc w)
  have hxt := setOf_typeof A xs fun w hw => (hx w hw).2
  have hyt := setOf_typeof A ys fun w hw => (hy w hw).2
  have hcan := model_eval_set_union_canonical (uc := uc)
    (v1 := .Set (setOf A xs)) (v2 := .Set (setOf A ys))
    (setOf_value_canonical uc A xs hxc) (setOf_value_canonical uc A ys hyc)
  simp only [__smtx_model_eval_set_union, __smtx_set_union] at hcan ⊢
  simp only [value_canonical, __smtx_value_canonical, native_and, Bool.and_eq_true] at hcan
  congr 1
  refine map_ext_of_lookup_eq hcan.1 (setOf_canonical uc A _ hxyc)
    (by rw [op_rec_leaf, setOf_leaf, setOf_leaf]) fun v => ?_
  rw [SetMaps.set_union_lookup (uc := uc) _ _ A v hxt hyt (setOf_canonical uc A xs hxc)
    (setOf_canonical uc A ys hyc) (setOf_default A xs), lookup_true_iff uc A xs v hxc,
    setOf_lookup uc A ys v hyc, setOf_lookup uc A _ v hxyc]
  by_cases h1 : v ∈ xs <;> simp [native_ite, h1]

/-- The intersection of the sets of two lists is the set of the values of the first that are in
the second. -/
theorem inter_eq (uc : SmtUSortDom) (A : SmtType) {xs ys : List SmtValue}
    (hx : ∀ w ∈ xs, __smtx_value_canonical uc w = true ∧ __smtx_typeof_value w = A)
    (hy : ∀ w ∈ ys, __smtx_value_canonical uc w = true ∧ __smtx_typeof_value w = A) :
    __smtx_model_eval_set_inter (.Set (setOf A xs)) (.Set (setOf A ys)) =
      .Set (setOf A (xs.filter fun w => decide (w ∈ ys))) := by
  have hxc := fun w hw => (hx w hw).1
  have hyc := fun w hw => (hy w hw).1
  have hfc : ∀ w ∈ xs.filter (fun w => decide (w ∈ ys)), __smtx_value_canonical uc w = true :=
    fun w hw => hxc w (List.mem_filter.mp hw).1
  have hxt := setOf_typeof A xs fun w hw => (hx w hw).2
  have hyt := setOf_typeof A ys fun w hw => (hy w hw).2
  have hcan := model_eval_set_inter_canonical (uc := uc)
    (v1 := .Set (setOf A xs)) (v2 := .Set (setOf A ys))
    (setOf_value_canonical uc A xs hxc) (setOf_value_canonical uc A ys hyc)
  simp only [__smtx_model_eval_set_inter, __smtx_set_inter] at hcan ⊢
  simp only [value_canonical, __smtx_value_canonical, native_and, Bool.and_eq_true] at hcan
  congr 1
  refine map_ext_of_lookup_eq hcan.1 (setOf_canonical uc A _ hfc)
    (by rw [op_rec_leaf, setOf_leaf, hxt]; rfl) fun v => ?_
  rw [SetMaps.set_inter_lookup (uc := uc) _ _ A v hxt hyt (setOf_canonical uc A xs hxc)
    (setOf_default A xs), lookup_true_iff uc A xs v hxc, lookup_true_iff uc A ys v hyc,
    setOf_lookup uc A _ v hfc]
  by_cases h1 : v ∈ xs <;> by_cases h2 : v ∈ ys <;>
    simp [native_ite, native_and, h1, h2, List.mem_filter]

/-- The difference of the sets of two lists is the set of the values of the first that are not
in the second. -/
theorem minus_eq (uc : SmtUSortDom) (A : SmtType) {xs ys : List SmtValue}
    (hx : ∀ w ∈ xs, __smtx_value_canonical uc w = true ∧ __smtx_typeof_value w = A)
    (hy : ∀ w ∈ ys, __smtx_value_canonical uc w = true ∧ __smtx_typeof_value w = A) :
    __smtx_model_eval_set_minus (.Set (setOf A xs)) (.Set (setOf A ys)) =
      .Set (setOf A (xs.filter fun w => !decide (w ∈ ys))) := by
  have hxc := fun w hw => (hx w hw).1
  have hyc := fun w hw => (hy w hw).1
  have hfc : ∀ w ∈ xs.filter (fun w => !decide (w ∈ ys)),
      __smtx_value_canonical uc w = true :=
    fun w hw => hxc w (List.mem_filter.mp hw).1
  have hxt := setOf_typeof A xs fun w hw => (hx w hw).2
  have hyt := setOf_typeof A ys fun w hw => (hy w hw).2
  have hcan := model_eval_set_minus_canonical (uc := uc)
    (v1 := .Set (setOf A xs)) (v2 := .Set (setOf A ys))
    (setOf_value_canonical uc A xs hxc) (setOf_value_canonical uc A ys hyc)
  simp only [__smtx_model_eval_set_minus, __smtx_set_minus] at hcan ⊢
  simp only [value_canonical, __smtx_value_canonical, native_and, Bool.and_eq_true] at hcan
  congr 1
  refine map_ext_of_lookup_eq hcan.1 (setOf_canonical uc A _ hfc)
    (by rw [op_rec_leaf, setOf_leaf, hxt]; rfl) fun v => ?_
  rw [SetMaps.set_minus_lookup (uc := uc) _ _ A v hxt hyt (setOf_canonical uc A xs hxc)
    (setOf_default A xs), lookup_true_iff uc A xs v hxc, lookup_true_iff uc A ys v hyc,
    setOf_lookup uc A _ v hfc]
  by_cases h1 : v ∈ xs <;> by_cases h2 : v ∈ ys <;>
    simp [native_ite, native_and, native_not, h1, h2, List.mem_filter]

/-- A value is a member of the set of a list when it is in the list. -/
theorem member_eq (uc : SmtUSortDom) (A : SmtType) (ws : List SmtValue) (x : SmtValue)
    (h : ∀ w ∈ ws, __smtx_value_canonical uc w = true) :
    __smtx_model_eval_set_member x (.Set (setOf A ws)) = .Boolean (decide (x ∈ ws)) := by
  simp only [__smtx_model_eval_set_member, __smtx_map_select]
  exact setOf_lookup uc A ws x h

/-- The lists of two equal sets have the same members. -/
theorem setOf_inj (uc : SmtUSortDom) (A : SmtType) {ws ws' : List SmtValue}
    (h : ∀ w ∈ ws, __smtx_value_canonical uc w = true)
    (h' : ∀ w ∈ ws', __smtx_value_canonical uc w = true) (e : setOf A ws = setOf A ws')
    (x : SmtValue) : x ∈ ws ↔ x ∈ ws' := by
  have h1 := setOf_lookup uc A ws x h
  rw [e, setOf_lookup uc A ws' x h'] at h1
  exact (decide_eq_decide.mp (SmtValue.Boolean.inj h1)).symm

theorem subset_eq (uc : SmtUSortDom) (A : SmtType) {xs ys : List SmtValue}
    (hx : ∀ w ∈ xs, __smtx_value_canonical uc w = true ∧ __smtx_typeof_value w = A)
    (hy : ∀ w ∈ ys, __smtx_value_canonical uc w = true ∧ __smtx_typeof_value w = A) :
    __smtx_model_eval_set_subset (.Set (setOf A xs)) (.Set (setOf A ys)) =
      .Boolean (decide (∀ w ∈ xs, w ∈ ys)) := by
  have hxc : ∀ w ∈ xs, __smtx_value_canonical uc w = true := fun w hw => (hx w hw).1
  have hfc : ∀ w ∈ xs.filter (fun w => decide (w ∈ ys)), __smtx_value_canonical uc w = true :=
    fun w hw => hxc w (List.mem_filter.mp hw).1
  rw [__smtx_model_eval_set_subset, inter_eq uc A hx hy]
  simp only [__smtx_model_eval_eq, native_veq]
  congr 1
  apply decide_eq_decide.mpr
  constructor
  · intro e w hw
    have := (setOf_inj uc A hfc hxc (SmtValue.Set.inj e) w).mpr hw
    exact of_decide_eq_true (List.mem_filter.mp this).2
  · intro h
    rw [setOf_ext uc A hfc hxc fun w => ⟨fun hw => (List.mem_filter.mp hw).1,
      fun hw => List.mem_filter.mpr ⟨hw, decide_eq_true (h w hw)⟩⟩]

/-! ## The list of a set -/

/-- The keys of the entries of a map. -/
def keys : SmtMap → List SmtValue
  | .default _ _ => []
  | .cons k _ m => k :: keys m

/-- What a canonical set of elements of the sort `A` says of its map. -/
theorem set_map_inv (uc : SmtUSortDom) (A : SmtType) : ∀ m : SmtMap,
    __smtx_typeof_map_value m = .Map A .Bool → __smtx_map_canonical uc m = true →
    __smtx_map_get_default m = .Boolean false →
    smt_map_default_leaf m = .default A (.Boolean false) ∧
    (∀ x, __smtx_map_lookup m x = .Boolean (decide (x ∈ keys m))) ∧
    ∀ k ∈ keys m, __smtx_typeof_value k = A ∧ __smtx_value_canonical uc k = true ∧
      sizeOf k < sizeOf m
  | .default T e, ht, _, hd => by
    simp only [__smtx_typeof_map_value, SmtType.Map.injEq] at ht
    simp only [__smtx_map_get_default] at hd
    subst hd
    refine ⟨by simp [smt_map_default_leaf, ht.1], fun x => by simp [__smtx_map_lookup, keys],
      fun k hk => by simp [keys] at hk⟩
  | .cons k e m, ht, hc, hd => by
    simp only [__smtx_typeof_map_value] at ht
    by_cases hT : native_Teq (.Map (__smtx_typeof_value k) (__smtx_typeof_value e))
        (__smtx_typeof_map_value m) = true
    · simp only [hT, native_ite, ↓reduceIte] at ht
      have hT' : SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value e) =
          __smtx_typeof_map_value m := by simpa [native_Teq] using hT
      rw [ht, SmtType.Map.injEq] at hT'
      simp only [__smtx_map_canonical, native_and, Bool.and_eq_true, native_not,
        Bool.not_eq_true'] at hc
      obtain ⟨⟨⟨⟨hkc, _⟩, hmc⟩, _⟩, hne⟩ := hc
      simp only [__smtx_map_get_default] at hd
      obtain ⟨hl, hlook, hks⟩ := set_map_inv uc A m ht hmc hd
      obtain ⟨b, rfl⟩ := bool_value_canonical hT'.2
      have hb : b = true := by
        cases b
        · simp [hd, native_veq] at hne
        · rfl
      subst hb
      refine ⟨by simpa [smt_map_default_leaf] using hl, fun x => ?_, fun j hj => ?_⟩
      · simp only [__smtx_map_lookup, native_ite, keys, List.mem_cons]
        by_cases hkx : k = x
        · simp [native_veq, hkx]
        · have hne' : x ≠ k := fun h => hkx h.symm
          simp [native_veq, hkx, hne', hlook x]
      · simp only [keys, List.mem_cons] at hj
        rcases hj with rfl | hj
        · exact ⟨hT'.1, hkc, by simp only [SmtMap.cons.sizeOf_spec]; omega⟩
        · obtain ⟨h1, h2, h3⟩ := hks j hj
          exact ⟨h1, h2, by simp only [SmtMap.cons.sizeOf_spec]; omega⟩
    · simp [hT, native_ite] at ht

/-- A canonical set of elements of the sort `A` is the set of the list of its keys, which are
canonical values of the sort `A`, smaller than the set. -/
theorem set_inv (uc : SmtUSortDom) {A : SmtType} {m : SmtMap}
    (ht : __smtx_typeof_value (.Set m) = .Set A)
    (hc : __smtx_value_canonical uc (.Set m) = true) :
    m = setOf A (keys m) ∧ ∀ k ∈ keys m, __smtx_typeof_value k = A ∧
      __smtx_value_canonical uc k = true ∧ sizeOf k < sizeOf m := by
  have htm : __smtx_typeof_map_value m = .Map A .Bool := by
    simp only [__smtx_typeof_value] at ht
    rcases typeof_map_value_shape m with ⟨T, U, hm⟩ | hm
    · rw [hm] at ht ⊢
      cases U <;> simp [__smtx_map_to_set_type] at ht
      rw [ht]
    · simp [hm, __smtx_map_to_set_type] at ht
  simp only [__smtx_value_canonical, native_and, Bool.and_eq_true, native_veq,
    decide_eq_true_eq] at hc
  obtain ⟨hl, hlook, hks⟩ := set_map_inv uc A m htm hc.1 hc.2
  have hkc : ∀ w ∈ keys m, __smtx_value_canonical uc w = true := fun w hw => (hks w hw).2.1
  refine ⟨?_, hks⟩
  apply map_ext_of_lookup_eq hc.1 (setOf_canonical uc A _ hkc)
  · rw [hl, setOf_leaf]
  · intro x; rw [hlook x, setOf_lookup uc A _ x hkc]

/-! A set that is not empty is an element of it with the rest. -/

/-- The element that Logos chooses of a set that is not empty is one of its members. -/
theorem choose_mem {M : SmtModel} (huc : usort_dom_wf M.usortDom) {A : SmtType} {m : SmtMap}
    (ht : __smtx_typeof_value (.Set m) = .Set A)
    (hc : __smtx_value_canonical M.usortDom (.Set m) = true)
    (hne : m ≠ .default A (.Boolean false)) :
    __smtx_map_lookup m (native_eval_map_diff M m (.default A (.Boolean false))) =
      .Boolean true := by
  have htm : __smtx_typeof_map_value m = .Map A .Bool := set_map_value_typed ht
  simp only [__smtx_value_canonical, native_and, Bool.and_eq_true, native_veq,
    decide_eq_true_eq] at hc
  have hDiff := SetMaps.map_diff_selects_model_eval_eq_false_of_default_eq huc
    m (SmtMap.default A (SmtValue.Boolean false)) A SmtType.Bool
    htm (by simp [__smtx_typeof_map_value, __smtx_typeof_value])
    hc.1 (set_empty_map_canonical A) hc.2 (by decide)
    (by simp [__smtx_model_eval_eq, native_veq, hne])
  rcases bool_value_canonical
    (SetMaps.set_map_lookup_bool (i := native_eval_map_diff M m
      (SmtMap.default A (SmtValue.Boolean false))) htm) with ⟨b, hb⟩
  rw [hb]
  rw [__smtx_map_lookup] at hDiff
  erw [hb] at hDiff
  cases b <;> simp_all [__smtx_model_eval_eq, native_veq]

/-- A set is a member of it with the others. -/
theorem split_eq (uc : SmtUSortDom) {A : SmtType} {m : SmtMap}
    (ht : __smtx_typeof_value (.Set m) = .Set A)
    (hc : __smtx_value_canonical uc (.Set m) = true) {c : SmtValue}
    (hmem : __smtx_map_lookup m c = .Boolean true) :
    __smtx_model_eval_set_union
      (__smtx_model_eval_set_union (__smtx_model_eval_set_singleton c)
        (.Set (.default A (.Boolean false))))
      (__smtx_model_eval_set_minus (.Set m) (__smtx_model_eval_set_singleton c)) = .Set m := by
  obtain ⟨hm, hks⟩ := set_inv uc ht hc
  have hk : ∀ w ∈ keys m, __smtx_value_canonical uc w = true ∧ __smtx_typeof_value w = A :=
    fun w hw => ⟨(hks w hw).2.1, (hks w hw).1⟩
  have hck : c ∈ keys m := by
    rw [hm, setOf_lookup uc A _ c fun w hw => (hk w hw).1] at hmem
    simpa using hmem
  have h1 : ∀ w ∈ [c], __smtx_value_canonical uc w = true ∧ __smtx_typeof_value w = A := by
    intro w hw; rw [List.mem_singleton.mp hw]; exact hk c hck
  have h0 : ∀ w ∈ ([] : List SmtValue),
      __smtx_value_canonical uc w = true ∧ __smtx_typeof_value w = A := fun _ h => nomatch h
  have hf : ∀ w ∈ (keys m).filter (fun w => !decide (w ∈ [c])),
      __smtx_value_canonical uc w = true ∧ __smtx_typeof_value w = A :=
    fun w hw => hk w (List.mem_filter.mp hw).1
  have h10 : ∀ w ∈ [c] ++ [], __smtx_value_canonical uc w = true ∧ __smtx_typeof_value w = A := by
    simpa using h1
  have he : (SmtMap.default A (.Boolean false)) = setOf A [] := rfl
  rw [singleton_eq, (hk c hck).2, he, union_eq uc A h1 h0]
  conv => lhs; arg 2; rw [hm]
  rw [minus_eq uc A hk h1, union_eq uc A h10 hf]
  conv => rhs; rw [hm]
  congr 1
  apply setOf_ext uc A (fun w hw => ?_) (fun w hw => (hk w hw).1) fun x => ?_
  · rcases List.mem_append.mp hw with hw | hw
    · exact (h10 w hw).1
    · exact (hf w hw).1
  · by_cases hx : x = c
    · subst hx; simp [hck]
    · simp [hx]

end Inox.Bridge
