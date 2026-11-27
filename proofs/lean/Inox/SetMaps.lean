import Cpc.Proofs.TypePreservation.Helpers
import Cpc.Proofs.Canonical.Ops
import Cpc.Proofs.Canonical.Fresh

/-!
# Lookups in the sets of Logos

The lemmas on the maps of Logos that `Sets.lean` uses, copied from the modules of Logos that
prove them (`Cpc.Proofs.RuleSupport.SetsMemberSupport`, `SetsEvalOpSupport` and
`ArraySupport`, at the revision of Logos that the lakefile names). Those modules import the
proofs of the translation of Logos, which take most of an hour to build without a cache; these
lemmas only need its canonical maps.
-/

namespace Inox.Bridge.SetMaps

variable {uc : SmtUSortDom}

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

theorem map_cons_head_key_type
    {k v : SmtValue} {m : SmtMap} {A B : SmtType}
    (hTy : __smtx_typeof_map_value (SmtMap.cons k v m) = SmtType.Map A B) :
    __smtx_typeof_value k = A := by
  by_cases hEq :
      native_Teq (SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v))
        (__smtx_typeof_map_value m)
  · have hTail : __smtx_typeof_map_value m = SmtType.Map A B := by
      simpa [__smtx_typeof_map_value, native_ite, hEq] using hTy
    have hHead :
        SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v) =
          SmtType.Map A B := by
      have hEq' :
          SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v) =
            __smtx_typeof_map_value m := by
        simpa [native_Teq] using hEq
      exact hEq'.trans hTail
    cases hHead
    rfl
  · simp [__smtx_typeof_map_value, native_ite, hEq] at hTy

theorem map_cons_head_value_type
    {k v : SmtValue} {m : SmtMap} {A B : SmtType}
    (hTy : __smtx_typeof_map_value (SmtMap.cons k v m) = SmtType.Map A B) :
    __smtx_typeof_value v = B := by
  by_cases hEq :
      native_Teq (SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v))
        (__smtx_typeof_map_value m)
  · have hTail : __smtx_typeof_map_value m = SmtType.Map A B := by
      simpa [__smtx_typeof_map_value, native_ite, hEq] using hTy
    have hHead :
        SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v) =
          SmtType.Map A B := by
      have hEq' :
          SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v) =
            __smtx_typeof_map_value m := by
        simpa [native_Teq] using hEq
      exact hEq'.trans hTail
    cases hHead
    rfl
  · simp [__smtx_typeof_map_value, native_ite, hEq] at hTy

theorem map_cons_tail_type
    {k v : SmtValue} {m : SmtMap} {A B : SmtType}
    (hTy : __smtx_typeof_map_value (SmtMap.cons k v m) = SmtType.Map A B) :
    __smtx_typeof_map_value m = SmtType.Map A B := by
  by_cases hEq :
      native_Teq (SmtType.Map (__smtx_typeof_value k) (__smtx_typeof_value v))
        (__smtx_typeof_map_value m)
  · simpa [__smtx_typeof_map_value, native_ite, hEq] using hTy
  · simp [__smtx_typeof_map_value, native_ite, hEq] at hTy

theorem map_cons_tail_canonical
    {k v : SmtValue} {m : SmtMap}
    (hCan : __smtx_map_canonical uc (SmtMap.cons k v m) = true) :
    __smtx_map_canonical uc m = true := by
  have hParts := hCan
  simp [__smtx_map_canonical, SmtEval.native_and] at hParts
  exact hParts.1.1.2

theorem map_cons_head_key_canonical
    {k v : SmtValue} {m : SmtMap}
    (hCan : __smtx_map_canonical uc (SmtMap.cons k v m) = true) :
    value_canonical uc k := by
  have hParts := hCan
  simp [__smtx_map_canonical, SmtEval.native_and] at hParts
  exact hParts.1.1.1.1

theorem map_cons_tail_ordered
    {k v : SmtValue} {m : SmtMap}
    (hCan : __smtx_map_canonical uc (SmtMap.cons k v m) = true) :
    __smtx_map_entries_ordered_after k m = true := by
  have hParts := hCan
  simp [__smtx_map_canonical, SmtEval.native_and] at hParts
  exact hParts.1.2

theorem set_map_cons_entry_true
    {k v : SmtValue} {m : SmtMap} {A : SmtType}
    (hTy : __smtx_typeof_map_value (SmtMap.cons k v m) =
      SmtType.Map A SmtType.Bool)
    (hCan : __smtx_map_canonical uc (SmtMap.cons k v m) = true)
    (hDef : __smtx_map_get_default (SmtMap.cons k v m) = SmtValue.Boolean false) :
    v = SmtValue.Boolean true := by
  have hvTy : __smtx_typeof_value v = SmtType.Bool :=
    map_cons_head_value_type hTy
  rcases bool_value_canonical hvTy with ⟨b, rfl⟩
  cases b
  · have hNeDefault : native_veq (SmtValue.Boolean false)
        (__smtx_map_get_default m) = false := by
      have hParts := hCan
      simp [__smtx_map_canonical, SmtEval.native_and, SmtEval.native_not] at hParts
      exact hParts.2
    have hTailDef : __smtx_map_get_default m = SmtValue.Boolean false := by
      simpa [__smtx_map_get_default] using hDef
    simp [hTailDef, native_veq] at hNeDefault
  · rfl

theorem mss_op_lookup_acc
    (isInter : native_Bool) :
    ∀ {m1 m2 acc : SmtMap} {A : SmtType} {i : SmtValue},
      __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool ->
      __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool ->
      __smtx_typeof_map_value acc = SmtType.Map A SmtType.Bool ->
      __smtx_map_canonical uc m1 = true ->
      __smtx_map_canonical uc acc = true ->
      __smtx_map_get_default m1 = SmtValue.Boolean false ->
      __smtx_map_lookup (__smtx_set_op_rec isInter m1 m2 acc) i =
        native_ite
          (native_and
            (native_veq (__smtx_map_lookup m1 i) (SmtValue.Boolean true))
            (native_iff
              (native_veq (__smtx_map_lookup m2 i) (SmtValue.Boolean true))
              isInter))
          (SmtValue.Boolean true)
          (__smtx_map_lookup acc i)
  | SmtMap.default T efalse, m2, acc, A, i, hm1Ty, hm2Ty, haccTy, hm1Can,
      haccCan, hm1Def => by
      have hefalse : efalse = SmtValue.Boolean false := by
        simpa [__smtx_map_get_default] using hm1Def
      simp [__smtx_set_op_rec, __smtx_map_lookup, hefalse, native_veq,
        SmtEval.native_and, native_ite, native_iff]
  | SmtMap.cons e etrue m1, m2, acc, A, i, hm1Ty, hm2Ty, haccTy, hm1Can,
      haccCan, hm1Def => by
      have hmTailTy : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool :=
        map_cons_tail_type hm1Ty
      have heTy : __smtx_typeof_value e = A :=
        map_cons_head_key_type hm1Ty
      have hmTailCan : __smtx_map_canonical uc m1 = true :=
        map_cons_tail_canonical hm1Can
      have heCan : value_canonical uc e :=
        map_cons_head_key_canonical hm1Can
      have hOrdTail : __smtx_map_entries_ordered_after e m1 = true :=
        map_cons_tail_ordered hm1Can
      have hmTailDef : __smtx_map_get_default m1 = SmtValue.Boolean false := by
        simpa [__smtx_map_get_default] using hm1Def
      have hetrue : etrue = SmtValue.Boolean true :=
        set_map_cons_entry_true hm1Ty hm1Can hm1Def
      subst etrue
      by_cases hCond :
          native_veq (__smtx_map_lookup m2 e) (SmtValue.Boolean true) = isInter
      · let acc' :=
          __smtx_map_update_aux (__smtx_map_get_default acc) acc e
            (SmtValue.Boolean true)
        have hCondDec :
            decide (__smtx_map_lookup m2 e = SmtValue.Boolean true) = isInter := by
          simpa [native_veq] using hCond
        have hacc'Ty : __smtx_typeof_map_value acc' = SmtType.Map A SmtType.Bool := by
          dsimp [acc']
          exact map_canon_insert_typed haccTy heTy rfl
        have hacc'Can : __smtx_map_canonical uc acc' = true := by
          dsimp [acc']
          exact map_update_aux_canonical haccCan heCan (value_canonical_boolean true)
        have hRec := mss_op_lookup_acc isInter (m1 := m1) (m2 := m2) (acc := acc')
          (A := A) (i := i) hmTailTy hm2Ty hacc'Ty hmTailCan hacc'Can
          hmTailDef
        cases hei : native_veq e i
        · have hAccLookup :
              __smtx_map_lookup acc' i = __smtx_map_lookup acc i := by
            dsimp [acc']
            exact map_lookup_update_aux_other haccCan hei
          simpa [__smtx_set_op_rec, hCond, hCondDec, __smtx_map_lookup,
            native_ite, native_iff, hei, hAccLookup] using hRec
        · have heiEq : e = i := eq_of_native_veq_true hei
          subst i
          have hTailLookup :
              __smtx_map_lookup m1 e = SmtValue.Boolean false := by
            calc
              __smtx_map_lookup m1 e = __smtx_map_get_default m1 :=
                map_lookup_eq_default_of_entries_ordered_after hmTailCan hOrdTail
              _ = SmtValue.Boolean false := hmTailDef
          have hAccLookup :
              __smtx_map_lookup acc' e = SmtValue.Boolean true := by
            dsimp [acc']
            exact map_lookup_update_aux_same haccCan
          simpa [__smtx_set_op_rec, hCond, hCondDec, __smtx_map_lookup,
            native_ite, native_iff, native_veq, hTailLookup, hAccLookup,
            SmtEval.native_and] using hRec
      · have hRec := mss_op_lookup_acc isInter (m1 := m1) (m2 := m2) (acc := acc)
          (A := A) (i := i) hmTailTy hm2Ty haccTy hmTailCan haccCan hmTailDef
        have hCondDec :
            ¬ decide (__smtx_map_lookup m2 e = SmtValue.Boolean true) = isInter := by
          intro h
          exact hCond (by simpa [native_veq] using h)
        cases hei : native_veq e i
        · -- the two sides differ only in a stale `Decidable` instance, which
          -- `simpa`'s closing step no longer accepts but `exact` still does.
          simp only [__smtx_set_op_rec, hCond, __smtx_map_lookup,
            native_ite, native_iff, hei] at hRec ⊢
          exact hRec
        · have heiEq : e = i := eq_of_native_veq_true hei
          subst i
          have hTailLookup :
              __smtx_map_lookup m1 e = SmtValue.Boolean false := by
            calc
              __smtx_map_lookup m1 e = __smtx_map_get_default m1 :=
                map_lookup_eq_default_of_entries_ordered_after hmTailCan hOrdTail
              _ = SmtValue.Boolean false := hmTailDef
          simpa [__smtx_set_op_rec, hCond, hCondDec, __smtx_map_lookup,
            native_ite, native_iff, native_veq, hTailLookup,
            SmtEval.native_and] using hRec

/-- Every lookup into a bool-valued map of type `Map A Bool` yields a Bool
    value, regardless of the index type. -/
theorem set_map_lookup_bool :
    ∀ {m : SmtMap} {A : SmtType} {i : SmtValue},
      __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool ->
        __smtx_typeof_value (__smtx_map_lookup m i) = SmtType.Bool
  | SmtMap.default T e, A, i, hTy => by
      have heTy : __smtx_typeof_value e = SmtType.Bool := by
        have h : SmtType.Map T (__smtx_typeof_value e) =
            SmtType.Map A SmtType.Bool := by
          simpa [__smtx_typeof_map_value] using hTy
        exact (SmtType.Map.injEq _ _ _ _ ▸ h).2
      simpa [__smtx_map_lookup] using heTy
  | SmtMap.cons k v m, A, i, hTy => by
      have hmTy : __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool :=
        map_cons_tail_type hTy
      have hvTy : __smtx_typeof_value v = SmtType.Bool :=
        map_cons_head_value_type hTy
      cases hki : native_veq k i
      · simpa [__smtx_map_lookup, native_ite, hki] using
          set_map_lookup_bool (m := m) (A := A) (i := i) hmTy
      · simpa [__smtx_map_lookup, native_ite, hki] using hvTy

/-- Lookup of a union of two canonical, Bool-valued, default-false set maps. -/
theorem set_union_lookup
    (m1 m2 : SmtMap) (A : SmtType) (v : SmtValue)
    (h1Ty : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool)
    (h2Ty : __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool)
    (h1Can : __smtx_map_canonical uc m1 = true)
    (h2Can : __smtx_map_canonical uc m2 = true)
    (h1Def : __smtx_map_get_default m1 = SmtValue.Boolean false) :
    __smtx_map_lookup
        (__smtx_set_op_rec false m1
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
            (SmtValue.Boolean false)) m2) v =
      native_ite
        (native_veq (__smtx_map_lookup m1 v) (SmtValue.Boolean true))
        (SmtValue.Boolean true)
        (__smtx_map_lookup m2 v) := by
  have hEmptyTy :
      __smtx_typeof_map_value
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
            (SmtValue.Boolean false)) = SmtType.Map A SmtType.Bool := by
    rw [h1Ty]
    simp [__smtx_index_typeof_map, __smtx_typeof_map_value, __smtx_typeof_value]
  have hRec :=
    mss_op_lookup_acc false (m1 := m1)
      (m2 := SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
        (SmtValue.Boolean false))
      (acc := m2) (A := A) (i := v) h1Ty hEmptyTy h2Ty h1Can h2Can h1Def
  rw [hRec]
  simp [__smtx_map_lookup, native_veq, native_iff, SmtEval.native_and, native_ite]

theorem map_canonical_default (A : SmtType) :
    __smtx_map_canonical uc (SmtMap.default A (SmtValue.Boolean false)) = true := by
  simp only [__smtx_map_canonical, __smtx_map_default_canonical, __smtx_value_canonical,
    __smtx_typeof_value, __smtx_type_default, native_veq, native_and,
    Bool.and_true]
  cases __smtx_type_bounded uc false A <;> simp [native_ite]

/-- Lookup of an intersection of two canonical, Bool-valued set maps. -/
theorem set_inter_lookup
    (m1 m2 : SmtMap) (A : SmtType) (v : SmtValue)
    (h1Ty : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool)
    (h2Ty : __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool)
    (h1Can : __smtx_map_canonical uc m1 = true)
    (h1Def : __smtx_map_get_default m1 = SmtValue.Boolean false) :
    __smtx_map_lookup
        (__smtx_set_op_rec true m1 m2
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
            (SmtValue.Boolean false))) v =
      native_ite
        (native_and (native_veq (__smtx_map_lookup m1 v) (SmtValue.Boolean true))
          (native_veq (__smtx_map_lookup m2 v) (SmtValue.Boolean true)))
        (SmtValue.Boolean true) (SmtValue.Boolean false) := by
  have hAccTy :
      __smtx_typeof_map_value
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
            (SmtValue.Boolean false)) = SmtType.Map A SmtType.Bool := by
    rw [h1Ty]
    simp [__smtx_index_typeof_map, __smtx_typeof_map_value, __smtx_typeof_value]
  rw [mss_op_lookup_acc true (m1 := m1) (m2 := m2)
    (acc := SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
      (SmtValue.Boolean false))
    (A := A) (i := v) h1Ty h2Ty hAccTy h1Can (map_canonical_default _) h1Def]
  simp [__smtx_map_lookup, native_veq, native_iff, SmtEval.native_and, native_ite]

/-- Lookup of a difference of two canonical, Bool-valued set maps. -/
theorem set_minus_lookup
    (m1 m2 : SmtMap) (A : SmtType) (v : SmtValue)
    (h1Ty : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool)
    (h2Ty : __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool)
    (h1Can : __smtx_map_canonical uc m1 = true)
    (h1Def : __smtx_map_get_default m1 = SmtValue.Boolean false) :
    __smtx_map_lookup
        (__smtx_set_op_rec false m1 m2
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
            (SmtValue.Boolean false))) v =
      native_ite
        (native_and (native_veq (__smtx_map_lookup m1 v) (SmtValue.Boolean true))
          (native_not (native_veq (__smtx_map_lookup m2 v) (SmtValue.Boolean true))))
        (SmtValue.Boolean true) (SmtValue.Boolean false) := by
  have hAccTy :
      __smtx_typeof_map_value
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
            (SmtValue.Boolean false)) = SmtType.Map A SmtType.Bool := by
    rw [h1Ty]
    simp [__smtx_index_typeof_map, __smtx_typeof_map_value, __smtx_typeof_value]
  rw [mss_op_lookup_acc false (m1 := m1) (m2 := m2)
    (acc := SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
      (SmtValue.Boolean false))
    (A := A) (i := v) h1Ty h2Ty hAccTy h1Can (map_canonical_default _) h1Def]
  simp [__smtx_map_lookup, native_veq, native_iff, SmtEval.native_and, native_ite,
    native_not]

theorem model_eval_eq_false_of_native_veq_false_non_reglan
    {v1 v2 : SmtValue} {B : SmtType}
    (hTy1 : __smtx_typeof_value v1 = B)
    (hTy2 : __smtx_typeof_value v2 = B)
    (hB : B ≠ SmtType.RegLan)
    (hNe : native_veq v1 v2 = false) :
    __smtx_model_eval_eq v1 v2 = SmtValue.Boolean false := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_eq, native_veq, __smtx_typeof_value] at hTy1 hTy2 hB hNe ⊢
  all_goals try assumption
  exact False.elim (hB hTy1.symm)

theorem map_default_eq_type_default_of_finite_domain :
    ∀ {m : SmtMap} {A B : SmtType},
      __smtx_typeof_map_value m = SmtType.Map A B ->
        __smtx_map_canonical uc m = true ->
          __smtx_is_finite_type uc A = true ->
            __smtx_map_get_default m = __smtx_type_default B
  | SmtMap.default T e, A, B, hTy, hCan, hFin => by
      cases hTy
      have hParts := hCan
      simp [__smtx_map_canonical, __smtx_map_default_canonical, hFin,
        native_ite, SmtEval.native_and] at hParts
      exact Smtm.eq_of_native_veq_true hParts.1
  | SmtMap.cons i e m, A, B, hTy, hCan, hFin => by
      have hmTy : __smtx_typeof_map_value m = SmtType.Map A B := by
        by_cases hEq :
            native_Teq
              (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
              (__smtx_typeof_map_value m)
        · simpa [__smtx_typeof_map_value, native_ite, hEq] using hTy
        · simp [__smtx_typeof_map_value, native_ite, hEq] at hTy
      have hmCan : __smtx_map_canonical uc m = true := by
        have hParts := hCan
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        exact hParts.1.1.2
      simpa [__smtx_map_get_default] using
        map_default_eq_type_default_of_finite_domain hmTy hmCan hFin

theorem map_default_leaf_eq_default_of_type :
    ∀ {m : SmtMap} {A B : SmtType},
      __smtx_typeof_map_value m = SmtType.Map A B ->
        Smtm.smt_map_default_leaf m =
          SmtMap.default A (__smtx_map_get_default m)
  | SmtMap.default T e, A, B, hTy => by
      cases hTy
      rfl
  | SmtMap.cons i e m, A, B, hTy => by
      have hmTy : __smtx_typeof_map_value m = SmtType.Map A B := by
        by_cases hEq :
            native_Teq
              (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
              (__smtx_typeof_map_value m)
        · simpa [__smtx_typeof_map_value, native_ite, hEq] using hTy
        · simp [__smtx_typeof_map_value, native_ite, hEq] at hTy
      simpa [Smtm.smt_map_default_leaf, __smtx_map_get_default] using
        map_default_leaf_eq_default_of_type hmTy

theorem map_default_leaf_eq_of_get_default_eq
    {m1 m2 : SmtMap} {A B : SmtType}
    (h1 : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (h2 : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (hDef : __smtx_map_get_default m1 = __smtx_map_get_default m2) :
    Smtm.smt_map_default_leaf m1 = Smtm.smt_map_default_leaf m2 := by
  rw [map_default_leaf_eq_default_of_type h1,
    map_default_leaf_eq_default_of_type h2, hDef]

theorem map_lookup_eq_default_of_not_typed_canonical (huc : usort_dom_wf uc) :
    ∀ {m : SmtMap} {A B : SmtType} {v : SmtValue},
      __smtx_typeof_map_value m = SmtType.Map A B ->
        __smtx_map_canonical uc m = true ->
          ¬ (__smtx_typeof_value v = A ∧
              __smtx_value_canonical uc v = true) ->
            __smtx_map_lookup m v = __smtx_map_get_default m
  | SmtMap.default T e, A, B, v, _hTy, _hCan, _hNot => by
      simp [__smtx_map_lookup, __smtx_map_get_default]
  | SmtMap.cons i e m, A, B, v, hTy, hCan, hNot => by
      have hmTy : __smtx_typeof_map_value m = SmtType.Map A B := by
        by_cases hEqTy :
            native_Teq
              (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
              (__smtx_typeof_map_value m)
        · simpa [__smtx_typeof_map_value, native_ite, hEqTy] using hTy
        · simp [__smtx_typeof_map_value, native_ite, hEqTy] at hTy
      have hEqTy' :
          SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e) =
            __smtx_typeof_map_value m := by
        by_cases hEqTy :
            native_Teq
              (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
              (__smtx_typeof_map_value m)
        · simpa [native_Teq] using hEqTy
        · simp [__smtx_typeof_map_value, native_ite, hEqTy] at hTy
      have hHead :
          SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e) =
            SmtType.Map A B := hEqTy'.trans hmTy
      have hiTy : __smtx_typeof_value i = A := by
        cases hHead
        rfl
      have hiCan : __smtx_value_canonical uc i = true := by
        have hParts := hCan
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        exact hParts.1.1.1.1
      have hmCan : __smtx_map_canonical uc m = true := by
        have hParts := hCan
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        exact hParts.1.1.2
      by_cases hivTrue : native_veq i v = true
      · have hiv : i = v := Smtm.eq_of_native_veq_true hivTrue
        subst v
        exact False.elim (hNot ⟨hiTy, hiCan⟩)
      · have hivFalse : native_veq i v = false := by
          cases hBool : native_veq i v <;> simp [hBool] at hivTrue ⊢
        have hRec :=
          map_lookup_eq_default_of_not_typed_canonical huc hmTy hmCan hNot
        simpa [__smtx_map_lookup, __smtx_map_get_default, native_ite,
          hivFalse] using hRec

/--
Fresh-index witness needed only for the infinite-domain branch of array
extensionality.  Discharged by the `Canonical.Fresh` freshness stack; the
residual datatype obligations live behind
`Smtm.infinite_datatype_large_witness` /
`Smtm.finite_nonunit_datatype_nondefault_value`.
-/
theorem fresh_default_lookup_for_infinite_map_domain (huc : usort_dom_wf uc)
    (m1 m2 : SmtMap)
    (A B : SmtType)
    (_hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (_hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (_hm1Can : __smtx_map_canonical uc m1 = true)
    (_hm2Can : __smtx_map_canonical uc m2 = true)
    (_hAInh : __smtx_inhabited_type A = true)
    (_hARec : __smtx_type_wf_rec A = true)
    (_hInfinite : __smtx_is_finite_type uc A = false) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = A ∧
        __smtx_value_canonical uc i = true ∧
          __smtx_map_lookup m1 i = __smtx_map_get_default m1 ∧
            __smtx_map_lookup m2 i = __smtx_map_get_default m2 :=
  Smtm.fresh_default_lookup_for_infinite_map_domain huc m1 m2 A B
    _hm1Ty _hm2Ty _hm1Can _hm2Can _hAInh _hARec _hInfinite

theorem map_defaults_eq_of_no_typed_canonical_lookup_diff (huc : usort_dom_wf uc)
    {m1 m2 : SmtMap} {A B : SmtType}
    (hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (hm1Can : __smtx_map_canonical uc m1 = true)
    (hm2Can : __smtx_map_canonical uc m2 = true)
    (hAInh : __smtx_inhabited_type A = true)
    (hARec : __smtx_type_wf_rec A = true)
    (hNoDiff :
      ¬ ∃ i : SmtValue,
        __smtx_typeof_value i = A ∧
          __smtx_value_canonical uc i = true ∧
            native_veq (__smtx_map_lookup m1 i)
              (__smtx_map_lookup m2 i) = false) :
    __smtx_map_get_default m1 = __smtx_map_get_default m2 := by
  cases hFin : __smtx_is_finite_type uc A
  · rcases fresh_default_lookup_for_infinite_map_domain huc
        m1 m2 A B hm1Ty hm2Ty hm1Can hm2Can hAInh hARec hFin with
      ⟨i, hiTy, hiCan, hiLookup1, hiLookup2⟩
    cases hVeq :
        native_veq (__smtx_map_get_default m1)
          (__smtx_map_get_default m2)
    · exact False.elim
        (hNoDiff ⟨i, hiTy, hiCan, by
          simpa [hiLookup1, hiLookup2] using hVeq⟩)
    · exact Smtm.eq_of_native_veq_true hVeq
  · calc
      __smtx_map_get_default m1 = __smtx_type_default B :=
        map_default_eq_type_default_of_finite_domain hm1Ty hm1Can hFin
      _ = __smtx_map_get_default m2 :=
        (map_default_eq_type_default_of_finite_domain hm2Ty hm2Can hFin).symm

theorem map_diff_typed_canonical_lookup_witness (huc : usort_dom_wf uc)
    (m1 m2 : SmtMap)
    (A B : SmtType)
    (hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (hm1Can : __smtx_map_canonical uc m1 = true)
    (hm2Can : __smtx_map_canonical uc m2 = true)
    (hAInh : __smtx_inhabited_type A = true)
    (hARec : __smtx_type_wf_rec A = true)
    (hNe : __smtx_model_eval_eq (SmtValue.Map m1) (SmtValue.Map m2) =
      SmtValue.Boolean false) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = A ∧
        __smtx_value_canonical uc i = true ∧
          native_veq (__smtx_map_lookup m1 i)
            (__smtx_map_lookup m2 i) = false := by
  by_cases hDiff :
      ∃ i : SmtValue,
        __smtx_typeof_value i = A ∧
          __smtx_value_canonical uc i = true ∧
            native_veq (__smtx_map_lookup m1 i)
              (__smtx_map_lookup m2 i) = false
  · exact hDiff
  · exfalso
    have hDefaultEq :
        __smtx_map_get_default m1 = __smtx_map_get_default m2 :=
      map_defaults_eq_of_no_typed_canonical_lookup_diff huc
        hm1Ty hm2Ty hm1Can hm2Can hAInh hARec hDiff
    have hLeafEq :
        Smtm.smt_map_default_leaf m1 = Smtm.smt_map_default_leaf m2 :=
      map_default_leaf_eq_of_get_default_eq hm1Ty hm2Ty hDefaultEq
    have hLookupEq :
        ∀ v : SmtValue, __smtx_map_lookup m1 v = __smtx_map_lookup m2 v := by
      intro v
      by_cases hv :
          __smtx_typeof_value v = A ∧ __smtx_value_canonical uc v = true
      · have hNotFalse :
            native_veq (__smtx_map_lookup m1 v)
              (__smtx_map_lookup m2 v) ≠ false := by
          intro hFalse
          exact hDiff ⟨v, hv.1, hv.2, hFalse⟩
        cases hVeq :
            native_veq (__smtx_map_lookup m1 v) (__smtx_map_lookup m2 v)
        · exact False.elim (hNotFalse hVeq)
        · exact Smtm.eq_of_native_veq_true hVeq
      · calc
          __smtx_map_lookup m1 v = __smtx_map_get_default m1 :=
            map_lookup_eq_default_of_not_typed_canonical huc hm1Ty hm1Can hv
          _ = __smtx_map_get_default m2 := hDefaultEq
          _ = __smtx_map_lookup m2 v :=
            (map_lookup_eq_default_of_not_typed_canonical huc hm2Ty hm2Can hv).symm
    have hEq : m1 = m2 :=
      Smtm.map_ext_of_lookup_eq hm1Can hm2Can hLeafEq hLookupEq
    subst m2
    simp [__smtx_model_eval_eq, native_veq] at hNe

theorem map_diff_selects_model_eval_eq_false_of_default_eq
    {M : SmtModel} (huc : usort_dom_wf M.usortDom)
    (m1 m2 : SmtMap)
    (A B : SmtType)
    (hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (hm1Can : __smtx_map_canonical M.usortDom m1 = true)
    (hm2Can : __smtx_map_canonical M.usortDom m2 = true)
    (hDefaultEq : __smtx_map_get_default m1 = __smtx_map_get_default m2)
    (hBNeRegLan : B ≠ SmtType.RegLan)
    (hNe : __smtx_model_eval_eq (SmtValue.Map m1) (SmtValue.Map m2) =
      SmtValue.Boolean false) :
    __smtx_model_eval_eq
        (__smtx_map_lookup m1 (native_eval_map_diff M m1 m2))
        (__smtx_map_lookup m2 (native_eval_map_diff M m1 m2)) =
      SmtValue.Boolean false := by
  classical
  change
    __smtx_model_eval_eq
        (__smtx_map_lookup m1 (native_eval_map_diff M m1 m2))
        (__smtx_map_lookup m2 (native_eval_map_diff M m1 m2)) =
      SmtValue.Boolean false
  rw [hm1Ty, hm2Ty]
  simp [native_ite, native_Teq, SmtEval.native_and]
  by_cases hDiff :
      ∃ i : SmtValue,
        __smtx_typeof_value i = A ∧
          __smtx_value_canonical M.usortDom i = true ∧
            native_veq (__smtx_map_lookup m1 i)
              (__smtx_map_lookup m2 i) = false
  · have hSpec := Classical.choose_spec hDiff
    have hLookup1Ty :
        __smtx_typeof_value
            (__smtx_map_lookup m1 (Classical.choose hDiff)) = B :=
      Smtm.map_lookup_typed hm1Ty hSpec.1
    have hLookup2Ty :
        __smtx_typeof_value
            (__smtx_map_lookup m2 (Classical.choose hDiff)) = B :=
      Smtm.map_lookup_typed hm2Ty hSpec.1
    have hFalse :
        __smtx_model_eval_eq
            (__smtx_map_lookup m1 (Classical.choose hDiff))
            (__smtx_map_lookup m2 (Classical.choose hDiff)) =
          SmtValue.Boolean false :=
      model_eval_eq_false_of_native_veq_false_non_reglan
        hLookup1Ty hLookup2Ty hBNeRegLan hSpec.2.2
    simpa [hDiff] using hFalse
  · exfalso
    have hLeafEq :
        Smtm.smt_map_default_leaf m1 = Smtm.smt_map_default_leaf m2 :=
      map_default_leaf_eq_of_get_default_eq hm1Ty hm2Ty hDefaultEq
    have hLookupEq :
        ∀ v : SmtValue, __smtx_map_lookup m1 v = __smtx_map_lookup m2 v := by
      intro v
      by_cases hv :
          __smtx_typeof_value v = A ∧ __smtx_value_canonical M.usortDom v = true
      · have hNotFalse :
            native_veq (__smtx_map_lookup m1 v)
              (__smtx_map_lookup m2 v) ≠ false := by
          intro hFalse
          exact hDiff ⟨v, hv.1, hv.2, hFalse⟩
        cases hVeq :
            native_veq (__smtx_map_lookup m1 v) (__smtx_map_lookup m2 v)
        · exact False.elim (hNotFalse hVeq)
        · exact Smtm.eq_of_native_veq_true hVeq
      · calc
          __smtx_map_lookup m1 v = __smtx_map_get_default m1 :=
            map_lookup_eq_default_of_not_typed_canonical huc hm1Ty hm1Can hv
          _ = __smtx_map_get_default m2 := hDefaultEq
          _ = __smtx_map_lookup m2 v :=
            (map_lookup_eq_default_of_not_typed_canonical huc hm2Ty hm2Can hv).symm
    have hEq : m1 = m2 :=
      Smtm.map_ext_of_lookup_eq hm1Can hm2Can hLeafEq hLookupEq
    subst m2
    simp [__smtx_model_eval_eq, native_veq] at hNe

end Inox.Bridge.SetMaps
