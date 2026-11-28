import Inox.Simplified

/-!
# Steps up to the values of closures

A step of a simplification may rewrite a subterm into one whose value is not the same, but the
same up to closures that have the same values, as a call whose result is a lambda over the
parameters of the call is the lambda where the parameters are the arguments. Values are related
(`Ext`) where they are the same, constructions of related fields, sets of related elements, or
closures that have related values at the same arguments and fuel. The equality of the semantics
compares related values alike (`ext_same`), where the sorts have no equalities of their own, as
it compares closures by their values.

A term refines another up to closures (`RefinesX`) where its values are related to those of the
other. Comparisons, negations, selectors, applications, memberships and insertions keep that
(`rewriteX_refines`), and at a Boolean it is a refinement (`ext_bool`). The steps that hold
up to closures are calls with literal arguments to the values of their bodies (`callCheck`), the
renamings of lambdas and of the closures in sets (`vfCheck`), applications of lambdas to
literals (`betaCheck`), renamings of lets of literals (`letLitCheck`) and memberships of
closures (`memberCheck`). `stepsApplyX` applies the steps of a simplification with those of
`Inox.Simplified` and these.
-/

namespace Inox.Closures

open Inox.Semantics Inox.Simplified

/-- Whether the program compares functions by their values. -/
def funEq : Program → Bool
  | .Program _ _ _ _ .ExtensionalEquality => true
  | _ => false

section
variable (O : Oracle) (P : Program)

mutual
/-- Values that are the same up to closures that have related values at the same arguments,
where the first has one, and that have values at the same arguments where the program compares
functions. -/
inductive Ext : Value → Value → Prop where
  | refl (v : Value) : Ext v v
  | adt {c : Id} {tps : List Ty} {vs vs' : List Value} (h : Exts vs vs') :
      Ext (.ADTV c tps vs) (.ADTV c tps vs')
  | set {B B' : Ty} {xs xs' : List Value} (h : Exts xs xs') : Ext (.SetV B xs) (.SetV B' xs')
  | clo {ps ps' : List Param} {b b' : Expr} {e e' : Env}
      (hty : funEq P = true →
        ∀ vs, O.params_have_types P e vs ps = O.params_have_types P e' vs ps')
      (hok : ∀ fuel vs, (∃ a, apply O P fuel (.ClosureV ps b e) vs = .Ok a) →
        (∃ a', apply O P fuel (.ClosureV ps' b' e') vs = .Ok a'))
      (hback : funEq P = true → ∀ fuel vs,
        (∃ a', apply O P fuel (.ClosureV ps' b' e') vs = .Ok a') →
          (∃ a, apply O P fuel (.ClosureV ps b e) vs = .Ok a))
      (hr : ∀ fuel vs a a', apply O P fuel (.ClosureV ps b e) vs = .Ok a →
        apply O P fuel (.ClosureV ps' b' e') vs = .Ok a' → Ext a a') :
      Ext (.ClosureV ps b e) (.ClosureV ps' b' e')
/-- Lists of related values, position by position. -/
inductive Exts : List Value → List Value → Prop where
  | nil : Exts [] []
  | cons {v v' : Value} {vs vs' : List Value} (h : Ext v v') (hs : Exts vs vs') :
      Exts (v :: vs) (v' :: vs')
end

/-- Values that the equality of the semantics compares alike. -/
def Same (a a' : Value) : Prop :=
  ∀ x, O.value_eq P x a = O.value_eq P x a' ∧ O.value_eq P a x = O.value_eq P a' x

/-- Lists of values that the equality compares alike, position by position. -/
inductive Sames : List Value → List Value → Prop where
  | nil : Sames [] []
  | cons {v v' : Value} {vs vs' : List Value} (h : Same O P v v') (hs : Sames vs vs') :
      Sames (v :: vs) (v' :: vs')

end

section
variable {O : Oracle} {P : Program}

theorem vals_right (hO : O.Sound) : ∀ {xs xs' : List Value}, Sames O P xs xs' →
    ∀ ys, O.values_eq P ys xs = O.values_eq P ys xs'
  | [], [], .nil, ys => rfl
  | x :: xs, x' :: xs', .cons h hs, ys => by
    rw [hO.values_eq, hO.values_eq]
    cases ys with
    | nil => rfl
    | cons y ys => simp only [(h y).1, vals_right hO hs ys]

theorem vals_left (hO : O.Sound) : ∀ {xs xs' : List Value}, Sames O P xs xs' →
    ∀ ys, O.values_eq P xs ys = O.values_eq P xs' ys
  | [], [], .nil, ys => rfl
  | x :: xs, x' :: xs', .cons h hs, ys => by
    rw [hO.values_eq, hO.values_eq]
    cases ys with
    | nil => rfl
    | cons y ys => simp only [(h y).2, vals_left hO hs ys]

theorem contains_list (hO : O.Sound) : ∀ {xs xs' : List Value}, Sames O P xs xs' →
    ∀ v, O.set_contains P xs v = O.set_contains P xs' v
  | [], [], .nil, v => rfl
  | x :: xs, x' :: xs', .cons h hs, v => by
    rw [hO.set_contains, hO.set_contains]
    simp only [(h v).2, contains_list hO hs v]

theorem contains_elem (hO : O.Sound) {v v' : Value} (h : Same O P v v') :
    ∀ ys, O.set_contains P ys v = O.set_contains P ys v'
  | [] => by rw [hO.set_contains, hO.set_contains]
  | y :: ys => by
    rw [hO.set_contains, hO.set_contains]
    simp only [(h y).1, contains_elem hO h ys]

theorem subset_right (hO : O.Sound) {xs xs' : List Value} (h : Sames O P xs xs') :
    ∀ ys, O.subset P ys xs = O.subset P ys xs'
  | [] => by rw [hO.subset, hO.subset]
  | y :: ys => by
    rw [hO.subset, hO.subset]
    simp only [contains_list hO h y, subset_right hO h ys]

theorem subset_left (hO : O.Sound) : ∀ {xs xs' : List Value}, Sames O P xs xs' →
    ∀ ys, O.subset P xs ys = O.subset P xs' ys
  | [], [], .nil, ys => rfl
  | x :: xs, x' :: xs', .cons h hs, ys => by
    rw [hO.subset, hO.subset]
    simp only [contains_elem hO h ys, subset_left hO hs ys]

/-- Closures that have values at the same arguments and fuel, which are compared alike, are
compared alike to a value, as the second operand of the comparison of closures. -/
theorem ce_right (hO : O.Sound) {f g g' : Value}
    (hok : ∀ fuel vs, (∃ a, apply O P fuel g vs = .Ok a) ↔
      (∃ a', apply O P fuel g' vs = .Ok a'))
    (hr : ∀ fuel vs a a', apply O P fuel g vs = .Ok a → apply O P fuel g' vs = .Ok a' →
      Same O P a a') :
    O.closures_equal P f g = O.closures_equal P f g' := by
  rw [hO.closures_equal, hO.closures_equal]
  cases f with
  | ClosureV ps b e =>
    simp only
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
      decide_eq_false_iff_not]
    refine forall_congr' fun vs => or_congr Iff.rfl (or_congr ?_ ?_)
    · refine forall_congr' fun fuel => ?_
      constructor
      · intro h a
        refine ⟨(h a).1, fun ha => ?_⟩
        obtain ⟨a0, ha0⟩ := (hok fuel vs).2 ⟨a, ha⟩
        exact (h a0).2 ha0
      · intro h a
        refine ⟨(h a).1, fun ha => ?_⟩
        obtain ⟨a0, ha0⟩ := (hok fuel vs).1 ⟨a, ha⟩
        exact (h a0).2 ha0
    · constructor
      · rintro ⟨fuel, a, c, ⟨ha, hc⟩, he⟩
        obtain ⟨c', hc'⟩ := (hok fuel vs).1 ⟨c, hc⟩
        exact ⟨fuel, a, c', ⟨ha, hc'⟩, by rw [← ((hr fuel vs c c' hc hc') a).1]; exact he⟩
      · rintro ⟨fuel, a, c', ⟨ha, hc'⟩, he⟩
        obtain ⟨c, hc⟩ := (hok fuel vs).2 ⟨c', hc'⟩
        exact ⟨fuel, a, c, ⟨ha, hc⟩, by rw [((hr fuel vs c c' hc hc') a).1]; exact he⟩
  | _ => rfl

/-- `ce_right`, as the first operand. -/
theorem ce_left (hO : O.Sound) {ps ps' : List Param} {b b' : Expr} {e e' : Env} {g : Value}
    (hty : ∀ vs, O.params_have_types P e vs ps = O.params_have_types P e' vs ps')
    (hok : ∀ fuel vs, (∃ a, apply O P fuel (.ClosureV ps b e) vs = .Ok a) ↔
      (∃ a', apply O P fuel (.ClosureV ps' b' e') vs = .Ok a'))
    (hr : ∀ fuel vs a a', apply O P fuel (.ClosureV ps b e) vs = .Ok a →
      apply O P fuel (.ClosureV ps' b' e') vs = .Ok a' → Same O P a a') :
    O.closures_equal P (.ClosureV ps b e) g = O.closures_equal P (.ClosureV ps' b' e') g := by
  rw [hO.closures_equal, hO.closures_equal]
  simp only
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
    decide_eq_false_iff_not]
  refine forall_congr' fun vs => or_congr (by rw [hty vs]) (or_congr ?_ ?_)
  · refine forall_congr' fun fuel => ?_
    constructor
    · intro h a
      refine ⟨fun ha => ?_, (h a).2⟩
      obtain ⟨a0, ha0⟩ := (hok fuel vs).2 ⟨a, ha⟩
      exact (h a0).1 ha0
    · intro h a
      refine ⟨fun ha => ?_, (h a).2⟩
      obtain ⟨a0, ha0⟩ := (hok fuel vs).1 ⟨a, ha⟩
      exact (h a0).1 ha0
  · constructor
    · rintro ⟨fuel, a, c, ⟨ha, hc⟩, he⟩
      obtain ⟨a', ha'⟩ := (hok fuel vs).1 ⟨a, ha⟩
      exact ⟨fuel, a', c, ⟨ha', hc⟩, by rw [← ((hr fuel vs a a' ha ha') c).2]; exact he⟩
    · rintro ⟨fuel, a', c, ⟨ha', hc⟩, he⟩
      obtain ⟨a, ha⟩ := (hok fuel vs).2 ⟨a', ha'⟩
      exact ⟨fuel, a, c, ⟨ha, hc⟩, by rw [((hr fuel vs a a' ha ha') c).2]; exact he⟩

theorem apply_stuck {f : Value} (hf : ∀ ps b e, f ≠ .ClosureV ps b e) (fuel : Int)
    (vs : List Value) : apply O P fuel f vs = .Stuck := by
  cases f with
  | ClosureV ps b e => exact absurd rfl (hf ps b e)
  | _ => unfold apply; rfl

/-- `ce_right` where the second operands are not closures. -/
theorem ce_nonclo (hO : O.Sound) {f g g' : Value} (hg : ∀ ps b e, g ≠ .ClosureV ps b e)
    (hg' : ∀ ps b e, g' ≠ .ClosureV ps b e) :
    O.closures_equal P f g = O.closures_equal P f g' :=
  ce_right hO (fun fuel vs => by simp [apply_stuck hg, apply_stuck hg'])
    (fun fuel vs a a' h _ => by simp [apply_stuck hg] at h)

theorem same_adt (hO : O.Sound) (hEq : ∀ c, sort_equality P c = none) {c : Id} {tps : List Ty}
    {vs vs' : List Value} (h : Sames O P vs vs') :
    Same O P (.ADTV c tps vs) (.ADTV c tps vs') := by
  intro x
  constructor
  · rw [hO.value_eq, hO.value_eq]
    cases x with
    | ADTV d _ ys => simp only [hEq d]; split <;> simp only [vals_right hO h ys]
    | ClosureV ps b e =>
      obtain ⟨_, _, _, _, eq⟩ := P
      cases eq
      · rfl
      · simp only [ce_nonclo hO (g := .ADTV c tps vs) (g' := .ADTV c tps vs')
          (fun _ _ _ h => nomatch h) (fun _ _ _ h => nomatch h)]
    | _ => simp
  · rw [hO.value_eq, hO.value_eq]
    cases x with
    | ADTV d _ ys => simp only [hEq c]; split <;> simp only [vals_left hO h ys]
    | _ => rfl

theorem same_set (hO : O.Sound) {B B' : Ty} {xs xs' : List Value} (h : Sames O P xs xs') :
    Same O P (.SetV B xs) (.SetV B' xs') := by
  intro x
  constructor
  · rw [hO.value_eq, hO.value_eq]
    cases x with
    | SetV _ ys => simp only [subset_right hO h ys, subset_left hO h ys]
    | ClosureV ps b e =>
      obtain ⟨_, _, _, _, eq⟩ := P
      cases eq
      · rfl
      · simp only [ce_nonclo hO (g := .SetV B xs) (g' := .SetV B' xs')
          (fun _ _ _ h => nomatch h) (fun _ _ _ h => nomatch h)]
    | _ => simp
  · rw [hO.value_eq, hO.value_eq]
    cases x with
    | SetV _ ys => simp only [subset_right hO h ys, subset_left hO h ys]
    | _ => rfl

theorem same_clo (hO : O.Sound) {ps ps' : List Param} {b b' : Expr} {e e' : Env}
    (hty : funEq P = true →
      ∀ vs, O.params_have_types P e vs ps = O.params_have_types P e' vs ps')
    (hok : ∀ fuel vs, (∃ a, apply O P fuel (.ClosureV ps b e) vs = .Ok a) →
      (∃ a', apply O P fuel (.ClosureV ps' b' e') vs = .Ok a'))
    (hback : funEq P = true → ∀ fuel vs,
      (∃ a', apply O P fuel (.ClosureV ps' b' e') vs = .Ok a') →
        (∃ a, apply O P fuel (.ClosureV ps b e) vs = .Ok a))
    (hr : ∀ fuel vs a a', apply O P fuel (.ClosureV ps b e) vs = .Ok a →
      apply O P fuel (.ClosureV ps' b' e') vs = .Ok a' → Same O P a a') :
    Same O P (.ClosureV ps b e) (.ClosureV ps' b' e') := by
  intro x
  constructor
  · rw [hO.value_eq, hO.value_eq]
    cases x with
    | ClosureV ps b e =>
      obtain ⟨_, _, _, _, eq⟩ := P
      cases eq
      · rfl
      · simp only [ce_right hO (fun fuel vs => ⟨hok fuel vs, hback rfl fuel vs⟩) hr]
    | _ => simp
  · rw [hO.value_eq, hO.value_eq]
    obtain ⟨_, _, _, _, eq⟩ := P
    cases eq
    · rfl
    · simp only [ce_left hO (hty rfl) (fun fuel vs => ⟨hok fuel vs, hback rfl fuel vs⟩) hr]

/-- The equality compares related values alike, where the sorts have no equalities of their own. -/
theorem ext_same (hO : O.Sound) (hEq : ∀ c, sort_equality P c = none) {a a' : Value}
    (h : Ext O P a a') : Same O P a a' :=
  Ext.rec (motive_1 := fun a a' _ => Same O P a a') (motive_2 := fun xs xs' _ => Sames O P xs xs')
    (fun _ _ => ⟨rfl, rfl⟩) (fun _ ih => same_adt hO hEq ih) (fun _ ih => same_set hO ih)
    (fun hty hok hback _ ih => same_clo hO hty hok hback ih) .nil (fun _ _ ih ihs => .cons ih ihs) h

theorem ext_bool {b : Bool} {v : Value} (h : Ext O P (.BoolV b) v) : v = .BoolV b := by
  cases h; rfl

/-- Related values are related to what values are related to. -/
theorem ext_trans {a b c : Value} (h1 : Ext O P a b) (h2 : Ext O P b c) : Ext O P a c :=
  Ext.rec (motive_1 := fun a b _ => ∀ c, Ext O P b c → Ext O P a c)
    (motive_2 := fun xs ys _ => ∀ zs, Exts O P ys zs → Exts O P xs zs)
    (fun _ _ h => h)
    (fun h ih _ h2 => by
      cases h2 with
      | refl => exact .adt h
      | adt h2 => exact .adt (ih _ h2))
    (fun h ih _ h2 => by
      cases h2 with
      | refl => exact .set h
      | set h2 => exact .set (ih _ h2))
    (fun hty hok hback hr ih _ h2 => by
      cases h2 with
      | refl => exact .clo hty hok hback hr
      | clo hty2 hok2 hback2 hr2 =>
        refine .clo (fun hf vs => (hty hf vs).trans (hty2 hf vs))
          (fun fuel vs ha => hok2 fuel vs (hok fuel vs ha))
          (fun hf fuel vs ha => hback hf fuel vs (hback2 hf fuel vs ha)) ?_
        intro fuel vs a a'' ha ha''
        obtain ⟨a', ha'⟩ := hok fuel vs ⟨a, ha⟩
        exact ih fuel vs a a' ha ha' _ (hr2 fuel vs a' a'' ha' ha''))
    (fun _ h2 => by cases h2; exact .nil)
    (fun _ _ ih ihs _ h2 => by
      cases h2 with
      | cons h hs => exact .cons (ih _ h) (ihs _ hs))
    h1 c h2

/-- `t'` refines `t` up to closures: in every environment where the facts hold, wherever `t` has
a value, `t'` has a related value with the same fuel. -/
def RefinesX (Fs : List Fact) (t t' : Expr) : Prop :=
  ∀ (fuel : Int) (env : Env) (v : Value), (∀ f ∈ Fs, f.Holds O P fuel env) →
    eval O P fuel env t = .Ok v → ∃ v', eval O P fuel env t' = .Ok v' ∧ Ext O P v v'

theorem refinesX_of {Fs : List Fact} {t t' : Expr} (h : Refines O P Fs t t') :
    RefinesX (O := O) (P := P) Fs t t' :=
  fun fuel env v hF hv => ⟨v, h fuel env v hF hv, .refl v⟩

theorem refinesX_trans {Fs : List Fact} {a b c : Expr} (h1 : RefinesX (O := O) (P := P) Fs a b)
    (h2 : RefinesX (O := O) (P := P) Fs b c) : RefinesX (O := O) (P := P) Fs a c := by
  intro fuel env v hF hv
  obtain ⟨v1, hv1, he1⟩ := h1 fuel env v hF hv
  obtain ⟨v2, hv2, he2⟩ := h2 fuel env v1 hF hv1
  exact ⟨v2, hv2, ext_trans he1 he2⟩

/-- The variables of `G` have values related to those of their expressions. -/
def GHolds (G : List (Id × Expr)) (fuel : Int) (env : Env) : Prop :=
  ∀ y e, (y, e) ∈ G → ∃ w, lookup_var (env_vars env) y = .Ok w ∧
    ∃ w', eval O P fuel env e = .Ok w' ∧ Ext O P w w'

/-- `RefinesX` where the variables of `G` also have values related to those of their
expressions. -/
def RefinesG (Fs : List Fact) (G : List (Id × Expr)) (t t' : Expr) : Prop :=
  ∀ (fuel : Int) (env : Env) (v : Value), (∀ f ∈ Fs, f.Holds O P fuel env) →
    GHolds (O := O) (P := P) G fuel env →
    eval O P fuel env t = .Ok v → ∃ v', eval O P fuel env t' = .Ok v' ∧ Ext O P v v'

theorem refinesG_of {Fs : List Fact} {G : List (Id × Expr)} {t t' : Expr}
    (h : RefinesX (O := O) (P := P) Fs t t') : RefinesG (O := O) (P := P) Fs G t t' :=
  fun fuel env v hF _ hv => h fuel env v hF hv

theorem refinesX_of_G {Fs : List Fact} {t t' : Expr}
    (h : RefinesG (O := O) (P := P) Fs [] t t') : RefinesX (O := O) (P := P) Fs t t' :=
  fun fuel env v hF hv => h fuel env v hF (fun _ _ h => by simp at h) hv

theorem exts_refl : ∀ xs : List Value, Exts O P xs xs
  | [] => .nil
  | x :: xs => .cons (.refl x) (exts_refl xs)

theorem exts_sames (hO : O.Sound) (hEq : ∀ c, sort_equality P c = none) :
    ∀ {xs xs' : List Value}, Exts O P xs xs' → Sames O P xs xs'
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => .cons (ext_same hO hEq h) (exts_sames hO hEq hs)

theorem setv_ext {B : Ty} {xs : List Value} {S' : Value} (h : Ext O P (.SetV B xs) S') :
    ∃ B' xs', S' = .SetV B' xs' ∧ Exts O P xs xs' := by
  cases h with
  | refl => exact ⟨B, xs, rfl, exts_refl xs⟩
  | set h => exact ⟨_, _, rfl, h⟩

theorem insert_ext (hO : O.Sound) (hEq : ∀ c, sort_equality P c = none) {xs xs' ys : List Value}
    {v v' : Value} (hs : Exts O P xs xs') (he : Ext O P v v') (h : set_insert O P xs v = .Ok ys) :
    ∃ ys', set_insert O P xs' v' = .Ok ys' ∧ Exts O P ys ys' := by
  unfold set_insert at h ⊢
  rw [contains_list hO (exts_sames hO hEq hs) v, contains_elem hO (ext_same hO hEq he) xs'] at h
  cases hc : O.set_contains P xs' v' with
  | Ok b =>
    rw [hc] at h
    simp only at h ⊢
    by_cases hb : b = true
    · simp only [hb, dite_true] at h ⊢; cases h; exact ⟨_, rfl, hs⟩
    · simp only [hb, dite_false] at h ⊢; cases h; exact ⟨_, rfl, .cons he hs⟩
  | _ => rw [hc] at h; cases h

theorem refinesX_Not {Fs : List Fact} {G : List (Id × Expr)} {a a' : Expr}
    (h : RefinesG (O := O) (P := P) Fs G a a') :
    RefinesG (O := O) (P := P) Fs G (.Not a) (.Not a') := by
  intro fuel env v hF hG hv
  simp only [eval, eval_bool] at hv ⊢
  cases ha : eval O P fuel env a with
  | Ok va =>
    obtain ⟨va', ha', he⟩ := h fuel env va hF hG ha
    rw [ha] at hv
    rw [ha']
    cases va with
    | BoolV b => rw [ext_bool he]; exact ⟨v, hv, .refl v⟩
    | _ => simp at hv
  | _ => rw [ha] at hv; cases hv

theorem refinesX_Equals_1 (hO : O.Sound) (hEq : ∀ c, sort_equality P c = none)
    {Fs : List Fact} {G : List (Id × Expr)}
    {a a' b : Expr} (h : RefinesG (O := O) (P := P) Fs G a a') :
    RefinesG (O := O) (P := P) Fs G (.Equals a b) (.Equals a' b) := by
  intro fuel env v hF hG hv
  simp only [eval] at hv ⊢
  cases ha : eval O P fuel env a with
  | Ok va =>
    obtain ⟨va', ha', he⟩ := h fuel env va hF hG ha
    rw [ha] at hv
    rw [ha']
    cases hb : eval O P fuel env b with
    | Ok vb =>
      rw [hb] at hv
      simp only
      rw [← ((ext_same hO hEq he) vb).2]
      exact ⟨v, hv, .refl v⟩
    | _ => rw [hb] at hv; cases hv
  | _ => rw [ha] at hv; cases hv

theorem refinesX_Equals_2 (hO : O.Sound) (hEq : ∀ c, sort_equality P c = none)
    {Fs : List Fact} {G : List (Id × Expr)}
    {a b b' : Expr} (h : RefinesG (O := O) (P := P) Fs G b b') :
    RefinesG (O := O) (P := P) Fs G (.Equals a b) (.Equals a b') := by
  intro fuel env v hF hG hv
  simp only [eval] at hv ⊢
  cases ha : eval O P fuel env a with
  | Ok va =>
    rw [ha] at hv
    simp only
    cases hb : eval O P fuel env b with
    | Ok vb =>
      obtain ⟨vb', hb', he⟩ := h fuel env vb hF hG hb
      rw [hb] at hv
      rw [hb']
      simp only
      rw [← ((ext_same hO hEq he) va).1]
      exact ⟨v, hv, .refl v⟩
    | _ => rw [hb] at hv; cases hv
  | _ => rw [ha] at hv; cases hv

theorem select_ext {sel : Id} : ∀ {fs : List Param} {vs vs' : List Value} {w : Value},
    Exts O P vs vs' → select_field fs vs sel = .Ok w →
      ∃ w', select_field fs vs' sel = .Ok w' ∧ Ext O P w w'
  | [], _, _, _, _, h => by simp [select_field] at h
  | .Param f _ :: fs, [], _, _, _, h => by simp [select_field] at h
  | .Param f _ :: fs, v :: vs, _, w, .cons he hs, h => by
    simp only [select_field] at h ⊢
    by_cases hf : f = sel
    · simp only [hf, dite_true] at h ⊢; cases h; exact ⟨_, rfl, he⟩
    · simp only [hf, dite_false] at h ⊢; exact select_ext hs h

theorem refinesX_ADTSelector {Fs : List Fact} {G : List (Id × Expr)} {a a' : Expr} {f : Id}
    (h : RefinesG (O := O) (P := P) Fs G a a') :
    RefinesG (O := O) (P := P) Fs G (.ADTSelector a f) (.ADTSelector a' f) := by
  intro fuel env v hF hG hv
  simp only [eval] at hv ⊢
  cases ha : eval O P fuel env a with
  | Ok va =>
    obtain ⟨va', ha', he⟩ := h fuel env va hF hG ha
    rw [ha] at hv
    rw [ha']
    cases he with
    | refl => exact ⟨v, hv, .refl v⟩
    | adt hs =>
      obtain ⟨_, cs, _, _, _⟩ := P
      simp only at hv ⊢
      cases hk : lookup_ctor cs _ with
      | Ok k =>
        rw [hk] at hv
        obtain ⟨_, _, fields⟩ := k
        exact select_ext hs hv
      | _ => rw [hk] at hv; cases hv
    | set _ => cases hv
    | clo _ _ _ => cases hv
  | _ => rw [ha] at hv; cases hv

theorem refinesX_Application {Fs : List Fact} {G : List (Id × Expr)} {a a' : Expr} {es : List Expr}
    (h : RefinesG (O := O) (P := P) Fs G a a') :
    RefinesG (O := O) (P := P) Fs G (.Application a es) (.Application a' es) := by
  intro fuel env v hF hG hv
  simp only [eval] at hv ⊢
  cases ha : eval O P fuel env a with
  | Ok va =>
    obtain ⟨va', ha', he⟩ := h fuel env va hF hG ha
    rw [ha] at hv
    rw [ha']
    cases hvs : eval_list O P fuel env es with
    | Ok vs =>
      rw [hvs] at hv
      simp only
      cases he with
      | refl => exact ⟨v, hv, .refl v⟩
      | adt _ => unfold apply at hv; cases hv
      | set _ => unfold apply at hv; cases hv
      | clo hty hok hback hr =>
        obtain ⟨v', hv'⟩ := hok fuel vs ⟨v, hv⟩
        exact ⟨v', hv', hr fuel vs v v' hv hv'⟩
    | _ => rw [hvs] at hv; cases hv
  | _ => rw [ha] at hv; cases hv

theorem refinesX_ElementOfSet_1 (hO : O.Sound) (hEq : ∀ c, sort_equality P c = none)
    {Fs : List Fact} {G : List (Id × Expr)} {a a' s : Expr}
    (h : RefinesG (O := O) (P := P) Fs G a a') :
    RefinesG (O := O) (P := P) Fs G (.ElementOfSet a s) (.ElementOfSet a' s) := by
  intro fuel env v hF hG hv
  simp only [eval] at hv ⊢
  cases ha : eval O P fuel env a with
  | Ok va =>
    obtain ⟨va', ha', he⟩ := h fuel env va hF hG ha
    rw [ha] at hv
    rw [ha']
    simp only at hv ⊢
    cases hs : eval_set O P fuel env s with
    | Ok S =>
      rw [hs] at hv
      simp only at hv ⊢
      rw [← contains_elem hO (ext_same hO hEq he)]
      exact ⟨v, hv, .refl v⟩
    | _ => rw [hs] at hv; cases hv
  | _ => rw [ha] at hv; cases hv

theorem eval_set_some {fuel : Int} {env : Env} {s : Expr} {S : Value}
    (h : eval_set O P fuel env s = .Ok S) :
    ∃ B xs, S = .SetV B xs ∧ eval O P fuel env s = .Ok (.SetV B xs) := by
  unfold eval_set at h
  cases he : eval O P fuel env s with
  | Ok w =>
    rw [he] at h
    cases w with
    | SetV B xs => cases h; exact ⟨B, xs, rfl, rfl⟩
    | _ => cases h
  | _ => rw [he] at h; cases h

theorem eval_set_of {fuel : Int} {env : Env} {s : Expr} {B : Ty} {xs : List Value}
    (h : eval O P fuel env s = .Ok (.SetV B xs)) : eval_set O P fuel env s = .Ok (.SetV B xs) := by
  unfold eval_set; rw [h]

theorem eval_set_ext {Fs : List Fact} {G : List (Id × Expr)} {s s' : Expr}
    (h : RefinesG (O := O) (P := P) Fs G s s')
    {fuel : Int} {env : Env} (hF : ∀ f ∈ Fs, f.Holds O P fuel env)
    (hG : GHolds (O := O) (P := P) G fuel env) {S : Value}
    (hs : eval_set O P fuel env s = .Ok S) :
    ∃ B xs, S = .SetV B xs ∧ ∃ B' xs', eval_set O P fuel env s' = .Ok (.SetV B' xs') ∧
      Exts O P xs xs' := by
  unfold eval_set at hs ⊢
  cases he : eval O P fuel env s with
  | Ok w =>
    rw [he] at hs
    obtain ⟨w', hw', hx⟩ := h fuel env w hF hG he
    rw [hw']
    cases w with
    | SetV B xs =>
      cases hs
      obtain ⟨B', xs', rfl, hxs⟩ := setv_ext hx
      exact ⟨B, xs, rfl, B', xs', rfl, hxs⟩
    | _ => cases hs
  | _ => rw [he] at hs; cases hs

theorem refinesX_ElementOfSet_2 (hO : O.Sound) (hEq : ∀ c, sort_equality P c = none)
    {Fs : List Fact} {G : List (Id × Expr)} {a s s' : Expr}
    (h : RefinesG (O := O) (P := P) Fs G s s') :
    RefinesG (O := O) (P := P) Fs G (.ElementOfSet a s) (.ElementOfSet a s') := by
  intro fuel env v hF hG hv
  simp only [eval] at hv ⊢
  cases ha : eval O P fuel env a with
  | Ok va =>
    rw [ha] at hv
    simp only at hv ⊢
    cases hs : eval_set O P fuel env s with
    | Ok S =>
      rw [hs] at hv
      obtain ⟨B, xs, rfl, B', xs', hs', hxs⟩ := eval_set_ext h hF hG hs
      rw [hs']
      simp only [set_elems] at hv ⊢
      rw [← contains_list hO (exts_sames hO hEq hxs)]
      exact ⟨v, hv, .refl v⟩
    | _ => rw [hs] at hv; cases hv
  | _ => rw [ha] at hv; cases hv

theorem refinesX_SetAdd_1 (hO : O.Sound) (hEq : ∀ c, sort_equality P c = none)
    {Fs : List Fact} {G : List (Id × Expr)} {s s' a : Expr}
    (h : RefinesG (O := O) (P := P) Fs G s s') :
    RefinesG (O := O) (P := P) Fs G (.SetAdd s a) (.SetAdd s' a) := by
  intro fuel env v hF hG hv
  simp only [eval] at hv ⊢
  cases hs : eval_set O P fuel env s with
  | Ok S =>
    rw [hs] at hv
    obtain ⟨B, xs, rfl, B', xs', hs', hxs⟩ := eval_set_ext h hF hG hs
    rw [hs']
    simp only at hv ⊢
    cases ha : eval O P fuel env a with
    | Ok va =>
      rw [ha] at hv
      simp only [set_elems, set_with] at hv ⊢
      cases hi : set_insert O P xs va with
      | Ok ys =>
        rw [hi] at hv
        cases hv
        obtain ⟨ys', hi', hys⟩ := insert_ext hO hEq hxs (.refl va) hi
        rw [hi']
        exact ⟨_, rfl, .set hys⟩
      | _ => rw [hi] at hv; cases hv
    | _ => rw [ha] at hv; cases hv
  | _ => rw [hs] at hv; cases hv

theorem refinesX_SetAdd_2 (hO : O.Sound) (hEq : ∀ c, sort_equality P c = none)
    {Fs : List Fact} {G : List (Id × Expr)} {s a a' : Expr}
    (h : RefinesG (O := O) (P := P) Fs G a a') :
    RefinesG (O := O) (P := P) Fs G (.SetAdd s a) (.SetAdd s a') := by
  intro fuel env v hF hG hv
  simp only [eval] at hv ⊢
  cases hs : eval_set O P fuel env s with
  | Ok S =>
    rw [hs] at hv
    simp only at hv ⊢
    cases ha : eval O P fuel env a with
    | Ok va =>
      rw [ha] at hv
      obtain ⟨va', ha', he⟩ := h fuel env va hF hG ha
      rw [ha']
      simp only at hv ⊢
      cases hi : set_insert O P (set_elems S) va with
      | Ok ys =>
        rw [hi] at hv
        cases hv
        obtain ⟨ys', hi', hys⟩ := insert_ext hO hEq (exts_refl _) he hi
        rw [hi']
        refine ⟨_, rfl, ?_⟩
        unfold eval_set at hs
        cases hS : eval O P fuel env s with
        | Ok w =>
          rw [hS] at hs
          cases w with
          | SetV B xs => cases hs; exact .set hys
          | _ => cases hs
        | _ => rw [hS] at hs; cases hs
      | _ => rw [hi] at hv; cases hv
    | _ => rw [ha] at hv; cases hv
  | _ => rw [hs] at hv; cases hv

end

/-! ## Calls that build closures -/

/-- `e` where the variables of `σ` are their expressions, if `e` has no lambdas, calls or
constructions, `n` deep. -/
def msubst (σ : List (Id × Expr)) : Nat → Expr → Option Expr
  | 0, _ => none
  | n + 1, e =>
    match e with
    | .Variable y => σ.lookup y
    | .IntegerLiteral i => some (.IntegerLiteral i)
    | .BooleanLiteral b => some (.BooleanLiteral b)
    | .FractionLiteral a b => some (.FractionLiteral a b)
    | .Error => some .Error
    | .Not a => (msubst σ n a).map .Not
    | .UMinus a => (msubst σ n a).map .UMinus
    | .IsConstructor a c => (msubst σ n a).map (.IsConstructor · c)
    | .ADTSelector a f => (msubst σ n a).map (.ADTSelector · f)
    | .Plus a b =>
      match msubst σ n a, msubst σ n b with
      | some a', some b' => some (.Plus a' b')
      | _, _ => none
    | .Minus a b =>
      match msubst σ n a, msubst σ n b with
      | some a', some b' => some (.Minus a' b')
      | _, _ => none
    | .Times a b =>
      match msubst σ n a, msubst σ n b with
      | some a', some b' => some (.Times a' b')
      | _, _ => none
    | .Division a b =>
      match msubst σ n a, msubst σ n b with
      | some a', some b' => some (.Division a' b')
      | _, _ => none
    | .Remainder a b =>
      match msubst σ n a, msubst σ n b with
      | some a', some b' => some (.Remainder a' b')
      | _, _ => none
    | .Modulo a b =>
      match msubst σ n a, msubst σ n b with
      | some a', some b' => some (.Modulo a' b')
      | _, _ => none
    | .LessThan a b =>
      match msubst σ n a, msubst σ n b with
      | some a', some b' => some (.LessThan a' b')
      | _, _ => none
    | .GreaterThan a b =>
      match msubst σ n a, msubst σ n b with
      | some a', some b' => some (.GreaterThan a' b')
      | _, _ => none
    | .LessEquals a b =>
      match msubst σ n a, msubst σ n b with
      | some a', some b' => some (.LessEquals a' b')
      | _, _ => none
    | .GreaterEquals a b =>
      match msubst σ n a, msubst σ n b with
      | some a', some b' => some (.GreaterEquals a' b')
      | _, _ => none
    | .Equals a b =>
      match msubst σ n a, msubst σ n b with
      | some a', some b' => some (.Equals a' b')
      | _, _ => none
    | .Implies a b =>
      match msubst σ n a, msubst σ n b with
      | some a', some b' => some (.Implies a' b')
      | _, _ => none
    | .Assume a b =>
      match msubst σ n a, msubst σ n b with
      | some a', some b' => some (.Assume a' b')
      | _, _ => none
    | .IfExpr c a b =>
      match msubst σ n c, msubst σ n a, msubst σ n b with
      | some c', some a', some b' => some (.IfExpr c' a' b')
      | _, _, _ => none
    | .And es => (es.mapM (msubst σ n)).map .And
    | .Or es => (es.mapM (msubst σ n)).map .Or
    | _ => none

section
variable {O : Oracle} {P : Program}

theorem msubst_list {σ : List (Id × Expr)} {n : Nat} {fuel : Int} {env env' : Env}
    (ih : ∀ e e', msubst σ n e = some e' → eval O P fuel env' e = eval O P fuel env e') :
    ∀ (es es' : List Expr), es.mapM (msubst σ n) = some es' →
      eval_list O P fuel env' es = eval_list O P fuel env es' ∧
      eval_and O P fuel env' es = eval_and O P fuel env es' ∧
      eval_or O P fuel env' es = eval_or O P fuel env es'
  | [], es', h => by
    simp at h; subst h
    refine ⟨?_, ?_, ?_⟩
    · rw [eval_list, eval_list]
    · rw [eval_and, eval_and]
    · rw [eval_or, eval_or]
  | a :: as, es', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨a', ha, as', has, rfl⟩ := h
    obtain ⟨h1, h2, h3⟩ := msubst_list ih as as' has
    have hae := ih a a' ha
    refine ⟨?_, ?_, ?_⟩
    · rw [eval_list, eval_list, hae, h1]
    · rw [eval_and, eval_and, eval_bool, eval_bool, hae, h2]
    · rw [eval_or, eval_or, eval_bool, eval_bool, hae, h3]


/-- Where each variable that `σ` substitutes has in `env'` the value that its substitute has in
`env`, an expression has in `env'` the value of its substitution in `env`. -/
theorem msubst_eval {σ : List (Id × Expr)} {fuel : Int} {env env' : Env}
    (hvar : ∀ y w, σ.lookup y = some w →
      eval O P fuel env' (.Variable y) = eval O P fuel env w) :
    ∀ n e e', msubst σ n e = some e' → eval O P fuel env' e = eval O P fuel env e'
  | 0, _, _, h => by simp [msubst] at h
  | n + 1, e, e', h => by
    have ih := msubst_eval hvar n
    unfold msubst at h
    split at h
    · next y =>
      exact hvar y e' h
    all_goals first
      | (cases h; simp only [eval]; done)
      | skip
    · obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [eval, eval_bool, ih _ _ ha]
    · obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [eval, eval_bool, ih _ _ ha]
    · obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [eval, eval_bool, ih _ _ ha]
    · obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [eval, eval_bool, ih _ _ ha]
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next c' a' b' hc ha hb =>
        cases h; simp only [eval, eval_bool, ih _ _ hc, ih _ _ ha, ih _ _ hb]
      · cases h
    · obtain ⟨es', hes, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [eval]
      exact (msubst_list ih _ _ hes).2.1
    · obtain ⟨es', hes, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [eval]
      exact (msubst_list ih _ _ hes).2.2
    · cases h

end

/-- Whether the constructor `c` is of a sort without an invariant. -/
def noInvCtor (cs : List Constructor) (ss : List ADTSort) (c : Id) : Bool :=
  match lookup_ctor cs c with
  | .Ok (.Constructor _ s _) =>
    match lookup_sort ss s with
    | .Ok (.Sort _ _ none _) => true
    | _ => false
  | _ => false

/-- The types of parameters whose values the semantics checks without the types of the
environment. -/
def primParam : Ty → Bool
  | .IntegerType | .BooleanType => true
  | _ => false

/-- Whether `e'` is what `e` evaluates to where the variables of `σ` are their literals, up to
the closures: constructions of sorts without invariants of such, lambdas of one parameter whose
body is `e'` where the parameter is renamed and the variables are their literals, and other
terms that the literals make ground, with the value of `e'`, `n` deep. -/
def vfCheck (cs : List Constructor) (ss : List ADTSort) (σ : List (Id × Expr)) :
    Nat → Expr → Expr → Bool
  | 0, _, _ => false
  | n + 1, .ADT c [] es, .ADT c' [] es' =>
    c == c' && noInvCtor cs ss c && es.length == es'.length &&
      (es.zip es').all fun p => vfCheck cs ss σ n p.1 p.2
  | _ + 1, .Lambda [.Param x T] b, .Lambda [.Param y T'] b' =>
    primParam T && Inox.Lowered.tyEq 100 T T' &&
      (msubst ((x, .Variable y) :: σ) 100 b).any (Inox.Lowered.exprEq 1000 · b')
  | n + 1, .SetAdd s e, .SetAdd s' e' => vfCheck cs ss σ n s s' && vfCheck cs ss σ n e e'
  | _ + 1, .FiniteSet [] _, .FiniteSet [] _ => true
  | _ + 1, e, e' =>
    match (msubst σ 100 e).bind (geval 100), geval 100 e' with
    | some w, some w' => litEq w w'
    | _, _ => false

/-- `evaluate` of a call with literal arguments to a function without type parameters, whose
body evaluates to `t'` up to closures. -/
def callCheck (cs : List Constructor) (ss : List ADTSort) (fns : List FunDef) (t t' : Expr) :
    Bool :=
  match t with
  | .FunctionInvocation f [] args =>
    match lookup_fun fns f, args.mapM (geval 100) with
    | .Ok (.FunDef _ [] params body), some _ =>
      params.length == args.length && vfCheck cs ss (params.zip args) 100 body t'
    | _, _ => false
  | _ => false

/-- `beta`: the application of a lambda of one parameter to a literal is the let of the
parameter, where the literal makes the body ground. -/
def betaCheck (t t' : Expr) : Bool :=
  match t, t' with
  | .Application (.Lambda [.Param x _] b) [a], .Let y a' b' =>
    Inox.Lowered.exprEq 1000 a a' &&
      match geval 100 a, (msubst [(x, a)] 100 b).bind (geval 100),
        (msubst [(y, a)] 100 b').bind (geval 100) with
      | some _, some w, some w' => litEq w w'
      | _, _, _ => false
  | _, _ => false

/-- `beta`: an application of a lambda to a variable, and its let, whose bodies are the same
ground term. -/
def betaVarCheck (t t' : Expr) : Bool :=
  match t, t' with
  | .Application (.Lambda [.Param _ _] b) [.Variable z], .Let _ (.Variable z') b' =>
    z == z' && match geval 100 b, geval 100 b' with
      | some w, some w' => litEq w w'
      | _, _ => false
  | _, _ => false

/-- `logic`: lets of the same literal whose bodies are the same where their variables are the
literal. -/
def letLitCheck (t t' : Expr) : Bool :=
  match t, t' with
  | .Let x a b, .Let y a' b' =>
    Inox.Lowered.exprEq 1000 a a' && (geval 100 a).isSome &&
      match msubst [(x, a)] 100 b, msubst [(y, a)] 100 b' with
      | some c, some c' => Inox.Lowered.exprEq 1000 c c'
      | _, _ => false
  | _, _ => false

/-- The elements of a set of insertions into the empty set. -/
def setElems : Expr → Option (List Expr)
  | .FiniteSet [] _ => some []
  | .SetAdd s b => (setElems s).map (b :: ·)
  | _ => none

/-- `evaluate` of a membership: in none of the elements, where none is equal to the value, or in
the one element, which is equal to it. -/
def memberCheck (cs : List Constructor) (ss : List ADTSort) (Fs : List Fact) (t t' : Expr) :
    Bool :=
  match t, t' with
  | .ElementOfSet a s, .BooleanLiteral false =>
    match setElems s with
    | some bs => bs.all fun b =>
      ruleCheck cs ss "evaluate" Fs (.Equals b a) (.BooleanLiteral false)
    | none => false
  | .ElementOfSet a (.SetAdd (.FiniteSet [] _) b), .BooleanLiteral true =>
    ruleCheck cs ss "evaluate" Fs (.Equals b a) (.BooleanLiteral true)
  | _, _ => false

section
variable {O : Oracle} {P : Program}

theorem insert_mem {xs ys : List Value} {v y : Value} (h : set_insert O P xs v = .Ok ys)
    (hy : y ∈ ys) : y ∈ xs ∨ y = v := by
  unfold set_insert at h
  cases hc : O.set_contains P xs v with
  | Ok b =>
    rw [hc] at h
    simp only at h
    by_cases hb : b = true
    · simp only [hb, dite_true] at h; cases h; exact .inl hy
    · simp only [hb, dite_false] at h
      cases h
      rcases List.mem_cons.mp hy with h | h
      · exact .inr h
      · exact .inl h
  | _ => rw [hc] at h; cases h

theorem contains_true (hO : O.Sound) {v : Value} : ∀ {xs : List Value},
    O.set_contains P xs v = .Ok true → ∃ y ∈ xs, O.value_eq P y v = .Ok true
  | [], h => by rw [hO.set_contains] at h; cases h
  | x :: xs, h => by
    rw [hO.set_contains] at h
    simp only at h
    cases he : O.value_eq P x v with
    | Ok b =>
      rw [he] at h
      simp only at h
      by_cases hb : b = true
      · subst hb; exact ⟨x, List.mem_cons_self, he⟩
      · simp only [hb, dite_false] at h
        obtain ⟨y, hy, hyv⟩ := contains_true hO h
        exact ⟨y, List.mem_cons_of_mem _ hy, hyv⟩
    | _ => rw [he] at h; cases h

theorem elems_of {fuel : Int} {env : Env} : ∀ {s : Expr} {bs : List Expr} {S : Value},
    setElems s = some bs → eval_set O P fuel env s = .Ok S →
      ∀ y ∈ set_elems S, ∃ b ∈ bs, eval O P fuel env b = .Ok y
  | .FiniteSet [] _, bs, S, _, hs, y, hy => by
    obtain ⟨B, xs, rfl, he⟩ := eval_set_some hs
    simp only [eval, eval_list, set_insert_all] at he
    cases he
    simp [set_elems] at hy
  | .SetAdd s b, bs, S, h, hs, y, hy => by
    simp only [setElems, Option.map_eq_some_iff] at h
    obtain ⟨bs0, h0, rfl⟩ := h
    obtain ⟨B, xs, rfl, he⟩ := eval_set_some hs
    simp only [eval] at he
    cases hs0 : eval_set O P fuel env s with
    | Ok S0 =>
      rw [hs0] at he
      obtain ⟨B0, xs0, rfl, _⟩ := eval_set_some hs0
      cases hb : eval O P fuel env b with
      | Ok vb =>
        rw [hb] at he
        simp only [set_elems, set_with] at he
        cases hi : set_insert O P xs0 vb with
        | Ok ys =>
          rw [hi] at he
          cases he
          rcases insert_mem hi hy with hy | rfl
          · obtain ⟨b', hb', hev⟩ := elems_of h0 hs0 y hy
            exact ⟨b', List.mem_cons_of_mem _ hb', hev⟩
          · exact ⟨b, List.mem_cons_self, hb⟩
        | _ => rw [hi] at he; cases he
      | _ => rw [hb] at he; cases he
    | _ => rw [hs0] at he; cases he

theorem memberCheck_refines (hO : O.Sound) {fns : List FunDef} {cs : List Constructor}
    {ss : List ADTSort} {is : List Interpretation} {eqm : FunctionEquality}
    (hP : P = .Program fns cs ss is eqm) {Fs : List Fact} {t t' : Expr}
    (h : memberCheck cs ss Fs t t' = true) : Refines O P Fs t t' := by
  intro fuel env v hF hv
  unfold memberCheck at h
  split at h
  · next a s =>
    split at h
    · next bs hbs =>
      simp only [eval] at hv ⊢
      cases ha : eval O P fuel env a with
      | Ok va =>
        rw [ha] at hv
        cases hs : eval_set O P fuel env s with
        | Ok S =>
          rw [hs] at hv
          simp only at hv
          cases hc : O.set_contains P (set_elems S) va with
          | Ok r =>
            rw [hc] at hv
            cases hv
            cases r with
            | false => rfl
            | true =>
              obtain ⟨y, hy, hyv⟩ := contains_true hO hc
              obtain ⟨b, hb, hev⟩ := elems_of hbs hs y hy
              have hr := ruleCheck_refines hO ⟨fns, is, eqm, hP⟩ (List.all_eq_true.mp h b hb)
                fuel env (.BoolV true) hF (by simp [eval, hev, ha, hyv])
              simp [eval] at hr
          | _ => rw [hc] at hv; cases hv
        | _ => rw [hs] at hv; cases hv
      | _ => rw [ha] at hv; cases hv
    · cases h
  · next a B b =>
    simp only [eval] at hv ⊢
    cases ha : eval O P fuel env a with
    | Ok va =>
      rw [ha] at hv
      cases hb : eval O P fuel env b with
      | Ok vb =>
        have h0 : eval_set O P fuel env (.FiniteSet [] B) =
            .Ok (.SetV (O.resolve (env_types env) B) []) :=
          eval_set_of (by simp [eval, eval_list, set_insert_all])
        have hS : eval_set O P fuel env (.SetAdd (.FiniteSet [] B) b) =
            .Ok (.SetV (O.resolve (env_types env) B) [vb]) := by
          apply eval_set_of
          simp only [eval]
          rw [h0, hb]
          simp only [set_elems, set_insert]
          rw [hO.set_contains]
          simp [set_with]
        rw [hS] at hv
        simp only [set_elems] at hv
        rw [hO.set_contains] at hv
        simp only at hv
        cases he : O.value_eq P vb va with
        | Ok r =>
          rw [he] at hv
          rw [hO.set_contains] at hv
          have hr := ruleCheck_refines hO ⟨fns, is, eqm, hP⟩ h fuel env (.BoolV r) hF
            (by simp [eval, hb, ha, he])
          simp only [eval, Result.Ok.injEq, Value.BoolV.injEq] at hr
          subst hr
          simp at hv
          rw [hv]
        | _ => rw [he] at hv; simp at hv
      | _ => simp [eval_set, eval, eval_list, set_insert_all, hb] at hv
    | _ => rw [ha] at hv; cases hv
  · cases h

theorem construct_noinv (hO : O.Sound) {fns : List FunDef} {cs : List Constructor}
    {ss : List ADTSort} {is : List Interpretation} {eqm : FunctionEquality}
    (hP : P = .Program fns cs ss is eqm) {c : Id} (h : noInvCtor cs ss c = true) (fuel : Int)
    (env : Env) (vs : List Value) : construct O P fuel env c [] vs = .Ok (.ADTV c [] vs) := by
  subst hP
  unfold noInvCtor at h
  cases hc : lookup_ctor cs c with
  | Ok k =>
    obtain ⟨_, s, _⟩ := k
    rw [hc] at h
    simp only at h
    cases hs : lookup_sort ss s with
    | Ok srt =>
      rw [hs] at h
      obtain ⟨_, _, inv, _⟩ := srt
      cases inv
      · simp [construct, hc, hs, hO.resolve_all]
      · simp at h
    | _ => rw [hs] at h; cases h
  | _ => rw [hc] at h; cases h

/-- A variable that `σ` substitutes by a literal has the value of the literal. -/
theorem lit_var (hO : O.Sound) {σ : List (Id × Expr)} {vars : List Binding}
    (hσ : ∀ y w, σ.lookup y = some w →
      ∃ u, geval 100 w = some u ∧ lookup_var vars y = .Ok u)
    {tys : List TypeBinding} {fuel : Int} {env : Env} :
    ∀ y w, σ.lookup y = some w →
      eval O P fuel (.Env tys vars) (.Variable y) = eval O P fuel env w := by
  intro y w hy
  obtain ⟨u, hu, hl⟩ := hσ y w hy
  rw [geval_eval hO 100 w hu]
  simp [eval, env_vars, hl]

theorem vfs_ext {σ : List (Id × Expr)} {cs : List Constructor} {ss : List ADTSort} {n : Nat}
    {fuel1 fuel2 : Int} {env1 env2 : Env}
    (ih : ∀ e e' {v : Value}, vfCheck cs ss σ n e e' = true → eval O P fuel1 env1 e = .Ok v →
      ∃ v', eval O P fuel2 env2 e' = .Ok v' ∧ Ext O P v v') :
    ∀ (es es' : List Expr) {vs : List Value}, es.length = es'.length →
      ((es.zip es').all fun p => vfCheck cs ss σ n p.1 p.2) = true →
      eval_list O P fuel1 env1 es = .Ok vs →
        ∃ vs', eval_list O P fuel2 env2 es' = .Ok vs' ∧ Exts O P vs vs'
  | [], [], vs, _, _, h => by
    rw [eval_list] at h; cases h; exact ⟨[], by rw [eval_list], .nil⟩
  | e :: es, e' :: es', vs, hlen, hall, h => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    rw [eval_list] at h
    cases he : eval O P fuel1 env1 e with
    | Ok v =>
      rw [he] at h
      cases hes : eval_list O P fuel1 env1 es with
      | Ok ws =>
        rw [hes] at h
        cases h
        obtain ⟨v', hv', hx⟩ := ih e e' hall.1 he
        obtain ⟨ws', hws', hxs⟩ := vfs_ext ih es es' hlen hall.2 hes
        exact ⟨v' :: ws', by rw [eval_list, hv', hws'], .cons hx hxs⟩
      | _ => rw [hes] at h; cases h
    | _ => rw [he] at h; cases h
  | [], _ :: _, _, hlen, _, _ => by simp at hlen
  | _ :: _, [], _, hlen, _, _ => by simp at hlen


theorem vf_ext (hO : O.Sound) (hEq : ∀ c, sort_equality P c = none) {fns : List FunDef}
    {cs : List Constructor} {ss : List ADTSort}
    {is : List Interpretation} {eqm : FunctionEquality} (hP : P = .Program fns cs ss is eqm)
    {σ : List (Id × Expr)} {tys1 : List TypeBinding} {vars1 : List Binding}
    (hσ : ∀ y w, σ.lookup y = some w →
      ∃ u, geval 100 w = some u ∧ lookup_var vars1 y = .Ok u)
    {fuel1 fuel2 : Int} {env2 : Env} :
    ∀ n e e' {v : Value}, vfCheck cs ss σ n e e' = true →
      eval O P fuel1 (.Env tys1 vars1) e = .Ok v →
        ∃ v', eval O P fuel2 env2 e' = .Ok v' ∧ Ext O P v v'
  | 0, _, _, _, h, _ => by simp [vfCheck] at h
  | n + 1, e, e', v, h, hv => by
    unfold vfCheck at h
    split at h
    · exfalso; omega
    · next m c es c' es' heq =>
      obtain rfl : n = m := by omega
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨rfl, hinv⟩, hlen⟩, hall⟩ := h
      simp only [eval] at hv ⊢
      cases hl : eval_list O P fuel1 (.Env tys1 vars1) es with
      | Ok vs =>
        rw [hl] at hv
        simp only [construct_noinv hO hP hinv] at hv
        cases hv
        obtain ⟨vs', hl', hx⟩ :=
          vfs_ext (fun e e' _ h hv => vf_ext hO hEq hP hσ n e e' h hv) es es' hlen hall hl
        rw [hl']
        simp only [construct_noinv hO hP hinv]
        exact ⟨_, rfl, .adt hx⟩
      | _ => rw [hl] at hv; cases hv
    · next m x T b y T' b' heq =>
      simp only [Bool.and_eq_true, Option.any_eq_true] at h
      obtain ⟨⟨hT, hTT⟩, b0, hb0, he⟩ := h
      rw [Inox.Lowered.exprEq_eq _ _ _ he] at hb0
      rw [← Inox.Lowered.tyEq_eq _ _ _ hTT]
      simp only [eval] at hv ⊢
      cases hv
      cases env2 with
      | Env tys2 vars2 =>
      have hap : ∀ fuel vs, apply O P fuel (.ClosureV [.Param x T] b (.Env tys1 vars1)) vs =
          apply O P fuel (.ClosureV [.Param y T] b' (.Env tys2 vars2)) vs := by
        intro fuel vs
        simp only [apply, param_ids]
        split
        · rfl
        · cases vs with
          | nil => simp [bind_all]
          | cons u vs =>
            cases vs with
            | cons _ _ => simp [bind_all]
            | nil =>
              simp only [bind_all, append_env]
              refine msubst_eval (fun z w hz => ?_) 100 b b' hb0
              rw [List.lookup_cons] at hz
              by_cases hzx : z = x
              · subst hzx
                simp only [beq_self_eq_true] at hz
                cases hz
                simp [eval, env_vars, lookup_var]
              · have hne : (z == x) = false := by simp [hzx]
                rw [hne] at hz
                obtain ⟨u', hu', hl⟩ := hσ z w hz
                rw [geval_eval hO 100 w hu']
                simp [eval, env_vars, lookup_var, hzx, hl]
      refine ⟨_, rfl, .clo (fun _ vs => ?_) (fun fuel vs h => by rw [← hap]; exact h)
        (fun _ fuel vs h => by rw [hap]; exact h) (fun fuel vs a a' h1 h2 => ?_)⟩
      · cases T <;> simp [primParam] at hT <;>
          (cases vs with
            | nil => simp [hO.params_have_types]
            | cons u vs => cases vs <;> simp [hO.params_have_types, hO.has_type])
      · rw [hap, h2] at h1
        cases h1
        exact .refl _
    · next m s e s' e' heq =>
      obtain rfl : n = m := by omega
      simp only [Bool.and_eq_true] at h
      simp only [eval] at hv ⊢
      cases hs : eval_set O P fuel1 (.Env tys1 vars1) s with
      | Ok S =>
        rw [hs] at hv
        obtain ⟨B, xs, rfl, hS⟩ := eval_set_some hs
        obtain ⟨w', hw', hx⟩ :=
          vf_ext hO hEq hP hσ (fuel2 := fuel2) (env2 := env2) n s s' h.1 hS
        obtain ⟨B', xs', rfl, hxs⟩ := setv_ext hx
        rw [eval_set_of hw']
        simp only [set_elems, set_with] at hv ⊢
        cases he : eval O P fuel1 (.Env tys1 vars1) e with
        | Ok va =>
          rw [he] at hv
          obtain ⟨va', he', hxa⟩ :=
            vf_ext hO hEq hP hσ (fuel2 := fuel2) (env2 := env2) n e e' h.2 he
          rw [he']
          simp only at hv ⊢
          cases hi : set_insert O P xs va with
          | Ok ys =>
            rw [hi] at hv
            cases hv
            obtain ⟨ys', hi', hys⟩ := insert_ext hO hEq hxs hxa hi
            rw [hi']
            exact ⟨_, rfl, .set hys⟩
          | _ => rw [hi] at hv; cases hv
        | _ => rw [he] at hv; cases hv
      | _ => rw [hs] at hv; cases hv
    · simp only [eval, eval_list, set_insert_all] at hv ⊢
      cases hv
      exact ⟨_, rfl, .set .nil⟩
    · next =>
      split at h
      · next w w' h1 h2 =>
        obtain ⟨e0, he0, hg⟩ := Option.bind_eq_some_iff.mp h1
        rw [msubst_eval (env := .Env tys1 vars1) (lit_var hO hσ) 100 _ e0 he0,
          geval_eval hO 100 e0 hg] at hv
        cases hv
        exact ⟨w', geval_eval hO 100 _ h2, by rw [litEq_eq h]; exact .refl _⟩
      · cases h

theorem eval_list_geval (hO : O.Sound) {fuel : Int} {env : Env} :
    ∀ (es : List Expr) {vs : List Value}, es.mapM (geval 100) = some vs →
      eval_list O P fuel env es = .Ok vs
  | [], vs, h => by simp at h; subst h; rw [eval_list]
  | e :: es, vs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨v, hv, ws, hws, rfl⟩ := h
    rw [eval_list, geval_eval hO 100 e hv, eval_list_geval hO es hws]

theorem zip_lookup : ∀ (params : List Id) (args : List Expr) {vals : List Value}
    {bs : List Binding}, args.mapM (geval 100) = some vals → bind_all params vals = .Ok bs →
    ∀ y w, (params.zip args).lookup y = some w →
      ∃ u, geval 100 w = some u ∧ lookup_var bs y = .Ok u
  | [], _, _, _, _, _, y, w, hy => by simp at hy
  | _ :: _, [], _, _, _, _, y, w, hy => by simp at hy
  | p :: ps, a :: as, vals, bs, hv, hb, y, w, hy => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hv
    obtain ⟨u, hu, us, hus, rfl⟩ := hv
    simp only [bind_all] at hb
    cases hr : bind_all ps us with
    | Ok rest =>
      rw [hr] at hb
      cases hb
      rw [List.zip_cons_cons, List.lookup_cons] at hy
      by_cases hyp : y = p
      · subst hyp
        simp only [beq_self_eq_true] at hy
        cases hy
        exact ⟨u, hu, by simp [lookup_var]⟩
      · have hne : (y == p) = false := by simp [hyp]
        rw [hne] at hy
        obtain ⟨u', hu', hl⟩ := zip_lookup ps as hus hr y w hy
        exact ⟨u', hu', by simp [lookup_var, hyp, hl]⟩
    | _ => rw [hr] at hb; cases hb

theorem callCheck_refinesX (hO : O.Sound) (hEq : ∀ c, sort_equality P c = none)
    {fns : List FunDef} {cs : List Constructor}
    {ss : List ADTSort} {is : List Interpretation} {eqm : FunctionEquality}
    (hP : P = .Program fns cs ss is eqm) {Fs : List Fact} {t t' : Expr}
    (h : callCheck cs ss fns t t' = true) : RefinesX (O := O) (P := P) Fs t t' := by
  intro fuel env v _ hv
  unfold callCheck at h
  split at h
  · next f args =>
    split at h
    · next params body vals hf hvals =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨_, hvf⟩ := h
      simp only [eval] at hv
      rw [eval_list_geval hO args hvals] at hv
      simp only at hv
      rw [call] at hv
      split at hv
      · cases hv
      · rw [hP] at hv
        simp only [hf] at hv
        cases hb : bind_all params vals with
        | Ok bs =>
          rw [hb] at hv
          simp only [bind_types] at hv
          rw [← hP] at hv
          exact vf_ext hO hEq hP (zip_lookup params args hvals hb) 100 body t' hvf hv
        | _ => rw [hb] at hv; cases hv
    · cases h
  · cases h

/-- The variable of a substitution by a literal has its value. -/
theorem lit_one (hO : O.Sound) {x : Id} {a : Expr} {va : Value} (hva : geval 100 a = some va)
    {tys : List TypeBinding} {vars : List Binding} {fuel : Int} {env : Env} :
    ∀ z w, [(x, a)].lookup z = some w →
      eval O P fuel (.Env tys (.Binding x va :: vars)) (.Variable z) = eval O P fuel env w := by
  intro z w hz
  rw [List.lookup_cons] at hz
  by_cases hzx : z = x
  · subst hzx
    simp only [beq_self_eq_true] at hz
    cases hz
    rw [geval_eval hO 100 _ hva]
    simp [eval, env_vars, lookup_var]
  · have hne : (z == x) = false := by simp [hzx]
    rw [hne] at hz
    simp at hz

theorem betaCheck_refines (hO : O.Sound) {Fs : List Fact} {t t' : Expr}
    (h : betaCheck t t' = true) : Refines O P Fs t t' := by
  intro fuel env v _ hv
  unfold betaCheck at h
  split at h
  · next x T b a y a' b' =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨ha, h⟩ := h
    rw [← Inox.Lowered.exprEq_eq _ _ _ ha]
    split at h
    · next va w w' hva hw hw' =>
      obtain ⟨b0, hb0, hg0⟩ := Option.bind_eq_some_iff.mp hw
      obtain ⟨b1, hb1, hg1⟩ := Option.bind_eq_some_iff.mp hw'
      cases env with
      | Env tys vars =>
      simp only [eval, eval_list, geval_eval hO 100 a hva] at hv
      simp only [apply, param_ids] at hv
      split at hv
      · cases hv
      · simp only [bind_all, append_env] at hv
        rw [msubst_eval (env := .Env tys (.Binding x va :: vars)) (lit_one hO hva) 100 b b0 hb0,
          geval_eval hO 100 b0 hg0] at hv
        cases hv
        simp only [eval, geval_eval hO 100 a hva, env_bind]
        rw [msubst_eval (env := .Env tys (.Binding y va :: vars)) (lit_one hO hva) 100 b' b1 hb1,
          geval_eval hO 100 b1 hg1, litEq_eq h]
    · cases h
  · cases h

theorem betaVarCheck_refines (hO : O.Sound) {Fs : List Fact} {t t' : Expr}
    (h : betaVarCheck t t' = true) : Refines O P Fs t t' := by
  intro fuel env v _ hv
  unfold betaVarCheck at h
  split at h
  · next x T b z y z' b' =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    split at h
    · next w w' hw hw' =>
      cases env with
      | Env tys vars =>
      simp only [eval, eval_list] at hv ⊢
      cases hz : lookup_var (env_vars (.Env tys vars)) z with
      | Ok vz =>
        rw [hz] at hv
        simp only [apply, param_ids] at hv
        split at hv
        · cases hv
        · simp only [bind_all, append_env] at hv
          rw [geval_eval hO 100 b hw] at hv
          cases hv
          simp only
          rw [geval_eval hO 100 b' hw', litEq_eq h]
      | _ => rw [hz] at hv; simp at hv
    · cases h
  · cases h

theorem letLitCheck_refines (hO : O.Sound) {Fs : List Fact} {t t' : Expr}
    (h : letLitCheck t t' = true) : Refines O P Fs t t' := by
  intro fuel env v _ hv
  unfold letLitCheck at h
  split at h
  · next x a b y a' b' =>
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨⟨ha, va, hva⟩, h⟩ := h
    rw [← Inox.Lowered.exprEq_eq _ _ _ ha]
    split at h
    · next c c' hc hc' =>
      rw [Inox.Lowered.exprEq_eq _ _ _ h] at hc
      cases env with
      | Env tys vars =>
      simp only [eval, geval_eval hO 100 a hva, env_bind] at hv ⊢
      rw [msubst_eval (env := .Env tys vars) (lit_one hO hva) 100 b c' hc] at hv
      rw [msubst_eval (env := .Env tys vars) (lit_one hO hva) 100 b' c' hc']
      exact hv
    · cases h
  · cases h

/-- `logic`: whether a construction is of a constructor, or a conditional on a literal. -/
def testerCheck (t t' : Expr) : Bool :=
  match t, t' with
  | .IsConstructor (.ADT d _ _) c, .BooleanLiteral b => b == decide (c = d)
  | .IfExpr (.BooleanLiteral c) a b, t' => Inox.Lowered.exprEq 1000 (if c then a else b) t'
  | _, _ => false

theorem testerCheck_refines {Fs : List Fact} {t t' : Expr} (h : testerCheck t t' = true) :
    Refines O P Fs t t' := by
  intro fuel env v _ hv
  unfold testerCheck at h
  split at h
  · next d tps es c b =>
    simp only [beq_iff_eq] at h
    subst h
    simp only [eval] at hv ⊢
    cases hl : eval_list O P fuel env es with
    | Ok vs =>
      rw [hl] at hv
      simp only at hv
      cases hc : construct O P fuel env d tps vs with
      | Ok w =>
        rw [hc] at hv
        obtain ⟨_, rfl⟩ := Inox.Lowered.construct_ok hc
        simp only at hv
        exact hv.symm ▸ rfl
      | _ => rw [hc] at hv; cases hv
    | _ => rw [hl] at hv; cases hv
  · rw [← Inox.Lowered.exprEq_eq _ _ _ h]
    simp only [eval, eval_bool] at hv
    split at hv <;> simp_all
  · cases h

end

/-! ## Closures in lets and lambdas -/

/-- A lambda of one parameter of a primitive type whose body mentions only its parameter, and
has no lambdas, calls or constructions. -/
def closedLam : Expr → Bool
  | .Lambda [.Param x T] b => primParam T && (msubst [(x, .Variable x)] 100 b).isSome
  | _ => false

/-- Variables that a term doesn't read, or literals. -/
def atomFree (X : List Id) : Expr → Bool
  | .Variable y => !X.contains y
  | .IntegerLiteral _ | .BooleanLiteral _ => true
  | _ => false

/-- A term whose value is related to itself where the variables `X` have related values: it reads
them only through comparisons, negations, conditionals, testers, selectors, applications and
lambdas, `n` deep. -/
def safe : List Id → Nat → Expr → Bool
  | _, 0, _ => false
  | X, n + 1, e =>
    match e with
    | .Variable _ | .IntegerLiteral _ | .BooleanLiteral _ => true
    | .Equals a b => safe X n a && safe X n b
    | .Not a => safe X n a
    | .IfExpr c a b => safe X n c && safe X n a && safe X n b
    | .IsConstructor a _ => safe X n a
    | .ADTSelector a _ => safe X n a
    | .FunctionInvocation _ _ es => es.all (atomFree X)
    | .Application f es => safe X n f && es.all (atomFree X)
    | .Lambda ps b => safe (X.filter fun y => !(param_ids ps).contains y) n b
    | _ => false

/-- What `G` keeps in the body of `(let ((x v)) b)`: `x` with `v`, if `v` is a closed lambda. -/
def letG (x : Id) (v : Expr) (G : List (Id × Expr)) : List (Id × Expr) :=
  (if closedLam v then [(x, v)] else []) ++ G.filter fun p => p.1 != x && closedLam p.2

/-- What `G` keeps in the body of a lambda of the parameters `ps`. -/
def lamG (ps : List Param) (G : List (Id × Expr)) : List (Id × Expr) :=
  G.filter fun p => !(param_ids ps).contains p.1 && closedLam p.2

/-- `expand`: a variable of `G` is its expression. -/
def gExpand (G : List (Id × Expr)) (t t' : Expr) : Bool :=
  match t with
  | .Variable y => (G.lookup y).any (Inox.Lowered.exprEq 1000 · t')
  | _ => false

section
variable {O : Oracle} {P : Program}

/-- The environments `E1` and `E2` have the same types, related values of the variables `X`,
and the same values of the others. -/
def EnvRel (X : List Id) (E1 E2 : Env) : Prop :=
  env_types E1 = env_types E2 ∧ ∀ y,
    (y ∈ X → ∀ v, lookup_var (env_vars E1) y = .Ok v →
      ∃ v', lookup_var (env_vars E2) y = .Ok v' ∧ Ext O P v v') ∧
    (y ∉ X → lookup_var (env_vars E1) y = lookup_var (env_vars E2) y)

theorem contains_false {X : List Id} {y : Id} : X.contains y = false ↔ y ∉ X := by
  rw [← Bool.not_eq_true, List.contains_iff_mem]

theorem lookup_append : ∀ (ids : List Id) (vs : List Value) {bs : List Binding},
    bind_all ids vs = .Ok bs → ∀ (vars : List Binding) (y : Id),
      lookup_var (append_env bs vars) y = if y ∈ ids then lookup_var bs y else lookup_var vars y
  | [], [], bs, h, vars, y => by simp [bind_all] at h; subst h; simp [append_env]
  | [], _ :: _, _, h, _, _ => by simp [bind_all] at h
  | _ :: _, [], _, h, _, _ => by simp [bind_all] at h
  | x :: xs, v :: vs, bs, h, vars, y => by
    simp only [bind_all] at h
    cases hr : bind_all xs vs with
    | Ok rest =>
      rw [hr] at h
      cases h
      have ih := lookup_append xs vs hr vars y
      by_cases hyx : y = x
      · subst hyx; simp [append_env, lookup_var]
      · simp only [append_env, lookup_var, hyx, dite_false, List.mem_cons, false_or]
        exact ih
    | _ => rw [hr] at h; cases h

theorem envRel_bind {X : List Id} {tys1 tys2 : List TypeBinding} {vars1 vars2 : List Binding}
    (h : EnvRel (O := O) (P := P) X (.Env tys1 vars1) (.Env tys2 vars2)) {ids : List Id}
    {vs : List Value} {bs : List Binding} (hb : bind_all ids vs = .Ok bs) :
    EnvRel (O := O) (P := P) (X.filter fun y => !ids.contains y)
      (.Env tys1 (append_env bs vars1)) (.Env tys2 (append_env bs vars2)) := by
  refine ⟨h.1, fun y => ⟨fun hy v hv => ?_, fun hy => ?_⟩⟩
  · simp only [List.mem_filter, Bool.not_eq_true', contains_false] at hy
    simp only [env_vars, lookup_append ids vs hb, hy.2, ite_false] at hv ⊢
    exact (h.2 y).1 hy.1 v hv
  · simp only [env_vars, lookup_append ids vs hb]
    by_cases hi : y ∈ ids
    · simp [hi]
    · simp only [hi, ite_false]
      have : y ∉ X := fun hx => hy (by simp [List.mem_filter, hx, hi])
      exact (h.2 y).2 this

theorem atom_eval {X : List Id} {E1 E2 : Env} (h : EnvRel (O := O) (P := P) X E1 E2)
    {fuel : Int} : ∀ {e : Expr}, atomFree X e = true → eval O P fuel E1 e = eval O P fuel E2 e
  | .Variable y, ha => by
    simp only [atomFree, Bool.not_eq_true', contains_false] at ha
    simp only [eval]; exact (h.2 y).2 ha
  | .IntegerLiteral _, _ => by simp [eval]
  | .BooleanLiteral _, _ => by simp [eval]

theorem atoms_eval {X : List Id} {E1 E2 : Env} (h : EnvRel (O := O) (P := P) X E1 E2)
    {fuel : Int} : ∀ {es : List Expr}, es.all (atomFree X) = true →
      eval_list O P fuel E1 es = eval_list O P fuel E2 es
  | [], _ => by rw [eval_list, eval_list]
  | e :: es, ha => by
    simp only [List.all_cons, Bool.and_eq_true] at ha
    rw [eval_list, eval_list, atom_eval h ha.1, atoms_eval h ha.2]

theorem apply_det {f : Value} {vs : List Value} {fuel : Int} {a b : Value}
    (ha : apply O P fuel f vs = .Ok a) (hb : apply O P fuel f vs = .Ok b) : a = b := by
  rw [ha] at hb; cases hb; rfl

/-- A safe term evaluates, where the variables `X` have related values, to related values. -/
theorem fl_ext (hO : O.Sound) (hEq : ∀ c, sort_equality P c = none) (hNo : funEq P = false) :
    ∀ (n : Nat) (X : List Id) (e : Expr) {E1 E2 : Env} {fuel : Int} {v : Value},
      safe X n e = true → EnvRel (O := O) (P := P) X E1 E2 → eval O P fuel E1 e = .Ok v →
        ∃ v', eval O P fuel E2 e = .Ok v' ∧ Ext O P v v'
  | 0, _, _, _, _, _, _, h, _, _ => by simp [safe] at h
  | n + 1, X, e, E1, E2, fuel, v, h, hR, hv => by
    have ih := fl_ext hO hEq hNo n
    unfold safe at h
    split at h
    · next y =>
      simp only [eval] at hv ⊢
      by_cases hy : y ∈ X
      · exact (hR.2 y).1 hy v hv
      · rw [← (hR.2 y).2 hy]; exact ⟨v, hv, .refl v⟩
    · simp only [eval] at hv ⊢; exact ⟨v, hv, .refl v⟩
    · simp only [eval] at hv ⊢; exact ⟨v, hv, .refl v⟩
    · next a b =>
      simp only [Bool.and_eq_true] at h
      simp only [eval] at hv ⊢
      cases ha : eval O P fuel E1 a with
      | Ok va =>
        rw [ha] at hv
        obtain ⟨va', ha', hxa⟩ := ih X a h.1 hR ha
        cases hb : eval O P fuel E1 b with
        | Ok vb =>
          rw [hb] at hv
          obtain ⟨vb', hb', hxb⟩ := ih X b h.2 hR hb
          rw [ha', hb']
          simp only at hv ⊢
          rw [← ((ext_same hO hEq hxb) va').1, ← ((ext_same hO hEq hxa) vb).2]
          exact ⟨v, hv, .refl v⟩
        | _ => rw [hb] at hv; cases hv
      | _ => rw [ha] at hv; cases hv
    · next a =>
      simp only [eval, eval_bool] at hv ⊢
      cases ha : eval O P fuel E1 a with
      | Ok va =>
        obtain ⟨va', ha', he⟩ := ih X a h hR ha
        rw [ha] at hv
        rw [ha']
        cases va with
        | BoolV b => rw [ext_bool he]; exact ⟨v, hv, .refl v⟩
        | _ => simp at hv
      | _ => rw [ha] at hv; cases hv
    · next c a b =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hc, hca⟩, hcb⟩ := h
      simp only [eval, eval_bool] at hv ⊢
      cases hcv : eval O P fuel E1 c with
      | Ok vc =>
        obtain ⟨vc', hc', he⟩ := ih X c hc hR hcv
        rw [hcv] at hv
        rw [hc']
        cases vc with
        | BoolV bc =>
          rw [ext_bool he]
          simp only at hv ⊢
          by_cases hbc : bc = true
          · simp only [hbc, dite_true] at hv ⊢; exact ih X a hca hR hv
          · simp only [hbc, dite_false] at hv ⊢; exact ih X b hcb hR hv
        | _ => simp at hv
      | _ => rw [hcv] at hv; cases hv
    · next a c =>
      simp only [eval] at hv ⊢
      cases ha : eval O P fuel E1 a with
      | Ok va =>
        obtain ⟨va', ha', he⟩ := ih X a h hR ha
        rw [ha] at hv
        rw [ha']
        cases he with
        | refl => exact ⟨v, hv, .refl v⟩
        | adt _ => exact ⟨v, hv, .refl v⟩
        | set _ => cases hv
        | clo _ _ _ _ => cases hv
      | _ => rw [ha] at hv; cases hv
    · next a f =>
      simp only [eval] at hv ⊢
      cases ha : eval O P fuel E1 a with
      | Ok va =>
        obtain ⟨va', ha', he⟩ := ih X a h hR ha
        rw [ha] at hv
        rw [ha']
        cases he with
        | refl => exact ⟨v, hv, .refl v⟩
        | adt hs =>
          obtain ⟨_, cs, _, _, _⟩ := P
          simp only at hv ⊢
          cases hk : lookup_ctor cs _ with
          | Ok k =>
            rw [hk] at hv
            obtain ⟨_, _, fields⟩ := k
            exact select_ext hs hv
          | _ => rw [hk] at hv; cases hv
        | set _ => cases hv
        | clo _ _ _ _ => cases hv
      | _ => rw [ha] at hv; cases hv
    · next f tps es =>
      simp only [eval] at hv ⊢
      rw [← atoms_eval hR h, ← hR.1]
      exact ⟨v, hv, .refl v⟩
    · next f es =>
      simp only [Bool.and_eq_true] at h
      simp only [eval] at hv ⊢
      cases ha : eval O P fuel E1 f with
      | Ok va =>
        obtain ⟨va', ha', he⟩ := ih X f h.1 hR ha
        rw [ha] at hv
        rw [ha', ← atoms_eval hR h.2]
        cases hvs : eval_list O P fuel E1 es with
        | Ok vs =>
          rw [hvs] at hv
          simp only at hv ⊢
          cases he with
          | refl => exact ⟨v, hv, .refl v⟩
          | adt _ => unfold apply at hv; cases hv
          | set _ => unfold apply at hv; cases hv
          | clo hty hok hback hr =>
            obtain ⟨v', hv'⟩ := hok fuel vs ⟨v, hv⟩
            exact ⟨v', hv', hr fuel vs v v' hv hv'⟩
        | _ => rw [hvs] at hv; cases hv
      | _ => rw [ha] at hv; cases hv
    · next ps b =>
      simp only [eval] at hv ⊢
      cases hv
      cases E1 with
      | Env tys1 vars1 =>
      cases E2 with
      | Env tys2 vars2 =>
      have key : ∀ fuel vs a, apply O P fuel (.ClosureV ps b (.Env tys1 vars1)) vs = .Ok a →
          ∃ a', apply O P fuel (.ClosureV ps b (.Env tys2 vars2)) vs = .Ok a' ∧
            Ext O P a a' := by
        intro fuel vs a ha
        simp only [apply] at ha ⊢
        split at ha
        · cases ha
        · next hf =>
          simp only [hf, dite_false]
          cases hb : bind_all (param_ids ps) vs with
          | Ok bs =>
            rw [hb] at ha
            simp only at ha ⊢
            exact ih _ b h (envRel_bind hR hb) ha
          | _ => rw [hb] at ha; cases ha
      refine ⟨_, rfl, .clo (fun hf => by simp [hNo] at hf) (fun fuel vs ⟨a, ha⟩ => ?_)
        (fun hf => by simp [hNo] at hf) (fun fuel vs a a' ha ha' => ?_)⟩
      · obtain ⟨a', ha', _⟩ := key fuel vs a ha
        exact ⟨a', ha'⟩
      · obtain ⟨a'', ha'', hx⟩ := key fuel vs a ha
        rw [apply_det ha' ha'']
        exact hx
    · cases h

theorem closed_body {x : Id} {b b0 : Expr} (h : msubst [(x, .Variable x)] 100 b = some b0)
    {fuel : Int} {tys1 tys2 : List TypeBinding} {vars1 vars2 : List Binding} {u : Value} :
    eval O P fuel (.Env tys1 (.Binding x u :: vars1)) b =
      eval O P fuel (.Env tys2 (.Binding x u :: vars2)) b := by
  have hv : ∀ (tys tys' : List TypeBinding) (vars vars' : List Binding),
      ∀ z w, [(x, Expr.Variable x)].lookup z = some w →
        eval O P fuel (.Env tys (.Binding x u :: vars)) (.Variable z) =
          eval O P fuel (.Env tys' (.Binding x u :: vars')) w := by
    intro tys tys' vars vars' z w hz
    rw [List.lookup_cons] at hz
    by_cases hzx : z = x
    · subst hzx
      simp only [beq_self_eq_true] at hz
      cases hz
      simp [eval, env_vars, lookup_var]
    · have hne : (z == x) = false := by simp [hzx]
      rw [hne] at hz
      simp at hz
  rw [msubst_eval (hv tys1 tys2 vars1 vars2) 100 b b0 h,
    ← msubst_eval (hv tys2 tys2 vars2 vars2) 100 b b0 h]

theorem closedLam_ok {e : Expr} (h : closedLam e = true) (fuel : Int) (E : Env) :
    ∃ w, eval O P fuel E e = .Ok w := by
  unfold closedLam at h
  split at h
  · simp [eval]
  · cases h

theorem closedLam_ext (hO : O.Sound) {e : Expr} (h : closedLam e = true) {fuel1 fuel2 : Int}
    {E1 E2 : Env} {w1 w2 : Value} (h1 : eval O P fuel1 E1 e = .Ok w1)
    (h2 : eval O P fuel2 E2 e = .Ok w2) : Ext O P w1 w2 := by
  unfold closedLam at h
  split at h
  · next x T b =>
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨hT, b0, hb0⟩ := h
    simp only [eval] at h1 h2
    cases h1
    cases h2
    cases E1 with
    | Env tys1 vars1 =>
    cases E2 with
    | Env tys2 vars2 =>
    have hap : ∀ fuel vs, apply O P fuel (.ClosureV [.Param x T] b (.Env tys1 vars1)) vs =
        apply O P fuel (.ClosureV [.Param x T] b (.Env tys2 vars2)) vs := by
      intro fuel vs
      simp only [apply, param_ids]
      split
      · rfl
      · cases vs with
        | nil => simp [bind_all]
        | cons u vs =>
          cases vs with
          | cons _ _ => simp [bind_all]
          | nil => simp only [bind_all, append_env]; exact closed_body hb0
    refine .clo (fun _ vs => ?_) (fun fuel vs h => by rw [← hap]; exact h)
      (fun _ fuel vs h => by rw [hap]; exact h) (fun fuel vs a a' h1 h2 => ?_)
    · cases T <;> simp [primParam] at hT <;>
        (cases vs with
          | nil => simp [hO.params_have_types]
          | cons u vs => cases vs <;> simp [hO.params_have_types, hO.has_type])
    · rw [hap, h2] at h1
      cases h1
      exact .refl _
  · cases h

theorem mem_of_lookup' {G : List (Id × Expr)} {y : Id} {e : Expr} (h : G.lookup y = some e) :
    (y, e) ∈ G := by
  induction G with
  | nil => simp at h
  | cons p G ih =>
    obtain ⟨k, w⟩ := p
    rw [List.lookup_cons] at h
    by_cases hyk : y = k
    · subst hyk
      simp only [beq_self_eq_true] at h
      cases h
      exact List.mem_cons_self
    · have hne : (y == k) = false := by simp [hyk]
      rw [hne] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem gExpand_refines {Fs : List Fact} {G : List (Id × Expr)} {t t' : Expr}
    (h : gExpand G t t' = true) : RefinesG (O := O) (P := P) Fs G t t' := by
  intro fuel env v _ hG hv
  unfold gExpand at h
  split at h
  · next y =>
    simp only [Option.any_eq_true] at h
    obtain ⟨e, he, hq⟩ := h
    rw [← Inox.Lowered.exprEq_eq _ _ _ hq]
    obtain ⟨w, hw, w', hw', hx⟩ := hG y e (mem_of_lookup' he)
    simp only [eval] at hv
    rw [hv] at hw
    cases hw
    exact ⟨w', hw', hx⟩
  · cases h

theorem refinesG_IsConstructor {Fs : List Fact} {G : List (Id × Expr)} {a a' : Expr} {c : Id}
    (h : RefinesG (O := O) (P := P) Fs G a a') :
    RefinesG (O := O) (P := P) Fs G (.IsConstructor a c) (.IsConstructor a' c) := by
  intro fuel env v hF hG hv
  simp only [eval] at hv ⊢
  cases ha : eval O P fuel env a with
  | Ok va =>
    obtain ⟨va', ha', he⟩ := h fuel env va hF hG ha
    rw [ha] at hv
    rw [ha']
    cases he with
    | refl => exact ⟨v, hv, .refl v⟩
    | adt _ => exact ⟨v, hv, .refl v⟩
    | set _ => cases hv
    | clo _ _ _ _ => cases hv
  | _ => rw [ha] at hv; cases hv

theorem refinesG_IfExpr_1 {Fs : List Fact} {G : List (Id × Expr)} {c c' a b : Expr}
    (h : RefinesG (O := O) (P := P) Fs G c c') :
    RefinesG (O := O) (P := P) Fs G (.IfExpr c a b) (.IfExpr c' a b) := by
  intro fuel env v hF hG hv
  simp only [eval, eval_bool] at hv ⊢
  cases hcv : eval O P fuel env c with
  | Ok vc =>
    obtain ⟨vc', hc', he⟩ := h fuel env vc hF hG hcv
    rw [hcv] at hv
    rw [hc']
    cases vc with
    | BoolV bc => rw [ext_bool he]; exact ⟨v, hv, .refl v⟩
    | _ => simp at hv
  | _ => rw [hcv] at hv; cases hv

theorem refinesG_IfExpr_2 {Fs : List Fact} {G : List (Id × Expr)} {c a a' b : Expr}
    (h : RefinesG (O := O) (P := P) Fs G a a') :
    RefinesG (O := O) (P := P) Fs G (.IfExpr c a b) (.IfExpr c a' b) := by
  intro fuel env v hF hG hv
  simp only [eval] at hv ⊢
  cases hcv : eval_bool O P fuel env c with
  | Ok bc =>
    rw [hcv] at hv
    simp only at hv ⊢
    by_cases hbc : bc = true
    · simp only [hbc, dite_true] at hv ⊢; exact h fuel env v hF hG hv
    · simp only [hbc, dite_false] at hv ⊢; exact ⟨v, hv, .refl v⟩
  | _ => rw [hcv] at hv; cases hv

theorem refinesG_IfExpr_3 {Fs : List Fact} {G : List (Id × Expr)} {c a b b' : Expr}
    (h : RefinesG (O := O) (P := P) Fs G b b') :
    RefinesG (O := O) (P := P) Fs G (.IfExpr c a b) (.IfExpr c a b') := by
  intro fuel env v hF hG hv
  simp only [eval] at hv ⊢
  cases hcv : eval_bool O P fuel env c with
  | Ok bc =>
    rw [hcv] at hv
    simp only at hv ⊢
    by_cases hbc : bc = true
    · simp only [hbc, dite_true] at hv ⊢; exact ⟨v, hv, .refl v⟩
    · simp only [hbc, dite_false] at hv ⊢; exact h fuel env v hF hG hv
  | _ => rw [hcv] at hv; cases hv

theorem refinesG_LetV (hO : O.Sound) (hEq : ∀ c, sort_equality P c = none)
    (hNo : funEq P = false) {Fs : List Fact} {G : List (Id × Expr)} {x : Id} {v v' b : Expr}
    (hs : safe [x] 100 b = true) (h : RefinesG (O := O) (P := P) Fs G v v') :
    RefinesG (O := O) (P := P) Fs G (.Let x v b) (.Let x v' b) := by
  intro fuel env w hF hG hw
  simp only [eval] at hw ⊢
  cases hv : eval O P fuel env v with
  | Ok vv =>
    rw [hv] at hw
    obtain ⟨vv', hv', he⟩ := h fuel env vv hF hG hv
    rw [hv']
    simp only at hw ⊢
    cases env with
    | Env tys vars =>
    refine fl_ext (E1 := env_bind (.Env tys vars) x vv) (E2 := env_bind (.Env tys vars) x vv')
      hO hEq hNo 100 [x] b hs ⟨rfl, fun y => ⟨fun hy u hu => ?_, fun hy => ?_⟩⟩ hw
    · simp only [List.mem_singleton] at hy
      subst hy
      simp only [env_bind, env_vars, lookup_var, dite_true] at hu ⊢
      cases hu
      exact ⟨vv', rfl, he⟩
    · simp only [List.mem_singleton] at hy
      simp [env_bind, env_vars, lookup_var, hy]
  | _ => rw [hv] at hw; cases hw

theorem gHolds_let (hO : O.Sound) {G : List (Id × Expr)} {x : Id} {v : Expr} {fuel : Int}
    {env : Env} {vv : Value} (hv : eval O P fuel env v = .Ok vv)
    (hG : GHolds (O := O) (P := P) G fuel env) :
    GHolds (O := O) (P := P) (letG x v G) fuel (env_bind env x vv) := by
  intro y e hye
  cases env with
  | Env tys vars =>
  simp only [letG, List.mem_append, List.mem_filter, Bool.and_eq_true, bne_iff_ne,
    ne_eq] at hye
  rcases hye with hye | ⟨hye, hyx, hc⟩
  · split at hye
    · next hc =>
      simp only [List.mem_singleton, Prod.mk.injEq] at hye
      obtain ⟨rfl, rfl⟩ := hye
      obtain ⟨w', hw'⟩ := closedLam_ok (O := O) (P := P) hc fuel (env_bind (.Env tys vars) y vv)
      exact ⟨vv, by simp [env_bind, env_vars, lookup_var], w', hw', closedLam_ext hO hc hv hw'⟩
    · simp at hye
  · obtain ⟨w, hw, w', hw', hx⟩ := hG y e hye
    obtain ⟨w'', hw''⟩ := closedLam_ok (O := O) (P := P) hc fuel (env_bind (.Env tys vars) x vv)
    refine ⟨w, ?_, w'', hw'', ext_trans hx (closedLam_ext hO hc hw' hw'')⟩
    simp only [env_bind, env_vars, lookup_var, hyx, dite_false] at hw ⊢
    exact hw

theorem refinesG_LetB (hO : O.Sound) {Fs : List Fact} {G : List (Id × Expr)} {x : Id}
    {v b b' : Expr} (h : RefinesG (O := O) (P := P) [] (letG x v G) b b') :
    RefinesG (O := O) (P := P) Fs G (.Let x v b) (.Let x v b') := by
  intro fuel env w _ hG hw
  simp only [eval] at hw ⊢
  cases hv : eval O P fuel env v with
  | Ok vv =>
    rw [hv] at hw
    simp only at hw ⊢
    exact h fuel _ w (fun _ h => by simp at h) (gHolds_let hO hv hG) hw
  | _ => rw [hv] at hw; cases hw

theorem refinesG_Lam (hO : O.Sound) (hNo : funEq P = false) {Fs : List Fact}
    {G : List (Id × Expr)} {ps : List Param} {b b' : Expr}
    (h : RefinesG (O := O) (P := P) [] (lamG ps G) b b') :
    RefinesG (O := O) (P := P) Fs G (.Lambda ps b) (.Lambda ps b') := by
  intro fuel env w _ hG hw
  simp only [eval] at hw ⊢
  cases hw
  cases env with
  | Env tys vars =>
  have key : ∀ fuel' vs a, apply O P fuel' (.ClosureV ps b (.Env tys vars)) vs = .Ok a →
      ∃ a', apply O P fuel' (.ClosureV ps b' (.Env tys vars)) vs = .Ok a' ∧ Ext O P a a' := by
    intro fuel' vs a ha
    simp only [apply] at ha ⊢
    split at ha
    · cases ha
    · next hf =>
      simp only [hf, dite_false]
      cases hb : bind_all (param_ids ps) vs with
      | Ok bs =>
        rw [hb] at ha
        simp only at ha ⊢
        refine h (fuel' - 1) _ a (fun _ h => by simp at h) (fun y e hye => ?_) ha
        simp only [lamG, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
          contains_false] at hye
        obtain ⟨hye, hyi, hc⟩ := hye
        obtain ⟨u, hu, u', hu', hx⟩ := hG y e hye
        obtain ⟨u'', hu''⟩ := closedLam_ok (O := O) (P := P) hc (fuel' - 1)
          (.Env tys (append_env bs vars))
        refine ⟨u, ?_, u'', hu'', ext_trans hx (closedLam_ext hO hc hu' hu'')⟩
        simp only [env_vars, lookup_append _ vs hb, hyi, ite_false] at hu ⊢
        exact hu
      | _ => rw [hb] at ha; cases ha
  refine ⟨_, rfl, .clo (fun hf => by simp [hNo] at hf) (fun fuel vs ⟨a, ha⟩ => ?_)
    (fun hf => by simp [hNo] at hf) (fun fuel vs a a' ha ha' => ?_)⟩
  · obtain ⟨a', ha', _⟩ := key fuel vs a ha
    exact ⟨a', ha'⟩
  · obtain ⟨a'', ha'', hx⟩ := key fuel vs a ha
    rw [apply_det ha' ha'']
    exact hx

end

/-- `e` where the subterm at the position `p` is what `r` makes of it, through the operands that
compare or apply values up to closures, the conditionals, the lets and, where functions aren't
compared, the values of lets whose bodies are safe and the bodies of lambdas, under the facts
`Fs` and the variables `G` with the values of closed lambdas. -/
def rewriteX (fe : Bool) (r : List Fact → List (Id × Expr) → Expr → Option Expr) :
    List Fact → List (Id × Expr) → List Nat → Expr → Option Expr
  | Fs, G, [], e => r Fs G e
  | Fs, G, 1 :: p, .Not a => (rewriteX fe r Fs G p a).map .Not
  | Fs, G, 1 :: p, .Equals a b => (rewriteX fe r Fs G p a).map (.Equals · b)
  | Fs, G, 2 :: p, .Equals a b => (rewriteX fe r Fs G p b).map (.Equals a ·)
  | Fs, G, 1 :: p, .ADTSelector a f => (rewriteX fe r Fs G p a).map (.ADTSelector · f)
  | Fs, G, 1 :: p, .IsConstructor a c => (rewriteX fe r Fs G p a).map (.IsConstructor · c)
  | Fs, G, 1 :: p, .Application a es => (rewriteX fe r Fs G p a).map (.Application · es)
  | Fs, G, 1 :: p, .ElementOfSet a s => (rewriteX fe r Fs G p a).map (.ElementOfSet · s)
  | Fs, G, 2 :: p, .ElementOfSet a s => (rewriteX fe r Fs G p s).map (.ElementOfSet a ·)
  | Fs, G, 1 :: p, .SetAdd s a => (rewriteX fe r Fs G p s).map (.SetAdd · a)
  | Fs, G, 2 :: p, .SetAdd s a => (rewriteX fe r Fs G p a).map (.SetAdd s ·)
  | Fs, G, 1 :: p, .IfExpr c a b => (rewriteX fe r Fs G p c).map (.IfExpr · a b)
  | Fs, G, 2 :: p, .IfExpr c a b => (rewriteX fe r Fs G p a).map (.IfExpr c · b)
  | Fs, G, 3 :: p, .IfExpr c a b => (rewriteX fe r Fs G p b).map (.IfExpr c a ·)
  | _, G, 2 :: p, .Let x v b => (rewriteX fe r [] (letG x v G) p b).map (.Let x v ·)
  | Fs, G, 1 :: 0 :: 1 :: p, .Let x v b =>
    if !fe && safe [x] 100 b then (rewriteX fe r Fs G p v).map (.Let x · b) else none
  | _, G, 2 :: p, .Lambda ps b =>
    if !fe then (rewriteX fe r [] (lamG ps G) p b).map (.Lambda ps ·) else none
  | _, _, _, _ => none

section
variable {O : Oracle} {P : Program}

theorem rewriteX_refines (hO : O.Sound) (hEq : ∀ c, sort_equality P c = none) {fe : Bool}
    (hfe : fe = false → funEq P = false)
    {r : List Fact → List (Id × Expr) → Expr → Option Expr}
    (hr : ∀ Fs G t t', r Fs G t = some t' → RefinesG (O := O) (P := P) Fs G t t') :
    ∀ (Fs : List Fact) (G : List (Id × Expr)) (p : List Nat) (e e' : Expr),
      rewriteX fe r Fs G p e = some e' → RefinesG (O := O) (P := P) Fs G e e'
  | Fs, G, [], e, e', h => hr Fs G e e' (by simpa [rewriteX] using h)
  | Fs, G, i :: p, e, e', h => by
    unfold rewriteX at h
    split at h
    all_goals first
      | (obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
         have ih := rewriteX_refines hO hEq hfe hr _ _ _ _ _ ht
         first
          | exact refinesX_Not ih
          | exact refinesX_Equals_1 hO hEq ih
          | exact refinesX_Equals_2 hO hEq ih
          | exact refinesX_ADTSelector ih
          | exact refinesG_IsConstructor ih
          | exact refinesX_Application ih
          | exact refinesX_ElementOfSet_1 hO hEq ih
          | exact refinesX_ElementOfSet_2 hO hEq ih
          | exact refinesX_SetAdd_1 hO hEq ih
          | exact refinesX_SetAdd_2 hO hEq ih
          | exact refinesG_IfExpr_1 ih
          | exact refinesG_IfExpr_2 ih
          | exact refinesG_IfExpr_3 ih
          | exact refinesG_LetB hO ih)
      | (split at h
         · next hc =>
           obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
           have ih := rewriteX_refines hO hEq hfe hr _ _ _ _ _ ht
           simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
           first
            | exact refinesG_LetV hO hEq (hfe hc.1) hc.2 ih
            | exact refinesG_Lam hO (hfe hc) ih
         · cases h)
      | cases h
      | simp_all

end

/-- The subterm at the position `p`, through the operands of `rewriteX`. -/
def subAt : List Nat → Expr → Option Expr
  | [], e => some e
  | 1 :: p, .Not a => subAt p a
  | 1 :: p, .Equals a _ => subAt p a
  | 2 :: p, .Equals _ b => subAt p b
  | 1 :: p, .ADTSelector a _ => subAt p a
  | 1 :: p, .IsConstructor a _ => subAt p a
  | 1 :: p, .Application a _ => subAt p a
  | 1 :: p, .ElementOfSet a _ => subAt p a
  | 2 :: p, .ElementOfSet _ s => subAt p s
  | 1 :: p, .SetAdd s _ => subAt p s
  | 2 :: p, .SetAdd _ a => subAt p a
  | 1 :: p, .IfExpr c _ _ => subAt p c
  | 2 :: p, .IfExpr _ a _ => subAt p a
  | 3 :: p, .IfExpr _ _ b => subAt p b
  | 2 :: p, .Let _ _ b => subAt p b
  | 1 :: 0 :: 1 :: p, .Let _ v _ => subAt p v
  | 2 :: p, .Lambda _ b => subAt p b
  | _, _ => none

/-- A step of `rename` of the parameter of a lambda, as the step that rewrites the lambda into its
renaming. -/
def renameStep (e : Expr) (s : Step) : Step :=
  if s.rule == "rename" && s.pos.reverse.take 3 == [0, 0, 1] then
    let q := s.pos.take (s.pos.length - 3)
    match subAt q e, s.result with
    | some (.Lambda [.Param x T] b), .Variable y =>
      match subst x (.Variable y) 100 b with
      | some b' => ⟨"rename", q, .Lambda [.Param y T] b'⟩
      | none => s
    | _, _ => s
  else s

/-- `e` after the steps `ss`, if each of them holds, in a program whose functions are `fns`,
whose constructors are `cs` and that compares functions where `fe`, where the facts `Fs` hold: a
step that doesn't keep the value through the operands of `rewriteAt` may keep it up to closures,
through those of `rewriteX`, where the sorts have no equalities of their own. -/
def stepsApplyX (cs : List Constructor) (ss : List ADTSort) (fns : List FunDef) (fe : Bool)
    (Fs : List Fact) : List Step → Expr → Option Expr
  | [], e => some e
  | s0 :: steps, e =>
    let s := renameStep e s0
    match rewriteAt (fun Fs t => if ruleCheck cs ss s.rule Fs t s.result then some s.result
        else none) (fun Fs t t' => revCheck cs ss s.rule Fs t t') Fs s.pos e with
    | some e1 => stepsApplyX cs ss fns fe Fs steps e1
    | none =>
      if noEq ss then
        (rewriteX fe (fun Fs G t =>
          if ruleCheck cs ss s.rule Fs t s.result ||
            ((s.rule == "evaluate" || s.rule == "unfold" || s.rule == "rename") &&
              (callCheck cs ss fns t s.result ||
              vfCheck cs ss [] 100 t s.result || memberCheck cs ss Fs t s.result)) ||
            (s.rule == "beta" && (betaCheck t s.result || betaVarCheck t s.result)) ||
            (s.rule == "logic" && (letLitCheck t s.result || testerCheck t s.result)) ||
            (s.rule == "expand" && gExpand G t s.result) then some s.result else none)
          Fs [] s.pos e).bind (stepsApplyX cs ss fns fe Fs steps)
      else none

/-- The steps that hold refine the expression that they start from, up to closures. -/
theorem stepsApplyX_refines {O : Oracle} {P : Program} {fns : List FunDef}
    {cs : List Constructor} {ss : List ADTSort} {is : List Interpretation}
    {eqm : FunctionEquality} (hO : O.Sound) (hP : P = .Program fns cs ss is eqm) {fe : Bool}
    (hfe : fe = false → funEq P = false) (Fs : List Fact) :
    ∀ (steps : List Step) (e e' : Expr), stepsApplyX cs ss fns fe Fs steps e = some e' →
      RefinesX (O := O) (P := P) Fs e e'
  | [], e, e', h => by
    simp [stepsApplyX] at h; subst h; exact refinesX_of refines_refl
  | s0 :: steps, e, e', h => by
    simp only [stepsApplyX] at h
    generalize renameStep e s0 = s at h
    split at h
    · next e1 h1 =>
      refine refinesX_trans (refinesX_of (rewriteAt_refines hO ?_ ?_ Fs s.pos e e1 h1))
        (stepsApplyX_refines hO hP hfe Fs steps e1 e' h)
      · intro Fs t t' ht
        split at ht
        · next hc => cases ht; exact ruleCheck_refines hO ⟨fns, is, eqm, hP⟩ hc
        · cases ht
      · intro Fs t t' ht hq
        split at ht
        · cases ht; exact revCheck_refines hP hq
        · cases ht
    · split at h
      · next hne =>
        have hEq := fun c => (hP ▸ sort_equality_none (fs := fns) (is := is) (eqm := eqm) hne c :
          sort_equality P c = none)
        obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
        refine refinesX_trans
          (refinesX_of_G (rewriteX_refines hO hEq hfe (fun Fs G t t' ht => ?_) Fs [] s.pos e e1 h1))
          (stepsApplyX_refines hO hP hfe Fs steps e1 e' h2)
        split at ht
        · next hc =>
          cases ht
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hc
          rcases hc with ((((hc | ⟨_, hc⟩) | ⟨_, hc⟩) | ⟨_, hc⟩) | ⟨_, hc⟩)
          · exact refinesG_of (refinesX_of (ruleCheck_refines hO ⟨fns, is, eqm, hP⟩ hc))
          · rcases hc with (hc | hc) | hc
            · exact refinesG_of (callCheck_refinesX hO hEq hP hc)
            · intro fuel env v _ _ hv
              cases env with
              | Env tys vars =>
              exact vf_ext hO hEq hP (σ := []) (fun _ _ h => by simp at h) 100 t _ hc hv
            · exact refinesG_of (refinesX_of (memberCheck_refines hO hP hc))
          · rcases hc with hc | hc
            · exact refinesG_of (refinesX_of (betaCheck_refines hO hc))
            · exact refinesG_of (refinesX_of (betaVarCheck_refines hO hc))
          · rcases hc with hc | hc
            · exact refinesG_of (refinesX_of (letLitCheck_refines hO hc))
            · exact refinesG_of (refinesX_of (testerCheck_refines hc))
          · exact gExpand_refines hc
        · cases ht
      · cases h

end Inox.Closures
