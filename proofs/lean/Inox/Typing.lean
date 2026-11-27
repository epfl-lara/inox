/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Semantics

/-!
# Types whose values are the same in two programs

The values of a type of integers, booleans, sorts and refinements of these by predicates on
integers and booleans are typed in a program by the definitions of its sorts and the meaning
of the predicates alone. Two programs that define these sorts alike type their values alike
(`has_type_same`), whatever else they define and whatever the values of the variables.
-/

namespace Inox.Typing

open Inox.Semantics

/-- The predicates on the variable `x` alone, of integers and booleans. -/
inductive PureExpr (x : Id) : Expr → Prop where
  | var : PureExpr x (.Variable x)
  | int (n : Int) : PureExpr x (.IntegerLiteral n)
  | bool (b : Bool) : PureExpr x (.BooleanLiteral b)
  | plus {a b : Expr} : PureExpr x a → PureExpr x b → PureExpr x (.Plus a b)
  | minus {a b : Expr} : PureExpr x a → PureExpr x b → PureExpr x (.Minus a b)
  | lt {a b : Expr} : PureExpr x a → PureExpr x b → PureExpr x (.LessThan a b)
  | gt {a b : Expr} : PureExpr x a → PureExpr x b → PureExpr x (.GreaterThan a b)
  | le {a b : Expr} : PureExpr x a → PureExpr x b → PureExpr x (.LessEquals a b)
  | ge {a b : Expr} : PureExpr x a → PureExpr x b → PureExpr x (.GreaterEquals a b)
  | not {a : Expr} : PureExpr x a → PureExpr x (.Not a)

variable {O : Oracle}

/-- A predicate on `x` evaluates alike in any program, whatever the other variables. -/
theorem eval_pure {Q Q' : Program} {x : Id} {v : Value} {p : Expr} (h : PureExpr x p)
    (fuel : Int) (t t' : List TypeBinding) (vs vs' : List Binding) :
    eval O Q fuel (.Env t (.Binding x v :: vs)) p =
      eval O Q' fuel (.Env t' (.Binding x v :: vs')) p := by
  induction h with
  | var => simp [eval, env_vars, lookup_var]
  | int n => simp [eval]
  | bool b => simp [eval]
  | plus _ _ iha ihb => simp only [eval, iha, ihb]
  | minus _ _ iha ihb => simp only [eval, iha, ihb]
  | lt _ _ iha ihb => simp only [eval, iha, ihb]
  | gt _ _ iha ihb => simp only [eval, iha, ihb]
  | le _ _ iha ihb => simp only [eval, iha, ihb]
  | ge _ _ iha ihb => simp only [eval, iha, ihb]
  | not _ iha => simp only [eval, eval_bool, iha]

/-- Sorts: their type parameters and their constructors, with their fields. -/
abbrev Sorts := Id → Option (List Id × List (Id × List Param))

def paramTy : Param → Ty
  | .Param _ t => t

/-- The types of integers, booleans, the type parameters `B`, sorts of `D` with arguments of
these that satisfy `ok`, and refinements of these by predicates on integers and booleans. -/
inductive PureTy (D : Sorts) (ok : Ty → Prop) : List Id → Ty → Prop where
  | int (B : List Id) : PureTy D ok B .IntegerType
  | bool (B : List Id) : PureTy D ok B .BooleanType
  | tparam {B : List Id} {a : Id} (h : a ∈ B) : PureTy D ok B (.TypeParameter a)
  | adt {B : List Id} {s : Id} {args : List Ty} {tps : List Id}
      {ctors : List (Id × List Param)} (hs : D s = some (tps, ctors))
      (hl : args.length = tps.length) (ha : ∀ t ∈ args, PureTy D ok B t)
      (hok : ∀ t ∈ args, ok t) : PureTy D ok B (.ADTType s args)
  | refine {B : List Id} {x : Id} {t : Ty} {p : Expr} (ht : PureTy D ok B t)
      (hp : PureExpr x p) : PureTy D ok B (.RefinementType x t p)

/-- The fields of the sorts are of these types, of their type parameters. -/
def SortsWF (D : Sorts) (ok : Ty → Prop) : Prop :=
  ∀ s tps ctors, D s = some (tps, ctors) → ∀ c ps, (c, ps) ∈ ctors → ∀ p ∈ ps,
    PureTy D ok tps (paramTy p)

/-- The program defines the sorts as `D` does, without invariants nor equalities. -/
def SortsIn (D : Sorts) : Program → Prop
  | .Program _ cs ss _ _ => ∀ s tps ctors, D s = some (tps, ctors) →
      lookup_sort ss s = .Ok (.Sort s tps none none) ∧
      (∀ c ps, (c, ps) ∈ ctors → lookup_ctor cs c = .Ok (.Constructor c s ps)) ∧
      (∀ c c' ps, lookup_ctor cs c = .Ok (.Constructor c' s ps) → (c, ps) ∈ ctors)

/-- The type parameters `B` are bound alike in `tenv` and `tenv'`, to types of `PureTy`, up to
`n` bindings deep. -/
def Cond (D : Sorts) (ok : Ty → Prop) : Nat → List Id → List TypeBinding → List TypeBinding →
    Prop
  | 0, B, _, _ => B = []
  | n + 1, B, tenv, tenv' => ∀ a ∈ B, ∃ y u uenv uenv' B', lookup_type tenv a =
      some (.TypeBinding y u uenv) ∧ lookup_type tenv' a = some (.TypeBinding y u uenv') ∧
      PureTy D ok B' u ∧ ok u ∧ Cond D ok n B' uenv uenv'

theorem lookup_bind : ∀ (tps : List Id) (args : List Ty) (a : Id),
    a ∈ tps → args.length = tps.length →
      ∃ t ∈ args, ∀ tenv', lookup_type (bind_types tps args tenv') a =
        some (.TypeBinding a t tenv')
  | [], _, a, h, _ => by simp at h
  | b :: tps, [], a, _, hl => by simp at hl
  | b :: tps, t :: args, a, h, hl => by
    by_cases hab : a = b
    · subst hab
      exact ⟨t, by simp, fun tenv' => by simp [bind_types, lookup_type]⟩
    · have h' : a ∈ tps := by simpa [hab] using h
      obtain ⟨t', ht', e⟩ := lookup_bind tps args a h' (by simpa using hl)
      exact ⟨t', by simp [ht'], fun tenv' => by simp [bind_types, lookup_type, hab, e tenv']⟩

theorem cond_bind {D : Sorts} {ok : Ty → Prop} {n : Nat} {B tps : List Id} {args : List Ty}
    {tenv tenv' : List TypeBinding} (ha : ∀ t ∈ args, PureTy D ok B t) (hok : ∀ t ∈ args, ok t)
    (hl : args.length = tps.length) (hC : Cond D ok n B tenv tenv') :
    Cond D ok (n + 1) tps (bind_types tps args tenv) (bind_types tps args tenv') := by
  intro a hab
  obtain ⟨t, ht, e⟩ := lookup_bind tps args a hab hl
  exact ⟨a, t, tenv, tenv', B, e tenv, e tenv', ha t ht, hok t ht, hC⟩

/-- Types of `PureTy` resolve alike where their type parameters are bound alike. -/
theorem resolve_same (hO : O.Sound) {D : Sorts} {ok : Ty → Prop} :
    ∀ (n : Nat) {B : List Id} {T : Ty} {tenv tenv' : List TypeBinding}, PureTy D ok B T →
      Cond D ok n B tenv tenv' → O.resolve tenv T = O.resolve tenv' T := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro B T tenv tenv' hT
  induction hT generalizing tenv tenv' with
  | int => intro _; rw [hO.resolve, hO.resolve]
  | bool => intro _; rw [hO.resolve, hO.resolve]
  | @tparam a h =>
    intro hC
    cases n with
    | zero => simp only [Cond] at hC; subst hC; simp at h
    | succ m =>
      obtain ⟨y, u, uenv, uenv', B', h1, h2, hu, _, hC'⟩ := hC a h
      rw [hO.resolve, hO.resolve]
      simp only []
      rw [h1, h2]
      exact ihn m (Nat.lt_succ_self m) hu hC'
  | @adt s args tps ctors hs hl ha hok iha =>
    intro hC
    rw [hO.resolve, hO.resolve]
    simp only [Ty.ADTType.injEq, true_and]
    have : ∀ ts : List Ty, (∀ t ∈ ts, O.resolve tenv t = O.resolve tenv' t) →
        O.resolve_all tenv ts = O.resolve_all tenv' ts := by
      intro ts h
      induction ts with
      | nil => rw [hO.resolve_all, hO.resolve_all]
      | cons t ts ih =>
        rw [hO.resolve_all, hO.resolve_all (ts := t :: ts)]
        simp only [h t (by simp), ih (fun t' ht' => h t' (by simp [ht']))]
    exact this args (fun t ht => iha t ht hC)
  | refine _ _ ih =>
    intro hC
    rw [hO.resolve, hO.resolve]
    simp only [ih hC]

theorem mem_of_lookup' {β : Type} : ∀ {l : List (Id × β)} {c : Id} {v : β},
    l.lookup c = some v → (c, v) ∈ l
  | [], _, _, h => by simp at h
  | (d, w) :: rest, c, v, h => by
    by_cases hcd : c = d
    · subst hcd
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h
      simp
    · have hb : (c == d) = false := by simpa using hcd
      have h' : rest.lookup c = some v := by simpa only [List.lookup, hb] using h
      exact List.mem_cons_of_mem _ (mem_of_lookup' h')

theorem lookup_of_mem' {β : Type} : ∀ {l : List (Id × β)} {c : Id} {v : β},
    (c, v) ∈ l → ∃ w, l.lookup c = some w
  | [], _, _, h => by simp at h
  | (d, w) :: rest, c, v, h => by
    by_cases hcd : c = d
    · subst hcd
      exact ⟨w, by simp [List.lookup]⟩
    · have h' : (c, v) ∈ rest := by
        rcases List.mem_cons.1 h with h | h
        · simp at h; exact absurd h.1 hcd
        · exact h
      obtain ⟨w', e⟩ := lookup_of_mem' h'
      have hb : (c == d) = false := by simpa using hcd
      exact ⟨w', by simp only [List.lookup, hb, e]⟩

/-- How a value of a sort of `D` is typed in a program that defines the sorts of `D`. -/
theorem has_type_adt (hO : O.Sound) {D : Sorts} {Q : Program} (hQ : SortsIn D Q) {s : Id}
    {tps : List Id} {ctors : List (Id × List Param)} (hs : D s = some (tps, ctors))
    (tenv : List TypeBinding) (vars : List Binding) (c : Id) (vtps : List Ty)
    (vs : List Value) (args : List Ty) :
    O.has_type Q (.Env tenv vars) (.ADTV c vtps vs) (.ADTType s args) = true ↔
      ∃ fs, ctors.lookup c = some fs ∧ vtps = O.resolve_all tenv args ∧
        O.params_have_types Q (.Env (bind_types tps args tenv) []) vs fs = true := by
  cases Q with
  | Program fns cs ss is eqs =>
  obtain ⟨hsort, hctor, hcompl⟩ := hQ s tps ctors hs
  rw [hO.has_type]
  cases hl : ctors.lookup c with
  | some fs =>
    have hc := hctor c fs (mem_of_lookup' hl)
    simp [hc, hsort]
    exact Iff.rfl
  | none =>
    cases hc : lookup_ctor cs c with
    | Ok k =>
      cases k with
      | Constructor c1 s2 fs =>
      by_cases hss : s = s2
      · subst hss
        obtain ⟨w, hw⟩ := lookup_of_mem' (hcompl c c1 fs hc)
        rw [hw] at hl
        cases hl
      · simp [hc, hsort, hss]
    | Stuck => simp [hc]
    | OutOfFuel => simp [hc]

/-- Values of types of `PureTy` are typed alike in two programs that define the sorts alike,
where the type parameters are bound alike, whatever the values of the variables. -/
theorem has_type_same (hO : O.Sound) {D : Sorts} {ok : Ty → Prop} {Ps P : Program}
    (hS : SortsIn D Ps) (hP : SortsIn D P) (hW : SortsWF D ok) :
    ∀ (sz : Nat) (v : Value), sizeOf v ≤ sz → ∀ (n : Nat) {B : List Id} {T : Ty}
      {tenv tenv' : List TypeBinding} (vars vars' : List Binding), PureTy D ok B T →
        Cond D ok n B tenv tenv' →
          O.has_type Ps (.Env tenv vars) v T = O.has_type P (.Env tenv' vars') v T := by
  intro sz
  induction sz using Nat.strongRecOn with
  | _ sz ihs =>
  intro v hv n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro B T tenv tenv' vars vars' hT
  induction hT generalizing tenv tenv' vars vars' with
  | int => intro _; rw [hO.has_type, hO.has_type]
  | bool => intro _; rw [hO.has_type, hO.has_type]
  | @tparam a h =>
    intro hC
    cases n with
    | zero => simp only [Cond] at hC; subst hC; simp at h
    | succ m =>
      obtain ⟨y, u, uenv, uenv', B', h1, h2, hu, _, hC'⟩ := hC a h
      rw [hO.has_type, hO.has_type]
      simp only [env_types]
      rw [h1, h2]
      exact ihn m (Nat.lt_succ_self m) [] [] hu hC'
  | @adt s args tps ctors hs hl ha hok iha =>
    intro hC
    cases v
    case ADTV c vtps vs =>
      have hres : O.resolve_all tenv args = O.resolve_all tenv' args := by
        have : ∀ ts : List Ty, (∀ t ∈ ts, PureTy D ok B t) →
            O.resolve_all tenv ts = O.resolve_all tenv' ts := by
          intro ts h
          induction ts with
          | nil => rw [hO.resolve_all, hO.resolve_all]
          | cons t ts ih =>
            rw [hO.resolve_all, hO.resolve_all (ts := t :: ts)]
            simp only [resolve_same hO n (h t (by simp)) hC,
              ih (fun t' ht' => h t' (by simp [ht']))]
        exact this args ha
      have hC2 := cond_bind (tenv := tenv) (tenv' := tenv') ha hok hl hC
      have hsz : ∀ w ∈ vs, sizeOf w < sz := by
        intro w hw
        have := List.sizeOf_lt_of_mem hw
        simp only [Value.ADTV.sizeOf_spec] at hv
        omega
      have hfields : ∀ fs, ctors.lookup c = some fs →
          O.params_have_types Ps (.Env (bind_types tps args tenv) []) vs fs =
            O.params_have_types P (.Env (bind_types tps args tenv') []) vs fs := by
        intro fs hlc
        have hfs : ∀ p ∈ fs, PureTy D ok tps (paramTy p) :=
          hW s tps ctors hs c fs (mem_of_lookup' hlc)
        generalize ([] : List Binding) = vars0
        clear hlc hv ihn iha
        induction vs generalizing fs vars0 with
        | nil =>
          cases fs <;> rw [hO.params_have_types, hO.params_have_types]
        | cons w rest ih =>
          cases fs with
          | nil => rw [hO.params_have_types, hO.params_have_types]
          | cons p fs =>
            cases p with
            | Param x t =>
            rw [hO.params_have_types, hO.params_have_types]
            simp only [env_bind]
            rw [ihs (sizeOf w) (hsz w (by simp)) w (Nat.le_refl _) (n + 1) vars0 vars0
                (by simpa [paramTy] using hfs (.Param x t) (by simp)) hC2,
              ih (fun w hw => hsz w (by simp [hw])) fs (fun p hp => hfs p (by simp [hp]))]
      rw [Bool.eq_iff_iff, has_type_adt hO hS hs, has_type_adt hO hP hs]
      constructor
      · rintro ⟨fs, h1, h2, h3⟩
        exact ⟨fs, h1, hres ▸ h2, (hfields fs h1) ▸ h3⟩
      · rintro ⟨fs, h1, h2, h3⟩
        exact ⟨fs, h1, hres ▸ h2, (hfields fs h1) ▸ h3⟩
    all_goals rw [hO.has_type, hO.has_type]
  | @refine x t p ht hp ih =>
    intro hC
    have e := fun fuel => eval_pure (O := O) (Q := Ps) (Q' := P) (v := v) hp fuel tenv tenv'
      vars vars'
    have hh : O.holds Ps (.Env tenv (.Binding x v :: vars)) p =
        O.holds P (.Env tenv' (.Binding x v :: vars')) p := by
      rw [Bool.eq_iff_iff, hO.holds, hO.holds]
      simp only [decide_eq_true_eq, e]
    rw [hO.has_type, hO.has_type]
    simp only [ih vars vars' hC, env_bind, hh]

end Inox.Typing
