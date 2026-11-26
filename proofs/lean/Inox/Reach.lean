/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Bridge

/-!
# The calls that evaluation goes through have values

`Total` of `Inox/NoSolution.lean` asks that every call of a function of the program give a value.
A solution only needs the calls that its evaluation goes through, and those give values: a call
that is stuck or that runs out of fuel makes the expression around it so. This module proves it
for the terms of the fragment, as a check on terms decides it.

`reaches K c t` decides that evaluating the expression of the term `t` goes through the call `c`,
in the models where the literals `K` have their values: `c` is `t`, or it is reached in an operand
that is evaluated. The operands of `ite`, `and`, `or` and `=>` after the first are only evaluated
when the first has the value that selects them, which `red K` has to give.

`called_of_reaches` is the theorem: where an expression has a value, each call that its term
reaches is a call of a function of the program to values of its parameters' types that gives a
value with some fuel (`Called`), in the models that agree with the calls and the variables.
`called_of_call` is the same of the body of a function whose call gives a value. With them, the
guard of an unfolding, which is a blocker of the path to its call, can imply that the call gives a
value, as `GuardOk` of `Inox/Relative.lean` asks: the check that relates the blockers to `reaches`
is not there yet.
-/

namespace Inox.Bridge

open Eo
open SmtEval
open Smtm
open Inox.Fresh
open Inox.Extend
open Inox.Model
open Inox.Semantics

/-- Evaluating the expression of the term `t` goes through the call `c`, in the models where the
literals `K` have their values: `c` is `t`, if `t` is not the function of an application (`top`),
or it is reached in an operand of `t` that is evaluated. An operand of `ite`, `and`, `or` or `=>`
after the first is evaluated when the first reduces under `K` to the value that selects it. A call
of a function without parameters is a constant, as a variable is, and is not counted. -/
def reaches (K : List (SmtTerm × Bool)) (c : SmtTerm) : Bool → SmtTerm → Bool
  | top, .Apply f a =>
    (top && decide (SmtTerm.Apply f a = c)) || reaches K c false f || reaches K c true a
  | _, .ite x a b =>
    reaches K c true x || (decide (red K x = .Boolean true) && reaches K c true a) ||
      (decide (red K x = .Boolean false) && reaches K c true b)
  | _, .and x y => reaches K c true x || (decide (red K x = .Boolean true) && reaches K c true y)
  | _, .or x y => reaches K c true x || (decide (red K x = .Boolean false) && reaches K c true y)
  | _, .imp x y => reaches K c true x || (decide (red K x = .Boolean true) && reaches K c true y)
  | _, .not x => reaches K c true x
  | _, .uneg x => reaches K c true x
  | _, .eq x y => reaches K c true x || reaches K c true y
  | _, .plus x y => reaches K c true x || reaches K c true y
  | _, .neg x y => reaches K c true x || reaches K c true y
  | _, .mult x y => reaches K c true x || reaches K c true y
  | _, .lt x y => reaches K c true x || reaches K c true y
  | _, .gt x y => reaches K c true x || reaches K c true y
  | _, .leq x y => reaches K c true x || reaches K c true y
  | _, .geq x y => reaches K c true x || reaches K c true y
  | _, _ => false

/-- A call reached in an application is the application, or is reached in its function or in one
of its arguments. -/
theorem reaches_spine {K : List (SmtTerm × Bool)} {c : SmtTerm} {top : Bool} :
    ∀ (us : List SmtTerm) (f : SmtTerm), reaches K c top (spine f us) = true →
      spine f us = c ∨ reaches K c (if us = [] then top else false) f = true ∨
        ∃ u ∈ us, reaches K c true u = true
  | [], _, h => Or.inr (Or.inl h)
  | a :: as, f, h => by
    rcases reaches_spine as (.Apply f a) h with h | h | ⟨u, hu, h⟩
    · exact Or.inl h
    · simp only [reaches, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with (⟨htop, heq⟩ | h) | h
      · by_cases has : as = []
        · subst has; exact Or.inl heq
        · simp [has] at htop
      · exact Or.inr (Or.inl (by simpa using h))
      · exact Or.inr (Or.inr ⟨a, .head _, h⟩)
    · exact Or.inr (Or.inr ⟨u, .tail _ hu, h⟩)

section Reach
variable (O : Oracle) (P : Program) (S : List Sig)

/-- The term `c` is a call of a function of `S` to terms whose values in `M` are those of values
of the types of its parameters, on which the call gives a value, with some fuel. -/
def Called (M : SmtModel) (c : SmtTerm) : Prop :=
  ∃ s ∈ S, ∃ us vs, c = spine (.UConst (nm s.name) s.toDef.ty) us ∧
    us.map (__smtx_model_eval M) = vs.map trV ∧
    List.Forall₂ HasV vs (s.params.map Prod.snd) ∧ ∃ n v, call O P n s.name [] [] vs = .Ok v

/-- What `called_of_reaches` says of `e`: where it has a value, the calls that its term reaches
give values. -/
def Reach (n : Int) (Γ : List (Id × Ty)) (e : Expr) : Prop :=
  ∀ env v, EnvTy Γ env → eval O P n env e = .Ok v →
    ∀ M, model_wf M → CallsOk O P S n M → VarsOk Γ env M → ∀ K, KSound M K →
      ∀ c, reaches K c true (tr S Γ e) = true → Called O P S M c

variable {O P S}

/-- A term that has the value of a Boolean reduces to no other. -/
theorem red_agrees (hty : LogosTyping) {M : SmtModel} (hw : model_wf M)
    {K : List (SmtTerm × Bool)} (hK : KSound M K) {t : SmtTerm} {b b' : Bool}
    (ht : __smtx_model_eval M t = trV (.BoolV b)) (hr : red K t = .Boolean b') : b = b' := by
  have h := eval_red hty hw hK t
  rw [hr, ht] at h
  simp only [__smtx_model_eval, trV, SmtValue.Boolean.injEq] at h
  exact h.symm

theorem reach_list {n : Int} {Γ : List (Id × Ty)} {env : Env} (hE : EnvTy Γ env) {M : SmtModel}
    (hw : model_wf M) (hc : CallsOk O P S n M) (hV : VarsOk Γ env M)
    {K : List (SmtTerm × Bool)} (hK : KSound M K) {c : SmtTerm} :
    ∀ (args : List Expr) (Ts : List Ty) (vs : List Value),
      (∀ p ∈ args.zip Ts, Reach O P S n Γ p.1) → args.length = Ts.length →
      eval_list O P n env args = .Ok vs →
      (∃ u ∈ args.map (tr S Γ), reaches K c true u = true) → Called O P S M c
  | [], _, _, _, _, _, ⟨_, hu, _⟩ => by simp at hu
  | _ :: _, [], _, _, hl, _, _ => by simp at hl
  | a :: args, T :: Ts, vs, ih, hl, h, ⟨u, hu, hr⟩ => by
    rw [eval_list] at h
    ok_split h
    rename_i v hv
    ok_split h
    rename_i ws hws
    simp only [List.map_cons, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ih (a, T) (.head _) env v hE hv M hw hc hV K hK c hr
    · exact reach_list hE hw hc hV hK args Ts ws (fun p hp => ih p (.tail _ hp))
        (by simpa using hl) hws ⟨u, hu, hr⟩

theorem reach_and (hO : O.Sound) (hty : LogosTyping) (hS : SigOk S) {n : Int}
    (hct : CallTy O P S n) {Γ : List (Id × Ty)} {env : Env} (hE : EnvTy Γ env) {M : SmtModel}
    (hw : model_wf M) (hc : CallsOk O P S n M) (hV : VarsOk Γ env M)
    {K : List (SmtTerm × Bool)} (hK : KSound M K) {c : SmtTerm} :
    ∀ (es : List Expr) (v : Value), (∀ e ∈ es, HasTy S Γ e .BooleanType) →
      (∀ e ∈ es, Reach O P S n Γ e) → eval_and O P n env es = .Ok v →
      reaches K c true (andT (es.map (tr S Γ))) = true → Called O P S M c
  | [], _, _, _, _, hr => by simp [andT, reaches] at hr
  | e :: es, v, hes, ih, h, hr => by
    rw [eval_and] at h
    ok_split h
    rename_i b hb
    simp only [List.map_cons, andT, reaches, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hr
    rcases hr with hr | ⟨hred, hr⟩
    · exact ih e (.head _) env _ hE (eval_bool_ok hb) M hw hc hV K hK c hr
    · have hb' := red_agrees hty hw hK
        ((ev hO hty hS hct (hes e (.head _)) env _ hE (eval_bool_ok hb)).2 M hw hc hV) hred
      subst hb'
      rw [dite_eq_left_of_eq_true (eq_true rfl)] at h
      exact reach_and hO hty hS hct hE hw hc hV hK es v (fun e' he' => hes e' (.tail _ he'))
        (fun e' he' => ih e' (.tail _ he')) h hr

theorem reach_or (hO : O.Sound) (hty : LogosTyping) (hS : SigOk S) {n : Int}
    (hct : CallTy O P S n) {Γ : List (Id × Ty)} {env : Env} (hE : EnvTy Γ env) {M : SmtModel}
    (hw : model_wf M) (hc : CallsOk O P S n M) (hV : VarsOk Γ env M)
    {K : List (SmtTerm × Bool)} (hK : KSound M K) {c : SmtTerm} :
    ∀ (es : List Expr) (v : Value), (∀ e ∈ es, HasTy S Γ e .BooleanType) →
      (∀ e ∈ es, Reach O P S n Γ e) → eval_or O P n env es = .Ok v →
      reaches K c true (orT (es.map (tr S Γ))) = true → Called O P S M c
  | [], _, _, _, _, hr => by simp [orT, reaches] at hr
  | e :: es, v, hes, ih, h, hr => by
    rw [eval_or] at h
    ok_split h
    rename_i b hb
    simp only [List.map_cons, orT, reaches, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hr
    rcases hr with hr | ⟨hred, hr⟩
    · exact ih e (.head _) env _ hE (eval_bool_ok hb) M hw hc hV K hK c hr
    · have hb' := red_agrees hty hw hK
        ((ev hO hty hS hct (hes e (.head _)) env _ hE (eval_bool_ok hb)).2 M hw hc hV) hred
      subst hb'
      rw [dite_eq_right_of_eq_false (eq_false Bool.false_ne_true)] at h
      exact reach_or hO hty hS hct hE hw hc hV hK es v (fun e' he' => hes e' (.tail _ he'))
        (fun e' he' => ih e' (.tail _ he')) h hr

/-- The calls that evaluation goes through have values: where an expression of the fragment has a
value, each call that its term reaches, under literals that have their values in a well-formed
model where the calls and the variables agree, is a call of a function of the program that gives
a value. -/
theorem called_of_reaches (hO : O.Sound) (hty : LogosTyping) (hS : SigOk S) (hP : ProgTy S P)
    {n : Int} (hct : CallTy O P S n) {Γ : List (Id × Ty)} {e : Expr} {T : Ty}
    (h : HasTy S Γ e T) : Reach O P S n Γ e := by
  induction h with
  | var hx hT =>
    intro env v hE he M hw hc hV K hK c hr
    simp [tr, hx, reaches] at hr
  | int i => intro env v hE he M hw hc hV K hK c hr; simp [tr, reaches] at hr
  | bool b => intro env v hE he M hw hc hV K hK c hr; simp [tr, reaches] at hr
  | ite htc _ _ ihc iha ihb =>
    intro env v hE he M hw hc hV K hK c hr
    rw [eval] at he
    ok_split he
    rename_i b hb
    have hcM := (ev hO hty hS hct htc env _ hE (eval_bool_ok hb)).2 M hw hc hV
    simp only [tr, reaches, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hr
    rcases hr with (hr | ⟨hred, hr⟩) | ⟨hred, hr⟩
    · exact ihc env _ hE (eval_bool_ok hb) M hw hc hV K hK c hr
    · have hb' := red_agrees hty hw hK hcM hred
      subst hb'
      rw [dite_eq_left_of_eq_true (eq_true rfl)] at he
      exact iha env v hE he M hw hc hV K hK c hr
    · have hb' := red_agrees hty hw hK hcM hred
      subst hb'
      rw [dite_eq_right_of_eq_false (eq_false Bool.false_ne_true)] at he
      exact ihb env v hE he M hw hc hV K hK c hr
  | @and es hes ih =>
    intro env v hE he M hw hc hV K hK c hr
    rw [eval] at he
    simp only [tr, trs_eq] at hr
    exact reach_and hO hty hS hct hE hw hc hV hK es v hes ih he hr
  | @or es hes ih =>
    intro env v hE he M hw hc hV K hK c hr
    rw [eval] at he
    simp only [tr, trs_eq] at hr
    exact reach_or hO hty hS hct hE hw hc hV hK es v hes ih he hr
  | not _ ih =>
    intro env v hE he M hw hc hV K hK c hr
    rw [eval] at he
    ok_split he
    rename_i b hb
    simp only [tr, reaches] at hr
    exact ih env _ hE (eval_bool_ok hb) M hw hc hV K hK c hr
  | @implies a b hta _ iha ihb =>
    intro env v hE he M hw hc hV K hK c hr
    rw [eval] at he
    ok_split he
    rename_i x hx
    have haM := (ev hO hty hS hct hta env _ hE (eval_bool_ok hx)).2 M hw hc hV
    simp only [tr, reaches, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hr
    rcases hr with hr | ⟨hred, hr⟩
    · exact iha env _ hE (eval_bool_ok hx) M hw hc hV K hK c hr
    · have hb' := red_agrees hty hw hK haM hred
      subst hb'
      rw [dite_eq_left_of_eq_true (eq_true rfl)] at he
      ok_split he
      rename_i y hy
      exact ihb env _ hE (eval_bool_ok hy) M hw hc hV K hK c hr
  | @equals a b T _ _ iha ihb =>
    intro env v hE he M hw hc hV K hK c hr
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    simp only [tr, reaches, Bool.or_eq_true] at hr
    rcases hr with hr | hr
    · exact iha env _ hE hx M hw hc hV K hK c hr
    · exact ihb env _ hE hy M hw hc hV K hK c hr
  | plus _ _ iha ihb | minus _ _ iha ihb | times _ _ iha ihb | lt _ _ iha ihb | gt _ _ iha ihb
    | le _ _ iha ihb | ge _ _ iha ihb =>
    intro env v hE he M hw hc hV K hK c hr
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    simp only [tr, reaches, Bool.or_eq_true] at hr
    rcases hr with hr | hr
    · exact iha env _ hE hx M hw hc hV K hK c hr
    · exact ihb env _ hE hy M hw hc hV K hK c hr
  | uminus _ ih =>
    intro env v hE he M hw hc hV K hK c hr
    rw [eval] at he
    ok_split he
    rename_i x hx
    simp only [tr, reaches] at hr
    exact ih env _ hE hx M hw hc hV K hK c hr
  | @invoke s args hs hl hargs ih =>
    intro env v hE he M hw hc hV K hK c hr
    rw [eval] at he
    ok_split he
    rename_i vs hvs
    have hmem := (findSig_spec hs).1
    have hlen : args.length = (s.params.map Prod.snd).length := by simpa using hl
    simp only [tr, hs, trs_eq] at hr
    rcases reaches_spine _ _ hr with hr | hr | hr
    · obtain ⟨hvsT, hvsM⟩ := ev_list hE args (s.params.map Prod.snd) vs hlen
        (fun p hp => ev hO hty hS hct (hargs p hp)) hvs
      rw [call_tenv hP hmem] at he
      exact ⟨s, hmem, _, vs, hr.symm, hvsM M hw hc hV, hvsT, n, v, he⟩
    · split at hr <;> simp [reaches] at hr
    · exact reach_list hE hw hc hV hK args _ vs ih hlen hvs hr
  | assume _ _ ihp ihb =>
    intro env v hE he M hw hc hV K hK c hr
    rw [eval] at he
    ok_split he
    rename_i b hb
    cases b
    · rw [dite_eq_right_of_eq_false (eq_false Bool.false_ne_true)] at he
      cases he
    · rw [dite_eq_left_of_eq_true (eq_true rfl)] at he
      simp only [tr] at hr
      exact ihb env v hE he M hw hc hV K hK c hr

/-- The calls that a call goes through have values: where a call of a function of `S` gives a
value, each call that the term of its body reaches is a call that gives a value, in the models
where the calls agree and the constants of the parameters have the values of the arguments. -/
theorem called_of_call (hO : O.Sound) (hty : LogosTyping) (hS : SigOk S) (hP : ProgTy S P)
    {s : Sig} {body : Expr} (hbody : HasBody P s body) (hbty : HasTy S s.params body s.ret)
    {vs : List Value} (hvs : List.Forall₂ HasV vs (s.params.map Prod.snd)) {n : Int} {v : Value}
    (hcall : call O P n s.name [] [] vs = .Ok v) {M : SmtModel} (hw : model_wf M)
    (hc : ∀ m, CallsOk O P S m M)
    (hV : ∀ bs, bind_all (s.params.map Prod.fst) vs = .Ok bs →
      VarsOk s.params (Env.Env (bind_types [] [] []) bs) M)
    {K : List (SmtTerm × Bool)} (hK : KSound M K) {c : SmtTerm}
    (hr : reaches K c true (tr S s.params body) = true) : Called O P S M c := by
  by_cases hn : n ≤ 0
  · rw [call, dite_eq_left_of_eq_true (eq_true hn)] at hcall; cases hcall
  rw [call, dite_eq_right_of_eq_false (eq_false hn)] at hcall
  cases P with
  | Program fs _ _ _ _ =>
  simp only [HasBody] at hbody
  dsimp only at hcall
  rw [hbody] at hcall
  dsimp only at hcall
  ok_split hcall
  rename_i bs hbs
  have hE : EnvTy s.params (Env.Env (bind_types [] [] []) bs) := by
    intro x T hx w hw'
    obtain ⟨u, hu, huT⟩ := bind_lookup s.params vs bs hbs hvs x T hx
    rw [lookup_var_det hw' hu]; exact huT
  exact called_of_reaches hO hty hS hP (call_ty' hO hty hS hP (n - 1)) hbty _ _ hE hcall M hw
    (hc (n - 1)) (hV bs hbs) K hK c hr

end Reach

end Inox.Bridge
