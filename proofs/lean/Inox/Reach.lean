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
when the first has the value that selects them, which `red K` has to give. It is `reachesW` with
the terms as they are: `reachesW w` sees the terms through `w`, a substitution of the arguments of
a call for the parameters of its function, so that the body of the function is compared with the
terms of the certificate, without the calls of the arguments.

`called_of_reaches` is the theorem: where an expression has a value, each call that its term
reaches is a call of a function of the program to values of its parameters' types that gives a
value with some fuel (`Called`), in the models that agree with the calls and the variables.
`called_of_call` is the same of the body of a function whose call gives a value. With them, the
guard of an unfolding, which holds only where a blocker of a path to its call does, implies that
the call gives a value: `Inox/Reached.lean` checks that the blockers are those of such paths.
-/

namespace Inox.Bridge

open Eo
open SmtEval
open Smtm
open Inox.Fresh
open Inox.Extend
open Inox.Model
open Inox.Semantics

/-- Whether `f`, applied to some arguments or to none, is a constant: the function of a call,
and not a constructor, a tester or a selector. -/
def isCall : SmtTerm → Bool
  | .Apply f _ => isCall f
  | .UConst _ _ => true
  | _ => false

/-- Evaluating the expression of the term `t` goes through the call `c`, in the models where the
literals `K` have their values, with the terms seen through `w`: `c` is `w t`, if `t` is not the
function of an application (`top`), or it is reached in an operand of `t` that is evaluated. An
operand of `ite`, `and`, `or` or `=>` after the first is evaluated when the first, through `w`,
reduces under `K` to the value that selects it. A call of a function without parameters is a
constant, as a variable is, and is not counted. With a substitution for `w`, `t` is the body of a
function and the terms are those of a call: the calls reached in the arguments are not counted,
since evaluating the body doesn't go through them. -/
def reachesW (w : SmtTerm → SmtTerm) (K : List (SmtTerm × Bool)) (c : SmtTerm) :
    Bool → SmtTerm → Bool
  | top, .Apply f a =>
    (top && isCall f && decide (w (SmtTerm.Apply f a) = c)) || reachesW w K c false f ||
      reachesW w K c true a
  | _, .ite x a b =>
    reachesW w K c true x || (decide (red K (w x) = .Boolean true) && reachesW w K c true a) ||
      (decide (red K (w x) = .Boolean false) && reachesW w K c true b)
  | _, .and x y =>
    reachesW w K c true x || (decide (red K (w x) = .Boolean true) && reachesW w K c true y)
  | _, .or x y =>
    reachesW w K c true x || (decide (red K (w x) = .Boolean false) && reachesW w K c true y)
  | _, .imp x y =>
    reachesW w K c true x || (decide (red K (w x) = .Boolean true) && reachesW w K c true y)
  | _, .not x => reachesW w K c true x
  | _, .uneg x => reachesW w K c true x
  | _, .eq x y => reachesW w K c true x || reachesW w K c true y
  | _, .plus x y => reachesW w K c true x || reachesW w K c true y
  | _, .neg x y => reachesW w K c true x || reachesW w K c true y
  | _, .mult x y => reachesW w K c true x || reachesW w K c true y
  | _, .div x y => reachesW w K c true x || reachesW w K c true y
  | _, .qdiv x y => reachesW w K c true x || reachesW w K c true y
  | _, .mod x y => reachesW w K c true x || reachesW w K c true y
  | _, .lt x y => reachesW w K c true x || reachesW w K c true y
  | _, .gt x y => reachesW w K c true x || reachesW w K c true y
  | _, .leq x y => reachesW w K c true x || reachesW w K c true y
  | _, .geq x y => reachesW w K c true x || reachesW w K c true y
  | _, .bvneg x => reachesW w K c true x
  | _, .bvnot x => reachesW w K c true x
  | _, .bvadd x y => reachesW w K c true x || reachesW w K c true y
  | _, .bvsub x y => reachesW w K c true x || reachesW w K c true y
  | _, .bvmul x y => reachesW w K c true x || reachesW w K c true y
  | _, .bvudiv x y => reachesW w K c true x || reachesW w K c true y
  | _, .bvurem x y => reachesW w K c true x || reachesW w K c true y
  | _, .bvult x y => reachesW w K c true x || reachesW w K c true y
  | _, .bvugt x y => reachesW w K c true x || reachesW w K c true y
  | _, .bvule x y => reachesW w K c true x || reachesW w K c true y
  | _, .bvuge x y => reachesW w K c true x || reachesW w K c true y
  | _, .bvsdiv x y => reachesW w K c true x || reachesW w K c true y
  | _, .bvsrem x y => reachesW w K c true x || reachesW w K c true y
  | _, .bvsmod x y => reachesW w K c true x || reachesW w K c true y
  | _, .bvslt x y => reachesW w K c true x || reachesW w K c true y
  | _, .bvsgt x y => reachesW w K c true x || reachesW w K c true y
  | _, .bvsle x y => reachesW w K c true x || reachesW w K c true y
  | _, .bvsge x y => reachesW w K c true x || reachesW w K c true y
  | _, _ => false

/-- `reachesW` with the terms as they are. -/
def reaches (K : List (SmtTerm × Bool)) (c : SmtTerm) (top : Bool) (t : SmtTerm) : Bool :=
  reachesW id K c top t

/-- A call reached in an application is the application, or is reached in its function or in one
of its arguments. -/
theorem reaches_spine {w : SmtTerm → SmtTerm} {K : List (SmtTerm × Bool)} {c : SmtTerm}
    {top : Bool} :
    ∀ (us : List SmtTerm) (f : SmtTerm), reachesW w K c top (spine f us) = true →
      (isCall f = true ∧ w (spine f us) = c) ∨
        reachesW w K c (if us = [] then top else false) f = true ∨
        ∃ u ∈ us, reachesW w K c true u = true
  | [], _, h => Or.inr (Or.inl h)
  | a :: as, f, h => by
    rcases reaches_spine as (.Apply f a) h with h | h | ⟨u, hu, h⟩
    · exact Or.inl ⟨by simpa [isCall] using h.1, h.2⟩
    · simp only [reachesW, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with (⟨⟨htop, hcall⟩, heq⟩ | h) | h
      · by_cases has : as = []
        · subst has; exact Or.inl ⟨hcall, heq⟩
        · simp [has] at htop
      · exact Or.inr (Or.inl (by simpa using h))
      · exact Or.inr (Or.inr ⟨a, .head _, h⟩)
    · exact Or.inr (Or.inr ⟨u, .tail _ hu, h⟩)

section Reach
variable (O : Oracle) (P : Program) (D : List Data) (S : List Sig)

/-- The term `c` is a call of a function of `S` to terms whose values in `M` are those of values
of the types of its parameters, on which the call gives a value, with some fuel. -/
def Called (M : SmtModel) (c : SmtTerm) : Prop :=
  ∃ s ∈ S, ∃ us vs, c = spine (.UConst (nm s.name) (s.toDef D).ty) us ∧
    us.map (__smtx_model_eval M) = vs.map (trV D) ∧
    List.Forall₂ (HasV D) vs (s.params.map Prod.snd) ∧ ∃ n v, call O P n s.name [] [] vs = .Ok v

/-- `Called`, of a call and its arguments seen through `w`. -/
def CalledW (M : SmtModel) (w : SmtTerm → SmtTerm) (c : SmtTerm) : Prop :=
  ∃ s ∈ S, ∃ us vs, c = w (spine (.UConst (nm s.name) (s.toDef D).ty) us) ∧
    us.map (fun u => __smtx_model_eval M (w u)) = vs.map (trV D) ∧
    List.Forall₂ (HasV D) vs (s.params.map Prod.snd) ∧ ∃ n v, call O P n s.name [] [] vs = .Ok v

/-- The terms of the expressions of `Γ` have through `w`, in `N`, the values that they have in
`M`. -/
def Through (Γ : List (Id × Ty)) (w : SmtTerm → SmtTerm) (N M : SmtModel) : Prop :=
  ∀ e T, HasTy D S Γ e T →
    __smtx_model_eval N (w (tr D S Γ e)) = __smtx_model_eval M (tr D S Γ e)

/-- What `called_of_reachesW` says of `e`: where it has a value, the calls that its term reaches
give values. -/
def Reach (n : Int) (Γ : List (Id × Ty)) (e : Expr) : Prop :=
  ∀ env v, EnvTy D Γ env → eval O P n env e = .Ok v →
    ∀ M, model_wf M → CallsOk O P D S n M → VarsOk D Γ env M →
      ∀ N w, model_wf N → Through D S Γ w N M → ∀ K, KSound N K →
        ∀ c, reachesW w K c true (tr D S Γ e) = true → CalledW O P D S N w c

variable {O P D S}

/-- A term that has the value of a Boolean reduces to no other. -/
theorem red_agrees (hty : LogosTyping) {M : SmtModel} (hw : model_wf M)
    {K : List (SmtTerm × Bool)} (hK : KSound M K) {t : SmtTerm} {b b' : Bool}
    (ht : __smtx_model_eval M t = trV D (.BoolV b)) (hr : red K t = .Boolean b') : b = b' := by
  have h := eval_red hty hw hK t
  rw [hr, ht] at h
  simp only [__smtx_model_eval, trV, SmtValue.Boolean.injEq] at h
  exact h.symm

/-- The terms of typed arguments have through `w` the values that they have in `M`. -/
theorem through_list {Γ : List (Id × Ty)} {w : SmtTerm → SmtTerm} {N M : SmtModel}
    (hT : Through D S Γ w N M) :
    ∀ (args : List Expr) (Ts : List Ty), args.length = Ts.length →
      (∀ p ∈ args.zip Ts, HasTy D S Γ p.1 p.2) →
      (args.map (tr D S Γ)).map (fun u => __smtx_model_eval N (w u)) =
        (args.map (tr D S Γ)).map (__smtx_model_eval M)
  | [], _, _, _ => rfl
  | _ :: _, [], hl, _ => by simp at hl
  | a :: args, T :: Ts, hl, h => by
    simp only [List.map_cons]
    rw [hT a T (h (a, T) (.head _)), through_list hT args Ts (by simpa using hl)
      (fun p hp => h p (.tail _ hp))]

section Lists
variable {n : Int} {Γ : List (Id × Ty)} {env : Env} (hE : EnvTy D Γ env) {M : SmtModel}
  (hw : model_wf M) (hc : CallsOk O P D S n M) (hV : VarsOk D Γ env M) {N : SmtModel}
  {w : SmtTerm → SmtTerm} (hN : model_wf N) (hT : Through D S Γ w N M)
  {K : List (SmtTerm × Bool)} (hK : KSound N K) {c : SmtTerm}
include hE hw hc hV hN hT hK

theorem reach_list :
    ∀ (args : List Expr) (Ts : List Ty) (vs : List Value),
      (∀ p ∈ args.zip Ts, Reach O P D S n Γ p.1) → args.length = Ts.length →
      eval_list O P n env args = .Ok vs →
      (∃ u ∈ args.map (tr D S Γ), reachesW w K c true u = true) → CalledW O P D S N w c
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
    · exact ih (a, T) (.head _) env v hE hv M hw hc hV N w hN hT K hK c hr
    · exact reach_list args Ts ws (fun p hp => ih p (.tail _ hp)) (by simpa using hl) hws
        ⟨u, hu, hr⟩

theorem reach_and (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hPD : ProgData D P)
    (hct : CallTy O P D S n) :
    ∀ (es : List Expr) (v : Value), (∀ e ∈ es, HasTy D S Γ e .BooleanType) →
      (∀ e ∈ es, Reach O P D S n Γ e) → eval_and O P n env es = .Ok v →
      reachesW w K c true (andT (es.map (tr D S Γ))) = true → CalledW O P D S N w c
  | [], _, _, _, _, hr => by simp [andT, reachesW] at hr
  | e :: es, v, hes, ih, h, hr => by
    rw [eval_and] at h
    ok_split h
    rename_i b hb
    simp only [List.map_cons, andT, reachesW, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hr
    rcases hr with hr | ⟨hred, hr⟩
    · exact ih e (.head _) env _ hE (eval_bool_ok hb) M hw hc hV N w hN hT K hK c hr
    · have hb' := red_agrees hty hN hK ((hT e _ (hes e (.head _))).trans
        ((ev hO hty hS hPD hct (hes e (.head _)) env _ hE (eval_bool_ok hb)).2 M hw hc hV)) hred
      subst hb'
      rw [dite_eq_left_of_eq_true (eq_true rfl)] at h
      exact reach_and hO hty hS hPD hct es v (fun e' he' => hes e' (.tail _ he'))
        (fun e' he' => ih e' (.tail _ he')) h hr

theorem reach_or (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hPD : ProgData D P)
    (hct : CallTy O P D S n) :
    ∀ (es : List Expr) (v : Value), (∀ e ∈ es, HasTy D S Γ e .BooleanType) →
      (∀ e ∈ es, Reach O P D S n Γ e) → eval_or O P n env es = .Ok v →
      reachesW w K c true (orT (es.map (tr D S Γ))) = true → CalledW O P D S N w c
  | [], _, _, _, _, hr => by simp [orT, reachesW] at hr
  | e :: es, v, hes, ih, h, hr => by
    rw [eval_or] at h
    ok_split h
    rename_i b hb
    simp only [List.map_cons, orT, reachesW, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hr
    rcases hr with hr | ⟨hred, hr⟩
    · exact ih e (.head _) env _ hE (eval_bool_ok hb) M hw hc hV N w hN hT K hK c hr
    · have hb' := red_agrees hty hN hK ((hT e _ (hes e (.head _))).trans
        ((ev hO hty hS hPD hct (hes e (.head _)) env _ hE (eval_bool_ok hb)).2 M hw hc hV)) hred
      subst hb'
      rw [dite_eq_right_of_eq_false (eq_false Bool.false_ne_true)] at h
      exact reach_or hO hty hS hPD hct es v (fun e' he' => hes e' (.tail _ he'))
        (fun e' he' => ih e' (.tail _ he')) h hr

end Lists

set_option maxHeartbeats 1600000 in
/-- The calls that evaluation goes through have values: where an expression of the fragment has a
value in the models where the calls and the variables agree, each call that its term reaches,
through `w` and under literals that have their values in a model where the terms have through `w`
the values of the first, is a call of a function of the program that gives a value. -/
theorem called_of_reachesW (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hP : ProgTy D S P)
    {n : Int} (hct : CallTy O P D S n) {Γ : List (Id × Ty)} {e : Expr} {T : Ty}
    (h : HasTy D S Γ e T) : Reach O P D S n Γ e := by
  have hPD := hP.data
  induction h with
  | var hx hT =>
    intro env v hE he M hw hc hV N w hN hT K hK c hr
    simp [tr, hx, reachesW] at hr
  | int i => intro env v hE he M hw hc hV N w hN hT K hK c hr; simp [tr, reachesW] at hr
  | bool b => intro env v hE he M hw hc hV N w hN hT K hK c hr; simp [tr, reachesW] at hr
  | ite htc _ _ ihc iha ihb =>
    intro env v hE he M hw hc hV N w hN hT K hK c hr
    rw [eval] at he
    ok_split he
    rename_i b hb
    have hcM := (hT _ _ htc).trans
      ((ev hO hty hS hPD hct htc env _ hE (eval_bool_ok hb)).2 M hw hc hV)
    simp only [tr, reachesW, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hr
    rcases hr with (hr | ⟨hred, hr⟩) | ⟨hred, hr⟩
    · exact ihc env _ hE (eval_bool_ok hb) M hw hc hV N w hN hT K hK c hr
    · have hb' := red_agrees hty hN hK hcM hred
      subst hb'
      rw [dite_eq_left_of_eq_true (eq_true rfl)] at he
      exact iha env v hE he M hw hc hV N w hN hT K hK c hr
    · have hb' := red_agrees hty hN hK hcM hred
      subst hb'
      rw [dite_eq_right_of_eq_false (eq_false Bool.false_ne_true)] at he
      exact ihb env v hE he M hw hc hV N w hN hT K hK c hr
  | @and es hes ih =>
    intro env v hE he M hw hc hV N w hN hT K hK c hr
    rw [eval] at he
    simp only [tr, trs_eq] at hr
    exact reach_and hE hw hc hV hN hT hK hO hty hS hPD hct es v hes ih he hr
  | @or es hes ih =>
    intro env v hE he M hw hc hV N w hN hT K hK c hr
    rw [eval] at he
    simp only [tr, trs_eq] at hr
    exact reach_or hE hw hc hV hN hT hK hO hty hS hPD hct es v hes ih he hr
  | not _ ih =>
    intro env v hE he M hw hc hV N w hN hT K hK c hr
    rw [eval] at he
    ok_split he
    rename_i b hb
    simp only [tr, reachesW] at hr
    exact ih env _ hE (eval_bool_ok hb) M hw hc hV N w hN hT K hK c hr
  | @implies a b hta _ iha ihb =>
    intro env v hE he M hw hc hV N w hN hT K hK c hr
    rw [eval] at he
    ok_split he
    rename_i x hx
    have haM := (hT _ _ hta).trans
      ((ev hO hty hS hPD hct hta env _ hE (eval_bool_ok hx)).2 M hw hc hV)
    simp only [tr, reachesW, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hr
    rcases hr with hr | ⟨hred, hr⟩
    · exact iha env _ hE (eval_bool_ok hx) M hw hc hV N w hN hT K hK c hr
    · have hb' := red_agrees hty hN hK haM hred
      subst hb'
      rw [dite_eq_left_of_eq_true (eq_true rfl)] at he
      ok_split he
      rename_i y hy
      exact ihb env _ hE (eval_bool_ok hy) M hw hc hV N w hN hT K hK c hr
  | @equals a b T _ _ iha ihb =>
    intro env v hE he M hw hc hV N w hN hT K hK c hr
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    simp only [tr, reachesW, Bool.or_eq_true] at hr
    rcases hr with hr | hr
    · exact iha env _ hE hx M hw hc hV N w hN hT K hK c hr
    · exact ihb env _ hE hy M hw hc hV N w hN hT K hK c hr
  | plus ha _ iha ihb | minus ha _ iha ihb | times ha _ iha ihb | lt ha _ iha ihb
    | gt ha _ iha ihb | div ha _ iha ihb | rem ha _ iha ihb | mod ha _ iha ihb
    | le ha _ iha ihb | ge ha _ iha ihb | bvPlus ha _ iha ihb | bvMinus ha _ iha ihb
    | bvTimes ha _ iha ihb | bvDiv ha _ iha ihb | bvRem ha _ iha ihb | bvLt ha _ iha ihb
    | bvGt ha _ iha ihb | bvLe ha _ iha ihb | bvGe ha _ iha ihb | rPlus ha _ iha ihb
    | rMinus ha _ iha ihb | rTimes ha _ iha ihb | rDiv ha _ iha ihb | rLt ha _ iha ihb
    | rGt ha _ iha ihb | rLe ha _ iha ihb | rGe ha _ iha ihb | bvMod ha _ iha ihb
    | sDiv ha _ iha ihb | sRem ha _ iha ihb | sMod ha _ iha ihb | sLt ha _ iha ihb
    | sGt ha _ iha ihb | sLe ha _ iha ihb | sGe ha _ iha ihb =>
    intro env v hE he M hw hc hV N w hN hT K hK c hr
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    simp only [tr, isBv_eq ha, isReal_eq ha, isSigned_eq ha, Ty.isBv, Ty.isReal, Ty.isSigned,
      Bool.false_eq_true, ↓reduceIte, reachesW, Bool.or_eq_true] at hr
    rcases hr with hr | hr
    · exact iha env _ hE hx M hw hc hV N w hN hT K hK c hr
    · exact ihb env _ hE hy M hw hc hV N w hN hT K hK c hr
  | bvLit _ _ _ => intro env v hE he M hw hc hV N w hN hT K hK c hr; simp [tr, reachesW] at hr
  | frac _ =>
    intro env v hE he M hw hc hV N w hN hT K hK c hr
    simp only [tr, reachesW, lit] at hr
    split at hr <;> split at hr <;> simp [reachesW] at hr
  | u2s _ ih | s2u _ ih =>
    intro env v hE he M hw hc hV N w hN hT K hK c hr
    rw [eval] at he
    ok_split he
    rename_i x hx
    simp only [tr] at hr
    exact ih env _ hE hx M hw hc hV N w hN hT K hK c hr
  | uminus ha ih | bvNeg ha ih | bvNot ha ih | rNeg ha ih =>
    intro env v hE he M hw hc hV N w hN hT K hK c hr
    rw [eval] at he
    ok_split he
    rename_i x hx
    simp only [tr, isBv_eq ha, Ty.isBv, Bool.false_eq_true, ↓reduceIte, reachesW] at hr
    exact ih env _ hE hx M hw hc hV N w hN hT K hK c hr
  | @invoke s args hs hl hargs ih =>
    intro env v hE he M hw hc hV N w hN hT K hK c hr
    rw [eval] at he
    ok_split he
    rename_i vs hvs
    have hmem := (findSig_spec hs).1
    have hlen : args.length = (s.params.map Prod.snd).length := by simpa using hl
    simp only [tr, hs, trs_eq] at hr
    rcases reaches_spine _ _ hr with hr | hr | hr
    · obtain ⟨hvsT, hvsM⟩ := ev_list hE args (s.params.map Prod.snd) vs hlen
        (fun p hp => ev hO hty hS hPD hct (hargs p hp)) hvs
      rw [call_tenv hP hmem] at he
      exact ⟨s, hmem, _, vs, hr.2.symm,
        (through_list hT args _ hlen hargs).trans (hvsM M hw hc hV), hvsT, n, v, he⟩
    · split at hr <;> simp [reachesW] at hr
    · exact reach_list hE hw hc hV hN hT hK args _ vs ih hlen hvs hr
  | assume _ _ ihp ihb =>
    intro env v hE he M hw hc hV N w hN hT K hK c hr
    rw [eval] at he
    ok_split he
    rename_i b hb
    cases b
    · rw [dite_eq_right_of_eq_false (eq_false Bool.false_ne_true)] at he
      cases he
    · rw [dite_eq_left_of_eq_true (eq_true rfl)] at he
      simp only [tr] at hr
      exact ihb env v hE he M hw hc hV N w hN hT K hK c hr
  | @adt k d i fs args hk hl hargs ih =>
    intro env v hE he M hw hc hV N w hN hT K hK c hr
    rw [eval] at he
    ok_split he
    rename_i vs hvs
    have hlen : args.length = (fs.map Prod.snd).length := by simpa using hl
    simp only [tr, hk, trs_eq] at hr
    rcases reaches_spine _ _ hr with hr | hr | hr
    · simp [isCall] at hr
    · split at hr <;> simp [reachesW] at hr
    · exact reach_list hE hw hc hV hN hT hK args _ vs ih hlen hvs hr
  | @isCons a k d i fs hk _ ih =>
    intro env v hE he M hw hc hV N w hN hT K hK c hr
    rw [eval] at he
    ok_split he
    rename_i x hx
    simp [tr, hk, reachesW, isCall] at hr
    exact ih env _ hE hx M hw hc hV N w hN hT K hK c hr
  | @sel a x d i j T hx _ ih =>
    intro env v hE he M hw hc hV N w hN hT K hK c hr
    rw [eval] at he
    ok_split he
    rename_i y hy
    simp [tr, hx, reachesW, isCall] at hr
    exact ih env _ hE hy M hw hc hV N w hN hT K hK c hr

/-- `called_of_reachesW` with the terms as they are: where an expression of the fragment has a
value, each call that its term reaches, under literals that have their values in a well-formed
model where the calls and the variables agree, is a call of a function of the program that gives
a value. -/
theorem called_of_reaches (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hP : ProgTy D S P)
    {n : Int} (hct : CallTy O P D S n) {Γ : List (Id × Ty)} {e : Expr} {T : Ty}
    (h : HasTy D S Γ e T) {env : Env} {v : Value} (hE : EnvTy D Γ env)
    (he : eval O P n env e = .Ok v) {M : SmtModel} (hw : model_wf M) (hc : CallsOk O P D S n M)
    (hV : VarsOk D Γ env M) {K : List (SmtTerm × Bool)} (hK : KSound M K) {c : SmtTerm}
    (hr : reaches K c true (tr D S Γ e) = true) : Called O P D S M c :=
  called_of_reachesW hO hty hS hP hct h env v hE he M hw hc hV M id hw (fun _ _ _ => rfl) K hK c
    hr

/-- The calls that a call goes through have values: where a call of a function of `S` gives a
value, each call that the term of its body reaches, through `w`, is a call that gives a value.
The body is evaluated in a model `M` where the calls agree and the constants of the parameters
have the values of the arguments, and the literals have their values in a model where the terms
have through `w` the values that they have in `M`. -/
theorem called_of_call (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hP : ProgTy D S P)
    {s : Sig} {body : Expr} (hbody : HasBody P s body) (hbty : HasTy D S s.params body s.ret)
    {vs : List Value} (hvs : List.Forall₂ (HasV D) vs (s.params.map Prod.snd)) {n : Int} {v : Value}
    (hcall : call O P n s.name [] [] vs = .Ok v) {M : SmtModel} (hw : model_wf M)
    (hc : ∀ m, CallsOk O P D S m M)
    (hV : ∀ bs, bind_all (s.params.map Prod.fst) vs = .Ok bs →
      VarsOk D s.params (Env.Env (bind_types [] [] []) bs) M)
    {N : SmtModel} {w : SmtTerm → SmtTerm} (hN : model_wf N) (hT : Through D S s.params w N M)
    {K : List (SmtTerm × Bool)} (hK : KSound N K) {c : SmtTerm}
    (hr : reachesW w K c true (tr D S s.params body) = true) : CalledW O P D S N w c := by
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
  have hE : EnvTy D s.params (Env.Env (bind_types [] [] []) bs) := by
    intro x T hx w hw'
    obtain ⟨u, hu, huT⟩ := bind_lookup s.params vs bs hbs hvs x T hx
    rw [lookup_var_det hw' hu]; exact huT
  exact called_of_reachesW hO hty hS hP (call_ty' hO hty hS hP (n - 1)) hbty _ _ hE hcall M hw
    (hc (n - 1)) (hV bs hbs) N w hN hT K hK c hr

end Reach

/-! ## The assumptions that evaluation goes through hold -/

mutual
/-- Evaluating `e` goes through an operation that is only defined where `φ` holds, in the models
where the literals `K` have their values: an `Assume` whose term, through `w`, is `φ`, or a
division whose divisor `d`, through `w`, makes `φ` be `(not (= d 0))`, in an operand that is
evaluated, as for `reachesW`. -/
def assumesW (D : List Data) (S : List Sig) (Γ : List (Id × Ty)) (w : SmtTerm → SmtTerm)
    (K : List (SmtTerm × Bool)) (φ : SmtTerm) : Expr → Bool
  | .Assume p b =>
    decide (w (tr D S Γ p) = φ) || assumesW D S Γ w K φ p || assumesW D S Γ w K φ b
  | .IfExpr c a b =>
    assumesW D S Γ w K φ c ||
      (decide (red K (w (tr D S Γ c)) = .Boolean true) && assumesW D S Γ w K φ a) ||
      (decide (red K (w (tr D S Γ c)) = .Boolean false) && assumesW D S Γ w K φ b)
  | .And es => assumesAnd D S Γ w K φ es
  | .Or es => assumesOr D S Γ w K φ es
  | .Not a | .UMinus a | .BVNot a | .BVUnsignedToSigned a | .BVSignedToUnsigned a =>
    assumesW D S Γ w K φ a
  | .Implies a b =>
    assumesW D S Γ w K φ a ||
      (decide (red K (w (tr D S Γ a)) = .Boolean true) && assumesW D S Γ w K φ b)
  | .Equals a b | .Plus a b | .Minus a b | .Times a b | .LessThan a b | .GreaterThan a b
  | .LessEquals a b | .GreaterEquals a b => assumesW D S Γ w K φ a || assumesW D S Γ w K φ b
  | .Division a b | .Remainder a b | .Modulo a b =>
    (!isBv D S Γ a && !isReal D S Γ a &&
        decide (SmtTerm.not (.eq (w (tr D S Γ b)) (.Numeral 0)) = φ)) ||
      (isReal D S Γ a &&
        decide (SmtTerm.not (.eq (w (tr D S Γ b)) (.qdiv (.Numeral 0) (.Numeral 1))) = φ)) ||
      assumesW D S Γ w K φ a || assumesW D S Γ w K φ b
  | .FunctionInvocation _ _ args | .ADT _ _ args => assumesAny D S Γ w K φ args
  | .IsConstructor a _ | .ADTSelector a _ => assumesW D S Γ w K φ a
  | _ => false

def assumesAnd (D : List Data) (S : List Sig) (Γ : List (Id × Ty)) (w : SmtTerm → SmtTerm)
    (K : List (SmtTerm × Bool)) (φ : SmtTerm) : List Expr → Bool
  | [] => false
  | e :: es =>
    assumesW D S Γ w K φ e ||
      (decide (red K (w (tr D S Γ e)) = .Boolean true) && assumesAnd D S Γ w K φ es)

def assumesOr (D : List Data) (S : List Sig) (Γ : List (Id × Ty)) (w : SmtTerm → SmtTerm)
    (K : List (SmtTerm × Bool)) (φ : SmtTerm) : List Expr → Bool
  | [] => false
  | e :: es =>
    assumesW D S Γ w K φ e ||
      (decide (red K (w (tr D S Γ e)) = .Boolean false) && assumesOr D S Γ w K φ es)

def assumesAny (D : List Data) (S : List Sig) (Γ : List (Id × Ty)) (w : SmtTerm → SmtTerm)
    (K : List (SmtTerm × Bool)) (φ : SmtTerm) : List Expr → Bool
  | [] => false
  | e :: es => assumesW D S Γ w K φ e || assumesAny D S Γ w K φ es
end

section Assumed
variable (O : Oracle) (P : Program) (D : List Data) (S : List Sig)

/-- What `holds_of_assumesW` says of `e`: where it has a value, the assumptions that its
evaluation goes through hold. -/
def Assumed (n : Int) (Γ : List (Id × Ty)) (e : Expr) : Prop :=
  ∀ env v, EnvTy D Γ env → eval O P n env e = .Ok v →
    ∀ M, model_wf M → CallsOk O P D S n M → VarsOk D Γ env M →
      ∀ N w, model_wf N → Through D S Γ w N M → ∀ K, KSound N K →
        ∀ φ, assumesW D S Γ w K φ e = true → __smtx_model_eval N φ = SmtValue.Boolean true

variable {O P D S}

section Lists
variable {n : Int} {Γ : List (Id × Ty)} {env : Env} (hE : EnvTy D Γ env) {M : SmtModel}
  (hw : model_wf M) (hc : CallsOk O P D S n M) (hV : VarsOk D Γ env M) {N : SmtModel}
  {w : SmtTerm → SmtTerm} (hN : model_wf N) (hT : Through D S Γ w N M)
  {K : List (SmtTerm × Bool)} (hK : KSound N K) {φ : SmtTerm}
include hE hw hc hV hN hT hK

theorem assumed_list :
    ∀ (args : List Expr) (Ts : List Ty) (vs : List Value),
      (∀ p ∈ args.zip Ts, Assumed O P D S n Γ p.1) → args.length = Ts.length →
      eval_list O P n env args = .Ok vs → assumesAny D S Γ w K φ args = true →
      __smtx_model_eval N φ = SmtValue.Boolean true
  | [], _, _, _, _, _, hr => by simp [assumesAny] at hr
  | _ :: _, [], _, _, hl, _, _ => by simp at hl
  | a :: args, T :: Ts, vs, ih, hl, h, hr => by
    rw [eval_list] at h
    ok_split h
    rename_i v hv
    ok_split h
    rename_i ws hws
    simp only [assumesAny, Bool.or_eq_true] at hr
    rcases hr with hr | hr
    · exact ih (a, T) (.head _) env v hE hv M hw hc hV N w hN hT K hK φ hr
    · exact assumed_list args Ts ws (fun p hp => ih p (.tail _ hp)) (by simpa using hl) hws hr

theorem assumed_and (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hPD : ProgData D P)
    (hct : CallTy O P D S n) :
    ∀ (es : List Expr) (v : Value), (∀ e ∈ es, HasTy D S Γ e .BooleanType) →
      (∀ e ∈ es, Assumed O P D S n Γ e) → eval_and O P n env es = .Ok v →
      assumesAnd D S Γ w K φ es = true → __smtx_model_eval N φ = SmtValue.Boolean true
  | [], _, _, _, _, hr => by simp [assumesAnd] at hr
  | e :: es, v, hes, ih, h, hr => by
    rw [eval_and] at h
    ok_split h
    rename_i b hb
    simp only [assumesAnd, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hr
    rcases hr with hr | ⟨hred, hr⟩
    · exact ih e (.head _) env _ hE (eval_bool_ok hb) M hw hc hV N w hN hT K hK φ hr
    · have hb' := red_agrees hty hN hK ((hT e _ (hes e (.head _))).trans
        ((ev hO hty hS hPD hct (hes e (.head _)) env _ hE (eval_bool_ok hb)).2 M hw hc hV)) hred
      subst hb'
      rw [dite_eq_left_of_eq_true (eq_true rfl)] at h
      exact assumed_and hO hty hS hPD hct es v (fun e' he' => hes e' (.tail _ he'))
        (fun e' he' => ih e' (.tail _ he')) h hr

theorem assumed_or (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hPD : ProgData D P)
    (hct : CallTy O P D S n) :
    ∀ (es : List Expr) (v : Value), (∀ e ∈ es, HasTy D S Γ e .BooleanType) →
      (∀ e ∈ es, Assumed O P D S n Γ e) → eval_or O P n env es = .Ok v →
      assumesOr D S Γ w K φ es = true → __smtx_model_eval N φ = SmtValue.Boolean true
  | [], _, _, _, _, hr => by simp [assumesOr] at hr
  | e :: es, v, hes, ih, h, hr => by
    rw [eval_or] at h
    ok_split h
    rename_i b hb
    simp only [assumesOr, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hr
    rcases hr with hr | ⟨hred, hr⟩
    · exact ih e (.head _) env _ hE (eval_bool_ok hb) M hw hc hV N w hN hT K hK φ hr
    · have hb' := red_agrees hty hN hK ((hT e _ (hes e (.head _))).trans
        ((ev hO hty hS hPD hct (hes e (.head _)) env _ hE (eval_bool_ok hb)).2 M hw hc hV)) hred
      subst hb'
      rw [dite_eq_right_of_eq_false (eq_false Bool.false_ne_true)] at h
      exact assumed_or hO hty hS hPD hct es v (fun e' he' => hes e' (.tail _ he'))
        (fun e' he' => ih e' (.tail _ he')) h hr

end Lists

set_option maxHeartbeats 1600000 in
/-- The assumptions that evaluation goes through hold: where an expression of the fragment has a
value in the models where the calls and the variables agree, the term of each assumption that its
evaluation goes through, through `w` and under literals that have their values in a model where
the terms have through `w` the values of the first, is true there. An assumption that fails makes
the expression stuck. -/
theorem holds_of_assumesW (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S)
    (hPD : ProgData D P) {n : Int}
    (hct : CallTy O P D S n) {Γ : List (Id × Ty)} {e : Expr} {T : Ty} (h : HasTy D S Γ e T) :
    Assumed O P D S n Γ e := by
  induction h with
  | var hx hT =>
    intro env v hE he M hw hc hV N w hN hT K hK φ hr
    simp [assumesW] at hr
  | int i => intro env v hE he M hw hc hV N w hN hT K hK φ hr; simp [assumesW] at hr
  | bool b => intro env v hE he M hw hc hV N w hN hT K hK φ hr; simp [assumesW] at hr
  | ite htc _ _ ihc iha ihb =>
    intro env v hE he M hw hc hV N w hN hT K hK φ hr
    rw [eval] at he
    ok_split he
    rename_i b hb
    have hcM := (hT _ _ htc).trans
      ((ev hO hty hS hPD hct htc env _ hE (eval_bool_ok hb)).2 M hw hc hV)
    simp only [assumesW, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hr
    rcases hr with (hr | ⟨hred, hr⟩) | ⟨hred, hr⟩
    · exact ihc env _ hE (eval_bool_ok hb) M hw hc hV N w hN hT K hK φ hr
    · have hb' := red_agrees hty hN hK hcM hred
      subst hb'
      rw [dite_eq_left_of_eq_true (eq_true rfl)] at he
      exact iha env v hE he M hw hc hV N w hN hT K hK φ hr
    · have hb' := red_agrees hty hN hK hcM hred
      subst hb'
      rw [dite_eq_right_of_eq_false (eq_false Bool.false_ne_true)] at he
      exact ihb env v hE he M hw hc hV N w hN hT K hK φ hr
  | @and es hes ih =>
    intro env v hE he M hw hc hV N w hN hT K hK φ hr
    rw [eval] at he
    simp only [assumesW] at hr
    exact assumed_and hE hw hc hV hN hT hK hO hty hS hPD hct es v hes ih he hr
  | @or es hes ih =>
    intro env v hE he M hw hc hV N w hN hT K hK φ hr
    rw [eval] at he
    simp only [assumesW] at hr
    exact assumed_or hE hw hc hV hN hT hK hO hty hS hPD hct es v hes ih he hr
  | not _ ih =>
    intro env v hE he M hw hc hV N w hN hT K hK φ hr
    rw [eval] at he
    ok_split he
    rename_i b hb
    simp only [assumesW] at hr
    exact ih env _ hE (eval_bool_ok hb) M hw hc hV N w hN hT K hK φ hr
  | @implies a b hta _ iha ihb =>
    intro env v hE he M hw hc hV N w hN hT K hK φ hr
    rw [eval] at he
    ok_split he
    rename_i x hx
    have haM := (hT _ _ hta).trans
      ((ev hO hty hS hPD hct hta env _ hE (eval_bool_ok hx)).2 M hw hc hV)
    simp only [assumesW, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hr
    rcases hr with hr | ⟨hred, hr⟩
    · exact iha env _ hE (eval_bool_ok hx) M hw hc hV N w hN hT K hK φ hr
    · have hb' := red_agrees hty hN hK haM hred
      subst hb'
      rw [dite_eq_left_of_eq_true (eq_true rfl)] at he
      ok_split he
      rename_i y hy
      exact ihb env _ hE (eval_bool_ok hy) M hw hc hV N w hN hT K hK φ hr
  | @equals a b T _ _ iha ihb =>
    intro env v hE he M hw hc hV N w hN hT K hK φ hr
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    simp only [assumesW, Bool.or_eq_true] at hr
    rcases hr with hr | hr
    · exact iha env _ hE hx M hw hc hV N w hN hT K hK φ hr
    · exact ihb env _ hE hy M hw hc hV N w hN hT K hK φ hr
  | plus _ _ iha ihb | minus _ _ iha ihb | times _ _ iha ihb | lt _ _ iha ihb | gt _ _ iha ihb
    | le _ _ iha ihb | ge _ _ iha ihb | bvPlus _ _ iha ihb | bvMinus _ _ iha ihb
    | bvTimes _ _ iha ihb | bvLt _ _ iha ihb | bvGt _ _ iha ihb | bvLe _ _ iha ihb
    | bvGe _ _ iha ihb | rPlus _ _ iha ihb | rMinus _ _ iha ihb | rTimes _ _ iha ihb
    | rLt _ _ iha ihb | rGt _ _ iha ihb | rLe _ _ iha ihb | rGe _ _ iha ihb | sLt _ _ iha ihb
    | sGt _ _ iha ihb | sLe _ _ iha ihb | sGe _ _ iha ihb =>
    intro env v hE he M hw hc hV N w hN hT K hK φ hr
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    simp only [assumesW, Bool.or_eq_true] at hr
    rcases hr with hr | hr
    · exact iha env _ hE hx M hw hc hV N w hN hT K hK φ hr
    · exact ihb env _ hE hy M hw hc hV N w hN hT K hK φ hr
  | bvDiv ha _ iha ihb | bvRem ha _ iha ihb | bvMod ha _ iha ihb | sDiv ha _ iha ihb
    | sRem ha _ iha ihb | sMod ha _ iha ihb =>
    intro env v hE he M hw hc hV N w hN hT K hK φ hr
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    simp only [assumesW, isBv_eq ha, isReal_eq ha, Ty.isBv, Ty.isReal, Bool.not_true,
      Bool.false_and, Bool.false_or, Bool.or_eq_true] at hr
    rcases hr with hr | hr
    · exact iha env _ hE hx M hw hc hV N w hN hT K hK φ hr
    · exact ihb env _ hE hy M hw hc hV N w hN hT K hK φ hr
  | @div a b hta htb iha ihb | @rem a b hta htb iha ihb | @mod a b hta htb iha ihb =>
    intro env v hE he M hw hc hV N w hN hT K hK φ hr
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    simp only [assumesW, isBv_eq hta, isReal_eq hta, Ty.isBv, Ty.isReal, Bool.not_false,
      Bool.true_and, Bool.false_and, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq] at hr
    rcases hr with (hr | hr) | hr
    · obtain ⟨hyT, hbM⟩ := ev hO hty hS hPD hct htb env _ hE hy
      obtain ⟨j, rfl⟩ := hasV_int hyT
      have hj : j ≠ 0 := by
        rintro rfl
        cases x <;> simp [arith_div, arith_rem, arith_mod] at he
      rw [← hr]
      simp [__smtx_model_eval, (hT _ _ htb).trans (hbM M hw hc hV), trV, __smtx_model_eval_eq,
        native_veq, hj, __smtx_model_eval_not, native_not]
    · exact iha env _ hE hx M hw hc hV N w hN hT K hK φ hr
    · exact ihb env _ hE hy M hw hc hV N w hN hT K hK φ hr
  | @rDiv a b hta htb iha ihb =>
    intro env v hE he M hw hc hV N w hN hT K hK φ hr
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    simp only [assumesW, isBv_eq hta, isReal_eq hta, Ty.isBv, Ty.isReal, Bool.not_false,
      Bool.not_true, Bool.true_and, Bool.false_and, Bool.and_false, Bool.false_or,
      Bool.or_eq_true, decide_eq_true_eq] at hr
    rcases hr with (hr | hr) | hr
    · obtain ⟨hyT, hbM⟩ := ev hO hty hS hPD hct htb env _ hE hy
      obtain ⟨q, rfl⟩ := hasV_real hyT
      obtain ⟨p, rfl⟩ := hasV_real (ev hO hty hS hPD hct hta env _ hE hx).1
      have hq : q.num ≠ 0 := by
        intro h0
        simp [arith_div, h0] at he
      have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast Rat.num_ne_zero.mp hq
      rw [← hr]
      simp [__smtx_model_eval, (hT _ _ htb).trans (hbM M hw hc hV), trV, ratOf_num_den,
        __smtx_model_eval_eq, native_veq, __smtx_model_eval_not, native_not,
        __smtx_to_real_coerce, __smtx_model_eval_ite, __smtx_model_eval_qdiv_total,
        native_mk_real, native_rdiv_total, native_rat_to_real, native_int_to_real, hq']
    · exact iha env _ hE hx M hw hc hV N w hN hT K hK φ hr
    · exact ihb env _ hE hy M hw hc hV N w hN hT K hK φ hr
  | bvLit _ _ _ => intro env v hE he M hw hc hV N w hN hT K hK φ hr; simp [assumesW] at hr
  | frac _ => intro env v hE he M hw hc hV N w hN hT K hK φ hr; simp [assumesW] at hr
  | uminus _ ih | bvNeg _ ih | bvNot _ ih | rNeg _ ih | u2s _ ih | s2u _ ih =>
    intro env v hE he M hw hc hV N w hN hT K hK φ hr
    rw [eval] at he
    ok_split he
    rename_i x hx
    simp only [assumesW] at hr
    exact ih env _ hE hx M hw hc hV N w hN hT K hK φ hr
  | @invoke s args hs hl hargs ih =>
    intro env v hE he M hw hc hV N w hN hT K hK φ hr
    rw [eval] at he
    ok_split he
    rename_i vs hvs
    have hlen : args.length = (s.params.map Prod.snd).length := by simpa using hl
    simp only [assumesW] at hr
    exact assumed_list hE hw hc hV hN hT hK args _ vs ih hlen hvs hr
  | @assume p b T htp _ ihp ihb =>
    intro env v hE he M hw hc hV N w hN hT K hK φ hr
    rw [eval] at he
    ok_split he
    rename_i x hx
    cases x
    · rw [dite_eq_right_of_eq_false (eq_false Bool.false_ne_true)] at he
      cases he
    · rw [dite_eq_left_of_eq_true (eq_true rfl)] at he
      simp only [assumesW, Bool.or_eq_true, decide_eq_true_eq] at hr
      rcases hr with (hr | hr) | hr
      · rw [← hr]
        exact (hT _ _ htp).trans
          ((ev hO hty hS hPD hct htp env _ hE (eval_bool_ok hx)).2 M hw hc hV)
      · exact ihp env _ hE (eval_bool_ok hx) M hw hc hV N w hN hT K hK φ hr
      · exact ihb env v hE he M hw hc hV N w hN hT K hK φ hr
  | @adt k d i fs args hk hl hargs ih =>
    intro env v hE he M hw hc hV N w hN hT K hK φ hr
    rw [eval] at he
    ok_split he
    rename_i vs hvs
    have hlen : args.length = (fs.map Prod.snd).length := by simpa using hl
    simp only [assumesW] at hr
    exact assumed_list hE hw hc hV hN hT hK args _ vs ih hlen hvs hr
  | isCons _ _ ih | sel _ _ ih =>
    intro env v hE he M hw hc hV N w hN hT K hK φ hr
    rw [eval] at he
    ok_split he
    rename_i x hx
    simp only [assumesW] at hr
    exact ih env _ hE hx M hw hc hV N w hN hT K hK φ hr

/-- The assumptions that a call goes through hold: where a call of a function of `S` gives a
value, the term of each assumption that the evaluation of its body goes through, through `w`, is
true, with the models of `called_of_call`. -/
theorem assumed_of_call (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hP : ProgTy D S P)
    {s : Sig} {body : Expr} (hbody : HasBody P s body) (hbty : HasTy D S s.params body s.ret)
    {vs : List Value} (hvs : List.Forall₂ (HasV D) vs (s.params.map Prod.snd)) {n : Int} {v : Value}
    (hcall : call O P n s.name [] [] vs = .Ok v) {M : SmtModel} (hw : model_wf M)
    (hc : ∀ m, CallsOk O P D S m M)
    (hV : ∀ bs, bind_all (s.params.map Prod.fst) vs = .Ok bs →
      VarsOk D s.params (Env.Env (bind_types [] [] []) bs) M)
    {N : SmtModel} {w : SmtTerm → SmtTerm} (hN : model_wf N) (hT : Through D S s.params w N M)
    {K : List (SmtTerm × Bool)} (hK : KSound N K) {φ : SmtTerm}
    (hr : assumesW D S s.params w K φ body = true) :
    __smtx_model_eval N φ = SmtValue.Boolean true := by
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
  have hE : EnvTy D s.params (Env.Env (bind_types [] [] []) bs) := by
    intro x T hx w hw'
    obtain ⟨u, hu, huT⟩ := bind_lookup s.params vs bs hbs hvs x T hx
    rw [lookup_var_det hw' hu]; exact huT
  exact holds_of_assumesW hO hty hS hP.2 (call_ty' hO hty hS hP (n - 1)) hbty _ _ hE hcall M hw
    (hc (n - 1)) (hV bs hbs) N w hN hT K hK φ hr

end Assumed

end Inox.Bridge
