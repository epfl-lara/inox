/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Instances

/-!
# The defining equations where the calls have values

`Good eqs M` asks that `M` satisfy each defining equation for all the values of its parameters.
The model that a solution of the query gives, where a function symbol is interpreted by evaluation
(see "The bridge to the semantics" in the README), satisfies the equation of a function only on the
arguments where its evaluation has a value: elsewhere, the call is stuck or doesn't terminate, and
the symbol's interpretation is arbitrary.

`GoodOn ok eqs M` asks the equations only on the arguments that `ok` accepts, and that the
equations evaluate to Booleans everywhere. The unfolding of an equation `(=> g s)` then holds in
the models of `GoodOn ok eqs` that satisfy the clauses before it, when its guard `g` implies that
`ok` accepts the arguments of its instance (`GuardOk`): this is what the blockers give, since a
blocker holds iff evaluation reaches the path it guards, and a call reached on the way to a
solution has a value. `no_good_model_of_unfold_on` is `no_good_model_of_unfold` restated with
`GoodOn`, the guards of the unfoldings being the new side condition.

Only the unfoldings are relativized. The clauses of instances and the facts that
`no_good_model_of_instances` verifies directly use the equations at their arguments without a
guard, so against `GoodOn` they stay hypotheses: on the regression corpus, 24 of the 1,176 facts
that `no_good_model_of_instances` covers are unfoldings.
-/

namespace Inox

open Logos (Sexp)
open Eo
open SmtEval
open Smtm
open Inox.Fresh
open Inox.Extend

/-- `M` satisfies each of the defining equations `eqs` for the values of its parameters that `ok`
accepts, and each evaluates to a Boolean for all of them. -/
def GoodOn (ok : Equation → List SmtValue → Prop) (eqs : List Equation) (M : SmtModel) : Prop :=
  ∀ e ∈ eqs, ∀ vs, List.Forall₂ (Typed M) e.params vs →
    (∃ b, __smtx_model_eval (setConsts M (bindValues e.params vs)) (__eo_to_smt e.term) =
      SmtValue.Boolean b) ∧
    (ok e vs → __smtx_model_eval (setConsts M (bindValues e.params vs)) (__eo_to_smt e.term) =
      SmtValue.Boolean true)

theorem goodOn_of_good {ok : Equation → List SmtValue → Prop} {eqs : List Equation}
    {M : SmtModel} (h : Good eqs M) : GoodOn ok eqs M :=
  fun e he vs hvs => ⟨⟨true, h e he vs hvs⟩, fun _ => h e he vs hvs⟩

/-- `Good` is `GoodOn` the predicate that accepts every argument. -/
theorem good_iff_goodOn {eqs : List Equation} {M : SmtModel} :
    Good eqs M ↔ GoodOn (fun _ _ => True) eqs M :=
  ⟨goodOn_of_good, fun h e he vs hvs => (h e he vs hvs).2 trivial⟩

/-- Reinterpreting a constant that `keepsB` accepts keeps the models of `GoodOn`. -/
theorem keepsOn_of_keepsB {ok : Equation → List SmtValue → Prop} {eqs : List Equation}
    {s : native_String} {T : SmtType} (h : keepsB eqs s T = true) : Keeps (GoodOn ok eqs) s T := by
  simp only [keepsB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
    Bool.and_eq_true] at h
  obtain ⟨hs, he⟩ := h
  intro M v hM e hmem vs hvs
  obtain ⟨hm, hp⟩ := he e hmem
  rw [setConsts_setConst (bindingOf_bindValues (by simpa using hp) vs),
    eval_setConst hs _ v _ (by simpa using hm)]
  exact hM e hmem vs hvs

theorem keepsConstOn_of_keeps {ok : Equation → List SmtValue → Prop} {r : TermSteps}
    (h : r.keeps = true) : ∀ st ∈ r.fresh, KeepsConst (GoodOn ok r.equations) st.const := by
  intro st hst s T hc
  have := List.all_eq_true.mp h st hst
  simp only [hc, asConst] at this
  exact keepsOn_of_keepsB this

/-- The guard of the clause `c`, an unfolding `(=> g s)`, implies that `ok` accepts the values of
the arguments of each instance `s` is of, in the models of `GoodOn ok eqs` that satisfy
`assums`. -/
def GuardOk (ok : Equation → List SmtValue → Prop) (eqs : List Equation) (assums : List Term)
    (c : Term) : Prop :=
  ∀ M, GoodOn ok eqs M → Satisfies M assums → ∀ g s, __eo_to_smt c = SmtTerm.imp g s →
    __smtx_model_eval M g = SmtValue.Boolean true →
    ∀ e ∈ eqs, ∀ us, instB e g s us = true → ok e (us.map (__smtx_model_eval M))

/-- With the predicate that accepts every argument, every guard is fine. -/
theorem guardOk_true (eqs : List Equation) (assums : List Term) (c : Term) :
    GuardOk (fun _ _ => True) eqs assums c :=
  fun _ _ _ _ _ _ _ _ _ _ _ => trivial

/-- An instance of a defining equation, guarded by a Boolean that implies that its arguments are
accepted, holds in the models of `GoodOn`, given the clauses before it. -/
theorem holds_unfold_on (hty : LogosTyping) {ok : Equation → List SmtValue → Prop}
    {eqs : List Equation} {c : Term} {assums : List Term}
    (h : unfoldB eqs c = true) (hg : GuardOk ok eqs assums c) :
    Holds (GoodOn ok eqs) assums c := by
  intro M hM hsat
  unfold unfoldB at h
  split at h
  · next g s heq =>
    obtain ⟨e, he, hinst⟩ := List.any_eq_true.mp h
    split at hinst
    · next us _ =>
      have hinst' := hinst
      simp only [instB, Bool.and_eq_true, decide_eq_true_eq] at hinst
      obtain ⟨⟨⟨hparams, hb⟩, hgb⟩, hsubst⟩ := hinst
      obtain ⟨hσ, htyped⟩ := params_of_paramsB hty hsat.1 hparams
      have hs : __smtx_model_eval M s = __smtx_model_eval
          (setConsts M (bindValues e.params (us.map (__smtx_model_eval M))))
          (__eo_to_smt e.term) := by
        rw [← hsubst, eval_subst hσ M _ hb, bindingValues_bindParams]
      rw [heq]
      simp only [__smtx_model_eval]
      obtain ⟨bg, hbg⟩ := eval_bool hty hsat.1 hgb
      cases bg
      · obtain ⟨b, hb'⟩ := (hM e he _ htyped).1
        rw [hbg, hs, hb']
        cases b <;> rfl
      · rw [hs, (hM e he _ htyped).2 (hg M hM hsat g s heq hbg e he us hinst')]
        exact eval_imp_true hty hsat.1 hgb
    · simp at hinst
  · simp at h

/-- Each fact holds, in the models that `Good` selects, given the clauses before it, unless
`just` accepts it given them. -/
def FactsHoldBy (Good : SmtModel → Prop) (just : List Term → Term → Prop) :
    List Term → List Term → Prop
  | _, [] => True
  | assums, t :: ts =>
    (just assums t ∨ Holds Good assums t) ∧ FactsHoldBy Good just (assums ++ [t]) ts

theorem factsHold_of_by {Good : SmtModel → Prop} {just : List Term → Term → Prop}
    (hjust : ∀ assums t, just assums t → Holds Good assums t) :
    ∀ {assums ts : List Term}, FactsHoldBy Good just assums ts → FactsHold Good assums ts
  | _, [], _ => trivial
  | assums, t :: _, ⟨h1, h2⟩ =>
    ⟨h1.elim (hjust assums t) id, factsHold_of_by hjust h2⟩

/-- An unfolding of a defining equation whose guard implies that its arguments are accepted. -/
def GuardedUnfold (ok : Equation → List SmtValue → Prop) (eqs : List Equation)
    (assums : List Term) (t : Term) : Prop :=
  unfoldB eqs t = true ∧ GuardOk ok eqs assums t

/-- `no_good_model_of_unfold`, for the models that satisfy the defining equations only on the
arguments that `ok` accepts: if the checker accepts a certificate, the check on terms holds, and
the defining equations don't mention the fresh symbols, then no well-formed model of `GoodOn ok`
satisfies the assumptions of the query, given that each fact holds in those models (given the
clauses before it), except the unfoldings whose guards imply that `ok` accepts their arguments. -/
theorem no_good_model_of_unfold_on (sound : LogosSound) (hty : LogosTyping)
    (ok : Equation → List SmtValue → Prop)
    {certificate : Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked) (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hkeeps : r.keeps = true)
    (hfacts : FactsHoldBy (GoodOn ok r.equations) (GuardedUnfold ok r.equations)
      (extend r.base r.fresh) r.facts) :
    ∀ M, GoodOn ok r.equations M → ¬ Satisfies M r.base :=
  no_good_model_of_accept sound hty (GoodOn ok r.equations) hAccept hr hcheck
    (keepsConstOn_of_keeps hkeeps)
    (factsHold_of_by (fun _ _ h => holds_unfold_on hty h.1 h.2) hfacts)

end Inox
