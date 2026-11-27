/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Correct
import Cpc.Api

/-!
From the conclusion of `Inox/Correct.lean`, that the conjunction of the assumptions of a proof
has no model, to a statement about the assumptions themselves: no well-formed model makes all of
them true, and so none makes true every formula of a list that contains them all (the asserts of
a script, say).

This module only needs the definitions of Logos: the conjunction `logos_assumption_term` and the
semantics of `Cpc/SmtModel.lean`. With `unsat_of_accept`, it gives that no model satisfies the
assumptions of the proof of a certificate that the checker accepts.
-/

namespace Inox

open Logos (Sexp)
open Eo
open Smtm

/-- `M` is a well-formed model in which every formula of `ts` is true. -/
def Satisfies (M : SmtModel) (ts : List Term) : Prop :=
  model_wf M ∧ ∀ t ∈ ts, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean true

/-- The conjunction that `argListAssumes` builds over the list folded from `rest` and `ts` is true
in `M` when the one over `rest` is and every formula of `ts` is. -/
theorem eval_argListAssumes_foldl (M : SmtModel) (ts : List Term) (rest : CArgList)
    (hts : ∀ t ∈ ts, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean true)
    (hrest : __smtx_model_eval M (__eo_to_smt (argListAssumes rest)) = SmtValue.Boolean true) :
    __smtx_model_eval M
        (__eo_to_smt (argListAssumes (ts.foldl logos_assumption_list_step rest))) =
      SmtValue.Boolean true := by
  induction ts generalizing rest with
  | nil => exact hrest
  | cons t ts ih =>
    apply ih
    · exact fun u hu => hts u (List.mem_cons_of_mem t hu)
    · have ht := hts t List.mem_cons_self
      show __smtx_model_eval M (SmtTerm.and (__eo_to_smt t) (__eo_to_smt (argListAssumes rest))) = _
      simp only [__smtx_model_eval, ht, hrest, __smtx_model_eval_and, SmtEval.native_and]
      rfl

/-- If every assumption is true in `M`, so is their conjunction. -/
theorem eval_logos_assumption_term (M : SmtModel) (assums : List Term)
    (h : ∀ t ∈ assums, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean true) :
    __smtx_model_eval M (__eo_to_smt (logos_assumption_term assums)) = SmtValue.Boolean true :=
  eval_argListAssumes_foldl M assums CArgList.nil h (by rfl)

/-- If the conjunction of the assumptions has no model, no model satisfies the assumptions. -/
theorem no_model_of_unsat (assums : List Term)
    (hUnsat : eo_satisfiability (logos_assumption_term assums) false) :
    ∀ M, ¬ Satisfies M assums := by
  intro M ⟨hwf, hsat⟩
  cases hUnsat with
  | intro_false hfalse =>
    have htrue := eval_logos_assumption_term M assums hsat
    rw [hfalse M hwf] at htrue
    cases htrue

/-- If the conjunction of the assumptions has no model, no model satisfies a list that contains
every assumption. -/
theorem no_model_of_unsat_of_subset (assums asserts : List Term)
    (hUnsat : eo_satisfiability (logos_assumption_term assums) false)
    (hSub : ∀ t ∈ assums, t ∈ asserts) :
    ∀ M, ¬ Satisfies M asserts := by
  intro M ⟨hwf, hsat⟩
  exact no_model_of_unsat assums hUnsat M ⟨hwf, fun t ht => hsat t (hSub t ht)⟩

/-- If the checker accepts a certificate, then no well-formed model makes all the assumptions of
its proof, as Logos reads them, true. -/
theorem no_model_of_accept (sound : LogosSound)
    (certificate : Sexp) (checked : Checked) (assums : List Term) (cmds : CCmdList)
    (hAccept : accept certificate = .ok checked)
    (hParse : parseProof checked.proof = .ok (assums, cmds)) :
    ∀ M, ¬ Satisfies M assums :=
  no_model_of_unsat assums (unsat_of_accept sound certificate checked assums cmds hAccept hParse)

end Inox
