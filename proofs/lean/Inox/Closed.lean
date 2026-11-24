/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Correct
import Inox.Extend
import Cpc.ApiCorrect
import Cpc.Proofs.TypePreservation.Full
import Cpc.Proofs.Canonical.Eval

/-!
The theorems of `Inox/Correct.lean` and `Inox/Extend.lean` without their hypotheses: Logos is
sound, and its evaluation preserves types, by its own theorems.
This module needs the proofs of Logos, which take hours to build.
-/

namespace Inox

open Logos (Sexp)
open Eo

theorem logos_sound : LogosSound := correct___logos_check_proof

/-- If the checker accepts a certificate, then the conjunction of the assumptions of its proof,
as Logos reads them, has no model. -/
theorem unsat_of_accept_closed
    (certificate : Sexp) (checked : Checked) (assums : List Term) (cmds : CCmdList)
    (hAccept : accept certificate = .ok checked)
    (hParse : parseProof checked.proof = .ok (assums, cmds)) :
    eo_satisfiability (logos_assumption_term assums) false :=
  unsat_of_accept logos_sound certificate checked assums cmds hAccept hParse

/-- Evaluation preserves types and gives canonical values, by the theorems of Logos. -/
theorem logos_typing : Extend.LogosTyping :=
  ⟨fun M t hM ht => ⟨Smtm.type_preservation M hM t ht, Smtm.model_eval_canonical M hM t ht⟩,
    fun _ h => Smtm.bool_value_canonical h⟩

/-- Any model of the base assumptions extends to a model of them and of the clauses of steps that
can follow them, each introducing a fresh symbol. -/
theorem extend_sat_closed (sts : List Extend.Step) (assums : List Term)
    (hsts : Extend.StepsFresh assums sts) (M : Smtm.SmtModel) (hsat : Satisfies M assums) :
    ∃ M', Satisfies M' (Extend.extend assums sts) :=
  Extend.extend_sat logos_typing sts assums hsts M hsat

end Inox
