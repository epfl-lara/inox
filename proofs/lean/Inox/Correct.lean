/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Accept
import Cpc.Spec

/-!
What the checker's answer gives, given the soundness of Logos: the assumptions of the proof of a
certificate that the checker accepts have no model. The checker checks that each is an assert of
the certificate's script as it is, up to how cvc5 prints testers.

The soundness of Logos is a hypothesis here, `LogosSound`, so that this module only needs the
definitions of Logos. `Inox/Closed.lean` discharges it with the theorem of Logos, whose proofs
take hours to build.
-/

namespace Inox

open Logos (Sexp)
open Eo

/-- The soundness of Logos, as `correct___logos_check_proof` of `Cpc/ApiCorrect.lean` states it:
the conjunction of the assumptions of a proof that Logos finds correct has no model. -/
def LogosSound : Prop :=
  ∀ (input : String) (assums : List Term) (cmds : CCmdList),
    parseProof input = Except.ok (assums, cmds) →
    logos_check_proof input = Except.ok Verdict.correct →
    eo_satisfiability (logos_assumption_term assums) false

/-- What `accept` accepts, Logos finds correct. -/
theorem logos_correct_of_accept (certificate : Sexp) (checked : Checked)
    (hAccept : accept certificate = .ok checked) :
    logos_check_proof checked.proof = .ok Verdict.correct := by
  unfold accept at hAccept
  split at hAccept
  · cases hAccept
  · split at hAccept
    · cases hAccept
      assumption
    · cases hAccept

/-- If the checker accepts a certificate, then the conjunction of the assumptions of its proof,
as Logos reads them, has no model. -/
theorem unsat_of_accept (sound : LogosSound)
    (certificate : Sexp) (checked : Checked) (assums : List Term) (cmds : CCmdList)
    (hAccept : accept certificate = .ok checked)
    (hParse : parseProof checked.proof = .ok (assums, cmds)) :
    eo_satisfiability (logos_assumption_term assums) false :=
  sound checked.proof assums cmds hParse (logos_correct_of_accept certificate checked hAccept)

end Inox
