/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Correct
import Cpc.ApiCorrect

/-!
The theorems of `Inox/Correct.lean` without their hypothesis: Logos is sound, by its own theorem.
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

end Inox
