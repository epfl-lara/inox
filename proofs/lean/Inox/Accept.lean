/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Checker
import Cpc.Api

/-!
What the checker accepts: a certificate whose rules account for its script (`Inox.check`), and
whose proof Logos finds correct. `Inox/Correct.lean` states what that gives.
-/

namespace Inox

open Logos (Sexp)

/-- The certificates of `content`: the s-expressions that start a line with `(inox-certificate`,
since Inox prints other lines there too. -/
def certificates (content : String) : List (Except String Sexp) :=
  let rec go : List String → List (Except String Sexp)
    | [] => []
    | line :: rest =>
      if line.startsWith "(inox-certificate" then
        (Sexp.Parser.sexp.run ("\n".intercalate (line :: rest))) :: go rest
      else go rest
  go (content.splitOn "\n")

/-- Why Logos doesn't find a proof correct. -/
def refusal : Except String Eo.Verdict → String
  | .ok .correct => "correct"
  | .ok .incorrect => "Logos doesn't accept the proof"
  | .ok .incomplete => "Logos accepts the proof, which is outside of what its correctness theorem covers"
  | .error e => s!"Logos can't read the proof: {e}"

/-- Checks `certificate` and has Logos check its proof. -/
def accept (certificate : Sexp) : Check Checked :=
  match check certificate with
  | .error why => .error why
  | .ok checked =>
    match Eo.logos_check_proof checked.proof with
    | .ok .correct => .ok checked
    | other => .error (refusal other)

end Inox
