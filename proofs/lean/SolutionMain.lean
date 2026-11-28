/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Reached
import Inox.Input
import Inox.Joined

/-!
`inox-solution <file>...` says, for each certificate of each file, whether
`no_solution_of_reached` (`Inox/Reached.lean`) applies to it: the checker accepts it
(`accept`), the rules hold on the terms that Logos reads (`TermSteps.check`), the equations and
the base clauses are the translations of the program and of the query read from them
(`sourceCheck`), and every fact is covered where the calls that evaluation goes through have
values (`reachedCheck`). These are the hypotheses of the theorem that are computed, so for such
a certificate the query that it reads has no solution in the program that it reads, given the
soundness of Logos. Otherwise it says which check fails, and with `--remaining` it prints the
facts that are not covered. It exits with 1 unless the theorem applies to every certificate.

With `--input` it also says, for each certificate, how many constraints of its input the theorem
on the encoders covers (`Inox.Input.covers_encoded`: where they all evaluate to `true`, so do
their encoded terms), and what the first of the others has that isn't read, and whether the
theorem on the input itself applies (`Inox.Joined.no_input_solution`: the input has no
solution), or why not.

It is an executable of the verification package, since the last two checks are defined over the
semantics of Inox: `lake build inox-solution` in `proofs/lean/verification`.
-/

open Inox Inox.Bridge

/-- Why `sourceCheck r` fails: its first part that does. -/
def whySource (r : TermSteps) : String :=
  let D := dataOf r
  let S := sigsOf r.equations
  let Γ := varsOf S r.query
  if !dataCheck D then "the datatypes it declares are not of the fragment"
  else if !sigCheck D S then "the signatures of its functions are not of the fragment"
  else if !r.equations.all (eqCheck D S) then
    s!"{(r.equations.filter fun e => !eqCheck D S e).length} of {r.equations.length} defining " ++
      "equations are not the translations of bodies of the fragment"
  else if !varsCheck D S Γ then "the free variables of its query are not of the fragment"
  else "its base clauses are not the translations of expressions of the fragment"

/-- Why `reachedCheck r` fails: a fresh symbol that is not apart, or the facts that are not
covered, by the kinds of their rules, with their clauses if `remaining`. -/
def whyReached (r : TermSteps) (remaining : Bool) : String :=
  let S := sigsOf r.equations
  if !apart (dataOf r) S (varsOf S r.query) r then
    "a fresh symbol is a function of the program or a variable of the query"
  else
    let covered := reachedCovered r
    let left := (r.facts.zip r.kinds).filter fun p => !covered p.1
    let kinds := (left.map (·.2.1)).eraseDups
    let counts := kinds.map fun k => s!"{k} {left.countP (·.2.1 == k)}"
    let clauses := if remaining then
        "".intercalate (left.map fun p => s!"\n  {p.2.1}: {text p.2.2}")
      else ""
    s!"{left.length} of {r.facts.length} facts are not covered [{", ".intercalate counts}]" ++
      clauses

/-- Whether the theorem applies to `certificate`, and what to say of it, with the terms that
Logos reads where it applies. -/
def applies (certificate : Logos.Sexp) (remaining : Bool) : Option TermSteps × String :=
  match accept certificate with
  | .error why => (none, s!"the checker doesn't accept it: {(why.splitOn "\n").headD why}")
  | .ok checked =>
    match termSteps checked with
    | .error why => (none, s!"on terms: {why}")
    | .ok r =>
      if !r.check then (none, s!"on terms: {r.why}")
      else if !sourceCheck r then (none, s!"outside the fragment: {whySource r}")
      else if !reachedCheck r then (none, whyReached r remaining)
      else (some r, s!"{r.equations.length} functions, {r.query.length} expressions of the " ++
        s!"query, {r.facts.length} facts")

/-- Whether `no_input_solution` applies to `certificate`, of which `no_solution_of_reached`
holds with the terms `r`, and what to say of it. -/
def joined (certificate : Logos.Sexp) (r : Option TermSteps) : Bool × String :=
  match r with
  | none => (false, "the theorem on the terms doesn't apply")
  | some r =>
    match Inox.Joined.readInput certificate with
    | .error why => (false, s!"the input isn't read: {why}")
    | .ok R =>
      if Inox.Joined.linkCheck R r then (true, "the input has no solution")
      else (false, "the input isn't lowered to the query without simplifications")

def main (args : List String) : IO UInt32 := do
  let remaining := args.contains "--remaining"
  let input := args.contains "--input"
  let files := args.filter fun a => a != "--remaining" && a != "--input"
  if files.isEmpty then
    IO.eprintln "usage: inox-solution [--remaining] [--input] <file>..."
    return 2
  let mut total := 0
  let mut proved := 0
  let mut constraints := 0
  let mut encoded := 0
  let mut inputs := 0
  for file in files do
    let mut n := 0
    for parsed in certificates (← IO.FS.readFile file) do
      n := n + 1
      total := total + 1
      let (r, what) := match parsed with
        | .error e => (none, s!"the certificate doesn't parse: {e}")
        | .ok certificate => applies certificate remaining
      let ok := r.isSome
      if ok then proved := proved + 1
      IO.println s!"{if ok then "no solution" else "not shown "} {file} {n}: {what}"
      if input then
        if let .ok certificate := parsed then
          let c := Inox.Input.covers certificate
          constraints := constraints + c.constraints
          encoded := encoded + c.covered.length
          let first := match c.first with
            | some why => s!"; of the first other, {why}"
            | none => ""
          IO.println s!"  input: {c.covered.length} of {c.constraints} constraints{first}"
          let (holds, why) := joined certificate r
          if holds then inputs := inputs + 1
          IO.println s!"  no_input_solution: {why}"
      (← IO.getStdout).flush
  IO.println s!"no_solution_of_reached applies to {proved} of {total} certificates"
  if input then
    IO.println s!"covers_encoded covers {encoded} of {constraints} constraints of their inputs"
    IO.println s!"no_input_solution applies to {inputs} of {total} certificates"
  return if proved == total && total > 0 then 0 else 1
