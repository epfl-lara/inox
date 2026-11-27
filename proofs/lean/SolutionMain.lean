/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Reached

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

/-- Whether the theorem applies to `certificate`, and what to say of it. -/
def applies (certificate : Logos.Sexp) (remaining : Bool) : Bool × String :=
  match accept certificate with
  | .error why => (false, s!"the checker doesn't accept it: {(why.splitOn "\n").headD why}")
  | .ok checked =>
    match termSteps checked with
    | .error why => (false, s!"on terms: {why}")
    | .ok r =>
      if !r.check then (false, s!"on terms: {r.why}")
      else if !sourceCheck r then (false, s!"outside the fragment: {whySource r}")
      else if !reachedCheck r then (false, whyReached r remaining)
      else (true, s!"{r.equations.length} functions, {r.query.length} expressions of the " ++
        s!"query, {r.facts.length} facts")

def main (args : List String) : IO UInt32 := do
  let remaining := args.contains "--remaining"
  let files := args.filter (· != "--remaining")
  if files.isEmpty then
    IO.eprintln "usage: inox-solution [--remaining] <file>..."
    return 2
  let mut total := 0
  let mut proved := 0
  for file in files do
    let mut n := 0
    for parsed in certificates (← IO.FS.readFile file) do
      n := n + 1
      total := total + 1
      let (ok, what) := match parsed with
        | .error e => (false, s!"the certificate doesn't parse: {e}")
        | .ok certificate => applies certificate remaining
      if ok then proved := proved + 1
      IO.println s!"{if ok then "no solution" else "not shown "} {file} {n}: {what}"
      (← IO.getStdout).flush
  IO.println s!"no_solution_of_reached applies to {proved} of {total} certificates"
  return if proved == total && total > 0 then 0 else 1
