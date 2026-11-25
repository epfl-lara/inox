/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox

/-!
`inox-check <file>...` checks the certificates of each file, such as what Inox prints for an
input with `get-proof` commands, and has Logos check their proofs. With `--rules`, it checks the
rules only. With `--terms`, it also checks the rules on the terms that Logos reads
(`Inox/RuleSteps.lean`): each rule that introduces a fresh symbol does, and every assumption of the
proof is a clause of a rule. It exits with 1 unless it accepts every certificate.
-/

open Inox
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

def main (args : List String) : IO UInt32 := do
  let (rulesOnly, terms, files) := match args with
    | "--rules" :: files => (true, false, files)
    | "--terms" :: files => (false, true, files)
    | files => (false, false, files)
  if files.isEmpty then
    IO.eprintln "usage: inox-check [--rules | --terms] <file>..."
    return 2
  let mut failed := false
  let mut total := 0
  for file in files do
    let mut n := 0
    for parsed in certificates (← IO.FS.readFile file) do
      n := n + 1
      total := total + 1
      let result : Check Checked := match parsed with
        | .error e => .error s!"the certificate doesn't parse: {e}"
        | .ok certificate => if rulesOnly then check certificate else accept certificate
      let result : Check (Checked × String) := match result with
        | .error e => .error e
        | .ok c =>
          if !terms then .ok (c, "") else
          match termSteps c with
          | .error e => .error s!"on terms: {e}"
          | .ok r =>
            if r.check then
              .ok (c, s!", on terms {r.fresh.length} fresh-symbol steps, {r.facts.length} facts, " ++
                s!"{r.derived.length} derived clauses, {r.base.length} base clauses, " ++
                s!"{r.equations.length} defining equations, " ++
                s!"{r.facts.length - r.otherFacts.length} facts are unfoldings of them" ++
                (if r.keeps then "" else " (but a fresh symbol is in an equation)"))
            else .error s!"on terms: {r.why}"
      match result with
      | .ok (c, onTerms) =>
        IO.println (s!"ok   {file} {n}: {c.asserts} asserts, {c.rules} rules, " ++
          s!"{c.instances} instances, {c.templates} templates{onTerms}")
      | .error why =>
        failed := true
        IO.println s!"FAIL {file} {n}: {why}"
    (← IO.getStdout).flush
  IO.println s!"{total} certificates, {if failed then "not all of which hold" else "which all hold"}"
  return if failed || total == 0 then 1 else 0
