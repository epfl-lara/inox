/- Copyright 2009-2026 EPFL, Lausanne -/
import Logos.Sexp
import Std.Data.HashMap
import Std.Data.HashSet

/-!
The s-expressions of a certificate, whose clauses are compared as text. An atom keeps its text.
-/

namespace Inox

open Logos (Sexp)

/-- The text of an s-expression, which two s-expressions share only when they are the same. -/
def text (e : Sexp) : String := e.serialize

def app (op : String) (args : List Sexp) : Sexp := .expr (.atom op :: args)

def tt : Sexp := .atom "true"
def ff : Sexp := .atom "false"
def mkNot (e : Sexp) : Sexp := app "not" [e]
/-- `es` without the s-expressions that one before them repeats. -/
def distinct (es : List Sexp) : List Sexp :=
  (es.foldl (fun (kept : List Sexp × Std.HashSet String) e =>
    if kept.2.contains (text e) then kept else (e :: kept.1, kept.2.insert (text e))) ([], {})).1.reverse

/-- The conjunction of `es`, flat as the solver builds it: the operands of an operand that is a
conjunction are its own, an operand is there once, and the conjunction of one operand is that
operand. -/
def mkAnd (es : List Sexp) : Sexp :=
  match distinct (es.flatMap fun e => match e with
    | .expr (.atom "and" :: inner) => inner
    | _ => [e]) with
  | [one] => one
  | flat => app "and" flat
def mkOr (es : List Sexp) : Sexp := app "or" es
def mkImplies (l r : Sexp) : Sexp := app "=>" [l, r]
def mkEq (l r : Sexp) : Sexp := app "=" [l, r]

/-- `e` with its testers `((_ is C) e)` and `(is-C e)` as cvc5 prints them in its proofs,
`(is C e)`, and otherwise as it is. -/
partial def testers : Sexp → Sexp
  | .expr (.expr [.atom "_", .atom "is", c] :: args) => .expr (.atom "is" :: c :: args.map testers)
  | .expr (.atom op :: args) =>
    if op.startsWith "is-" then .expr (.atom "is" :: .atom (op.drop 3).toString :: args.map testers)
    else .expr (.atom op :: args.map testers)
  | .expr items => .expr (items.map testers)
  | atom => atom

/-- The conjunction (`op` is `and`, `unit` is `true`, `zero` is `false`) or disjunction of `es`
as scala-smtlib's `and` and `or` build it: `zero` if an operand is `zero`, and otherwise its one
operand other than `unit`, or `unit` if it has none; with several such operands, all of `es`, `unit`
ones too. -/
def junction (op : String) (unit zero : Sexp) (es : List Sexp) : Sexp :=
  if es.any (text · == text zero) then zero
  else match es.filter (text · != text unit) with
    | [] => unit
    | [one] => one
    | _ => app op es

/-- `e` with its conjunctions and disjunctions built as the solver builds them (`junction`), from
the inside out: an instance of a template, whose parameters may have the values `true` or `false`,
is the template's clauses with the values, which the solver prints with its constructors. They
only drop operands that are units, or keep a zero alone, so the clause means what it did. -/
partial def simplified : Sexp → Sexp
  | .expr (.atom "and" :: es) => junction "and" tt ff (es.map simplified)
  | .expr (.atom "or" :: es) => junction "or" ff tt (es.map simplified)
  | .expr items => .expr (items.map simplified)
  | atom => atom

/-- `e` where each symbol that `values` has is its value, and each of the `terms`, by its text,
is its own. -/
partial def substitute (values : Std.HashMap String Sexp) (terms : List (String × Sexp) := []) : Sexp → Sexp
  | .atom a => (values.get? a).getD (.atom a)
  | .expr items =>
    match if terms.isEmpty then none else terms.lookup (text (.expr items)) with
    | some value => value
    | none => .expr (items.map (substitute values terms))

end Inox
