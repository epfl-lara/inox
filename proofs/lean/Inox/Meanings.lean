/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Sexp

/-!
# The meanings of the symbols of a template

A template's clauses name, besides its parameters, local symbols: the blockers of its branches,
the results of its expressions, the values of its nested calls and constructors. Each has a
meaning, a term over the template's parameters. `meanings` reads them as the source check of the
Scala checker (`inox.certificates.Sources`) does:

- the source's `where` gives the meanings of the symbols whose clauses are guarded several times,
  such as the result of an `ite`, an `and` or an `or`, a merged call, or the typing of a value;
- a blocker means the conditions of its path: `(and p c)` for `(= b (and p c))`, `(= (and p c) b)`,
  `(= b p)` where `b` is a path with no condition of its own, or `(=> p (= b c))` where `b` is the
  blocker of clauses of its own; `false` for `(= b false)`; `(or b1 b2 ..)` for a merge
  `(= (or b1 b2 ..) b)`;
- failing these, a symbol that one clause `(=> b (= v t))` (or `(=> b (= t v))`) defines means `t`.

The typing of a set has no such meaning: it names an element and a rest of the set, which are
any when the set is not empty. `setTyping` reads them as the element that `set.choose` gives and
the others, which makes the typing true.

Symbols in a meaning are replaced by theirs. A symbol defined from itself, such as an element of a
set that is a union with it, has no meaning, nor has one defined several times.

Nothing relies on this for soundness: the meanings are definitions of fresh symbols, which
`Inox/Instances.lean` checks as any other, and the clauses of an instance are checked once they
are substituted.
-/

namespace Inox.Meanings

open Logos (Sexp)

/-- The atoms of `e`. -/
partial def atoms : Sexp → List String
  | .atom a => [a]
  | .expr es => es.flatMap atoms

/-- `e` without the assumptions of the source, `(assume c v)` being `v`. -/
partial def unassumed : Sexp → Sexp
  | .expr [.atom "assume", _, v] => unassumed v
  | .expr es => .expr (es.map unassumed)
  | a => a

/-- `e` with `(ite c a a)` as `a`. -/
partial def collapse : Sexp → Sexp
  | .expr es => match es.map collapse with
    | [.atom "ite", c, a, b] => if a == b then a else .expr [.atom "ite", c, a, b]
    | es => .expr es
  | a => a

/-- What a meaning `(l, r)` that the source gives says, if it is that of the typing of a set whose
elements have no typing of their own: `l` is a marker of the typing of `x`, and `r` is
`(ite (= x empty) true (assume (= x (set.union {e} rest)) l'))`, where `l'` is `l` of `rest`.
Such a typing is true of each set, with an element of `x` for `e` and the others for `rest` when
`x` is not empty. This gives the meanings of the two markers, `true`, and those of `e` and `rest`:
the element that `set.choose` gives of `x`, and `x` without it. -/
def setTyping : Sexp × Sexp → Option (List (Sexp × Sexp) × List (String × Sexp))
  | (l@(.expr _), .expr [.atom "ite", .expr [.atom "=", .atom x, empty], .atom "true",
      .expr [.atom "assume",
        .expr [.atom "=", .atom x', .expr [.atom "set.union", one, .atom rest]], l']]) =>
    let elem := match one with
      | .expr [.atom "set.insert", .atom e, empty'] => if empty' == empty then some e else none
      | .expr [.atom "set.singleton", .atom e] => some e
      | _ => none
    match elem with
    | some e =>
      if x' == x && e != x && rest != x && e != rest &&
          l' == substitute (Std.HashMap.ofList [(x, .atom rest)]) [] l then
        let c := app "set.choose" [.atom x]
        some ([(l, tt), (l', tt)],
          [(e, c), (rest, app "set.minus" [.atom x, app "set.singleton" [c]])])
      else none
    | none => none
  | _ => none

/-- What the clauses of a template state of its local symbols. -/
structure Shape where
  /-- the meanings that the source gives -/
  given : Std.HashMap String Sexp
  /-- the path of each blocker -/
  blockers : Std.HashMap String Sexp := {}
  /-- the terms that the clauses define each other symbol as -/
  definitions : Std.HashMap String (List Sexp) := {}

/-- Reads the clauses of a template: `free` are its local symbols whose meanings the source doesn't
give, `call` is the call of its source, if it is a function. -/
def Shape.of (start : String) (free : String → Bool) (given : Std.HashMap String Sexp)
    (call : Option Sexp) (body : List Sexp) : Shape := Id.run do
  let mut blockers : Std.HashMap String Sexp := {}
  let mut guarded : Array (String × Sexp) := #[]
  let mut aliases : Array (String × String) := #[]
  for clause in body do
    match clause with
    | .expr [.atom "=", rhs@(.expr [.atom "and", .atom _, _]), .atom b] =>
      if free b && !blockers.contains b then blockers := blockers.insert b rhs
    | .expr [.atom "=", .atom b, rhs@(.expr (.atom "and" :: .atom _ :: _ :: _))] =>
      if free b && !blockers.contains b then blockers := blockers.insert b rhs
    | .expr [.atom "=", .atom b, .atom "false"] =>
      if free b && !blockers.contains b then blockers := blockers.insert b ff
    | .expr [.atom "=", rhs@(.expr (.atom "or" :: _)), .atom m] =>
      if free m && !blockers.contains m then blockers := blockers.insert m rhs
    | .expr [.atom "=", .atom b, .atom m] => aliases := aliases.push (b, m)
    | .expr [.atom "=>", .atom b, c] => guarded := guarded.push (b, c)
    | _ => pure ()
  -- `(= b m)`: the blocker `b` of a path with no condition of its own, below `m`, or the reverse
  for (b, m) in aliases do
    let defined (a : String) := a == start || blockers.contains a
    if defined m && free b && !defined b then blockers := blockers.insert b (.atom m)
    else if defined b && free m && !defined m then blockers := blockers.insert m (.atom b)
  -- `(=> b (= p c))` with `p` the blocker of clauses of its own: the blocker of that condition
  let guards : Std.HashSet String := Std.HashSet.ofList (guarded.toList.map (·.1))
  for (b, clause) in guarded do
    if let .expr [.atom "=", .atom p, c] := clause then
      if guards.contains p && free p && p != b && !blockers.contains p && !(atoms c).contains p then
        blockers := blockers.insert p (app "and" [.atom b, c])
  let definable (e : Sexp) : Bool := match e with
    | .atom a => free a && !blockers.contains a && a != start
    | _ => false
  let mut definitions : Std.HashMap String (List Sexp) := {}
  for (_, clause) in guarded do
    match clause with
    | .expr [.atom "=", v@(.atom a), t] =>
      if definable v && !(atoms t).contains a then
        definitions := definitions.insert a (definitions.getD a [] ++ [t])
      else if let .atom w := t then
        if definable t && !definable v && call != some v && !given.contains a then
          definitions := definitions.insert w (definitions.getD w [] ++ [v])
    | .expr [.atom "=", t, .atom v] =>
      if definable (.atom v) && !definable t && !(atoms t).contains v && call != some t &&
          !(match t with | .atom a => given.contains a | _ => false) then
        definitions := definitions.insert v (definitions.getD v [] ++ [t])
    | _ => pure ()
  return { given, blockers, definitions }

mutual

/-- The meaning of `v`, if it has one; `visiting` are the symbols whose meanings are being found,
which a meaning can't mention. -/
partial def Shape.meaning (s : Shape) (visiting : List String) (v : String) : Option Sexp :=
  if visiting.contains v then none else
  let vis := v :: visiting
  match s.given.get? v, s.blockers.get? v, s.definitions.get? v with
  | some m, _, _ => s.expand vis m
  | none, some path, _ => s.expand vis path
  | none, none, some [t] => s.expand vis t
  | _, _, _ => none

/-- `e` with each symbol that has a meaning replaced by it; none where a symbol of `e` is defined
from itself. -/
partial def Shape.expand (s : Shape) (visiting : List String) : Sexp → Option Sexp
  | .atom a =>
    if visiting.contains a then none
    else if s.given.contains a || s.blockers.contains a || s.definitions.contains a then
      some ((s.meaning visiting a).getD (.atom a))
    else some (.atom a)
  | .expr es => (es.mapM (s.expand visiting)).map .expr

end

/-- The meaning of each local symbol of a template that has one, in the order of `locals`: the
template's start is its first parameter, `given` are the meanings that its source's `where` gives
of its symbols, with the meanings of the source's markers in place, and `call` is the call of its
source, if it is a function. The source's assumptions are left out of the meanings, `(assume c v)`
being `v`. -/
def meanings (params : List Sexp) (locals : List String) (body : List Sexp)
    (given : List (String × Sexp)) (call : Option Sexp) : List (String × Sexp) :=
  match params with
  | .atom start :: _ =>
    let localSet := Std.HashSet.ofList locals
    let givenMap := Std.HashMap.ofList (given.filterMap fun (v, m) =>
      if localSet.contains v then some (v, unassumed m) else none)
    let s :=
      Shape.of start (fun a => localSet.contains a && !givenMap.contains a) givenMap call body
    locals.filterMap fun v => (s.meaning [] v).map fun m => (v, collapse m)
  | _ => []

end Inox.Meanings
