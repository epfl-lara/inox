/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Sexp

/-!
The lowering of the sources of the templates of a certificate, which Inox's SMT-LIB 3 printer
prints, to the syntax of the solver's session, in which the clauses of the templates are: the port
of `inox.certificates.Lowering` of the Scala checker, which documents each construct.

It only reads the certificate's tables: the `source-definitions` (the datatypes, and the
declarations and definitions of the functions of the sources), the `source-symbols` (the Inox
definition of each symbol of the sources, the sort of each variable, and the type arguments of each
instantiation of an uninterpreted function), and the session's `solver-symbols` (the Inox
definition of each symbol of the session, and for the symbols that a type determines, the SMT-LIB 3
sort of that type, or the list of the sorts of the type arguments of an instance).

A source prints each symbol whose session symbol depends on a type under the key that the
`solver-symbols` record for it, `(as x k)`, so the lowering infers no sort: it picks the session
symbol of the same Inox definition and of the same key, and a symbol without a key is that of the
one session symbol of its definition. Sorts are compared without their refinements (`:var` and
`:restrict`). The bodies of the `source-definitions` are generic: their keys mention the type
parameters of the definition, which the type arguments of a call, the key of its head, replace.

An error `(error S "message")` is lowered to an assumption that never holds, `(assume false v)`,
where `v` is a value of its sort that Logos reads, `0` or `false`, in place of the Scala
checker's `(error S')`: the terms of a source are read by Logos. An error of another sort is
refused.

It refuses a symbol of which the session has no symbol or several, and lambdas, `tuple.unit`,
bags, string operations and floating points, which it doesn't lower.
-/

namespace Inox.Lowering

open Logos (Sexp)

abbrev Lower := Except String

def refuse {α : Type} (why : String) : Lower α := .error why

def quoted : Sexp → Bool
  | .atom t => t.startsWith "\""
  | _ => false

/-- A symbol of a table: its name, its kind, the descriptions of the Inox definition that it
stands for, and the SMT-LIB 3 sort that it records, if any. -/
structure Entry where
  name : String
  kind : String
  descriptions : List String
  sort : Option Sexp

def keptAttributes : List Sexp → List Sexp
  | .atom ":var" :: _ :: rest => keptAttributes rest
  | .atom ":restrict" :: _ :: rest => keptAttributes rest
  | a :: rest => a :: keptAttributes rest
  | [] => []

/-- The sort `s` without its refinements, the attributes `:var` and `:restrict` of its
annotations `(! ..)`. -/
partial def erase : Sexp → Sexp
  | .expr (.atom "!" :: base :: attributes) =>
    match keptAttributes attributes with
    | [] => erase base
    | as => .expr (.atom "!" :: erase base :: as)
  | .expr items => .expr (items.map erase)
  | atom => atom

/-- The entry of the line `(name kind "description".. [sort])` of a symbol table. -/
def entry (line : Sexp) : Lower Entry :=
  match line with
  | .expr (.atom name :: .atom kind :: rest) =>
    let descriptions := (rest.takeWhile quoted).map text
    match rest.dropWhile quoted with
    | [] => pure ⟨name, kind, descriptions, none⟩
    | [s] => pure ⟨name, kind, descriptions, some (erase s)⟩
    | _ => refuse s!"{text line} doesn't describe a symbol"
  | other => refuse s!"{text other} doesn't describe a symbol"

def isDigits (t : String) : Bool := !t.isEmpty && t.all Char.isDigit

def isDecimal (t : String) : Bool :=
  match t.splitOn "." with
  | [a, b] => isDigits a && isDigits b
  | _ => false

def digitsAfter (t : String) (prefix_ : String) (ok : Char → Bool) : Bool :=
  t.startsWith prefix_ && t.length > prefix_.length && (t.toList.drop prefix_.length).all ok

def isBinary (t : String) : Bool := digitsAfter t "#b" fun c => c == '0' || c == '1'
def isHex (t : String) : Bool :=
  digitsAfter t "#x" fun c => c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def isLiteral (t : String) : Bool :=
  t == "true" || t == "false" || isDigits t || isDecimal t || isBinary t || isHex t || t.startsWith "\""

def intSort : Sexp := .atom "Int"
def bitVector (n : Nat) : Sexp := .expr [.atom "_", .atom "BitVec", .atom (toString n)]

/-- The size of the bit vector sort `s`. -/
def bitVectorOf : Sexp → Option Nat
  | .expr [.atom "_", .atom "BitVec", .atom n] => if isDigits n then some n.toNat! else none
  | .expr [.atom "!", .expr [.atom "_", .atom "BitVec", .atom n], .atom ":unsigned"] =>
    if isDigits n then some n.toNat! else none
  | _ => none

/-- The definition of a function of the sources, of type parameters `params`. -/
structure Definition where
  params : List String
  arguments : List String
  body : Sexp

/-- What the source of a template is of: `(function <call> <body>)`, `(definition <call> [(names
(<name> <subterm>) ..)])` or `(expression <term>)`, each with an optional `(where (l r) ..)` at its
end, which gives meanings. The lowering makes a `definition` a `function` with the body of the
function's definition. -/
inductive Source where
  | function (call body : Sexp) (meanings : List (Sexp × Sexp))
  | definition (call : Sexp) (names : List (Sexp × Sexp)) (meanings : List (Sexp × Sexp))
  | expression (term : Sexp) (meanings : List (Sexp × Sexp))

def pairsOf (name : String) : Sexp → Option (List (Sexp × Sexp))
  | .expr (.atom n :: pairs) => if n != name then none else pairs.mapM fun p => match p with
    | .expr [l, r] => some (l, r)
    | _ => none
  | _ => none

def whereOf : Sexp → Option (List (Sexp × Sexp)) := pairsOf "where"

def Source.ofSexp : Sexp → Option Source
  | .expr (.atom kind :: rest) =>
    let (terms, meanings) := match rest.getLast? >>= whereOf with
      | some w => (rest.dropLast, w)
      | none => (rest, [])
    match kind, terms with
    | "function", [call, body] => some (.function call body meanings)
    | "expression", [t] => some (.expression t meanings)
    | "definition", [call] => some (.definition call [] meanings)
    | "definition", [call, ns] => (pairsOf "names" ns).map (.definition call · meanings)
    | _, _ => none
  | _ => none

def Source.meanings : Source → List (Sexp × Sexp)
  | .function _ _ ms => ms
  | .definition _ _ ms => ms
  | .expression _ ms => ms

/-- The tables of a certificate. -/
structure Tables where
  session : Array Entry
  sessionNames : Std.HashMap String Entry
  sources : Std.HashMap String Entry
  /-- the definition of each defined function -/
  definitions : Std.HashMap String Definition
  /-- the uninterpreted functions that the source definitions declare, which markers are not -/
  declared : Std.HashSet String
  /-- the session's functions of their own, which `((as @ S) f ts)` applies directly -/
  predicates : Std.HashSet String

def atomOf (what : String) : Sexp → Lower String
  | .atom a => pure a
  | other => refuse s!"{text other} is not {what}"

def parameters (xs : List Sexp) : Lower (List (String × Sexp)) :=
  xs.mapM fun x => match x with
    | .expr [.atom x, s] => pure (x, s)
    | other => refuse s!"{text other} is not a parameter"

/-- The definitions of `d`: `define-fun` and `define-fun-rec` of `f ((x S) ..) R body` or of
`(par (A ..) (f ((x S) ..) R body))`, and `define-funs-rec` of the list of the signatures, each
`(f ((x S) ..) R)` or `(par (A ..) (f ((x S) ..) R))`, and of the list of the bodies. -/
def definitionsOf (d : Sexp) : Lower (List (String × Definition)) := do
  let signature (dec : Sexp) : Lower (String × List String × List (String × Sexp) × Sexp) :=
    match dec with
    | .expr [.atom "par", .expr ps, .expr [.atom f, .expr xs, range]] => do
      pure (f, ← ps.mapM (atomOf "a sort parameter"), ← parameters xs, range)
    | .expr [.atom f, .expr xs, range] => do pure (f, [], ← parameters xs, range)
    | other => refuse s!"{text other} is not the signature of a function"
  match d with
  | .expr [.atom k, .atom f, .expr xs, _, body] =>
    if k == "define-fun" || k == "define-fun-rec" then pure [(f, ⟨[], (← parameters xs).map (·.1), body⟩)]
    else pure []
  | .expr [.atom k, .expr [.atom "par", .expr ps, .expr [.atom f, .expr xs, _, body]]] =>
    if k == "define-fun" || k == "define-fun-rec" then
      pure [(f, ⟨← ps.mapM (atomOf "a sort parameter"), (← parameters xs).map (·.1), body⟩)]
    else pure []
  | .expr [.atom "define-funs-rec", .expr decs, .expr bodies] =>
    if decs.length != bodies.length then refuse s!"{text d} is not a definition"
    (decs.zip bodies).mapM fun (dec, body) => do
      let (f, ps, xs, _) ← signature dec
      pure (f, ⟨ps, xs.map (·.1), body⟩)
  | .expr (.atom k :: _) =>
    if k == "define-fun" || k == "define-fun-rec" || k == "define-funs-rec" then refuse s!"{text d} is not a definition"
    else pure []
  | _ => pure []

/-- The tables of a certificate: its `script` (with that of its templates), its session's
`solverSymbols`, and its source `declarations` (the `source-definitions`) and `sourceSymbols`. -/
def Tables.make (script solverSymbols declarations sourceSymbols : List Sexp) : Lower Tables := do
  let session ← solverSymbols.mapM entry
  let sources ← sourceSymbols.mapM entry
  let mut definitions : Std.HashMap String Definition := {}
  for d in declarations do
    for (f, defn) in ← definitionsOf d do
      definitions := definitions.insert f defn
  let declared := declarations.filterMap fun d => match d with
    | .expr [.atom "declare-fun", .atom f, _, _] => some f
    | .expr [.atom "declare-fun", .expr [.atom "par", _, .expr (.atom f :: _)]] => some f
    | _ => none
  let predicates := script.filterMap fun c => match c with
    | .expr [.atom "declare-fun", .atom f, .expr (_ :: _), _] => some f
    | _ => none
  pure {
    session := session.toArray,
    sessionNames := Std.HashMap.ofList (session.map fun e => (e.name, e)),
    sources := Std.HashMap.ofList (sources.map fun e => (e.name, e)),
    definitions,
    declared := Std.HashSet.ofList declared,
    predicates := Std.HashSet.ofList predicates }

namespace Tables

variable (t : Tables)

def source (a kind : String) : Option Entry := (t.sources.get? a).filter (·.kind == kind)

/-- A marker: an uninterpreted function of the sources that the declarations don't declare. -/
def isMarker (a : String) : Bool := (t.source a "uninterpreted").isSome && !t.declared.contains a

/-- Whether `e` names a marker. -/
partial def hasMarker : Sexp → Bool
  | .atom a => t.isMarker a
  | .expr items => items.any hasMarker

def isVariable (bound : Std.HashSet String) (a : String) : Bool :=
  bound.contains a || (t.source a "variable").isSome

/-- The one session symbol that `p` holds of. -/
def unique (what : String) (p : Entry → Bool) : Lower Sexp :=
  match t.session.toList.filter p with
  | [e] => pure (.atom e.name)
  | [] => refuse s!"the session has no {what}"
  | es => refuse s!"the session has several {what}s: {", ".intercalate (es.map (·.name))}"

/-- The session's sort of the sort `s`. -/
partial def lowerSort (s : Sexp) : Lower Sexp :=
  match erase s with
  | .atom "Bool" => pure (.atom "Bool")
  | .atom "Int" => pure intSort
  | .atom "Real" => pure (.atom "Real")
  | .atom "String" => pure (.atom "String")
  | .atom "Char" => pure (bitVector 16)
  | .expr (.atom "->" :: _) => pure intSort
  | .expr [.atom "Array", k, v] => do pure (app "Array" [← lowerSort k, ← lowerSort v])
  | .expr [.atom "Set", e] => do pure (app "Set" [← lowerSort e])
  | other => match bitVectorOf other with
    | some n => pure (bitVector n)
    | none => t.unique s!"sort {text other}" fun e => e.kind == "sort" && e.sort == some other

partial def instantiate (subst : Std.HashMap String Sexp) : Sexp → Sexp
  | .atom a => (subst.get? a).getD (.atom a)
  | .expr items => .expr (items.map (instantiate subst))

/-- The operations that lower to themselves, applied to their lowered arguments. -/
def same : List String := ["not", "and", "or", "=>", "xor", "=", "distinct", "<", "<=", ">", ">=",
  "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
  "+", "-", "*", "div", "mod", "abs", "bvadd", "bvsub", "bvmul", "bvudiv", "bvsdiv",
  "bvurem", "bvsrem", "bvsmod", "bvneg", "bvnot", "bvand", "bvor", "bvxor", "bvshl", "bvashr", "bvlshr",
  "store", "/", "bv2nat", "ite", "select"]
def setOperations : List (String × String) := [("member", "set.member"), ("subset", "set.subset"),
  ("union", "set.union"), ("intersection", "set.inter"), ("setminus", "set.minus")]

def bindings (bs : List Sexp) : Lower (List (String × Sexp)) :=
  bs.mapM fun b => match b with
    | .expr [.atom x, s] => pure (x, s)
    | other => refuse s!"{text other} is not a binding"

/-- Whether `e` has no variable, for a set's first element. -/
partial def ground (bound : Std.HashSet String) : Sexp → Bool
  | .atom a => !t.isVariable bound a
  | .expr items => items.all (ground bound)

/-- The symbol `x` under the key `k` that picks its symbol of the session, `(as x k)`, and the
arguments that it is applied to. -/
def keyed : Sexp → Option (Sexp × Sexp × List Sexp)
  | .expr [.atom "as", x, k] => some (x, k, [])
  | .expr (.expr [.atom "as", x, k] :: args) => some (x, k, args)
  | _ => none

/-- The session's symbol of the symbol `head` of the sources: the one of the same Inox
definition, and of the sort `key` when the source gives one. -/
def symbol (head : Sexp) (key : Option Sexp) : Lower Sexp :=
  let pick (what : String) (p : Entry → Bool) : Lower Sexp :=
    t.unique (what ++ (key.map fun k => s!" at {text k}").getD "") fun e => p e && key.all (e.sort == some ·)
  let index (i : String) := s!"\"{i}\""
  match head with
  | .atom "tuple" => pick "tuple constructor" fun e => e.kind == "constructor" && e.descriptions.length == 1
  | .expr [.atom "_", .atom "tuple.select", .atom i] =>
    pick s!"tuple selector {i}" fun e =>
      e.kind == "selector" && e.descriptions.length == 2 && e.descriptions[1]? == some (index i)
  | .expr [.atom "_", .atom "is", .atom c] =>
    match (t.source c "constructor").bind (·.descriptions.head?) with
    | some id => pick s!"tester of {id}" fun e =>
        e.kind == "tester" && e.descriptions.length == 2 && e.descriptions.head? == some id
    | none => refuse s!"{c} is not a constructor of the sources"
  | .atom a => match t.sources.get? a with
    | some ⟨_, "constructor", id :: _, _⟩ =>
      pick s!"constructor {id}" fun e =>
        e.kind == "constructor" && e.descriptions.length == 2 && e.descriptions.head? == some id
    | some ⟨_, "selector", [id, _, i], _⟩ =>
      pick s!"selector {i} of {id}" fun e =>
        e.kind == "selector" && e.descriptions.length == 3 && e.descriptions.head? == some id &&
          e.descriptions[2]? == some i
    | some ⟨_, "function", id :: _, _⟩ =>
      pick s!"instance of {id}" fun e => e.kind == "function" && e.descriptions.head? == some id
    | some ⟨_, "uninterpreted", id, _⟩ =>
      if t.isMarker a then refuse s!"{a} is no symbol of the sources"
      else t.unique s!"uninterpreted function {" ".intercalate id}" fun e =>
        e.kind == "uninterpreted" && e.descriptions == id
    | _ => refuse s!"{a} is no symbol of the sources"
  | other => refuse s!"{text other} is no symbol of the sources"

def applied (head : Sexp) (args : List Sexp) : Sexp := if args.isEmpty then head else .expr (head :: args)

def cannot {α : Type} (e : Sexp) : Lower α := refuse s!"{text e} can't be lowered"

/-- The lowering of the term `e`, whose bound variables are `bound`. -/
partial def lower (bound : Std.HashSet String) (e : Sexp) : Lower Sexp := do
  match e with
  | .atom a =>
    if isLiteral a || bound.contains a then pure e
    else match t.source a "variable" with
    | some src =>
      match t.sessionNames.get? a with
      | some s =>
        if s.kind != "variable" || s.descriptions != src.descriptions then
          refuse s!"the variable {a} of the sources is {s.kind} {" ".intercalate s.descriptions} in the session"
        pure e
      | none => pure e
    | none => t.symbol e none
  | .expr [.atom "!", x, .atom ":unsigned"] => lower bound x
  | .expr [.atom "!", x, .atom ":signed"] => lower bound x
  | .expr [.atom "!", x, .atom ":char"] => lower bound x
  | _ => match keyed e with
    | some (.atom "emptyset", s, []) => pure (app "as" [.atom "set.empty", app "Set" [← t.lowerSort s]])
    | some (.atom "const", s, [d]) => pure (.expr [app "as" [.atom "const", ← t.lowerSort s], ← lower bound d])
    | some (head, k, args) =>
      match head, args with
      | .atom m, _ =>
        if t.isMarker m then return applied (app "as" [head, k]) (← args.mapM (lower bound))
        if m == "@" then
          match args with
          | .atom f :: rest =>
            if t.predicates.contains f && t.isVariable bound f then
              return .expr (.atom f :: (← rest.mapM (lower bound)))
          | _ => pure ()
          if args.isEmpty then cannot e
          let sort := erase k
          let d ← t.unique s!"application of sort {text sort}" fun s => s.kind == "application" && s.sort == some sort
          return .expr (d :: (← args.mapM (lower bound)))
        pure (applied (← t.symbol head (some (erase k))) (← args.mapM (lower bound)))
      | _, _ => pure (applied (← t.symbol head (some (erase k))) (← args.mapM (lower bound)))
    | none => unkeyed bound e
where
  /-- The lowering of `e`, which is no symbol under a key. -/
  unkeyed (bound : Std.HashSet String) (e : Sexp) : Lower Sexp := do
    match e with
    | .expr [head@(.expr (.atom "_" :: .atom k :: _)), x] =>
      if ["int2bv", "zero_extend", "sign_extend", "extract"].contains k then pure (.expr [head, ← lower bound x])
      else pure (.expr [← t.symbol head none, ← lower bound x])
    | .expr [.atom "let", .expr bs, body] => do
      let bs ← bindings bs
      let values ← bs.mapM fun (x, v) => do pure (Sexp.expr [.atom x, ← lower bound v])
      pure (.expr [.atom "let", .expr values, ← lower (bound.insertMany (bs.map (·.1))) body])
    | .expr [.atom "forall", .expr bs, body] => do
      let bs ← bindings bs
      let lowered ← bs.mapM fun (x, s) => do pure (Sexp.expr [.atom x, ← t.lowerSort s])
      pure (.expr [.atom "forall", .expr lowered, ← lower (bound.insertMany (bs.map (·.1))) body])
    | .expr [.atom "exists", .expr bs, body] => do
      let bs ← bindings bs
      let lowered ← bs.mapM fun (x, s) => do pure (Sexp.expr [.atom x, ← t.lowerSort s])
      let negated := match body with
        | .expr [.atom "not", b] => b
        | b => mkNot b
      pure (mkNot (.expr [.atom "forall", .expr lowered, ← lower (bound.insertMany (bs.map (·.1))) negated]))
    | .expr (.atom "insert" :: (empty@(.expr [.atom "as", .atom "emptyset", _])) :: first :: rest) => do
      if t.ground bound first then
        let singleton := app "set.singleton" [← lower bound first]
        if rest.isEmpty then pure singleton
        else pure (.expr (.atom "set.insert" :: (← rest.mapM (lower bound)) ++ [singleton]))
      else pure (.expr (.atom "set.insert" :: (← (first :: rest).mapM (lower bound)) ++ [← lower bound empty]))
    | .expr [.atom "insert", s, x] => do pure (app "set.insert" [← lower bound x, ← lower bound s])
    | .expr [.atom "error", s, _] => do
      -- an error is an assumption that never holds, of some value of its sort
      match ← t.lowerSort s with
      | .atom "Bool" => pure (app "assume" [ff, ff])
      | .atom "Int" => pure (app "assume" [ff, .atom "0"])
      | other => refuse s!"an error of sort {text other} is not lowered yet"
    | .expr (.atom op :: args) =>
      match setOperations.lookup op with
      | some op' => do pure (app op' (← args.mapM (lower bound)))
      | none =>
        if (op == "assume" && args.length == 2) || same.contains op then do pure (app op (← args.mapM (lower bound)))
        else pure (applied (← t.symbol (.atom op) none) (← args.mapM (lower bound)))
    | .expr (head :: args) => pure (applied (← t.symbol head none) (← args.mapM (lower bound)))
    | other => cannot other

/-- The term `e` where each outermost subterm that `table` names is its name, and the subterms named. -/
partial def named (table : List (Sexp × Sexp)) (e : Sexp) : StateM (List Sexp) Sexp := do
  match table.lookup e with
  | some name => modify (e :: ·); pure name
  | none => match e with
    | .expr items => pure (.expr (← items.mapM (named table)))
    | a => pure a

/-- The instantiated body `body` of a definition, where each uninterpreted function is the one
of its type arguments: each instantiation of an uninterpreted function is a symbol of its own in
the sources, whose entry ends with its type arguments, which are its key. -/
partial def instanceOf (body : Sexp) : Lower Sexp := do
  match body with
  | .expr [.atom "as", .atom u, k] =>
    match t.source u "uninterpreted" with
    | some e =>
      if e.sort.isNone || e.sort == some k then pure body
      else match t.sources.toList.filter (fun (_, o) =>
          o.kind == "uninterpreted" && o.descriptions == e.descriptions && o.sort == some k) with
      | [(_, o)] => pure (.expr [.atom "as", .atom o.name, k])
      | [] => refuse s!"the sources have no instance of the uninterpreted function {u} at {text k}"
      | _ => refuse s!"the sources have several instances of the uninterpreted function {u} at {text k}"
    | none => pure (.expr [.atom "as", .atom u, ← instanceOf k])
  | .expr items => pure (.expr (← items.mapM instanceOf))
  | atom => pure atom

/-- The source of the template of the call `call` of a defined function: the body of the
function's definition at the sorts of its type arguments, which are the key of the call, and at its
arguments, where each outermost subterm that is the right of a pair of `names` is the left of the
pair. Sorts are compared without their refinements. It refuses a name that names no subterm of the
body, and a subterm named twice. The uninterpreted functions of the body are those of its type
arguments (`instanceOf`). -/
def defined (call : Sexp) (names : List (Sexp × Sexp)) : Lower Sexp := do
  let (f, sorts, args) ← match keyed call, call with
    | some (.atom f, .expr sorts, args), _ => pure (f, sorts, args)
    | _, .expr (.atom f :: args) => pure (f, [], args)
    | _, .atom f => pure (f, [], [])
    | _, other => refuse s!"{text other} is not the call of a function"
  let some d := t.definitions.get? f | refuse s!"the function {f} has no definition"
  if d.params.length != sorts.length then
    refuse s!"{text call} has {sorts.length} type arguments, not {d.params.length}"
  if d.arguments.length != args.length then
    refuse s!"{text call} has {args.length} arguments, not {d.arguments.length}"
  let subst := Std.HashMap.ofList (d.params.zip sorts ++ d.arguments.zip args)
  let body ← t.instanceOf (erase (instantiate subst d.body))
  let table := names.map fun (name, original) => (erase original, name)
  if (table.map (·.1)).eraseDups.length != table.length then refuse s!"the names of {text call} name a subterm twice"
  let (source, used) := (named table body).run []
  for (original, _) in table do
    if !used.contains original then refuse s!"the body of {f} has no subterm {text original}"
  pure source

/-- The lowering of the source `s` and of its `where`: a symbol of the template that the left of a
pair names is kept. -/
def lowerSource (s : Source) : Lower Source := do
  let pairs ← s.meanings.mapM fun (l, r) => do
    match l with
    | .atom _ => pure (l, ← t.lower {} r)
    | _ => pure (← t.lower {} l, ← t.lower {} r)
  match s with
  | .function call body _ => pure (.function (← t.lower {} call) (← t.lower {} body) pairs)
  | .definition call names _ => pure (.function (← t.lower {} call) (← t.lower {} (← t.defined call names)) pairs)
  | .expression e _ => pure (.expression (← t.lower {} e) pairs)

/-- `e` where each marker that `meanings` gives a meaning to is replaced by that meaning. -/
partial def unmark (meanings : List (Sexp × Sexp)) (seen : List Sexp) (e : Sexp) : Sexp :=
  match meanings.lookup e with
  | some r => if seen.contains e then e else unmark meanings (e :: seen) r
  | none => match e with
    | .expr items => .expr (items.map (unmark meanings seen))
    | a => a

/-- `e` without its assumptions, `(assume c b)` being `b`, and without the conjuncts that have
markers, of its conjunctions that hold where `e` does. -/
partial def strip (e : Sexp) : Sexp :=
  match e with
  | .expr [.atom "assume", _, b] => strip b
  | .expr (.atom "and" :: cs) =>
    match (cs.map strip).filter (!t.hasMarker ·) with
    | [] => tt
    | [c] => c
    | kept => .expr (.atom "and" :: kept)
  | other => other

/-- What the checker in Lean states of the expression of a lowered source of kind `expression`,
which an instance of `expression` kind asserts: the expression, with the meanings that the source
gives to its markers in place of the markers, without its assumptions, and without the conjuncts
that have markers left; nothing if a marker is left outside of them. This is the expression, or a
weaker one: a model of the source's expression is one of it, given the meanings of the markers,
which only the Scala checker checks against the clauses of the template. -/
def statement : Source → Option Sexp
  | .expression e meanings =>
    let terms := meanings.filter fun (l, _) => match l with | .expr _ => true | _ => false
    let stated := t.strip (unmark terms [] e)
    if t.hasMarker stated then none else some stated
  | _ => none

end Tables

end Inox.Lowering
