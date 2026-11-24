/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Sexp
import Inox.Lowering

/-!
The checker of the certificates that Inox prints for its unsat answers, as the Scala checker
`inox.certificates.Checker` of `proofs` (see `proofs/certificates/README.md`): each assert of the
certificate's script is a clause that a rule of `unrolling.RuleKernel` builds, or an assumption,
and the proof assumes asserts of the script only, as they are. `Inox.Accept` then has Logos check
the proof.

It lowers the source of every template to the syntax of the session (`Inox.Lowering`), and
refuses a certificate with a source that doesn't lower, as the Scala checker does. It doesn't
check that the clauses of a template are those of its source, which the Scala checker does.
-/

namespace Inox

open Logos (Sexp)

abbrev Check := Except String

def fail {α : Type} (msg : String) : Check α := .error msg

/-- The arguments of a rule, by name. -/
structure Arguments where
  kind : String
  byName : List (String × List Sexp)

namespace Arguments

def make (kind : String) (args : List Sexp) : Check Arguments := do
  let byName ← args.mapM fun arg => match arg with
    | .expr (.atom name :: terms) => pure (name, terms)
    | other => fail s!"{text other} is not an argument of a {kind} rule"
  if (byName.map (·.1)).eraseDups.length != byName.length then fail s!"a {kind} rule has an argument twice"
  pure ⟨kind, byName⟩

def has (args : Arguments) (name : String) : Bool := args.byName.any (·.1 == name)

def opt (args : Arguments) (name : String) : Check (Option Sexp) :=
  match args.byName.lookup name with
  | none => pure none
  | some [term] => pure (some term)
  | some terms => fail s!"the argument {name} of a {args.kind} rule has {terms.length} terms"

def one (args : Arguments) (name : String) : Check Sexp := do
  match ← args.opt name with
  | some term => pure term
  | none => fail s!"a {args.kind} rule has no argument {name}"

def several (args : Arguments) (name : String) (size : Option Nat := none) : Check (List Sexp) :=
  match args.byName.lookup name with
  | none => fail s!"a {args.kind} rule has no argument {name}"
  | some terms =>
    if size.all (· == terms.length) then pure terms
    else fail s!"the argument {name} of a {args.kind} rule has {terms.length} terms"

/-- Checks that the rule only has the arguments `names`. -/
def only (args : Arguments) (names : List String) : Check Unit :=
  match args.byName.find? fun arg => !names.contains arg.1 with
  | some arg => fail s!"a {args.kind} rule has no argument {arg.1}"
  | none => pure ()

end Arguments

/-- Checks that `application` applies `symbol` to `args`, where the session may apply it through
a function of its own. -/
def checkApplication (application symbol : Sexp) (args : List Sexp) : Check Unit :=
  let applied := (symbol :: args).map text
  match application with
  | .expr items =>
    if items.map text == applied || (!items.isEmpty && items.tail.map text == applied) then pure ()
    else fail s!"{text application} doesn't apply {text symbol} to its arguments"
  | other => fail s!"{text other} doesn't apply {text symbol} to its arguments"

def guarded (guard : Option Sexp) (e : Sexp) : Sexp :=
  match guard with
  | some g => mkImplies g e
  | none => e

/-- The clauses of the rule of kind `kind` on `args`, for the rules that don't instantiate a
template (see `unrolling.RuleKernel` in Inox). -/
def ruleClauses (kind : String) (args : Arguments) : Check (List Sexp) := do
  match kind with
  | "Define" =>
    args.only ["guard", "literal", "value"]
    pure [guarded (← args.opt "guard") (mkEq (← args.one "literal") (← args.one "value"))]
  | "Enables" =>
    args.only ["blocker", "target"]
    pure [mkImplies (← args.one "blocker") (← args.one "target")]
  | "Hypothesis" =>
    args.only ["literal", "condition", "fact"]
    pure [mkImplies (mkAnd [← args.one "literal", ← args.one "condition"]) (← args.one "fact")]
  | "Root" =>
    args.only ["start"]
    pure [← args.one "start"]
  | "Typed" =>
    args.only ["blocker", "typing"]
    pure [mkImplies (← args.one "blocker") (mkEq (← args.one "typing") tt)]
  | "Holds" =>
    args.only ["blocker", "quantification"]
    pure [mkImplies (← args.one "blocker") (← args.one "quantification")]
  | "Unreachable" =>
    args.only ["literal", "under"]
    pure [guarded (← args.opt "under") (mkNot (← args.one "literal"))]
  | "Decreases" =>
    args.only ["blocker", "decrease", "unless"]
    let decrease ← args.one "decrease"
    let fact := match ← args.opt "unless" with
      | some diverges => mkOr [decrease, diverges]
      | none => decrease
    pure [mkImplies (← args.one "blocker") fact]
  | "Congruence" =>
    args.only ["premises", "result"]
    pure [mkImplies (mkAnd (← args.several "premises")) (← args.one "result")]
  | "Witness" =>
    args.only ["start", "differ", "failures"]
    let differ ← args.one "differ"
    let distinguished ←
      if args.has "failures" then do
        match ← args.several "failures" (some 2) with
        | [err1, err2] => pure (mkOr [mkNot (mkEq err1 err2), mkAnd [mkNot err1, mkNot err2, differ]])
        | _ => fail "a Witness rule has two failures"
      else pure differ
    pure [mkImplies (← args.one "start") distinguished]
  | "Reflexivity" =>
    args.only ["guard", "eq", "terms", "eq12"]
    match ← args.several "terms" (some 2) with
    | [e1, e2] =>
      checkApplication (← args.one "eq12") (← args.one "eq") [e1, e2]
      let condition := match ← args.opt "guard" with
        | some g => mkAnd [g, mkEq e1 e2]
        | none => mkEq e1 e2
      pure [mkImplies condition (← args.one "eq12")]
    | _ => fail "a Reflexivity rule has two terms"
  | "Symmetry" =>
    args.only ["blocker", "eq", "terms", "eq12", "eq21"]
    match ← args.several "terms" (some 2) with
    | [e1, e2] =>
      checkApplication (← args.one "eq12") (← args.one "eq") [e1, e2]
      checkApplication (← args.one "eq21") (← args.one "eq") [e2, e1]
      pure [mkImplies (← args.one "blocker") (mkEq (← args.one "eq12") (← args.one "eq21"))]
    | _ => fail "a Symmetry rule has two terms"
  | "Transitivity" =>
    args.only ["guard", "eq", "terms", "eq12", "eq23", "eq13"]
    match ← args.several "terms" (some 3) with
    | [e1, e2, e3] =>
      checkApplication (← args.one "eq12") (← args.one "eq") [e1, e2]
      checkApplication (← args.one "eq23") (← args.one "eq") [e2, e3]
      checkApplication (← args.one "eq13") (← args.one "eq") [e1, e3]
      pure [mkImplies (mkAnd [← args.one "guard", ← args.one "eq12", ← args.one "eq23"]) (← args.one "eq13")]
    | _ => fail "a Transitivity rule has three terms"
  | "Dispatched" =>
    args.only ["blocker", "rest"]
    pure [mkImplies (mkNot (← args.one "rest")) (mkNot (← args.one "blocker"))]
  | "DispatchFailure" =>
    args.only ["enabler", "application", "body"]
    pure [mkImplies (← args.one "enabler") (mkEq (← args.one "application") (← args.one "body"))]
  | "SameLambda" =>
    args.only ["start", "lambda", "representative"]
    pure [mkImplies (← args.one "start") (mkEq (← args.one "lambda") (← args.one "representative"))]
  | "LambdaEquality" =>
    args.only ["blocker", "lambdas", "closures", "intensional"]
    match ← args.several "lambdas" (some 2) with
    | [lambda1, lambda2] =>
      let equals := mkEq lambda1 lambda2
      let blocker ← args.one "blocker"
      match ← args.opt "closures", args.has "intensional" with
      | some eqs, true => pure [mkImplies blocker (mkEq eqs equals)]
      | none, true => pure [mkImplies blocker (mkNot equals)]
      | some eqs, false => pure [mkImplies (mkAnd [blocker, eqs]) equals]
      | none, false => pure []
    | _ => fail "a LambdaEquality rule has two lambdas"
  | other => fail s!"{other} is not a kind of rule"

/-- What a certificate has, once checked. -/
structure Checked where
  asserts : Nat
  rules : Nat
  instances : Nat
  assumptions : Nat
  templates : Nat
  /-- the source of each template, lowered to the syntax of the session -/
  lowered : Array Lowering.Source
  /-- cvc5's proof, in the CPC of Logos -/
  cpc : List Sexp

/-- The text of the proof of a certificate, for a CPC checker. -/
def Checked.proof (c : Checked) : String := "\n".intercalate (c.cpc.map text) ++ "\n"

def assertsOf (script : List Sexp) : Array Sexp :=
  (script.filterMap fun command => match command with
    | .expr [.atom "assert", t] => some t
    | _ => none).toArray

def index (e : Sexp) (bound : Nat) (what : String) : Check Nat :=
  match e with
  | .atom a =>
    match if !a.isEmpty && a.all Char.isDigit then a.toNat? else none with
    | some n => if n < bound then pure n else fail s!"{a} is not the index of an assert of {what}"
    | none => fail s!"{a} is not the index of an assert of {what}"
  | other => fail s!"{text other} is not the index of an assert of {what}"

def isAtom : Sexp → Bool
  | .atom _ => true
  | _ => false

/-- A template: its parameters, and its clauses. -/
abbrev Template := List Sexp × List Sexp

/-- The state of the check of the rules: the asserts that a rule or an assumption names, the
symbols that the rules introduce, each with the kind of the rule that does, and the number of
instances of templates. -/
structure Rules where
  named : Array Bool
  introduced : Std.HashMap String String := {}
  instances : Nat := 0

def Rules.introduce (state : Rules) (symbol : Sexp) (kind : String) : Check Rules :=
  match symbol with
  | .atom a =>
    match state.introduced.get? a with
    | some other => fail s!"{a} is introduced by both a {other} and a {kind} rule"
    | none => pure { state with introduced := state.introduced.insert a kind }
  | other => fail s!"{text other}, which a {kind} rule introduces, is not a symbol"

/-- Checks that the asserts that the rule `line` names are its clauses. -/
def checkRule (clauses : Array Sexp) (templates : Array Template) (state : Rules) (line : Sexp) : Check Rules := do
  match line with
  | .expr (.atom kind :: .expr (.atom "args" :: args) :: rest) =>
    let arguments ← Arguments.make kind args
    let (instance?, indices) := match rest with
      | .expr [.atom "instance", template, .expr values] :: indices => (some (template, values), indices)
      | indices => (none, indices)
    let is ← indices.mapM (index · clauses.size "the script")
    if is.isEmpty then fail s!"a {kind} rule names no assert"
    let state := { state with named := is.foldl (fun named i => named.set! i true) state.named }
    let isInstance := kind == "Unfold" || kind == "Instance"
    match instance? with
    | some (template, values) =>
      if !isInstance then fail s!"a {kind} rule has an instance"
      if kind == "Unfold" then arguments.only ["blocker", "failure"]
      else
        arguments.only ["expression", "axiom", "counterexample"]
        if (["expression", "axiom", "counterexample"].filter arguments.has).length != 1 then
          fail "an Instance rule is of one kind"
      let (params, body) := templates[← index template templates.size "the templates"]!
      let pairs ← values.mapM fun value => match value with
        | .expr [symbol, value] => pure (symbol, value)
        | other => fail s!"{text other} is not the value of a symbol"
      if (pairs.map (text ·.1)).eraseDups.length != pairs.length then fail "an instance gives a symbol two values"
      if (pairs.map (text ·.1)).take params.length != params.map text then
        fail "an instance doesn't give the values of its template's parameters first"
      -- the template's other symbols are replaced by symbols of the instance
      match (pairs.drop params.length).find? fun pair => !isAtom pair.1 || !isAtom pair.2 with
      | some (symbol, value) => fail s!"{text symbol} is replaced by {text value}, and they are not both symbols"
      | none => pure ()
      -- a parameter is a symbol, or a term that the template has as it is
      let values : Std.HashMap String Sexp := Std.HashMap.ofList (pairs.filterMap fun pair => match pair.1 with
        | .atom symbol => some (symbol, pair.2)
        | _ => none)
      let terms := pairs.filterMap fun pair => if isAtom pair.1 then none else some (text pair.1, pair.2)
      let instantiated : Std.HashSet String :=
        Std.HashSet.ofList (body.map fun clause => text (testers (simplified (substitute values terms clause))))
      for i in is do
        if !instantiated.contains (text (testers clauses[i]!)) then
          fail s!"assert {i}, {text clauses[i]!}, is not a clause of the instance that a {kind} rule names"
      pure { state with instances := state.instances + 1 }
    | none =>
      if isInstance then fail s!"a {kind} rule has no instance"
      let expected := (← ruleClauses kind arguments).map fun clause => text (testers clause)
      for i in is do
        if !expected.contains (text (testers clauses[i]!)) then
          fail s!"assert {i}, {text clauses[i]!}, is not a clause of the {kind} rule that names it"
      match kind with
      | "Define" | "Hypothesis" => state.introduce (← arguments.one "literal") kind
      | "Root" => state.introduce (← arguments.one "start") kind
      | _ => pure state
  | other => fail s!"{text other} is not a rule"

/-- The version of the format that the checker checks. -/
def version : String := "4"

/-- Checks `certificate`, and says why when it doesn't hold. -/
def check (certificate : Sexp) : Check Checked := do
  match certificate with
  | .expr [.atom "inox-certificate", .atom v,
      .expr (.atom "script" :: script),
      .expr (.atom "templates" :: .expr (.atom "script" :: templateScript) :: templateLines),
      .expr (.atom "rules" :: ruleLines),
      .expr [.atom "assumptions", .expr (.atom "query" :: query), .expr (.atom "complete" :: complete)],
      .expr (.atom "solver-symbols" :: solverSymbols),
      .expr (.atom "source-definitions" :: sourceDefinitions),
      .expr (.atom "source-symbols" :: sourceSymbols),
      .expr (.atom "cpc" :: cpc)] =>
    if v != version then fail s!"the certificate has version {v}, and the checker checks version {version}"
    let clauses := assertsOf script
    let templateClauses := assertsOf templateScript

    let tables ← Lowering.Tables.make (script ++ templateScript) solverSymbols sourceDefinitions sourceSymbols
    let mut templates : Array Template := #[]
    let mut lowered : Array Lowering.Source := #[]
    for line in templateLines do
      match line with
      | .expr (.atom i :: .expr (.atom "params" :: params) :: rest) =>
        if i != toString templates.size then fail s!"{text line} is not template {templates.size}"
        if (params.map text).eraseDups.length != params.length then fail s!"template {i} has a parameter twice"
        let (source, indices) ← match rest with
          | s :: indices => match Lowering.Source.ofSexp s with
            | some source => pure (source, indices)
            | none => fail s!"template {i} has no source"
          | [] => fail s!"template {i} has no source"
        match tables.lowerSource source with
        | .ok source => lowered := lowered.push source
        | .error why => fail s!"the source of template {i} can't be lowered: {why}"
        let body ← indices.mapM fun i => do
          pure templateClauses[← index i templateClauses.size "the templates"]!
        templates := templates.push (params, body)
      | other => fail s!"{text other} is not template {templates.size}"

    let mut state : Rules := { named := Array.replicate clauses.size false }
    for line in ruleLines do
      state ← checkRule clauses templates state line

    let queryIndices ← query.mapM (index · clauses.size "the script")
    let completeIndices ← complete.mapM (index · clauses.size "the script")
    let mut named := state.named
    for i in queryIndices ++ completeIndices do
      if named[i]! then fail s!"assert {i} is both an assumption and the clause of a rule, or an assumption twice"
      named := named.set! i true
    for i in completeIndices do
      match clauses[i]! with
      | .atom _ | .expr [.atom "not", .atom _] => pure ()
      | other => fail s!"the assumption {text other} doesn't state that an open conjunction or disjunction is complete"
    for i in [0:clauses.size] do
      if !named[i]! then fail s!"assert {i}, {text clauses[i]!}, is the clause of no rule and no assumption"

    -- the proof refutes the script, where its definitions name terms: each of its assumptions is
    -- an assert of the script as it is, up to how cvc5 prints testers
    let asserted : Std.HashSet String := Std.HashSet.ofList (clauses.toList.map fun clause => text (testers clause))
    let mut definitions : Std.HashMap String Sexp := {}
    for step in cpc do
      match step with
      | .expr [.atom "define", .atom name, .expr [], term] =>
        definitions := definitions.insert name (substitute definitions [] term)
      | .expr [.atom "assume", _, formula] =>
        let assumed := substitute definitions [] formula
        if !asserted.contains (text (testers assumed)) then
          fail s!"the proof assumes {text assumed}, which the script doesn't assert"
      | _ => pure ()

    pure {
      asserts := clauses.size, rules := ruleLines.length, instances := state.instances,
      assumptions := queryIndices.length + completeIndices.length, templates := templates.size, lowered, cpc := cpc }
  | .expr (.atom "inox-certificate" :: .atom v :: _) =>
    if v != version then fail s!"the certificate has version {v}, and the checker checks version {version}"
    else fail "this is not a certificate"
  | _ => fail "this is not a certificate"

end Inox
