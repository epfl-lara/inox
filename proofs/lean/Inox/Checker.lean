/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Sexp
import Inox.Lowering
import Inox.Encoders
import Inox.Meanings

/-!
The checker of the certificates that Inox prints for its unsat answers, as the Scala checker
`inox.certificates.Checker` of `proofs` (see `proofs/certificates/README.md`): each assert of the
certificate's script is a clause that a rule of `unrolling.RuleKernel` builds, or an assumption,
and the proof assumes asserts of the script only, as they are. `Inox.Accept` then has Logos check
the proof.

It lowers the source of every template to the syntax of the session (`Inox.Lowering`), and
refuses a certificate with a source that doesn't lower, as the Scala checker does. It doesn't
check that the clauses of a template are those of its source, which the Scala checker does; it
keeps the defining equations of the functions, for `Inox/Unfold.lean`.
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
  /-- the script of the clauses -/
  script : List Sexp
  /-- each rule's kind and clauses, in the order of the rules, as cvc5 prints testers -/
  applied : List (String × List Sexp)
  /-- the asserts that are assumptions of the query, as cvc5 prints testers -/
  query : List Sexp
  /-- the asserts that are assumptions of completeness, as cvc5 prints testers -/
  complete : List Sexp
  /-- the commands of the script of the templates -/
  templateScript : List Sexp := []
  /-- the defining equation `(= call body)` of each template whose source is a function -/
  sources : List Sexp := []
  /-- for each rule, in the order of `applied`, the definitions `(symbol, meaning)` of the local
  symbols of its instance (`Inox/Meanings.lean`), when it is the instance of a template -/
  defined : List (List (Sexp × Sexp)) := []
  /-- the source `t` of each instance of a template whose source is an expression `(expression t)`,
  that an `Instance` rule of kind `expression` names, with the instance's values for its symbols -/
  expressions : List Sexp := []

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
  applied : Array (String × List Sexp) := #[]
  /-- the definitions of the local symbols of each rule's instance, as `applied` -/
  defined : Array (List (Sexp × Sexp)) := #[]
  /-- the meanings of the local symbols of the templates, by template -/
  meanings : Std.HashMap Nat (List (String × Sexp)) := {}
  /-- the source expressions of the instances of `expression` kind, instantiated -/
  expressions : Array Sexp := #[]

def Rules.introduce (state : Rules) (symbol : Sexp) (kind : String) : Check Rules :=
  match symbol with
  | .atom a =>
    match state.introduced.get? a with
    | some other => fail s!"{a} is introduced by both a {other} and a {kind} rule"
    | none => pure { state with introduced := state.introduced.insert a kind }
  | other => fail s!"{text other}, which a {kind} rule introduces, is not a symbol"

/-- Checks that the asserts that the rule `line` names are its clauses. -/
def checkRule (clauses : Array Sexp) (templates : Array Template) (sources : Array (Option Sexp))
    (given : Array (List (String × Sexp) × Option Sexp)) (state : Rules) (line : Sexp) :
    Check Rules := do
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
      let ti ← index template templates.size "the templates"
      let (params, body) := templates[ti]!
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
      let instClauses := body.map fun clause => testers (simplified (substitute values terms clause))
      let instantiated : Std.HashSet String := Std.HashSet.ofList (instClauses.map text)
      for i in is do
        if !instantiated.contains (text (testers clauses[i]!)) then
          fail s!"assert {i}, {text clauses[i]!}, is not a clause of the instance that a {kind} rule names"
      let applied := state.applied.push (kind, instClauses)
      -- the definitions of the instance's local symbols, which nothing relies on
      let ms := match state.meanings.get? ti with
        | some ms => ms
        | none =>
          let (symbols, call) := given[ti]?.getD ([], none)
          Meanings.meanings params ((pairs.drop params.length).filterMap fun pair =>
            match pair.1 with
            | .atom a => some a
            | _ => none) body symbols call
      let defs := ms.map fun (v, m) =>
        (testers (substitute values terms (.atom v)), testers (substitute values terms m))
      -- the source expression of the instance, which the query asserts
      let expressions := match sources[ti]?.join with
        | some t => if kind == "Instance" && arguments.has "expression" then
            state.expressions.push (testers (substitute values terms t)) else state.expressions
        | none => state.expressions
      pure { state with instances := state.instances + 1, applied := applied, expressions,
                        defined := state.defined.push defs,
                        meanings := state.meanings.insert ti ms }
    | none =>
      if isInstance then fail s!"a {kind} rule has no instance"
      let built := (← ruleClauses kind arguments).map testers
      let expected := built.map text
      let state := { state with applied := state.applied.push (kind, built),
                                defined := state.defined.push [] }
      for i in is do
        if !expected.contains (text (testers clauses[i]!)) then
          fail s!"assert {i}, {text clauses[i]!}, is not a clause of the {kind} rule that names it"
      match kind with
      | "Define" | "Hypothesis" => state.introduce (← arguments.one "literal") kind
      | "Root" => state.introduce (← arguments.one "start") kind
      | _ => pure state
  | other => fail s!"{text other} is not a rule"

/-- The version of the format that the checker checks. -/
def version : String := "5"

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
      -- The simplification steps relate the sources to the original program. The Scala checker
      -- replays them; this checker doesn't yet, so its result holds over the simplified program.
      .expr (.atom "simplifications" :: _),
      .expr (.atom "input" :: input),
      .expr (.atom "cpc" :: cpc)] =>
    if v != version then fail s!"the certificate has version {v}, and the checker checks version {version}"
    -- the constraints of the input are encoded as the certificate states
    let _ ← Encoders.check input sourceSymbols
    let clauses := assertsOf script
    let templateClauses := assertsOf templateScript

    let tables ← Lowering.Tables.make (script ++ templateScript) solverSymbols sourceDefinitions sourceSymbols
    let mut templates : Array Template := #[]
    let mut lowered : Array Lowering.Source := #[]
    let mut sources : Array Sexp := #[]
    let mut expressions : Array (Option Sexp) := #[]
    let mut given : Array (List (String × Sexp) × Option Sexp) := #[]
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
        let definition := match source with
          | .definition call (_ :: _) _ => (tables.defined call [] >>= tables.lower {}).toOption
          | _ => none
        match tables.lowerSource source with
        | .ok source =>
          lowered := lowered.push source
          -- the meanings that the source gives of the template's symbols (`Inox/Meanings.lean`)
          let terms := source.meanings.filter fun (l, _) => match l with
            | .expr _ => true
            | _ => false
          -- the typing of a set is true, of an element of it and of the others
          let sets := source.meanings.filterMap Meanings.setTyping
          let terms := sets.flatMap (·.1) ++ terms
          -- those with markers left, such as the typing of a value, the clauses can't state
          let symbols := sets.flatMap (·.2) ++ source.meanings.filterMap fun (l, r) => match l with
            | .atom v =>
              let m := Meanings.collapse (Lowering.Tables.unmark terms [] r)
              if tables.hasMarker m then none else some (v, m)
            | _ => none
          given := given.push (symbols, match source with
            | .function call _ _ => some call
            | _ => none)
          -- the defining equation of a function is kept for the check of the rules on terms
          -- (`Inox/Unfold.lean`), unless it has markers, which Logos can't read; that of a defined
          -- function whose source names subterms of its body is also kept with the body of its
          -- definition, when that lowers. So is an expression, which the instances of `expression`
          -- kind state of the query (`Inox/Terms.lean`), as `Lowering.Tables.statement` states it
          match source with
          | .function call body _ =>
            for body in [body] ++ (definition.filter (· != body)).toList do
              if !tables.hasMarker call && !tables.hasMarker body then
                sources := sources.push (testers (.expr [.atom "=", call, body]))
            expressions := expressions.push none
          | _ => expressions := expressions.push (tables.statement source)
        | .error why => fail s!"the source of template {i} can't be lowered: {why}"
        let body ← indices.mapM fun i => do
          pure templateClauses[← index i templateClauses.size "the templates"]!
        templates := templates.push (params, body)
      | other => fail s!"{text other} is not template {templates.size}"

    let mut state : Rules := { named := Array.replicate clauses.size false }
    for line in ruleLines do
      state ← checkRule clauses templates expressions given state line

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
    -- an assert of the script as it is, up to how cvc5 prints testers, and where the solver may
    -- have inlined the bindings of both
    let asserted : Std.HashSet String := Std.HashSet.ofList (clauses.toList.flatMap fun clause =>
      [text (testers clause), text (testers (inlined clause))])
    let mut definitions : Std.HashMap String Sexp := {}
    for step in cpc do
      match step with
      | .expr [.atom "define", .atom name, .expr [], term] =>
        definitions := definitions.insert name (substitute definitions [] term)
      | .expr [.atom "assume", _, formula] =>
        let assumed := substitute definitions [] formula
        if !asserted.contains (text (testers assumed)) && !asserted.contains (text (testers (inlined assumed))) then
          fail s!"the proof assumes {text assumed}, which the script doesn't assert"
      | _ => pure ()

    -- the definitions of local symbols: those of symbols that a rule introduces, or that an
    -- `Enables` rule enables, are left out, and so is a second one of a symbol
    let enabled : Std.HashSet String :=
      Std.HashSet.ofList (state.applied.toList.flatMap fun (kind, cs) =>
      if kind == "Enables" then cs.filterMap fun c => match c with
        | .expr [.atom "=>", _, target] => some (text target)
        | _ => none
      else [])
    let mut seen : Std.HashSet String := {}
    let mut defined : Array (List (Sexp × Sexp)) := #[]
    for defs in state.defined do
      let mut kept : Array (Sexp × Sexp) := #[]
      for (v, m) in defs do
        let name := text v
        if !seen.contains name && !state.introduced.contains name && !enabled.contains name then
          seen := seen.insert name
          kept := kept.push (v, m)
      defined := defined.push kept.toList

    pure {
      asserts := clauses.size, rules := ruleLines.length, instances := state.instances,
      assumptions := queryIndices.length + completeIndices.length, templates := templates.size,
      lowered, cpc := cpc,
      script := script, applied := state.applied.toList,
      query := queryIndices.map fun i => testers clauses[i]!,
      complete := completeIndices.map fun i => testers clauses[i]!,
      templateScript := templateScript, sources := sources.toList, defined := defined.toList,
      expressions := state.expressions.toList }
  | .expr (.atom "inox-certificate" :: .atom v :: _) =>
    if v != version then fail s!"the certificate has version {v}, and the checker checks version {version}"
    else fail "this is not a certificate"
  | _ => fail "this is not a certificate"

end Inox
