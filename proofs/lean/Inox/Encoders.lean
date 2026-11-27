/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Sexp
import Inox.Lowering

/-!
The check of the input of a certificate: that each of its constraints is encoded as the
certificate states, by the encoders that it names. It is the port of
`inox.certificates.Encoders` of the Scala checker.

The input and the encoded terms are terms of Inox's SMT-LIB 3 syntax, the first over the symbols
of the input and the second over those of the sources. An encoder rewrites the terms of its
theory and leaves the others as they are, so the check goes through both terms at once: they have
the same shape, a symbol of the input facing the symbol of the sources that stands for the same
identifier, except where the input has a term of an encoder's theory, which faces what the encoder
makes of it. The sorts that an encoded term has and the input doesn't are not checked here.

The check knows the encoders `propositions`, which changes no term, `bags` and `map-merge`. With
`bags`, the sort `(Bag T)` is the datatype `Bag` of the encoder at `T`, and

    (as bag.empty T)            is  Leaf
    (bag.insert b e)            is  (Node 0 b (Elem e 1))
    (bag.union a b)             is  (Node 0 a b)
    (bag.difference a b)        is  (Node 1 a b)
    (bag.intersection a b)      is  (Node 2 a b)
    (bag.multiplicity e b)      is  (get b e)
    (bag.singleton k v)         is  (ite false Leaf (Node 0 Leaf <elem>))

where `<elem>` is `(Elem k v)` when `v` is a positive literal, `Leaf` when it is another literal,
and `(ite (> v 0) (Elem k v) Leaf)` otherwise. With `map-merge`, `(map.merge mask m1 m2)` is the
call of the encoder's `mapMerge`. The symbols of an encoder are those of the sources that stand
for an identifier of its name that the input doesn't have, and the source definitions of the
datatype `Bag` and of its functions `get` and `inv` must be those of the encoder.

Each constraint also gives the steps of the solver's simplification of the encoded term, the rule
of each and the term after it, which lead to the source of the template of the constraint. The
check reads them, and doesn't check them yet. Each function of the source definitions comes with
its body after the encoders, which is what the encoders make of its definition in the input, and
the steps of its simplification, the last of which is the body of its source definition.
-/

namespace Inox.Encoders

open Logos (Sexp)
open Inox.Lowering (Lower refuse Entry entry)

def known : List String := ["propositions", "bags", "map-merge"]

/-- The text of a string literal. -/
def unquote (d : String) : Option String :=
  if d.startsWith "\"" && d.endsWith "\"" && d.length ≥ 2
  then some (String.ofList (d.toList.drop 1).dropLast) else none

/-- The identifier `name$id` that a symbol is described with: a sort is described with a type
`name$id[..]` of its datatype. -/
def Entry.id (e : Entry) : Option String :=
  e.descriptions.head?.map fun d =>
    String.ofList (((unquote d).getD d).toList.takeWhile (· != '['))

/-- What a symbol stands for, whatever the types: its kind and its identifier, and for a selector
the index of its field. -/
def Entry.identifier (e : Entry) : String × Option String × Option String :=
  (e.kind, Entry.id e, if e.kind == "selector" then e.descriptions.getLast? else none)

/-- The name of an identifier `name$id`. -/
def nameOf (t : String) : String :=
  let cs := t.toList.reverse
  if cs.contains '$' then String.ofList (cs.dropWhile (· != '$')).tail.reverse else t

/-- A sort of the theories, which both sides name alike and only one table may have. -/
def Entry.builtin (e : Entry) : Bool :=
  e.kind == "sort" && (Entry.id e).any fun d => !d.toList.contains '$'

/-- The input and the sources of a certificate, and the encoders between them. -/
structure Relation where
  encoders : List String
  inputs : List Entry
  outputs : List Entry

namespace Relation

def input (r : Relation) (a : String) : Option Entry := r.inputs.find? (·.name == a)
def output (r : Relation) (a : String) : Option Entry := r.outputs.find? (·.name == a)

/-- `a` is the symbol of an encoder: one of the sources of kind `kind` that stands for an
identifier of name `name` that the input doesn't have. -/
def theory (r : Relation) (a : Sexp) (kind name : String) : Bool :=
  match a with
  | .atom a => (r.output a).any fun e => e.kind == kind && (Entry.id e).any fun d =>
      nameOf d == name && !r.inputs.any fun i => i.kind == kind && Entry.id i == some d
  | _ => false

/-- `out` is `(as c S)` for the constructor `name` of the encoder of bags, and `S` is its
datatype. -/
def bagConstructor (r : Relation) (out : Sexp) (name : String) : Bool :=
  match out with
  | .expr [.atom "as", c, .expr [b, _]] => r.theory c "constructor" name && r.theory b "sort" "Bag"
  | _ => false

def node (r : Relation) (out : Sexp) : Option (Sexp × Sexp × Sexp) :=
  match out with
  | .expr [head, op, a, b] => if r.bagConstructor head "Node" then some (op, a, b) else none
  | _ => none

def isInt : Sexp → Option Int
  | .atom t => if t.isNat then some t.toNat! else none
  | .expr [.atom "-", .atom t] => if t.isNat then some (-(t.toNat! : Int)) else none
  | _ => none

def no {α : Type} (i o : Sexp) : Lower α :=
  refuse s!"{text o} is not what the encoders make of {text i}"

def bagOps : List String :=
  ["bag.empty", "bag.insert", "bag.union", "bag.difference", "bag.intersection",
   "bag.multiplicity", "bag.singleton"]

def binders : List String := ["forall", "exists", "lambda", "choose"]

/-- Checks that `o` is what the encoders make of `i`, where the variables that `i` binds face
those that `bound` gives. -/
partial def relate (r : Relation) (i o : Sexp) (bound : List (String × String)) : Lower Unit :=
  let bags := r.encoders.contains "bags"
  let all (xs ys : List Sexp) : Lower Unit :=
    if xs.length != ys.length then no i o
    else (xs.zip ys).forM fun (x, y) => r.relate x y bound
  let isElem (k v e : Sexp) : Lower Unit :=
    match e with
    | .expr [head, k2, v2] =>
      if r.bagConstructor head "Elem" then do r.relate k k2 bound; r.relate v v2 bound else no i o
    | _ => no i o
  match i, o with
  | .atom a, .atom b =>
    match bound.lookup a with
    | some b' => if b' == b then pure () else no i o
    | none =>
      match r.input a, r.output b with
      | some x, some y => if Entry.identifier x == Entry.identifier y then pure () else no i o
      | none, none => if a == b then pure () else no i o
      | some x, none => if a == b && Entry.builtin x then pure () else no i o
      | none, some y => if a == b && Entry.builtin y then pure () else no i o
  | .expr (.atom h :: args), .expr outs =>
    if bags && h == "Bag" then
      match args, outs with
      | [t], [b, t2] => if r.theory b "sort" "Bag" then r.relate t t2 bound else no i o
      | _, _ => no i o
    else if bags && h == "as" && args.head? == some (.atom "bag.empty") then
      match args, outs with
      | [_, t], [.atom "as", _, .expr [_, t2]] =>
        if r.bagConstructor o "Leaf" then r.relate t t2 bound else no i o
      | _, _ => no i o
    else if bags && h == "bag.insert" then
      match args, r.node o with
      | [b, e], some (.atom "0", b2, .expr [head, e2, .atom "1"]) =>
        if r.bagConstructor head "Elem" then do r.relate b b2 bound; r.relate e e2 bound
        else no i o
      | _, _ => no i o
    else if bags && (h == "bag.union" || h == "bag.difference" || h == "bag.intersection") then
      let code := if h == "bag.union" then "0" else if h == "bag.difference" then "1" else "2"
      match args, r.node o with
      | [a, b], some (.atom c, a2, b2) =>
        if c == code then do r.relate a a2 bound; r.relate b b2 bound else no i o
      | _, _ => no i o
    else if bags && h == "bag.multiplicity" then
      match args, outs with
      | [e, b], [.expr [.atom "as", g, .expr [_]], b2, e2] =>
        if r.theory g "function" "get" then do r.relate b b2 bound; r.relate e e2 bound
        else no i o
      | _, _ => no i o
    else if bags && h == "bag.singleton" then
      match args, outs with
      | [k, v], [.atom "ite", .atom "false", leaf, sum] =>
        match r.bagConstructor leaf "Leaf", r.node sum with
        | true, some (.atom "0", leaf2, e) =>
          if !r.bagConstructor leaf2 "Leaf" then no i o
          else match isInt v with
            | some n => if n > 0 then isElem k v e
              else if r.bagConstructor e "Leaf" then pure () else no i o
            | none =>
              match e with
              | .expr [.atom "ite", .expr [.atom ">", v2, .atom "0"], e', leaf3] =>
                if r.bagConstructor leaf3 "Leaf" then do r.relate v v2 bound; isElem k v e'
                else no i o
              | _ => no i o
        | _, _ => no i o
      | _, _ => no i o
    else if bags && bagOps.contains h then no i o
    else if r.encoders.contains "map-merge" && h == "map.merge" then
      match args, outs with
      | [mask, m1, m2], [.expr [.atom "as", f, .expr [_, _]], mask2, n1, n2] =>
        if r.theory f "function" "mapMerge" then do
          r.relate mask mask2 bound; r.relate m1 n1 bound; r.relate m2 n2 bound
        else no i o
      | _, _ => all (.atom h :: args) outs
    else if binders.contains h || h == "let" then
      match args, outs with
      | [.expr xs, body], [.atom h2, .expr ys, body2] =>
        if h != h2 || xs.length != ys.length then no i o
        else do
          let pairs ← (xs.zip ys).mapM fun p =>
            match p with
            | (.expr [.atom x, s], .expr [.atom y, s2]) => do r.relate s s2 bound; pure (x, y)
            | _ => no i o
          r.relate body body2 (pairs ++ bound)
      | _, _ => all (.atom h :: args) outs
    else all (.atom h :: args) outs
  | .expr xs, .expr ys => all xs ys
  | _, _ => no i o

end Relation

def pattern (text : String) : Sexp :=
  match Sexp.Parser.sexp.run text with
  | .ok s => s
  | .error _ => .atom "?"

/-! The definitions of the encoder of bags (see `solvers.theories.BagEncoder`), as the sources
print them: each `?x` stands for a symbol, the same wherever it occurs. Those of a name of the
encoder (`?Bag`, `?Node`, `?op` ..) are its symbols, and the others are bound variables. -/

def bagDatatype : Sexp := pattern ("(par (?T) ((?Node (?op Int) (?left (?Bag ?T)) " ++
  "(?right (?Bag ?T))) (?Elem (?key ?T) (?value Int)) (?Leaf)))")

/-- The sort parameters, the parameters, the sort and the body of `get`. -/
def bagGet : Sexp := pattern ("((?T) ((?b (?Bag ?T)) (?x ?T)) Int " ++
  "(ite ((as (_ is ?Node) (?Bag ?T)) ?b) " ++
  "(let ((?v1 ((as ?get (?T)) ((as ?left (?Bag ?T)) ?b) ?x))) " ++
  "(let ((?v2 ((as ?get (?T)) ((as ?right (?Bag ?T)) ?b) ?x))) " ++
  "(ite (= ((as ?op (?Bag ?T)) ?b) 0) (+ ?v1 ?v2) " ++
  "(ite (= ((as ?op (?Bag ?T)) ?b) 1) (ite (<= ?v1 ?v2) 0 (- ?v1 ?v2)) " ++
  "(ite (<= ?v1 ?v2) ?v1 ?v2))))) " ++
  "(ite (and ((as (_ is ?Elem) (?Bag ?T)) ?b) (= ((as ?key (?Bag ?T)) ?b) ?x)) " ++
  "((as ?value (?Bag ?T)) ?b) 0)))")

/-- The invariant of the datatype: multiplicities are not negative. -/
def bagInvariant : Sexp := pattern ("((?T) ((?b (?Bag ?T))) Bool " ++
  "(or (not ((as (_ is ?Elem) (?Bag ?T)) ?b)) (>= ((as ?value (?Bag ?T)) ?b) 0)))")

/-- A function that commands of SMT-LIB 3 define: its sort parameters, its parameters, its sort
and its body. -/
structure Function where
  params : List Sexp
  args : List Sexp
  range : Sexp
  body : Sexp

/-- The functions that `commands`, declarations and definitions of SMT-LIB 3, define. -/
def functions (commands : List Sexp) : List (String × Function) :=
  let signature : Sexp → Option (String × List Sexp × List Sexp × Sexp)
    | .expr [.atom "par", .expr ps, .expr [.atom f, .expr xs, range]] => some (f, ps, xs, range)
    | .expr [.atom f, .expr xs, range] => some (f, [], xs, range)
    | _ => none
  commands.flatMap fun c =>
    match c with
    | .expr [.atom "define-fun", .atom f, .expr xs, range, body]
    | .expr [.atom "define-fun-rec", .atom f, .expr xs, range, body] =>
      [(f, ⟨[], xs, range, body⟩)]
    | .expr [.atom "define-fun", .expr [.atom "par", .expr ps, .expr [.atom f, .expr xs, r, b]]]
    | .expr [.atom "define-fun-rec",
        .expr [.atom "par", .expr ps, .expr [.atom f, .expr xs, r, b]]] =>
      [(f, ⟨ps, xs, r, b⟩)]
    | .expr [.atom "define-funs-rec", .expr decs, .expr bodies] =>
      (decs.zip bodies).filterMap fun (d, body) =>
        (signature d).map fun (f, ps, xs, range) => (f, ⟨ps, xs, range, body⟩)
    | _ => []

/-- The datatypes that `commands` declare: each sort with its sort parameters and
constructors. -/
def datatypes (commands : List Sexp) : List (String × Sexp) :=
  commands.flatMap fun c =>
    match c with
    | .expr [.atom "declare-datatypes", .expr sorts, .expr decls] =>
      if sorts.length != decls.length then []
      else (sorts.zip decls).filterMap fun (s, decl) =>
        match s with
        | .expr [.atom d, _] => some (d, decl)
        | _ => none
    | _ => []

namespace Relation

/-- The symbol of the input among `ins` that stands for the identifier that `a`, a symbol of the
sources, stands for. -/
def inputOf (r : Relation) (a : String) (ins : List String) : Option String :=
  (r.output a).bind fun y => ins.find? fun b =>
    (r.input b).any fun x => Entry.identifier x == Entry.identifier y

/-- The symbol of the sources among `outs` that stands for the identifier that `a`, a symbol of
the input, stands for. -/
def sourceOf (r : Relation) (a : String) (outs : List String) : Option String :=
  (r.input a).bind fun x => outs.find? fun b =>
    (r.output b).any fun y => Entry.identifier x == Entry.identifier y

/-- `a` is the selector of index `index` of the constructor `name` of an encoder: a selector of
the sources, described by a constructor of that name that the input doesn't have. -/
def selector (r : Relation) (a : String) (name : String) (index : Nat) : Bool :=
  (r.output a).any fun e =>
    e.kind == "selector" && e.descriptions.getLast? == some s!"\"{index}\"" &&
      (Entry.id e).any fun d =>
        nameOf d == name && !r.inputs.any fun i => i.kind == "constructor" && Entry.id i == some d

/-- The symbol of the encoder of bags that `x`, a name of its definitions, stands for. -/
def bagSymbol (r : Relation) (x a : String) : Option Bool :=
  match x with
  | "Bag" => some (r.theory (.atom a) "sort" "Bag")
  | "Node" | "Elem" | "Leaf" => some (r.theory (.atom a) "constructor" x)
  | "op" => some (r.selector a "Node" 0)
  | "left" => some (r.selector a "Node" 1)
  | "right" => some (r.selector a "Node" 2)
  | "key" => some (r.selector a "Elem" 0)
  | "value" => some (r.selector a "Elem" 1)
  | "get" => some (r.theory (.atom a) "function" "get")
  | _ => none

/-- `t` is `p` where each `?x` of `p` is the atom that `binding` gives it, extended. -/
partial def matchPattern (p t : Sexp) (binding : List (String × String)) :
    Option (List (String × String)) :=
  match p, t with
  | .atom x, .atom a =>
    if x.startsWith "?" then
      match binding.lookup x with
      | some b => if a == b then some binding else none
      | none => some ((x, a) :: binding)
    else if x == a then some binding else none
  | .expr ps, .expr ts =>
    if ps.length != ts.length then none
    else (ps.zip ts).foldlM (init := binding) fun b (p, t) => matchPattern p t b
  | _, _ => none

/-- Checks that `definition`, of the sources, is `pattern`, a definition of an encoder. -/
def theoryDefinition (r : Relation) (pattern definition : Sexp) : Lower Unit :=
  match matchPattern pattern definition [] with
  | some binding =>
    if binding.all (fun (x, a) => (r.bagSymbol (x.drop 1).toString a).getD true) &&
        (binding.map (·.2)).eraseDups.length == binding.length then pure ()
    else refuse s!"{text definition} is not the definition of the encoder"
  | none => refuse s!"{text definition} is not the definition of the encoder"

/-- The variables that `xs` bind face those that `ys` bind, the sorts of parameters under
`bound`. -/
def bind (r : Relation) (xs ys : List Sexp) (bound : List (String × String)) (i o : Sexp) :
    Lower (List (String × String)) :=
  if xs.length != ys.length then no i o
  else (xs.zip ys).mapM fun p =>
    match p with
    | (.atom x, .atom y) => pure (x, y)
    | (.expr [.atom x, s], .expr [.atom y, s2]) => do r.relate s s2 bound; pure (x, y)
    | _ => no i o

end Relation

/-- The term after the steps `steps` of a simplification of `term`, which are recorded, and not
yet checked. -/
def simplified (term : Sexp) (steps : List Sexp) : Lower Sexp :=
  steps.foldlM (init := term) fun _ step =>
    match step with
    | .expr [.atom _, t] => pure t
    | other => refuse s!"{text other} is not a step of a simplification"

/-- Checks the input `input` of a certificate whose sources have the definitions
`sourceDefinitions` and the symbols `sourceSymbols`, and gives the number of constraints and
functions that it checked: none when the certificate has no input. -/
def check (input sourceDefinitions sourceSymbols : List Sexp) : Lower Nat :=
  match input with
  | [] => pure 0
  | .expr (.atom "encoders" :: names) :: .expr (.atom "definitions" :: definitions) :: rest => do
    let (lines, symbols) ← match rest.getLast? with
      | some (.expr (.atom "symbols" :: lines)) => pure (rest.dropLast, lines)
      | _ => refuse "the input of the certificate has no symbols"
    let encoders ← names.mapM fun n =>
      match n with
      | .atom t =>
        match unquote t with
        | some n => pure n
        | none => refuse s!"{t} is not the name of an encoder"
      | other => refuse s!"{text other} is not the name of an encoder"
    for n in encoders do
      if !known.contains n then refuse s!"the checker doesn't check the encoder {n}"
    let r : Relation := ⟨encoders, ← symbols.mapM entry, ← sourceSymbols.mapM entry⟩
    let inFuns := functions definitions
    let outFuns := functions sourceDefinitions
    let mut defined : List String := []
    for line in lines do
      match line with
      | .expr [.atom "constraint", i, .expr [.atom "encoded", o],
          .expr (.atom "simplified" :: steps)] =>
        r.relate i o []
        let _ ← simplified o steps
      -- a function of the sources: its body after the encoders is the body of its definition in
      -- the input, and its simplification the body of its source definition
      | .expr [.atom "function", call, .expr [.atom "encoded", body],
          .expr (.atom "simplified" :: steps)] =>
        let (f, args) ← match call with
          | .expr [.atom "as", .atom f, _] => pure (f, [])
          | .expr (.expr [.atom "as", .atom f, _] :: args) => pure (f, args)
          | .expr (.atom f :: args) => pure (f, args)
          | .atom f => pure (f, [])
          | other => refuse s!"{text other} is not the call of a function"
        let some out := outFuns.lookup f
          | refuse s!"{f} is not a function of the source definitions"
        let params := out.args.map fun x => match x with
          | .expr (p :: _) => p
          | p => p
        if params != args then refuse s!"{text call} is not the call of {f} on its parameters"
        if (← simplified body steps) != out.body then
          refuse s!"the body of {f} is not the simplification of its encoded body"
        match r.inputOf f (inFuns.map (·.1)) with
        | some g =>
          let some inp := inFuns.lookup g | pure ()
          let tparams ← r.bind inp.params out.params [] (.atom g) (.atom f)
          let ps ← r.bind inp.args out.args tparams (.atom g) (.atom f)
          r.relate inp.range out.range tparams
          r.relate inp.body body (ps ++ tparams)
        | none => pure ()
        defined := f :: defined
      | other => refuse s!"{text other} is not a constraint or a function of the input"
    for (f, _) in outFuns do
      if !defined.contains f then refuse s!"the input doesn't say what {f} is the simplification of"
    -- the datatypes of the input are those of the sources
    let outData := datatypes sourceDefinitions
    for (d, decl) in datatypes definitions do
      match (r.sourceOf d (outData.map (·.1))).bind (List.lookup · outData) with
      | some decl2 =>
        match decl, decl2 with
        | .expr [.atom "par", .expr ps, cs], .expr [.atom "par", .expr ps2, cs2] =>
          r.relate cs cs2 (← r.bind ps ps2 [] decl decl2)
        | _, _ => r.relate decl decl2 []
      | none => pure ()
    -- the datatype and the functions of the encoder of bags are those of the encoder
    if encoders.contains "bags" then
      for (d, decl) in outData do
        if r.theory (.atom d) "sort" "Bag" then r.theoryDefinition bagDatatype decl
      for (f, fn) in outFuns do
        for (name, pattern) in [("get", bagGet), ("inv", bagInvariant)] do
          if r.theory (.atom f) "function" name then
            r.theoryDefinition pattern (.expr [.expr fn.params, .expr fn.args, fn.range, fn.body])
    pure lines.length
  | _ => refuse "the input of the certificate is not one"

end Inox.Encoders
