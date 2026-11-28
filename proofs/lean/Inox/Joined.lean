/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Reached
import Inox.Input
import Inox.Lowered
import Inox.Simplified

/-!
# The input has no solution

`no_solution_of_reached` (`Inox/Reached.lean`) is about the program and the query that Logos
reads from the certificate. This module joins it to the input of the certificate, as
`Inox/Input.lean` reads it, where the input is lowered to them: its functions, and its
constraints after the steps of their simplifications (`Inox/Simplified.lean`), are lowered
(`Inox/Lowered.lean`) to the functions and the expressions of the query that Logos reads, up to
the names of their symbols, which the check matches (`linkCheck`). Then no values of the
variables of the input make all its constraints evaluate to `true` in its program
(`no_input_solution`).

The input is read where it is first-order, and its variables are integers, booleans, reals,
signed bit-vectors or values of datatypes, of their types (`InputSolution`), where the type
parameters of a datatype are its type arguments. A variable of a signed bit-vector is unsigned
in the query, whose signed view is the variable of the input. A variable of a datatype is in
the query where its type is lowered to a datatype of Logos, without type parameters, whose
constructors are those of its sort, of fields of the types that those of the sort are lowered
to (`dataMapOk`): its value in the query is then its value, with the constructors of Logos
(`lowerV`).
-/

namespace Inox.Joined

open Inox.Semantics Inox.Bridge Inox.Lowered Logos
open Inox.Simplified (Fact Step stepsApply stepsApply_refines Refines primValue OfTy OfTys
  substParams lookup_ctor_mem)
open Inox.Input (sectionOf Table Ctx funsOf readExpr)
open Inox.Encoded (FunIn IsPrim)

/-! ## The input -/

/-- The type of a sort of a variable or of a function of the input that is read. -/
def primTy : Sexp → Option Ty
  | .atom "Int" => some .IntegerType
  | .atom "Bool" => some .BooleanType
  | .atom "Real" => some .RealType
  | .expr [.atom "_", .atom "BitVec", .atom n] =>
    if !n.isEmpty && n.all Char.isDigit && n.toNat! > 0 then some (.BVType true n.toNat!)
    else none
  | _ => none

/-- The types that are read: bit-vectors are signed, as Inox reads them by default. -/
def isPrimTy : Ty → Bool
  | .IntegerType | .BooleanType | .RealType => true
  | .BVType s _ => s
  | _ => false

/-- The type of a variable of the query is that of the variable of the input, where Logos
reads a signed bit-vector as an unsigned one. -/
def primEq : Ty → Ty → Bool
  | .IntegerType, .IntegerType | .BooleanType, .BooleanType | .RealType, .RealType => true
  | .BVType s w, .BVType s' w' => s && !s' && w == w'
  | _, _ => false

theorem primEq_prim {a b : Ty} (h : primEq a b = true) : isPrimTy a = true := by
  cases a <;> cases b <;> simp_all [primEq, isPrimTy]

/-- The type of signed bit-vectors. -/
def isSignedTy : Ty → Bool
  | .BVType s _ => s
  | _ => false

/-- The unsigned view of a signed bit-vector, the value of the variable of the query of a
variable of the input of a signed bit-vector. -/
def unsignedOf : Value → Value
  | .BVV _ w x => .BVV false w x
  | v => v

/-- The type of a datatype. -/
def isDataTy : Ty → Bool
  | .ADTType _ _ => true
  | _ => false

/-- The kind of the values of a type. -/
def kindOfTy : Ty → LK
  | .IntegerType => .int
  | .ADTType _ _ => .any
  | _ => .prim

mutual
/-- The value of the query of a value of the input: its constructors are those that `K` matches
them with, without type arguments, and its bit-vectors are unsigned, as Logos reads them. -/
def lowerV (K : Id → Option Id) : Value → Value
  | .BVV _ w x => .BVV false w x
  | .ADTV c _ vs => .ADTV ((K c).getD c) [] (lowerVs K vs)
  | v => v
/-- `lowerV` of each value. -/
def lowerVs (K : Id → Option Id) : List Value → List Value
  | [] => []
  | v :: vs => lowerV K v :: lowerVs K vs
end

/-- The sort of a type of a datatype. -/
def sortOfTy : Ty → Option Id
  | .ADTType s _ => some s
  | _ => none

/-- A field of the type `T` of the input is lowered to a field of the type `T'` of Logos: they
are the same type of integers, booleans or reals, or `M` matches the type of a datatype `T`
with the datatype `T'`. -/
def fieldTyOk (M : List (Ty × Id)) (T T' : Ty) : Bool :=
  match T, T' with
  | .IntegerType, .IntegerType | .BooleanType, .BooleanType | .RealType, .RealType => true
  | .ADTType _ _, .ADTType s' [] => M.any fun (U, t) => tyEq 100 U T && t == s'
  | _, _ => false

/-- The fields `fs` of the input are lowered to the fields `fs'` of Logos, position by
position. -/
def fieldsMatch (M : List (Ty × Id)) : List Param → List (Id × Ty) → Bool
  | [], [] => true
  | .Param _ T :: fs, (_, T') :: fs' => fieldTyOk M T T' && fieldsMatch M fs fs'
  | _, _ => false

/-- The types of datatypes of the input that `M` matches with datatypes of `D` are lowered to
them: `K` matches each constructor of their sort with one of the datatype, of fields of the
types of the fields of the constructor, where the type parameters of the sort are the type
arguments, that are lowered to theirs. -/
def dataMapOk (cs : List Constructor) (ss : List ADTSort) (K : Id → Option Id) (D : List Data)
    (M : List (Ty × Id)) : Bool :=
  M.all fun (T, s') => match T with
    | .ADTType s tps => match lookup_sort ss s with
      | .Ok (.Sort _ tparams _ _) => cs.all fun
        | .Constructor c s1 fs => s1 != s || match K c with
          | some c' => match findCtor D c' with
            | some (d, _, fs') =>
              d.name == s' && fieldsMatch M (substParams (tparams.zip tps) fs) fs'
            | none => false
          | none => false
      | _ => false
    | _ => false

/-- The types of datatypes of the fields of the constructors of the types of `M` with the
datatypes of the fields of the constructors that `K` matches them with, added to `M`, `n`
times. -/
def tyClosure (cs : List Constructor) (ss : List ADTSort) (K : Id → Option Id) (D : List Data) :
    Nat → List (Ty × Id) → List (Ty × Id)
  | 0, M => M
  | n + 1, M =>
    let more := M.flatMap fun (T, _) => match T with
      | .ADTType s tps => match lookup_sort ss s with
        | .Ok (.Sort _ tparams _ _) => cs.flatMap fun
          | .Constructor c s1 fs => if s1 != s then [] else match K c with
            | some c' => match findCtor D c' with
              | some (_, _, fs') => ((substParams (tparams.zip tps) fs).zip fs').filterMap fun
                | (.Param _ U, (_, .ADTType t' [])) => (sortOfTy U).map fun _ => (U, t')
                | _ => none
              | none => []
            | none => []
        | _ => []
      | _ => []
    let new := more.foldl (fun acc (U, t) =>
      if (M ++ acc).any fun (V, u) => tyEq 100 V U && u == t then acc else acc ++ [(U, t)]) []
    if new.isEmpty then M else tyClosure cs ss K D n (M ++ new)

/-- The constructors of the sort `s` of the input with those of the datatype `s'` of `D`,
position by position. -/
def sortPairs (cs : List Constructor) (D : List Data) (s s' : Id) : List (Id × Id) :=
  match findData D s' with
  | some d => (cs.filterMap fun
      | .Constructor c s0 _ => if s0 == s then some c else none).zip (d.ctors.map (·.1))
  | none => []

/-- The constructors that `κ` matches, with those of their sorts and of the sorts of their
fields, position by position, `n` times. -/
def ctorClosure (cs : List Constructor) (D : List Data) :
    Nat → List (Id × Id) → List (Id × Id)
  | 0, κ => κ
  | n + 1, κ =>
    let more := κ.flatMap fun (c, c') =>
      match lookup_ctor cs c, findCtor D c' with
      | .Ok (.Constructor _ s fs), some (d, _, fs') =>
        sortPairs cs D s d.name ++ (fs.zip fs').flatMap fun
          | (.Param _ T, (_, T')) => match sortOfTy T, sortOfTy T' with
            | some t, some t' => sortPairs cs D t t'
            | _, _ => []
      | _, _ => []
    let κ' := (κ ++ more).eraseDups
    if κ'.length == κ.length then κ else ctorClosure cs D n κ'

/-- The kind of a field of the type `T`: integers, other primitive values, values of a
datatype, or any value. -/
def fieldKindOfTy : Ty → LK
  | .IntegerType => .int
  | .BooleanType | .RealType => .prim
  | .ADTType s [] => .data s
  | _ => .any

/-- The kind of a field. -/
def fieldKindOf : Param → LK
  | .Param _ T => fieldKindOfTy T

/-- The name of a field. -/
def paramName : Param → Id
  | .Param f _ => f

/-- Two kinds that are the same, other than of tuples. -/
def kindEq : LK → LK → Bool
  | .int, .int | .prim, .prim | .any, .any => true
  | .data s, .data s' => s == s'
  | _, _ => false

theorem kindEq_eq {a b : LK} (h : kindEq a b = true) : a = b := by
  unfold kindEq at h
  split at h <;> simp_all

/-- `F` gives the field `p` the datatype `s` and its kind. -/
def fieldKindOk (F : Id → Option (Id × LK)) (s : Id) (p : Param) : Bool :=
  match F (paramName p) with
  | some (s', k) => s' == s && kindEq k (fieldKindOf p)
  | none => false

theorem fieldKindOk_eq {F : Id → Option (Id × LK)} {s : Id} {p : Param}
    (h : fieldKindOk F s p = true) : F (paramName p) = some (s, fieldKindOf p) := by
  unfold fieldKindOk at h
  split at h
  · next s' k he =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [he, h.1, kindEq_eq h.2]
  · cases h


/-- The input: its functions, with the kinds of their parameters and of their results, its
constraints, its variables and whether it may compare functions. -/
structure InputRead where
  funs : List FunDef
  sigs : List (Id × List LK × LK)
  query : List Expr
  vars : List (Id × Ty)
  ctors : List Constructor
  sorts : List ADTSort
  extEq : Bool
  /-- the source expressions that the solver simplified, before it did, with the steps that
  rewrite them -/
  simps : List (Expr × List Step) := []

/-- The program of the input. -/
def InputRead.program (R : InputRead) : Program :=
  .Program R.funs R.ctors R.sorts []
    (if R.extEq then .ExtensionalEquality else .NoFunctionEquality)

/-- The facts that hold of the variables of the input: they have values of their types, and
those of primitive types have primitive values. -/
def InputRead.facts (R : InputRead) : List Fact :=
  R.vars.filterMap (fun p => (R.vars.lookup p.1).map (.typed p.1 ·)) ++
    R.vars.filterMap fun p => (R.vars.lookup p.1).bind fun T =>
      if isPrimTy T then some (.prim p.1) else none

/-- Values of the variables of the input, of their types, that make all its constraints evaluate
to `true` in its program. -/
def InputSolution (O : Oracle) (R : InputRead) (vs : List Value) : Prop :=
  List.Forall₂ (fun v T => OfTy R.ctors R.sorts T v) vs (R.vars.map Prod.snd) ∧
    ∃ bs, bind_all (R.vars.map Prod.fst) vs = .Ok bs ∧
      ∀ q ∈ R.query, ∃ n, eval O R.program n (Env.Env [] bs) q = .Ok (.BoolV true)

/-- What the constraint `q` is after the steps of its simplification, if they hold. -/
def InputRead.finalOf (R : InputRead) (q : Expr) : Expr :=
  match R.simps.find? (fun p => exprEq 1000 p.1 q) with
  | some (_, ss) => (stepsApply R.ctors R.sorts R.facts ss q).getD q
  | none => q

/-- The constraints after their simplifications. -/
def InputRead.final (R : InputRead) : List Expr := R.query.map R.finalOf

theorem finalOf_refines {O : Oracle} (hO : O.Sound) (R : InputRead) (q : Expr) :
    Refines O R.program R.facts q (R.finalOf q) := by
  unfold InputRead.finalOf
  split
  · next ss _ =>
    cases h : stepsApply R.ctors R.sorts R.facts ss q with
    | none => exact Inox.Simplified.refines_refl
    | some e =>
      simp only [Option.getD_some]
      exact stepsApply_refines (P := R.program) hO ⟨_, _, _, rfl⟩ R.facts ss q e h
  · exact Inox.Simplified.refines_refl

/-- The expression that a source expression of the simplifications assumes the typing of its
free variables of, and how many of them it assumes. -/
def untyped : Nat → Sexp → Nat × Sexp
  | n + 1, s@(.expr [.atom "assume", .expr [.expr [.atom "as", .atom ty, _], _, _], b]) =>
    if ty.startsWith "typing" then
      let (k, e) := untyped n b
      (k + 1, e)
    else (0, s)
  | _, e => (0, e)

/-- The position of a step, as a list of numbers. -/
def readPos : Sexp → Option (List Nat)
  | .expr ps => ps.mapM fun | .atom a => a.toNat? | _ => none
  | _ => none

/-- The steps of a source expression that the solver simplified, with positions in it under the
`k` assumptions of the typing of its variables, or nothing if one isn't read. -/
def readSteps (c : Ctx) (k : Nat) (steps : List Sexp) : Option (List Step) :=
  steps.mapM fun
    | .expr [.atom rule, pos, sub] => do
      let p ← readPos pos
      if p.take k != List.replicate k 2 then none
      let e ← (readExpr c 1000 sub).toOption
      pure ⟨rule, p.drop k, e⟩
    | _ => none

/-- The source expressions of the simplifications, with their steps, whose symbols are those of
the sources. The names that the solver gives their subterms don't matter, since the steps are
checked on the expressions as they are read. -/
def readSimps (certificate : Sexp) : List (Expr × List Step) :=
  let c : Ctx := ⟨Table.of (sectionOf certificate "source-symbols"), "Int", true, []⟩
  (sectionOf certificate "simplifications").filterMap fun
    | .expr [.atom "expression", _, original, .expr (.atom "names" :: _),
        .expr (.atom "steps" :: ss)] =>
      let (k, body) := untyped 100 original
      match (readExpr c 1000 body).toOption, readSteps c k ss with
      | some e, some steps => some (e, steps)
      | _, _ => none
    | _ => none

def orThrow {α : Type} (o : Option α) (why : String) : Except String α :=
  match o with
  | some a => .ok a
  | none => .error why

/-- The input of the certificate, or why it isn't read: every definition is that of a function
over the sorts that are read, that of a datatype or that of the invariant of a datatype, which
is the function `s$inv` of the datatype `s`, and every constraint is read. -/
def readInput (certificate : Sexp) : Except String InputRead := do
  let input := sectionOf certificate "input"
  let symbols := input.flatMap fun | .expr (.atom "symbols" :: rows) => rows | _ => []
  let definitions := input.flatMap fun | .expr (.atom "definitions" :: ds) => ds | _ => []
  let constraints := input.filterMap fun
    | .expr (.atom "constraint" :: i :: _) => some i
    | _ => none
  let t := Table.of symbols
  let c : Ctx := ⟨t, "Int", true, []⟩
  let fs := funsOf t true "Int" definitions
  let sorts := Inox.Input.sortsOf t true "Int" definitions
  -- the invariants of the datatypes: the datatype, the parameter and the body
  let invs := definitions.filterMap fun
    | .expr [.atom "datatype-invariant", .atom p, .atom sort, body] => some (t.id sort, p, body)
    | _ => none
  if fs.length + sorts.length + invs.length != definitions.length then
    throw "a definition of the input is not that of a function or a datatype that is read"
  -- the kind of a sort: that of its type, or of the values of a datatype
  let kindOf (B : List Id) (s : Sexp) : Option LK := match primTy s, s with
    | some T, _ => some (kindOfTy T)
    | none, .atom a =>
      if B.contains a then some .any else if t.kind a == "sort" then some (.data (t.id a)) else none
    | none, .expr (.atom a :: _ :: _) => if t.kind a == "sort" then some .any else none
    | none, _ => none
  let read ← fs.mapM fun f => do
    let body ← (readExpr f.ctx 1000 f.body).mapError (s!"the body of {f.name} has `{·}`")
    let ks ← f.sorts.mapM fun s =>
      orThrow (kindOf f.tparams s) s!"a parameter of {f.name} is of a sort that isn't read"
    let k ← orThrow (kindOf f.tparams f.ret) s!"{f.name} is of a sort that isn't read"
    pure (FunDef.FunDef f.name f.tparams f.params body, (f.name, ks, k))
  -- the invariant of the datatype `s` is the function `s$inv`, of no other name
  let invFuns ← invs.mapM fun (s, p, body) => do
    if fs.any (·.name == s ++ "$inv") || (invs.filter (·.1 == s)).length != 1 then
      throw s!"the invariant of {s} has the name of another function"
    let b ← (readExpr c 1000 body).mapError (s!"the invariant of {s} has `{·}`")
    pure (FunDef.FunDef (s ++ "$inv") [] [p] b)
  let query ← constraints.mapM fun i =>
    (readExpr c 1000 i).mapError (s!"a constraint has `{·}`")
  let vars ← (symbols.filterMap fun
    | .expr [.atom x, .atom "variable", _, _, sort] => some (x, sort)
    | _ => none).mapM fun (x, s) =>
      match primTy s, s with
      | some T, _ => pure (x, T)
      | none, _ =>
        match Inox.Input.readSortTy c [] 100 s with
        | some (.ADTType a tps) => pure (x, .ADTType a tps)
        | _ => throw s!"the variable {x} is of a sort that isn't read"
  pure
    { funs := read.map (·.1) ++ invFuns, sigs := read.map (·.2), query, vars
      ctors := sorts.flatMap fun (s, _, cs) => cs.map fun (c, ps) => .Constructor c s ps
      sorts := sorts.map fun (s, tps, _) =>
        .Sort s tps (if invs.any (·.1 == s) then some (s ++ "$inv") else none) none
      extEq := !(sectionOf certificate "simplifications").contains
        (.expr [.atom "function-equality", .atom "none"])
      simps := readSimps certificate }

/-! ## Matching the names -/

/-- The names of the input matched with those of the lowered expressions: of variables, of
functions, of constructors and of fields. -/
structure Names where
  vars : List (Id × Id) := []
  funs : List (Id × Id) := []
  ctors : List (Id × Id) := []
  fields : List (Id × Id) := []

def Names.app (a b : Names) : Names :=
  ⟨a.vars ++ b.vars, a.funs ++ b.funs, a.ctors ++ b.ctors, a.fields ++ b.fields⟩

/-- The names of `e` with those of `e'` at the same positions. They are only candidates, which
the check checks. -/
def pairs : Nat → Expr → Expr → Names
  | 0, _, _ => {}
  | n + 1, e, e' =>
    let all (es es' : List Expr) : Names :=
      (es.zip es').foldl (fun acc (a, a') => acc.app (pairs n a a')) {}
    match e, e' with
    | .Variable x, .Variable y => { vars := [(x, y)] }
    | .Let x a b, e' =>
      let inner := pairs n b e'
      match findVar x 1000 b e' with
      | some a' => inner.app (pairs n a a')
      | none => inner
    | .FunctionInvocation f _ es, .FunctionInvocation g _ es' =>
      ({ funs := [(f, g)] } : Names).app (all es es')
    | .ADT c _ es, .ADT c' _ es' => ({ ctors := [(c, c')] } : Names).app (all es es')
    | .ADT c _ es, .Assume _ (.ADT c' _ es') => ({ ctors := [(c, c')] } : Names).app (all es es')
    | .BVUnsignedToSigned a, .BVUnsignedToSigned a' => pairs n a a'
    | .BVUnsignedToSigned a, e' => pairs n a e'
    | .BVSignedToUnsigned a, e' => pairs n a e'
    | .IsConstructor a c, .IsConstructor a' c' =>
      ({ ctors := [(c, c')] } : Names).app (pairs n a a')
    | .ADTSelector a f, .ADTSelector a' f' =>
      ({ fields := [(f, f')] } : Names).app (pairs n a a')
    | .Plus a b, .Plus a' (.Plus b' (.IntegerLiteral 0)) => all [a, b] [a', b']
    | .Times a b, .Times a' (.Times b' (.IntegerLiteral 1)) => all [a, b] [a', b']
    | e, e' =>
      match kids e, kids e' with
      | some (i, es), some (j, es') => if i == j then all es es' else {}
      | _, _ => {}

/-- The functions of the input with those that they are lowered to: those that the constraints
call, and those that their bodies call, `n` calls deep. -/
def funPairs (R : InputRead) (P : List FunDef) : Nat → Names → Names
  | 0, N => N
  | n + 1, N =>
    let more := N.funs.map fun (f, g) =>
      match lookup_fun R.funs f, lookup_fun P g with
      | .Ok (.FunDef _ _ _ b), .Ok (.FunDef _ _ _ b') => pairs 1000 b b'
      | _, _ => {}
    let N' := more.foldl Names.app N
    let φ' := N'.funs.eraseDups
    if φ'.length == N.funs.eraseDups.length then N' else funPairs R P n N'

/-- The fields of the constructor `c` of the constructors `cs`. -/
def fieldsOf (cs : List Constructor) (c : Id) : List Id :=
  match lookup_ctor cs c with
  | .Ok (.Constructor _ _ fs) => fieldNames fs
  | _ => []

/-- The matching of the names of the input with those of the query of Logos. -/
structure Link where
  /-- the variables of the input, with those of the query -/
  ρ : List (Id × Id)
  /-- the functions of the input, with those of the program of Logos -/
  φ : List (Id × Id)
  /-- the constructors of the input, with those of the program of Logos -/
  κ : List (Id × Id)
  /-- the fields of the input, with those of the program of Logos -/
  σ : List (Id × Id)
  /-- the types of datatypes of the input, with the datatypes of Logos -/
  μ : List (Ty × Id)

def Link.of (R : InputRead) (r : TermSteps) : Link :=
  let P := r.equations.map funOf
  let N0 := ((R.final.zip (queryOf r.query)).map fun (q, q') => pairs 1000 q q').foldl
    Names.app {}
  let N := funPairs R P (R.funs.length + 1) N0
  let D := dataOf r
  let Γt := varsOf (sigsOf r.equations) r.query
  -- the constructors of the sorts of the variables of the query, and of their fields
  let κ0 := N.ctors ++ N.vars.flatMap fun (x, y) =>
    match (R.vars.lookup x).bind sortOfTy, (Γt.lookup y).bind sortOfTy with
    | some s, some s' => sortPairs R.ctors D s s'
    | _, _ => []
  let κ := ctorClosure R.ctors D (R.ctors.length + 1) κ0.eraseDups
  let cs := D.flatMap ctorsOfData
  -- the fields of the constructors, position by position
  let σ := (N.fields ++
    κ.flatMap fun (c, c') => (fieldsOf R.ctors c).zip (fieldsOf cs c')).eraseDups
  -- the types of the datatypes of the variables of the query, and of their fields
  let ρ := N.vars.eraseDups
  let μ0 := Γt.filterMap fun (y, T') => match (ρ.find? (·.2 == y)).map (·.1) with
    | some x => match R.vars.lookup x, T' with
      | some (.ADTType s tps), .ADTType s' [] => some (.ADTType s tps, s')
      | _, _ => none
    | none => none
  ⟨ρ, N.funs.eraseDups, κ, σ,
    tyClosure R.ctors R.sorts (fun c => κ.lookup c) D (R.ctors.length + 1) μ0⟩

/-- The signature of the names of the input that are matched. -/
def Link.sig (L : Link) (R : InputRead) : LSig where
  funs f := match L.φ.lookup f, R.sigs.lookup f with
    | some g, some (ks, k) => some (g, ks, k)
    | _, _ => none
  ctors c := L.κ.lookup c
  fields f := L.σ.lookup f
  kinds c := match L.κ.lookup c, lookup_ctor R.ctors c with
    | some _, .Ok (.Constructor _ s fs) => some (s, fs.map fieldKindOf)
    | _, _ => none
  fieldKinds f := R.ctors.findSome? fun
    | .Constructor _ s fs => (fs.find? (paramName · == f)).map fun p => (s, fieldKindOf p)
  invs c := match lookup_ctor R.ctors c with
    | .Ok (.Constructor _ s fs) => match lookup_sort R.sorts s with
      | .Ok (.Sort _ _ (some inv) _) => match lookup_fun R.funs inv with
        | .Ok (.FunDef g _ [p] B) => if g = inv then some (p, fs, B) else none
        | _ => none
      | _ => none
    | _ => none

/-- What a variable of the input of the type `T` is lowered to, where it is matched with the
variable `y` of the query, with its kind: the signed view of `y` for a signed bit-vector. -/
def ctxOf (y : Id) (T : Ty) : Expr × LK :=
  if isSignedTy T then (.BVUnsignedToSigned (.Variable y), .prim) else (.Variable y, kindOfTy T)

/-- The variable of the query in what a variable of the input is lowered to. -/
def ctxVar : Expr → Option Id
  | .Variable y => some y
  | .BVUnsignedToSigned (.Variable y) => some y
  | _ => none

theorem ctxVar_ctxOf (y : Id) (T : Ty) : ctxVar (ctxOf y T).1 = some y := by
  unfold ctxOf; split <;> rfl

/-- The variables of the input that are matched, with their kinds. -/
def Link.ctx (L : Link) (R : InputRead) : Id → Option (Expr × LK) := fun x =>
  match L.ρ.lookup x, R.vars.lookup x with
  | some y, some T => some (ctxOf y T)
  | _, _ => none

/-- The variable of the input that is matched with the variable `y` of the query. -/
def Link.pre (L : Link) (y : Id) : Option Id := (L.ρ.find? (·.2 == y)).map (·.1)

/-- The function `f` of the input is lowered to the function `g` of `P`. -/
def funCheck (S : LSig) (fs P : List FunDef) (f g : Id) (ks : List LK) (k : LK) : Bool :=
  match lookup_fun fs f, lookup_fun P g with
  | .Ok (.FunDef f0 tp ps b), .Ok (.FunDef g0 tp' ps' b') =>
    f0 == f && g0 == g && tp'.isEmpty && decide ps'.Nodup &&
      ps.length == ks.length && ps'.length == ks.length &&
      lowersCheck S 1000 (paramsCtx ps ps' ks) b b' k
  | _, _ => false

/-- The fields `fs'` are those of `F` of the fields `fs`, position by position. -/
def fieldsOkB (F : Id → Option Id) : List Id → List Id → Bool
  | [], [] => true
  | f :: fs, f' :: fs' => F f == some f' && fieldsOkB F fs fs'
  | _, _ => false

theorem fieldsOk_of {F : Id → Option Id} : ∀ {fs fs' : List Id}, fieldsOkB F fs fs' = true →
    FieldsOk F fs fs'
  | [], [], _ => trivial
  | f :: fs, f' :: fs', h => by
    simp only [fieldsOkB, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1, fieldsOk_of h.2⟩
  | [], _ :: _, h => by simp [fieldsOkB] at h
  | _ :: _, [], h => by simp [fieldsOkB] at h

/-- The sort `s` of the sorts `ss` has no invariant. -/
def noInv (ss : List ADTSort) (s : Id) : Bool :=
  match lookup_sort ss s with
  | .Ok (.Sort s0 _ none _) => s0 == s
  | _ => false

/-- The constructor `c` of the input is the constructor `c'` of `cs'`, with the fields of `S`
at the same positions, both of sorts without invariants. -/
def ctorCheck (S : LSig) (cs : List Constructor) (ss : List ADTSort) (cs' : List Constructor)
    (ss' : List ADTSort) (c c' : Id) : Bool :=
  match lookup_ctor cs c, lookup_ctor cs' c' with
  | .Ok (.Constructor c0 s fs), .Ok (.Constructor c1 s' fs') =>
    c0 == c && c1 == c' && noInv ss' s' &&
      fieldsOkB S.fields (fieldNames fs) (fieldNames fs')
  | _, _ => false

theorem fieldKinds_of {F : Id → Option (Id × LK)} {s : Id} : ∀ {fs : List Param},
    fs.all (fieldKindOk F s) = true → FieldKinds F s fs (fs.map fieldKindOf)
  | [], _ => trivial
  | .Param f T :: fs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact ⟨fieldKindOk_eq h.1, fieldKinds_of h.2⟩

theorem ctorOf_of {cs : List Constructor} {ss : List ADTSort} {c s : Id} {fs : List Param}
    {fns : List FunDef} {is : List Interpretation} {eqm : FunctionEquality}
    (hc : lookup_ctor cs c = .Ok (.Constructor c s fs)) (hs : noInv ss s = true) :
    CtorOf c fs (.Program fns cs ss is eqm) := by
  unfold noInv at hs
  split at hs
  · next s0 tps eq h =>
    simp only [beq_iff_eq] at hs
    subst hs
    exact ⟨s0, tps, eq, hc, h⟩
  · cases hs

/-- The input is lowered to the program and the query that Logos reads from the certificate:
each expression of the query is what the constraint at its position is lowered to, the
functions that they call are lowered to those of the program, and each variable of the query is
a variable of the input of its type, matched with no other. -/
def linkCheck (R : InputRead) (r : TermSteps) : Bool :=
  let L := Link.of R r
  let S := L.sig R
  let Γ := L.ctx R
  let Γt := varsOf (sigsOf r.equations) r.query
  let Qt := queryOf r.query
  R.vars.all (fun p => isPrimTy p.2 || isDataTy p.2) &&
    Qt.length == R.final.length &&
    (R.final.zip Qt).all (fun (q, q') => lowersCheck S 1000 Γ q q' .any) &&
    L.φ.all (fun (f, _) => match S.funs f with
      | some (g, ks, k) => funCheck S R.funs (r.equations.map funOf) f g ks k
      | none => true) &&
    Γt.all (fun (y, T) => match L.pre y with
      | some x =>
        (match R.vars.lookup x with
          | some T' => primEq T' T || fieldTyOk L.μ T' T
          | none => false) &&
        (match Γ x with
          | some (e, _) => ctxVar e == some y
          | _ => false)
      | none => false) &&
    L.ρ.all (fun (x, _) => match Γ x with
      | some (e, _) => match ctxVar e with
        | some y => L.pre y == some x && Γt.any (·.1 == y)
        | none => true
      | _ => true) &&
    L.κ.all (fun (c, _) => match S.ctors c with
      | some c' => ctorCheck S R.ctors R.sorts ((dataOf r).flatMap ctorsOfData)
          ((dataOf r).map fun d => .Sort d.name [] none none) c c'
      | none => true) &&
    L.κ.all (fun (c, _) => L.κ.all fun (d, _) => !(S.ctors c == S.ctors d) || c == d) &&
    L.σ.all (fun (f, _) => L.σ.all fun (g, _) => !(S.fields f == S.fields g) || f == g) &&
    L.κ.all (fun (c, _) => match lookup_ctor R.ctors c with
      | .Ok (.Constructor _ s fs) => fs.all (fieldKindOk S.fieldKinds s)
      | _ => true) &&
    dataMapOk R.ctors R.sorts S.ctors (dataOf r) L.μ

/-! ## The theorem -/

theorem hasV_prim {D : List Data} {T : Ty} (hT : isPrimTy T = true) {v : Value}
    (h : HasV [] v T) : HasV D v T := by
  cases T <;> simp [isPrimTy] at hT <;> cases v <;> exact h

theorem hasV_of_typed {cs : List Constructor} {ss : List ADTSort} {T : Ty}
    (hT : isPrimTy T = true) {v : Value}
    (h : OfTy cs ss T v) : HasV [] v T := by
  cases h <;> simp [isPrimTy] at hT <;> simp only [HasV]
  next h => exact h
  next h => exact ⟨trivial, trivial, h⟩

/-- The value of a variable of the query is of its type. -/
theorem hasV_query {cs : List Constructor} {ss : List ADTSort} {D : List Data} {T' T : Ty}
    {v : Value}
    (h : primEq T' T = true) (hv : OfTy cs ss T' v) : HasV D (unsignedOf v) T := by
  cases T' <;> cases T <;> simp [primEq] at h
  all_goals cases hv
  all_goals simp_all [unsignedOf, HasV]

theorem primValue_of_typed {cs : List Constructor} {ss : List ADTSort} {T : Ty}
    (hT : isPrimTy T = true)
    {v : Value} (h : OfTy cs ss T v) : primValue v = true := by
  cases h <;> simp [isPrimTy] at hT <;> rfl

/-- The values of the variables, of their types, by their names. -/
theorem bind_lookup_typed {cs : List Constructor} {ss : List ADTSort} :
    ∀ (ps : List (Id × Ty)) (vs : List Value)
    (bs : List Binding), bind_all (ps.map Prod.fst) vs = .Ok bs →
    List.Forall₂ (fun v T => OfTy cs ss T v) vs (ps.map Prod.snd) →
    ∀ x T, ps.lookup x = some T → ∃ v, lookup_var bs x = .Ok v ∧ OfTy cs ss T v
  | [], _, _, _, _, x, T, hx => by simp at hx
  | (y, U) :: ps, v :: vs, bs, h, .cons hv hvs, x, T, hx => by
    simp only [List.map_cons] at h
    rw [bind_all] at h
    split at h
    · next bs' hbs' =>
      cases h
      by_cases hxy : x = y
      · subst hxy
        simp only [List.lookup_cons_self, Option.some.injEq] at hx
        subst hx
        exact ⟨v, by rw [lookup_var, dite_eq_left_of_eq_true (eq_true rfl)], hv⟩
      · have hx' : ps.lookup x = some T := by
          have hb : (x == y) = false := beq_false_of_ne hxy
          simp only [List.lookup, hb] at hx
          exact hx
        obtain ⟨w, hw, hwT⟩ := bind_lookup_typed ps vs bs' hbs' hvs x T hx'
        exact ⟨w, by rw [lookup_var, dite_eq_right_of_eq_false (eq_false hxy)]; exact hw, hwT⟩
    · cases h
    · cases h

theorem primValue_of_hasV {T : Ty} (hT : isPrimTy T = true) {v : Value} (h : HasV [] v T) :
    primValue v = true := by
  cases T <;> simp [isPrimTy] at hT <;> cases v <;> simp [HasV] at h <;> rfl

/-- A key of a list of pairs has a value in it, the first of the key. -/
theorem lookup_of_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {p : α × β}, p ∈ l → ∃ b, l.lookup p.1 = some b ∧ (p.1, b) ∈ l
  | (a, b) :: l, p, h => by
    by_cases hp : p.1 = a
    · refine ⟨b, ?_, ?_⟩
      · simp [List.lookup, hp]
      · rw [hp]; exact List.mem_cons_self
    · have h' : p ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd (by rw [h]) hp
        · exact h
      obtain ⟨b', hb, hm⟩ := lookup_of_mem h'
      refine ⟨b', ?_, List.mem_cons_of_mem _ hm⟩
      simp only [List.lookup]
      split
      · next he => exact absurd (beq_iff_eq.mp he) hp
      · exact hb

theorem has_of_hasV {D : List Data} {K : Id → Option (Id × List LK)} {T : Ty}
    (hT : isPrimTy T = true) {v : Value} (h : HasV D v T) : Has K (kindOfTy T) v := by
  cases T <;> simp [isPrimTy] at hT <;> cases v <;> simp [HasV] at h
  · exact .int _
  · exact .prim rfl
  · exact .prim rfl
  · exact .prim rfl

theorem prim_of_kind {K : Id → Option (Id × List LK)} {T : Ty} (hT : isPrimTy T = true)
    {v : Value} (h : Has K (kindOfTy T) v) : IsPrim v = true := by
  cases T <;> simp [isPrimTy] at hT <;> simp only [kindOfTy] at h <;> cases h <;>
    first | rfl | assumption

/-- A value of a type has the kind of the type. -/
theorem has_of_typed {K : Id → Option (Id × List LK)} {cs : List Constructor}
    {ss : List ADTSort} {T : Ty} {v : Value} (h : OfTy cs ss T v) : Has K (kindOfTy T) v := by
  cases h
  · exact .int _
  · exact .prim rfl
  · exact .prim rfl
  · exact .any _
  · exact .prim rfl

/-- A value of a primitive type is lowered to its unsigned view. -/
theorem lowerV_prim {K : Id → Option Id} {cs : List Constructor} {ss : List ADTSort} {T : Ty}
    (hT : isPrimTy T = true) {v : Value} (h : OfTy cs ss T v) : lowerV K v = unsignedOf v := by
  cases h <;> simp [isPrimTy] at hT <;> rfl

theorem fieldTyOk_adt {M : List (Ty × Id)} {s : Id} {tps : List Ty} {T' : Ty}
    (h : fieldTyOk M (.ADTType s tps) T' = true) :
    ∃ s', T' = .ADTType s' [] ∧ (Ty.ADTType s tps, s') ∈ M := by
  cases T' with
  | ADTType s' args =>
    cases args with
    | nil =>
      simp only [fieldTyOk, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨U, t⟩, hm, he, rfl⟩ := h
      have hU := Inox.Lowered.tyEq_eq _ _ _ he
      simp only at hU
      subst hU
      exact ⟨t, rfl, hm⟩
    | cons _ _ => simp [fieldTyOk] at h
  | _ => simp [fieldTyOk] at h

section
variable {cs : List Constructor} {ss : List ADTSort} {K : Id → Option Id} {D : List Data}
  {M : List (Ty × Id)}

mutual
/-- A value of a type of the input that is lowered to a type of Logos is related to its
lowering, which is of that type. -/
theorem lower_ty (hM : dataMapOk cs ss K D M = true) : ∀ {T : Ty} {v : Value} {T' : Ty},
    OfTy cs ss T v → fieldTyOk M T T' = true → VR K v (lowerV K v) ∧ HasV D (lowerV K v) T'
  | _, _, T', .int _, h => by
    cases T' <;> simp [fieldTyOk] at h
    exact ⟨.prim rfl, trivial⟩
  | _, _, T', .bool _, h => by
    cases T' <;> simp [fieldTyOk] at h
    exact ⟨.prim rfl, trivial⟩
  | _, _, T', .real hr, h => by
    cases T' <;> simp [fieldTyOk] at h
    exact ⟨.prim rfl, hr⟩
  | _, _, T', .bv _, h => by cases T' <;> simp [fieldTyOk] at h
  | _, _, T', @OfTy.adt _ _ c s tps fs vs tparams inv eq hc hs _ hvs, h => by
    obtain ⟨s', rfl, hm⟩ := fieldTyOk_adt h
    have hd := List.all_eq_true.mp hM _ hm
    simp only [hs] at hd
    have hk := List.all_eq_true.mp hd _ (lookup_ctor_mem hc).1
    simp only [bne_self_eq_false, Bool.false_or] at hk
    split at hk
    · next c' hK =>
      split at hk
      · next d i fs' hf =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hk
        obtain ⟨hn, hfs⟩ := hk
        obtain ⟨hr, hv⟩ := lower_tys hM hvs hfs
        have hl : lowerV K (.ADTV c tps vs) = .ADTV c' [] (lowerVs K vs) := by
          simp only [lowerV, hK, Option.getD_some]
        rw [hl]
        exact ⟨.adt hK hr, by simp only [HasV, true_and]; exact ⟨d, i, fs', hf, hn, hv⟩⟩
      · cases hk
    · cases hk
/-- `lower_ty` of each field. -/
theorem lower_tys (hM : dataMapOk cs ss K D M = true) : ∀ {fs : List Param} {vs : List Value}
    {fs' : List (Id × Ty)}, OfTys cs ss fs vs → fieldsMatch M fs fs' = true →
    VRs K vs (lowerVs K vs) ∧ HasVs D (lowerVs K vs) (fs'.map Prod.snd)
  | _, _, [], .nil, _ => ⟨.nil, by simp [lowerVs, HasVs]⟩
  | _, _, _ :: _, .nil, h => by simp [fieldsMatch] at h
  | _, _, [], .cons _ _, h => by simp [fieldsMatch] at h
  | _, _, (_, _) :: _, .cons hv hr, h => by
    simp only [fieldsMatch, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := lower_ty hM hv h.1
    obtain ⟨h3, h4⟩ := lower_tys hM hr h.2
    exact ⟨.cons h1 h3, by simp only [lowerVs, List.map_cons, HasVs]; exact ⟨h2, h4⟩⟩
end
end

/-- Binding the names `ys` to the values that `g` gives them. -/
theorem bind_map (g : Id → Value) : ∀ ys : List Id,
    ∃ bs, bind_all ys (ys.map g) = .Ok bs ∧ ∀ y ∈ ys, lookup_var bs y = .Ok (g y)
  | [] => ⟨[], by simp [bind_all], by simp⟩
  | y :: ys => by
    obtain ⟨bs, hbs, hl⟩ := bind_map g ys
    refine ⟨.Binding y (g y) :: bs, by simp [bind_all, hbs], fun x hx => ?_⟩
    by_cases hxy : x = y
    · subst hxy; simp [lookup_var]
    · have hx' : x ∈ ys := by simpa [hxy] using hx
      simp [lookup_var, hxy, hl x hx']

theorem forall₂_map {D : List Data} (g : Id → Value) : ∀ {Γ : List (Id × Ty)},
    (∀ p ∈ Γ, HasV D (g p.1) p.2) →
      List.Forall₂ (HasV D) ((Γ.map Prod.fst).map g) (Γ.map Prod.snd)
  | [], _ => .nil
  | p :: Γ, h => .cons (h p (by simp)) (forall₂_map g fun q hq => h q (by simp [hq]))

theorem mem_zip_right {α β : Type} {b : β} : ∀ {l : List α} {l' : List β},
    l'.length = l.length → b ∈ l' → ∃ a, (a, b) ∈ l.zip l'
  | [], [], _, h => by simp at h
  | a :: l, b' :: l', hl, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨a, by simp⟩
    · obtain ⟨a', ha'⟩ := mem_zip_right (l := l) (by simpa using hl) h
      exact ⟨a', List.mem_cons_of_mem _ ha'⟩
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], _, h => by simp at h

/-- The input has no solution: where the theorem of `no_solution_of_reached` holds of a
certificate and its input is lowered to the program and the query that Logos reads from it
(`linkCheck`), no values of the variables of the input, of their types, make all its
constraints evaluate to `true` in its program. -/
theorem no_input_solution {O : Oracle} (sound : LogosSound) (hO : O.Sound)
    (hty : Inox.Extend.LogosTyping) {certificate : Logos.Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked) (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hsrc : sourceCheck r = true)
    (hreached : reachedCheck r = true) {R : InputRead} (_hR : readInput certificate = .ok R)
    (hlink : linkCheck R r = true) :
    ∀ vs, ¬ InputSolution O R vs := by
  intro vs ⟨hvs, bs, hbs, hsol⟩
  unfold linkCheck at hlink
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hlink
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hprim, hlen⟩, hq⟩, hfuns⟩, hvars⟩, hρ⟩, hctors⟩, hκ⟩, hσ⟩, hfk⟩, hdm⟩ :=
    hlink
  generalize hL : Link.of R r = L at hq hfuns hvars hρ hctors hκ hσ hfk hdm
  have hF : Funs R.program (programOf (dataOf r) r.equations) (L.sig R) := by
    intro f g ks k hf
    have hf' := hf
    simp only [Link.sig] at hf'
    split at hf'
    · next g0 ks0 k0 h1 h2 =>
      cases hf'
      have hc := hfuns (f, g) (Inox.Lowered.mem_of_lookup h1)
      simp only [hf] at hc
      unfold funCheck at hc
      split at hc
      · next f0 tp ps b g1 tp' ps' b' hb hb' =>
        simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hnd⟩, hl1⟩, hl2⟩, hl⟩ := hc
        exact ⟨tp, ps, ps', b, b', hb, hb', hnd, hl1, hl2, (lowers_sound _ 1000).1 _ _ _ _ hl⟩
      · cases hc
    · cases hf'
  have hC : Ctors R.program (programOf (dataOf r) r.equations) (L.sig R) := by
    refine ⟨fun c c' hc => ?_, fun c d c' hc hd => ?_, fun f g f' hf hg => ?_,
      fun c s ks hk => ?_, fun c p fs B hv => ?_⟩
    · have hk := hctors (c, c') (Inox.Lowered.mem_of_lookup hc)
      simp only [show (L.sig R).ctors c = some c' from hc] at hk
      unfold ctorCheck at hk
      split at hk
      · next c0 s fs c1 s' fs' h1 h2 =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hk
        obtain ⟨⟨⟨rfl, rfl⟩, hs'⟩, hfs⟩ := hk
        exact ⟨fs, fs', ⟨s, h1⟩, ctorOf_of h2 hs', fieldsOk_of hfs⟩
      · cases hk
    · have hk := hκ (c, c') (Inox.Lowered.mem_of_lookup hc) (d, c')
        (Inox.Lowered.mem_of_lookup hd)
      simp only [show (L.sig R).ctors c = some c' from hc,
        show (L.sig R).ctors d = some c' from hd] at hk
      simpa using hk
    · have hk := hσ (f, f') (Inox.Lowered.mem_of_lookup hf) (g, f')
        (Inox.Lowered.mem_of_lookup hg)
      simp only [show (L.sig R).fields f = some f' from hf,
        show (L.sig R).fields g = some f' from hg] at hk
      simpa using hk
    · have hk' := hk
      simp only [Link.sig] at hk'
      split at hk'
      · next c' c0 s0 fs h1 h2 =>
        cases hk'
        have hf := hfk (c, c') (Inox.Lowered.mem_of_lookup h1)
        simp only [h2] at hf
        have hc := hctors (c, c') (Inox.Lowered.mem_of_lookup h1)
        simp only [show (L.sig R).ctors c = some c' from h1] at hc
        unfold ctorCheck at hc
        rw [h2] at hc
        split at hc
        · next c2 s2 fs2 c1 s' fs' he _ =>
          cases he
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨⟨⟨rfl, rfl⟩, _⟩, _⟩ := hc
          exact ⟨fs, ⟨_, h2⟩, fieldKinds_of hf⟩
        · cases hc
      · cases hk'
    · simp only [Link.sig] at hv
      split at hv
      · next c0 s fs0 h1 =>
        split at hv
        · next s0 tps inv eq h2 =>
          split at hv
          · next g tps' p0 B0 h3 =>
            split at hv
            · next hg =>
              subst hg
              simp only [Option.some.injEq, Prod.mk.injEq] at hv
              obtain ⟨rfl, rfl, rfl⟩ := hv
              exact ⟨_, _, _, _, _, c0, s, s0, tps, eq, g, tps', rfl, h1, h2, h3⟩
            · cases hv
          · cases hv
        · cases hv
      · cases hv
  -- the values of the variables of the query: those of the variables of the input, as Logos
  -- reads them
  let g : Id → Value := fun y => match L.pre y with
    | some x => match lookup_var bs x with
      | .Ok v => lowerV (L.sig R).ctors v
      | _ => .UnitV
    | none => .UnitV
  have hg : ∀ x T y, R.vars.lookup x = some T → L.pre y = some x →
      ∃ v, lookup_var bs x = .Ok v ∧ OfTy R.ctors R.sorts T v ∧
        g y = lowerV (L.sig R).ctors v := by
    intro x T y hx hy
    obtain ⟨v, hv1, hv2⟩ := bind_lookup_typed R.vars vs bs hbs hvs x T hx
    exact ⟨v, hv1, hv2, by simp only [g, hy, hv1]⟩
  obtain ⟨bs', hbs', hl'⟩ := bind_map g ((varsOf (sigsOf r.equations) r.query).map Prod.fst)
  have hEnv : EnvOk O (programOf (dataOf r) r.equations) (L.sig R).ctors (L.sig R).kinds
      (L.ctx R) (Env.Env [] bs) (Env.Env [] bs') := by
    intro x y k hx
    have hx' := hx
    unfold Link.ctx at hx'
    split at hx'
    · next y0 T h1 h2 =>
      have hyk : ctxOf y0 T = (y, k) := Option.some.inj hx'
      have hyv : ctxVar y = some y0 := by
        rw [show y = (ctxOf y0 T).1 by rw [hyk]]; exact ctxVar_ctxOf y0 T
      have hc := hρ (x, y0) (Inox.Lowered.mem_of_lookup h1)
      simp only [hx, hyv, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at hc
      obtain ⟨hpre, y1, hy1, hy⟩ := hc
      obtain ⟨v, hv1, hv2, hgv⟩ := hg x T y0 h2 hpre
      have hc' := hvars y1 hy1
      rw [hy, hpre] at hc'
      simp only [h2, Bool.and_eq_true, Bool.or_eq_true] at hc'
      have hl := hl' y0 (List.mem_map.mpr ⟨y1, hy1, hy⟩)
      refine ⟨v, hv1, ?_⟩
      have hlv : lookup_var (env_vars (Env.Env [] bs')) y0 = .Ok (lowerV (L.sig R).ctors v) := by
        rw [← hgv]; exact hl
      unfold ctxOf at hyk
      split at hyk
      · next hs =>
        cases hyk
        cases hv2 <;> simp [isSignedTy] at hs
        subst hs
        refine ⟨.prim rfl, _, 0, .prim rfl, fun _ _ => ?_⟩
        simp only [eval, hlv, lowerV]
      · next hs =>
        cases hyk
        have hk := has_of_typed (K := (L.sig R).kinds) hv2
        refine ⟨hk, lowerV (L.sig R).ctors v, 0, ?_, fun _ _ => by simp only [eval, hlv]⟩
        rcases hc'.1 with hp | hd
        · have hTp := primEq_prim hp
          have hu : lowerV (L.sig R).ctors v = v := by
            rw [lowerV_prim hTp hv2]
            cases hv2 <;> simp_all [isSignedTy, unsignedOf, isPrimTy]
          rw [hu]
          exact .prim (prim_of_kind hTp hk)
        · exact (lower_ty hdm hv2 hd).1
    · cases hx'
  have hvs' : List.Forall₂ (HasV (dataOf r))
      (((varsOf (sigsOf r.equations) r.query).map Prod.fst).map g)
      ((varsOf (sigsOf r.equations) r.query).map Prod.snd) := by
    refine forall₂_map g fun p hp => ?_
    have hc := hvars p hp
    split at hc
    · next x hpre =>
      simp only [Bool.and_eq_true] at hc
      obtain ⟨hT, _⟩ := hc
      split at hT
      · next T' hx =>
        obtain ⟨v, _, hv, hgv⟩ := hg x T' p.1 hx hpre
        rw [hgv]
        rcases Bool.or_eq_true _ _ ▸ hT with hT | hT
        · rw [lowerV_prim (primEq_prim hT) hv]
          exact hasV_query hT hv
        · exact (lower_ty hdm hv hT).2
      · cases hT
    · cases hc
  refine no_solution_of_reached sound hO hty hAccept hr hcheck hsrc hreached _
    ⟨hvs', bs', hbs', fun q' hq' => ?_⟩
  obtain ⟨q, hqq⟩ := mem_zip_right hlen hq'
  obtain ⟨q0, hq0, hfq⟩ := List.mem_map.mp (List.of_mem_zip hqq).1
  obtain ⟨n, hn0⟩ := hsol q0 hq0
  have hfacts : ∀ f ∈ R.facts, f.Holds O R.program n (Env.Env [] bs) := by
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨p, _, hpf⟩ := List.mem_filterMap.mp hf
      obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hpf
      obtain ⟨v, hv1, hv2⟩ := bind_lookup_typed R.vars vs bs hbs hvs p.1 T hT
      exact ⟨v, hv1, hv2⟩
    · obtain ⟨p, _, hpf⟩ := List.mem_filterMap.mp hf
      obtain ⟨T, hT, hpf⟩ := Option.bind_eq_some_iff.mp hpf
      split at hpf
      · next hpT =>
        cases hpf
        obtain ⟨v, hv1, hv2⟩ := bind_lookup_typed R.vars vs bs hbs hvs p.1 T hT
        exact ⟨v, hv1, primValue_of_typed hpT hv2⟩
      · cases hpf
  have hn := finalOf_refines hO R q0 n _ _ hfacts hn0
  rw [hfq] at hn
  have hl := (lowers_sound _ 1000).1 _ _ _ _ (hq (q, q') hqq)
  obtain ⟨_, v', m, rv, hm⟩ := lowers_eval hO hF hC n.toNat hl _ _ hEnv n (Int.self_le_toNat n) _ hn
  rw [vr_bool rv] at hm
  exact ⟨m, hm m (Int.le_refl m)⟩

end Inox.Joined
