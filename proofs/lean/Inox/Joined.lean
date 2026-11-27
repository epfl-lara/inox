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

The input is read where it is first-order, with datatypes without type parameters nor
invariants, and its variables are integers, booleans or reals.
-/

namespace Inox.Joined

open Inox.Semantics Inox.Bridge Inox.Lowered Logos
open Inox.Simplified (Fact Step stepsApply stepsApply_refines Refines primValue)
open Inox.Input (sectionOf Table Ctx funsOf readExpr)
open Inox.Encoded (FunIn IsPrim)

/-! ## The input -/

/-- The type of a sort of a variable or of a function of the input that is read. -/
def primTy : Sexp → Option Ty
  | .atom "Int" => some .IntegerType
  | .atom "Bool" => some .BooleanType
  | .atom "Real" => some .RealType
  | _ => none

/-- The types that are read. -/
def isPrimTy : Ty → Bool
  | .IntegerType | .BooleanType | .RealType => true
  | _ => false

/-- The equality of the types that are read. -/
def primEq : Ty → Ty → Bool
  | .IntegerType, .IntegerType | .BooleanType, .BooleanType | .RealType, .RealType => true
  | _, _ => false

theorem primEq_eq {a b : Ty} (h : primEq a b = true) : a = b := by
  cases a <;> cases b <;> simp [primEq] at h <;> rfl

/-- The kind of the values of a type. -/
def kindOfTy : Ty → LK
  | .IntegerType => .int
  | _ => .prim

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

/-- The facts that hold of the variables of the input: they have values of primitive types. -/
def InputRead.facts (R : InputRead) : List Fact := R.vars.map fun p => .prim p.1

/-- What the constraint `q` is after the steps of its simplification, if they hold. -/
def InputRead.finalOf (R : InputRead) (q : Expr) : Expr :=
  match R.simps.find? (fun p => exprEq 1000 p.1 q) with
  | some (_, ss) => (stepsApply R.ctors R.facts ss q).getD q
  | none => q

/-- The constraints after their simplifications. -/
def InputRead.final (R : InputRead) : List Expr := R.query.map R.finalOf

theorem finalOf_refines {O : Oracle} (hO : O.Sound) (R : InputRead) (q : Expr) :
    Refines O R.program R.facts q (R.finalOf q) := by
  unfold InputRead.finalOf
  split
  · next ss _ =>
    cases h : stepsApply R.ctors R.facts ss q with
    | none => exact Inox.Simplified.refines_refl
    | some e =>
      simp only [Option.getD_some]
      exact stepsApply_refines (P := R.program) hO ⟨_, _, _, _, rfl⟩ R.facts ss q e h
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

/-- The source expressions of the simplifications without names, with their steps, whose
symbols are those of the sources. -/
def readSimps (certificate : Sexp) : List (Expr × List Step) :=
  let c : Ctx := ⟨Table.of (sectionOf certificate "source-symbols"), "Int", true, []⟩
  (sectionOf certificate "simplifications").filterMap fun
    | .expr [.atom "expression", _, original, .expr [.atom "names"], .expr (.atom "steps" :: ss)] =>
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
without type parameters over the sorts that are read or that of a datatype without type
parameters, and every constraint is read. -/
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
  if fs.length + sorts.length != definitions.length then
    throw "a definition of the input is not that of a function or a datatype that is read"
  if sorts.any (fun s => !s.2.1.isEmpty) then throw "a datatype has type parameters"
  -- the kind of a sort: that of its type, or of the values of a datatype
  let kindOf (s : Sexp) : Option LK := match primTy s, s with
    | some T, _ => some (kindOfTy T)
    | none, .atom a => if t.kind a == "sort" then some (.data (t.id a)) else none
    | none, _ => none
  let read ← fs.mapM fun f => do
    if !f.tparams.isEmpty then throw s!"the function {f.name} has type parameters"
    let body ← (readExpr f.ctx 1000 f.body).mapError (s!"the body of {f.name} has `{·}`")
    let ks ← f.sorts.mapM fun s =>
      orThrow (kindOf s) s!"a parameter of {f.name} is of a sort that isn't read"
    let k ← orThrow (kindOf f.ret) s!"{f.name} is of a sort that isn't read"
    pure (FunDef.FunDef f.name [] f.params body, (f.name, ks, k))
  let query ← constraints.mapM fun i =>
    (readExpr c 1000 i).mapError (s!"a constraint has `{·}`")
  let vars ← (symbols.filterMap fun
    | .expr [.atom x, .atom "variable", _, _, sort] => some (x, sort)
    | _ => none).mapM fun (x, s) =>
      orThrow ((primTy s).map (x, ·)) s!"the variable {x} is of a sort that isn't read"
  pure
    { funs := read.map (·.1), sigs := read.map (·.2), query, vars
      ctors := sorts.flatMap fun (s, _, cs) => cs.map fun (c, ps) => .Constructor c s ps
      sorts := sorts.map fun (s, _, _) => .Sort s [] none none
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

def Link.of (R : InputRead) (r : TermSteps) : Link :=
  let P := r.equations.map funOf
  let N0 := ((R.final.zip (queryOf r.query)).map fun (q, q') => pairs 1000 q q').foldl
    Names.app {}
  let N := funPairs R P (R.funs.length + 1) N0
  let κ := N.ctors.eraseDups
  let cs := (dataOf r).flatMap ctorsOfData
  -- the fields of the constructors, position by position
  let σ := (N.fields ++
    κ.flatMap fun (c, c') => (fieldsOf R.ctors c).zip (fieldsOf cs c')).eraseDups
  ⟨N.vars.eraseDups, N.funs.eraseDups, κ, σ⟩

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

/-- The variables of the input that are matched, with their kinds. -/
def Link.ctx (L : Link) (R : InputRead) : Id → Option (Expr × LK) := fun x =>
  match L.ρ.lookup x, R.vars.lookup x with
  | some y, some T => some (.Variable y, kindOfTy T)
  | _, _ => none

/-- The variable of the input that is matched with the variable `y` of the query. -/
def Link.pre (L : Link) (y : Id) : Option Id := (L.ρ.find? (·.2 == y)).map (·.1)

/-- The function `f` of the input is lowered to the function `g` of `P`. -/
def funCheck (S : LSig) (fs P : List FunDef) (f g : Id) (ks : List LK) (k : LK) : Bool :=
  match lookup_fun fs f, lookup_fun P g with
  | .Ok (.FunDef f0 tp ps b), .Ok (.FunDef g0 tp' ps' b') =>
    f0 == f && tp.isEmpty && g0 == g && tp'.isEmpty && decide ps'.Nodup &&
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
    c0 == c && c1 == c' && noInv ss s && noInv ss' s' &&
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
  R.vars.all (fun p => isPrimTy p.2) &&
    Qt.length == R.final.length &&
    (R.final.zip Qt).all (fun (q, q') => lowersCheck S 1000 Γ q q' .any) &&
    L.φ.all (fun (f, _) => match S.funs f with
      | some (g, ks, k) => funCheck S R.funs (r.equations.map funOf) f g ks k
      | none => true) &&
    Γt.all (fun (y, T) => match L.pre y with
      | some x =>
        (match R.vars.lookup x with
          | some T' => primEq T' T
          | none => false) &&
        (match Γ x with
          | some (.Variable y0, _) => y0 == y
          | _ => false)
      | none => false) &&
    L.ρ.all (fun (x, _) => match Γ x with
      | some (.Variable y, _) => L.pre y == some x && Γt.any (·.1 == y)
      | _ => true) &&
    L.κ.all (fun (c, _) => match S.ctors c with
      | some c' => ctorCheck S R.ctors R.sorts ((dataOf r).flatMap ctorsOfData)
          ((dataOf r).map fun d => .Sort d.name [] none none) c c'
      | none => true) &&
    L.κ.all (fun (c, _) => L.κ.all fun (d, _) => !(S.ctors c == S.ctors d) || c == d) &&
    L.σ.all (fun (f, _) => L.σ.all fun (g, _) => !(S.fields f == S.fields g) || f == g) &&
    L.κ.all (fun (c, _) => match lookup_ctor R.ctors c with
      | .Ok (.Constructor _ s fs) => fs.all (fieldKindOk S.fieldKinds s)
      | _ => true)

/-! ## The theorem -/

theorem hasV_prim {D : List Data} {T : Ty} (hT : isPrimTy T = true) {v : Value}
    (h : HasV [] v T) : HasV D v T := by
  cases T <;> simp [isPrimTy] at hT <;> cases v <;> exact h

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

theorem prim_of_kind {K : Id → Option (Id × List LK)} {T : Ty} {v : Value}
    (h : Has K (kindOfTy T) v) : IsPrim v = true := by
  cases T <;> simp only [kindOfTy] at h <;> cases h <;> first | rfl | assumption

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
(`linkCheck`), no values of the variables of the input make all its constraints evaluate to
`true` in its program. -/
theorem no_input_solution {O : Oracle} (sound : LogosSound) (hO : O.Sound)
    (hty : Inox.Extend.LogosTyping) {certificate : Logos.Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked) (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hsrc : sourceCheck r = true)
    (hreached : reachedCheck r = true) {R : InputRead} (_hR : readInput certificate = .ok R)
    (hlink : linkCheck R r = true) :
    ∀ vs, ¬ Solution O R.program [] R.vars R.query vs := by
  intro vs ⟨hvs, bs, hbs, hsol⟩
  unfold linkCheck at hlink
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hlink
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hprim, hlen⟩, hq⟩, hfuns⟩, hvars⟩, hρ⟩, hctors⟩, hκ⟩, hσ⟩, hfk⟩ := hlink
  generalize hL : Link.of R r = L at hq hfuns hvars hρ hctors hκ hσ hfk
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
        obtain ⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hnd⟩, hl1⟩, hl2⟩, hl⟩ := hc
        exact ⟨ps, ps', b, b', hb, hb', hnd, hl1, hl2, (lowers_sound _ 1000).1 _ _ _ _ hl⟩
      · cases hc
    · cases hf'
  have hC : Ctors R.program (programOf (dataOf r) r.equations) (L.sig R) := by
    refine ⟨fun c c' hc => ?_, fun c d c' hc hd => ?_, fun f g f' hf hg => ?_,
      fun c s ks hk => ?_⟩
    · have hk := hctors (c, c') (Inox.Lowered.mem_of_lookup hc)
      simp only [show (L.sig R).ctors c = some c' from hc] at hk
      unfold ctorCheck at hk
      split at hk
      · next c0 s fs c1 s' fs' h1 h2 =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hk
        obtain ⟨⟨⟨⟨rfl, rfl⟩, hs⟩, hs'⟩, hfs⟩ := hk
        exact ⟨fs, fs', ctorOf_of h1 hs, ctorOf_of h2 hs', fieldsOk_of hfs⟩
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
          obtain ⟨⟨⟨⟨rfl, rfl⟩, hs⟩, _⟩, _⟩ := hc
          exact ⟨fs, ctorOf_of h2 hs, fieldKinds_of hf⟩
        · cases hc
      · cases hk'
  -- the values of the variables of the query: those of the variables of the input
  let g : Id → Value := fun y => match L.pre y with
    | some x => match lookup_var bs x with
      | .Ok v => v
      | _ => .UnitV
    | none => .UnitV
  have hg : ∀ x T y, R.vars.lookup x = some T → L.pre y = some x →
      ∃ v, lookup_var bs x = .Ok v ∧ HasV [] v T ∧ g y = v := by
    intro x T y hx hy
    obtain ⟨v, hv1, hv2⟩ := bind_lookup R.vars vs bs hbs hvs x T hx
    exact ⟨v, hv1, hv2, by simp only [g, hy, hv1]⟩
  obtain ⟨bs', hbs', hl'⟩ := bind_map g ((varsOf (sigsOf r.equations) r.query).map Prod.fst)
  have hEnv : EnvOk O (programOf (dataOf r) r.equations) (L.sig R).ctors (L.sig R).kinds
      (L.ctx R) (Env.Env [] bs) (Env.Env [] bs') := by
    intro x y k hx
    have hx' := hx
    unfold Link.ctx at hx'
    split at hx'
    · next y0 T h1 h2 =>
      cases hx'
      have hc := hρ (x, y0) (Inox.Lowered.mem_of_lookup h1)
      simp only [hx, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at hc
      obtain ⟨hpre, y1, hy1, hy⟩ := hc
      obtain ⟨v, hv1, hv2, hgv⟩ := hg x T y0 h2 hpre
      have hk := has_of_hasV (K := (L.sig R).kinds)
        (hprim (x, T) (Inox.Lowered.mem_of_lookup h2)) hv2
      refine ⟨v, hv1, hk, v, 0, .prim (prim_of_kind hk), fun _ _ => ?_⟩
      rw [eval, show lookup_var (env_vars (Env.Env [] bs')) y0 = lookup_var bs' y0 from rfl,
        hl' y0 (List.mem_map.mpr ⟨y1, hy1, hy⟩), hgv]
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
        have hTT := primEq_eq hT
        obtain ⟨v, _, hv, hgv⟩ := hg x T' p.1 hx hpre
        rw [hgv, ← hTT]
        exact hasV_prim (hprim (x, T') (Inox.Lowered.mem_of_lookup hx)) hv
      · cases hT
    · cases hc
  refine no_solution_of_reached sound hO hty hAccept hr hcheck hsrc hreached _
    ⟨hvs', bs', hbs', fun q' hq' => ?_⟩
  obtain ⟨q, hqq⟩ := mem_zip_right hlen hq'
  obtain ⟨q0, hq0, hfq⟩ := List.mem_map.mp (List.of_mem_zip hqq).1
  obtain ⟨n, hn0⟩ := hsol q0 hq0
  have hfacts : ∀ f ∈ R.facts, f.Holds O R.program n (Env.Env [] bs) := by
    intro f hf
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
    obtain ⟨T, hT, hTm⟩ := lookup_of_mem hp
    obtain ⟨v, hv1, hv2⟩ := bind_lookup R.vars vs bs hbs hvs p.1 T hT
    exact ⟨v, hv1, primValue_of_hasV (hprim (p.1, T) hTm) hv2⟩
  have hn := finalOf_refines hO R q0 n _ _ hfacts hn0
  rw [hfq] at hn
  have hl := (lowers_sound _ 1000).1 _ _ _ _ (hq (q, q') hqq)
  obtain ⟨_, v', m, rv, hm⟩ := lowers_eval hO hF hC n.toNat hl _ _ hEnv n (Int.self_le_toNat n) _ hn
  rw [vr_bool rv] at hm
  exact ⟨m, hm m (Int.le_refl m)⟩

end Inox.Joined
