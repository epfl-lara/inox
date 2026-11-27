/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Reached
import Inox.Input
import Inox.Lowered

/-!
# The input has no solution

`no_solution_of_reached` (`Inox/Reached.lean`) is about the program and the query that Logos
reads from the certificate. This module joins it to the input of the certificate, as
`Inox/Input.lean` reads it, where the input is lowered to them without simplifications: its
functions and its constraints are lowered (`Inox/Lowered.lean`) to the functions and the
expressions of the query that Logos reads, up to the names of their symbols, which the check
matches (`linkCheck`). Then no values of the variables of the input make all its constraints
evaluate to `true` in its program (`no_input_solution`).

The input is read where it is first-order, without datatypes, and its variables are integers,
booleans or reals.
-/

namespace Inox.Joined

open Inox.Semantics Inox.Bridge Inox.Lowered Logos
open Inox.Input (sectionOf Table Ctx funsOf readExpr)
open Inox.Encoded (FunIn)

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

/-- The input: its functions, with the kinds of their parameters and of their results, its
constraints, its variables and whether it may compare functions. -/
structure InputRead where
  funs : List FunDef
  sigs : List (Id × List LK × LK)
  query : List Expr
  vars : List (Id × Ty)
  extEq : Bool

/-- The program of the input. -/
def InputRead.program (R : InputRead) : Program :=
  .Program R.funs [] [] [] (if R.extEq then .ExtensionalEquality else .NoFunctionEquality)

def orThrow {α : Type} (o : Option α) (why : String) : Except String α :=
  match o with
  | some a => .ok a
  | none => .error why

/-- The input of the certificate, or why it isn't read: every definition is that of a function
without type parameters over the sorts that are read, and every constraint is read. -/
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
  if fs.length != definitions.length then
    throw "a definition of the input is not that of a function that is read"
  let read ← fs.mapM fun f => do
    if !f.tparams.isEmpty then throw s!"the function {f.name} has type parameters"
    let body ← (readExpr f.ctx 1000 f.body).mapError (s!"the body of {f.name} has `{·}`")
    let ks ← f.sorts.mapM fun s =>
      orThrow ((primTy s).map kindOfTy) s!"a parameter of {f.name} is of a sort that isn't read"
    let k ← orThrow ((primTy f.ret).map kindOfTy) s!"{f.name} is of a sort that isn't read"
    pure (FunDef.FunDef f.name [] f.params body, (f.name, ks, k))
  let query ← constraints.mapM fun i =>
    (readExpr c 1000 i).mapError (s!"a constraint has `{·}`")
  let vars ← (symbols.filterMap fun
    | .expr [.atom x, .atom "variable", _, _, sort] => some (x, sort)
    | _ => none).mapM fun (x, s) =>
      orThrow ((primTy s).map (x, ·)) s!"the variable {x} is of a sort that isn't read"
  pure
    { funs := read.map (·.1), sigs := read.map (·.2), query, vars
      extEq := !(sectionOf certificate "simplifications").contains
        (.expr [.atom "function-equality", .atom "none"]) }

/-! ## Matching the names -/

/-- The operations whose operands are matched position by position, by a tag. -/
def kids : Expr → Option (Nat × List Expr)
  | .Plus a b => some (0, [a, b])
  | .Minus a b => some (1, [a, b])
  | .Times a b => some (2, [a, b])
  | .UMinus a => some (3, [a])
  | .Division a b => some (4, [a, b])
  | .Remainder a b => some (5, [a, b])
  | .Modulo a b => some (6, [a, b])
  | .LessThan a b => some (7, [a, b])
  | .GreaterThan a b => some (8, [a, b])
  | .LessEquals a b => some (9, [a, b])
  | .GreaterEquals a b => some (10, [a, b])
  | .Equals a b => some (11, [a, b])
  | .Not a => some (12, [a])
  | .Implies a b => some (13, [a, b])
  | .And es => some (14, es)
  | .Or es => some (15, es)
  | .IfExpr c a b => some (16, [c, a, b])
  | .Assume p a => some (17, [p, a])
  | _ => none

/-- The variables and the functions of `e` with those of `e'` at the same positions. They are
only candidates, which the check checks. -/
def pairs : Nat → Expr → Expr → List (Id × Id) × List (Id × Id)
  | 0, _, _ => ([], [])
  | n + 1, e, e' =>
    let all (es es' : List Expr) : List (Id × Id) × List (Id × Id) :=
      (es.zip es').foldl (fun (vs, fs) (a, a') =>
        let (vs', fs') := pairs n a a'
        (vs ++ vs', fs ++ fs')) ([], [])
    match e, e' with
    | .Variable x, .Variable y => ([(x, y)], [])
    | .FunctionInvocation f _ es, .FunctionInvocation g _ es' =>
      let (vs, fs) := all es es'
      (vs, (f, g) :: fs)
    | .Plus a b, .Plus a' (.Plus b' (.IntegerLiteral 0)) => all [a, b] [a', b']
    | e, e' =>
      match kids e, kids e' with
      | some (i, es), some (j, es') => if i == j then all es es' else ([], [])
      | _, _ => ([], [])

/-- The functions of the input with those that they are lowered to: those that the constraints
call, and those that their bodies call, `n` calls deep. -/
def funPairs (R : InputRead) (P : List FunDef) : Nat → List (Id × Id) → List (Id × Id)
  | 0, φ => φ
  | n + 1, φ =>
    let more := φ.flatMap fun (f, g) =>
      match lookup_fun R.funs f, lookup_fun P g with
      | .Ok (.FunDef _ _ _ b), .Ok (.FunDef _ _ _ b') => (pairs 1000 b b').2
      | _, _ => []
    let φ' := (φ ++ more).eraseDups
    if φ'.length == φ.length then φ else funPairs R P n φ'

/-- The matching of the names of the input with those of the query of Logos. -/
structure Link where
  /-- the variables of the input, with those of the query -/
  ρ : List (Id × Id)
  /-- the functions of the input, with those of the program of Logos -/
  φ : List (Id × Id)

def Link.of (R : InputRead) (r : TermSteps) : Link :=
  let ps := (R.query.zip (queryOf r.query)).map fun (q, q') => pairs 1000 q q'
  let ρ := (ps.flatMap (·.1)).eraseDups
  let φ := funPairs R (r.equations.map funOf) (R.funs.length + 1) (ps.flatMap (·.2)).eraseDups
  ⟨ρ, φ⟩

/-- The signature of the functions of the input that are matched. -/
def Link.sig (L : Link) (R : InputRead) : LSig := fun f =>
  match L.φ.lookup f, R.sigs.lookup f with
  | some g, some (ks, k) => some (g, ks, k)
  | _, _ => none

/-- The variables of the input that are matched, with their kinds. -/
def Link.ctx (L : Link) (R : InputRead) : Id → Option (Id × LK) := fun x =>
  match L.ρ.lookup x, R.vars.lookup x with
  | some y, some T => some (y, kindOfTy T)
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
    Qt.length == R.query.length &&
    (R.query.zip Qt).all (fun (q, q') => lowersCheck S 1000 Γ q q' .any) &&
    L.φ.all (fun (f, _) => match S f with
      | some (g, ks, k) => funCheck S R.funs (r.equations.map funOf) f g ks k
      | none => true) &&
    Γt.all (fun (y, T) => match L.pre y with
      | some x =>
        (match R.vars.lookup x with
          | some T' => primEq T' T
          | none => false) &&
        (match Γ x with
          | some (y0, _) => y0 == y
          | none => false)
      | none => false) &&
    L.ρ.all (fun (x, _) => match Γ x with
      | some (y, _) => L.pre y == some x && Γt.any (·.1 == y)
      | none => true)

/-! ## The theorem -/

theorem hasV_prim {D : List Data} {T : Ty} (hT : isPrimTy T = true) {v : Value}
    (h : HasV [] v T) : HasV D v T := by
  cases T <;> simp [isPrimTy] at hT <;> cases v <;> exact h

theorem has_of_hasV {D : List Data} {T : Ty} (hT : isPrimTy T = true) {v : Value}
    (h : HasV D v T) : Has (kindOfTy T) v := by
  cases T <;> simp [isPrimTy] at hT <;> cases v <;> simp [HasV] at h
  · exact .int _
  · exact .prim rfl
  · exact .prim rfl

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
  obtain ⟨⟨⟨⟨⟨hprim, hlen⟩, hq⟩, hfuns⟩, hvars⟩, hρ⟩ := hlink
  generalize hL : Link.of R r = L at hq hfuns hvars hρ
  have hF : Funs R.program (programOf (dataOf r) r.equations) (L.sig R) := by
    intro f g ks k hf
    have hf' := hf
    unfold Link.sig at hf'
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
  have hEnv : EnvOk (L.ctx R) (Env.Env [] bs) (Env.Env [] bs') := by
    intro x y k hx
    have hx' := hx
    unfold Link.ctx at hx'
    split at hx'
    · next y0 T h1 h2 =>
      cases hx'
      have hc := hρ (x, y) (Inox.Lowered.mem_of_lookup h1)
      simp only [hx, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at hc
      obtain ⟨hpre, y1, hy1, hy⟩ := hc
      obtain ⟨v, hv1, hv2, hgv⟩ := hg x T y h2 hpre
      refine ⟨v, hv1, ?_, has_of_hasV (hprim (x, T) (Inox.Lowered.mem_of_lookup h2)) hv2⟩
      rw [show lookup_var (env_vars (Env.Env [] bs')) y = lookup_var bs' y from rfl,
        hl' y (List.mem_map.mpr ⟨y1, hy1, hy⟩), hgv]
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
  obtain ⟨n, hn⟩ := hsol q (List.of_mem_zip hqq).1
  have hl := (lowers_sound _ 1000).1 _ _ _ _ (hq (q, q') hqq)
  obtain ⟨_, m, hm⟩ := lowers_eval hO hF n.toNat hl _ _ hEnv n (Int.self_le_toNat n) _ hn
  exact ⟨m, hm m (Int.le_refl m)⟩

end Inox.Joined
