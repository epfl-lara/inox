/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.NoSolution

/-!
# The program and the query of a certificate, on integers and Booleans

`no_solution` (`Inox/NoSolution.lean`) is about a program `P` and a query `qs`, and asks that the
defining equations and the base clauses of the certificate are their translations (`EqFor`,
`BaseFor`). This file reads `P` and `qs` back from the certificate and checks that:

- `back` reads a term of Logos as an expression of the semantics. Nothing is proved of it: the
  check translates what it gives and compares the result with the term;
- `infer` types an expression of the fragment (`infer_sound`);
- `programOf`, `sigsOf`, `varsOf` and `queryOf` are the program, its signatures, the free
  variables and the query that the equations and the base clauses denote;
- `sourceCheck` holds when each equation is the translation of the body read from it, each base
  clause that of the expression read from it, and the names and the types are those of the
  fragment. It gives the hypotheses of `no_solution` on the program and the query
  (`no_solution_of_check`). When the check of the certificate covers every fact, nothing is
  assumed of its clauses (`no_solution_of_covered`).

The names are those that Logos gives the constants, and an n-ary operation is read as Logos
reads it: `(+ a b)` is `a + (b + 0)`. That this program and this query are the ones that Inox
answered about is not proved: it is what the certificate's sources state. A call of a function
without parameters is read as a variable, so the check refuses a certificate that has one.
-/

namespace Inox.Bridge

open Eo
open SmtEval
open Smtm
open Inox.Fresh
open Inox.Extend
open Inox.Model
open Inox.Semantics

/-! ## Reading terms back -/

/-- The identifier whose characters have the codes `s`. -/
def idOf (s : native_String) : Id := String.ofList (s.map Char.ofNat)

/-- The type of a sort of the fragment. -/
def tyOf : SmtType → Ty
  | .Int => .IntegerType
  | .Bool => .BooleanType
  | _ => .UnitType

mutual
/-- The expression that the term `t` is read as. A term outside the fragment is read as `Error`,
which no check accepts. An assumption is read from its mark (`markAssumes` of
`Inox/Terms.lean`), and `mod` as `Modulo`, which is `Remainder` on integers. -/
def back : SmtTerm → Expr
  | .UConst s _ => .Variable (idOf s)
  | .Numeral i => .IntegerLiteral i
  | .Boolean b => .BooleanLiteral b
  | .ite (.xor c (.Boolean false)) a _ => .Assume (back c) (back a)
  | .ite c a b => .IfExpr (back c) (back a) (back b)
  | .not a => .Not (back a)
  | .imp a b => .Implies (back a) (back b)
  | .eq a b => .Equals (back a) (back b)
  | .plus a b => .Plus (back a) (back b)
  | .neg a b => .Minus (back a) (back b)
  | .mult a b => .Times (back a) (back b)
  | .div a b => .Division (back a) (back b)
  | .mod a b => .Modulo (back a) (back b)
  | .uneg a => .UMinus (back a)
  | .lt a b => .LessThan (back a) (back b)
  | .gt a b => .GreaterThan (back a) (back b)
  | .leq a b => .LessEquals (back a) (back b)
  | .geq a b => .GreaterEquals (back a) (back b)
  | .and a r => .And (back a :: backAnd r)
  | .or a r => .Or (back a :: backOr r)
  | .Apply f a => .FunctionInvocation (backHead f) [] (backArgs f ++ [back a])
  | _ => .Error

/-- The conjuncts of the rest `r` of a conjunction, which ends with `true`. -/
def backAnd : SmtTerm → List Expr
  | .and a r => back a :: backAnd r
  | _ => []

/-- The disjuncts of the rest `r` of a disjunction, which ends with `false`. -/
def backOr : SmtTerm → List Expr
  | .or a r => back a :: backOr r
  | _ => []

/-- The function that the head `f` of an application applies. -/
def backHead : SmtTerm → Id
  | .Apply f _ => backHead f
  | .UConst s _ => idOf s
  | _ => ""

/-- The arguments that the head `f` of an application already has. -/
def backArgs : SmtTerm → List Expr
  | .Apply f a => backArgs f ++ [back a]
  | _ => []
end

/-- The constants that `t` mentions other than as the function of an application, with their
sorts. -/
def consts : SmtTerm → List (native_String × SmtType)
  | .UConst s T => [(s, T)]
  | .ite c a b => consts c ++ consts a ++ consts b
  | .not a | .uneg a => consts a
  | .imp a b | .eq a b | .plus a b | .neg a b | .mult a b | .div a b | .mod a b | .lt a b
  | .gt a b | .leq a b | .geq a b | .and a b | .or a b => consts a ++ consts b
  | .Apply (.UConst _ _) a => consts a
  | .Apply f a => consts f ++ consts a
  | _ => []

/-! ## Typing -/

/-- Whether a type of the fragment is that of the Booleans. -/
def kind : Ty → Option Bool
  | .IntegerType => some false
  | .BooleanType => some true
  | _ => none

/-- The type of the fragment of a kind. -/
def ofKind : Bool → Ty
  | true => .BooleanType
  | false => .IntegerType

theorem kind_spec {T : Ty} {b : Bool} (h : kind T = some b) : T = ofKind b := by
  cases T <;> simp [kind] at h <;> subst h <;> rfl

theorem fragTy_ofKind (b : Bool) : FragTy (ofKind b) := by cases b <;> trivial

mutual
/-- The kind of the type of `e`, if it is an expression of the fragment. -/
def infer (S : List Sig) (Γ : List (Id × Ty)) : Expr → Option Bool
  | .Variable x => (Γ.lookup x).bind kind
  | .IntegerLiteral _ => some false
  | .BooleanLiteral _ => some true
  | .IfExpr c a b =>
    match infer S Γ c, infer S Γ a, infer S Γ b with
    | some true, some k, some k' => if k = k' then some k else none
    | _, _, _ => none
  | .And es => if inferAll S Γ es then some true else none
  | .Or es => if inferAll S Γ es then some true else none
  | .Not a => if infer S Γ a = some true then some true else none
  | .Implies a b =>
    if infer S Γ a = some true ∧ infer S Γ b = some true then some true else none
  | .Equals a b =>
    match infer S Γ a, infer S Γ b with
    | some k, some k' => if k = k' then some true else none
    | _, _ => none
  | .Plus a b | .Minus a b | .Times a b | .Division a b | .Remainder a b | .Modulo a b =>
    if infer S Γ a = some false ∧ infer S Γ b = some false then some false else none
  | .UMinus a => if infer S Γ a = some false then some false else none
  | .LessThan a b | .GreaterThan a b | .LessEquals a b | .GreaterEquals a b =>
    if infer S Γ a = some false ∧ infer S Γ b = some false then some true else none
  | .FunctionInvocation f [] args =>
    match findSig S f with
    | some s => if inferArgs S Γ args (s.params.map Prod.snd) then kind s.ret else none
    | none => none
  | .Assume p b => if infer S Γ p = some true then infer S Γ b else none
  | _ => none

/-- The expressions `es` are Booleans. -/
def inferAll (S : List Sig) (Γ : List (Id × Ty)) : List Expr → Bool
  | [] => true
  | e :: es => infer S Γ e = some true && inferAll S Γ es

/-- The arguments `es` are of the types `Ts`. -/
def inferArgs (S : List Sig) (Γ : List (Id × Ty)) : List Expr → List Ty → Bool
  | [], [] => true
  | e :: es, T :: Ts => (infer S Γ e).isSome && infer S Γ e = kind T && inferArgs S Γ es Ts
  | _, _ => false
end

mutual
theorem infer_sound (S : List Sig) (Γ : List (Id × Ty)) :
    ∀ (e : Expr) (k : Bool), infer S Γ e = some k → HasTy S Γ e (ofKind k)
  | .Variable x, k, h => by
    simp only [infer] at h
    cases hx : Γ.lookup x with
    | none => simp [hx] at h
    | some T =>
      simp only [hx, Option.bind_some] at h
      have := kind_spec h
      subst this
      exact .var hx (fragTy_ofKind k)
  | .IntegerLiteral i, k, h => by
    simp only [infer, Option.some.injEq] at h; subst h; exact .int i
  | .BooleanLiteral b, k, h => by
    simp only [infer, Option.some.injEq] at h; subst h; exact .bool b
  | .IfExpr c a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i k1 k2 hc ha hb
      split at h
      · rename_i hk
        simp only [Option.some.injEq] at h
        subst hk; subst h
        exact .ite (infer_sound S Γ c true hc) (infer_sound S Γ a _ ha) (infer_sound S Γ b _ hb)
      · cases h
    · cases h
  | .And es, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hall
      simp only [Option.some.injEq] at h; subst h
      exact .and (inferAll_sound S Γ es hall)
    · cases h
  | .Or es, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hall
      simp only [Option.some.injEq] at h; subst h
      exact .or (inferAll_sound S Γ es hall)
    · cases h
  | .Not a, k, h => by
    simp only [infer] at h
    split at h
    · rename_i ha
      simp only [Option.some.injEq] at h; subst h
      exact .not (infer_sound S Γ a true ha)
    · cases h
  | .Implies a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .implies (infer_sound S Γ a true hab.1) (infer_sound S Γ b true hab.2)
    · cases h
  | .Equals a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i k1 k2 ha hb
      split at h
      · rename_i hk
        simp only [Option.some.injEq] at h
        subst hk; subst h
        exact .equals (infer_sound S Γ a _ ha) (infer_sound S Γ b _ hb)
      · cases h
    · cases h
  | .Plus a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .plus (infer_sound S Γ a false hab.1) (infer_sound S Γ b false hab.2)
    · cases h
  | .Minus a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .minus (infer_sound S Γ a false hab.1) (infer_sound S Γ b false hab.2)
    · cases h
  | .Times a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .times (infer_sound S Γ a false hab.1) (infer_sound S Γ b false hab.2)
    · cases h
  | .Division a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .div (infer_sound S Γ a false hab.1) (infer_sound S Γ b false hab.2)
    · cases h
  | .Remainder a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .rem (infer_sound S Γ a false hab.1) (infer_sound S Γ b false hab.2)
    · cases h
  | .Modulo a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .mod (infer_sound S Γ a false hab.1) (infer_sound S Γ b false hab.2)
    · cases h
  | .UMinus a, k, h => by
    simp only [infer] at h
    split at h
    · rename_i ha
      simp only [Option.some.injEq] at h; subst h
      exact .uminus (infer_sound S Γ a false ha)
    · cases h
  | .LessThan a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .lt (infer_sound S Γ a false hab.1) (infer_sound S Γ b false hab.2)
    · cases h
  | .GreaterThan a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .gt (infer_sound S Γ a false hab.1) (infer_sound S Γ b false hab.2)
    · cases h
  | .LessEquals a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .le (infer_sound S Γ a false hab.1) (infer_sound S Γ b false hab.2)
    · cases h
  | .GreaterEquals a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .ge (infer_sound S Γ a false hab.1) (infer_sound S Γ b false hab.2)
    · cases h
  | .FunctionInvocation f [] args, k, h => by
    simp only [infer] at h
    split at h
    · rename_i s hs
      split at h
      · rename_i hargs
        obtain ⟨_, rfl⟩ := findSig_spec hs
        have hr := kind_spec h
        obtain ⟨hlen, hall⟩ := inferArgs_sound S Γ args _ hargs
        rw [← hr]
        exact .invoke hs (by simpa using hlen) hall
      · cases h
    · cases h
  | .FunctionInvocation f (_ :: _) args, k, h => by simp [infer] at h
  | .Assume p b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hp
      exact .assume (infer_sound S Γ p true hp) (infer_sound S Γ b k h)
    · cases h
  | .Let _ _ _, k, h | .Application _ _, k, h | .Lambda _ _, k, h
  | .Forall _ _, k, h | .UninterpretedCall _ _ _, k, h | .Error, k, h | .CharLiteral _, k, h
  | .BVLiteral _ _ _, k, h | .FractionLiteral _ _, k, h | .FPLiteral _ _ _, k, h
  | .StringLiteral _, k, h | .UnitLiteral, k, h | .RoundNearestTiesToEven, k, h
  | .RoundNearestTiesToAway, k, h | .RoundTowardPositive, k, h | .RoundTowardNegative, k, h
  | .RoundTowardZero, k, h | .ADT _ _ _, k, h | .IsConstructor _ _, k, h | .ADTSelector _ _, k, h
  | .StringConcat _ _, k, h | .SubString _ _ _, k, h | .StringLength _, k, h
  | .BVNot _, k, h
  | .BVAnd _ _, k, h | .BVOr _ _, k, h | .BVXor _ _, k, h | .BVShiftLeft _ _, k, h
  | .BVAShiftRight _ _, k, h | .BVLShiftRight _ _, k, h | .BVNarrowingCast _ _, k, h
  | .BVWideningCast _ _, k, h | .BVUnsignedToSigned _, k, h | .BVSignedToUnsigned _, k, h
  | .BVToInt _, k, h | .IntToBV _ _ _, k, h | .FPEquals _ _, k, h | .FPAdd _ _ _, k, h
  | .FPSub _ _ _, k, h | .FPUMinus _, k, h | .FPFMA _ _ _ _, k, h | .FPMul _ _ _, k, h
  | .FPDiv _ _ _, k, h | .FPAbs _, k, h | .FPMax _ _, k, h | .FPMin _ _, k, h
  | .FPRound _ _, k, h | .Sqrt _ _, k, h | .FPCast _ _ _ _, k, h | .FPFromBinary _ _ _, k, h
  | .FPToBV _ _ _ _, k, h | .FPToReal _, k, h | .FPLessThan _ _, k, h | .FPGreaterThan _ _, k, h
  | .FPLessEquals _ _, k, h | .FPGreaterEquals _ _, k, h | .FPIsZero _, k, h
  | .FPIsInfinite _, k, h | .FPIsNaN _, k, h | .FPIsNegative _, k, h | .FPIsPositive _, k, h
  | .FPIsNormal _, k, h | .FPIsSubnormal _, k, h | .Tuple _, k, h | .TupleSelect _ _, k, h
  | .FiniteSet _, k, h | .SetAdd _ _, k, h | .ElementOfSet _ _, k, h | .SubsetOf _ _, k, h
  | .SetIntersection _ _, k, h | .SetUnion _ _, k, h | .SetDifference _ _, k, h
  | .FiniteBag _, k, h | .BagAdd _ _, k, h | .MultiplicityInBag _ _, k, h
  | .BagIntersection _ _, k, h | .BagUnion _ _, k, h | .BagDifference _ _, k, h
  | .FiniteMap _ _, k, h | .MapApply _ _, k, h | .MapUpdated _ _ _, k, h
  | .MapMerge _ _ _, k, h => by
    simp [infer] at h

theorem inferAll_sound (S : List Sig) (Γ : List (Id × Ty)) :
    ∀ es : List Expr, inferAll S Γ es = true → ∀ e ∈ es, HasTy S Γ e .BooleanType
  | [], _ => fun e he => by cases he
  | a :: es, h => fun e he => by
    simp only [inferAll, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp he with he | he
    · rw [he]; exact infer_sound S Γ a true h.1
    · exact inferAll_sound S Γ es h.2 e he

theorem inferArgs_sound (S : List Sig) (Γ : List (Id × Ty)) :
    ∀ (es : List Expr) (Ts : List Ty), inferArgs S Γ es Ts = true →
      es.length = Ts.length ∧ ∀ p ∈ es.zip Ts, HasTy S Γ p.1 p.2
  | [], [], _ => ⟨rfl, fun p hp => by cases hp⟩
  | [], _ :: _, h => by simp [inferArgs] at h
  | _ :: _, [], h => by simp [inferArgs] at h
  | e :: es, T :: Ts, h => by
    simp only [inferArgs, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hsome, hk⟩, hrest⟩ := h
    obtain ⟨k, hek⟩ := Option.isSome_iff_exists.mp hsome
    have hT := kind_spec (hek ▸ hk).symm
    obtain ⟨hlen, hall⟩ := inferArgs_sound S Γ es Ts hrest
    refine ⟨by simp [hlen], fun p hp => ?_⟩
    rw [List.zip_cons_cons] at hp
    rcases List.mem_cons.mp hp with hp | hp
    · rw [hp, hT]; exact infer_sound S Γ e k hek
    · exact hall p hp
end

/-- An expression of the fragment is in the fragment of fuel monotonicity. -/
theorem HasTy.frag {S : List Sig} {Γ : List (Id × Ty)} {e : Expr} {T : Ty} (h : HasTy S Γ e T) :
    Frag e := by
  induction h with
  | var _ _ => exact .var
  | int _ => exact .int
  | bool _ => exact .bool
  | ite _ _ _ ihc iha ihb => exact .ite ihc iha ihb
  | and _ ih => exact .and ih
  | or _ ih => exact .or ih
  | not _ ih => exact .not ih
  | implies _ _ iha ihb => exact .implies iha ihb
  | equals _ _ iha ihb => exact .equals iha ihb
  | plus _ _ iha ihb => exact .plus iha ihb
  | minus _ _ iha ihb => exact .minus iha ihb
  | times _ _ iha ihb => exact .times iha ihb
  | div _ _ iha ihb => exact .div iha ihb
  | rem _ _ iha ihb => exact .rem iha ihb
  | mod _ _ iha ihb => exact .mod iha ihb
  | uminus _ ih => exact .uminus ih
  | lt _ _ iha ihb => exact .lt iha ihb
  | gt _ _ iha ihb => exact .gt iha ihb
  | le _ _ iha ihb => exact .le iha ihb
  | ge _ _ iha ihb => exact .ge iha ihb
  | @invoke s args _ hlen _ ih =>
    refine .invoke fun a ha => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    have hi' : i < (s.params.map Prod.snd).length := by rw [List.length_map, ← hlen]; exact hi
    exact ih (_, _) (List.mem_iff_getElem.mpr
      ⟨i, by rw [List.length_zip]; exact Nat.lt_min.mpr ⟨hi, hi'⟩, List.getElem_zip⟩)
  | assume _ _ ihp ihb => exact .assume ihp ihb

/-! ## The program and the query of a certificate -/

/-- The sort of the function that the head `f` of an application applies. -/
def headTy : SmtTerm → SmtType
  | .Apply f _ => headTy f
  | .UConst _ T => T
  | _ => .None

/-- The sort of the results of a function of sort `T` with `n` parameters. -/
def resultTy : Nat → SmtType → SmtType
  | 0, T => T
  | n + 1, .FunType _ R => resultTy n R
  | _ + 1, _ => .None

/-- The signature of the function that the equation `e` defines. -/
def sigOf (e : Equation) : Sig :=
  match __eo_to_smt e.term with
  | .eq lhs _ =>
    { name := backHead lhs, params := e.params.map fun p => (idOf p.1, tyOf p.2),
      ret := tyOf (resultTy e.params.length (headTy lhs)) }
  | _ => { name := "", params := [], ret := .UnitType }

/-- The body of the function that the equation `e` defines, with its assumptions when the
equation has its source. -/
def bodyOf (e : Equation) : Expr :=
  match __eo_to_smt (e.source.getD e.term) with
  | .eq _ rhs => back rhs
  | _ => .Error

/-- The function that the equation `e` defines. -/
def funOf (e : Equation) : FunDef :=
  .FunDef (sigOf e).name [] ((sigOf e).params.map Prod.fst) (bodyOf e)

/-- The signatures of the functions that the equations define. -/
def sigsOf (eqs : List Equation) : List Sig := eqs.map sigOf

/-- The program of the functions that the equations define. -/
def programOf (eqs : List Equation) : Program :=
  .Program (eqs.map funOf) [] [] [] .NoFunctionEquality

/-- The free variables of the base clauses: their constants, other than the functions of `S`. -/
def varsOf (S : List Sig) (base : List Term) : List (Id × Ty) :=
  (((base.flatMap fun t => consts (__eo_to_smt t)).eraseDups.map
    fun p => (idOf p.1, tyOf p.2)).filter fun p => S.all fun s => p.1 != s.name)

/-- The query: the expressions that the base clauses read as. -/
def queryOf (base : List Term) : List Expr := base.map fun t => back (__eo_to_smt t)

/-- The signatures `S` are of the fragment, with distinct names. -/
def sigCheck (S : List Sig) : Bool :=
  decide (S.map Sig.name).Nodup && S.all fun s =>
    (kind s.ret).isSome && decide (s.params.map Prod.fst).Nodup &&
      s.params.all fun p => (kind p.2).isSome && S.all fun s' => p.1 != s'.name

/-- The equation `e` is the translation of the function read from it, whose body is typed. -/
def eqCheck (S : List Sig) (e : Equation) : Bool :=
  let s := sigOf e
  decide (e.params = ptys s.params) &&
    decide (__eo_to_smt e.term = .eq
      (spine (.UConst (nm s.name) s.toDef.ty) ((ptys s.params).map fun q => .UConst q.1 q.2))
      (tr S s.params (bodyOf e))) &&
    (kind s.ret).isSome && decide (infer S s.params (bodyOf e) = kind s.ret)

/-- The variables `Γ` are of the fragment, and named after no function of `S`. -/
def varsCheck (S : List Sig) (Γ : List (Id × Ty)) : Bool :=
  Γ.all fun p => (kind p.2).isSome && S.all fun s => p.1 != s.name

/-- Each base clause is the translation of the expression read from it, which is a Boolean. -/
def baseCheck (S : List Sig) (Γ : List (Id × Ty)) (base : List Term) : Bool :=
  base.all fun t =>
    let q := back (__eo_to_smt t)
    decide (infer S Γ q = some true) && decide (__eo_to_smt t = tr S Γ q)

/-- The equations and the base clauses of `r` are the translations of the program and of the
query read from them, which are of the fragment. -/
def sourceCheck (r : TermSteps) : Bool :=
  let S := sigsOf r.equations
  let Γ := varsOf S r.base
  sigCheck S && r.equations.all (eqCheck S) && varsCheck S Γ && baseCheck S Γ r.base

theorem fragTy_of_kind {T : Ty} (h : (kind T).isSome = true) : FragTy T := by
  cases T <;> simp [kind] at h <;> trivial

theorem sigOk_of_check {S : List Sig} (h : sigCheck S = true) : SigOk S := by
  simp only [sigCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne] at h
  obtain ⟨hnd, hall⟩ := h
  exact
    { params := fun s hs p hp => fragTy_of_kind ((hall s hs).2 p hp).1
      ret := fun s hs => fragTy_of_kind (hall s hs).1.1
      nodup := hnd
      pnodup := fun s hs => (hall s hs).1.2
      fresh := fun s hs p hp s' hs' => ((hall s hs).2 p hp).2 s' hs' }

/-- The program of the equations has the function of each, when their names are distinct. -/
theorem lookup_funOf : ∀ {eqs : List Equation}, ((sigsOf eqs).map Sig.name).Nodup →
    ∀ e ∈ eqs, lookup_fun (eqs.map funOf) (sigOf e).name = .Ok (funOf e)
  | [], _, e, he => by cases he
  | a :: eqs, hnd, e, he => by
    simp only [sigsOf, List.map_cons, List.nodup_cons] at hnd
    rw [List.map_cons, lookup_fun]
    rcases List.mem_cons.mp he with rfl | he
    · simp [funOf]
    · have hne : (sigOf e).name ≠ (sigOf a).name := fun heq =>
        hnd.1 (heq ▸ List.mem_map_of_mem (List.mem_map_of_mem he))
      show (if _h : (sigOf e).name = (sigOf a).name then _ else _) = _
      split
      · rename_i heq; exact absurd heq hne
      · exact lookup_funOf hnd.2 e he

variable {O : Oracle}

/-- What the check gives for a function of the equations. -/
theorem eqCheck_spec {eqs : List Equation} (hS : sigCheck (sigsOf eqs) = true)
    {e : Equation} (he : e ∈ eqs) (h : eqCheck (sigsOf eqs) e = true) :
    EqFor (programOf eqs) (sigsOf eqs) (sigOf e) e := by
  simp only [eqCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hp, ht⟩, hk⟩, hi⟩ := h
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hk
  refine ⟨bodyOf e, lookup_funOf (sigOk_of_check hS).nodup e he, ?_, hp, ht⟩
  rw [kind_spec hk]
  exact infer_sound _ _ _ k (hi.trans hk)

theorem progTy_of_check {eqs : List Equation} (hS : sigCheck (sigsOf eqs) = true)
    (h : eqs.all (eqCheck (sigsOf eqs)) = true) : ProgTy (sigsOf eqs) (programOf eqs) := by
  intro s hs
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hs
  obtain ⟨body, hb, hty, _⟩ := eqCheck_spec hS he (List.all_eq_true.mp h e he)
  exact ⟨body, hb, hty⟩

theorem progFrag_of_check {eqs : List Equation} (hS : sigCheck (sigsOf eqs) = true)
    (h : eqs.all (eqCheck (sigsOf eqs)) = true) : ProgFrag (programOf eqs) := by
  intro g tps ps body hmem
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
  obtain ⟨body', hb, hty, _⟩ := eqCheck_spec hS he (List.all_eq_true.mp h e he)
  have hl := lookup_funOf (sigOk_of_check hS).nodup e he
  simp only [HasBody, programOf] at hb
  rw [hl, heq] at hb
  cases hb
  exact hty.frag

theorem varsFresh_of_check {S : List Sig} {Γ : List (Id × Ty)} (h : varsCheck S Γ = true) :
    VarsFresh S Γ := by
  simp only [varsCheck, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at h
  exact ⟨fun p hp => fragTy_of_kind (h p hp).1, fun p hp s hs => (h p hp).2 s hs⟩

theorem baseFor_of_check {S : List Sig} {Γ : List (Id × Ty)} {base : List Term}
    (h : baseCheck S Γ base = true) : BaseFor S Γ (queryOf base) base := by
  simp only [baseCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  intro t ht
  exact ⟨_, List.mem_map_of_mem ht, infer_sound S Γ _ true (h t ht).1, (h t ht).2⟩

/-- The query of an accepted certificate has no solution in the program of the certificate, when
the check of this file holds (`hsrc`) and every call of the program gives a value (`htot`), given
that the facts that the check of the certificate doesn't cover hold in the models of the defining
equations (`hfacts`). -/
theorem no_solution_of_check (sound : LogosSound) (hO : O.Sound) (hty : LogosTyping)
    {certificate : Logos.Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked) (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hkeeps : r.keeps = true) (hsrc : sourceCheck r = true)
    (htot : Total O (programOf r.equations) (sigsOf r.equations))
    (hfacts : FactsHoldExcept (Good r.equations) r.covered (extend r.base r.fresh) r.facts) :
    ∀ vs, ¬ Solution O (programOf r.equations) (varsOf (sigsOf r.equations) r.base)
      (queryOf r.base) vs := by
  simp only [sourceCheck, Bool.and_eq_true] at hsrc
  obtain ⟨⟨⟨hS, hE⟩, hΓ⟩, hB⟩ := hsrc
  exact no_solution sound hO hty (sigOk_of_check hS) (progFrag_of_check hS hE)
    (progTy_of_check hS hE) htot hAccept hr hcheck hkeeps
    (fun e he => ⟨sigOf e, List.mem_map_of_mem he,
      eqCheck_spec hS he (List.all_eq_true.mp hE e he)⟩)
    (varsFresh_of_check hΓ) (baseFor_of_check hB) hfacts

/-- As `no_solution_of_check`, for a certificate of which the check covers every fact
(`hcovered`): nothing is assumed of its clauses. -/
theorem no_solution_of_covered (sound : LogosSound) (hO : O.Sound) (hty : LogosTyping)
    {certificate : Logos.Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked) (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hkeeps : r.keeps = true) (hsrc : sourceCheck r = true)
    (hcovered : r.facts.all r.covered = true)
    (htot : Total O (programOf r.equations) (sigsOf r.equations)) :
    ∀ vs, ¬ Solution O (programOf r.equations) (varsOf (sigsOf r.equations) r.base)
      (queryOf r.base) vs :=
  no_solution_of_check sound hO hty hAccept hr hcheck hkeeps hsrc htot
    (factsHoldExcept_of_all hcovered)

end Inox.Bridge
