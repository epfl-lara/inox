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
  clause that of an expression of the query, which is read from the base clauses with the
  assumptions of the source expressions marked (`TermSteps.query`), and the names and the types
  are those of the fragment. It gives the hypotheses of `no_solution` on the program and the
  query (`no_solution_of_check`). When the check of the certificate covers every fact, nothing
  is assumed of its clauses (`no_solution_of_covered`).

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
  | .Datatype s _ => .ADTType (idOf s) []
  | _ => .UnitType

/-- The name that the constructor of index `i` of the datatype `s` is read with. Logos has no
names for the constructors and for the fields. -/
def ctorName (s : native_String) (i : Nat) : Id := idOf s ++ "#" ++ toString i

/-- The name that the field of index `j` of the constructor of index `i` of the datatype `s` is
read with. -/
def fieldName (s : native_String) (i j : Nat) : Id := ctorName s i ++ "." ++ toString j

/-- The constructor that the head `f` of an application applies, if it applies one. -/
def backCtor : SmtTerm → Option Id
  | .Apply f _ => backCtor f
  | .DtCons s _ i => some (ctorName s i)
  | _ => none

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
  | .DtCons s _ i => .ADT (ctorName s i) [] []
  | .Apply (.DtTester s _ i) a => .IsConstructor (back a) (ctorName s i)
  | .Apply (.DtSel s _ i j) a => .ADTSelector (back a) (fieldName s i j)
  | .Apply f a =>
    match backCtor f with
    | some c => .ADT c [] (backArgs f ++ [back a])
    | none => .FunctionInvocation (backHead f) [] (backArgs f ++ [back a])
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
  | .xor a b => consts a ++ consts b
  | .imp a b | .eq a b | .plus a b | .neg a b | .mult a b | .div a b | .mod a b | .lt a b
  | .gt a b | .leq a b | .geq a b | .and a b | .or a b => consts a ++ consts b
  | .Apply (.UConst _ _) a => consts a
  | .Apply f a => consts f ++ consts a
  | _ => []

/-! ## Typing -/

/-- The types of the fragment: the integers, the Booleans and the datatypes. -/
inductive K where
  | int
  | bool
  | data (s : Id)
  deriving DecidableEq

/-- The type of a kind. -/
def K.ty : K → Ty
  | .int => .IntegerType
  | .bool => .BooleanType
  | .data s => .ADTType s []

/-- The kind of a type of the fragment. -/
def kind (D : List Data) : Ty → Option K
  | .IntegerType => some .int
  | .BooleanType => some .bool
  | .ADTType s [] => if (findData D s).isSome then some (.data s) else none
  | _ => none

theorem kind_spec {D : List Data} {T : Ty} {k : K} (h : kind D T = some k) : T = k.ty := by
  cases T <;> try (simp [kind] at h; done)
  case IntegerType => simp only [kind, Option.some.injEq] at h; subst h; rfl
  case BooleanType => simp only [kind, Option.some.injEq] at h; subst h; rfl
  case ADTType s args =>
    cases args with
    | cons _ _ => simp [kind] at h
    | nil =>
      simp only [kind] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; rfl
      · cases h

theorem fragTy_of_kind {D : List Data} {T : Ty} (h : (kind D T).isSome = true) : FragTy D T := by
  cases T <;> try (simp [kind] at h; done)
  case IntegerType => trivial
  case BooleanType => trivial
  case ADTType s args =>
    cases args with
    | cons _ _ => simp [kind] at h
    | nil =>
      simp only [kind] at h
      split at h
      · rename_i hs; simpa [FragTy] using hs
      · cases h

theorem kind_data {D : List Data} (hD : DataOk D) {d : Data} (hd : d ∈ D) :
    kind D (.ADTType d.name []) = some (.data d.name) := by
  simp [kind, findData_of_mem hD.nodup hd]

mutual
/-- The kind of the type of `e`, if it is an expression of the fragment. -/
def infer (D : List Data) (S : List Sig) (Γ : List (Id × Ty)) : Expr → Option K
  | .Variable x => (Γ.lookup x).bind (kind D)
  | .IntegerLiteral _ => some .int
  | .BooleanLiteral _ => some .bool
  | .IfExpr c a b =>
    match infer D S Γ c, infer D S Γ a, infer D S Γ b with
    | some .bool, some k, some k' => if k = k' then some k else none
    | _, _, _ => none
  | .And es => if inferAll D S Γ es then some .bool else none
  | .Or es => if inferAll D S Γ es then some .bool else none
  | .Not a => if infer D S Γ a = some .bool then some .bool else none
  | .Implies a b =>
    if infer D S Γ a = some .bool ∧ infer D S Γ b = some .bool then some .bool else none
  | .Equals a b =>
    match infer D S Γ a, infer D S Γ b with
    | some k, some k' => if k = k' then some .bool else none
    | _, _ => none
  | .Plus a b | .Minus a b | .Times a b | .Division a b | .Remainder a b | .Modulo a b =>
    if infer D S Γ a = some .int ∧ infer D S Γ b = some .int then some .int else none
  | .UMinus a => if infer D S Γ a = some .int then some .int else none
  | .LessThan a b | .GreaterThan a b | .LessEquals a b | .GreaterEquals a b =>
    if infer D S Γ a = some .int ∧ infer D S Γ b = some .int then some .bool else none
  | .FunctionInvocation f [] args =>
    match findSig S f with
    | some s => if inferArgs D S Γ args (s.params.map Prod.snd) then kind D s.ret else none
    | none => none
  | .Assume p b => if infer D S Γ p = some .bool then infer D S Γ b else none
  | .ADT c [] args =>
    match findCtor D c with
    | some (d, _, fs) =>
      if inferArgs D S Γ args (fs.map Prod.snd) then some (.data d.name) else none
    | none => none
  | .IsConstructor a c =>
    match findCtor D c with
    | some (d, _, _) => if infer D S Γ a = some (.data d.name) then some .bool else none
    | none => none
  | .ADTSelector a x =>
    match findSel D x with
    | some (d, _, _, T) => if infer D S Γ a = some (.data d.name) then kind D T else none
    | none => none
  | _ => none

/-- The expressions `es` are Booleans. -/
def inferAll (D : List Data) (S : List Sig) (Γ : List (Id × Ty)) : List Expr → Bool
  | [] => true
  | e :: es => infer D S Γ e = some .bool && inferAll D S Γ es

/-- The arguments `es` are of the types `Ts`. -/
def inferArgs (D : List Data) (S : List Sig) (Γ : List (Id × Ty)) : List Expr → List Ty → Bool
  | [], [] => true
  | e :: es, T :: Ts => (infer D S Γ e).isSome && infer D S Γ e = kind D T && inferArgs D S Γ es Ts
  | _, _ => false
end

mutual
theorem infer_sound (hD : DataOk D) (S : List Sig) (Γ : List (Id × Ty)) :
    ∀ (e : Expr) (k : K), infer D S Γ e = some k → HasTy D S Γ e (k.ty)
  | .Variable x, k, h => by
    simp only [infer] at h
    cases hx : Γ.lookup x with
    | none => simp [hx] at h
    | some T =>
      simp only [hx, Option.bind_some] at h
      have := kind_spec h
      subst this
      exact .var hx (fragTy_of_kind (by rw [h]; rfl))
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
        exact .ite (infer_sound hD S Γ c .bool hc) (infer_sound hD S Γ a _ ha) (infer_sound hD S Γ
            b _ hb)
      · cases h
    · cases h
  | .And es, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hall
      simp only [Option.some.injEq] at h; subst h
      exact .and (inferAll_sound hD S Γ es hall)
    · cases h
  | .Or es, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hall
      simp only [Option.some.injEq] at h; subst h
      exact .or (inferAll_sound hD S Γ es hall)
    · cases h
  | .Not a, k, h => by
    simp only [infer] at h
    split at h
    · rename_i ha
      simp only [Option.some.injEq] at h; subst h
      exact .not (infer_sound hD S Γ a .bool ha)
    · cases h
  | .Implies a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .implies (infer_sound hD S Γ a .bool hab.1) (infer_sound hD S Γ b .bool hab.2)
    · cases h
  | .Equals a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i k1 k2 ha hb
      split at h
      · rename_i hk
        simp only [Option.some.injEq] at h
        subst hk; subst h
        exact .equals (infer_sound hD S Γ a _ ha) (infer_sound hD S Γ b _ hb)
      · cases h
    · cases h
  | .Plus a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .plus (infer_sound hD S Γ a .int hab.1) (infer_sound hD S Γ b .int hab.2)
    · cases h
  | .Minus a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .minus (infer_sound hD S Γ a .int hab.1) (infer_sound hD S Γ b .int hab.2)
    · cases h
  | .Times a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .times (infer_sound hD S Γ a .int hab.1) (infer_sound hD S Γ b .int hab.2)
    · cases h
  | .Division a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .div (infer_sound hD S Γ a .int hab.1) (infer_sound hD S Γ b .int hab.2)
    · cases h
  | .Remainder a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .rem (infer_sound hD S Γ a .int hab.1) (infer_sound hD S Γ b .int hab.2)
    · cases h
  | .Modulo a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .mod (infer_sound hD S Γ a .int hab.1) (infer_sound hD S Γ b .int hab.2)
    · cases h
  | .UMinus a, k, h => by
    simp only [infer] at h
    split at h
    · rename_i ha
      simp only [Option.some.injEq] at h; subst h
      exact .uminus (infer_sound hD S Γ a .int ha)
    · cases h
  | .LessThan a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .lt (infer_sound hD S Γ a .int hab.1) (infer_sound hD S Γ b .int hab.2)
    · cases h
  | .GreaterThan a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .gt (infer_sound hD S Γ a .int hab.1) (infer_sound hD S Γ b .int hab.2)
    · cases h
  | .LessEquals a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .le (infer_sound hD S Γ a .int hab.1) (infer_sound hD S Γ b .int hab.2)
    · cases h
  | .GreaterEquals a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hab
      simp only [Option.some.injEq] at h; subst h
      exact .ge (infer_sound hD S Γ a .int hab.1) (infer_sound hD S Γ b .int hab.2)
    · cases h
  | .FunctionInvocation f [] args, k, h => by
    simp only [infer] at h
    split at h
    · rename_i s hs
      split at h
      · rename_i hargs
        obtain ⟨_, rfl⟩ := findSig_spec hs
        have hr := kind_spec h
        obtain ⟨hlen, hall⟩ := inferArgs_sound hD S Γ args _ hargs
        rw [← hr]
        exact .invoke hs (by simpa using hlen) hall
      · cases h
    · cases h
  | .FunctionInvocation f (_ :: _) args, k, h => by simp [infer] at h
  | .Assume p b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hp
      exact .assume (infer_sound hD S Γ p .bool hp) (infer_sound hD S Γ b k h)
    · cases h
  | .ADT c [] args, k, h => by
    simp only [infer] at h
    split at h
    · rename_i d i fs hc
      split at h
      · rename_i hargs
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨hlen, hall⟩ := inferArgs_sound hD S Γ args _ hargs
        exact .adt hc (by simpa using hlen) hall
      · cases h
    · cases h
  | .ADT c (_ :: _) args, k, h => by simp [infer] at h
  | .IsConstructor a c, k, h => by
    simp only [infer] at h
    split at h
    · rename_i d i fs hc
      split at h
      · rename_i ha
        simp only [Option.some.injEq] at h; subst h
        exact .isCons hc (infer_sound hD S Γ a _ ha)
      · cases h
    · cases h
  | .ADTSelector a x, k, h => by
    simp only [infer] at h
    split at h
    · rename_i d i j T hx
      split at h
      · rename_i ha
        rw [← kind_spec h]
        exact .sel hx (infer_sound hD S Γ a _ ha)
      · cases h
    · cases h
  | .Let _ _ _, k, h | .Application _ _, k, h | .Lambda _ _, k, h
  | .Forall _ _, k, h | .UninterpretedCall _ _ _, k, h | .Error, k, h | .CharLiteral _, k, h
  | .BVLiteral _ _ _, k, h | .FractionLiteral _ _, k, h | .FPLiteral _ _ _, k, h
  | .StringLiteral _, k, h | .UnitLiteral, k, h | .RoundNearestTiesToEven, k, h
  | .RoundNearestTiesToAway, k, h | .RoundTowardPositive, k, h | .RoundTowardNegative, k, h
  | .RoundTowardZero, k, h
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

theorem inferAll_sound (hD : DataOk D) (S : List Sig) (Γ : List (Id × Ty)) :
    ∀ es : List Expr, inferAll D S Γ es = true → ∀ e ∈ es, HasTy D S Γ e .BooleanType
  | [], _ => fun e he => by cases he
  | a :: es, h => fun e he => by
    simp only [inferAll, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp he with he | he
    · rw [he]; exact infer_sound hD S Γ a .bool h.1
    · exact inferAll_sound hD S Γ es h.2 e he

theorem inferArgs_sound (hD : DataOk D) (S : List Sig) (Γ : List (Id × Ty)) :
    ∀ (es : List Expr) (Ts : List Ty), inferArgs D S Γ es Ts = true →
      es.length = Ts.length ∧ ∀ p ∈ es.zip Ts, HasTy D S Γ p.1 p.2
  | [], [], _ => ⟨rfl, fun p hp => by cases hp⟩
  | [], _ :: _, h => by simp [inferArgs] at h
  | _ :: _, [], h => by simp [inferArgs] at h
  | e :: es, T :: Ts, h => by
    simp only [inferArgs, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hsome, hk⟩, hrest⟩ := h
    obtain ⟨k, hek⟩ := Option.isSome_iff_exists.mp hsome
    have hT := kind_spec (hek ▸ hk).symm
    obtain ⟨hlen, hall⟩ := inferArgs_sound hD S Γ es Ts hrest
    refine ⟨by simp [hlen], fun p hp => ?_⟩
    rw [List.zip_cons_cons] at hp
    rcases List.mem_cons.mp hp with hp | hp
    · rw [hp, hT]; exact infer_sound hD S Γ e k hek
    · exact hall p hp
end

/-- An expression of the fragment is in the fragment of fuel monotonicity. -/
theorem HasTy.frag {S : List Sig} {Γ : List (Id × Ty)} {e : Expr} {T : Ty} (h : HasTy D S Γ e T) :
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
  | @adt c d i fs args _ hlen _ ih =>
    refine .adt fun a ha => ?_
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp ha
    have hn' : n < (fs.map Prod.snd).length := by rw [List.length_map, ← hlen]; exact hn
    exact ih (_, _) (List.mem_iff_getElem.mpr
      ⟨n, by rw [List.length_zip]; exact Nat.lt_min.mpr ⟨hn, hn'⟩, List.getElem_zip⟩)
  | isCons _ _ ih => exact .isCons ih
  | sel _ _ ih => exact .select ih

/-! ## The datatypes of a certificate -/

/-- The datatypes that the declaration `dd0` declares, from those of `dd` on. -/
def declNames (dd0 : SmtDatatypeDecl) : SmtDatatypeDecl → List (native_String × SmtDatatypeDecl)
  | .nil => []
  | .cons s _ dd => (s, dd0) :: declNames dd0 dd

mutual
/-- The datatypes that the sort `T` mentions, each with its declaration. -/
def declsOfType : SmtType → List (native_String × SmtDatatypeDecl)
  | .Datatype _ dd => declNames dd dd ++ declsOfDecl dd
  | .FunType A B => declsOfType A ++ declsOfType B
  | _ => []

def declsOfDecl : SmtDatatypeDecl → List (native_String × SmtDatatypeDecl)
  | .nil => []
  | .cons _ d dd => declsOfDt d ++ declsOfDecl dd

def declsOfDt : SmtDatatype → List (native_String × SmtDatatypeDecl)
  | .null => []
  | .sum c d => declsOfCons c ++ declsOfDt d

def declsOfCons : SmtDatatypeCons → List (native_String × SmtDatatypeDecl)
  | .unit => []
  | .cons T c => declsOfType T ++ declsOfCons c
end

/-- The sorts that `t` mentions: those of its constants, and the datatypes of its constructors,
testers and selectors. -/
def typesOf : SmtTerm → List SmtType
  | .UConst _ T => [T]
  | .DtCons s dd _ | .DtSel s dd _ _ | .DtTester s dd _ => [.Datatype s dd]
  | .ite c a b => typesOf c ++ typesOf a ++ typesOf b
  | .not a | .uneg a => typesOf a
  | .xor a b | .imp a b | .eq a b | .plus a b | .neg a b | .mult a b | .div a b | .mod a b
  | .lt a b | .gt a b | .leq a b | .geq a b | .and a b | .or a b | .Apply a b =>
    typesOf a ++ typesOf b
  | _ => []

/-- The fields of a constructor of the datatype `s`, of index `i`, from the field of index `j`
on. -/
def fieldsOfCons (s : native_String) (i : Nat) : SmtDatatypeCons → Nat → List (Id × Ty)
  | .unit, _ => []
  | .cons U c, j => (fieldName s i j, tyOf U) :: fieldsOfCons s i c (j + 1)

/-- The constructors of the datatype `s`, from the constructor of index `i` on. -/
def ctorsOfDt (s : native_String) : SmtDatatype → Nat → List (Id × List (Id × Ty))
  | .null, _ => []
  | .sum c d, i => (ctorName s i, fieldsOfCons s i c 0) :: ctorsOfDt s d (i + 1)

/-- The datatype `p.1` of the declaration `p.2`, with the names that its constructors and their
fields are read with. -/
def dataOfDecl (p : native_String × SmtDatatypeDecl) : Data where
  name := idOf p.1
  decl := p.2
  ctors := ctorsOfDt p.1 (__smtx_dt_resolve (__smtx_dd_lookup p.1 p.2) p.2) 0

/-- The datatypes that the terms `ts` and the sorts `Ts` mention. -/
def datasOf (ts : List SmtTerm) (Ts : List SmtType) : List Data :=
  ((ts.flatMap typesOf ++ Ts).flatMap declsOfType).eraseDups.map dataOfDecl

/-- The datatypes are as the bridge asks (`DataOk`). -/
def dataCheck (D : List Data) : Bool :=
  decide (D.map (·.name)).Nodup &&
    decide (D.flatMap fun d => d.ctors.map (·.1)).Nodup &&
    decide (D.flatMap fun d => d.ctors.flatMap fun c => c.2.map (·.1)).Nodup &&
    (D.all fun d => d.ctors.all fun c => c.2.all fun f => (kind D f.2).isSome) &&
    D.all fun d =>
      decide (__smtx_dt_resolve (__smtx_dd_lookup (nm d.name) d.decl) d.decl =
        sumT D d.ctors) &&
      __smtx_type_wf (.Datatype (nm d.name) d.decl)

theorem dataOk_of_check {D : List Data} (h : dataCheck D = true) : DataOk D := by
  simp only [dataCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hn, hc⟩, hs⟩, hf⟩, hr⟩ := h
  exact
    { nodup := hn
      ctors := hc
      sels := hs
      fields := fun d hd c hc f hf' => fragTy_of_kind (hf d hd c hc f hf')
      resolved := fun d hd => (hr d hd).1
      wf := fun d hd => (hr d hd).2 }

/-- The constructors of the datatype `d`, as those of a program. -/
def ctorsOfData (d : Data) : List Constructor :=
  d.ctors.map fun c => .Constructor c.1 d.name (c.2.map fun f => .Param f.1 f.2)

theorem lookup_ctor_data (name : Id) (rest : List Constructor) (c : Id) :
    ∀ cs : List (Id × List (Id × Ty)),
      lookup_ctor ((cs.map fun k => Constructor.Constructor k.1 name
        (k.2.map fun f => .Param f.1 f.2)) ++ rest) c =
      match lookupIdx c cs with
      | some r => .Ok (.Constructor c name (r.2.map fun f => .Param f.1 f.2))
      | none => lookup_ctor rest c
  | [] => by simp [lookupIdx]
  | k :: cs => by
    rw [List.map_cons, List.cons_append, lookup_ctor]
    by_cases hk : c = k.1
    · subst hk
      simp [lookupIdx]
    · rw [dite_eq_right_of_eq_false (eq_false hk), lookup_ctor_data name rest c cs]
      have hk' : ¬k.1 = c := fun e => hk e.symm
      simp only [lookupIdx, hk', ↓reduceIte]
      cases lookupIdx c cs <;> rfl

theorem lookup_ctor_of : ∀ {D : List Data} {c : Id} {d : Data} {i : Nat} {fs : List (Id × Ty)},
    findCtor D c = some (d, i, fs) →
    lookup_ctor (D.flatMap ctorsOfData) c =
      .Ok (.Constructor c d.name (fs.map fun f => .Param f.1 f.2))
  | [], _, _, _, _, h => by cases h
  | a :: D, c, d, i, fs, h => by
    rw [List.flatMap_cons, ctorsOfData, lookup_ctor_data]
    simp only [findCtor, List.findSome?_cons, ctorIn] at h
    cases hl : lookupIdx c a.ctors with
    | some r =>
      simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | none =>
      simp only [hl, Option.map_none] at h
      exact lookup_ctor_of h

theorem lookup_sort_of : ∀ {D : List Data} {d : Data}, d ∈ D →
    lookup_sort (D.map fun d => ADTSort.Sort d.name [] none) d.name = .Ok (.Sort d.name [] none)
  | [], _, h => by cases h
  | a :: D, d, h => by
    rw [List.map_cons, lookup_sort]
    by_cases hn : d.name = a.name
    · rw [dite_eq_left_of_eq_true (eq_true hn), hn]
    · rw [dite_eq_right_of_eq_false (eq_false hn)]
      rcases List.mem_cons.mp h with rfl | h'
      · exact absurd rfl hn
      · exact lookup_sort_of h'

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

/-- The datatypes of the certificate: those that its equations, with the sorts of their
parameters, its base clauses and its query mention. -/
def dataOf (r : TermSteps) : List Data :=
  datasOf
    ((r.equations.flatMap fun e =>
        __eo_to_smt e.term :: (e.source.map __eo_to_smt).toList) ++
      (r.base ++ r.query).map __eo_to_smt)
    (r.equations.flatMap fun e => e.params.map (·.2))

/-- The program of the functions that the equations define, with the datatypes `D`, which have no
type parameters and no invariants. -/
def programOf (D : List Data) (eqs : List Equation) : Program :=
  .Program (eqs.map funOf) (D.flatMap ctorsOfData) (D.map fun d => .Sort d.name [] none) []
    .NoFunctionEquality

theorem progData_programOf (D : List Data) (eqs : List Equation) :
    ProgData D (programOf D eqs) := by
  intro c d i fs h
  exact ⟨lookup_ctor_of h, lookup_sort_of (findCtor_spec h).1⟩

/-- The free variables of the clauses `base`: their constants, other than the functions of `S`. -/
def varsOf (S : List Sig) (base : List Term) : List (Id × Ty) :=
  (((base.flatMap fun t => consts (__eo_to_smt t)).eraseDups.map
    fun p => (idOf p.1, tyOf p.2)).filter fun p => S.all fun s => p.1 != s.name)

/-- The query: the expressions that the clauses `query` read as, which are the base clauses with
the assumptions of the source expressions marked (`TermSteps.query`). -/
def queryOf (query : List Term) : List Expr := query.map fun t => back (__eo_to_smt t)

/-- The signatures `S` are of the fragment, with distinct names. -/
def sigCheck (D : List Data) (S : List Sig) : Bool :=
  decide (S.map Sig.name).Nodup && S.all fun s =>
    (kind D s.ret).isSome && decide (s.params.map Prod.fst).Nodup &&
      s.params.all fun p => (kind D p.2).isSome && S.all fun s' => p.1 != s'.name

/-- The equation `e` is the translation of the function read from it, whose body is typed. -/
def eqCheck (D : List Data) (S : List Sig) (e : Equation) : Bool :=
  let s := sigOf e
  decide (e.params = ptys D s.params) &&
    decide (__eo_to_smt e.term = .eq
      (spine (.UConst (nm s.name) (s.toDef D).ty)
        ((ptys D s.params).map fun q => .UConst q.1 q.2))
      (tr D S s.params (bodyOf e))) &&
    (kind D s.ret).isSome && decide (infer D S s.params (bodyOf e) = kind D s.ret)

/-- The variables `Γ` are of the fragment, and named after no function of `S`. -/
def varsCheck (D : List Data) (S : List Sig) (Γ : List (Id × Ty)) : Bool :=
  Γ.all fun p => (kind D p.2).isSome && S.all fun s => p.1 != s.name

/-- Each expression of the query is a Boolean, and each base clause is the translation of one,
which leaves its assumptions out. -/
def baseCheck (D : List Data) (S : List Sig) (Γ : List (Id × Ty)) (base query : List Term) :
    Bool :=
  (query.all fun s => decide (infer D S Γ (back (__eo_to_smt s)) = some .bool)) &&
    base.all fun t => query.any fun s =>
      decide (__eo_to_smt t = tr D S Γ (back (__eo_to_smt s)))

/-- The equations and the base clauses of `r` are the translations of the program and of the
query read from them, which are of the fragment, with the datatypes that they mention. -/
def sourceCheck (r : TermSteps) : Bool :=
  let D := dataOf r
  let S := sigsOf r.equations
  let Γ := varsOf S r.query
  dataCheck D && sigCheck D S && r.equations.all (eqCheck D S) && varsCheck D S Γ &&
    baseCheck D S Γ r.base r.query

theorem sigOk_of_check {D : List Data} (hD : DataOk D) {S : List Sig}
    (h : sigCheck D S = true) : SigOk D S := by
  simp only [sigCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne] at h
  obtain ⟨hnd, hall⟩ := h
  exact
    { data := hD
      params := fun s hs p hp => fragTy_of_kind ((hall s hs).2 p hp).1
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

variable {O : Oracle} {D : List Data}

/-- What the check gives for a function of the equations. -/
theorem eqCheck_spec (hD : DataOk D) {eqs : List Equation}
    (hS : sigCheck D (sigsOf eqs) = true) {e : Equation} (he : e ∈ eqs)
    (h : eqCheck D (sigsOf eqs) e = true) :
    EqFor (programOf D eqs) D (sigsOf eqs) (sigOf e) e := by
  simp only [eqCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hp, ht⟩, hk⟩, hi⟩ := h
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hk
  refine ⟨bodyOf e, lookup_funOf (sigOk_of_check hD hS).nodup e he, ?_, hp, ht⟩
  rw [kind_spec hk]
  exact infer_sound hD _ _ _ k (hi.trans hk)

theorem progTy_of_check (hD : DataOk D) {eqs : List Equation}
    (hS : sigCheck D (sigsOf eqs) = true) (h : eqs.all (eqCheck D (sigsOf eqs)) = true) :
    ProgTy D (sigsOf eqs) (programOf D eqs) := by
  refine ⟨fun s hs => ?_, progData_programOf D eqs⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hs
  obtain ⟨body, hb, hty, _⟩ := eqCheck_spec hD hS he (List.all_eq_true.mp h e he)
  exact ⟨body, hb, hty⟩

theorem progFrag_of_check (hD : DataOk D) {eqs : List Equation}
    (hS : sigCheck D (sigsOf eqs) = true) (h : eqs.all (eqCheck D (sigsOf eqs)) = true) :
    ProgFrag (programOf D eqs) := by
  intro g tps ps body hmem
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
  obtain ⟨body', hb, hty, _⟩ := eqCheck_spec hD hS he (List.all_eq_true.mp h e he)
  have hl := lookup_funOf (sigOk_of_check hD hS).nodup e he
  simp only [HasBody, programOf] at hb
  rw [hl, heq] at hb
  cases hb
  exact hty.frag

theorem varsFresh_of_check {S : List Sig} {Γ : List (Id × Ty)} (h : varsCheck D S Γ = true) :
    VarsFresh D S Γ := by
  simp only [varsCheck, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at h
  exact ⟨fun p hp => fragTy_of_kind (h p hp).1, fun p hp s hs => (h p hp).2 s hs⟩

theorem baseFor_of_check (hD : DataOk D) {S : List Sig} {Γ : List (Id × Ty)}
    {base query : List Term} (h : baseCheck D S Γ base query = true) :
    BaseFor D S Γ (queryOf query) base := by
  simp only [baseCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true] at h
  intro t ht
  obtain ⟨s, hs, hts⟩ := h.2 t ht
  exact ⟨_, List.mem_map_of_mem hs, infer_sound hD S Γ _ .bool (h.1 s hs), hts⟩

/-- The expressions of the query are Booleans. -/
theorem query_ty_of_check (hD : DataOk D) {S : List Sig} {Γ : List (Id × Ty)}
    {base query : List Term} (h : baseCheck D S Γ base query = true) :
    ∀ q ∈ queryOf query, HasTy D S Γ q .BooleanType := by
  simp only [baseCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  intro q hq
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
  exact infer_sound hD S Γ _ .bool (h.1 s hs)

/-- The query of an accepted certificate has no solution in the program of the certificate, when
the check of this file holds (`hsrc`) and every call of the program gives a value (`htot`), given
that the facts that the check of the certificate doesn't cover hold in the models of the defining
equations (`hfacts`). -/
theorem no_solution_of_check (sound : LogosSound) (hO : O.Sound) (hty : LogosTyping)
    {certificate : Logos.Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked) (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hkeeps : r.keeps = true) (hsrc : sourceCheck r = true)
    (htot : Total O (programOf (dataOf r) r.equations) (dataOf r) (sigsOf r.equations))
    (hfacts : FactsHoldExcept (Good r.equations) r.covered (extend r.base r.fresh) r.facts) :
    ∀ vs, ¬ Solution O (programOf (dataOf r) r.equations) (dataOf r)
      (varsOf (sigsOf r.equations) r.query) (queryOf r.query) vs := by
  simp only [sourceCheck, Bool.and_eq_true] at hsrc
  obtain ⟨⟨⟨⟨hD, hS⟩, hE⟩, hΓ⟩, hB⟩ := hsrc
  have hD := dataOk_of_check hD
  exact no_solution sound hO hty (sigOk_of_check hD hS) (progFrag_of_check hD hS hE)
    (progTy_of_check hD hS hE) htot hAccept hr hcheck hkeeps
    (fun e he => ⟨sigOf e, List.mem_map_of_mem he,
      eqCheck_spec hD hS he (List.all_eq_true.mp hE e he)⟩)
    (varsFresh_of_check hΓ) (baseFor_of_check hD hB) hfacts

/-- As `no_solution_of_check`, for a certificate of which the check covers every fact
(`hcovered`): nothing is assumed of its clauses. -/
theorem no_solution_of_covered (sound : LogosSound) (hO : O.Sound) (hty : LogosTyping)
    {certificate : Logos.Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked) (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hkeeps : r.keeps = true) (hsrc : sourceCheck r = true)
    (hcovered : r.facts.all r.covered = true)
    (htot : Total O (programOf (dataOf r) r.equations) (dataOf r) (sigsOf r.equations)) :
    ∀ vs, ¬ Solution O (programOf (dataOf r) r.equations) (dataOf r)
      (varsOf (sigsOf r.equations) r.query) (queryOf r.query) vs :=
  no_solution_of_check sound hO hty hAccept hr hcheck hkeeps hsrc htot
    (factsHoldExcept_of_all hcovered)

end Inox.Bridge
