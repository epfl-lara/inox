/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.NoSolution

/-!
# The program and the query of a certificate, on a first-order fragment

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
  | .BitVec n => .BVType false n
  | .Real => .RealType
  | .Set T => .SetType (tyOf T)
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

/-- The width of the term `t`, when it is a bit-vector. -/
def widthOf (t : SmtTerm) : Int :=
  match __smtx_typeof t with
  | .BitVec n => n
  | _ => 0

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
  | .qdiv (.Numeral n) (.Numeral d) => .FractionLiteral n d
  | .qdiv (.uneg (.Numeral n)) (.Numeral d) => .FractionLiteral (-n) d
  | .qdiv a b => .Division (back a) (back b)
  | .mod a b => .Modulo (back a) (back b)
  | .uneg a => .UMinus (back a)
  | .lt a b => .LessThan (back a) (back b)
  | .gt a b => .GreaterThan (back a) (back b)
  | .leq a b => .LessEquals (back a) (back b)
  | .geq a b => .GreaterEquals (back a) (back b)
  | .Binary w x => .BVLiteral false w x
  | .bvadd a b => .Plus (back a) (back b)
  | .bvsub a b => .Minus (back a) (back b)
  | .bvmul a b => .Times (back a) (back b)
  | .bvudiv a b => .Division (back a) (back b)
  | .bvurem a b => .Remainder (back a) (back b)
  | .bvneg a => .UMinus (back a)
  | .bvnot a => .BVNot (back a)
  | .bvult a b => .LessThan (back a) (back b)
  | .bvugt a b => .GreaterThan (back a) (back b)
  | .bvule a b => .LessEquals (back a) (back b)
  | .bvuge a b => .GreaterEquals (back a) (back b)
  | .bvsdiv a b =>
    .BVSignedToUnsigned
      (.Division (.BVUnsignedToSigned (back a)) (.BVUnsignedToSigned (back b)))
  | .bvsrem a b =>
    .BVSignedToUnsigned
      (.Remainder (.BVUnsignedToSigned (back a)) (.BVUnsignedToSigned (back b)))
  | .bvsmod a b =>
    .BVSignedToUnsigned
      (.Modulo (.BVUnsignedToSigned (back a)) (.BVUnsignedToSigned (back b)))
  | .bvslt a b => .LessThan (.BVUnsignedToSigned (back a)) (.BVUnsignedToSigned (back b))
  | .bvsgt a b => .GreaterThan (.BVUnsignedToSigned (back a)) (.BVUnsignedToSigned (back b))
  | .bvsle a b => .LessEquals (.BVUnsignedToSigned (back a)) (.BVUnsignedToSigned (back b))
  | .bvsge a b => .GreaterEquals (.BVUnsignedToSigned (back a)) (.BVUnsignedToSigned (back b))
  | .bvand a b => .BVAnd (back a) (back b)
  | .bvor a b => .BVOr (back a) (back b)
  | .bvxor a b => .BVXor (back a) (back b)
  | .bvshl a b => .BVShiftLeft (back a) (back b)
  | .bvashr a b => .BVAShiftRight (back a) (back b)
  | .bvlshr a b => .BVLShiftRight (back a) (back b)
  | .extract (.Numeral i) (.Numeral 0) a => .BVNarrowingCast (back a) (i + 1)
  | .zero_extend (.Numeral k) a => .BVWideningCast (back a) (k + widthOf a)
  | .sign_extend (.Numeral k) a =>
    .BVSignedToUnsigned (.BVWideningCast (.BVUnsignedToSigned (back a)) (k + widthOf a))
  | .and a r => .And (back a :: backAnd r)
  | .or a r => .Or (back a :: backOr r)
  | .set_empty T => .FiniteSet [] (tyOf T)
  | .set_singleton a => .FiniteSet [back a] (tyOf (__smtx_typeof a))
  | .set_union (.set_singleton a) s => .SetAdd (back s) (back a)
  | .set_union a b => .SetUnion (back a) (back b)
  | .set_inter a b => .SetIntersection (back a) (back b)
  | .set_minus a b => .SetDifference (back a) (back b)
  | .set_member a s => .ElementOfSet (back a) (back s)
  | .set_subset a b => .SubsetOf (back a) (back b)
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
  | .not a | .uneg a | .bvneg a | .bvnot a | .extract _ _ a | .zero_extend _ a
  | .sign_extend _ a | .set_singleton a => consts a
  | .xor a b => consts a ++ consts b
  | .imp a b | .eq a b | .plus a b | .neg a b | .mult a b | .div a b | .mod a b | .lt a b
  | .gt a b | .leq a b | .geq a b | .and a b | .or a b | .bvadd a b | .bvsub a b | .bvmul a b
  | .bvudiv a b | .bvurem a b | .bvult a b | .bvugt a b | .bvule a b | .bvuge a b
  | .qdiv a b | .bvsdiv a b | .bvsrem a b | .bvsmod a b | .bvslt a b | .bvsgt a b | .bvsle a b
  | .bvsge a b | .bvand a b | .bvor a b | .bvxor a b | .bvshl a b | .bvashr a b
  | .bvlshr a b | .set_union a b | .set_inter a b | .set_minus a b | .set_member a b
  | .set_subset a b => consts a ++ consts b
  | .Apply (.UConst _ _) a => consts a
  | .Apply f a => consts f ++ consts a
  | _ => []

/-! ## Typing -/

/-- The types of the fragment: the integers, the Booleans, the reals, the bit-vectors, the
datatypes, and the sets of these. -/
inductive K where
  | int
  | bool
  | real
  | bv (s : Bool) (w : Int)
  | data (s : Id)
  | set (k : K)
  deriving DecidableEq

/-- The type of a kind. -/
def K.ty : K → Ty
  | .int => .IntegerType
  | .bool => .BooleanType
  | .real => .RealType
  | .bv s w => .BVType s w
  | .data s => .ADTType s []
  | .set k => .SetType k.ty

/-- The kind of a type of the fragment. -/
def kind (D : List Data) : Ty → Option K
  | .IntegerType => some .int
  | .BooleanType => some .bool
  | .RealType => some .real
  | .BVType s w => if 0 < w then some (.bv s w) else none
  | .ADTType s [] => if (findData D s).isSome then some (.data s) else none
  | .SetType A => (kind D A).map .set
  | _ => none

theorem kind_spec' {D : List Data} : ∀ (T : Ty) (k : K), kind D T = some k → T = k.ty
  | .IntegerType, k, h => by simp only [kind, Option.some.injEq] at h; subst h; rfl
  | .BooleanType, k, h => by simp only [kind, Option.some.injEq] at h; subst h; rfl
  | .RealType, k, h => by simp only [kind, Option.some.injEq] at h; subst h; rfl
  | .BVType s w, k, h => by
    simp only [kind] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · cases h
  | .ADTType s [], k, h => by
    simp only [kind] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · cases h
  | .SetType A, k, h => by
    simp only [kind, Option.map_eq_some_iff] at h
    obtain ⟨k', hk, rfl⟩ := h
    simp only [K.ty, ← kind_spec' A k' hk]
  | .ADTType _ (_ :: _), _, h | .UnitType, _, h | .CharType, _, h | .StringType, _, h
  | .FPType _ _, _, h | .RoundingModeType, _, h | .TypeParameter _, _, h | .TupleType _, _, h
  | .BagType _, _, h | .MapType _ _, _, h | .FunctionType _ _, _, h
  | .RefinementType _ _ _, _, h | .PropType, _, h | .PiType _ _, _, h
  | .SigmaType _ _, _, h => by simp [kind] at h

theorem kind_spec {D : List Data} {T : Ty} {k : K} (h : kind D T = some k) : T = k.ty :=
  kind_spec' T k h

theorem fragTy_of_kind' {D : List Data} : ∀ T : Ty, (kind D T).isSome = true → FragTy D T
  | .IntegerType, _ => trivial
  | .BooleanType, _ => trivial
  | .RealType, _ => trivial
  | .BVType s w, h => by
    simp only [kind] at h
    split at h
    · rename_i hw; exact hw
    · cases h
  | .ADTType s [], h => by
    simp only [kind] at h
    split at h
    · rename_i hs; simpa [FragTy] using hs
    · cases h
  | .SetType A, h => by
    simp only [kind, Option.isSome_map] at h
    exact fragTy_of_kind' A h
  | .ADTType _ (_ :: _), h | .UnitType, h | .CharType, h | .StringType, h
  | .FPType _ _, h | .RoundingModeType, h | .TypeParameter _, h | .TupleType _, h
  | .BagType _, h | .MapType _ _, h | .FunctionType _ _, h
  | .RefinementType _ _ _, h | .PropType, h | .PiType _ _, h
  | .SigmaType _ _, h => by simp [kind] at h

theorem fragTy_of_kind {D : List Data} {T : Ty} (h : (kind D T).isSome = true) : FragTy D T :=
  fragTy_of_kind' T h

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
  | .BVLiteral s w x =>
    if 0 < w ∧ 0 ≤ x ∧ x < 2 ^ w.toNat then some (.bv s w) else none
  | .FractionLiteral _ d => if d ≠ 0 then some .real else none
  | .Plus a b | .Minus a b | .Times a b | .Division a b =>
    match infer D S Γ a, infer D S Γ b with
    | some .int, some .int => some .int
    | some (.bv s w), some (.bv s' w') => if s = s' ∧ w = w' then some (.bv s w) else none
    | some .real, some .real => some .real
    | _, _ => none
  | .Remainder a b =>
    match infer D S Γ a, infer D S Γ b with
    | some .int, some .int => some .int
    | some (.bv s w), some (.bv s' w') => if s = s' ∧ w = w' then some (.bv s w) else none
    | _, _ => none
  | .Modulo a b =>
    match infer D S Γ a, infer D S Γ b with
    | some .int, some .int => some .int
    | some (.bv s w), some (.bv s' w') => if s = s' ∧ w = w' then some (.bv s w) else none
    | _, _ => none
  | .BVUnsignedToSigned a =>
    match infer D S Γ a with
    | some (.bv false w) => some (.bv true w)
    | _ => none
  | .BVSignedToUnsigned a =>
    match infer D S Γ a with
    | some (.bv true w) => some (.bv false w)
    | _ => none
  | .UMinus a =>
    match infer D S Γ a with
    | some .int => some .int
    | some (.bv s w) => some (.bv s w)
    | some .real => some .real
    | _ => none
  | .BVNot a =>
    match infer D S Γ a with
    | some (.bv s w) => some (.bv s w)
    | _ => none
  | .BVAnd a b | .BVOr a b | .BVXor a b | .BVShiftLeft a b | .BVAShiftRight a b
  | .BVLShiftRight a b =>
    match infer D S Γ a, infer D S Γ b with
    | some (.bv s w), some (.bv s' w') => if s = s' ∧ w = w' then some (.bv s w) else none
    | _, _ => none
  | .BVNarrowingCast a v =>
    match infer D S Γ a with
    | some (.bv s w) => if 0 < v ∧ v < w then some (.bv s v) else none
    | _ => none
  | .BVWideningCast a v =>
    match infer D S Γ a with
    | some (.bv s w) => if w < v then some (.bv s v) else none
    | _ => none
  | .LessThan a b | .GreaterThan a b | .LessEquals a b | .GreaterEquals a b =>
    match infer D S Γ a, infer D S Γ b with
    | some .int, some .int => some .bool
    | some (.bv s w), some (.bv s' w') => if s = s' ∧ w = w' then some .bool else none
    | some .real, some .real => some .bool
    | _, _ => none
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
  | .FiniteSet es A =>
    match kind D A with
    | some k =>
      if es.length ≤ 1 ∧ inferArgs D S Γ es (es.map fun _ => A) = true then some (.set k)
      else none
    | none => none
  | .SetAdd s a =>
    match infer D S Γ s, infer D S Γ a with
    | some (.set k), some k' => if k = k' then some (.set k) else none
    | _, _ => none
  | .ElementOfSet a s =>
    match infer D S Γ a, infer D S Γ s with
    | some k', some (.set k) => if k = k' then some .bool else none
    | _, _ => none
  | .SubsetOf s u =>
    match infer D S Γ s, infer D S Γ u with
    | some (.set k), some (.set k') => if k = k' then some .bool else none
    | _, _ => none
  | .SetUnion s u | .SetIntersection s u | .SetDifference s u =>
    match infer D S Γ s, infer D S Γ u with
    | some (.set k), some (.set k') => if k = k' then some (.set k) else none
    | _, _ => none
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
    · rename_i ha hb
      simp only [Option.some.injEq] at h; subst h
      exact .plus (infer_sound hD S Γ a .int ha) (infer_sound hD S Γ b .int hb)
    · rename_i s w s' w' ha hb
      split at h
      · rename_i hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [Option.some.injEq] at h; subst h
        exact .bvPlus (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
      · cases h
    · rename_i ha hb
      simp only [Option.some.injEq] at h; subst h
      exact .rPlus (infer_sound hD S Γ a .real ha) (infer_sound hD S Γ b .real hb)
    · cases h
  | .Minus a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i ha hb
      simp only [Option.some.injEq] at h; subst h
      exact .minus (infer_sound hD S Γ a .int ha) (infer_sound hD S Γ b .int hb)
    · rename_i s w s' w' ha hb
      split at h
      · rename_i hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [Option.some.injEq] at h; subst h
        exact .bvMinus (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
      · cases h
    · rename_i ha hb
      simp only [Option.some.injEq] at h; subst h
      exact .rMinus (infer_sound hD S Γ a .real ha) (infer_sound hD S Γ b .real hb)
    · cases h
  | .Times a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i ha hb
      simp only [Option.some.injEq] at h; subst h
      exact .times (infer_sound hD S Γ a .int ha) (infer_sound hD S Γ b .int hb)
    · rename_i s w s' w' ha hb
      split at h
      · rename_i hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [Option.some.injEq] at h; subst h
        exact .bvTimes (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
      · cases h
    · rename_i ha hb
      simp only [Option.some.injEq] at h; subst h
      exact .rTimes (infer_sound hD S Γ a .real ha) (infer_sound hD S Γ b .real hb)
    · cases h
  | .Division a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i ha hb
      simp only [Option.some.injEq] at h; subst h
      exact .div (infer_sound hD S Γ a .int ha) (infer_sound hD S Γ b .int hb)
    · rename_i s w s' w' ha hb
      split at h
      · rename_i hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [Option.some.injEq] at h; subst h
        cases s
        · exact .bvDiv (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
        · exact .sDiv (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
      · cases h
    · rename_i ha hb
      simp only [Option.some.injEq] at h; subst h
      exact .rDiv (infer_sound hD S Γ a .real ha) (infer_sound hD S Γ b .real hb)
    · cases h
  | .Remainder a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i ha hb
      simp only [Option.some.injEq] at h; subst h
      exact .rem (infer_sound hD S Γ a .int ha) (infer_sound hD S Γ b .int hb)
    · rename_i s w s' w' ha hb
      split at h
      · rename_i hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [Option.some.injEq] at h; subst h
        cases s
        · exact .bvRem (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
        · exact .sRem (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
      · cases h
    · cases h
  | .Modulo a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i ha hb
      simp only [Option.some.injEq] at h; subst h
      exact .mod (infer_sound hD S Γ a .int ha) (infer_sound hD S Γ b .int hb)
    · rename_i s w s' w' ha hb
      split at h
      · rename_i hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [Option.some.injEq] at h; subst h
        cases s
        · exact .bvMod (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
        · exact .sMod (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
      · cases h
    · cases h
  | .BVUnsignedToSigned a, k, h => by
    simp only [infer] at h
    split at h
    · rename_i w ha
      simp only [Option.some.injEq] at h; subst h
      exact .u2s (infer_sound hD S Γ a (.bv false w) ha)
    · cases h
  | .BVSignedToUnsigned a, k, h => by
    simp only [infer] at h
    split at h
    · rename_i w ha
      simp only [Option.some.injEq] at h; subst h
      exact .s2u (infer_sound hD S Γ a (.bv true w) ha)
    · cases h
  | .UMinus a, k, h => by
    simp only [infer] at h
    split at h
    · rename_i ha
      simp only [Option.some.injEq] at h; subst h
      exact .uminus (infer_sound hD S Γ a .int ha)
    · rename_i s w ha
      simp only [Option.some.injEq] at h; subst h
      exact .bvNeg (infer_sound hD S Γ a (.bv s w) ha)
    · rename_i ha
      simp only [Option.some.injEq] at h; subst h
      exact .rNeg (infer_sound hD S Γ a .real ha)
    · cases h
  | .FiniteSet es A, k, h => by
    simp only [infer] at h
    split at h
    · rename_i kA hA
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨_, hall⟩ := inferArgs_sound hD S Γ es _ hc.2
        have hAT := kind_spec hA
        have hl := hc.1
        simp only [K.ty]
        rw [← hAT]
        match es, hl, hall with
        | [], _, _ => exact .setEmpty (fragTy_of_kind (by rw [hA]; rfl))
        | [a], _, hall => exact .setOne (hall (a, A) (by simp))
        | _ :: _ :: _, hl, _ => simp at hl
      · cases h
    · cases h
  | .SetAdd s a, k, h => by
    simp only [infer] at h
    split at h
    · rename_i k1 k2 hs ha
      split at h
      · rename_i hk
        subst hk
        simp only [Option.some.injEq] at h; subst h
        exact .setAdd (infer_sound hD S Γ s (.set k1) hs) (infer_sound hD S Γ a k1 ha)
      · cases h
    · cases h
  | .ElementOfSet a s, k, h => by
    simp only [infer] at h
    split at h
    · rename_i k2 k1 ha hs
      split at h
      · rename_i hk
        subst hk
        simp only [Option.some.injEq] at h; subst h
        exact .elementOf (infer_sound hD S Γ a k1 ha) (infer_sound hD S Γ s (.set k1) hs)
      · cases h
    · cases h
  | .SubsetOf s u, k, h => by
    simp only [infer] at h
    split at h
    · rename_i k1 k2 hs hu
      split at h
      · rename_i hk
        subst hk
        simp only [Option.some.injEq] at h; subst h
        exact .subsetOf (infer_sound hD S Γ s (.set k1) hs) (infer_sound hD S Γ u (.set k1) hu)
      · cases h
    · cases h
  | .SetUnion s u, k, h => by
    simp only [infer] at h
    split at h
    · rename_i k1 k2 hs hu
      split at h
      · rename_i hk
        subst hk
        simp only [Option.some.injEq] at h; subst h
        exact .setUnion (infer_sound hD S Γ s (.set k1) hs) (infer_sound hD S Γ u (.set k1) hu)
      · cases h
    · cases h
  | .SetIntersection s u, k, h => by
    simp only [infer] at h
    split at h
    · rename_i k1 k2 hs hu
      split at h
      · rename_i hk
        subst hk
        simp only [Option.some.injEq] at h; subst h
        exact .setInter (infer_sound hD S Γ s (.set k1) hs) (infer_sound hD S Γ u (.set k1) hu)
      · cases h
    · cases h
  | .SetDifference s u, k, h => by
    simp only [infer] at h
    split at h
    · rename_i k1 k2 hs hu
      split at h
      · rename_i hk
        subst hk
        simp only [Option.some.injEq] at h; subst h
        exact .setDiff (infer_sound hD S Γ s (.set k1) hs) (infer_sound hD S Γ u (.set k1) hu)
      · cases h
    · cases h
  | .BVAnd a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i s w s' w' ha hb
      split at h
      · rename_i hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [Option.some.injEq] at h; subst h
        exact .bvAnd (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
      · cases h
    · cases h
  | .BVOr a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i s w s' w' ha hb
      split at h
      · rename_i hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [Option.some.injEq] at h; subst h
        exact .bvOr (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
      · cases h
    · cases h
  | .BVXor a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i s w s' w' ha hb
      split at h
      · rename_i hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [Option.some.injEq] at h; subst h
        exact .bvXor (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
      · cases h
    · cases h
  | .BVShiftLeft a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i s w s' w' ha hb
      split at h
      · rename_i hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [Option.some.injEq] at h; subst h
        exact .bvShl (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
      · cases h
    · cases h
  | .BVAShiftRight a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i s w s' w' ha hb
      split at h
      · rename_i hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [Option.some.injEq] at h; subst h
        exact .bvAShr (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
      · cases h
    · cases h
  | .BVLShiftRight a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i s w s' w' ha hb
      split at h
      · rename_i hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [Option.some.injEq] at h; subst h
        exact .bvLShr (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
      · cases h
    · cases h
  | .BVNarrowingCast a v, k, h => by
    simp only [infer] at h
    split at h
    · rename_i s w ha
      split at h
      · rename_i hv
        simp only [Option.some.injEq] at h; subst h
        exact .narrow (infer_sound hD S Γ a (.bv s w) ha) hv.1 hv.2
      · cases h
    · cases h
  | .BVWideningCast a v, k, h => by
    simp only [infer] at h
    split at h
    · rename_i s w ha
      split at h
      · rename_i hv
        simp only [Option.some.injEq] at h; subst h
        exact .widen (infer_sound hD S Γ a (.bv s w) ha) hv
      · cases h
    · cases h
  | .BVNot a, k, h => by
    simp only [infer] at h
    split at h
    · rename_i s w ha
      simp only [Option.some.injEq] at h; subst h
      exact .bvNot (infer_sound hD S Γ a (.bv s w) ha)
    · cases h
  | .FractionLiteral n d, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hd
      simp only [Option.some.injEq] at h; subst h
      exact .frac hd
    · cases h
  | .BVLiteral s w x, k, h => by
    simp only [infer] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h; subst h
      exact .bvLit hc.1 hc.2.1 hc.2.2
    · cases h
  | .LessThan a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i ha hb
      simp only [Option.some.injEq] at h; subst h
      exact .lt (infer_sound hD S Γ a .int ha) (infer_sound hD S Γ b .int hb)
    · rename_i s w s' w' ha hb
      split at h
      · rename_i hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [Option.some.injEq] at h; subst h
        cases s
        · exact .bvLt (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
        · exact .sLt (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
      · cases h
    · rename_i ha hb
      simp only [Option.some.injEq] at h; subst h
      exact .rLt (infer_sound hD S Γ a .real ha) (infer_sound hD S Γ b .real hb)
    · cases h
  | .GreaterThan a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i ha hb
      simp only [Option.some.injEq] at h; subst h
      exact .gt (infer_sound hD S Γ a .int ha) (infer_sound hD S Γ b .int hb)
    · rename_i s w s' w' ha hb
      split at h
      · rename_i hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [Option.some.injEq] at h; subst h
        cases s
        · exact .bvGt (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
        · exact .sGt (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
      · cases h
    · rename_i ha hb
      simp only [Option.some.injEq] at h; subst h
      exact .rGt (infer_sound hD S Γ a .real ha) (infer_sound hD S Γ b .real hb)
    · cases h
  | .LessEquals a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i ha hb
      simp only [Option.some.injEq] at h; subst h
      exact .le (infer_sound hD S Γ a .int ha) (infer_sound hD S Γ b .int hb)
    · rename_i s w s' w' ha hb
      split at h
      · rename_i hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [Option.some.injEq] at h; subst h
        cases s
        · exact .bvLe (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
        · exact .sLe (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
      · cases h
    · rename_i ha hb
      simp only [Option.some.injEq] at h; subst h
      exact .rLe (infer_sound hD S Γ a .real ha) (infer_sound hD S Γ b .real hb)
    · cases h
  | .GreaterEquals a b, k, h => by
    simp only [infer] at h
    split at h
    · rename_i ha hb
      simp only [Option.some.injEq] at h; subst h
      exact .ge (infer_sound hD S Γ a .int ha) (infer_sound hD S Γ b .int hb)
    · rename_i s w s' w' ha hb
      split at h
      · rename_i hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [Option.some.injEq] at h; subst h
        cases s
        · exact .bvGe (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
        · exact .sGe (infer_sound hD S Γ a (.bv _ w) ha) (infer_sound hD S Γ b (.bv _ w) hb)
      · cases h
    · rename_i ha hb
      simp only [Option.some.injEq] at h; subst h
      exact .rGe (infer_sound hD S Γ a .real ha) (infer_sound hD S Γ b .real hb)
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
  | .FPLiteral _ _ _, k, h
  | .StringLiteral _, k, h | .UnitLiteral, k, h | .RoundNearestTiesToEven, k, h
  | .RoundNearestTiesToAway, k, h | .RoundTowardPositive, k, h | .RoundTowardNegative, k, h
  | .RoundTowardZero, k, h
  | .StringConcat _ _, k, h | .SubString _ _ _, k, h | .StringLength _, k, h
  | .BVToInt _, k, h | .IntToBV _ _ _, k, h | .FPEquals _ _, k, h | .FPAdd _ _ _, k, h
  | .FPSub _ _ _, k, h | .FPUMinus _, k, h | .FPFMA _ _ _ _, k, h | .FPMul _ _ _, k, h
  | .FPDiv _ _ _, k, h | .FPAbs _, k, h | .FPMax _ _, k, h | .FPMin _ _, k, h
  | .FPRound _ _, k, h | .Sqrt _ _, k, h | .FPCast _ _ _ _, k, h | .FPFromBinary _ _ _, k, h
  | .FPToBV _ _ _ _, k, h | .FPToReal _, k, h | .FPLessThan _ _, k, h | .FPGreaterThan _ _, k, h
  | .FPLessEquals _ _, k, h | .FPGreaterEquals _ _, k, h | .FPIsZero _, k, h
  | .FPIsInfinite _, k, h | .FPIsNaN _, k, h | .FPIsNegative _, k, h | .FPIsPositive _, k, h
  | .FPIsNormal _, k, h | .FPIsSubnormal _, k, h | .Tuple _, k, h | .TupleSelect _ _, k, h
  | .FiniteBag _ _, k, h | .BagAdd _ _, k, h | .MultiplicityInBag _ _, k, h
  | .BagIntersection _ _, k, h | .BagUnion _ _, k, h | .BagDifference _ _, k, h
  | .FiniteMap _ _ _ _, k, h | .MapApply _ _, k, h | .MapUpdated _ _ _, k, h
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
  | bvLit _ _ _ => exact .bv
  | bvMod _ _ iha ihb => exact .mod iha ihb
  | sDiv _ _ iha ihb => exact .div iha ihb
  | sRem _ _ iha ihb => exact .rem iha ihb
  | sMod _ _ iha ihb => exact .mod iha ihb
  | sLt _ _ iha ihb => exact .lt iha ihb
  | sGt _ _ iha ihb => exact .gt iha ihb
  | sLe _ _ iha ihb => exact .le iha ihb
  | sGe _ _ iha ihb => exact .ge iha ihb
  | u2s _ ih => exact .u2s ih
  | s2u _ ih => exact .s2u ih
  | frac _ => exact .frac
  | rPlus _ _ iha ihb => exact .plus iha ihb
  | rMinus _ _ iha ihb => exact .minus iha ihb
  | rTimes _ _ iha ihb => exact .times iha ihb
  | rDiv _ _ iha ihb => exact .div iha ihb
  | rNeg _ ih => exact .uminus ih
  | rLt _ _ iha ihb => exact .lt iha ihb
  | rGt _ _ iha ihb => exact .gt iha ihb
  | rLe _ _ iha ihb => exact .le iha ihb
  | rGe _ _ iha ihb => exact .ge iha ihb
  | bvPlus _ _ iha ihb => exact .plus iha ihb
  | bvMinus _ _ iha ihb => exact .minus iha ihb
  | bvTimes _ _ iha ihb => exact .times iha ihb
  | bvDiv _ _ iha ihb => exact .div iha ihb
  | bvRem _ _ iha ihb => exact .rem iha ihb
  | bvNeg _ ih => exact .uminus ih
  | bvNot _ ih => exact .bvnot ih
  | bvAnd _ _ iha ihb => exact .bvand iha ihb
  | bvOr _ _ iha ihb => exact .bvor iha ihb
  | bvXor _ _ iha ihb => exact .bvxor iha ihb
  | bvShl _ _ iha ihb => exact .shl iha ihb
  | bvAShr _ _ iha ihb => exact .ashr iha ihb
  | bvLShr _ _ iha ihb => exact .lshr iha ihb
  | narrow _ _ _ ih => exact .narrow ih
  | widen _ _ ih => exact .widen ih
  | bvLt _ _ iha ihb => exact .lt iha ihb
  | bvGt _ _ iha ihb => exact .gt iha ihb
  | bvLe _ _ iha ihb => exact .le iha ihb
  | bvGe _ _ iha ihb => exact .ge iha ihb
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
  | setEmpty _ => exact .finiteSet fun _ h => nomatch h
  | setOne _ ih => exact .finiteSet fun a ha => by rw [List.mem_singleton.mp ha]; exact ih
  | setAdd _ _ ihs iha => exact .setAdd ihs iha
  | elementOf _ _ iha ihs => exact .elementOf iha ihs
  | subsetOf _ _ iha ihb => exact .subsetOf iha ihb
  | setUnion _ _ iha ihb => exact .setUnion iha ihb
  | setInter _ _ iha ihb => exact .setInter iha ihb
  | setDiff _ _ iha ihb => exact .setDiff iha ihb

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
  | .Set A => declsOfType A
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
  | .set_empty T => [T]
  | .not a | .uneg a | .bvneg a | .bvnot a | .extract _ _ a | .zero_extend _ a
  | .sign_extend _ a | .set_singleton a => typesOf a
  | .xor a b | .imp a b | .eq a b | .plus a b | .neg a b | .mult a b | .div a b | .mod a b
  | .lt a b | .gt a b | .leq a b | .geq a b | .and a b | .or a b | .Apply a b | .bvadd a b
  | .bvsub a b | .bvmul a b | .bvudiv a b | .bvurem a b | .bvult a b | .bvugt a b | .bvule a b
  | .bvuge a b | .qdiv a b | .bvsdiv a b | .bvsrem a b | .bvsmod a b | .bvslt a b | .bvsgt a b
  | .bvsle a b | .bvsge a b | .bvand a b | .bvor a b | .bvxor a b | .bvshl a b | .bvashr a b
  | .bvlshr a b | .set_union a b | .set_inter a b | .set_minus a b | .set_member a b
  | .set_subset a b => typesOf a ++ typesOf b
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
