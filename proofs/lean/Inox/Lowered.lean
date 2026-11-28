/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Encoded

/-!
# What the lowering to SMT-LIB makes of an expression

The query of `Inox/Reached.lean` is read back from the terms of Logos (`back`), which aren't
the expressions of the input: their symbols have other names, their constructors and their
fields too, an error is an assumption that fails, and a sum or a product of two integers has
a trailing `+ 0` or `* 1`, as Logos reads the sums and the products of SMT-LIB. An expression
of the input relates to what it is lowered to (`Lowers`) up to these, and where an expression
of the input evaluates to a value, the expression that it is lowered to evaluates with enough
fuel to the same value up to the names of its constructors (`lowers_eval`), in a program whose
functions are what those of the input are lowered to (`Funs`) and whose constructors are those
of the input (`Ctors`).

The relation is of first-order expressions over integers, other primitive values and values
of datatypes, with calls of functions, whose type parameters it ignores, as those that they are
lowered to have none, and lets, which the lowering inlines or drops: no lambdas yet. A
construction of a sort with an invariant is lowered to the assumption of the invariant of its
arguments (`instInv`), where its body doesn't depend on the fuel or the types. A signed
bit-vector may be lowered to the signed view of an unsigned one, as Logos reads bit-vectors,
whose unsigned view is then the unsigned one (`toUnsigned`). It follows the kinds of the
values, so that a field of a value of a datatype is known to be an integer where the field is
of the integers and the value is a construction of fields of their kinds (`Has`).
-/

namespace Inox.Lowered

open Inox.Semantics
open Inox.Encoded (IsPrim FunIn call_inv call_fun eval_tuple_inv)
open Inox.Bags (eval_bool_ok)

/-- The kinds of values that the relation follows: integers, which a trailing `+ 0` keeps,
primitive values, whose equality is that of the values whatever the program, any value,
tuples, of the arguments of calls, and values of the datatype `s`, whose fields are of their
kinds. -/
inductive LK where
  | int
  | prim
  | any
  | tuple (ks : List LK)
  | data (s : Id)

/-- The value `v` is of the kind `k`, where the constructors of `T` construct values of their
datatypes from fields of their kinds. -/
inductive Has (T : Id → Option (Id × List LK)) : LK → Value → Prop where
  | int (n : Int) : Has T .int (.IntV n)
  | prim {v : Value} (h : IsPrim v = true) : Has T .prim v
  | any (v : Value) : Has T .any v
  | tupleNil : Has T (.tuple []) (.TupleV [])
  | tupleCons {k : LK} {ks : List LK} {v : Value} {vs : List Value} (h : Has T k v)
      (hr : Has T (.tuple ks) (.TupleV vs)) : Has T (.tuple (k :: ks)) (.TupleV (v :: vs))
  | data {s c : Id} {ks : List LK} {tps : List Ty} {vs : List Value} (hc : T c = some (s, ks))
      (h : Has T (.tuple ks) (.TupleV vs)) : Has T (.data s) (.ADTV c tps vs)

/-- The kind `k` is in the kind `k'`. -/
def Sub : LK → LK → Bool
  | .int, .int | .int, .prim | .int, .any | .prim, .prim | .prim, .any | .any, .any => true
  | .data s, .data s' => s == s'
  | .data _, .any => true
  | _, _ => false

theorem has_sub {T : Id → Option (Id × List LK)} {k k' : LK} (hs : Sub k k' = true) {v : Value}
    (h : Has T k v) : Has T k' v := by
  cases k <;> cases k' <;> simp [Sub] at hs
  all_goals first
    | exact h
    | exact .any v
    | (cases h; exact .prim rfl)
    | (subst hs; exact h)

/-- What the lowering does with the names of the input: each function with the function that
it is lowered to, the kinds of its parameters and the kind of its result, each constructor
with the constructor that it is lowered to, and each field with its field. -/
structure LSig where
  funs : Id → Option (Id × List LK × LK)
  ctors : Id → Option Id
  fields : Id → Option Id
  /-- the datatype of each constructor, with the kinds of its fields -/
  kinds : Id → Option (Id × List LK) := fun _ => none
  /-- the datatype of each field, with its kind -/
  fieldKinds : Id → Option (Id × LK) := fun _ => none
  /-- the parameter of the invariant of each constructor of a sort with an invariant, its fields
  and the body of the invariant -/
  invs : Id → Option (Id × List Param × Expr) := fun _ => none

mutual
/-- The value `v` of the input is the value `v'` of the lowered program up to the names of
the constructors, which are those of `K`. -/
inductive VR (K : Id → Option Id) : Value → Value → Prop where
  | prim {v : Value} (h : IsPrim v = true) : VR K v v
  | adt {c c' : Id} {tps tps' : List Ty} {vs vs' : List Value} (h : K c = some c')
      (hs : VRs K vs vs') : VR K (.ADTV c tps vs) (.ADTV c' tps' vs')
  | tuple {vs vs' : List Value} (hs : VRs K vs vs') : VR K (.TupleV vs) (.TupleV vs')
inductive VRs (K : Id → Option Id) : List Value → List Value → Prop where
  | nil : VRs K [] []
  | cons {v v' : Value} {vs vs' : List Value} (h : VR K v v') (hs : VRs K vs vs') :
      VRs K (v :: vs) (v' :: vs')
end

theorem vr_prim {K : Id → Option Id} {v v' : Value} (h : VR K v v') (hp : IsPrim v = true) :
    v' = v := by
  cases h with
  | prim _ => rfl
  | adt _ _ => simp [IsPrim] at hp
  | tuple _ => simp [IsPrim] at hp

theorem vr_has {K : Id → Option Id} {T : Id → Option (Id × List LK)} {v v' : Value}
    (h : VR K v v') : ∀ {k : LK}, Has T k v → k = .int ∨ k = .prim → v' = v
  | _, .int _, _ => vr_prim h rfl
  | _, .prim hp, _ => vr_prim h hp
  | _, .any _, hk => by simp at hk
  | _, .tupleNil, hk => by simp at hk
  | _, .tupleCons _ _, hk => by simp at hk
  | _, .data _ _, hk => by simp at hk

/-- `Γ` where the variable `x` is `o`. -/
def bindCtx (Γ : Id → Option (Expr × LK)) (x : Id) (o : Option (Expr × LK)) :
    Id → Option (Expr × LK) :=
  fun z => if z = x then o else Γ z

/-- The argument of the field `sel` among the arguments `args` of a construction whose fields
are `fields`. -/
def pick : List Param → List Expr → Id → Option Expr
  | .Param f _ :: fs, a :: as, sel => if f = sel then some a else pick fs as sel
  | _, _, _ => none

/-- The body `e` of the invariant of a construction, of the parameter `p`, where the selection
of each field of `p` is the argument `args` of the construction of the fields `fields`, `n`
deep, for the bodies that don't depend on the fuel or the types: no calls, constructions or
lets, and no other variables. -/
def instInv (p : Id) (fields : List Param) (args : List Expr) : Nat → Expr → Option Expr
  | 0, _ => none
  | n + 1, e =>
    let r := instInv p fields args n
    match e with
    | .IntegerLiteral i => some (.IntegerLiteral i)
    | .BooleanLiteral b => some (.BooleanLiteral b)
    | .FractionLiteral a b => some (.FractionLiteral a b)
    | .Error => some .Error
    | .Not a => (r a).map .Not
    | .UMinus a => (r a).map .UMinus
    | .IsConstructor a c => (r a).map (.IsConstructor · c)
    | .ADTSelector a f =>
      match a with
      | .Variable q => if q = p then pick fields args f else none
      | _ => (r a).map (.ADTSelector · f)
    | .Plus a b => (r a).bind fun a' => (r b).map (.Plus a' ·)
    | .Minus a b => (r a).bind fun a' => (r b).map (.Minus a' ·)
    | .Times a b => (r a).bind fun a' => (r b).map (.Times a' ·)
    | .Division a b => (r a).bind fun a' => (r b).map (.Division a' ·)
    | .Remainder a b => (r a).bind fun a' => (r b).map (.Remainder a' ·)
    | .Modulo a b => (r a).bind fun a' => (r b).map (.Modulo a' ·)
    | .LessThan a b => (r a).bind fun a' => (r b).map (.LessThan a' ·)
    | .GreaterThan a b => (r a).bind fun a' => (r b).map (.GreaterThan a' ·)
    | .LessEquals a b => (r a).bind fun a' => (r b).map (.LessEquals a' ·)
    | .GreaterEquals a b => (r a).bind fun a' => (r b).map (.GreaterEquals a' ·)
    | .Equals a b => (r a).bind fun a' => (r b).map (.Equals a' ·)
    | .Implies a b => (r a).bind fun a' => (r b).map (.Implies a' ·)
    | .Assume a b => (r a).bind fun a' => (r b).map (.Assume a' ·)
    | .IfExpr c a b => (r c).bind fun c' => (r a).bind fun a' => (r b).map (.IfExpr c' a' ·)
    | .And es => (es.mapM r).map .And
    | .Or es => (es.mapM r).map .Or
    | _ => none

/-- `Lowers S Γ e e' k`: the expression `e` of the input is lowered to `e'`, and its values are
of the kind `k`, where each variable `x` of `Γ` is lowered to the expression `y` of
`Γ x = some (y, k)`, of the kind `k`: a variable, or what the value of a let is lowered to where
the lowering inlines it. The functions, the constructors and the fields of the input are those
of `S`. -/
inductive Lowers (S : LSig) : (Id → Option (Expr × LK)) → Expr → Expr → LK → Prop where
  | var {Γ : Id → Option (Expr × LK)} {x : Id} {y : Expr} {k : LK} (h : Γ x = some (y, k)) :
      Lowers S Γ (.Variable x) y k
  /-- A let whose value the lowering inlines. -/
  | letIn {Γ : Id → Option (Expr × LK)} {x : Id} {a a' b e' : Expr} {ka k : LK}
      (ha : Lowers S Γ a a' ka) (hb : Lowers S (bindCtx Γ x (some (a', ka))) b e' k) :
      Lowers S Γ (.Let x a b) e' k
  /-- A let whose variable the lowering drops. -/
  | letDrop {Γ : Id → Option (Expr × LK)} {x : Id} {a b e' : Expr} {k : LK}
      (hb : Lowers S (bindCtx Γ x none) b e' k) : Lowers S Γ (.Let x a b) e' k
  | int {Γ : Id → Option (Expr × LK)} (n : Int) :
      Lowers S Γ (.IntegerLiteral n) (.IntegerLiteral n) .int
  | bool {Γ : Id → Option (Expr × LK)} (b : Bool) :
      Lowers S Γ (.BooleanLiteral b) (.BooleanLiteral b) .prim
  | frac {Γ : Id → Option (Expr × LK)} (n d : Int) :
      Lowers S Γ (.FractionLiteral n d) (.FractionLiteral n d) .prim
  | bvLit {Γ : Id → Option (Expr × LK)} (s : Bool) (w x : Int) :
      Lowers S Γ (.BVLiteral s w x) (.BVLiteral s w x) .prim
  /-- A signed bit-vector, as Logos reads it: the signed view of an unsigned one. -/
  | bvSignedLit {Γ : Id → Option (Expr × LK)} (w x : Int) :
      Lowers S Γ (.BVLiteral true w x) (.BVUnsignedToSigned (.BVLiteral false w x)) .prim
  /-- The unsigned view of what is lowered to the signed view of an unsigned bit-vector. -/
  | toUnsigned {Γ : Id → Option (Expr × LK)} {a a' : Expr}
      (ha : Lowers S Γ a (.BVUnsignedToSigned a') .prim) :
      Lowers S Γ (.BVSignedToUnsigned a) a' .prim
  | toSigned {Γ : Id → Option (Expr × LK)} {a a' : Expr} (ha : Lowers S Γ a a' .any) :
      Lowers S Γ (.BVUnsignedToSigned a) (.BVUnsignedToSigned a') .prim
  /-- Signed bit-vectors are equal where their unsigned views are. -/
  | eqSigned {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr}
      (ha : Lowers S Γ a (.BVUnsignedToSigned a') .prim)
      (hb : Lowers S Γ b (.BVUnsignedToSigned b') .prim) :
      Lowers S Γ (.Equals a b) (.Equals a' b') .prim
  /-- An error has no value, whatever it is lowered to. -/
  | error {Γ : Id → Option (Expr × LK)} (e' : Expr) (k : LK) : Lowers S Γ .Error e' k
  | weaken {Γ : Id → Option (Expr × LK)} {e e' : Expr} {k k' : LK} (h : Lowers S Γ e e' k)
      (hs : Sub k k' = true) : Lowers S Γ e e' k'
  | plusInt {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .int)
      (hb : Lowers S Γ b b' .int) : Lowers S Γ (.Plus a b) (.Plus a' b') .int
  /-- A sum of two integers, as Logos reads it. -/
  | plusZero {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .int)
      (hb : Lowers S Γ b b' .int) :
      Lowers S Γ (.Plus a b) (.Plus a' (.Plus b' (.IntegerLiteral 0))) .int
  | plus {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.Plus a b) (.Plus a' b') .prim
  | minusInt {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .int)
      (hb : Lowers S Γ b b' .int) : Lowers S Γ (.Minus a b) (.Minus a' b') .int
  | minus {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.Minus a b) (.Minus a' b') .prim
  | timesInt {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .int)
      (hb : Lowers S Γ b b' .int) : Lowers S Γ (.Times a b) (.Times a' b') .int
  | times {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.Times a b) (.Times a' b') .prim
  | uminusInt {Γ : Id → Option (Expr × LK)} {a a' : Expr} (ha : Lowers S Γ a a' .int) :
      Lowers S Γ (.UMinus a) (.UMinus a') .int
  | uminus {Γ : Id → Option (Expr × LK)} {a a' : Expr} (ha : Lowers S Γ a a' .any) :
      Lowers S Γ (.UMinus a) (.UMinus a') .prim
  /-- A product of two integers, as Logos reads it. -/
  | timesOne {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .int)
      (hb : Lowers S Γ b b' .int) :
      Lowers S Γ (.Times a b) (.Times a' (.Times b' (.IntegerLiteral 1))) .int
  | divInt {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .int)
      (hb : Lowers S Γ b b' .int) : Lowers S Γ (.Division a b) (.Division a' b') .int
  | modInt {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .int)
      (hb : Lowers S Γ b b' .int) : Lowers S Γ (.Modulo a b) (.Modulo a' b') .int
  | remInt {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .int)
      (hb : Lowers S Γ b b' .int) : Lowers S Γ (.Remainder a b) (.Remainder a' b') .int
  | div {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.Division a b) (.Division a' b') .prim
  | rem {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.Remainder a b) (.Remainder a' b') .prim
  | mod {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.Modulo a b) (.Modulo a' b') .prim
  | lt {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.LessThan a b) (.LessThan a' b') .prim
  | gt {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.GreaterThan a b) (.GreaterThan a' b') .prim
  | le {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.LessEquals a b) (.LessEquals a' b') .prim
  | ge {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.GreaterEquals a b) (.GreaterEquals a' b') .prim
  /-- Primitive values are equal alike in both programs. -/
  | eq {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .prim)
      (hb : Lowers S Γ b b' .prim) : Lowers S Γ (.Equals a b) (.Equals a' b') .prim
  | not {Γ : Id → Option (Expr × LK)} {a a' : Expr} (ha : Lowers S Γ a a' .any) :
      Lowers S Γ (.Not a) (.Not a') .prim
  | implies {Γ : Id → Option (Expr × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.Implies a b) (.Implies a' b') .prim
  | andNil {Γ : Id → Option (Expr × LK)} : Lowers S Γ (.And []) (.And []) .prim
  | andCons {Γ : Id → Option (Expr × LK)} {a a' : Expr} {es es' : List Expr}
      (ha : Lowers S Γ a a' .any) (hr : Lowers S Γ (.And es) (.And es') .prim) :
      Lowers S Γ (.And (a :: es)) (.And (a' :: es')) .prim
  | orNil {Γ : Id → Option (Expr × LK)} : Lowers S Γ (.Or []) (.Or []) .prim
  | orCons {Γ : Id → Option (Expr × LK)} {a a' : Expr} {es es' : List Expr}
      (ha : Lowers S Γ a a' .any) (hr : Lowers S Γ (.Or es) (.Or es') .prim) :
      Lowers S Γ (.Or (a :: es)) (.Or (a' :: es')) .prim
  | ite {Γ : Id → Option (Expr × LK)} {c c' a a' b b' : Expr} {k : LK}
      (hc : Lowers S Γ c c' .any) (ha : Lowers S Γ a a' k) (hb : Lowers S Γ b b' k) :
      Lowers S Γ (.IfExpr c a b) (.IfExpr c' a' b') k
  | assume {Γ : Id → Option (Expr × LK)} {p p' a a' : Expr} {k : LK}
      (hp : Lowers S Γ p p' .any) (ha : Lowers S Γ a a' k) :
      Lowers S Γ (.Assume p a) (.Assume p' a') k
  | tupleNil {Γ : Id → Option (Expr × LK)} : Lowers S Γ (.Tuple []) (.Tuple []) (.tuple [])
  | tupleCons {Γ : Id → Option (Expr × LK)} {e e' : Expr} {es es' : List Expr} {k : LK}
      {ks : List LK} (he : Lowers S Γ e e' k)
      (hr : Lowers S Γ (.Tuple es) (.Tuple es') (.tuple ks)) :
      Lowers S Γ (.Tuple (e :: es)) (.Tuple (e' :: es')) (.tuple (k :: ks))
  /-- A call of a function, whatever its type arguments. -/
  | call {Γ : Id → Option (Expr × LK)} {f g : Id} {ks : List LK} {k : LK} {tps tps' : List Ty}
      {es es' : List Expr} (hf : S.funs f = some (g, ks, k))
      (ha : Lowers S Γ (.Tuple es) (.Tuple es') (.tuple ks)) :
      Lowers S Γ (.FunctionInvocation f tps es) (.FunctionInvocation g tps' es') k
  /-- A construction, of a constructor of a sort without an invariant (`Ctors`). -/
  | adt {Γ : Id → Option (Expr × LK)} {c c' : Id} {ks : List LK} {tps tps' : List Ty}
      {es es' : List Expr} (hc : S.ctors c = some c')
      (ha : Lowers S Γ (.Tuple es) (.Tuple es') (.tuple ks)) :
      Lowers S Γ (.ADT c tps es) (.ADT c' tps' es') .any
  | isCtor {Γ : Id → Option (Expr × LK)} {e e' : Expr} {c c' : Id} (hc : S.ctors c = some c')
      (he : Lowers S Γ e e' .any) : Lowers S Γ (.IsConstructor e c) (.IsConstructor e' c') .prim
  | sel {Γ : Id → Option (Expr × LK)} {e e' : Expr} {f f' : Id} (hf : S.fields f = some f')
      (he : Lowers S Γ e e' .any) : Lowers S Γ (.ADTSelector e f) (.ADTSelector e' f') .any
  /-- A construction of a value of a datatype, from fields of their kinds. -/
  | adtData {Γ : Id → Option (Expr × LK)} {c c' s : Id} {ks : List LK} {tps tps' : List Ty}
      {es es' : List Expr} (hc : S.ctors c = some c') (hk : S.kinds c = some (s, ks))
      (ha : Lowers S Γ (.Tuple es) (.Tuple es') (.tuple ks)) :
      Lowers S Γ (.ADT c tps es) (.ADT c' tps' es') (.data s)
  /-- A construction of a constructor of a sort with an invariant, which holds of the arguments
  where the construction has a value: any value, or one of the datatype of the constructor where
  the arguments are of the kinds of its fields. -/
  | adtInv {Γ : Id → Option (Expr × LK)} {c c' p : Id} {fields : List Param} {B I J : Expr}
      {n : Nat} {ks : List LK} {k : LK} {tps tps' : List Ty} {es es' : List Expr}
      (hc : S.ctors c = some c') (hv : S.invs c = some (p, fields, B))
      (hI : instInv p fields es n B = some I) (hi : Lowers S Γ I J .any)
      (ha : Lowers S Γ (.Tuple es) (.Tuple es') (.tuple ks))
      (hk : k = .any ∨ ∃ s, k = .data s ∧ S.kinds c = some (s, ks)) :
      Lowers S Γ (.ADT c tps es) (.Assume J (.ADT c' tps' es')) k
  /-- A selection of a field of a value of a datatype, of the kind of the field. -/
  | selData {Γ : Id → Option (Expr × LK)} {e e' : Expr} {f f' s : Id} {k : LK}
      (hf : S.fields f = some f') (hk : S.fieldKinds f = some (s, k))
      (he : Lowers S Γ e e' (.data s)) : Lowers S Γ (.ADTSelector e f) (.ADTSelector e' f') k

/-- The variables of the body of a function: its parameters `params`, which are the parameters
`params'` of the function that it is lowered to, of the kinds `ks`. -/
def paramsCtx (params params' : List Id) (ks : List LK) : Id → Option (Expr × LK) :=
  fun x => ((params.zip (params'.zip ks)).lookup x).map fun p => (.Variable p.1, p.2)

/-- The functions of `S` are those of `Ps`, whose type parameters the relation ignores, and
their bodies are lowered to those of their functions in `P`, without type parameters, whose
parameters are distinct. -/
def Funs (Ps P : Program) (S : LSig) : Prop :=
  ∀ f g ks k, S.funs f = some (g, ks, k) → ∃ tparams params params' body body',
    FunIn f tparams params body Ps ∧ FunIn g [] params' body' P ∧ params'.Nodup ∧
      params.length = ks.length ∧ params'.length = ks.length ∧
      Lowers S (paramsCtx params params' ks) body body' k

/-- The program has the constructor `c`, with the fields `fs`, of a sort without an
invariant. -/
def CtorOf (c : Id) (fs : List Param) : Program → Prop
  | .Program _ cs ss _ _ => ∃ s tps eq, lookup_ctor cs c = .Ok (.Constructor c s fs) ∧
      lookup_sort ss s = .Ok (.Sort s tps none eq)

/-- The program has the constructor `c`, with the fields `fs`. -/
def CtorIn (c : Id) (fs : List Param) : Program → Prop
  | .Program _ cs _ _ _ => ∃ s, lookup_ctor cs c = .Ok (.Constructor c s fs)

/-- The names of the fields. -/
def fieldNames : List Param → List Id
  | [] => []
  | .Param f _ :: fs => f :: fieldNames fs

/-- The fields `fs'` are those of `F` of the fields `fs`, position by position. -/
def FieldsOk (F : Id → Option Id) : List Id → List Id → Prop
  | [], [] => True
  | f :: fs, f' :: fs' => F f = some f' ∧ FieldsOk F fs fs'
  | _, _ => False

/-- The fields `fs` are of the datatype `s` and of the kinds `ks` in `F`, position by
position. -/
def FieldKinds (F : Id → Option (Id × LK)) (s : Id) : List Param → List LK → Prop
  | [], [] => True
  | .Param f _ :: fs, k :: ks => F f = some (s, k) ∧ FieldKinds F s fs ks
  | _, _ => False

/-- The constructors of `S` are those of `Ps`, and their constructors in `P` are of sorts
without invariants, with the fields of `S` at the same positions. The constructors and the
fields of `S` are distinct, as their names in `P` are. The constructors of `S.kinds` are those
of `Ps` too, whose fields are of the kinds of `S.fieldKinds`, and the invariants of `S.invs` are
those of the sorts of their constructors in `Ps`. -/
structure Ctors (Ps P : Program) (S : LSig) : Prop where
  ctor : ∀ c c', S.ctors c = some c' → ∃ fs fs', CtorIn c fs Ps ∧ CtorOf c' fs' P ∧
    FieldsOk S.fields (fieldNames fs) (fieldNames fs')
  ctorInj : ∀ c d c', S.ctors c = some c' → S.ctors d = some c' → c = d
  fieldInj : ∀ f g f', S.fields f = some f' → S.fields g = some f' → f = g
  kinds : ∀ c s ks, S.kinds c = some (s, ks) →
    ∃ fs, CtorIn c fs Ps ∧ FieldKinds S.fieldKinds s fs ks
  inv : ∀ c p fs B, S.invs c = some (p, fs, B) → ∃ fns cs ss is eqm c0 s s0 tps eq inv tparams,
    Ps = .Program fns cs ss is eqm ∧ lookup_ctor cs c = .Ok (.Constructor c0 s fs) ∧
      lookup_sort ss s = .Ok (.Sort s0 tps (some inv) eq) ∧ FunIn inv tparams [p] B Ps

/-! ## Values -/

theorem real_prim {n d : Int} {v : Value} (h : real n d = .Ok v) : IsPrim v = true := by
  unfold real at h
  split at h
  · cases h
  · cases h; rfl

local macro "prim_of" h:ident : tactic => `(tactic| (
  repeat' (first | split at $h:ident | (dsimp only at $h:ident))
  all_goals first
    | (cases $h:ident; done)
    | (cases $h:ident; rfl)
    | exact real_prim $h:ident
    | (cases $h:ident; simp [bv, IsPrim])
    | skip))

theorem plus_prim {a b v : Value} (h : arith_plus a b = .Ok v) : IsPrim v = true := by
  unfold arith_plus at h; prim_of h

theorem minus_prim {a b v : Value} (h : arith_minus a b = .Ok v) : IsPrim v = true := by
  unfold arith_minus at h; prim_of h

theorem times_prim {a b v : Value} (h : arith_times a b = .Ok v) : IsPrim v = true := by
  unfold arith_times at h; prim_of h

theorem neg_prim {a v : Value} (h : arith_neg a = .Ok v) : IsPrim v = true := by
  unfold arith_neg at h; prim_of h

theorem div_prim {a b v : Value} (h : arith_div a b = .Ok v) : IsPrim v = true := by
  unfold arith_div at h; prim_of h

theorem rem_prim {a b v : Value} (h : arith_rem a b = .Ok v) : IsPrim v = true := by
  unfold arith_rem at h; prim_of h

theorem mod_prim {a b v : Value} (h : arith_mod a b = .Ok v) : IsPrim v = true := by
  unfold arith_mod at h; prim_of h

theorem mem_of_lookup {β : Type} : ∀ {l : List (Id × β)} {c : Id} {v : β},
    l.lookup c = some v → (c, v) ∈ l
  | [], _, _, h => by simp at h
  | (d, w) :: l, c, v, h => by
    by_cases hcd : c = d
    · subst hcd
      simp [List.lookup] at h
      simp [h]
    · have hb : (c == d) = false := by simpa using hcd
      simp only [List.lookup, hb] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)


theorem plus_args {a b v : Value} (h : arith_plus a b = .Ok v) :
    IsPrim a = true ∧ IsPrim b = true := by
  cases a <;> cases b <;> simp_all [arith_plus, IsPrim]

theorem minus_args {a b v : Value} (h : arith_minus a b = .Ok v) :
    IsPrim a = true ∧ IsPrim b = true := by
  cases a <;> cases b <;> simp_all [arith_minus, IsPrim]

theorem times_args {a b v : Value} (h : arith_times a b = .Ok v) :
    IsPrim a = true ∧ IsPrim b = true := by
  cases a <;> cases b <;> simp_all [arith_times, IsPrim]

theorem div_args {a b v : Value} (h : arith_div a b = .Ok v) :
    IsPrim a = true ∧ IsPrim b = true := by
  cases a <;> cases b <;> simp_all [arith_div, IsPrim]

theorem rem_args {a b v : Value} (h : arith_rem a b = .Ok v) :
    IsPrim a = true ∧ IsPrim b = true := by
  cases a <;> cases b <;> simp_all [arith_rem, IsPrim]

theorem mod_args {a b v : Value} (h : arith_mod a b = .Ok v) :
    IsPrim a = true ∧ IsPrim b = true := by
  cases a <;> cases b <;> simp_all [arith_mod, IsPrim]

theorem neg_args {a v : Value} (h : arith_neg a = .Ok v) : IsPrim a = true := by
  cases a <;> simp_all [arith_neg, IsPrim]

theorem lt_args {a b : Value} {r : Bool} (h : arith_lt a b = .Ok r) :
    IsPrim a = true ∧ IsPrim b = true := by
  cases a <;> cases b <;> simp_all [arith_lt, IsPrim]

theorem le_args {a b : Value} {r : Bool} (h : arith_le a b = .Ok r) :
    IsPrim a = true ∧ IsPrim b = true := by
  cases a <;> cases b <;> simp_all [arith_le, arith_lt, IsPrim]

theorem vrs_length {K : Id → Option Id} : ∀ {vs vs' : List Value}, VRs K vs vs' →
    vs.length = vs'.length
  | _, _, .nil => rfl
  | _, _, .cons _ hs => by simp [vrs_length hs]

/-- Selecting a field of the values `vs` and the field of `S` of the lowered values `vs'`. -/
theorem select_lowered {S : LSig} (hinj : ∀ f g f', S.fields f = some f' → S.fields g = some f' →
    f = g) : ∀ {fs fs' : List Param} {vs vs' : List Value},
    FieldsOk S.fields (fieldNames fs) (fieldNames fs') →
    VRs S.ctors vs vs' → ∀ {sel sel' : Id} {v : Value}, S.fields sel = some sel' →
      select_field fs vs sel = .Ok v → ∃ v', select_field fs' vs' sel' = .Ok v' ∧ VR S.ctors v v'
  | [], [], _, _, _, _, _, _, _, _, h => by simp [select_field] at h
  | .Param f _ :: fs, .Param f' _ :: fs', v :: vs, v' :: vs', hf, .cons hv hvs, sel, sel', w,
      hs, h => by
    simp only [fieldNames, FieldsOk] at hf
    obtain ⟨hff, hr⟩ := hf
    · by_cases hfs : f = sel
      · subst hfs
        rw [hs] at hff
        cases hff
        simp [select_field] at h
        subst h
        exact ⟨v', by simp [select_field], hv⟩
      · have hne : f' ≠ sel' := fun e => hfs (hinj _ _ _ hff (e ▸ hs))
        simp only [select_field, hfs, dite_false] at h
        obtain ⟨u, hu, hr'⟩ := select_lowered hinj hr hvs hs h
        exact ⟨u, by simp [select_field, hne, hu], hr'⟩
  | .Param _ _ :: _, .Param _ _ :: _, [], _, _, hv, _, _, _, _, h => by simp [select_field] at h
  | .Param _ _ :: _, .Param _ _ :: _, _ :: _, [], _, hv, _, _, _, _, _ => by cases hv
  | [], .Param _ _ :: _, _, _, hf, _, _, _, _, _, _ => by simp [fieldNames, FieldsOk] at hf
  | .Param _ _ :: _, [], _, _, hf, _, _, _, _, _, _ => by simp [fieldNames, FieldsOk] at hf

/-- The field `sel` of the values `vs` of the fields `fs` is of its kind. -/
theorem select_has {T : Id → Option (Id × List LK)} {F : Id → Option (Id × LK)} {s : Id} :
    ∀ {fs : List Param} {ks : List LK} {vs : List Value}, FieldKinds F s fs ks →
      Has T (.tuple ks) (.TupleV vs) → ∀ {sel : Id} {k : LK} {v : Value}, F sel = some (s, k) →
        select_field fs vs sel = .Ok v → Has T k v
  | [], [], _, _, _, _, _, _, _, h => by simp [select_field] at h
  | .Param f _ :: fs, k0 :: ks, v0 :: vs, hf, .tupleCons hv hr, sel, k, v, hs, h => by
    simp only [FieldKinds] at hf
    by_cases hfs : f = sel
    · subst hfs
      rw [hf.1] at hs
      cases hs
      simp [select_field] at h
      subst h
      exact hv
    · simp only [select_field, hfs, dite_false] at h
      exact select_has hf.2 hr hs h
  | .Param _ _ :: _, _ :: _, [], _, _, _, _, _, _, h => by simp [select_field] at h
  | [], _ :: _, _, hf, _, _, _, _, _, _ => by simp [FieldKinds] at hf
  | .Param _ _ :: _, [], _, hf, _, _, _, _, _, _ => by simp [FieldKinds] at hf

/-- Binding the arguments of a call to the parameters of a function and the lowered arguments
to those of the function that it is lowered to gives the variables of its body their values. -/
theorem bind_lowered {K : Id → Option Id} {T : Id → Option (Id × List LK)} :
    ∀ {params params' : List Id} {ks : List LK} {vs vs' : List Value},
    params'.Nodup → params.length = ks.length → params'.length = ks.length →
    Has T (.tuple ks) (.TupleV vs) → VRs K vs vs' → ∀ {bs : List Binding},
      bind_all params vs = .Ok bs →
      ∃ bs', bind_all params' vs' = .Ok bs' ∧
        ∀ x y k, (params.zip (params'.zip ks)).lookup x = some (y, k) →
          ∃ v v', lookup_var bs x = .Ok v ∧ lookup_var bs' y = .Ok v' ∧ VR K v v' ∧ Has T k v
  | [], [], [], [], [], _, _, _, _, _, bs, hb => by
    simp [bind_all] at hb
    subst hb
    exact ⟨[], by simp [bind_all], fun x y k hx => by simp at hx⟩
  | p :: ps, p' :: ps', k :: ks, v :: vs, v' :: vs', hnd, hl1, hl2, h, hvr, bs, hb => by
    cases h with
    | tupleCons hv hr =>
      cases hvr with
      | cons hvv hvrs =>
      rw [bind_all] at hb
      split at hb
      · next bs1 hbs1 =>
        cases hb
        have hnd' := (List.nodup_cons.mp hnd)
        obtain ⟨bs1', hb1', hl⟩ :=
          bind_lowered hnd'.2 (by simpa using hl1) (by simpa using hl2) hr hvrs hbs1
        refine ⟨.Binding p' v' :: bs1', by simp [bind_all, hb1'], fun x y k2 hx => ?_⟩
        by_cases hxp : x = p
        · subst hxp
          simp at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact ⟨v, v', by simp [lookup_var], by simp [lookup_var], hvv, hv⟩
        · have hb : (x == p) = false := by simpa using hxp
          have hx' : (ps.zip (ps'.zip ks)).lookup x = some (y, k2) := by
            simpa only [List.zip_cons_cons, List.lookup, hb] using hx
          obtain ⟨u, u', h1, h2, h3, h4⟩ := hl x y k2 hx'
          have hy : y ∈ ps' := (List.of_mem_zip (List.of_mem_zip (mem_of_lookup hx')).2).1
          have hyp : y ≠ p' := fun e => hnd'.1 (e ▸ hy)
          exact ⟨u, u', by simp [lookup_var, hxp, h1], by simp [lookup_var, hyp, h2], h3, h4⟩
      · cases hb
      · cases hb
  | [], [], [], _ :: _, _, _, _, _, h, _, _, _ => by cases h
  | [], _ :: _, _, _, _, _, hl1, hl2, _, _, _, _ => by simp at hl1 hl2; omega
  | _ :: _, [], _, _, _, _, hl1, hl2, _, _, _, _ => by simp at hl1 hl2; omega
  | [], [], _ :: _, _, _, _, hl1, _, _, _, _, _ => by simp at hl1
  | _ :: _, _ :: _, [], _, _, _, hl1, _, _, _, _, _ => by simp at hl1
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, h, _, _, _ => by cases h
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, hvr, _, _ => by cases hvr
  | [], [], [], [], _ :: _, _, _, _, _, hvr, _, _ => by cases hvr
theorem vr_tuple_inv {K : Id → Option Id} {vs : List Value} {t : Value}
    (h : VR K (.TupleV vs) t) : ∃ vs', t = .TupleV vs' ∧ VRs K vs vs' := by
  cases h with
  | prim hp => simp [IsPrim] at hp
  | tuple hs => exact ⟨_, rfl, hs⟩

theorem vr_bool {K : Id → Option Id} {b : Bool} {t : Value} (h : VR K (.BoolV b) t) :
    t = .BoolV b :=
  vr_prim h rfl

theorem construct_of {O : Oracle} {Q : Program} {c : Id} {fs : List Param} (h : CtorOf c fs Q)
    (fuel : Int) (env : Env) (tps : List Ty) (vs : List Value) :
    construct O Q fuel env c tps vs = .Ok (.ADTV c (O.resolve_all (env_types env) tps) vs) := by
  cases Q with
  | Program fns cs ss is eqs =>
  obtain ⟨s, tps0, eq, hc, hs⟩ := h
  simp [construct, hc, hs]

/-! ## Evaluation -/

section Evaluation
variable {O : Oracle} {Ps P : Program} {S : LSig}

theorem pick_eval {fuel : Int} {env : Env} :
    ∀ (fields : List Param) (args : List Expr) (vs : List Value) (sel : Id) {v : Value}
      {a : Expr}, select_field fields vs sel = .Ok v → eval_list O P fuel env args = .Ok vs →
      pick fields args sel = some a → eval O P fuel env a = .Ok v
  | .Param f _ :: fs, b :: bs, vs, sel, v, a, hs, hl, hp => by
    rw [eval_list] at hl
    split at hl
    · next vb hb =>
      split at hl
      · next ws hws =>
        cases hl
        simp only [pick] at hp
        simp only [select_field] at hs
        by_cases hf : f = sel
        · simp only [hf, if_true, Option.some.injEq] at hp
          simp only [hf, dite_true, Result.Ok.injEq] at hs
          subst hp; subst hs; exact hb
        · simp only [hf, if_false] at hp
          simp only [hf, dite_false] at hs
          exact pick_eval fs bs ws sel hs hws hp
      · cases hl
      · cases hl
    · cases hl
    · cases hl
  | [], _, _, _, _, _, _, _, hp => by simp [pick] at hp
  | .Param _ _ :: _, [], _, _, _, _, _, _, hp => by simp [pick] at hp

theorem construct_ok {fuel : Int} {env : Env} {c : Id} {tps : List Ty} {vs : List Value}
    {w : Value} (h : construct O P fuel env c tps vs = .Ok w) : ∃ tps', w = .ADTV c tps' vs := by
  rw [construct] at h
  repeat' (split at h)
  all_goals first | (cases h; exact ⟨_, rfl⟩) | cases h

theorem pick_eq {fuel : Int} {env : Env} :
    ∀ (fields : List Param) (args : List Expr) (vs : List Value) (sel : Id) {a : Expr},
      eval_list O P fuel env args = .Ok vs → pick fields args sel = some a →
      eval O P fuel env a = select_field fields vs sel
  | .Param f _ :: fs, b :: bs, vs, sel, a, hl, hp => by
    rw [eval_list] at hl
    split at hl
    · next vb hb =>
      split at hl
      · next ws hws =>
        cases hl
        simp only [pick] at hp
        simp only [select_field]
        by_cases hf : f = sel
        · simp only [hf, if_true, Option.some.injEq] at hp
          subst hp; simp [hf, hb]
        · simp only [hf, if_false] at hp
          simp only [hf, dite_false]
          exact pick_eq fs bs ws sel hws hp
      · cases hl
      · cases hl
    · cases hl
    · cases hl
  | [], _, _, _, _, _, hp => by simp [pick] at hp
  | .Param _ _ :: _, [], _, _, _, _, hp => by simp [pick] at hp

theorem eval_lists_eq {f1 f2 : Int} {env1 env2 : Env} {r : Expr → Option Expr}
    (ih : ∀ e e', r e = some e' → eval O P f1 env1 e = eval O P f2 env2 e') :
    ∀ (es es' : List Expr), es.mapM r = some es' →
      eval_and O P f1 env1 es = eval_and O P f2 env2 es' ∧
      eval_or O P f1 env1 es = eval_or O P f2 env2 es'
  | [], es', h => by
    simp at h; subst h
    exact ⟨by rw [eval_and, eval_and], by rw [eval_or, eval_or]⟩
  | a :: as, es', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨a', ha, as', has, rfl⟩ := h
    obtain ⟨h2, h3⟩ := eval_lists_eq ih as as' has
    have hae := ih a a' ha
    exact ⟨by rw [eval_and, eval_and, eval_bool, eval_bool, hae, h2],
      by rw [eval_or, eval_or, eval_bool, eval_bool, hae, h3]⟩

/-- Where `p` is a construction of `c` of the values `vs` of the arguments `args`, the body of
an invariant has the value of what `instInv` makes of it, whatever the fuel and the types. -/
theorem instInv_eval {p : Id} {fields : List Param} {args : List Expr} {f1 f2 : Int}
    {env1 env2 : Env} {c s : Id} {tps : List Ty} {vs : List Value}
    (hp : lookup_var (env_vars env1) p = .Ok (.ADTV c tps vs))
    (hc : ∃ fns cs ss is eqm c0, P = .Program fns cs ss is eqm ∧
      lookup_ctor cs c = .Ok (.Constructor c0 s fields))
    (ha : eval_list O P f2 env2 args = .Ok vs) :
    ∀ n e e', instInv p fields args n e = some e' → eval O P f1 env1 e = eval O P f2 env2 e'
  | 0, _, _, h => by simp [instInv] at h
  | n + 1, e, e', h => by
    have ih := instInv_eval (f1 := f1) hp hc ha n
    cases e <;> simp only [instInv, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    all_goals first
      | (obtain ⟨a', h1, b', h2, rfl⟩ := h; simp only [eval, eval_bool, ih _ _ h1, ih _ _ h2])
      | (obtain ⟨a', h1, rfl⟩ := h; simp only [eval, eval_bool, ih _ _ h1])
      | (cases h; done)
      | (cases h; simp only [eval]; done)
      | (obtain ⟨c', h1, a', h2, b', h3, rfl⟩ := h
         simp only [eval, eval_bool, ih _ _ h1, ih _ _ h2, ih _ _ h3])
      | (obtain ⟨es', hes, rfl⟩ := h
         simp only [eval]
         first | exact (eval_lists_eq ih _ _ hes).1 | exact (eval_lists_eq ih _ _ hes).2)
      | skip
    split at h
    · next q =>
      by_cases hq : q = p
      · subst hq
        simp only [if_true] at h
        obtain ⟨fns, cs, ss, is, eqm, c0, rfl, hcs⟩ := hc
        simp only [eval, hp, hcs]
        exact (pick_eq fields args vs _ ha h).symm
      · simp [hq] at h
    · obtain ⟨a', h1, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [eval, ih _ _ h1]

/-- The variables of `Γ` have values in `env` and `env'` that relate, of their kinds. -/
def EnvOk (O : Oracle) (P : Program) (K : Id → Option Id) (T : Id → Option (Id × List LK))
    (Γ : Id → Option (Expr × LK)) (env env' : Env) : Prop :=
  ∀ x y k, Γ x = some (y, k) → ∃ v, lookup_var (env_vars env) x = .Ok v ∧ Has T k v ∧
    ∃ (v' : Value) (m : Int), VR K v v' ∧ ∀ fuel : Int, m ≤ fuel → eval O P fuel env' y = .Ok v'

theorem envOk_params {O : Oracle} {P : Program} {K : Id → Option Id}
    {T : Id → Option (Id × List LK)}
    {params params' : List Id} {ks : List LK} {tys tys' : List TypeBinding} {bs bs' : List Binding}
    (h : ∀ x y k, (params.zip (params'.zip ks)).lookup x = some (y, k) →
      ∃ v v', lookup_var bs x = .Ok v ∧ lookup_var bs' y = .Ok v' ∧ VR K v v' ∧ Has T k v) :
    EnvOk O P K T (paramsCtx params params' ks) (.Env tys bs) (.Env tys' bs') := by
  intro x y k hx
  simp only [paramsCtx, Option.map_eq_some_iff] at hx
  obtain ⟨⟨y0, k0⟩, hl, he⟩ := hx
  cases he
  obtain ⟨v, v', h1, h2, h3, h4⟩ := h x y0 k0 hl
  exact ⟨v, h1, h4, v', 0, h3, fun _ _ => by simp only [eval, env_vars, h2]⟩

theorem envOk_letIn {O : Oracle} {P : Program} {K : Id → Option Id}
    {T : Id → Option (Id × List LK)}
    {Γ : Id → Option (Expr × LK)} {env env' : Env} {x : Id} {a' : Expr} {ka : LK} {va va' : Value}
    {m : Int} (h : EnvOk O P K T Γ env env') (hk : Has T ka va) (hr : VR K va va')
    (he : ∀ fuel : Int, m ≤ fuel → eval O P fuel env' a' = .Ok va') :
    EnvOk O P K T (bindCtx Γ x (some (a', ka))) (env_bind env x va) env' := by
  intro z y k hz
  cases env with
  | Env tys bs =>
  by_cases hzx : z = x
  · subst hzx
    simp only [bindCtx, if_true, Option.some.injEq, Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl⟩ := hz
    exact ⟨va, by simp [env_bind, env_vars, lookup_var], hk, va', m, hr, he⟩
  · simp only [bindCtx, hzx, if_false] at hz
    obtain ⟨v, h1, h2, h3⟩ := h z y k hz
    exact ⟨v, by simpa [env_bind, env_vars, lookup_var, hzx] using h1, h2, h3⟩

theorem envOk_letDrop {O : Oracle} {P : Program} {K : Id → Option Id}
    {T : Id → Option (Id × List LK)} {Γ : Id → Option (Expr × LK)} {env env' : Env} {x : Id}
    {va : Value} (h : EnvOk O P K T Γ env env') :
    EnvOk O P K T (bindCtx Γ x none) (env_bind env x va) env' := by
  intro z y k hz
  cases env with
  | Env tys bs =>
  by_cases hzx : z = x
  · subst hzx
    simp [bindCtx] at hz
  · simp only [bindCtx, hzx, if_false] at hz
    obtain ⟨v, h1, h2, h3⟩ := h z y k hz
    exact ⟨v, by simpa [env_bind, env_vars, lookup_var, hzx] using h1, h2, h3⟩

theorem toSigned_inv {Q : Program} {fuel : Int} {env : Env} {a : Expr} {v : Value}
    (h : eval O Q fuel env (.BVUnsignedToSigned a) = .Ok v) :
    ∃ w x, v = .BVV true w x ∧ eval O Q fuel env a = .Ok (.BVV false w x) := by
  simp only [eval] at h
  split at h
  · next va ha =>
    split at h
    · cases h; exact ⟨_, _, rfl, ha⟩
    · cases h
  · cases h
  · cases h

theorem toUnsigned_inv {Q : Program} {fuel : Int} {env : Env} {a : Expr} {v : Value}
    (h : eval O Q fuel env (.BVSignedToUnsigned a) = .Ok v) :
    ∃ w x, v = .BVV false w x ∧ eval O Q fuel env a = .Ok (.BVV true w x) := by
  simp only [eval] at h
  split at h
  · next va ha =>
    split at h
    · cases h; exact ⟨_, _, rfl, ha⟩
    · cases h
  · cases h
  · cases h

/-- What is lowered to the signed view of `a'` is a signed bit-vector, whose unsigned view is the
value of `a'`. -/
theorem unsigned_of {Q : Program} {env : Env} {a' : Expr} {w x : Int} {m : Int}
    (h : ∀ f : Int, m ≤ f → eval O Q f env (.BVUnsignedToSigned a') = .Ok (.BVV true w x)) :
    ∀ f : Int, m ≤ f → eval O Q f env a' = .Ok (.BVV false w x) := by
  intro f hf
  obtain ⟨w', x', he, h'⟩ := toSigned_inv (h f hf)
  cases he
  exact h'

/-- Where an expression of the input evaluates to a value, the expression that it is lowered
to evaluates with enough fuel to a value that relates to it, and it is of the kind of the
relation. -/
theorem lowers_eval (hO : O.Sound) (hF : Funs Ps P S) (hC : Ctors Ps P S) :
    ∀ (n : Nat) {Γ : Id → Option (Expr × LK)} {e e' : Expr} {k : LK}, Lowers S Γ e e' k →
      ∀ (env env' : Env), EnvOk O P S.ctors S.kinds Γ env env' →
        ∀ (fuel : Int), fuel ≤ n → ∀ (v : Value), eval O Ps fuel env e = .Ok v →
          Has S.kinds k v ∧ ∃ (v' : Value) (m : Int), VR S.ctors v v' ∧
            ∀ fuel' : Int, m ≤ fuel' → eval O P fuel' env' e' = .Ok v' := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro Γ e e' k h
  induction h with
  | var hx =>
    intro env env' hΓ fuel hfn v hv
    obtain ⟨w, h1, hk, w', m, hr, h2⟩ := hΓ _ _ _ hx
    simp only [eval, h1] at hv
    cases hv
    exact ⟨hk, w', m, hr, h2⟩
  | letIn _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
      exact ihb _ env' (envOk_letIn hΓ hka ra e1) fuel hfn v hv
    · cases hv
    · cases hv
  | letDrop _ ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · exact ihb _ env' (envOk_letDrop hΓ) fuel hfn v hv
    · cases hv
    · cases hv
  | int n =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    cases hv
    exact ⟨.int n, _, 0, .prim rfl, fun _ _ => by simp only [eval]⟩
  | bool b =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    cases hv
    exact ⟨.prim rfl, _, 0, .prim rfl, fun _ _ => by simp only [eval]⟩
  | frac n d =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    exact ⟨.prim (real_prim hv), v, 0, .prim (real_prim hv),
      fun _ _ => by simp only [eval]; exact hv⟩
  | error e' k =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    cases hv
  | bvLit s w x =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    cases hv
    exact ⟨.prim rfl, _, 0, .prim rfl, fun _ _ => by simp only [eval]⟩
  | bvSignedLit w x =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    cases hv
    exact ⟨.prim rfl, _, 0, .prim rfl, fun _ _ => by simp only [eval]⟩
  | toUnsigned _ iha =>
    intro env env' hΓ fuel hfn v hv
    obtain ⟨w, x, rfl, ha⟩ := toUnsigned_inv hv
    obtain ⟨_, v', n1, r1, e1⟩ := iha env env' hΓ fuel hfn _ ha
    rw [vr_prim r1 rfl] at e1
    exact ⟨.prim rfl, _, n1, .prim rfl, unsigned_of e1⟩
  | toSigned _ iha =>
    intro env env' hΓ fuel hfn v hv
    obtain ⟨w, x, rfl, ha⟩ := toSigned_inv hv
    obtain ⟨_, v', n1, r1, e1⟩ := iha env env' hΓ fuel hfn _ ha
    rw [vr_prim r1 rfl] at e1
    exact ⟨.prim rfl, _, n1, .prim rfl, fun f hf => by simp only [eval, e1 f hf]⟩
  | eqSigned _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        cases hka with
        | prim hpa =>
        cases hkb with
        | prim hpb =>
        rw [vr_prim ra hpa] at e1; rw [vr_prim rb hpb] at e2
        obtain ⟨wa, xa, rfl, _⟩ := toSigned_inv (e1 n1 (Int.le_refl _))
        obtain ⟨wb, xb, rfl, _⟩ := toSigned_inv (e2 n2 (Int.le_refl _))
        have ea := unsigned_of e1
        have eb := unsigned_of e2
        split at hv
        · next r hr =>
          cases hv
          have hr' : O.value_eq P (.BVV false wa xa) (.BVV false wb xb) = .Ok r := by
            rw [← hr, hO.value_eq, hO.value_eq (P := Ps)]
            simp
          refine ⟨.prim rfl, _, max n1 n2, .prim rfl, fun f hf => ?_⟩
          simp only [eval, ea f (by omega), eb f (by omega), hr']
        · cases hv
        · cases hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | weaken _ hs ih =>
    intro env env' hΓ fuel hfn v hv
    obtain ⟨hk, v', m, hr, e1⟩ := ih env env' hΓ fuel hfn v hv
    exact ⟨has_sub hs hk, v', m, hr, e1⟩
  | plusInt _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        cases hka; cases hkb
        rw [vr_prim ra rfl] at e1; rw [vr_prim rb rfl] at e2
        simp only [arith_plus] at hv; cases hv
        refine ⟨.int _, _, max n1 n2, .prim rfl, fun f hf => ?_⟩
        simp only [eval, e1 f (by omega), e2 f (by omega), arith_plus]
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | plusZero _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        cases hka; cases hkb
        rw [vr_prim ra rfl] at e1; rw [vr_prim rb rfl] at e2
        simp only [arith_plus] at hv; cases hv
        refine ⟨.int _, _, max n1 n2, .prim rfl, fun f hf => ?_⟩
        simp only [eval, e1 f (by omega), e2 f (by omega), arith_plus, Int.add_zero]
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | plus _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        obtain ⟨pa, pb⟩ := plus_args hv
        rw [vr_prim ra pa] at e1; rw [vr_prim rb pb] at e2
        refine ⟨.prim (plus_prim hv), v, max n1 n2, .prim (plus_prim hv), fun f hf => ?_⟩
        simp only [eval, e1 f (by omega), e2 f (by omega)]
        exact hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | minusInt _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        cases hka; cases hkb
        rw [vr_prim ra rfl] at e1; rw [vr_prim rb rfl] at e2
        simp only [arith_minus] at hv; cases hv
        refine ⟨.int _, _, max n1 n2, .prim rfl, fun f hf => ?_⟩
        simp only [eval, e1 f (by omega), e2 f (by omega), arith_minus]
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | minus _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        obtain ⟨pa, pb⟩ := minus_args hv
        rw [vr_prim ra pa] at e1; rw [vr_prim rb pb] at e2
        refine ⟨.prim (minus_prim hv), v, max n1 n2, .prim (minus_prim hv), fun f hf => ?_⟩
        simp only [eval, e1 f (by omega), e2 f (by omega)]
        exact hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | timesInt _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        cases hka; cases hkb
        rw [vr_prim ra rfl] at e1; rw [vr_prim rb rfl] at e2
        simp only [arith_times] at hv; cases hv
        refine ⟨.int _, _, max n1 n2, .prim rfl, fun f hf => ?_⟩
        simp only [eval, e1 f (by omega), e2 f (by omega), arith_times]
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | times _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        obtain ⟨pa, pb⟩ := times_args hv
        rw [vr_prim ra pa] at e1; rw [vr_prim rb pb] at e2
        refine ⟨.prim (times_prim hv), v, max n1 n2, .prim (times_prim hv), fun f hf => ?_⟩
        simp only [eval, e1 f (by omega), e2 f (by omega)]
        exact hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | uminusInt _ iha =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
      cases hka
      rw [vr_prim ra rfl] at e1
      simp only [arith_neg] at hv; cases hv
      exact ⟨.int _, _, n1, .prim rfl, fun f hf => by simp only [eval, e1 f hf, arith_neg]⟩
    · cases hv
    · cases hv
  | uminus _ iha =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
      rw [vr_prim ra (neg_args hv)] at e1
      exact ⟨.prim (neg_prim hv), v, n1, .prim (neg_prim hv),
        fun f hf => by simp only [eval, e1 f hf]; exact hv⟩
    · cases hv
    · cases hv
  | timesOne _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        cases hka; cases hkb
        rw [vr_prim ra rfl] at e1; rw [vr_prim rb rfl] at e2
        simp only [arith_times] at hv; cases hv
        refine ⟨.int _, _, max n1 n2, .prim rfl, fun f hf => ?_⟩
        simp only [eval, e1 f (by omega), e2 f (by omega), arith_times, Int.mul_one]
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | divInt _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        cases hka; cases hkb
        rw [vr_prim ra rfl] at e1; rw [vr_prim rb rfl] at e2
        simp only [arith_div] at hv
        split at hv
        · cases hv
        · cases hv
          refine ⟨.int _, _, max n1 n2, .prim rfl, fun f hf => ?_⟩
          simp only [eval, e1 f (by omega), e2 f (by omega), arith_div]
          simp_all
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | modInt _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        cases hka; cases hkb
        rw [vr_prim ra rfl] at e1; rw [vr_prim rb rfl] at e2
        simp only [arith_mod] at hv
        split at hv
        · cases hv
        · cases hv
          refine ⟨.int _, _, max n1 n2, .prim rfl, fun f hf => ?_⟩
          simp only [eval, e1 f (by omega), e2 f (by omega), arith_mod]
          simp_all
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | remInt _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        cases hka; cases hkb
        rw [vr_prim ra rfl] at e1; rw [vr_prim rb rfl] at e2
        simp only [arith_rem] at hv
        split at hv
        · cases hv
        · cases hv
          refine ⟨.int _, _, max n1 n2, .prim rfl, fun f hf => ?_⟩
          simp only [eval, e1 f (by omega), e2 f (by omega), arith_rem]
          simp_all
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | div _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        obtain ⟨pa, pb⟩ := div_args hv
        rw [vr_prim ra pa] at e1; rw [vr_prim rb pb] at e2
        refine ⟨.prim (div_prim hv), v, max n1 n2, .prim (div_prim hv), fun f hf => ?_⟩
        simp only [eval, e1 f (by omega), e2 f (by omega)]
        exact hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | rem _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        obtain ⟨pa, pb⟩ := rem_args hv
        rw [vr_prim ra pa] at e1; rw [vr_prim rb pb] at e2
        refine ⟨.prim (rem_prim hv), v, max n1 n2, .prim (rem_prim hv), fun f hf => ?_⟩
        simp only [eval, e1 f (by omega), e2 f (by omega)]
        exact hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | mod _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        obtain ⟨pa, pb⟩ := mod_args hv
        rw [vr_prim ra pa] at e1; rw [vr_prim rb pb] at e2
        refine ⟨.prim (mod_prim hv), v, max n1 n2, .prim (mod_prim hv), fun f hf => ?_⟩
        simp only [eval, e1 f (by omega), e2 f (by omega)]
        exact hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | lt _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        split at hv
        · next r hr =>
          cases hv
          have hp : IsPrim va = true ∧ IsPrim vb = true := by
            first
              | exact lt_args hr
              | exact (lt_args hr).symm
              | exact le_args hr
              | exact (le_args hr).symm
          rw [vr_prim ra hp.1] at e1; rw [vr_prim rb hp.2] at e2
          refine ⟨.prim rfl, _, max n1 n2, .prim rfl, fun f hf => ?_⟩
          simp only [eval, e1 f (by omega), e2 f (by omega), hr]
        · cases hv
        · cases hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | gt _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        split at hv
        · next r hr =>
          cases hv
          have hp : IsPrim va = true ∧ IsPrim vb = true := by
            first
              | exact lt_args hr
              | exact (lt_args hr).symm
              | exact le_args hr
              | exact (le_args hr).symm
          rw [vr_prim ra hp.1] at e1; rw [vr_prim rb hp.2] at e2
          refine ⟨.prim rfl, _, max n1 n2, .prim rfl, fun f hf => ?_⟩
          simp only [eval, e1 f (by omega), e2 f (by omega), hr]
        · cases hv
        · cases hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | le _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        split at hv
        · next r hr =>
          cases hv
          have hp : IsPrim va = true ∧ IsPrim vb = true := by
            first
              | exact lt_args hr
              | exact (lt_args hr).symm
              | exact le_args hr
              | exact (le_args hr).symm
          rw [vr_prim ra hp.1] at e1; rw [vr_prim rb hp.2] at e2
          refine ⟨.prim rfl, _, max n1 n2, .prim rfl, fun f hf => ?_⟩
          simp only [eval, e1 f (by omega), e2 f (by omega), hr]
        · cases hv
        · cases hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | ge _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        split at hv
        · next r hr =>
          cases hv
          have hp : IsPrim va = true ∧ IsPrim vb = true := by
            first
              | exact lt_args hr
              | exact (lt_args hr).symm
              | exact le_args hr
              | exact (le_args hr).symm
          rw [vr_prim ra hp.1] at e1; rw [vr_prim rb hp.2] at e2
          refine ⟨.prim rfl, _, max n1 n2, .prim rfl, fun f hf => ?_⟩
          simp only [eval, e1 f (by omega), e2 f (by omega), hr]
        · cases hv
        · cases hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | eq _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, va', n1, ra, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, vb', n2, rb, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        split at hv
        · next r hr =>
          cases hv
          rw [vr_has ra hka (by simp)] at e1; rw [vr_has rb hkb (by simp)] at e2
          have hr' : O.value_eq P va vb = .Ok r := by
            rw [← hr, hO.value_eq, hO.value_eq (P := Ps)]
            cases hka with
            | prim hp => cases va <;> simp_all [IsPrim]
          refine ⟨.prim rfl, _, max n1 n2, .prim rfl, fun f hf => ?_⟩
          simp only [eval, e1 f (by omega), e2 f (by omega), hr']
        · cases hv
        · cases hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | not _ iha =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next b hb =>
      obtain ⟨_, _, n1, r1, e1⟩ := iha env env' hΓ fuel hfn _ (eval_bool_ok hb)
      rw [vr_bool r1] at e1
      cases hv
      exact ⟨.prim rfl, _, n1, .prim rfl, fun f hf => by simp [eval, eval_bool, e1 f hf]⟩
    · cases hv
    · cases hv
  | implies _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next a ha =>
      obtain ⟨_, _, n1, r1, e1⟩ := iha env env' hΓ fuel hfn _ (eval_bool_ok ha)
      rw [vr_bool r1] at e1
      cases a with
      | true =>
        simp only [dite_true] at hv
        split at hv
        · next b hb =>
          obtain ⟨_, _, n2, r2, e2⟩ := ihb env env' hΓ fuel hfn _ (eval_bool_ok hb)
          rw [vr_bool r2] at e2
          cases hv
          exact ⟨.prim rfl, _, max n1 n2, .prim rfl, fun f hf => by
            simp [eval, eval_bool, e1 f (by omega), e2 f (by omega)]⟩
        · cases hv
        · cases hv
      | false =>
        simp at hv
        cases hv
        exact ⟨.prim rfl, _, n1, .prim rfl, fun f hf => by simp [eval, eval_bool, e1 f hf]⟩
    · cases hv
    · cases hv
  | andNil =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    rw [eval_and] at hv
    cases hv
    exact ⟨.prim rfl, _, 0, .prim rfl, fun _ _ => by simp only [eval]; rw [eval_and]⟩
  | andCons _ _ iha ihr =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    rw [eval_and] at hv
    split at hv
    · next b hb =>
      obtain ⟨_, _, n1, r1, e1⟩ := iha env env' hΓ fuel hfn _ (eval_bool_ok hb)
      rw [vr_bool r1] at e1
      cases b with
      | true =>
        simp only [dite_true] at hv
        obtain ⟨hk, v', n2, r2, e2⟩ := ihr env env' hΓ fuel hfn v (by simp only [eval]; exact hv)
        refine ⟨hk, v', max n1 n2, r2, fun f hf => ?_⟩
        have h2 := e2 f (by omega)
        simp only [eval] at h2 ⊢
        rw [eval_and]
        simp only [eval_bool, e1 f (by omega), dite_true, h2]
      | false =>
        simp at hv
        cases hv
        refine ⟨.prim rfl, _, n1, .prim rfl, fun f hf => ?_⟩
        simp only [eval]
        rw [eval_and]
        simp [eval_bool, e1 f hf]
    · cases hv
    · cases hv
  | orNil =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    rw [eval_or] at hv
    cases hv
    exact ⟨.prim rfl, _, 0, .prim rfl, fun _ _ => by simp only [eval]; rw [eval_or]⟩
  | orCons _ _ iha ihr =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    rw [eval_or] at hv
    split at hv
    · next b hb =>
      obtain ⟨_, _, n1, r1, e1⟩ := iha env env' hΓ fuel hfn _ (eval_bool_ok hb)
      rw [vr_bool r1] at e1
      cases b with
      | false =>
        simp at hv
        obtain ⟨hk, v', n2, r2, e2⟩ := ihr env env' hΓ fuel hfn v (by simp only [eval]; exact hv)
        refine ⟨hk, v', max n1 n2, r2, fun f hf => ?_⟩
        have h2 := e2 f (by omega)
        simp only [eval] at h2 ⊢
        rw [eval_or]
        simp [eval_bool, e1 f (by omega), h2]
      | true =>
        simp only [dite_true] at hv
        cases hv
        refine ⟨.prim rfl, _, n1, .prim rfl, fun f hf => ?_⟩
        simp only [eval]
        rw [eval_or]
        simp [eval_bool, e1 f hf]
    · cases hv
    · cases hv
  | ite _ _ _ ihc iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next c hc =>
      obtain ⟨_, _, n1, r1, e1⟩ := ihc env env' hΓ fuel hfn _ (eval_bool_ok hc)
      rw [vr_bool r1] at e1
      cases c with
      | true =>
        simp only [dite_true] at hv
        obtain ⟨hk, v', n2, r2, e2⟩ := iha env env' hΓ fuel hfn v hv
        exact ⟨hk, v', max n1 n2, r2, fun f hf => by
          simp [eval, eval_bool, e1 f (by omega), e2 f (by omega)]⟩
      | false =>
        simp at hv
        obtain ⟨hk, v', n2, r2, e2⟩ := ihb env env' hΓ fuel hfn v hv
        exact ⟨hk, v', max n1 n2, r2, fun f hf => by
          simp [eval, eval_bool, e1 f (by omega), e2 f (by omega)]⟩
    · cases hv
    · cases hv
  | assume _ _ ihp ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next c hc =>
      obtain ⟨_, _, n1, r1, e1⟩ := ihp env env' hΓ fuel hfn _ (eval_bool_ok hc)
      rw [vr_bool r1] at e1
      cases c with
      | true =>
        simp only [dite_true] at hv
        obtain ⟨hk, v', n2, r2, e2⟩ := ihb env env' hΓ fuel hfn v hv
        exact ⟨hk, v', max n1 n2, r2, fun f hf => by
          simp [eval, eval_bool, e1 f (by omega), e2 f (by omega)]⟩
      | false =>
        simp at hv
    · cases hv
    · cases hv
  | tupleNil =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval, eval_list] at hv
    cases hv
    exact ⟨.tupleNil, _, 0, .tuple .nil, fun _ _ => by simp only [eval, eval_list]⟩
  | tupleCons _ _ ihe ihr =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    rw [eval_list] at hv
    split at hv
    · next vs hvs =>
      cases hv
      split at hvs
      · next w hw =>
        split at hvs
        · next ws hws =>
          cases hvs
          obtain ⟨hk1, w', n1, r1, e1⟩ := ihe env env' hΓ fuel hfn w hw
          obtain ⟨hk2, t', n2, r2, e2⟩ :=
            ihr env env' hΓ fuel hfn (.TupleV ws) (by simp only [eval, hws])
          obtain ⟨ws', rfl, hws'⟩ := vr_tuple_inv r2
          refine ⟨.tupleCons hk1 hk2, _, max n1 n2, .tuple (.cons r1 hws'), fun f hf => ?_⟩
          simp only [eval]
          rw [eval_list]
          simp only [e1 f (by omega), eval_tuple_inv (e2 f (by omega))]
        · cases hvs
        · cases hvs
      · cases hvs
      · cases hvs
    · cases hv
    · cases hv
  | @call _ f g ks k tps tps' es es' hf _ iha =>
    intro env env' hΓ fuel hfn v hv
    obtain ⟨tparams, params, params', body, body', hFS, hFP, hnd, hl1, hl2, hlow⟩ :=
      hF f g ks k hf
    simp only [eval] at hv
    split at hv
    · next vs hvs =>
      obtain ⟨hpos, bs, hbs, hbody⟩ := call_inv hFS hv
      obtain ⟨hHas, t', n1, rt, e1⟩ :=
        iha env env' hΓ fuel hfn (.TupleV vs) (by simp only [eval, hvs])
      obtain ⟨vs', rfl, hvrs⟩ := vr_tuple_inv rt
      obtain ⟨bs', hbs', hl⟩ := bind_lowered hnd hl1 hl2 hHas hvrs hbs
      cases n with
      | zero => omega
      | succ m =>
      obtain ⟨hk, v', m2, rv, e2⟩ := ihn m (Nat.lt_succ_self m) hlow
        (Env.Env (bind_types tparams tps (env_types env)) bs)
        (Env.Env (bind_types [] tps' (env_types env')) bs') (envOk_params hl) (fuel - 1)
        (by omega) v hbody
      refine ⟨hk, v', max (max n1 (m2 + 1)) 1, rv, fun f' hf' => ?_⟩
      simp only [eval, eval_tuple_inv (e1 f' (by omega))]
      rw [call_fun hFP (by omega) _ _ hbs']
      exact e2 (f' - 1) (by omega)
    · cases hv
    · cases hv
  | @adt _ c c' ks tps tps' es es' hc _ iha =>
    intro env env' hΓ fuel hfn v hv
    obtain ⟨fs, fs', hS, hP, _⟩ := hC.ctor c c' hc
    simp only [eval] at hv
    split at hv
    · next vs hvs =>
      obtain ⟨tps0, rfl⟩ := construct_ok hv
      obtain ⟨_, t', n1, rt, e1⟩ :=
        iha env env' hΓ fuel hfn (.TupleV vs) (by simp only [eval, hvs])
      obtain ⟨vs', rfl, hvrs⟩ := vr_tuple_inv rt
      refine ⟨.any _, .ADTV c' (O.resolve_all (env_types env') tps') vs', n1, .adt hc hvrs,
        fun f hf => ?_⟩
      simp only [eval, eval_tuple_inv (e1 f hf)]
      rw [construct_of hP]
    · cases hv
    · cases hv
  | @adtInv _ c c' p fields B I J n0 ks k0 tps tps' es es' hc hv0 hI _ _ hk0 ihi iha =>
    intro env env' hΓ fuel hfn v hv
    obtain ⟨fs, fs', _, hP, _⟩ := hC.ctor c c' hc
    obtain ⟨fns, cs, ss, is, eqm, c0, s, s0, tpsS, eq, inv, tparams, hPs, hcs, hss, hfun⟩ :=
      hC.inv c p fields B hv0
    simp only [eval] at hv
    split at hv
    · next vs hvs =>
      have hw := hv
      obtain ⟨tps0, rfl⟩ := construct_ok hw
      subst hPs
      rw [construct] at hv
      simp only [hcs, hss] at hv
      split at hv
      · next holds hcall =>
        split at hv
        · obtain ⟨_, bs, hbs, hB⟩ := call_inv hfun hcall
          simp only [bind_all, Result.Ok.injEq] at hbs
          subst hbs
          have hI' : eval O (.Program fns cs ss is eqm) fuel env I = .Ok (.BoolV true) := by
            rw [← instInv_eval (f1 := fuel - 1) (tps := O.resolve_all (env_types env) tps)
              (env1 := Env.Env (bind_types tparams tps (env_types env))
                [.Binding p (.ADTV c (O.resolve_all (env_types env) tps) vs)])
              (by simp [env_vars, lookup_var]) ⟨fns, cs, ss, is, eqm, c0, rfl, hcs⟩ hvs n0 B I hI]
            exact hB
          obtain ⟨_, w', n1, r1, e1⟩ := ihi env env' hΓ fuel hfn _ hI'
          rw [vr_bool r1] at e1
          obtain ⟨hks, t', n2, rt, e2⟩ :=
            iha env env' hΓ fuel hfn (.TupleV vs) (by simp only [eval, hvs])
          obtain ⟨vs', rfl, hvrs⟩ := vr_tuple_inv rt
          have hk : Has S.kinds k0 (.ADTV c tps0 vs) := by
            rcases hk0 with rfl | ⟨s1, rfl, hs1⟩
            · exact .any _
            · exact .data hs1 hks
          refine ⟨hk, .ADTV c' (O.resolve_all (env_types env') tps') vs', max n1 n2,
            .adt hc hvrs, fun f hf => ?_⟩
          simp only [eval, eval_bool, e1 f (by omega), dite_true,
            eval_tuple_inv (e2 f (by omega))]
          rw [construct_of hP]
        · cases hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | @isCtor _ e e' c c' hc _ ihe =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      obtain ⟨_, va', n1, ra, e1⟩ := ihe env env' hΓ fuel hfn va ha
      cases ra with
      | prim hp => cases va <;> simp [IsPrim] at hp <;> simp at hv
      | tuple _ => simp at hv
      | @adt d d' tps tps' ws ws' hd _ =>
        simp only at hv
        cases hv
        have hiff : (c = d) ↔ (c' = d') := by
          constructor
          · intro h; subst h; rw [hc] at hd; cases hd; rfl
          · intro h; subst h; exact hC.ctorInj _ _ _ hc hd
        refine ⟨.prim rfl, _, n1, .prim rfl, fun f hf => ?_⟩
        simp only [eval, e1 f hf]
        simp [hiff]
    · cases hv
    · cases hv
  | @sel _ e e' f0 f0' hf _ ihe =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      obtain ⟨_, va', n1, ra, e1⟩ := ihe env env' hΓ fuel hfn va ha
      cases ra with
      | prim hp => cases va <;> simp [IsPrim] at hp <;> simp at hv
      | tuple _ => simp at hv
      | @adt c c' tps tps' ws ws' hc hws =>
        obtain ⟨fs, fs', hS, hP, hfs⟩ := hC.ctor c c' hc
        cases Ps with
        | Program fns cs ss is eqs =>
        cases P with
        | Program fns' cs' ss' is' eqs' =>
        obtain ⟨s, hcs⟩ := hS
        obtain ⟨s', tp0', eq0', hcs', _⟩ := hP
        simp only [hcs] at hv
        obtain ⟨v', hv', rv⟩ := select_lowered hC.fieldInj hfs hws hf hv
        refine ⟨.any _, v', n1, rv, fun f hf' => ?_⟩
        simp only [eval, e1 f hf', hcs', hv']
    · cases hv
    · cases hv
  | @adtData _ c c' s ks tps tps' es es' hc hk _ iha =>
    intro env env' hΓ fuel hfn v hv
    obtain ⟨fs, fs', hS, hP, _⟩ := hC.ctor c c' hc
    simp only [eval] at hv
    split at hv
    · next vs hvs =>
      obtain ⟨tps0, rfl⟩ := construct_ok hv
      obtain ⟨hks, t', n1, rt, e1⟩ :=
        iha env env' hΓ fuel hfn (.TupleV vs) (by simp only [eval, hvs])
      obtain ⟨vs', rfl, hvrs⟩ := vr_tuple_inv rt
      refine ⟨.data hk hks, .ADTV c' (O.resolve_all (env_types env') tps') vs', n1,
        .adt hc hvrs, fun f hf => ?_⟩
      simp only [eval, eval_tuple_inv (e1 f hf)]
      rw [construct_of hP]
    · cases hv
    · cases hv
  | @selData _ e e' f0 f0' s0 k0 hf hk _ ihe =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      obtain ⟨hka, va', n1, ra, e1⟩ := ihe env env' hΓ fuel hfn va ha
      cases ra with
      | prim hp => cases va <;> simp [IsPrim] at hp <;> simp at hv
      | tuple _ => simp at hv
      | @adt c c' tps tps' ws ws' hc hws =>
        cases hka with
        | @data _ _ ks _ _ hck hks =>
        obtain ⟨fs, fs', hS, hP, hfs⟩ := hC.ctor c c' hc
        obtain ⟨fs0, hS0, hfk⟩ := hC.kinds c s0 ks hck
        cases Ps with
        | Program fns cs ss is eqs =>
        cases P with
        | Program fns' cs' ss' is' eqs' =>
        obtain ⟨s, hcs⟩ := hS
        obtain ⟨s1, hcs0⟩ := hS0
        obtain ⟨s', tp0', eq0', hcs', _⟩ := hP
        rw [hcs] at hcs0
        cases hcs0
        simp only [hcs] at hv
        obtain ⟨v', hv', rv⟩ := select_lowered hC.fieldInj hfs hws hf hv
        refine ⟨select_has hfk hks hk hv, v', n1, rv, fun f hf' => ?_⟩
        simp only [eval, e1 f hf', hcs', hv']
    · cases hv
    · cases hv

end Evaluation

/-! ## The check -/

/-- Whether two types are the same, `n` deep, where they are of the fragment. -/
def tyEq : Nat → Ty → Ty → Bool
  | 0, _, _ => false
  | n + 1, T, T' =>
    let all (Ts Ts' : List Ty) : Bool :=
      Ts.length == Ts'.length && (Ts.zip Ts').all fun p => tyEq n p.1 p.2
    match T, T' with
    | .IntegerType, .IntegerType | .BooleanType, .BooleanType | .RealType, .RealType => true
    | .BVType s w, .BVType s' w' => s == s' && w == w'
    | .TypeParameter a, .TypeParameter b => a == b
    | .FunctionType Ts U, .FunctionType Ts' U' => all Ts Ts' && tyEq n U U'
    | .ADTType s Ts, .ADTType s' Ts' => s == s' && all Ts Ts'
    | _, _ => false

/-- Whether two parameters are the same, with types of the fragment. -/
def paramEq (n : Nat) : Param → Param → Bool
  | .Param x T, .Param y U => x == y && tyEq n T U

/-- Whether two lists of parameters are the same, with types of the fragment. -/
def paramsEq (n : Nat) (ps ps' : List Param) : Bool :=
  ps.length == ps'.length && (ps.zip ps').all fun p => paramEq n p.1 p.2

/-- Whether two expressions are the same, `n` deep, where they are of the fragment. -/
def exprEq : Nat → Expr → Expr → Bool
  | 0, _, _ => false
  | n + 1, e, e' =>
    let all (es es' : List Expr) : Bool :=
      es.length == es'.length && (es.zip es').all fun p => exprEq n p.1 p.2
    match e, e' with
    | .Variable x, .Variable y => x == y
    | .IntegerLiteral a, .IntegerLiteral b => a == b
    | .BooleanLiteral a, .BooleanLiteral b => a == b
    | .FractionLiteral a b, .FractionLiteral c d => a == c && b == d
    | .StringLiteral a, .StringLiteral b => a == b
    | .BVLiteral s w x, .BVLiteral s' w' x' => s == s' && w == w' && x == x'
    | .Error, .Error => true
    | .StringConcat a b, .StringConcat a' b' => exprEq n a a' && exprEq n b b'
    | .Plus a b, .Plus a' b' => exprEq n a a' && exprEq n b b'
    | .Minus a b, .Minus a' b' => exprEq n a a' && exprEq n b b'
    | .Times a b, .Times a' b' => exprEq n a a' && exprEq n b b'
    | .Division a b, .Division a' b' => exprEq n a a' && exprEq n b b'
    | .Remainder a b, .Remainder a' b' => exprEq n a a' && exprEq n b b'
    | .Modulo a b, .Modulo a' b' => exprEq n a a' && exprEq n b b'
    | .LessThan a b, .LessThan a' b' => exprEq n a a' && exprEq n b b'
    | .GreaterThan a b, .GreaterThan a' b' => exprEq n a a' && exprEq n b b'
    | .LessEquals a b, .LessEquals a' b' => exprEq n a a' && exprEq n b b'
    | .GreaterEquals a b, .GreaterEquals a' b' => exprEq n a a' && exprEq n b b'
    | .Equals a b, .Equals a' b' => exprEq n a a' && exprEq n b b'
    | .Implies a b, .Implies a' b' => exprEq n a a' && exprEq n b b'
    | .Assume a b, .Assume a' b' => exprEq n a a' && exprEq n b b'
    | .UMinus a, .UMinus a' => exprEq n a a'
    | .Not a, .Not a' => exprEq n a a'
    | .BVUnsignedToSigned a, .BVUnsignedToSigned a' => exprEq n a a'
    | .BVSignedToUnsigned a, .BVSignedToUnsigned a' => exprEq n a a'
    | .IfExpr c a b, .IfExpr c' a' b' => exprEq n c c' && exprEq n a a' && exprEq n b b'
    | .IsConstructor a c, .IsConstructor a' c' => c == c' && exprEq n a a'
    | .ADTSelector a f, .ADTSelector a' f' => f == f' && exprEq n a a'
    | .And es, .And es' => all es es'
    | .Or es, .Or es' => all es es'
    | .Tuple es, .Tuple es' => all es es'
    | .FunctionInvocation f [] es, .FunctionInvocation g [] es' => f == g && all es es'
    | .ADT c [] es, .ADT c' [] es' => c == c' && all es es'
    | .Let x a b, .Let y a' b' => x == y && exprEq n a a' && exprEq n b b'
    | .Forall ps b, .Forall ps' b' => paramsEq 1000 ps ps' && exprEq n b b'
    | .Lambda ps b, .Lambda ps' b' => paramsEq 1000 ps ps' && exprEq n b b'
    | _, _ => false

theorem list_eq_of_all {α : Type} {r : α → α → Bool} (hr : ∀ a b, r a b = true → a = b) :
    ∀ {es es' : List α}, es.length = es'.length → (∀ p ∈ es.zip es', r p.1 p.2 = true) →
      es = es'
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | a :: as, b :: bs, hl, h => by
    simp only [List.zip_cons_cons, List.mem_cons, forall_eq_or_imp] at h
    rw [hr a b h.1, list_eq_of_all hr (by simpa using hl) h.2]

theorem tyEq_eq : ∀ n T T', tyEq n T T' = true → T = T'
  | 0, _, _, h => by simp [tyEq] at h
  | n + 1, T, T', h => by
    have ih := tyEq_eq n
    unfold tyEq at h
    split at h <;>
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h <;>
      first
      | rfl
      | (obtain ⟨rfl, rfl⟩ := h; rfl)
      | (subst h; rfl)
      | (obtain ⟨⟨h1, h2⟩, h3⟩ := h; rw [list_eq_of_all ih (by simpa using h1) h2, ih _ _ h3])
      | (obtain ⟨rfl, h1, h2⟩ := h; rw [list_eq_of_all ih (by simpa using h1) h2])
      | cases h

theorem paramsEq_eq {n : Nat} {ps ps' : List Param} (h : paramsEq n ps ps' = true) : ps = ps' := by
  unfold paramsEq at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  refine list_eq_of_all (r := paramEq n) ?_ h.1 h.2
  intro p q hpq
  cases p; cases q
  simp only [paramEq, Bool.and_eq_true, beq_iff_eq] at hpq
  rw [hpq.1, tyEq_eq _ _ _ hpq.2]

theorem exprEq_eq : ∀ n e e', exprEq n e e' = true → e = e'
  | 0, _, _, h => by simp [exprEq] at h
  | n + 1, e, e', h => by
    have ih := exprEq_eq n
    unfold exprEq at h
    split at h <;>
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h <;>
      first
      | rfl
      | (obtain ⟨⟨h1, h2⟩, h3⟩ := h; rw [ih _ _ h1, ih _ _ h2, ih _ _ h3])
      | (obtain ⟨⟨rfl, h1⟩, h2⟩ := h; rw [ih _ _ h1, ih _ _ h2])
      | (obtain ⟨rfl, h1, h2⟩ := h; rw [list_eq_of_all ih (by simpa using h1) h2])
      | (obtain ⟨h1, h2⟩ := h; rw [list_eq_of_all ih (by simpa using h1) h2])
      | (obtain ⟨rfl, h1⟩ := h; rw [ih _ _ h1])
      | (obtain ⟨rfl, rfl⟩ := h; rfl)
      | (obtain ⟨h1, h2⟩ := h; rw [ih _ _ h1, ih _ _ h2])
      | (rw [ih _ _ h])
      | (subst h; rfl)
      | (obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; rfl)
      | (obtain ⟨h1, h2⟩ := h; rw [paramsEq_eq h1, ih _ _ h2])
      | cases h

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
  | .Tuple es => some (18, es)
  | _ => none

/-- What the lowering inlines for the variable `x` of `e`: the expression at its first position
in `e'`, which `e` is lowered to, if `x` is found, `n` deep. It is only a candidate, which the
check checks. -/
def findVar (x : Id) : Nat → Expr → Expr → Option Expr
  | 0, _, _ => none
  | n + 1, e, e' =>
    let all (es es' : List Expr) : Option Expr :=
      (es.zip es').foldl (fun acc (a, a') => acc <|> findVar x n a a') none
    match e, e' with
    | .Variable y, e' => if y = x then some e' else none
    | .Let y a b, e' =>
      if y = x then none
      else findVar x n b e' <|> (findVar y n b e').bind fun a' => findVar x n a a'
    | .FunctionInvocation _ _ es, .FunctionInvocation _ _ es' => all es es'
    | .ADT _ _ es, .ADT _ _ es' => all es es'
    | .IsConstructor a _, .IsConstructor a' _ => findVar x n a a'
    | .ADTSelector a _, .ADTSelector a' _ => findVar x n a a'
    | .Plus a b, .Plus a' (.Plus b' (.IntegerLiteral 0)) => all [a, b] [a', b']
    | .Times a b, .Times a' (.Times b' (.IntegerLiteral 1)) => all [a, b] [a', b']
    | e, e' =>
      match kids e, kids e' with
      | some (i, es), some (j, es') => if i == j then all es es' else none
      | _, _ => none

mutual
/-- Whether `e` is lowered to `e'` with values of the kind `k`, in at most `n` steps of the
check. -/
def lowersCheck (S : LSig) : Nat → (Id → Option (Expr × LK)) → Expr → Expr → LK → Bool
  | 0, _, _, _, _ => false
  | n + 1, Γ, e, e', k =>
    match e, e' with
    | .Error, _ => true
    | .Variable x, e' =>
      match Γ x with
      | some (y, k0) => exprEq 1000 y e' && Sub k0 k
      | none => false
    | .Let x a b, e' =>
      match findVar x 1000 b e' with
      | some a' =>
        (lowersCheck S n Γ a a' .int && lowersCheck S n (bindCtx Γ x (some (a', .int))) b e' k) ||
        (lowersCheck S n Γ a a' .prim &&
          lowersCheck S n (bindCtx Γ x (some (a', .prim))) b e' k) ||
        (lowersCheck S n Γ a a' .any && lowersCheck S n (bindCtx Γ x (some (a', .any))) b e' k)
      | none => lowersCheck S n (bindCtx Γ x none) b e' k
    | .IntegerLiteral a, .IntegerLiteral b => a == b && Sub .int k
    | .BooleanLiteral a, .BooleanLiteral b => a == b && Sub .prim k
    | .FractionLiteral a b, .FractionLiteral c d => a == c && b == d && Sub .prim k
    | .BVLiteral s w x, .BVLiteral s' w' x' => s == s' && w == w' && x == x' && Sub .prim k
    | .BVLiteral s w x, .BVUnsignedToSigned (.BVLiteral s' w' x') =>
      s && !s' && w == w' && x == x' && Sub .prim k
    | .BVSignedToUnsigned a, e' => Sub .prim k && lowersCheck S n Γ a (.BVUnsignedToSigned e') .prim
    | .BVUnsignedToSigned a, .BVUnsignedToSigned a' => Sub .prim k && lowersCheck S n Γ a a' .any
    | .Plus a b, .Plus a' b' =>
      (Sub .int k && lowersCheck S n Γ a a' .int &&
        match b' with
        | .Plus b'' (.IntegerLiteral z) => z == 0 && lowersCheck S n Γ b b'' .int
        | _ => false) ||
      (Sub .int k && lowersCheck S n Γ a a' .int && lowersCheck S n Γ b b' .int) ||
      (Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any)
    | .Minus a b, .Minus a' b' =>
      (Sub .int k && lowersCheck S n Γ a a' .int && lowersCheck S n Γ b b' .int) ||
      (Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any)
    | .Times a b, .Times a' b' =>
      (Sub .int k && lowersCheck S n Γ a a' .int &&
        match b' with
        | .Times b'' (.IntegerLiteral z) => z == 1 && lowersCheck S n Γ b b'' .int
        | _ => false) ||
      (Sub .int k && lowersCheck S n Γ a a' .int && lowersCheck S n Γ b b' .int) ||
      (Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any)
    | .UMinus a, .UMinus a' =>
      (Sub .int k && lowersCheck S n Γ a a' .int) || (Sub .prim k && lowersCheck S n Γ a a' .any)
    | .Division a b, .Division a' b' =>
      (Sub .int k && lowersCheck S n Γ a a' .int && lowersCheck S n Γ b b' .int) ||
      (Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any)
    | .Remainder a b, .Remainder a' b' =>
      (Sub .int k && lowersCheck S n Γ a a' .int && lowersCheck S n Γ b b' .int) ||
      (Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any)
    | .Modulo a b, .Modulo a' b' =>
      (Sub .int k && lowersCheck S n Γ a a' .int && lowersCheck S n Γ b b' .int) ||
      (Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any)
    | .LessThan a b, .LessThan a' b' =>
      Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any
    | .GreaterThan a b, .GreaterThan a' b' =>
      Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any
    | .LessEquals a b, .LessEquals a' b' =>
      Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any
    | .GreaterEquals a b, .GreaterEquals a' b' =>
      Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any
    | .Equals a b, .Equals a' b' =>
      (Sub .prim k && lowersCheck S n Γ a a' .prim && lowersCheck S n Γ b b' .prim) ||
      (Sub .prim k && lowersCheck S n Γ a (.BVUnsignedToSigned a') .prim &&
        lowersCheck S n Γ b (.BVUnsignedToSigned b') .prim)
    | .Not a, .Not a' => Sub .prim k && lowersCheck S n Γ a a' .any
    | .Implies a b, .Implies a' b' =>
      Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any
    | .And es, .And es' => Sub .prim k && lowersAll S n Γ es es'
    | .Or es, .Or es' => Sub .prim k && lowersAll S n Γ es es'
    | .IfExpr c a b, .IfExpr c' a' b' =>
      lowersCheck S n Γ c c' .any && lowersCheck S n Γ a a' k && lowersCheck S n Γ b b' k
    | .Assume p a, .Assume p' a' => lowersCheck S n Γ p p' .any && lowersCheck S n Γ a a' k
    | .FunctionInvocation f _ es, .FunctionInvocation g _ es' =>
      match S.funs f with
      | some (g0, ks, k0) => g0 == g && Sub k0 k && lowersArgs S n Γ es es' ks
      | none => false
    | .ADT c _ es, .ADT c' _ es' =>
      match S.ctors c with
      | some c0 => c0 == c' &&
        ((match S.kinds c with
          | some (s, ks) => Sub (.data s) k && lowersArgs S n Γ es es' ks
          | none => false) ||
          (Sub .any k && lowersArgs S n Γ es es' (es.map fun _ => .any)))
      | none => false
    | .ADT c _ es, .Assume J (.ADT c' _ es') =>
      match S.ctors c, S.invs c with
      | some c0, some (p, fields, B) => c0 == c' &&
        (match instInv p fields es 1000 B with
          | some I => lowersCheck S n Γ I J .any
          | none => false) &&
        ((match S.kinds c with
          | some (s, ks) => Sub (.data s) k && lowersArgs S n Γ es es' ks
          | none => false) ||
          (Sub .any k && lowersArgs S n Γ es es' (es.map fun _ => .any)))
      | _, _ => false
    | .IsConstructor a c, .IsConstructor a' c' =>
      match S.ctors c with
      | some c0 => c0 == c' && Sub .prim k && lowersCheck S n Γ a a' .any
      | none => false
    | .ADTSelector a f, .ADTSelector a' f' =>
      match S.fields f with
      | some f0 => f0 == f' &&
        ((match S.fieldKinds f with
          | some (s, kf) => Sub kf k && lowersCheck S n Γ a a' (.data s)
          | none => false) ||
          (Sub .any k && lowersCheck S n Γ a a' .any))
      | none => false
    | _, _ => false

/-- Whether each of `es` is lowered to the expression of `es'` at its position, with any
values. -/
def lowersAll (S : LSig) : Nat → (Id → Option (Expr × LK)) → List Expr → List Expr → Bool
  | 0, _, _, _ => false
  | _ + 1, _, [], [] => true
  | n + 1, Γ, a :: es, a' :: es' => lowersCheck S n Γ a a' .any && lowersAll S n Γ es es'
  | _ + 1, _, _, _ => false

/-- Whether each of the arguments `es` is lowered to that of `es'` at its position, of the kind
of `ks` at its position. -/
def lowersArgs (S : LSig) :
    Nat → (Id → Option (Expr × LK)) → List Expr → List Expr → List LK → Bool
  | 0, _, _, _, _ => false
  | _ + 1, _, [], [], [] => true
  | n + 1, Γ, a :: es, a' :: es', k :: ks =>
    lowersCheck S n Γ a a' k && lowersArgs S n Γ es es' ks
  | _ + 1, _, _, _, _ => false
end

theorem lowers_sound (S : LSig) : ∀ n : Nat,
    (∀ Γ e e' k, lowersCheck S n Γ e e' k = true → Lowers S Γ e e' k) ∧
    (∀ Γ es es', lowersAll S n Γ es es' = true →
      Lowers S Γ (.And es) (.And es') .prim ∧ Lowers S Γ (.Or es) (.Or es') .prim) ∧
    (∀ Γ es es' ks, lowersArgs S n Γ es es' ks = true →
      Lowers S Γ (.Tuple es) (.Tuple es') (.tuple ks))
  | 0 => ⟨fun _ _ _ _ h => by simp [lowersCheck] at h, fun _ _ _ h => by simp [lowersAll] at h,
      fun _ _ _ _ h => by simp [lowersArgs] at h⟩
  | n + 1 => by
    obtain ⟨ih, iha, ihs⟩ := lowers_sound S n
    refine ⟨fun Γ e e' k h => ?_, fun Γ es es' h => ?_, fun Γ es es' ks h => ?_⟩
    · unfold lowersCheck at h
      split at h
      · exact .error _ _
      · split at h
        · next hx =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨he, hs⟩ := h
          rw [← exprEq_eq _ _ _ he]
          exact .weaken (.var hx) hs
        · cases h
      · split at h
        · simp only [Bool.or_eq_true, Bool.and_eq_true] at h
          rcases h with (⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨ha, hb⟩
          · exact .letIn (ih _ _ _ _ ha) (ih _ _ _ _ hb)
          · exact .letIn (ih _ _ _ _ ha) (ih _ _ _ _ hb)
          · exact .letIn (ih _ _ _ _ ha) (ih _ _ _ _ hb)
        · exact .letDrop (ih _ _ _ _ h)
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, hs⟩ := h
        exact .weaken (.int _) hs
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, hs⟩ := h
        exact .weaken (.bool _) hs
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨rfl, rfl⟩, hs⟩ := h
        exact .weaken (.frac _ _) hs
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hs⟩ := h
        exact .weaken (.bvLit _ _ _) hs
      · simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
        obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hs⟩ := h
        exact .weaken (.bvSignedLit _ _) hs
      · simp only [Bool.and_eq_true] at h
        obtain ⟨hs, ha⟩ := h
        exact .weaken (.toUnsigned (ih _ _ _ _ ha)) hs
      · simp only [Bool.and_eq_true] at h
        obtain ⟨hs, ha⟩ := h
        exact .weaken (.toSigned (ih _ _ _ _ ha)) hs
      · simp only [Bool.or_eq_true] at h
        rcases h with (h | h) | h
        · simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hs, ha⟩, hm⟩ := h
          split at hm
          · simp only [Bool.and_eq_true, beq_iff_eq] at hm
            obtain ⟨rfl, hb⟩ := hm
            exact .weaken (.plusZero (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
          · cases hm
        · simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hs, ha⟩, hb⟩ := h
          exact .weaken (.plusInt (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
        · simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hs, ha⟩, hb⟩ := h
          exact .weaken (.plus (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
      · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
        rcases h with ⟨⟨hs, ha⟩, hb⟩ | ⟨⟨hs, ha⟩, hb⟩
        · exact .weaken (.minusInt (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
        · exact .weaken (.minus (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
      · simp only [Bool.or_eq_true] at h
        rcases h with (h | h) | h
        · simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hs, ha⟩, hm⟩ := h
          split at hm
          · simp only [Bool.and_eq_true, beq_iff_eq] at hm
            obtain ⟨rfl, hb⟩ := hm
            exact .weaken (.timesOne (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
          · cases hm
        · simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hs, ha⟩, hb⟩ := h
          exact .weaken (.timesInt (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
        · simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hs, ha⟩, hb⟩ := h
          exact .weaken (.times (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
      · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
        rcases h with ⟨hs, ha⟩ | ⟨hs, ha⟩
        · exact .weaken (.uminusInt (ih _ _ _ _ ha)) hs
        · exact .weaken (.uminus (ih _ _ _ _ ha)) hs
      · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
        rcases h with ⟨⟨hs, ha⟩, hb⟩ | ⟨⟨hs, ha⟩, hb⟩
        · exact .weaken (.divInt (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
        · exact .weaken (.div (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
      · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
        rcases h with ⟨⟨hs, ha⟩, hb⟩ | ⟨⟨hs, ha⟩, hb⟩
        · exact .weaken (.remInt (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
        · exact .weaken (.rem (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
      · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
        rcases h with ⟨⟨hs, ha⟩, hb⟩ | ⟨⟨hs, ha⟩, hb⟩
        · exact .weaken (.modInt (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
        · exact .weaken (.mod (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
      · simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hs, ha⟩, hb⟩ := h
        exact .weaken (.lt (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
      · simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hs, ha⟩, hb⟩ := h
        exact .weaken (.gt (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
      · simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hs, ha⟩, hb⟩ := h
        exact .weaken (.le (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
      · simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hs, ha⟩, hb⟩ := h
        exact .weaken (.ge (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
      · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
        rcases h with ⟨⟨hs, ha⟩, hb⟩ | ⟨⟨hs, ha⟩, hb⟩
        · exact .weaken (.eq (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
        · exact .weaken (.eqSigned (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
      · simp only [Bool.and_eq_true] at h
        obtain ⟨hs, ha⟩ := h
        exact .weaken (.not (ih _ _ _ _ ha)) hs
      · simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hs, ha⟩, hb⟩ := h
        exact .weaken (.implies (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
      · simp only [Bool.and_eq_true] at h
        obtain ⟨hs, ha⟩ := h
        exact .weaken (iha _ _ _ ha).1 hs
      · simp only [Bool.and_eq_true] at h
        obtain ⟨hs, ha⟩ := h
        exact .weaken (iha _ _ _ ha).2 hs
      · simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hc, ha⟩, hb⟩ := h
        exact .ite (ih _ _ _ _ hc) (ih _ _ _ _ ha) (ih _ _ _ _ hb)
      · simp only [Bool.and_eq_true] at h
        obtain ⟨hp, ha⟩ := h
        exact .assume (ih _ _ _ _ hp) (ih _ _ _ _ ha)
      · split at h
        · next hf =>
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨⟨rfl, hs⟩, ha⟩ := h
          exact .weaken (.call hf (ihs _ _ _ _ ha)) hs
        · cases h
      · split at h
        · next hc =>
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
          obtain ⟨rfl, h | h⟩ := h
          · split at h
            · next s0 ks hk =>
              simp only [Bool.and_eq_true] at h
              obtain ⟨hs, ha⟩ := h
              exact .weaken (.adtData hc hk (ihs _ _ _ _ ha)) hs
            · cases h
          · obtain ⟨hs, ha⟩ := h
            exact .weaken (.adt hc (ihs _ _ _ _ ha)) hs
        · cases h
      · split at h
        · next c0 p fields B hc hv =>
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
          obtain ⟨⟨rfl, hI⟩, h⟩ := h
          split at hI
          · next I hI0 =>
            rcases h with h | ⟨hs, ha⟩
            · split at h
              · next s0 ks hk =>
                simp only [Bool.and_eq_true] at h
                obtain ⟨hs, ha⟩ := h
                exact .weaken (.adtInv hc hv hI0 (ih _ _ _ _ hI) (ihs _ _ _ _ ha)
                  (.inr ⟨s0, rfl, hk⟩)) hs
              · cases h
            · exact .weaken (.adtInv hc hv hI0 (ih _ _ _ _ hI) (ihs _ _ _ _ ha) (.inl rfl)) hs
          · cases hI
        · cases h
      · split at h
        · next hc =>
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨⟨rfl, hs⟩, ha⟩ := h
          exact .weaken (.isCtor hc (ih _ _ _ _ ha)) hs
        · cases h
      · split at h
        · next hf =>
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
          obtain ⟨rfl, h | h⟩ := h
          · split at h
            · next s0 kf hk =>
              simp only [Bool.and_eq_true] at h
              obtain ⟨hs, ha⟩ := h
              exact .weaken (.selData hf hk (ih _ _ _ _ ha)) hs
            · cases h
          · obtain ⟨hs, ha⟩ := h
            exact .weaken (.sel hf (ih _ _ _ _ ha)) hs
        · cases h
      · cases h
    · cases es with
      | nil =>
        cases es' with
        | nil => exact ⟨.andNil, .orNil⟩
        | cons _ _ => simp [lowersAll] at h
      | cons a es =>
        cases es' with
        | nil => simp [lowersAll] at h
        | cons a' es' =>
          simp only [lowersAll, Bool.and_eq_true] at h
          obtain ⟨ha, hr⟩ := h
          exact ⟨.andCons (ih _ _ _ _ ha) (iha _ _ _ hr).1,
            .orCons (ih _ _ _ _ ha) (iha _ _ _ hr).2⟩
    · cases es with
      | nil =>
        cases es' with
        | nil =>
          cases ks with
          | nil => exact .tupleNil
          | cons _ _ => simp [lowersArgs] at h
        | cons _ _ => simp [lowersArgs] at h
      | cons a es =>
        cases es' with
        | nil => simp [lowersArgs] at h
        | cons a' es' =>
          cases ks with
          | nil => simp [lowersArgs] at h
          | cons k ks =>
            simp only [lowersArgs, Bool.and_eq_true] at h
            obtain ⟨ha, hr⟩ := h
            exact .tupleCons (ih _ _ _ _ ha) (ihs _ _ _ _ hr)

end Inox.Lowered
