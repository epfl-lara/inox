/- Copyright 2009-2026 EPFL, Lausanne -/

-- Generated from semantics.md by inox.semantics.Codegen. Do not edit: change semantics.md
-- and regenerate (see proofs/README.md).

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Inox.Semantics

/-- The names of variables, functions, constructors, sorts and fields. -/
abbrev Id := String

inductive Result (T : Type) : Type where
  | Ok (value : T) : Result T
  | Stuck : Result T
  | OutOfFuel : Result T

inductive RoundingMode : Type where
  | RNE : RoundingMode
  | RNA : RoundingMode
  | RTP : RoundingMode
  | RTN : RoundingMode
  | RTZ : RoundingMode

mutual
inductive Ty : Type where
  | IntegerType : Ty
  | BooleanType : Ty
  | UnitType : Ty
  | CharType : Ty
  | RealType : Ty
  | StringType : Ty
  | BVType (signed : Bool) (width : Int) : Ty
  | FPType (exponent : Int) (significand : Int) : Ty
  | RoundingModeType : Ty
  | TypeParameter (id : Id) : Ty
  | TupleType (elems : List Ty) : Ty
  | SetType (elem : Ty) : Ty
  | BagType (elem : Ty) : Ty
  | MapType (from_ : Ty) (to : Ty) : Ty
  | FunctionType (from_ : List Ty) (to : Ty) : Ty
  | ADTType (sort : Id) (args : List Ty) : Ty
  | RefinementType (id : Id) (base : Ty) (prop : Expr) : Ty
  | PropType : Ty
  | PiType (params : List Param) (to : Ty) : Ty
  | SigmaType (params : List Param) (to : Ty) : Ty

inductive Param : Type where
  | Param (id : Id) (tpe : Ty) : Param

inductive Expr : Type where
  | Assume (pred : Expr) (body : Expr) : Expr
  | Variable (id : Id) : Expr
  | Let (id : Id) (value : Expr) (body : Expr) : Expr
  | Application (callee : Expr) (args : List Expr) : Expr
  | Lambda (params : List Param) (body : Expr) : Expr
  | Forall (params : List Param) (body : Expr) : Expr
  | UninterpretedCall (id : Id) (tps : List Ty) (args : List Expr) : Expr
  | Error : Expr
  | FunctionInvocation (id : Id) (tps : List Ty) (args : List Expr) : Expr
  | IfExpr (cond : Expr) (thenn : Expr) (elze : Expr) : Expr
  | CharLiteral (code : Int) : Expr
  | BVLiteral (signed : Bool) (width : Int) (bits : Int) : Expr
  | IntegerLiteral (value : Int) : Expr
  | FractionLiteral (num : Int) (den : Int) : Expr
  | FPLiteral (exponent : Int) (significand : Int) (bits : Int) : Expr
  | BooleanLiteral (value : Bool) : Expr
  | StringLiteral (chars : List Int) : Expr
  | UnitLiteral : Expr
  | RoundNearestTiesToEven : Expr
  | RoundNearestTiesToAway : Expr
  | RoundTowardPositive : Expr
  | RoundTowardNegative : Expr
  | RoundTowardZero : Expr
  | ADT (id : Id) (tps : List Ty) (args : List Expr) : Expr
  | IsConstructor (expr : Expr) (id : Id) : Expr
  | ADTSelector (adt : Expr) (selector : Id) : Expr
  | Equals (lhs : Expr) (rhs : Expr) : Expr
  | And (exprs : List Expr) : Expr
  | Or (exprs : List Expr) : Expr
  | Implies (lhs : Expr) (rhs : Expr) : Expr
  | Not (expr : Expr) : Expr
  | StringConcat (lhs : Expr) (rhs : Expr) : Expr
  | SubString (expr : Expr) (start : Expr) (end_ : Expr) : Expr
  | StringLength (expr : Expr) : Expr
  | Plus (lhs : Expr) (rhs : Expr) : Expr
  | Minus (lhs : Expr) (rhs : Expr) : Expr
  | UMinus (expr : Expr) : Expr
  | Times (lhs : Expr) (rhs : Expr) : Expr
  | Division (lhs : Expr) (rhs : Expr) : Expr
  | Remainder (lhs : Expr) (rhs : Expr) : Expr
  | Modulo (lhs : Expr) (rhs : Expr) : Expr
  | LessThan (lhs : Expr) (rhs : Expr) : Expr
  | GreaterThan (lhs : Expr) (rhs : Expr) : Expr
  | LessEquals (lhs : Expr) (rhs : Expr) : Expr
  | GreaterEquals (lhs : Expr) (rhs : Expr) : Expr
  | BVNot (expr : Expr) : Expr
  | BVAnd (lhs : Expr) (rhs : Expr) : Expr
  | BVOr (lhs : Expr) (rhs : Expr) : Expr
  | BVXor (lhs : Expr) (rhs : Expr) : Expr
  | BVShiftLeft (lhs : Expr) (rhs : Expr) : Expr
  | BVAShiftRight (lhs : Expr) (rhs : Expr) : Expr
  | BVLShiftRight (lhs : Expr) (rhs : Expr) : Expr
  | BVNarrowingCast (expr : Expr) (width : Int) : Expr
  | BVWideningCast (expr : Expr) (width : Int) : Expr
  | BVUnsignedToSigned (expr : Expr) : Expr
  | BVSignedToUnsigned (expr : Expr) : Expr
  | BVToInt (expr : Expr) : Expr
  | IntToBV (width : Int) (signed : Bool) (expr : Expr) : Expr
  | FPEquals (lhs : Expr) (rhs : Expr) : Expr
  | FPAdd (rm : Expr) (lhs : Expr) (rhs : Expr) : Expr
  | FPSub (rm : Expr) (lhs : Expr) (rhs : Expr) : Expr
  | FPUMinus (expr : Expr) : Expr
  | FPFMA (rm : Expr) (e1 : Expr) (e2 : Expr) (e3 : Expr) : Expr
  | FPMul (rm : Expr) (lhs : Expr) (rhs : Expr) : Expr
  | FPDiv (rm : Expr) (lhs : Expr) (rhs : Expr) : Expr
  | FPAbs (expr : Expr) : Expr
  | FPMax (lhs : Expr) (rhs : Expr) : Expr
  | FPMin (lhs : Expr) (rhs : Expr) : Expr
  | FPRound (rm : Expr) (expr : Expr) : Expr
  | Sqrt (rm : Expr) (expr : Expr) : Expr
  | FPCast (exponent : Int) (significand : Int) (rm : Expr) (expr : Expr) : Expr
  | FPFromBinary (exponent : Int) (significand : Int) (expr : Expr) : Expr
  | FPToBV (width : Int) (signed : Bool) (rm : Expr) (expr : Expr) : Expr
  | FPToReal (expr : Expr) : Expr
  | FPLessThan (lhs : Expr) (rhs : Expr) : Expr
  | FPGreaterThan (lhs : Expr) (rhs : Expr) : Expr
  | FPLessEquals (lhs : Expr) (rhs : Expr) : Expr
  | FPGreaterEquals (lhs : Expr) (rhs : Expr) : Expr
  | FPIsZero (expr : Expr) : Expr
  | FPIsInfinite (expr : Expr) : Expr
  | FPIsNaN (expr : Expr) : Expr
  | FPIsNegative (expr : Expr) : Expr
  | FPIsPositive (expr : Expr) : Expr
  | FPIsNormal (expr : Expr) : Expr
  | FPIsSubnormal (expr : Expr) : Expr
  | Tuple (exprs : List Expr) : Expr
  | TupleSelect (tuple : Expr) (index : Int) : Expr
  | FiniteSet (elems : List Expr) (base : Ty) : Expr
  | SetAdd (set : Expr) (elem : Expr) : Expr
  | ElementOfSet (elem : Expr) (set : Expr) : Expr
  | SubsetOf (lhs : Expr) (rhs : Expr) : Expr
  | SetIntersection (lhs : Expr) (rhs : Expr) : Expr
  | SetUnion (lhs : Expr) (rhs : Expr) : Expr
  | SetDifference (lhs : Expr) (rhs : Expr) : Expr
  | FiniteBag (elems : List ExprPair) (base : Ty) : Expr
  | BagAdd (bag : Expr) (elem : Expr) : Expr
  | MultiplicityInBag (elem : Expr) (bag : Expr) : Expr
  | BagIntersection (lhs : Expr) (rhs : Expr) : Expr
  | BagUnion (lhs : Expr) (rhs : Expr) : Expr
  | BagDifference (lhs : Expr) (rhs : Expr) : Expr
  | FiniteMap (pairs : List ExprPair) (default : Expr) (keys : Ty) (values : Ty) : Expr
  | MapApply (map : Expr) (key : Expr) : Expr
  | MapUpdated (map : Expr) (key : Expr) (value : Expr) : Expr
  | MapMerge (mask : Expr) (map1 : Expr) (map2 : Expr) : Expr

inductive ExprPair : Type where
  | ExprPair (fst : Expr) (snd : Expr) : ExprPair
end

inductive TypeBinding : Type where
  | TypeBinding (id : Id) (tpe : Ty) (env : List TypeBinding) : TypeBinding

mutual
inductive Value : Type where
  | IntV (value : Int) : Value
  | BoolV (value : Bool) : Value
  | UnitV : Value
  | CharV (code : Int) : Value
  | RealV (num : Int) (den : Int) : Value
  | StringV (chars : List Int) : Value
  | BVV (signed : Bool) (width : Int) (bits : Int) : Value
  | FPV (exponent : Int) (significand : Int) (bits : Int) : Value
  | RoundingModeV (mode : RoundingMode) : Value
  | TupleV (elems : List Value) : Value
  | ClosureV (params : List Param) (body : Expr) (env : Env) : Value
  | SetV (base : Ty) (elems : List Value) : Value
  | BagV (base : Ty) (entries : List BagEntry) : Value
  | MapV (keys : Ty) (values : Ty) (entries : List MapEntry) (default : Value) : Value
  | ADTV (ctor : Id) (tps : List Ty) (args : List Value) : Value

inductive BagEntry : Type where
  | BagEntry (elem : Value) (count : Int) : BagEntry

inductive MapEntry : Type where
  | MapEntry (key : Value) (value : Value) : MapEntry

inductive Binding : Type where
  | Binding (id : Id) (value : Value) : Binding

inductive Env : Type where
  | Env (types : List TypeBinding) (vars : List Binding) : Env
end

inductive FunDef : Type where
  | FunDef (id : Id) (tparams : List Id) (params : List Id) (body : Expr) : FunDef

inductive Constructor : Type where
  | Constructor (id : Id) (sort : Id) (fields : List Param) : Constructor

inductive ADTSort : Type where
  | Sort (id : Id) (tparams : List Id) (invariant : Option Id) (equality : Option Id) : ADTSort

inductive Interpretation : Type where
  | Interpretation (id : Id) (tps : List Ty) (params : List Id) (body : Expr) : Interpretation

inductive FunctionEquality : Type where
  | NoFunctionEquality : FunctionEquality
  | ExtensionalEquality : FunctionEquality

inductive Program : Type where
  | Program (functions : List FunDef) (constructors : List Constructor) (sorts : List ADTSort) (interpretations : List Interpretation) (equality : FunctionEquality) : Program

inductive BitOp : Type where
  | AndOp : BitOp
  | OrOp : BitOp
  | XorOp : BitOp
  | ShiftLeftOp : BitOp
  | AShiftRightOp : BitOp
  | LShiftRightOp : BitOp

inductive Rat : Type where
  | Rat (num : Int) (den : Int) : Rat

inductive FPOp : Type where
  | FPAddOp : FPOp
  | FPSubOp : FPOp
  | FPMulOp : FPOp
  | FPDivOp : FPOp
  | FPMinOp : FPOp
  | FPMaxOp : FPOp

inductive FPRel : Type where
  | FPEqRel : FPRel
  | FPLtRel : FPRel
  | FPLeRel : FPRel

inductive FPClass : Type where
  | ZeroClass : FPClass
  | InfiniteClass : FPClass
  | NaNClass : FPClass
  | NegativeClass : FPClass
  | PositiveClass : FPClass
  | NormalClass : FPClass
  | SubnormalClass : FPClass

inductive BagOp : Type where
  | IntersectionOp : BagOp
  | UnionOp : BagOp
  | DifferenceOp : BagOp

noncomputable section

open Classical

/-- The functions of the semantics that quantify over values and are defined in terms of
themselves, through the evaluation of the functions that values hold. Such a definition is no
recursion that Lean accepts, so the semantics is relative to an oracle that gives them, and
`Oracle.Sound` states that the oracle gives them as the semantics defines them. -/
structure Oracle : Type where
  value_eq : Program → Value → Value → (Result Bool)
  adt_equal : Program → Id → (List Ty) → Value → Value → (Result Bool)
  values_eq : Program → (List Value) → (List Value) → (Result Bool)
  set_contains : Program → (List Value) → Value → (Result Bool)
  subset : Program → (List Value) → (List Value) → (Result Bool)
  bag_get : Program → (List BagEntry) → Value → (Result Int)
  sub_bag : Program → (List BagEntry) → (List BagEntry) → (Result Bool)
  map_get : Program → (List MapEntry) → Value → Value → (Result Value)
  same_entries : Program → (List MapEntry) → (List MapEntry) → Value → (List MapEntry) → Value → (Result Bool)
  resolve : (List TypeBinding) → Ty → Ty
  resolve_params : (List TypeBinding) → (List Param) → (List Param)
  resolve_all : (List TypeBinding) → (List Ty) → (List Ty)
  has_type : Program → Env → Value → Ty → Bool
  holds : Program → Env → Expr → Bool
  invariant_holds : Program → Id → (List Ty) → (List TypeBinding) → Value → Bool
  function_has_type : Program → Env → Value → (List Ty) → Ty → Bool
  pi_has_type : Program → Env → Value → (List Param) → Ty → Bool
  sigma_has_type : Program → Env → (List Value) → (List Param) → Ty → Bool
  have_types : Program → Env → (List Value) → (List Ty) → Bool
  params_have_types : Program → Env → (List Value) → (List Param) → Bool
  all_have_type : Program → Env → (List Value) → Ty → Bool
  bag_has_type : Program → Env → (List BagEntry) → Ty → Bool
  map_has_type : Program → Env → (List MapEntry) → Ty → Ty → Bool
  forall_result : Program → Int → Env → (List Param) → Expr → (Result Value)
  closures_equal : Program → Value → Value → Bool

def lookup_var (vars : List Binding) (x : Id) : Result Value :=
  (match vars with
  | List.nil =>
    Result.Stuck
  | (List.cons (Binding.Binding y v) rest) =>
    (if _h : x = y then
      (Result.Ok v)
    else
      (lookup_var rest x)))

def lookup_type (types : List TypeBinding) (x : Id) : Option TypeBinding :=
  (match types with
  | List.nil =>
    Option.none
  | (List.cons b rest) =>
    (match b with
    | (TypeBinding.TypeBinding y _ _) =>
      (if _h : x = y then
        (Option.some b)
      else
        (lookup_type rest x))))

def bind_types (ids : List Id) (tps : List Ty) (env : List TypeBinding) : List TypeBinding :=
  (match ids with
  | List.nil =>
    List.nil
  | (List.cons x xs) =>
    (match tps with
    | List.nil =>
      List.nil
    | (List.cons t ts) =>
      (List.cons (TypeBinding.TypeBinding x t env) (bind_types xs ts env))))

def env_types (env : Env) : List TypeBinding :=
  (match env with
  | (Env.Env tys _) =>
    tys)

def env_vars (env : Env) : List Binding :=
  (match env with
  | (Env.Env _ vars) =>
    vars)

def env_bind (env : Env) (x : Id) (v : Value) : Env :=
  (match env with
  | (Env.Env tys vars) =>
    (Env.Env tys (List.cons (Binding.Binding x v) vars)))

def param_ids (ps : List Param) : List Id :=
  (match ps with
  | List.nil =>
    List.nil
  | (List.cons (Param.Param x _) rest) =>
    (List.cons x (param_ids rest)))

def bind_all (ids : List Id) (vs : List Value) : Result (List Binding) :=
  (match ids with
  | List.nil =>
    (match vs with
    | List.nil =>
      (Result.Ok List.nil)
    | _ =>
      Result.Stuck)
  | (List.cons x xs) =>
    (match vs with
    | List.nil =>
      Result.Stuck
    | (List.cons v rest) =>
      (match (bind_all xs rest) with
      | Result.Ok bs =>
        (Result.Ok (List.cons (Binding.Binding x v) bs))
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)))

def lookup_fun (fs : List FunDef) (f : Id) : Result FunDef :=
  (match fs with
  | List.nil =>
    Result.Stuck
  | (List.cons fd rest) =>
    (match fd with
    | (FunDef.FunDef g _ _ _) =>
      (if _h : f = g then
        (Result.Ok fd)
      else
        (lookup_fun rest f))))

def lookup_ctor (cs : List Constructor) (c : Id) : Result Constructor :=
  (match cs with
  | List.nil =>
    Result.Stuck
  | (List.cons k rest) =>
    (match k with
    | (Constructor.Constructor d _ _) =>
      (if _h : c = d then
        (Result.Ok k)
      else
        (lookup_ctor rest c))))

def lookup_sort (ss : List ADTSort) (s : Id) : Result ADTSort :=
  (match ss with
  | List.nil =>
    Result.Stuck
  | (List.cons srt rest) =>
    (match srt with
    | (ADTSort.Sort t _ _ _) =>
      (if _h : s = t then
        (Result.Ok srt)
      else
        (lookup_sort rest s))))

def select_field (fields : List Param) (args : List Value) (sel : Id) : Result Value :=
  (match fields with
  | List.nil =>
    Result.Stuck
  | (List.cons (Param.Param f _) fs) =>
    (match args with
    | List.nil =>
      Result.Stuck
    | (List.cons v vs) =>
      (if _h : f = sel then
        (Result.Ok v)
      else
        (select_field fs vs sel))))

def append_env (bs : List Binding) (env : List Binding) : List Binding :=
  (match bs with
  | List.nil =>
    env
  | (List.cons b rest) =>
    (List.cons b (append_env rest env)))

def lookup_interpretation (is : List Interpretation) (f : Id) (tps : List Ty) : Result Interpretation :=
  (match is with
  | List.nil =>
    Result.Stuck
  | (List.cons i rest) =>
    (match i with
    | (Interpretation.Interpretation g us _ _) =>
      (if _h : (f = g) ∧ (tps = us) then
        (Result.Ok i)
      else
        (lookup_interpretation rest f tps))))

def gcd (a : Int) (b : Int) : Int :=
  (if _h : b = (0 : Int) then
    a
  else
    (gcd b (a % b)))
termination_by b.natAbs
decreasing_by
  have := Int.emod_nonneg a _h
  have := Int.emod_lt a _h
  omega

def abs (a : Int) : Int :=
  (if _h : a < (0 : Int) then
    ((0 : Int) - a)
  else
    a)

def real (n : Int) (d : Int) : Result Value :=
  (if _h : d = (0 : Int) then
    Result.Stuck
  else
    (let g := (gcd (abs n) (abs d))
    (let s := (if _h : d < (0 : Int) then
        ((0 : Int) - (1 : Int))
      else
        (1 : Int))
    (Result.Ok (Value.RealV (s * (n / g)) (s * (d / g)))))))

def pow2 (n : Int) : Int :=
  (if _h : n ≤ (0 : Int) then
    (1 : Int)
  else
    ((2 : Int) * (pow2 (n - (1 : Int)))))
termination_by n.toNat
decreasing_by omega

def fp_exp (e : Int) (s : Int) (x : Int) : Int :=
  ((x / (pow2 (s - (1 : Int)))) % (pow2 e))

def fp_max_exp (e : Int) : Int :=
  ((pow2 e) - (1 : Int))

def fp_frac (s : Int) (x : Int) : Int :=
  (x % (pow2 (s - (1 : Int))))

def fp_nan (e : Int) (s : Int) (x : Int) : Bool :=
  ((decide ((fp_exp e s x) = (fp_max_exp e))) && (!(decide ((fp_frac s x) = (0 : Int)))))

def fp_bits (e : Int) (s : Int) (neg : Bool) (be : Int) (f : Int) : Int :=
  ((if _h : neg = true then
    (pow2 ((e + s) - (1 : Int)))
  else
    (0 : Int)) + ((be * (pow2 (s - (1 : Int)))) + f))

def fp_nan_bits (e : Int) (s : Int) : Int :=
  (fp_bits e s false (fp_max_exp e) (pow2 (s - (2 : Int))))

def fp_canonical (e : Int) (s : Int) (x : Int) : Int :=
  (if _h : (fp_nan e s x) = true then
    (fp_nan_bits e s)
  else
    x)

def append_chars (xs : List Int) (ys : List Int) : List Int :=
  (match xs with
  | List.nil =>
    ys
  | (List.cons x rest) =>
    (List.cons x (append_chars rest ys)))

def take (n : Int) (xs : List Int) : List Int :=
  (if _h : n ≤ (0 : Int) then
    List.nil
  else
    (match xs with
    | List.nil =>
      List.nil
    | (List.cons x rest) =>
      (List.cons x (take (n - (1 : Int)) rest))))

def drop (n : Int) (xs : List Int) : List Int :=
  (if _h : n ≤ (0 : Int) then
    xs
  else
    (match xs with
    | List.nil =>
      List.nil
    | (List.cons _ rest) =>
      (drop (n - (1 : Int)) rest)))

def length (xs : List Int) : Int :=
  (match xs with
  | List.nil =>
    (0 : Int)
  | (List.cons _ rest) =>
    ((1 : Int) + (length rest)))

def same_bv (s : Bool) (w : Int) (t : Bool) (v : Int) : Bool :=
  ((decide (s = t)) && (decide (w = v)))

def bv (s : Bool) (w : Int) (x : Int) : Value :=
  (Value.BVV s w (x % (pow2 w)))

def arith_plus (a : Value) (b : Value) : Result Value :=
  (match a with
  | (Value.IntV x) =>
    (match b with
    | (Value.IntV y) =>
      (Result.Ok (Value.IntV (x + y)))
    | _ =>
      Result.Stuck)
  | (Value.RealV n d) =>
    (match b with
    | (Value.RealV m e) =>
      (real ((n * e) + (m * d)) (d * e))
    | _ =>
      Result.Stuck)
  | (Value.BVV s w x) =>
    (match b with
    | (Value.BVV t v y) =>
      (if _h : (same_bv s w t v) = true then
        (Result.Ok (bv s w (x + y)))
      else
        Result.Stuck)
    | _ =>
      Result.Stuck)
  | _ =>
    Result.Stuck)

def arith_minus (a : Value) (b : Value) : Result Value :=
  (match a with
  | (Value.IntV x) =>
    (match b with
    | (Value.IntV y) =>
      (Result.Ok (Value.IntV (x - y)))
    | _ =>
      Result.Stuck)
  | (Value.RealV n d) =>
    (match b with
    | (Value.RealV m e) =>
      (real ((n * e) - (m * d)) (d * e))
    | _ =>
      Result.Stuck)
  | (Value.BVV s w x) =>
    (match b with
    | (Value.BVV t v y) =>
      (if _h : (same_bv s w t v) = true then
        (Result.Ok (bv s w (x - y)))
      else
        Result.Stuck)
    | _ =>
      Result.Stuck)
  | _ =>
    Result.Stuck)

def arith_neg (a : Value) : Result Value :=
  (match a with
  | (Value.IntV x) =>
    (Result.Ok (Value.IntV ((0 : Int) - x)))
  | (Value.RealV n d) =>
    (Result.Ok (Value.RealV ((0 : Int) - n) d))
  | (Value.BVV s w x) =>
    (Result.Ok (bv s w ((0 : Int) - x)))
  | _ =>
    Result.Stuck)

def arith_times (a : Value) (b : Value) : Result Value :=
  (match a with
  | (Value.IntV x) =>
    (match b with
    | (Value.IntV y) =>
      (Result.Ok (Value.IntV (x * y)))
    | _ =>
      Result.Stuck)
  | (Value.RealV n d) =>
    (match b with
    | (Value.RealV m e) =>
      (real (n * m) (d * e))
    | _ =>
      Result.Stuck)
  | (Value.BVV s w x) =>
    (match b with
    | (Value.BVV t v y) =>
      (if _h : (same_bv s w t v) = true then
        (Result.Ok (bv s w (x * y)))
      else
        Result.Stuck)
    | _ =>
      Result.Stuck)
  | _ =>
    Result.Stuck)

def twos (w : Int) (x : Int) : Int :=
  (if _h : (pow2 (w - (1 : Int))) ≤ x then
    (x - (pow2 w))
  else
    x)

def bv_int (s : Bool) (w : Int) (x : Int) : Int :=
  (if _h : s = true then
    (twos w x)
  else
    x)

def tdiv (a : Int) (b : Int) : Int :=
  (if _h : (0 : Int) ≤ a then
    (a / b)
  else
    ((0 : Int) - (((0 : Int) - a) / b)))

def arith_div (a : Value) (b : Value) : Result Value :=
  (match a with
  | (Value.IntV x) =>
    (match b with
    | (Value.IntV y) =>
      (if _h : y = (0 : Int) then
        Result.Stuck
      else
        (Result.Ok (Value.IntV (x / y))))
    | _ =>
      Result.Stuck)
  | (Value.RealV n d) =>
    (match b with
    | (Value.RealV m e) =>
      (if _h : m = (0 : Int) then
        Result.Stuck
      else
        (real (n * e) (d * m)))
    | _ =>
      Result.Stuck)
  | (Value.BVV s w x) =>
    (match b with
    | (Value.BVV t v y) =>
      (if _h : (same_bv s w t v) = true then
        (let i := (bv_int s w x)
        (let j := (bv_int s w y)
        (if _h : j = (0 : Int) then
          (if _h : s = true then
            (Result.Ok (bv s w (if _h : (0 : Int) ≤ i then
              ((0 : Int) - (1 : Int))
            else
              (1 : Int))))
          else
            (Result.Ok (bv s w ((pow2 w) - (1 : Int)))))
        else
          (Result.Ok (bv s w (tdiv i j))))))
      else
        Result.Stuck)
    | _ =>
      Result.Stuck)
  | _ =>
    Result.Stuck)

def trem (a : Int) (b : Int) : Int :=
  (a - (b * (tdiv a b)))

def arith_rem (a : Value) (b : Value) : Result Value :=
  (match a with
  | (Value.IntV x) =>
    (match b with
    | (Value.IntV y) =>
      (if _h : y = (0 : Int) then
        Result.Stuck
      else
        (Result.Ok (Value.IntV (x % y))))
    | _ =>
      Result.Stuck)
  | (Value.BVV s w x) =>
    (match b with
    | (Value.BVV t v y) =>
      (if _h : (same_bv s w t v) = true then
        (let i := (bv_int s w x)
        (let j := (bv_int s w y)
        (if _h : j = (0 : Int) then
          (Result.Ok a)
        else
          (Result.Ok (bv s w (trem i j))))))
      else
        Result.Stuck)
    | _ =>
      Result.Stuck)
  | _ =>
    Result.Stuck)

def arith_mod (a : Value) (b : Value) : Result Value :=
  (match a with
  | (Value.IntV x) =>
    (match b with
    | (Value.IntV y) =>
      (if _h : y = (0 : Int) then
        Result.Stuck
      else
        (Result.Ok (Value.IntV (x % y))))
    | _ =>
      Result.Stuck)
  | (Value.BVV s w x) =>
    (match b with
    | (Value.BVV t v y) =>
      (if _h : (same_bv s w t v) = true then
        (let i := (bv_int s w x)
        (let j := (bv_int s w y)
        (if _h : j = (0 : Int) then
          (Result.Ok a)
        else
          (let r := (i % j)
          (Result.Ok (bv s w (if _h : (j < (0 : Int)) ∧ (¬ (r = (0 : Int))) then
            (r + j)
          else
            r)))))))
      else
        Result.Stuck)
    | _ =>
      Result.Stuck)
  | _ =>
    Result.Stuck)

def arith_lt (a : Value) (b : Value) : Result Bool :=
  (match a with
  | (Value.IntV x) =>
    (match b with
    | (Value.IntV y) =>
      (Result.Ok (decide (x < y)))
    | _ =>
      Result.Stuck)
  | (Value.RealV n d) =>
    (match b with
    | (Value.RealV m e) =>
      (Result.Ok (decide ((n * e) < (m * d))))
    | _ =>
      Result.Stuck)
  | (Value.CharV x) =>
    (match b with
    | (Value.CharV y) =>
      (Result.Ok (decide (x < y)))
    | _ =>
      Result.Stuck)
  | (Value.BVV s w x) =>
    (match b with
    | (Value.BVV t v y) =>
      (if _h : (same_bv s w t v) = true then
        (Result.Ok (decide ((bv_int s w x) < (bv_int s w y))))
      else
        Result.Stuck)
    | _ =>
      Result.Stuck)
  | _ =>
    Result.Stuck)

def arith_le (a : Value) (b : Value) : Result Bool :=
  (match (arith_lt b a) with
  | Result.Ok lt =>
    (Result.Ok (!lt))
  | Result.Stuck => Result.Stuck
  | Result.OutOfFuel => Result.OutOfFuel)

def shift_amount (w : Int) (y : Int) : Int :=
  (if _h : w ≤ y then
    w
  else
    y)

def bit (a : Int) : Int :=
  (a % (2 : Int))

def bit_and (a : Int) (b : Int) : Int :=
  (if _h : (a ≤ (0 : Int)) ∨ (b ≤ (0 : Int)) then
    (0 : Int)
  else
    (((2 : Int) * (bit_and (a / (2 : Int)) (b / (2 : Int)))) + ((bit a) * (bit b))))
termination_by a.toNat
decreasing_by omega

def bit_or (a : Int) (b : Int) : Int :=
  (if _h : a ≤ (0 : Int) then
    b
  else
    (if _h : b ≤ (0 : Int) then
      a
    else
      (((2 : Int) * (bit_or (a / (2 : Int)) (b / (2 : Int)))) + (((bit a) + (bit b)) - ((bit a) * (bit b))))))
termination_by a.toNat
decreasing_by omega

def bit_xor (a : Int) (b : Int) : Int :=
  (if _h : a ≤ (0 : Int) then
    b
  else
    (if _h : b ≤ (0 : Int) then
      a
    else
      (((2 : Int) * (bit_xor (a / (2 : Int)) (b / (2 : Int)))) + (((bit a) + (bit b)) % (2 : Int)))))
termination_by a.toNat
decreasing_by omega

def bit_op (op : BitOp) (s : Bool) (w : Int) (x : Int) (y : Int) : Value :=
  (let k := (pow2 (shift_amount w y))
  (match op with
  | BitOp.AndOp =>
    (Value.BVV s w (bit_and x y))
  | BitOp.OrOp =>
    (Value.BVV s w (bit_or x y))
  | BitOp.XorOp =>
    (Value.BVV s w (bit_xor x y))
  | BitOp.ShiftLeftOp =>
    (bv s w (x * k))
  | BitOp.AShiftRightOp =>
    (bv s w ((twos w x) / k))
  | BitOp.LShiftRightOp =>
    (Value.BVV s w (x / k))))

def bv_binary (op : BitOp) (a : Value) (b : Value) : Result Value :=
  (match a with
  | (Value.BVV s w x) =>
    (match b with
    | (Value.BVV t v y) =>
      (if _h : (same_bv s w t v) = true then
        (Result.Ok (bit_op op s w x y))
      else
        Result.Stuck)
    | _ =>
      Result.Stuck)
  | _ =>
    Result.Stuck)

def bv_cast (a : Value) (v : Int) : Result Value :=
  (match a with
  | (Value.BVV s w x) =>
    (Result.Ok (bv s v (bv_int s w x)))
  | _ =>
    Result.Stuck)

def fp_inf (e : Int) (s : Int) (x : Int) : Bool :=
  ((decide ((fp_exp e s x) = (fp_max_exp e))) && (decide ((fp_frac s x) = (0 : Int))))

def fp_sign (e : Int) (s : Int) (x : Int) : Bool :=
  (decide ((pow2 ((e + s) - (1 : Int))) ≤ x))

def rat_cmp (a : Rat) (b : Rat) : Int :=
  (match a with
  | (Rat.Rat n d) =>
    (match b with
    | (Rat.Rat m k) =>
      (if _h : (n * k) < (m * d) then
        ((0 : Int) - (1 : Int))
      else
        (if _h : (n * k) = (m * d) then
          (0 : Int)
        else
          (1 : Int)))))

def fp_bias (e : Int) : Int :=
  ((pow2 (e - (1 : Int))) - (1 : Int))

def fp_rat (e : Int) (s : Int) (x : Int) : Rat :=
  (let be := (fp_exp e s x)
  (let f := (fp_frac s x)
  (let m := (if _h : be = (0 : Int) then
      f
    else
      (f + (pow2 (s - (1 : Int)))))
  (let k := (((if _h : be = (0 : Int) then
      (1 : Int)
    else
      be) - (fp_bias e)) - (s - (1 : Int)))
  (let sg := (if _h : (fp_sign e s x) = true then
      ((0 : Int) - (1 : Int))
    else
      (1 : Int))
  (if _h : k < (0 : Int) then
    (Rat.Rat (sg * m) (pow2 ((0 : Int) - k)))
  else
    (Rat.Rat (sg * (m * (pow2 k))) (1 : Int))))))))

def fp_cmp (e : Int) (s : Int) (x : Int) (y : Int) : Int :=
  (if _h : (fp_inf e s x) = true then
    (if _h : ((fp_inf e s y) = true) ∧ ((fp_sign e s x) = (fp_sign e s y)) then
      (0 : Int)
    else
      (if _h : (fp_sign e s x) = true then
        ((0 : Int) - (1 : Int))
      else
        (1 : Int)))
  else
    (if _h : (fp_inf e s y) = true then
      (if _h : (fp_sign e s y) = true then
        (1 : Int)
      else
        ((0 : Int) - (1 : Int)))
    else
      (rat_cmp (fp_rat e s x) (fp_rat e s y))))

def fp_rel (rel : FPRel) (a : Value) (b : Value) : Result Value :=
  (match a with
  | (Value.FPV e s x) =>
    (match b with
    | (Value.FPV e2 s2 y) =>
      (if _h : (e = e2) ∧ (s = s2) then
        (if _h : ((fp_nan e s x) = true) ∨ ((fp_nan e s y) = true) then
          (Result.Ok (Value.BoolV false))
        else
          (let c := (fp_cmp e s x y)
          (match rel with
          | FPRel.FPEqRel =>
            (Result.Ok (Value.BoolV (decide (c = (0 : Int)))))
          | FPRel.FPLtRel =>
            (Result.Ok (Value.BoolV (decide (c < (0 : Int)))))
          | FPRel.FPLeRel =>
            (Result.Ok (Value.BoolV (decide (c ≤ (0 : Int))))))))
      else
        Result.Stuck)
    | _ =>
      Result.Stuck)
  | _ =>
    Result.Stuck)

def rat_add (a : Rat) (b : Rat) : Rat :=
  (match a with
  | (Rat.Rat n d) =>
    (match b with
    | (Rat.Rat m k) =>
      (Rat.Rat ((n * k) + (m * d)) (d * k))))

def rat_num (a : Rat) : Int :=
  (match a with
  | (Rat.Rat n _) =>
    n)

def fp_zero (e : Int) (s : Int) (x : Int) : Bool :=
  ((decide ((fp_exp e s x) = (0 : Int))) && (decide ((fp_frac s x) = (0 : Int))))

def fp_zero_bits (e : Int) (s : Int) (neg : Bool) : Int :=
  (fp_bits e s neg (0 : Int) (0 : Int))

def is_rtn (rm : RoundingMode) : Bool :=
  (match rm with
  | RoundingMode.RTN =>
    true
  | _ =>
    false)

def bitlen (n : Int) : Int :=
  (if _h : n ≤ (0 : Int) then
    (0 : Int)
  else
    ((1 : Int) + (bitlen (n / (2 : Int)))))
termination_by n.toNat
decreasing_by omega

def rat_ilog2 (a : Rat) : Int :=
  (match a with
  | (Rat.Rat n d) =>
    (let k := ((bitlen n) - (bitlen d))
    (if _h : k < (0 : Int) then
      (if _h : (n * (pow2 ((0 : Int) - k))) < d then
        (k - (1 : Int))
      else
        k)
    else
      (if _h : n < (d * (pow2 k)) then
        (k - (1 : Int))
      else
        k))))

def scaled (n : Int) (d : Int) (p : Int) : Rat :=
  (if _h : p < (0 : Int) then
    (Rat.Rat n (d * (pow2 ((0 : Int) - p))))
  else
    (Rat.Rat (n * (pow2 p)) d))

def fp_inf_bits (e : Int) (s : Int) (neg : Bool) : Int :=
  (fp_bits e s neg (fp_max_exp e) (0 : Int))

def fp_overflow (rm : RoundingMode) (e : Int) (s : Int) (neg : Bool) : Int :=
  (if _h : (match rm with
    | RoundingMode.RNE =>
      true
    | RoundingMode.RNA =>
      true
    | RoundingMode.RTP =>
      (!neg)
    | RoundingMode.RTN =>
      neg
    | RoundingMode.RTZ =>
      false) = true then
    (fp_inf_bits e s neg)
  else
    (fp_bits e s neg ((fp_max_exp e) - (1 : Int)) ((pow2 (s - (1 : Int))) - (1 : Int))))

def fp_pack (rm : RoundingMode) (e : Int) (s : Int) (neg : Bool) (qe : Int) (m : Int) : Int :=
  (let carry := (decide (m = (pow2 s)))
  (let m2 := (if _h : carry = true then
      (pow2 (s - (1 : Int)))
    else
      m)
  (let qe2 := (if _h : carry = true then
      (qe + (1 : Int))
    else
      qe)
  (if _h : m2 = (0 : Int) then
    (fp_zero_bits e s neg)
  else
    (if _h : m2 < (pow2 (s - (1 : Int))) then
      (fp_bits e s neg (0 : Int) m2)
    else
      (let be := ((qe2 + (s - (1 : Int))) + (fp_bias e))
      (if _h : (fp_max_exp e) ≤ be then
        (fp_overflow rm e s neg)
      else
        (fp_bits e s neg be (m2 - (pow2 (s - (1 : Int))))))))))))

def round_up (rm : RoundingMode) (neg : Bool) (i : Int) (c : Int) (inexact : Bool) : Bool :=
  (if _h : ¬ (inexact = true) then
    false
  else
    (match rm with
    | RoundingMode.RNE =>
      ((decide ((0 : Int) < c)) || ((decide (c = (0 : Int))) && (decide ((i % (2 : Int)) = (1 : Int)))))
    | RoundingMode.RNA =>
      (decide ((0 : Int) ≤ c))
    | RoundingMode.RTP =>
      (!neg)
    | RoundingMode.RTN =>
      neg
    | RoundingMode.RTZ =>
      false))

def sign_cmp (a : Int) (b : Int) : Int :=
  (if _h : a < b then
    ((0 : Int) - (1 : Int))
  else
    (if _h : a = b then
      (0 : Int)
    else
      (1 : Int)))

def fp_round (rm : RoundingMode) (e : Int) (s : Int) (q : Rat) : Int :=
  (match q with
  | (Rat.Rat n d) =>
    (let neg := (decide (n < (0 : Int)))
    (let a := (Rat.Rat (abs n) d)
    (let emin := ((1 : Int) - (fp_bias e))
    (let k := (rat_ilog2 a)
    (let qe := ((if _h : k < emin then
        emin
      else
        k) - (s - (1 : Int)))
    (match (scaled (abs n) d ((0 : Int) - qe)) with
    | (Rat.Rat sn sd) =>
      (let i := (sn / sd)
      (let r := (sn % sd)
      (fp_pack rm e s neg qe (i + (if _h : (round_up rm neg i (sign_cmp ((2 : Int) * r) sd) (!(decide (r = (0 : Int))))) = true then
        (1 : Int)
      else
        (0 : Int)))))))))))))

def fp_add (rm : RoundingMode) (e : Int) (s : Int) (x : Int) (y : Int) : Int :=
  (if _h : ((fp_nan e s x) = true) ∨ ((fp_nan e s y) = true) then
    (fp_nan_bits e s)
  else
    (if _h : (fp_inf e s x) = true then
      (if _h : ((fp_inf e s y) = true) ∧ (¬ ((fp_sign e s x) = (fp_sign e s y))) then
        (fp_nan_bits e s)
      else
        x)
    else
      (if _h : (fp_inf e s y) = true then
        y
      else
        (let q := (rat_add (fp_rat e s x) (fp_rat e s y))
        (if _h : (rat_num q) = (0 : Int) then
          (if _h : (((fp_zero e s x) = true) ∧ ((fp_zero e s y) = true)) ∧ ((fp_sign e s x) = (fp_sign e s y)) then
            x
          else
            (fp_zero_bits e s (is_rtn rm)))
        else
          (fp_round rm e s q))))))

def fp_neg (e : Int) (s : Int) (x : Int) : Int :=
  (if _h : (fp_nan e s x) = true then
    (fp_nan_bits e s)
  else
    (if _h : (fp_sign e s x) = true then
      (x - (pow2 ((e + s) - (1 : Int))))
    else
      (x + (pow2 ((e + s) - (1 : Int))))))

def rat_mul (a : Rat) (b : Rat) : Rat :=
  (match a with
  | (Rat.Rat n d) =>
    (match b with
    | (Rat.Rat m k) =>
      (Rat.Rat (n * m) (d * k))))

def fp_mul (rm : RoundingMode) (e : Int) (s : Int) (x : Int) (y : Int) : Int :=
  (let neg := (!(decide ((fp_sign e s x) = (fp_sign e s y))))
  (if _h : ((fp_nan e s x) = true) ∨ ((fp_nan e s y) = true) then
    (fp_nan_bits e s)
  else
    (if _h : ((fp_inf e s x) = true) ∨ ((fp_inf e s y) = true) then
      (if _h : ((fp_zero e s x) = true) ∨ ((fp_zero e s y) = true) then
        (fp_nan_bits e s)
      else
        (fp_inf_bits e s neg))
    else
      (if _h : ((fp_zero e s x) = true) ∨ ((fp_zero e s y) = true) then
        (fp_zero_bits e s neg)
      else
        (fp_round rm e s (rat_mul (fp_rat e s x) (fp_rat e s y)))))))

def rat_div (a : Rat) (b : Rat) : Rat :=
  (match a with
  | (Rat.Rat n d) =>
    (match b with
    | (Rat.Rat m k) =>
      (if _h : m < (0 : Int) then
        (Rat.Rat ((0 : Int) - (n * k)) ((0 : Int) - (d * m)))
      else
        (Rat.Rat (n * k) (d * m)))))

def fp_div (rm : RoundingMode) (e : Int) (s : Int) (x : Int) (y : Int) : Int :=
  (let neg := (!(decide ((fp_sign e s x) = (fp_sign e s y))))
  (if _h : (((fp_nan e s x) = true) ∨ ((fp_nan e s y) = true)) ∨ ((((fp_inf e s x) = true) ∧ ((fp_inf e s y) = true)) ∨ (((fp_zero e s x) = true) ∧ ((fp_zero e s y) = true))) then
    (fp_nan_bits e s)
  else
    (if _h : (fp_inf e s x) = true then
      (fp_inf_bits e s neg)
    else
      (if _h : (fp_inf e s y) = true then
        (fp_zero_bits e s neg)
      else
        (if _h : (fp_zero e s y) = true then
          (fp_inf_bits e s neg)
        else
          (if _h : (fp_zero e s x) = true then
            (fp_zero_bits e s neg)
          else
            (fp_round rm e s (rat_div (fp_rat e s x) (fp_rat e s y)))))))))

def fp_max (e : Int) (s : Int) (x : Int) (y : Int) (max : Bool) : Int :=
  (if _h : (fp_nan e s x) = true then
    (fp_canonical e s y)
  else
    (if _h : (fp_nan e s y) = true then
      x
    else
      (if _h : ((fp_zero e s x) = true) ∧ ((fp_zero e s y) = true) then
        (if _h : max = (fp_sign e s x) then
          y
        else
          x)
      else
        (if _h : max = (decide ((fp_cmp e s x y) < (0 : Int))) then
          y
        else
          x))))

def fp_op (op : FPOp) (rm : RoundingMode) (e : Int) (s : Int) (x : Int) (y : Int) : Int :=
  (match op with
  | FPOp.FPAddOp =>
    (fp_add rm e s x y)
  | FPOp.FPSubOp =>
    (fp_add rm e s x (fp_neg e s y))
  | FPOp.FPMulOp =>
    (fp_mul rm e s x y)
  | FPOp.FPDivOp =>
    (fp_div rm e s x y)
  | FPOp.FPMinOp =>
    (fp_max e s x y false)
  | FPOp.FPMaxOp =>
    (fp_max e s x y true))

def fp_binary (op : FPOp) (rm : RoundingMode) (a : Value) (b : Value) : Result Value :=
  (match a with
  | (Value.FPV e s x) =>
    (match b with
    | (Value.FPV e2 s2 y) =>
      (if _h : (e = e2) ∧ (s = s2) then
        (Result.Ok (Value.FPV e s (fp_op op rm e s x y)))
      else
        Result.Stuck)
    | _ =>
      Result.Stuck)
  | _ =>
    Result.Stuck)

def fp_fma (rm : RoundingMode) (e : Int) (s : Int) (x : Int) (y : Int) (z : Int) : Int :=
  (let neg := (!(decide ((fp_sign e s x) = (fp_sign e s y))))
  (if _h : (((fp_nan e s x) = true) ∨ ((fp_nan e s y) = true)) ∨ ((fp_nan e s z) = true) then
    (fp_nan_bits e s)
  else
    (if _h : ((fp_inf e s x) = true) ∨ ((fp_inf e s y) = true) then
      (if _h : (((fp_zero e s x) = true) ∨ ((fp_zero e s y) = true)) ∨ (((fp_inf e s z) = true) ∧ (¬ ((fp_sign e s z) = neg))) then
        (fp_nan_bits e s)
      else
        (fp_inf_bits e s neg))
    else
      (if _h : (fp_inf e s z) = true then
        z
      else
        (let q := (rat_add (rat_mul (fp_rat e s x) (fp_rat e s y)) (fp_rat e s z))
        (if _h : (rat_num q) = (0 : Int) then
          (if _h : (((fp_zero e s x) = true) ∨ ((fp_zero e s y) = true)) ∧ (((fp_zero e s z) = true) ∧ ((fp_sign e s z) = neg)) then
            z
          else
            (fp_zero_bits e s (is_rtn rm)))
        else
          (fp_round rm e s q)))))))

def fp_abs (e : Int) (s : Int) (x : Int) : Int :=
  (if _h : (fp_sign e s x) = true then
    (fp_neg e s x)
  else
    (fp_canonical e s x))

def round_rat_int (rm : RoundingMode) (q : Rat) : Int :=
  (match q with
  | (Rat.Rat n d) =>
    (let neg := (decide (n < (0 : Int)))
    (let i := ((abs n) / d)
    (let r := ((abs n) % d)
    (let m := (i + (if _h : (round_up rm neg i (sign_cmp ((2 : Int) * r) d) (!(decide (r = (0 : Int))))) = true then
        (1 : Int)
      else
        (0 : Int)))
    (if _h : neg = true then
      ((0 : Int) - m)
    else
      m))))))

def fp_round_integral (rm : RoundingMode) (e : Int) (s : Int) (x : Int) : Int :=
  (if _h : (((fp_nan e s x) = true) ∨ ((fp_inf e s x) = true)) ∨ ((fp_zero e s x) = true) then
    (fp_canonical e s x)
  else
    (let m := (round_rat_int rm (fp_rat e s x))
    (if _h : m = (0 : Int) then
      (fp_zero_bits e s (fp_sign e s x))
    else
      (fp_round rm e s (Rat.Rat m (1 : Int))))))

def isqrt_from (n : Int) (x : Int) : Int :=
  (let y := ((x + (n / x)) / (2 : Int))
  (if _h : ((0 : Int) < y) ∧ (y < x) then
    (isqrt_from n y)
  else
    x))
termination_by x.toNat
decreasing_by omega

def isqrt (n : Int) : Int :=
  (if _h : n ≤ (0 : Int) then
    (0 : Int)
  else
    (isqrt_from n (pow2 (((bitlen n) + (1 : Int)) / (2 : Int)))))

def fp_sqrt (rm : RoundingMode) (e : Int) (s : Int) (x : Int) : Int :=
  (if _h : (fp_nan e s x) = true then
    (fp_nan_bits e s)
  else
    (if _h : (fp_zero e s x) = true then
      x
    else
      (if _h : (fp_sign e s x) = true then
        (fp_nan_bits e s)
      else
        (if _h : (fp_inf e s x) = true then
          x
        else
          (match (fp_rat e s x) with
          | (Rat.Rat n d) =>
            (let k := ((rat_ilog2 (Rat.Rat n d)) / (2 : Int))
            (let emin := ((1 : Int) - (fp_bias e))
            (let qe := ((if _h : k < emin then
                emin
              else
                k) - (s - (1 : Int)))
            (match (scaled n d ((2 : Int) - ((2 : Int) * qe))) with
            | (Rat.Rat sn sd) =>
              (let m := (sn / sd)
              (let exact := (decide ((sn % sd) = (0 : Int)))
              (let t := (isqrt m)
              (let i := (t / (2 : Int))
              (let half := (decide ((t % (2 : Int)) = (1 : Int)))
              (let sticky := ((!exact) || (!(decide ((t * t) = m))))
              (let c := (if _h : half = true then
                  (if _h : sticky = true then
                    (1 : Int)
                  else
                    (0 : Int))
                else
                  ((0 : Int) - (1 : Int)))
              (fp_pack rm e s false qe (i + (if _h : (round_up rm false i c (half || sticky)) = true then
                (1 : Int)
              else
                (0 : Int))))))))))))))))))))

def fp_of_rat (rm : RoundingMode) (e : Int) (s : Int) (q : Rat) : Int :=
  (if _h : (rat_num q) = (0 : Int) then
    (fp_zero_bits e s false)
  else
    (fp_round rm e s q))

def fp_cast (rm : RoundingMode) (e : Int) (s : Int) (v : Value) : Result Int :=
  (match v with
  | (Value.FPV e2 s2 x) =>
    (if _h : (fp_nan e2 s2 x) = true then
      (Result.Ok (fp_nan_bits e s))
    else
      (if _h : (fp_inf e2 s2 x) = true then
        (Result.Ok (fp_inf_bits e s (fp_sign e2 s2 x)))
      else
        (if _h : (fp_zero e2 s2 x) = true then
          (Result.Ok (fp_zero_bits e s (fp_sign e2 s2 x)))
        else
          (Result.Ok (fp_round rm e s (fp_rat e2 s2 x))))))
  | (Value.BVV sg w x) =>
    (Result.Ok (fp_of_rat rm e s (Rat.Rat (bv_int sg w x) (1 : Int))))
  | (Value.RealV n d) =>
    (Result.Ok (fp_of_rat rm e s (Rat.Rat n d)))
  | _ =>
    Result.Stuck)

def fp_to_int (rm : RoundingMode) (e : Int) (s : Int) (x : Int) (lo : Int) (hi : Int) : Int :=
  (if _h : (fp_nan e s x) = true then
    (0 : Int)
  else
    (if _h : (fp_inf e s x) = true then
      (if _h : (fp_sign e s x) = true then
        lo
      else
        hi)
    else
      (let m := (round_rat_int rm (fp_rat e s x))
      (if _h : m < lo then
        lo
      else
        (if _h : hi < m then
          hi
        else
          m)))))

def fp_class (k : FPClass) (v : Value) : Result Value :=
  (match v with
  | (Value.FPV e s x) =>
    (let be := (fp_exp e s x)
    (let nan := (fp_nan e s x)
    (match k with
    | FPClass.ZeroClass =>
      (Result.Ok (Value.BoolV (fp_zero e s x)))
    | FPClass.InfiniteClass =>
      (Result.Ok (Value.BoolV (fp_inf e s x)))
    | FPClass.NaNClass =>
      (Result.Ok (Value.BoolV nan))
    | FPClass.NegativeClass =>
      (Result.Ok (Value.BoolV ((!nan) && (fp_sign e s x))))
    | FPClass.PositiveClass =>
      (Result.Ok (Value.BoolV ((!nan) && (!(fp_sign e s x)))))
    | FPClass.NormalClass =>
      (Result.Ok (Value.BoolV ((!(decide (be = (0 : Int)))) && (!(decide (be = (fp_max_exp e)))))))
    | FPClass.SubnormalClass =>
      (Result.Ok (Value.BoolV ((decide (be = (0 : Int))) && (!(fp_zero e s x))))))))
  | _ =>
    Result.Stuck)

def nth (vs : List Value) (i : Int) : Result Value :=
  (match vs with
  | List.nil =>
    Result.Stuck
  | (List.cons v rest) =>
    (if _h : i = (1 : Int) then
      (Result.Ok v)
    else
      (nth rest (i - (1 : Int)))))

def set_insert (O : Oracle) (P : Program) (xs : List Value) (v : Value) : Result (List Value) :=
  (match (O.set_contains P xs v) with
  | Result.Ok in_ =>
    (if _h : in_ = true then
      (Result.Ok xs)
    else
      (Result.Ok (List.cons v xs)))
  | Result.Stuck => Result.Stuck
  | Result.OutOfFuel => Result.OutOfFuel)

def set_insert_all (O : Oracle) (P : Program) (xs : List Value) (vs : List Value) : Result (List Value) :=
  (match vs with
  | List.nil =>
    (Result.Ok xs)
  | (List.cons v rest) =>
    (match (set_insert O P xs v) with
    | Result.Ok ys =>
      (set_insert_all O P ys rest)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel))

def set_elems (v : Value) : List Value :=
  (match v with
  | (Value.SetV _ xs) =>
    xs
  | _ =>
    List.nil)

def set_with (v : Value) (xs : List Value) : Value :=
  (match v with
  | (Value.SetV base _) =>
    (Value.SetV base xs)
  | _ =>
    v)

def set_filter (O : Oracle) (P : Program) (xs : List Value) (ys : List Value) (keep : Bool) : Result (List Value) :=
  (match xs with
  | List.nil =>
    (Result.Ok List.nil)
  | (List.cons x rest) =>
    (match (O.set_contains P ys x) with
    | Result.Ok in_ =>
      (match (set_filter O P rest ys keep) with
      | Result.Ok zs =>
        (if _h : in_ = keep then
          (Result.Ok (List.cons x zs))
        else
          (Result.Ok zs))
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel))

def bag_remove (O : Oracle) (P : Program) (xs : List BagEntry) (v : Value) : Result (List BagEntry) :=
  (match xs with
  | List.nil =>
    (Result.Ok List.nil)
  | (List.cons (BagEntry.BagEntry x n) rest) =>
    (match (O.value_eq P x v) with
    | Result.Ok same =>
      (if _h : same = true then
        (Result.Ok rest)
      else
        (match (bag_remove O P rest v) with
        | Result.Ok ys =>
          (Result.Ok (List.cons (BagEntry.BagEntry x n) ys))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel))
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel))

def bag_set (O : Oracle) (P : Program) (xs : List BagEntry) (v : Value) (n : Int) : Result (List BagEntry) :=
  (match (bag_remove O P xs v) with
  | Result.Ok ys =>
    (if _h : (0 : Int) < n then
      (Result.Ok (List.cons (BagEntry.BagEntry v n) ys))
    else
      (Result.Ok ys))
  | Result.Stuck => Result.Stuck
  | Result.OutOfFuel => Result.OutOfFuel)

def bag_entries (v : Value) : List BagEntry :=
  (match v with
  | (Value.BagV _ xs) =>
    xs
  | _ =>
    List.nil)

def bag_with (v : Value) (xs : List BagEntry) : Value :=
  (match v with
  | (Value.BagV base _) =>
    (Value.BagV base xs)
  | _ =>
    v)

def min (a : Int) (b : Int) : Int :=
  (if _h : a < b then
    a
  else
    b)

def bag_combine (op : BagOp) (a : Int) (b : Int) : Int :=
  (match op with
  | BagOp.IntersectionOp =>
    (min a b)
  | BagOp.UnionOp =>
    (a + b)
  | BagOp.DifferenceOp =>
    (a - b))

def bag_merge (O : Oracle) (P : Program) (op : BagOp) (acc : List BagEntry) (xs : List BagEntry) (ys : List BagEntry) : Result (List BagEntry) :=
  (match xs with
  | List.nil =>
    (Result.Ok acc)
  | (List.cons (BagEntry.BagEntry x n) rest) =>
    (match (O.bag_get P ys x) with
    | Result.Ok m =>
      (match (bag_set O P acc x (bag_combine op n m)) with
      | Result.Ok acc2 =>
        (bag_merge O P op acc2 rest ys)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel))

def bag_add_all (O : Oracle) (P : Program) (acc : List BagEntry) (xs : List BagEntry) : Result (List BagEntry) :=
  (match xs with
  | List.nil =>
    (Result.Ok acc)
  | (List.cons (BagEntry.BagEntry x n) rest) =>
    (match (O.bag_get P acc x) with
    | Result.Ok m =>
      (match (bag_set O P acc x (m + n)) with
      | Result.Ok acc2 =>
        (bag_add_all O P acc2 rest)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel))

def map_remove (O : Oracle) (P : Program) (xs : List MapEntry) (k : Value) : Result (List MapEntry) :=
  (match xs with
  | List.nil =>
    (Result.Ok List.nil)
  | (List.cons (MapEntry.MapEntry x v) rest) =>
    (match (O.value_eq P x k) with
    | Result.Ok same =>
      (if _h : same = true then
        (Result.Ok rest)
      else
        (match (map_remove O P rest k) with
        | Result.Ok ys =>
          (Result.Ok (List.cons (MapEntry.MapEntry x v) ys))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel))
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel))

def map_put (O : Oracle) (P : Program) (xs : List MapEntry) (k : Value) (v : Value) : Result (List MapEntry) :=
  (match (map_remove O P xs k) with
  | Result.Ok ys =>
    (Result.Ok (List.cons (MapEntry.MapEntry k v) ys))
  | Result.Stuck => Result.Stuck
  | Result.OutOfFuel => Result.OutOfFuel)

def map_without (O : Oracle) (P : Program) (xs : List MapEntry) (ks : List Value) : Result (List MapEntry) :=
  (match xs with
  | List.nil =>
    (Result.Ok List.nil)
  | (List.cons (MapEntry.MapEntry k v) rest) =>
    (match (O.set_contains P ks k) with
    | Result.Ok in_ =>
      (match (map_without O P rest ks) with
      | Result.Ok ys =>
        (if _h : in_ = true then
          (Result.Ok ys)
        else
          (Result.Ok (List.cons (MapEntry.MapEntry k v) ys)))
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel))

def map_take (O : Oracle) (P : Program) (acc : List MapEntry) (ks : List Value) (xs : List MapEntry) (d : Value) : Result (List MapEntry) :=
  (match ks with
  | List.nil =>
    (Result.Ok acc)
  | (List.cons k rest) =>
    (match (O.map_get P xs k d) with
    | Result.Ok v =>
      (match (map_put O P acc k v) with
      | Result.Ok acc2 =>
        (map_take O P acc2 rest xs d)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel))

mutual
def call (O : Oracle) (P : Program) (fuel : Int) (f : Id) (tps : List Ty) (tenv : List TypeBinding) (vs : List Value) : Result Value :=
  (if _h : fuel ≤ (0 : Int) then
    Result.OutOfFuel
  else
    (match P with
    | (Program.Program fs _ _ _ _) =>
      (match (lookup_fun fs f) with
      | Result.Ok fd =>
        (match fd with
        | (FunDef.FunDef _ tparams params body) =>
          (match (bind_all params vs) with
          | Result.Ok bs =>
            (eval O P (fuel - (1 : Int)) (Env.Env (bind_types tparams tps tenv) bs) body)
          | Result.Stuck => Result.Stuck
          | Result.OutOfFuel => Result.OutOfFuel))
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)))
termination_by (fuel.toNat, 0, 0)

def eval (O : Oracle) (P : Program) (fuel : Int) (env : Env) (e : Expr) : Result Value :=
  match e with
  | (Expr.Assume pred body) =>
    (match (eval_bool O P fuel env pred) with
    | Result.Ok b =>
      (if _h : b = true then
        (eval O P fuel env body)
      else
        Result.Stuck)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.Variable x) =>
    (lookup_var (env_vars env) x)
  | (Expr.Let x value body) =>
    (match (eval O P fuel env value) with
    | Result.Ok v =>
      (eval O P fuel (env_bind env x v) body)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.Application callee args) =>
    (match (eval O P fuel env callee) with
    | Result.Ok f =>
      (match (eval_list O P fuel env args) with
      | Result.Ok vs =>
        (apply O P fuel f vs)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.Lambda params body) =>
    (Result.Ok (Value.ClosureV params body env))
  | (Expr.Forall params body) =>
    (O.forall_result P fuel env params body)
  | (Expr.UninterpretedCall f tps args) =>
    (match (eval_list O P fuel env args) with
    | Result.Ok vs =>
      (if _h : fuel ≤ (0 : Int) then
        Result.OutOfFuel
      else
        (match P with
        | (Program.Program _ _ _ is _) =>
          (match (lookup_interpretation is f (O.resolve_all (env_types env) tps)) with
          | Result.Ok i =>
            (match i with
            | (Interpretation.Interpretation _ _ params body) =>
              (match (bind_all params vs) with
              | Result.Ok bs =>
                (eval O P (fuel - (1 : Int)) (Env.Env List.nil bs) body)
              | Result.Stuck => Result.Stuck
              | Result.OutOfFuel => Result.OutOfFuel))
          | Result.Stuck => Result.Stuck
          | Result.OutOfFuel => Result.OutOfFuel)))
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | Expr.Error =>
    Result.Stuck
  | (Expr.FunctionInvocation f tps args) =>
    (match (eval_list O P fuel env args) with
    | Result.Ok vs =>
      (call O P fuel f tps (env_types env) vs)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.IfExpr cond thenn elze) =>
    (match (eval_bool O P fuel env cond) with
    | Result.Ok b =>
      (if _h : b = true then
        (eval O P fuel env thenn)
      else
        (eval O P fuel env elze))
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.CharLiteral c) =>
    (Result.Ok (Value.CharV c))
  | (Expr.BVLiteral s w x) =>
    (Result.Ok (Value.BVV s w x))
  | (Expr.IntegerLiteral i) =>
    (Result.Ok (Value.IntV i))
  | (Expr.FractionLiteral n d) =>
    (real n d)
  | (Expr.FPLiteral e s x) =>
    (Result.Ok (Value.FPV e s (fp_canonical e s x)))
  | (Expr.BooleanLiteral b) =>
    (Result.Ok (Value.BoolV b))
  | (Expr.StringLiteral cs) =>
    (Result.Ok (Value.StringV cs))
  | Expr.UnitLiteral =>
    (Result.Ok Value.UnitV)
  | Expr.RoundNearestTiesToEven =>
    (Result.Ok (Value.RoundingModeV RoundingMode.RNE))
  | Expr.RoundNearestTiesToAway =>
    (Result.Ok (Value.RoundingModeV RoundingMode.RNA))
  | Expr.RoundTowardPositive =>
    (Result.Ok (Value.RoundingModeV RoundingMode.RTP))
  | Expr.RoundTowardNegative =>
    (Result.Ok (Value.RoundingModeV RoundingMode.RTN))
  | Expr.RoundTowardZero =>
    (Result.Ok (Value.RoundingModeV RoundingMode.RTZ))
  | (Expr.ADT c tps args) =>
    (match (eval_list O P fuel env args) with
    | Result.Ok vs =>
      (construct O P fuel env c tps vs)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.IsConstructor adt c) =>
    (match (eval O P fuel env adt) with
    | Result.Ok v =>
      (match v with
      | (Value.ADTV d _ _) =>
        (Result.Ok (Value.BoolV (decide (c = d))))
      | _ =>
        Result.Stuck)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.ADTSelector adt sel) =>
    (match (eval O P fuel env adt) with
    | Result.Ok v =>
      (match v with
      | (Value.ADTV c _ vs) =>
        (match P with
        | (Program.Program _ cs _ _ _) =>
          (match (lookup_ctor cs c) with
          | Result.Ok k =>
            (match k with
            | (Constructor.Constructor _ _ fields) =>
              (select_field fields vs sel))
          | Result.Stuck => Result.Stuck
          | Result.OutOfFuel => Result.OutOfFuel))
      | _ =>
        Result.Stuck)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.Equals lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (match (O.value_eq P a b) with
        | Result.Ok same =>
          (Result.Ok (Value.BoolV same))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.And es) =>
    (eval_and O P fuel env es)
  | (Expr.Or es) =>
    (eval_or O P fuel env es)
  | (Expr.Implies lhs rhs) =>
    (match (eval_bool O P fuel env lhs) with
    | Result.Ok a =>
      (if _h : a = true then
        (match (eval_bool O P fuel env rhs) with
        | Result.Ok b =>
          (Result.Ok (Value.BoolV b))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      else
        (Result.Ok (Value.BoolV true)))
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.Not expr) =>
    (match (eval_bool O P fuel env expr) with
    | Result.Ok a =>
      (Result.Ok (Value.BoolV (!a)))
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.StringConcat lhs rhs) =>
    (match (eval_string O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval_string O P fuel env rhs) with
      | Result.Ok b =>
        (Result.Ok (Value.StringV (append_chars a b)))
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.SubString expr start end_) =>
    (match (eval_string O P fuel env expr) with
    | Result.Ok cs =>
      (match (eval_int O P fuel env start) with
      | Result.Ok b =>
        (match (eval_int O P fuel env end_) with
        | Result.Ok c =>
          (if _h : (b < (0 : Int)) ∨ (c ≤ b) then
            (Result.Ok (Value.StringV List.nil))
          else
            (Result.Ok (Value.StringV (take (c - b) (drop b cs)))))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.StringLength expr) =>
    (match (eval_string O P fuel env expr) with
    | Result.Ok cs =>
      (Result.Ok (Value.IntV (length cs)))
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.Plus lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (arith_plus a b)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.Minus lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (arith_minus a b)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.UMinus expr) =>
    (match (eval O P fuel env expr) with
    | Result.Ok a =>
      (arith_neg a)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.Times lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (arith_times a b)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.Division lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (arith_div a b)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.Remainder lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (arith_rem a b)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.Modulo lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (arith_mod a b)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.LessThan lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (match (arith_lt a b) with
        | Result.Ok r =>
          (Result.Ok (Value.BoolV r))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.GreaterThan lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (match (arith_lt b a) with
        | Result.Ok r =>
          (Result.Ok (Value.BoolV r))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.LessEquals lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (match (arith_le a b) with
        | Result.Ok r =>
          (Result.Ok (Value.BoolV r))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.GreaterEquals lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (match (arith_le b a) with
        | Result.Ok r =>
          (Result.Ok (Value.BoolV r))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.BVNot expr) =>
    (match (eval O P fuel env expr) with
    | Result.Ok a =>
      (match a with
      | (Value.BVV s w x) =>
        (Result.Ok (Value.BVV s w (((pow2 w) - (1 : Int)) - x)))
      | _ =>
        Result.Stuck)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.BVAnd lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (bv_binary BitOp.AndOp a b)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.BVOr lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (bv_binary BitOp.OrOp a b)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.BVXor lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (bv_binary BitOp.XorOp a b)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.BVShiftLeft lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (bv_binary BitOp.ShiftLeftOp a b)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.BVAShiftRight lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (bv_binary BitOp.AShiftRightOp a b)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.BVLShiftRight lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (bv_binary BitOp.LShiftRightOp a b)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.BVNarrowingCast expr w) =>
    (match (eval O P fuel env expr) with
    | Result.Ok a =>
      (bv_cast a w)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.BVWideningCast expr w) =>
    (match (eval O P fuel env expr) with
    | Result.Ok a =>
      (bv_cast a w)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.BVUnsignedToSigned expr) =>
    (match (eval O P fuel env expr) with
    | Result.Ok a =>
      (match a with
      | (Value.BVV false w x) =>
        (Result.Ok (Value.BVV true w x))
      | _ =>
        Result.Stuck)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.BVSignedToUnsigned expr) =>
    (match (eval O P fuel env expr) with
    | Result.Ok a =>
      (match a with
      | (Value.BVV true w x) =>
        (Result.Ok (Value.BVV false w x))
      | _ =>
        Result.Stuck)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.BVToInt expr) =>
    (match (eval O P fuel env expr) with
    | Result.Ok a =>
      (match a with
      | (Value.BVV s w x) =>
        (Result.Ok (Value.IntV (bv_int s w x)))
      | _ =>
        Result.Stuck)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.IntToBV w s expr) =>
    (match (eval_int O P fuel env expr) with
    | Result.Ok i =>
      (Result.Ok (bv s w i))
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPEquals lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (fp_rel FPRel.FPEqRel a b)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPAdd rm lhs rhs) =>
    (match (eval_rm O P fuel env rm) with
    | Result.Ok m =>
      (match (eval O P fuel env lhs) with
      | Result.Ok a =>
        (match (eval O P fuel env rhs) with
        | Result.Ok b =>
          (fp_binary FPOp.FPAddOp m a b)
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPSub rm lhs rhs) =>
    (match (eval_rm O P fuel env rm) with
    | Result.Ok m =>
      (match (eval O P fuel env lhs) with
      | Result.Ok a =>
        (match (eval O P fuel env rhs) with
        | Result.Ok b =>
          (fp_binary FPOp.FPSubOp m a b)
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPUMinus expr) =>
    (match (eval O P fuel env expr) with
    | Result.Ok a =>
      (match a with
      | (Value.FPV e s x) =>
        (Result.Ok (Value.FPV e s (fp_neg e s x)))
      | _ =>
        Result.Stuck)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPFMA rm e1 e2 e3) =>
    (match (eval_rm O P fuel env rm) with
    | Result.Ok m =>
      (match (eval O P fuel env e1) with
      | Result.Ok a =>
        (match (eval O P fuel env e2) with
        | Result.Ok b =>
          (match (eval O P fuel env e3) with
          | Result.Ok c =>
            (match a with
            | (Value.FPV e s x) =>
              (match b with
              | (Value.FPV e2 s2 y) =>
                (match c with
                | (Value.FPV e3 s3 z) =>
                  (if _h : ((e = e2) ∧ (s = s2)) ∧ ((e = e3) ∧ (s = s3)) then
                    (Result.Ok (Value.FPV e s (fp_fma m e s x y z)))
                  else
                    Result.Stuck)
                | _ =>
                  Result.Stuck)
              | _ =>
                Result.Stuck)
            | _ =>
              Result.Stuck)
          | Result.Stuck => Result.Stuck
          | Result.OutOfFuel => Result.OutOfFuel)
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPMul rm lhs rhs) =>
    (match (eval_rm O P fuel env rm) with
    | Result.Ok m =>
      (match (eval O P fuel env lhs) with
      | Result.Ok a =>
        (match (eval O P fuel env rhs) with
        | Result.Ok b =>
          (fp_binary FPOp.FPMulOp m a b)
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPDiv rm lhs rhs) =>
    (match (eval_rm O P fuel env rm) with
    | Result.Ok m =>
      (match (eval O P fuel env lhs) with
      | Result.Ok a =>
        (match (eval O P fuel env rhs) with
        | Result.Ok b =>
          (fp_binary FPOp.FPDivOp m a b)
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPAbs expr) =>
    (match (eval O P fuel env expr) with
    | Result.Ok a =>
      (match a with
      | (Value.FPV e s x) =>
        (Result.Ok (Value.FPV e s (fp_abs e s x)))
      | _ =>
        Result.Stuck)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPMax lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (fp_binary FPOp.FPMaxOp RoundingMode.RNE a b)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPMin lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (fp_binary FPOp.FPMinOp RoundingMode.RNE a b)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPRound rm expr) =>
    (match (eval_rm O P fuel env rm) with
    | Result.Ok m =>
      (match (eval O P fuel env expr) with
      | Result.Ok a =>
        (match a with
        | (Value.FPV e s x) =>
          (Result.Ok (Value.FPV e s (fp_round_integral m e s x)))
        | _ =>
          Result.Stuck)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.Sqrt rm expr) =>
    (match (eval_rm O P fuel env rm) with
    | Result.Ok m =>
      (match (eval O P fuel env expr) with
      | Result.Ok a =>
        (match a with
        | (Value.FPV e s x) =>
          (Result.Ok (Value.FPV e s (fp_sqrt m e s x)))
        | _ =>
          Result.Stuck)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPCast e s rm expr) =>
    (match (eval_rm O P fuel env rm) with
    | Result.Ok m =>
      (match (eval O P fuel env expr) with
      | Result.Ok a =>
        (match (fp_cast m e s a) with
        | Result.Ok x =>
          (Result.Ok (Value.FPV e s x))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPFromBinary e s expr) =>
    (match (eval O P fuel env expr) with
    | Result.Ok a =>
      (match a with
      | (Value.BVV _ w x) =>
        (if _h : w = (e + s) then
          (Result.Ok (Value.FPV e s (fp_canonical e s x)))
        else
          Result.Stuck)
      | _ =>
        Result.Stuck)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPToBV w sg rm expr) =>
    (match (eval_rm O P fuel env rm) with
    | Result.Ok m =>
      (match (eval O P fuel env expr) with
      | Result.Ok a =>
        (match a with
        | (Value.FPV e s x) =>
          (let lo := (if _h : sg = true then
              ((0 : Int) - (pow2 (w - (1 : Int))))
            else
              (0 : Int))
          (let hi := (if _h : sg = true then
              ((pow2 (w - (1 : Int))) - (1 : Int))
            else
              ((pow2 w) - (1 : Int)))
          (Result.Ok (bv sg w (fp_to_int m e s x lo hi)))))
        | _ =>
          Result.Stuck)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPToReal expr) =>
    (match (eval O P fuel env expr) with
    | Result.Ok a =>
      (match a with
      | (Value.FPV e s x) =>
        (if _h : ((fp_nan e s x) = true) ∨ ((fp_inf e s x) = true) then
          Result.Stuck
        else
          (match (fp_rat e s x) with
          | (Rat.Rat n d) =>
            (real n d)))
      | _ =>
        Result.Stuck)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPLessThan lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (fp_rel FPRel.FPLtRel a b)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPGreaterThan lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (fp_rel FPRel.FPLtRel b a)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPLessEquals lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (fp_rel FPRel.FPLeRel a b)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPGreaterEquals lhs rhs) =>
    (match (eval O P fuel env lhs) with
    | Result.Ok a =>
      (match (eval O P fuel env rhs) with
      | Result.Ok b =>
        (fp_rel FPRel.FPLeRel b a)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPIsZero expr) =>
    (match (eval O P fuel env expr) with
    | Result.Ok a =>
      (fp_class FPClass.ZeroClass a)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPIsInfinite expr) =>
    (match (eval O P fuel env expr) with
    | Result.Ok a =>
      (fp_class FPClass.InfiniteClass a)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPIsNaN expr) =>
    (match (eval O P fuel env expr) with
    | Result.Ok a =>
      (fp_class FPClass.NaNClass a)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPIsNegative expr) =>
    (match (eval O P fuel env expr) with
    | Result.Ok a =>
      (fp_class FPClass.NegativeClass a)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPIsPositive expr) =>
    (match (eval O P fuel env expr) with
    | Result.Ok a =>
      (fp_class FPClass.PositiveClass a)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPIsNormal expr) =>
    (match (eval O P fuel env expr) with
    | Result.Ok a =>
      (fp_class FPClass.NormalClass a)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FPIsSubnormal expr) =>
    (match (eval O P fuel env expr) with
    | Result.Ok a =>
      (fp_class FPClass.SubnormalClass a)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.Tuple es) =>
    (match (eval_list O P fuel env es) with
    | Result.Ok vs =>
      (Result.Ok (Value.TupleV vs))
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.TupleSelect tuple i) =>
    (match (eval O P fuel env tuple) with
    | Result.Ok t =>
      (match t with
      | (Value.TupleV vs) =>
        (nth vs i)
      | _ =>
        Result.Stuck)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FiniteSet es base) =>
    (match (eval_list O P fuel env es) with
    | Result.Ok vs =>
      (match (set_insert_all O P List.nil vs) with
      | Result.Ok xs =>
        (Result.Ok (Value.SetV (O.resolve (env_types env) base) xs))
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.SetAdd set elem) =>
    (match (eval_set O P fuel env set) with
    | Result.Ok s =>
      (match (eval O P fuel env elem) with
      | Result.Ok v =>
        (match (set_insert O P (set_elems s) v) with
        | Result.Ok ys =>
          (Result.Ok (set_with s ys))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.ElementOfSet elem set) =>
    (match (eval O P fuel env elem) with
    | Result.Ok v =>
      (match (eval_set O P fuel env set) with
      | Result.Ok s =>
        (match (O.set_contains P (set_elems s) v) with
        | Result.Ok in_ =>
          (Result.Ok (Value.BoolV in_))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.SubsetOf lhs rhs) =>
    (match (eval_set O P fuel env lhs) with
    | Result.Ok s =>
      (match (eval_set O P fuel env rhs) with
      | Result.Ok u =>
        (match (O.subset P (set_elems s) (set_elems u)) with
        | Result.Ok sub =>
          (Result.Ok (Value.BoolV sub))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.SetIntersection lhs rhs) =>
    (match (eval_set O P fuel env lhs) with
    | Result.Ok s =>
      (match (eval_set O P fuel env rhs) with
      | Result.Ok u =>
        (match (set_filter O P (set_elems s) (set_elems u) true) with
        | Result.Ok zs =>
          (Result.Ok (set_with s zs))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.SetUnion lhs rhs) =>
    (match (eval_set O P fuel env lhs) with
    | Result.Ok s =>
      (match (eval_set O P fuel env rhs) with
      | Result.Ok u =>
        (match (set_insert_all O P (set_elems s) (set_elems u)) with
        | Result.Ok zs =>
          (Result.Ok (set_with s zs))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.SetDifference lhs rhs) =>
    (match (eval_set O P fuel env lhs) with
    | Result.Ok s =>
      (match (eval_set O P fuel env rhs) with
      | Result.Ok u =>
        (match (set_filter O P (set_elems s) (set_elems u) false) with
        | Result.Ok zs =>
          (Result.Ok (set_with s zs))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FiniteBag es base) =>
    (match (eval_bag_entries O P fuel env List.nil es) with
    | Result.Ok xs =>
      (Result.Ok (Value.BagV (O.resolve (env_types env) base) xs))
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.BagAdd bag elem) =>
    (match (eval_bag O P fuel env bag) with
    | Result.Ok b =>
      (match (eval O P fuel env elem) with
      | Result.Ok v =>
        (match (O.bag_get P (bag_entries b) v) with
        | Result.Ok n =>
          (match (bag_set O P (bag_entries b) v (n + (1 : Int))) with
          | Result.Ok ys =>
            (Result.Ok (bag_with b ys))
          | Result.Stuck => Result.Stuck
          | Result.OutOfFuel => Result.OutOfFuel)
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.MultiplicityInBag elem bag) =>
    (match (eval O P fuel env elem) with
    | Result.Ok v =>
      (match (eval_bag O P fuel env bag) with
      | Result.Ok b =>
        (match (O.bag_get P (bag_entries b) v) with
        | Result.Ok n =>
          (Result.Ok (Value.IntV n))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.BagIntersection lhs rhs) =>
    (match (eval_bag O P fuel env lhs) with
    | Result.Ok b =>
      (match (eval_bag O P fuel env rhs) with
      | Result.Ok c =>
        (match (bag_merge O P BagOp.IntersectionOp List.nil (bag_entries b) (bag_entries c)) with
        | Result.Ok zs =>
          (Result.Ok (bag_with b zs))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.BagUnion lhs rhs) =>
    (match (eval_bag O P fuel env lhs) with
    | Result.Ok b =>
      (match (eval_bag O P fuel env rhs) with
      | Result.Ok c =>
        (match (bag_add_all O P (bag_entries b) (bag_entries c)) with
        | Result.Ok zs =>
          (Result.Ok (bag_with b zs))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.BagDifference lhs rhs) =>
    (match (eval_bag O P fuel env lhs) with
    | Result.Ok b =>
      (match (eval_bag O P fuel env rhs) with
      | Result.Ok c =>
        (match (bag_merge O P BagOp.DifferenceOp List.nil (bag_entries b) (bag_entries c)) with
        | Result.Ok zs =>
          (Result.Ok (bag_with b zs))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.FiniteMap pairs default kt vt) =>
    (match (eval_map_entries O P fuel env List.nil pairs) with
    | Result.Ok xs =>
      (match (eval O P fuel env default) with
      | Result.Ok d =>
        (Result.Ok (Value.MapV (O.resolve (env_types env) kt) (O.resolve (env_types env) vt) xs d))
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.MapApply map key) =>
    (match (eval O P fuel env map) with
    | Result.Ok m =>
      (match (eval O P fuel env key) with
      | Result.Ok k =>
        (match m with
        | (Value.MapV _ _ xs d) =>
          (O.map_get P xs k d)
        | _ =>
          Result.Stuck)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.MapUpdated map key value) =>
    (match (eval O P fuel env map) with
    | Result.Ok m =>
      (match (eval O P fuel env key) with
      | Result.Ok k =>
        (match (eval O P fuel env value) with
        | Result.Ok v =>
          (match m with
          | (Value.MapV kt vt xs d) =>
            (match (map_put O P xs k v) with
            | Result.Ok ys =>
              (Result.Ok (Value.MapV kt vt ys d))
            | Result.Stuck => Result.Stuck
            | Result.OutOfFuel => Result.OutOfFuel)
          | _ =>
            Result.Stuck)
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
  | (Expr.MapMerge mask map1 map2) =>
    (match (eval_set O P fuel env mask) with
    | Result.Ok ks =>
      (match (eval O P fuel env map1) with
      | Result.Ok m1 =>
        (match (eval O P fuel env map2) with
        | Result.Ok m2 =>
          (match m1 with
          | (Value.MapV _ _ xs d1) =>
            (match m2 with
            | (Value.MapV kt vt ys d2) =>
              (match (map_without O P ys (set_elems ks)) with
              | Result.Ok rest =>
                (match (map_take O P rest (set_elems ks) xs d1) with
                | Result.Ok zs =>
                  (Result.Ok (Value.MapV kt vt zs d2))
                | Result.Stuck => Result.Stuck
                | Result.OutOfFuel => Result.OutOfFuel)
              | Result.Stuck => Result.Stuck
              | Result.OutOfFuel => Result.OutOfFuel)
            | _ =>
              Result.Stuck)
          | _ =>
            Result.Stuck)
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel)
termination_by (fuel.toNat, sizeOf e, 0)

def eval_list (O : Oracle) (P : Program) (fuel : Int) (env : Env) (es : List Expr) : Result (List Value) :=
  (match es with
  | List.nil =>
    (Result.Ok List.nil)
  | (List.cons e rest) =>
    (match (eval O P fuel env e) with
    | Result.Ok v =>
      (match (eval_list O P fuel env rest) with
      | Result.Ok vs =>
        (Result.Ok (List.cons v vs))
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel))
termination_by (fuel.toNat, sizeOf es, 0)

def eval_int (O : Oracle) (P : Program) (fuel : Int) (env : Env) (e : Expr) : Result Int :=
  (match (eval O P fuel env e) with
  | Result.Ok v =>
    (match v with
    | (Value.IntV i) =>
      (Result.Ok i)
    | _ =>
      Result.Stuck)
  | Result.Stuck => Result.Stuck
  | Result.OutOfFuel => Result.OutOfFuel)
termination_by (fuel.toNat, sizeOf e, 1)

def eval_bool (O : Oracle) (P : Program) (fuel : Int) (env : Env) (e : Expr) : Result Bool :=
  (match (eval O P fuel env e) with
  | Result.Ok v =>
    (match v with
    | (Value.BoolV b) =>
      (Result.Ok b)
    | _ =>
      Result.Stuck)
  | Result.Stuck => Result.Stuck
  | Result.OutOfFuel => Result.OutOfFuel)
termination_by (fuel.toNat, sizeOf e, 1)

def construct (O : Oracle) (P : Program) (fuel : Int) (env : Env) (c : Id) (tps : List Ty) (vs : List Value) : Result Value :=
  (match P with
  | (Program.Program _ cs ss _ _) =>
    (match (lookup_ctor cs c) with
    | Result.Ok k =>
      (match k with
      | (Constructor.Constructor _ s _) =>
        (match (lookup_sort ss s) with
        | Result.Ok srt =>
          (match srt with
          | (ADTSort.Sort _ _ Option.none _) =>
            (Result.Ok (Value.ADTV c (O.resolve_all (env_types env) tps) vs))
          | (ADTSort.Sort _ _ (Option.some inv) _) =>
            (match (call O P fuel inv tps (env_types env) (List.cons (Value.ADTV c (O.resolve_all (env_types env) tps) vs) List.nil)) with
            | Result.Ok holds =>
              (match holds with
              | (Value.BoolV true) =>
                (Result.Ok (Value.ADTV c (O.resolve_all (env_types env) tps) vs))
              | _ =>
                Result.Stuck)
            | Result.Stuck => Result.Stuck
            | Result.OutOfFuel => Result.OutOfFuel))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel))
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel))
termination_by (fuel.toNat, 0, 1)

def eval_and (O : Oracle) (P : Program) (fuel : Int) (env : Env) (es : List Expr) : Result Value :=
  (match es with
  | List.nil =>
    (Result.Ok (Value.BoolV true))
  | (List.cons e rest) =>
    (match (eval_bool O P fuel env e) with
    | Result.Ok b =>
      (if _h : b = true then
        (eval_and O P fuel env rest)
      else
        (Result.Ok (Value.BoolV false)))
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel))
termination_by (fuel.toNat, sizeOf es, 0)

def eval_or (O : Oracle) (P : Program) (fuel : Int) (env : Env) (es : List Expr) : Result Value :=
  (match es with
  | List.nil =>
    (Result.Ok (Value.BoolV false))
  | (List.cons e rest) =>
    (match (eval_bool O P fuel env e) with
    | Result.Ok b =>
      (if _h : b = true then
        (Result.Ok (Value.BoolV true))
      else
        (eval_or O P fuel env rest))
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel))
termination_by (fuel.toNat, sizeOf es, 0)

def apply (O : Oracle) (P : Program) (fuel : Int) (f : Value) (vs : List Value) : Result Value :=
  (match f with
  | (Value.ClosureV params body (Env.Env tys vars)) =>
    (if _h : fuel ≤ (0 : Int) then
      Result.OutOfFuel
    else
      (match (bind_all (param_ids params) vs) with
      | Result.Ok bs =>
        (eval O P (fuel - (1 : Int)) (Env.Env tys (append_env bs vars)) body)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel))
  | _ =>
    Result.Stuck)
termination_by (fuel.toNat, 0, 0)

def eval_rm (O : Oracle) (P : Program) (fuel : Int) (env : Env) (e : Expr) : Result RoundingMode :=
  (match (eval O P fuel env e) with
  | Result.Ok v =>
    (match v with
    | (Value.RoundingModeV rm) =>
      (Result.Ok rm)
    | _ =>
      Result.Stuck)
  | Result.Stuck => Result.Stuck
  | Result.OutOfFuel => Result.OutOfFuel)
termination_by (fuel.toNat, sizeOf e, 1)

def eval_string (O : Oracle) (P : Program) (fuel : Int) (env : Env) (e : Expr) : Result (List Int) :=
  (match (eval O P fuel env e) with
  | Result.Ok v =>
    (match v with
    | (Value.StringV cs) =>
      (Result.Ok cs)
    | _ =>
      Result.Stuck)
  | Result.Stuck => Result.Stuck
  | Result.OutOfFuel => Result.OutOfFuel)
termination_by (fuel.toNat, sizeOf e, 1)

def eval_set (O : Oracle) (P : Program) (fuel : Int) (env : Env) (e : Expr) : Result Value :=
  (match (eval O P fuel env e) with
  | Result.Ok v =>
    (match v with
    | (Value.SetV _ _) =>
      (Result.Ok v)
    | _ =>
      Result.Stuck)
  | Result.Stuck => Result.Stuck
  | Result.OutOfFuel => Result.OutOfFuel)
termination_by (fuel.toNat, sizeOf e, 1)

def eval_bag (O : Oracle) (P : Program) (fuel : Int) (env : Env) (e : Expr) : Result Value :=
  (match (eval O P fuel env e) with
  | Result.Ok v =>
    (match v with
    | (Value.BagV _ _) =>
      (Result.Ok v)
    | _ =>
      Result.Stuck)
  | Result.Stuck => Result.Stuck
  | Result.OutOfFuel => Result.OutOfFuel)
termination_by (fuel.toNat, sizeOf e, 1)

def eval_bag_entries (O : Oracle) (P : Program) (fuel : Int) (env : Env) (acc : List BagEntry) (es : List ExprPair) : Result (List BagEntry) :=
  (match es with
  | List.nil =>
    (Result.Ok acc)
  | (List.cons (ExprPair.ExprPair k c) rest) =>
    (match (eval O P fuel env k) with
    | Result.Ok v =>
      (match (eval_int O P fuel env c) with
      | Result.Ok n =>
        (match (bag_set O P acc v n) with
        | Result.Ok acc2 =>
          (eval_bag_entries O P fuel env acc2 rest)
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel))
termination_by (fuel.toNat, sizeOf es, 0)

def eval_map_entries (O : Oracle) (P : Program) (fuel : Int) (env : Env) (acc : List MapEntry) (es : List ExprPair) : Result (List MapEntry) :=
  (match es with
  | List.nil =>
    (Result.Ok acc)
  | (List.cons (ExprPair.ExprPair k v) rest) =>
    (match (eval O P fuel env k) with
    | Result.Ok kv =>
      (match (eval O P fuel env v) with
      | Result.Ok vv =>
        (match (map_put O P acc kv vv) with
        | Result.Ok acc2 =>
          (eval_map_entries O P fuel env acc2 rest)
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel))
termination_by (fuel.toNat, sizeOf es, 0)
end

def sort_equality (P : Program) (c : Id) : Option Id :=
  (match P with
  | (Program.Program _ cs ss _ _) =>
    (match (lookup_ctor cs c) with
    | (Result.Ok (Constructor.Constructor _ s _)) =>
      (match (lookup_sort ss s) with
      | (Result.Ok (ADTSort.Sort _ _ _ eq)) =>
        eq
      | _ =>
        Option.none)
    | _ =>
      Option.none))

def param_types (ps : List Param) : List Ty :=
  (match ps with
  | List.nil =>
    List.nil
  | (List.cons (Param.Param _ t) rest) =>
    (List.cons t (param_types rest)))

def valid_chars (cs : List Int) : Bool :=
  (match cs with
  | List.nil =>
    true
  | (List.cons c rest) =>
    (((decide ((0 : Int) ≤ c)) && (decide (c ≤ (196607 : Int)))) && (valid_chars rest)))

def distinct_values (O : Oracle) (P : Program) (xs : List Value) : Bool :=
  (match xs with
  | List.nil =>
    true
  | (List.cons x rest) =>
    ((decide ((O.set_contains P rest x) = (Result.Ok false))) && (distinct_values O P rest)))

def bag_elems (xs : List BagEntry) : List Value :=
  (match xs with
  | List.nil =>
    List.nil
  | (List.cons (BagEntry.BagEntry x _) rest) =>
    (List.cons x (bag_elems rest)))

def map_keys (xs : List MapEntry) : List Value :=
  (match xs with
  | List.nil =>
    List.nil
  | (List.cons (MapEntry.MapEntry k _) rest) =>
    (List.cons k (map_keys rest)))

def same_arity (ps : List Param) (ts : List Ty) : Bool :=
  (match ps with
  | List.nil =>
    (match ts with
    | List.nil =>
      true
    | _ =>
      false)
  | (List.cons _ rest) =>
    (match ts with
    | List.nil =>
      false
    | (List.cons _ more) =>
      (same_arity rest more)))

def instance_ (O : Oracle) (P : Program) (fuel : Int) (env : Env) (params : List Param) (vs : List Value) (body : Expr) : Result Value :=
  (match env with
  | (Env.Env tys vars) =>
    (match (bind_all (param_ids params) vs) with
    | Result.Ok bs =>
      (eval O P fuel (Env.Env tys (append_env bs vars)) body)
    | Result.Stuck => Result.Stuck
    | Result.OutOfFuel => Result.OutOfFuel))

/-- The oracle gives each of its functions as the semantics defines it. -/
structure Oracle.Sound (O : Oracle) : Prop where
  value_eq : ∀ (P : Program) (a : Value) (b : Value), O.value_eq P a b = (
    match a with
    | (Value.IntV _) =>
      (Result.Ok (decide (a = b)))
    | (Value.BoolV _) =>
      (Result.Ok (decide (a = b)))
    | Value.UnitV =>
      (Result.Ok (decide (a = b)))
    | (Value.CharV _) =>
      (Result.Ok (decide (a = b)))
    | (Value.RealV _ _) =>
      (Result.Ok (decide (a = b)))
    | (Value.StringV _) =>
      (Result.Ok (decide (a = b)))
    | (Value.BVV _ _ _) =>
      (Result.Ok (decide (a = b)))
    | (Value.FPV _ _ _) =>
      (Result.Ok (decide (a = b)))
    | (Value.RoundingModeV _) =>
      (Result.Ok (decide (a = b)))
    | (Value.TupleV xs) =>
      (match b with
      | (Value.TupleV ys) =>
        (O.values_eq P xs ys)
      | _ =>
        (Result.Ok false))
    | (Value.ClosureV _ _ _) =>
      (match P with
      | (Program.Program _ _ _ _ eq) =>
        (match eq with
        | FunctionEquality.NoFunctionEquality =>
          Result.Stuck
        | FunctionEquality.ExtensionalEquality =>
          (Result.Ok (O.closures_equal P a b))))
    | (Value.SetV _ xs) =>
      (match b with
      | (Value.SetV _ ys) =>
        (match (O.subset P xs ys) with
        | Result.Ok sub =>
          (if _h : sub = true then
            (O.subset P ys xs)
          else
            (Result.Ok false))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | _ =>
        (Result.Ok false))
    | (Value.BagV _ xs) =>
      (match b with
      | (Value.BagV _ ys) =>
        (match (O.sub_bag P xs ys) with
        | Result.Ok sub =>
          (if _h : sub = true then
            (O.sub_bag P ys xs)
          else
            (Result.Ok false))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | _ =>
        (Result.Ok false))
    | (Value.MapV _ _ xs d) =>
      (match b with
      | (Value.MapV _ _ ys e) =>
        (match (O.value_eq P d e) with
        | Result.Ok same =>
          (if _h : same = true then
            (match (O.same_entries P xs xs d ys e) with
            | Result.Ok l =>
              (if _h : l = true then
                (O.same_entries P ys xs d ys e)
              else
                (Result.Ok false))
            | Result.Stuck => Result.Stuck
            | Result.OutOfFuel => Result.OutOfFuel)
          else
            (Result.Ok false))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | _ =>
        (Result.Ok false))
    | (Value.ADTV c tps xs) =>
      (match b with
      | (Value.ADTV d _ ys) =>
        (match (sort_equality P c) with
        | (Option.some f) =>
          (O.adt_equal P f tps a b)
        | Option.none =>
          (if _h : c = d then
            (O.values_eq P xs ys)
          else
            (Result.Ok false)))
      | _ =>
        (Result.Ok false))
    )
  adt_equal : ∀ (P : Program) (f : Id) (tps : List Ty) (a : Value) (b : Value), O.adt_equal P f tps a b = (
    (if _h : (decide (∃ (fuel : Int), (decide ((call O P fuel f tps List.nil (List.cons a (List.cons b List.nil))) = (Result.Ok (Value.BoolV true)))) = true)) = true then
      (Result.Ok true)
    else
      (if _h : (decide (∃ (fuel : Int), (decide ((call O P fuel f tps List.nil (List.cons a (List.cons b List.nil))) = (Result.Ok (Value.BoolV false)))) = true)) = true then
        (Result.Ok false)
      else
        Result.Stuck))
    )
  values_eq : ∀ (P : Program) (xs : List Value) (ys : List Value), O.values_eq P xs ys = (
    (match xs with
    | List.nil =>
      (match ys with
      | List.nil =>
        (Result.Ok true)
      | _ =>
        (Result.Ok false))
    | (List.cons x xr) =>
      (match ys with
      | List.nil =>
        (Result.Ok false)
      | (List.cons y yr) =>
        (match (O.value_eq P x y) with
        | Result.Ok same =>
          (if _h : same = true then
            (O.values_eq P xr yr)
          else
            (Result.Ok false))
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)))
    )
  set_contains : ∀ (P : Program) (xs : List Value) (v : Value), O.set_contains P xs v = (
    (match xs with
    | List.nil =>
      (Result.Ok false)
    | (List.cons x rest) =>
      (match (O.value_eq P x v) with
      | Result.Ok same =>
        (if _h : same = true then
          (Result.Ok true)
        else
          (O.set_contains P rest v))
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel))
    )
  subset : ∀ (P : Program) (xs : List Value) (ys : List Value), O.subset P xs ys = (
    (match xs with
    | List.nil =>
      (Result.Ok true)
    | (List.cons x rest) =>
      (match (O.set_contains P ys x) with
      | Result.Ok in_ =>
        (if _h : in_ = true then
          (O.subset P rest ys)
        else
          (Result.Ok false))
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel))
    )
  bag_get : ∀ (P : Program) (xs : List BagEntry) (v : Value), O.bag_get P xs v = (
    (match xs with
    | List.nil =>
      (Result.Ok (0 : Int))
    | (List.cons (BagEntry.BagEntry x n) rest) =>
      (match (O.value_eq P x v) with
      | Result.Ok same =>
        (if _h : same = true then
          (Result.Ok n)
        else
          (O.bag_get P rest v))
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel))
    )
  sub_bag : ∀ (P : Program) (xs : List BagEntry) (ys : List BagEntry), O.sub_bag P xs ys = (
    (match xs with
    | List.nil =>
      (Result.Ok true)
    | (List.cons (BagEntry.BagEntry x n) rest) =>
      (match (O.bag_get P ys x) with
      | Result.Ok m =>
        (if _h : n = m then
          (O.sub_bag P rest ys)
        else
          (Result.Ok false))
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel))
    )
  map_get : ∀ (P : Program) (xs : List MapEntry) (k : Value) (d : Value), O.map_get P xs k d = (
    (match xs with
    | List.nil =>
      (Result.Ok d)
    | (List.cons (MapEntry.MapEntry x v) rest) =>
      (match (O.value_eq P x k) with
      | Result.Ok same =>
        (if _h : same = true then
          (Result.Ok v)
        else
          (O.map_get P rest k d))
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel))
    )
  same_entries : ∀ (P : Program) (ks : List MapEntry) (xs : List MapEntry) (d : Value) (ys : List MapEntry) (e : Value), O.same_entries P ks xs d ys e = (
    (match ks with
    | List.nil =>
      (Result.Ok true)
    | (List.cons (MapEntry.MapEntry k _) rest) =>
      (match (O.map_get P xs k d) with
      | Result.Ok a =>
        (match (O.map_get P ys k e) with
        | Result.Ok b =>
          (match (O.value_eq P a b) with
          | Result.Ok same =>
            (if _h : same = true then
              (O.same_entries P rest xs d ys e)
            else
              (Result.Ok false))
          | Result.Stuck => Result.Stuck
          | Result.OutOfFuel => Result.OutOfFuel)
        | Result.Stuck => Result.Stuck
        | Result.OutOfFuel => Result.OutOfFuel)
      | Result.Stuck => Result.Stuck
      | Result.OutOfFuel => Result.OutOfFuel))
    )
  resolve : ∀ (tenv : List TypeBinding) (t : Ty), O.resolve tenv t = (
    (match t with
    | (Ty.TypeParameter x) =>
      (match (lookup_type tenv x) with
      | (Option.some (TypeBinding.TypeBinding _ u uenv)) =>
        (O.resolve uenv u)
      | Option.none =>
        t)
    | (Ty.TupleType ts) =>
      (Ty.TupleType (O.resolve_all tenv ts))
    | (Ty.SetType u) =>
      (Ty.SetType (O.resolve tenv u))
    | (Ty.BagType u) =>
      (Ty.BagType (O.resolve tenv u))
    | (Ty.MapType u w) =>
      (Ty.MapType (O.resolve tenv u) (O.resolve tenv w))
    | (Ty.FunctionType ts u) =>
      (Ty.FunctionType (O.resolve_all tenv ts) (O.resolve tenv u))
    | (Ty.ADTType s ts) =>
      (Ty.ADTType s (O.resolve_all tenv ts))
    | (Ty.RefinementType x u prop) =>
      (Ty.RefinementType x (O.resolve tenv u) prop)
    | (Ty.PiType ps u) =>
      (Ty.PiType (O.resolve_params tenv ps) (O.resolve tenv u))
    | (Ty.SigmaType ps u) =>
      (Ty.SigmaType (O.resolve_params tenv ps) (O.resolve tenv u))
    | _ =>
      t)
    )
  resolve_params : ∀ (tenv : List TypeBinding) (ps : List Param), O.resolve_params tenv ps = (
    (match ps with
    | List.nil =>
      List.nil
    | (List.cons (Param.Param x t) rest) =>
      (List.cons (Param.Param x (O.resolve tenv t)) (O.resolve_params tenv rest)))
    )
  resolve_all : ∀ (tenv : List TypeBinding) (ts : List Ty), O.resolve_all tenv ts = (
    (match ts with
    | List.nil =>
      List.nil
    | (List.cons t rest) =>
      (List.cons (O.resolve tenv t) (O.resolve_all tenv rest)))
    )
  has_type : ∀ (P : Program) (env : Env) (v : Value) (t : Ty), O.has_type P env v t = (
    match t with
    | Ty.IntegerType =>
      (match v with
      | (Value.IntV _) =>
        true
      | _ =>
        false)
    | Ty.BooleanType =>
      (match v with
      | (Value.BoolV _) =>
        true
      | _ =>
        false)
    | Ty.UnitType =>
      (match v with
      | Value.UnitV =>
        true
      | _ =>
        false)
    | Ty.CharType =>
      (match v with
      | (Value.CharV c) =>
        ((decide ((0 : Int) ≤ c)) && (decide (c < (65536 : Int))))
      | _ =>
        false)
    | Ty.RealType =>
      (match v with
      | (Value.RealV n d) =>
        ((decide ((0 : Int) < d)) && (decide ((gcd (abs n) d) = (1 : Int))))
      | _ =>
        false)
    | Ty.StringType =>
      (match v with
      | (Value.StringV cs) =>
        (valid_chars cs)
      | _ =>
        false)
    | (Ty.BVType s w) =>
      (match v with
      | (Value.BVV s2 w2 x) =>
        (((decide (s = s2)) && (decide (w = w2))) && ((decide ((0 : Int) ≤ x)) && (decide (x < (pow2 w)))))
      | _ =>
        false)
    | (Ty.FPType e s) =>
      (match v with
      | (Value.FPV e2 s2 x) =>
        (((decide (e = e2)) && (decide (s = s2))) && (((decide ((0 : Int) ≤ x)) && (decide (x < (pow2 (e + s))))) && (decide (x = (fp_canonical e s x)))))
      | _ =>
        false)
    | Ty.RoundingModeType =>
      (match v with
      | (Value.RoundingModeV _) =>
        true
      | _ =>
        false)
    | (Ty.TypeParameter x) =>
      (match (lookup_type (env_types env) x) with
      | (Option.some (TypeBinding.TypeBinding _ u uenv)) =>
        (O.has_type P (Env.Env uenv List.nil) v u)
      | Option.none =>
        (match v with
        | (Value.IntV _) =>
          true
        | _ =>
          false))
    | (Ty.TupleType ts) =>
      (match v with
      | (Value.TupleV vs) =>
        (O.have_types P env vs ts)
      | _ =>
        false)
    | (Ty.SetType u) =>
      (match v with
      | (Value.SetV _ xs) =>
        ((O.all_have_type P env xs u) && (distinct_values O P xs))
      | _ =>
        false)
    | (Ty.BagType u) =>
      (match v with
      | (Value.BagV _ xs) =>
        ((O.bag_has_type P env xs u) && (distinct_values O P (bag_elems xs)))
      | _ =>
        false)
    | (Ty.MapType u w) =>
      (match v with
      | (Value.MapV _ _ xs d) =>
        ((O.has_type P env d w) && ((O.map_has_type P env xs u w) && (distinct_values O P (map_keys xs))))
      | _ =>
        false)
    | (Ty.FunctionType from_ to) =>
      (match v with
      | (Value.ClosureV params _ _) =>
        ((same_arity params from_) && (O.function_has_type P env v from_ to))
      | _ =>
        false)
    | (Ty.ADTType s args) =>
      (match v with
      | (Value.ADTV c tps vs) =>
        (match P with
        | (Program.Program _ cs ss _ _) =>
          (match (lookup_ctor cs c) with
          | (Result.Ok (Constructor.Constructor _ s2 fields)) =>
            (match (lookup_sort ss s) with
            | (Result.Ok (ADTSort.Sort _ tparams inv _)) =>
              (((decide (s = s2)) && (decide (tps = (O.resolve_all (env_types env) args)))) && ((O.params_have_types P (Env.Env (bind_types tparams args (env_types env)) List.nil) vs fields) && (match inv with
              | Option.none =>
                true
              | (Option.some f) =>
                (O.invariant_holds P f args (env_types env) v))))
            | _ =>
              false)
          | _ =>
            false))
      | _ =>
        false)
    | (Ty.RefinementType x u prop) =>
      ((O.has_type P env v u) && (O.holds P (env_bind env x v) prop))
    | Ty.PropType =>
      (match v with
      | (Value.BoolV _) =>
        true
      | _ =>
        false)
    | (Ty.PiType ps to) =>
      (match v with
      | (Value.ClosureV params _ _) =>
        ((same_arity params (param_types ps)) && (O.pi_has_type P env v ps to))
      | _ =>
        false)
    | (Ty.SigmaType ps to) =>
      (match v with
      | (Value.TupleV vs) =>
        (O.sigma_has_type P env vs ps to)
      | _ =>
        false)
    )
  holds : ∀ (P : Program) (env : Env) (prop : Expr), O.holds P env prop = (
    (decide (∃ (fuel : Int), (decide ((eval O P fuel env prop) = (Result.Ok (Value.BoolV true)))) = true))
    )
  invariant_holds : ∀ (P : Program) (f : Id) (args : List Ty) (tenv : List TypeBinding) (v : Value), O.invariant_holds P f args tenv v = (
    (decide (∃ (fuel : Int), (decide ((call O P fuel f args tenv (List.cons v List.nil)) = (Result.Ok (Value.BoolV true)))) = true))
    )
  function_has_type : ∀ (P : Program) (env : Env) (f : Value) (from_ : List Ty) (to : Ty), O.function_has_type P env f from_ to = (
    (decide (∀ (vs : List Value), ((!(O.have_types P env vs from_)) || (decide (∃ (fuel : Int) (r : Value), ((decide ((apply O P fuel f vs) = (Result.Ok r))) && (O.has_type P env r to)) = true))) = true))
    )
  pi_has_type : ∀ (P : Program) (env : Env) (f : Value) (ps : List Param) (to : Ty), O.pi_has_type P env f ps to = (
    (decide (∀ (vs : List Value), ((!(O.params_have_types P env vs ps)) || (decide (∃ (fuel : Int) (r : Value) (bs : List Binding), (((decide ((bind_all (param_ids ps) vs) = (Result.Ok bs))) && (decide ((apply O P fuel f vs) = (Result.Ok r)))) && (O.has_type P (Env.Env (env_types env) (append_env bs (env_vars env))) r to)) = true))) = true))
    )
  sigma_has_type : ∀ (P : Program) (env : Env) (vs : List Value) (ps : List Param) (to : Ty), O.sigma_has_type P env vs ps to = (
    (match ps with
    | List.nil =>
      (match vs with
      | (List.cons v List.nil) =>
        (O.has_type P env v to)
      | _ =>
        false)
    | (List.cons (Param.Param x t) more) =>
      (match vs with
      | (List.cons v rest) =>
        ((O.has_type P env v t) && (O.sigma_has_type P (env_bind env x v) rest more to))
      | _ =>
        false))
    )
  have_types : ∀ (P : Program) (env : Env) (vs : List Value) (ts : List Ty), O.have_types P env vs ts = (
    (match vs with
    | List.nil =>
      (match ts with
      | List.nil =>
        true
      | _ =>
        false)
    | (List.cons v rest) =>
      (match ts with
      | List.nil =>
        false
      | (List.cons t more) =>
        ((O.has_type P env v t) && (O.have_types P env rest more))))
    )
  params_have_types : ∀ (P : Program) (env : Env) (vs : List Value) (ps : List Param), O.params_have_types P env vs ps = (
    (match vs with
    | List.nil =>
      (match ps with
      | List.nil =>
        true
      | _ =>
        false)
    | (List.cons v rest) =>
      (match ps with
      | List.nil =>
        false
      | (List.cons (Param.Param x t) more) =>
        ((O.has_type P env v t) && (O.params_have_types P (env_bind env x v) rest more))))
    )
  all_have_type : ∀ (P : Program) (env : Env) (vs : List Value) (t : Ty), O.all_have_type P env vs t = (
    (match vs with
    | List.nil =>
      true
    | (List.cons v rest) =>
      ((O.has_type P env v t) && (O.all_have_type P env rest t)))
    )
  bag_has_type : ∀ (P : Program) (env : Env) (xs : List BagEntry) (t : Ty), O.bag_has_type P env xs t = (
    (match xs with
    | List.nil =>
      true
    | (List.cons (BagEntry.BagEntry x n) rest) =>
      (((decide ((0 : Int) < n)) && (O.has_type P env x t)) && (O.bag_has_type P env rest t)))
    )
  map_has_type : ∀ (P : Program) (env : Env) (xs : List MapEntry) (t : Ty) (u : Ty), O.map_has_type P env xs t u = (
    (match xs with
    | List.nil =>
      true
    | (List.cons (MapEntry.MapEntry k v) rest) =>
      (((O.has_type P env k t) && (O.has_type P env v u)) && (O.map_has_type P env rest t u)))
    )
  forall_result : ∀ (P : Program) (fuel : Int) (env : Env) (params : List Param) (body : Expr), O.forall_result P fuel env params body = (
    (if _h : (decide (∃ (vs : List Value), ((O.params_have_types P env vs params) && (decide ((instance_ O P fuel env params vs body) = (Result.Ok (Value.BoolV false))))) = true)) = true then
      (Result.Ok (Value.BoolV false))
    else
      (if _h : (decide (∃ (vs : List Value), ((O.params_have_types P env vs params) && (decide ((instance_ O P fuel env params vs body) = Result.OutOfFuel))) = true)) = true then
        Result.OutOfFuel
      else
        (if _h : (decide (∀ (vs : List Value), ((!(O.params_have_types P env vs params)) || (decide ((instance_ O P fuel env params vs body) = (Result.Ok (Value.BoolV true))))) = true)) = true then
          (Result.Ok (Value.BoolV true))
        else
          Result.Stuck)))
    )
  closures_equal : ∀ (P : Program) (f : Value) (g : Value), O.closures_equal P f g = (
    (match f with
    | (Value.ClosureV params _ cenv) =>
      (decide (∀ (vs : List Value), ((!(O.params_have_types P cenv vs params)) || ((decide (∀ (fuel : Int) (a : Value), ((!(decide ((apply O P fuel f vs) = (Result.Ok a)))) && (!(decide ((apply O P fuel g vs) = (Result.Ok a))))) = true)) || (decide (∃ (fuel : Int) (a : Value) (b : Value), (((decide ((apply O P fuel f vs) = (Result.Ok a))) && (decide ((apply O P fuel g vs) = (Result.Ok b)))) && (decide ((O.value_eq P a b) = (Result.Ok true)))) = true)))) = true))
    | _ =>
      false)
    )

end

end Inox.Semantics
