/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Bags
import Inox.Typing

/-!
# What the encoder of bags makes of a program

`Inox/Bags.lean` is about the datatype of the encoder. This module is about programs: the
values of the input relate to those of the encoded program by their kinds (`Rel`), an
expression relates to what the encoder makes of it (`Encodes`), and where an expression of the
input evaluates to a value, its encoded expression evaluates, with enough fuel, to a value
that relates to it (`encodes_eval`), in an encoded program whose functions are what the encoder
makes of those of the input (`Progs`).
-/

namespace Inox.Encoded

open Inox.Semantics Inox.Bags Inox.Typing

/-- The kinds of values: elements of bags, which are the same in both programs, integers,
booleans, bags of elements, values of a sort of the program, tuples and functions, from the
kinds of their arguments to the kind of their result. -/
inductive Kind where
  | elem
  | int
  | bool
  | bag
  | adt (s : Id)
  | tuple (ks : List Kind)
  | fn (ks : List Kind) (k : Kind)

mutual
/-- Whether two kinds are the same. -/
def kindEq : Kind → Kind → Bool
  | .elem, .elem => true
  | .int, .int => true
  | .bool, .bool => true
  | .bag, .bag => true
  | .adt s, .adt t => s == t
  | .tuple ks, .tuple ls => kindsEq ks ls
  | .fn ks k, .fn ls l => kindsEq ks ls && kindEq k l
  | _, _ => false
def kindsEq : List Kind → List Kind → Bool
  | [], [] => true
  | k :: ks, l :: ls => kindEq k l && kindsEq ks ls
  | _, _ => false
end

mutual
theorem kindEq_eq : ∀ {a b : Kind}, kindEq a b = true → a = b
  | .elem, .elem, _ => rfl
  | .int, .int, _ => rfl
  | .bool, .bool, _ => rfl
  | .bag, .bag, _ => rfl
  | .adt s, .adt t, h => by simp only [kindEq, beq_iff_eq] at h; rw [h]
  | .tuple ks, .tuple ls, h => by simp only [kindEq] at h; rw [kindsEq_eq h]
  | .fn ks k, .fn ls l, h => by
    simp only [kindEq, Bool.and_eq_true] at h
    rw [kindsEq_eq h.1, kindEq_eq h.2]
  | .elem, .fn _ _, h | .int, .fn _ _, h | .bool, .fn _ _, h | .bag, .fn _ _, h
  | .adt _, .fn _ _, h | .tuple _, .fn _ _, h
  | .fn _ _, .elem, h | .fn _ _, .int, h | .fn _ _, .bool, h | .fn _ _, .bag, h
  | .fn _ _, .adt _, h | .fn _ _, .tuple _, h
  | .elem, .int, h | .elem, .bool, h | .elem, .bag, h | .elem, .adt _, h | .elem, .tuple _, h
  | .int, .elem, h | .int, .bool, h | .int, .bag, h | .int, .adt _, h | .int, .tuple _, h
  | .bool, .elem, h | .bool, .int, h | .bool, .bag, h | .bool, .adt _, h | .bool, .tuple _, h
  | .bag, .elem, h | .bag, .int, h | .bag, .bool, h | .bag, .adt _, h | .bag, .tuple _, h
  | .adt _, .elem, h | .adt _, .int, h | .adt _, .bool, h | .adt _, .bag, h
  | .adt _, .tuple _, h
  | .tuple _, .elem, h | .tuple _, .int, h | .tuple _, .bool, h | .tuple _, .bag, h
  | .tuple _, .adt _, h => by simp [kindEq] at h
theorem kindsEq_eq : ∀ {a b : List Kind}, kindsEq a b = true → a = b
  | [], [], _ => rfl
  | k :: ks, l :: ls, h => by
    simp only [kindsEq, Bool.and_eq_true] at h
    rw [kindEq_eq h.1, kindsEq_eq h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [kindsEq] at h
end

/-- The signature of a program: the sort of each constructor with the names and the kinds of
its fields, and the type parameters of each function, the type of elements in its body, the
kinds of its parameters and the kind of its result, the sorts whose values are typed alike in
both programs, and the kind of the type parameters of sorts. -/
structure Sig where
  ctors : Id → Option (Id × List (Id × Kind))
  funs : Id → Option (List Id × Ty × List Kind × Kind)
  unint : Id → Option (List Kind × Kind)
  flat : Id → Bool
  sorts : Sorts
  elemKind : Kind

mutual
/-- Whether a kind has no functions in it, given the sorts `A` that have none. -/
def foKind (A : Id → Bool) : Kind → Bool
  | .fn _ _ => false
  | .tuple ks => foKinds A ks
  | .adt s => A s
  | _ => true
def foKinds (A : Id → Bool) : List Kind → Bool
  | [] => true
  | k :: ks => foKind A k && foKinds A ks
end

/-- The sorts `A` have no functions in them: no constructor of theirs has a function in its
fields. -/
def Sig.fo (S : Sig) (A : Id → Bool) : Prop :=
  ∀ c s fs, S.ctors c = some (s, fs) → A s = true → foKinds A (fs.map Prod.snd) = true

/-- The kind of the component `i` of a tuple, counted from 1. -/
def nthKind : List Kind → Int → Option Kind
  | [], _ => none
  | k :: ks, i => if i = 1 then some k else nthKind ks (i - 1)

/-- The kind of the field `sel` of a constructor. -/
def fieldKind : List (Id × Kind) → Id → Option Kind
  | [], _ => none
  | (f, k) :: fs, sel => if f = sel then some k else fieldKind fs sel

/-- The kind of the values of a type of `PureTy`, with `κ` that of the type parameters of
sorts. -/
def pureKind (κ : Kind) : Ty → Kind
  | .IntegerType => .int
  | .BooleanType => .bool
  | .ADTType s _ => .adt s
  | .RefinementType _ t _ => pureKind κ t
  | _ => κ

/-- The arguments of sorts are of the kind of their type parameters. -/
def Sig.ok (S : Sig) (t : Ty) : Prop := pureKind S.elemKind t = S.elemKind

def paramId : Param → Id
  | .Param x _ => x

/-- The sorts of the signature are well formed, and their constructors have fields of the
kinds of their types. -/
def Sig.Ok (S : Sig) : Prop :=
  SortsWF S.sorts S.ok ∧ ∀ s tps ctors, S.sorts s = some (tps, ctors) → ∀ c ps,
    (c, ps) ∈ ctors → S.ctors c = some (s, ps.map fun p => (paramId p, pureKind S.elemKind
      (paramTy p)))

/-- A parameter of a quantifier, of the type of elements `Te` or of a type of `PureTy`. -/
inductive ParamKind (S : Sig) (Te : Ty) : Ty → Kind → Prop where
  | elem {a : Id} (h : Te = .TypeParameter a) : ParamKind S Te (.TypeParameter a) .elem
  | pure {t : Ty} (h : PureTy S.sorts S.ok [] t) : ParamKind S Te t (pureKind S.elemKind t)

/-- Types that have values in any program: integers, booleans, elements and functions to
these. -/
inductive Inhab (Te : Ty) : Ty → Prop where
  | int : Inhab Te .IntegerType
  | bool : Inhab Te .BooleanType
  | elem {a : Id} (h : Te = .TypeParameter a) : Inhab Te (.TypeParameter a)
  | fn {ts : List Ty} {t : Ty} (h : t = .IntegerType ∨ t = .BooleanType ∨ t = Te) :
      Inhab Te (.FunctionType ts t)

inductive ParamsOk (S : Sig) (Te : Ty) : List Param → List Kind → Prop where
  | nil : ParamsOk S Te [] []
  | cons {x : Id} {t : Ty} {ps : List Param} {k : Kind} {ks : List Kind}
      (hk : ParamKind S Te t k) (hr : ParamsOk S Te ps ks) :
      ParamsOk S Te (.Param x t :: ps) (k :: ks)

/-- The types whose values do not depend on the program nor on the environment. -/
def SimpleTy : Ty → Prop
  | .IntegerType | .BooleanType | .TypeParameter _ => True
  | _ => False

/-- `e'` is what the encoder makes of `e`, an expression of the kind `k`, with `Te` the type
of the elements and `Γ` the kinds of the variables. A function keeps the kinds `Γ0` of the
variables of its body other than its parameters. The encoding is flat (`u`) when it has no
operations of bags, which need more fuel in the encoded program, and the body of a function
or of a quantifier is flat. -/
inductive Encodes (N : Names) (S : Sig) (Te : Ty) :
    (Id → Option Kind) → Expr → Expr → Kind → Bool → Prop where
  | var {Γ : Id → Option Kind} {u : Bool} (x : Id) (k : Kind) (h : Γ x = some k) :
      Encodes N S Te Γ (.Variable x) (.Variable x) k u
  | int {Γ : Id → Option Kind} {u : Bool} (n : Int) :
      Encodes N S Te Γ (.IntegerLiteral n) (.IntegerLiteral n) .int u
  | bool {Γ : Id → Option Kind} {u : Bool} (b : Bool) :
      Encodes N S Te Γ (.BooleanLiteral b) (.BooleanLiteral b) .bool u
  | plus {Γ : Id → Option Kind} {u : Bool} {a a' b b' : Expr}
      (ha : Encodes N S Te Γ a a' .int u) (hb : Encodes N S Te Γ b b' .int u) :
      Encodes N S Te Γ (.Plus a b) (.Plus a' b') .int u
  | minus {Γ : Id → Option Kind} {u : Bool} {a a' b b' : Expr}
      (ha : Encodes N S Te Γ a a' .int u) (hb : Encodes N S Te Γ b b' .int u) :
      Encodes N S Te Γ (.Minus a b) (.Minus a' b') .int u
  | lt {Γ : Id → Option Kind} {u : Bool} {a a' b b' : Expr}
      (ha : Encodes N S Te Γ a a' .int u) (hb : Encodes N S Te Γ b b' .int u) :
      Encodes N S Te Γ (.LessThan a b) (.LessThan a' b') .bool u
  | gt {Γ : Id → Option Kind} {u : Bool} {a a' b b' : Expr}
      (ha : Encodes N S Te Γ a a' .int u) (hb : Encodes N S Te Γ b b' .int u) :
      Encodes N S Te Γ (.GreaterThan a b) (.GreaterThan a' b') .bool u
  | le {Γ : Id → Option Kind} {u : Bool} {a a' b b' : Expr}
      (ha : Encodes N S Te Γ a a' .int u) (hb : Encodes N S Te Γ b b' .int u) :
      Encodes N S Te Γ (.LessEquals a b) (.LessEquals a' b') .bool u
  | ge {Γ : Id → Option Kind} {u : Bool} {a a' b b' : Expr}
      (ha : Encodes N S Te Γ a a' .int u) (hb : Encodes N S Te Γ b b' .int u) :
      Encodes N S Te Γ (.GreaterEquals a b) (.GreaterEquals a' b') .bool u
  | eq {Γ : Id → Option Kind} {u : Bool} {a a' b b' : Expr} {k : Kind} {A : Id → Bool}
      (hk : foKind A k = true) (hS : S.fo A) (ha : Encodes N S Te Γ a a' k u)
      (hb : Encodes N S Te Γ b b' k u) :
      Encodes N S Te Γ (.Equals a b) (.Equals a' b') .bool u
  | not {Γ : Id → Option Kind} {u : Bool} {a a' : Expr} (ha : Encodes N S Te Γ a a' .bool u) :
      Encodes N S Te Γ (.Not a) (.Not a') .bool u
  | andNil {Γ : Id → Option Kind} {u : Bool} : Encodes N S Te Γ (.And []) (.And []) .bool u
  | andCons {Γ : Id → Option Kind} {u : Bool} {a a' : Expr} {as as' : List Expr}
      (ha : Encodes N S Te Γ a a' .bool u) (hr : Encodes N S Te Γ (.And as) (.And as') .bool u) :
      Encodes N S Te Γ (.And (a :: as)) (.And (a' :: as')) .bool u
  | orNil {Γ : Id → Option Kind} {u : Bool} : Encodes N S Te Γ (.Or []) (.Or []) .bool u
  | orCons {Γ : Id → Option Kind} {u : Bool} {a a' : Expr} {as as' : List Expr}
      (ha : Encodes N S Te Γ a a' .bool u) (hr : Encodes N S Te Γ (.Or as) (.Or as') .bool u) :
      Encodes N S Te Γ (.Or (a :: as)) (.Or (a' :: as')) .bool u
  | implies {Γ : Id → Option Kind} {u : Bool} {a a' b b' : Expr}
      (ha : Encodes N S Te Γ a a' .bool u) (hb : Encodes N S Te Γ b b' .bool u) :
      Encodes N S Te Γ (.Implies a b) (.Implies a' b') .bool u
  | ite {Γ : Id → Option Kind} {u : Bool} {c c' a a' b b' : Expr} {k : Kind}
      (hc : Encodes N S Te Γ c c' .bool u) (ha : Encodes N S Te Γ a a' k u)
      (hb : Encodes N S Te Γ b b' k u) : Encodes N S Te Γ (.IfExpr c a b) (.IfExpr c' a' b') k u
  | let_ {Γ : Id → Option Kind} {u : Bool} (x : Id) {a a' b b' : Expr} {kx k : Kind}
      (ha : Encodes N S Te Γ a a' kx u)
      (hb : Encodes N S Te (fun y => if y = x then some kx else Γ y) b b' k u) :
      Encodes N S Te Γ (.Let x a b) (.Let x a' b') k u
  | assume {Γ : Id → Option Kind} {u : Bool} {p p' b b' : Expr} {k : Kind}
      (hp : Encodes N S Te Γ p p' .bool u) (hb : Encodes N S Te Γ b b' k u) :
      Encodes N S Te Γ (.Assume p b) (.Assume p' b') k u
  | empty {Γ : Id → Option Kind} (base : Ty) :
      Encodes N S Te Γ (.FiniteBag [] base) (.ADT N.leaf [Te] []) .bag false
  | add {Γ : Id → Option Kind} {b b' e e' : Expr} (hb : Encodes N S Te Γ b b' .bag false)
      (he : Encodes N S Te Γ e e' .elem false) :
      Encodes N S Te Γ (.BagAdd b e)
        (.ADT N.node [Te] [.IntegerLiteral 0, b', .ADT N.elem [Te] [e', .IntegerLiteral 1]])
        .bag false
  | union {Γ : Id → Option Kind} {a a' b b' : Expr} (ha : Encodes N S Te Γ a a' .bag false)
      (hb : Encodes N S Te Γ b b' .bag false) :
      Encodes N S Te Γ (.BagUnion a b) (.ADT N.node [Te] [.IntegerLiteral 0, a', b']) .bag false
  | difference {Γ : Id → Option Kind} {a a' b b' : Expr} (ha : Encodes N S Te Γ a a' .bag false)
      (hb : Encodes N S Te Γ b b' .bag false) :
      Encodes N S Te Γ (.BagDifference a b) (.ADT N.node [Te] [.IntegerLiteral 1, a', b'])
        .bag false
  | intersection {Γ : Id → Option Kind} {a a' b b' : Expr}
      (ha : Encodes N S Te Γ a a' .bag false) (hb : Encodes N S Te Γ b b' .bag false) :
      Encodes N S Te Γ (.BagIntersection a b)
        (.ADT N.node [Te] [.IntegerLiteral 2, a', b']) .bag false
  | mult {Γ : Id → Option Kind} {e e' b b' : Expr} (he : Encodes N S Te Γ e e' .elem false)
      (hb : Encodes N S Te Γ b b' .bag false) :
      Encodes N S Te Γ (.MultiplicityInBag e b) (.FunctionInvocation N.get [Te] [b', e'])
        .int false
  | tupleNil {Γ : Id → Option Kind} {u : Bool} :
      Encodes N S Te Γ (.Tuple []) (.Tuple []) (.tuple []) u
  | tupleCons {Γ : Id → Option Kind} {u : Bool} {e e' : Expr} {es es' : List Expr} {k : Kind}
      {ks : List Kind} (he : Encodes N S Te Γ e e' k u)
      (hr : Encodes N S Te Γ (.Tuple es) (.Tuple es') (.tuple ks) u) :
      Encodes N S Te Γ (.Tuple (e :: es)) (.Tuple (e' :: es')) (.tuple (k :: ks)) u
  | tupleSelect {Γ : Id → Option Kind} {u : Bool} {t t' : Expr} {ks : List Kind} {k : Kind}
      (i : Int) (ht : Encodes N S Te Γ t t' (.tuple ks) u) (hk : nthKind ks i = some k) :
      Encodes N S Te Γ (.TupleSelect t i) (.TupleSelect t' i) k u
  | adt {Γ : Id → Option Kind} {u : Bool} {c s : Id} {fs : List (Id × Kind)}
      (tps tps' : List Ty) {es es' : List Expr} (hc : S.ctors c = some (s, fs))
      (ha : Encodes N S Te Γ (.Tuple es) (.Tuple es') (.tuple (fs.map Prod.snd)) u) :
      Encodes N S Te Γ (.ADT c tps es) (.ADT c tps' es') (.adt s) u
  | sel {Γ : Id → Option Kind} {u : Bool} {e e' : Expr} {s : Id} (sel : Id) {k : Kind}
      (he : Encodes N S Te Γ e e' (.adt s) u)
      (hk : ∀ c fs, S.ctors c = some (s, fs) → ∀ k', fieldKind fs sel = some k' → k' = k) :
      Encodes N S Te Γ (.ADTSelector e sel) (.ADTSelector e' sel) k u
  | isCtor {Γ : Id → Option Kind} {u : Bool} {e e' : Expr} {s : Id} (c : Id)
      (he : Encodes N S Te Γ e e' (.adt s) u) :
      Encodes N S Te Γ (.IsConstructor e c) (.IsConstructor e' c) .bool u
  | callPoly {Γ : Id → Option Kind} {u : Bool} {f A : Id} {ks : List Kind} {k : Kind}
      {es es' : List Expr} (hf : S.funs f = some ([A], .TypeParameter A, ks, k))
      (hu : u = true → S.flat f = true)
      (ha : Encodes N S Te Γ (.Tuple es) (.Tuple es') (.tuple ks) u) :
      Encodes N S Te Γ (.FunctionInvocation f [Te] es) (.FunctionInvocation f [Te] es') k u
  | callMono {Γ : Id → Option Kind} {u : Bool} {f : Id} {Tf : Ty} {ks : List Kind} {k : Kind}
      (tps : List Ty) {es es' : List Expr} (hf : S.funs f = some ([], Tf, ks, k))
      (hu : u = true → S.flat f = true)
      (ha : Encodes N S Te Γ (.Tuple es) (.Tuple es') (.tuple ks) u) :
      Encodes N S Te Γ (.FunctionInvocation f tps es) (.FunctionInvocation f [] es') k u
  | lambda {Γ : Id → Option Kind} {u : Bool} (Γ0 : List (Id × Kind)) {ps ps' : List Param}
      {body body' : Expr} {ks : List Kind} {k : Kind} (hΓ : ∀ p ∈ Γ0, Γ p.1 = some p.2)
      (hp : param_ids ps = param_ids ps')
      (hb : Encodes N S Te (fun x => ((param_ids ps).zip ks ++ Γ0).lookup x) body body' k true) :
      Encodes N S Te Γ (.Lambda ps body) (.Lambda ps' body') (.fn ks k) u
  | app {Γ : Id → Option Kind} {u : Bool} {f f' : Expr} {es es' : List Expr} {ks : List Kind}
      {k : Kind} (hf : Encodes N S Te Γ f f' (.fn ks k) u)
      (ha : Encodes N S Te Γ (.Tuple es) (.Tuple es') (.tuple ks) u) :
      Encodes N S Te Γ (.Application f es) (.Application f' es') k u
  | forall_ {Γ : Id → Option Kind} {u : Bool} {ps : List Param} {body body' : Expr}
      {ks : List Kind} (hk : ParamsOk S Te ps ks)
      (hb : Encodes N S Te (fun x => (((param_ids ps).zip ks).lookup x).or (Γ x)) body body'
        .bool true) :
      Encodes N S Te Γ (.Forall ps body) (.Forall ps body') .bool u
  | forallUnused {Γ : Id → Option Kind} {u : Bool} {ps : List Param} {body body' : Expr}
      (hps : ∀ p ∈ ps, Inhab Te (paramTy p))
      (hb : Encodes N S Te (fun x => if x ∈ param_ids ps then none else Γ x) body body'
        .bool true) :
      Encodes N S Te Γ (.Forall ps body) (.Forall ps body') .bool u
  | uninterp {Γ : Id → Option Kind} {u : Bool} {f : Id} {ks : List Kind} {k : Kind}
      {es es' : List Expr} (hf : S.unint f = some (ks, k)) (hu : u = true → S.flat f = true)
      (ha : Encodes N S Te Γ (.Tuple es) (.Tuple es') (.tuple ks) u) :
      Encodes N S Te Γ (.UninterpretedCall f [] es) (.UninterpretedCall f [] es') k u
  | error {Γ : Id → Option Kind} {u : Bool} (k : Kind) : Encodes N S Te Γ .Error .Error k u

/-- The value `v` of the input and the value `v'` of the encoded program are of the kind `k`
and the same, up to the bags in them, which `v'` has the encodings of. Functions are the same
when the body of one is what the encoder makes of the body of the other and the values of
their variables are the same in this sense. -/
inductive Rel (O : Oracle) (P : Program) (N : Names) (K : Value → Prop)
    (E : Value → Value → Bool) (T0 : Ty) (S : Sig) : Kind → Value → Value → Prop where
  | elem (v : Value) (h : K v) : Rel O P N K E T0 S .elem v v
  | int (n : Int) : Rel O P N K E T0 S .int (.IntV n) (.IntV n)
  | bool (b : Bool) : Rel O P N K E T0 S .bool (.BoolV b) (.BoolV b)
  | bag (t : Ty) (xs : List BagEntry) (c : Id) (args : List Value) (hxs : Canon E K xs)
      (henc : Enc O P N K E xs (.ADTV c [T0] args))
      (hc : c = N.node ∨ c = N.elem ∨ c = N.leaf) :
      Rel O P N K E T0 S .bag (.BagV t xs) (.ADTV c [T0] args)
  | tupleNil : Rel O P N K E T0 S (.tuple []) (.TupleV []) (.TupleV [])
  | tupleCons {k : Kind} {ks : List Kind} {v v' : Value} {vs vs' : List Value}
      (h : Rel O P N K E T0 S k v v')
      (hr : Rel O P N K E T0 S (.tuple ks) (.TupleV vs) (.TupleV vs')) :
      Rel O P N K E T0 S (.tuple (k :: ks)) (.TupleV (v :: vs)) (.TupleV (v' :: vs'))
  | adt {c s : Id} {fs : List (Id × Kind)} {tps tps' : List Ty} {vs vs' : List Value}
      (h : S.ctors c = some (s, fs))
      (hr : Rel O P N K E T0 S (.tuple (fs.map Prod.snd)) (.TupleV vs) (.TupleV vs')) :
      Rel O P N K E T0 S (.adt s) (.ADTV c tps vs) (.ADTV c tps' vs')
  | closure {Te : Ty} (Γ0 : List (Id × Kind)) {ps ps' : List Param} {body body' : Expr}
      {ks : List Kind} {k : Kind} {tys tys' : List TypeBinding} {vars vars' : List Binding}
      {vs vs' : List Value} (hp : param_ids ps = param_ids ps')
      (hT : O.resolve_all tys [Te] = [T0] ∧ O.resolve_all tys' [Te] = [T0])
      (hb : Encodes N S Te (fun x => ((param_ids ps).zip ks ++ Γ0).lookup x) body body' k true)
      (hr : Rel O P N K E T0 S (.tuple (Γ0.map Prod.snd)) (.TupleV vs) (.TupleV vs'))
      (hv : (Γ0.map Prod.fst).map (lookup_var vars) = vs.map Result.Ok)
      (hv' : (Γ0.map Prod.fst).map (lookup_var vars') = vs'.map Result.Ok) :
      Rel O P N K E T0 S (.fn ks k) (.ClosureV ps body (.Env tys vars))
        (.ClosureV ps' body' (.Env tys' vars'))

/-- The names of parameters. -/
def paramNames : List Param → List Id
  | [] => []
  | .Param x _ :: rest => x :: paramNames rest

/-- The program has the constructor `c` of the sort `s`, a sort without an invariant nor an
equality, with the fields `fs`. -/
def CtorIn (c s : Id) (fs : List (Id × Kind)) : Program → Prop
  | .Program _ cs ss _ _ => ∃ params tps, lookup_ctor cs c = .Ok (.Constructor c s params) ∧
      paramNames params = fs.map Prod.fst ∧ lookup_sort ss s = .Ok (.Sort s tps none none)

/-- The program has the function `f`. -/
def FunIn (f : Id) (tparams params : List Id) (body : Expr) : Program → Prop
  | .Program fs _ _ _ _ => lookup_fun fs f = .Ok (.FunDef f tparams params body)

/-- What the theorems assume of the program `Ps` of the input and of the encoded program `P`,
other than of their functions: `P` defines the datatype of the encoder as the encoder does,
both have the same equality on the elements and the constructors of the signature. -/
structure Base (O : Oracle) (Ps P : Program) (N : Names) (K : Value → Prop)
    (E : Value → Value → Bool) (T0 : Ty) (S : Sig) (inv bi eq b1 b2 : Id) : Prop where
  sound : O.Sound
  names : N.Distinct
  bags : HasBags N P
  sort : HasSort N inv bi eq P
  equals : HasEquals N eq b1 b2 P
  h1x : b1 ≠ N.x
  h2x : b2 ≠ N.x
  h12 : b1 ≠ b2
  keyS : KeyEq O Ps K E
  key : KeyEq O P K E
  elems : ∀ bs vs, O.params_have_types P (Env.Env (bind_types [N.T] [T0] []) bs) vs
    [.Param N.x (.TypeParameter N.T)] = true ↔ ∃ v, vs = [v] ∧ K v
  ctorS : ∀ c s fs, S.ctors c = some (s, fs) → CtorIn c s fs Ps
  ctor : ∀ c s fs, S.ctors c = some (s, fs) → CtorIn c s fs P
  simple : SimpleTy T0
  elemsS : ∀ v, O.has_type Ps (.Env [] []) v T0 = true ↔ K v
  sortsS : SortsIn S.sorts Ps
  sortsP : SortsIn S.sorts P

section Values
variable {O : Oracle} {Ps P : Program} {N : Names} {K : Value → Prop}
  {E : Value → Value → Bool}
  {T0 : Ty} {S : Sig} {inv bi eq b1 b2 : Id}

theorem sort_equality_ctor {c s : Id} {fs : List (Id × Kind)} {Q : Program}
    (h : CtorIn c s fs Q) : sort_equality Q c = none := by
  cases Q with
  | Program fns cs ss is eqs =>
  obtain ⟨params, tps, hc, _, hs⟩ := h
  simp [sort_equality, hc, hs]

/-- Values without functions in them that relate are equal in the input when they are in the
encoded program. -/
theorem rel_value_eq (hB : Base O Ps P N K E T0 S inv bi eq b1 b2) {A : Id → Bool}
    (hS : S.fo A) :
    ∀ {k : Kind} {a a' : Value}, Rel O P N K E T0 S k a a' → foKind A k = true →
      ∀ {b b' : Value}, Rel O P N K E T0 S k b b' →
        O.value_eq Ps a b = O.value_eq P a' b' := by
  intro k a a' h
  induction h with
  | closure _ _ _ _ _ _ _ => intro hk; simp [foKind] at hk
  | elem v hv =>
    intro hk b b' hb
    cases hb with
    | elem _ hw => rw [hB.keyS.eq _ _ hv hw, hB.key.eq _ _ hv hw]
  | int n =>
    intro hk b b' hb
    cases hb
    simp only [hB.sound.value_eq]
  | bool n =>
    intro hk b b' hb
    cases hb
    simp only [hB.sound.value_eq]
  | bag t xs c args hxs henc hc =>
    intro hk b b' hb
    cases hb with
    | bag u ys c2 args2 hys henc2 hc2 =>
      have heq := enc_equal hB.sound hB.names hB.bags hB.equals hB.h1x hB.h2x hB.h12 hB.key
        (hB.elems _) hxs hys henc henc2 t u
      rw [bag_value_eq hB.sound hB.key hxs hys] at heq
      rw [bag_value_eq hB.sound hB.keyS hxs hys, hB.sound.value_eq]
      simp only [sort_equality_bag hB.bags hB.sort hc, heq]
  | tupleNil =>
    intro hk b b' hb
    cases hb
    simp only [hB.sound.value_eq, hB.sound.values_eq]
  | tupleCons h hr ih ihr =>
    intro hk b b' hb
    cases hb with
    | tupleCons h2 hr2 =>
      simp only [foKind, foKinds, Bool.and_eq_true] at hk
      have e1 := ih hk.1 h2
      have e2 := ihr (by simpa [foKind] using hk.2) hr2
      rw [hB.sound.value_eq, hB.sound.value_eq (P := P)] at e2 ⊢
      simp only [] at e2 ⊢
      rw [hB.sound.values_eq, hB.sound.values_eq (P := P)]
      simp only [e1, e2]
  | @adt c s fs tps tps' vs vs' h hr ih =>
    intro hk b b' hb
    cases hb with
    | @adt d _ fs2 _ _ ws ws' h2 hr2 =>
      rw [hB.sound.value_eq, hB.sound.value_eq (P := P)]
      simp only [sort_equality_ctor (hB.ctorS _ _ _ h), sort_equality_ctor (hB.ctor _ _ _ h)]
      by_cases hcd : c = d
      · subst hcd
        have hfs := h.symm.trans h2
        simp only [Option.some.injEq, Prod.mk.injEq] at hfs
        obtain ⟨_, rfl⟩ := hfs
        have e := ih (by simpa [foKind] using hS _ _ _ h (by simpa [foKind] using hk)) hr2
        rw [hB.sound.value_eq, hB.sound.value_eq (P := P)] at e
        simp only [] at e
        simp [e]
      · simp [hcd]

theorem rel_tuple_inv {k : Kind} {v v' : Value} {ks : List Kind}
    (h : Rel O P N K E T0 S k v v') (hk : k = .tuple ks) :
    ∃ vs vs', v = .TupleV vs ∧ v' = .TupleV vs' := by
  cases h <;> first | exact ⟨_, _, rfl, rfl⟩ | cases hk

theorem rel_nth : ∀ {vs vs' : List Value} {ks : List Kind},
    Rel O P N K E T0 S (.tuple ks) (.TupleV vs) (.TupleV vs') →
    ∀ {i : Int} {v : Value}, nth vs i = .Ok v →
      ∃ v' k, nthKind ks i = some k ∧ nth vs' i = .Ok v' ∧ Rel O P N K E T0 S k v v'
  | [], _, _, h, i, v, hn => by simp [nth] at hn
  | w :: ws, _, _, h, i, v, hn => by
    cases h with
    | tupleCons h hr =>
      rw [nth] at hn
      by_cases hi : i = 1
      · simp only [hi, dite_true] at hn
        cases hn
        exact ⟨_, _, by simp [nthKind, hi], by simp [nth, hi], h⟩
      · simp only [hi, dite_false] at hn
        obtain ⟨v', k, h1, h2, h3⟩ := rel_nth hr hn
        exact ⟨v', k, by simp [nthKind, hi, h1], by simp [nth, hi, h2], h3⟩

theorem rel_select : ∀ {fs : List (Id × Kind)} {ps ps' : List Param} {vs vs' : List Value},
    paramNames ps = fs.map Prod.fst → paramNames ps' = fs.map Prod.fst →
    Rel O P N K E T0 S (.tuple (fs.map Prod.snd)) (.TupleV vs) (.TupleV vs') →
    ∀ {sel : Id} {v : Value}, select_field ps vs sel = .Ok v →
      ∃ v' k, fieldKind fs sel = some k ∧ select_field ps' vs' sel = .Ok v' ∧
        Rel O P N K E T0 S k v v'
  | [], ps, _, _, _, hp, _, _, sel, v, hs => by
    cases ps with
    | nil => simp [select_field] at hs
    | cons p _ => cases p; simp [paramNames] at hp
  | (f, k) :: fs, ps, ps', vs, vs', hp, hp', h, sel, v, hs => by
    cases ps with
    | nil => simp [paramNames] at hp
    | cons p ps1 =>
    cases ps' with
    | nil => simp [paramNames] at hp'
    | cons p' ps1' =>
    cases p with
    | Param x t =>
    cases p' with
    | Param x' t' =>
    simp only [paramNames, List.map, List.cons.injEq] at hp hp'
    obtain ⟨hxf, hp⟩ := hp
    obtain ⟨hxf', hp'⟩ := hp'
    simp only [List.map] at h
    cases h with
    | tupleCons h hr =>
      rw [select_field] at hs
      by_cases hx : f = sel
      · simp only [hxf, hx, dite_true] at hs
        cases hs
        exact ⟨_, k, by simp [fieldKind, hx], by simp [select_field, hxf', hx], h⟩
      · simp only [hxf, hx, dite_false] at hs
        obtain ⟨v', k2, h1, h2, h3⟩ := rel_select hp hp' hr hs
        exact ⟨v', k2, by simp [fieldKind, hx, h1], by simp [select_field, hxf', hx, h2], h3⟩

theorem rel_bind : ∀ {params : List Id} {ks : List Kind} {vs vs' : List Value},
    Rel O P N K E T0 S (.tuple ks) (.TupleV vs) (.TupleV vs') →
    ∀ {bs : List Binding}, bind_all params vs = .Ok bs →
      ∃ bs', bind_all params vs' = .Ok bs' ∧
        ∀ x k, (params.zip ks).lookup x = some k → ∃ v v', lookup_var bs x = .Ok v ∧
          lookup_var bs' x = .Ok v' ∧ Rel O P N K E T0 S k v v'
  | [], _, vs, _, h, bs, hb => by
    cases h with
    | tupleNil => exact ⟨[], by simp [bind_all], fun x k hx => by simp at hx⟩
    | tupleCons _ _ => simp [bind_all] at hb
  | p :: ps, _, vs, _, h, bs, hb => by
    cases h with
    | tupleNil => simp [bind_all] at hb
    | @tupleCons k ks v v' vs1 vs1' h hr =>
      rw [bind_all] at hb
      split at hb
      · next bs1 hbs1 =>
        cases hb
        obtain ⟨bs1', hb1', hl⟩ := rel_bind hr hbs1
        refine ⟨.Binding p v' :: bs1', by simp [bind_all, hb1'], fun x k2 hx => ?_⟩
        by_cases hxp : x = p
        · subst hxp
          simp at hx
          subst hx
          exact ⟨v, v', by simp [lookup_var], by simp [lookup_var], h⟩
        · have hb : (x == p) = false := by simpa using hxp
          simp only [List.zip_cons_cons, List.lookup, hb] at hx
          obtain ⟨u, u', h1, h2, h3⟩ := hl x k2 hx
          exact ⟨u, u', by simp [lookup_var, hxp, h1], by simp [lookup_var, hxp, h2], h3⟩
      · cases hb
      · cases hb

theorem rel_bind_app (vars vars' : List Binding) :
    ∀ {params : List Id} {ks : List Kind} {vs vs' : List Value},
    Rel O P N K E T0 S (.tuple ks) (.TupleV vs) (.TupleV vs') →
    ∀ {bs : List Binding}, bind_all params vs = .Ok bs →
      ∃ bs', bind_all params vs' = .Ok bs' ∧
        (∀ x k, (params.zip ks).lookup x = some k →
          ∃ v v', lookup_var (append_env bs vars) x = .Ok v ∧
            lookup_var (append_env bs' vars') x = .Ok v' ∧ Rel O P N K E T0 S k v v') ∧
        ∀ x, (params.zip ks).lookup x = none →
          lookup_var (append_env bs vars) x = lookup_var vars x ∧
            lookup_var (append_env bs' vars') x = lookup_var vars' x
  | [], _, vs, _, h, bs, hb => by
    cases h with
    | tupleNil =>
      simp only [bind_all] at hb
      cases hb
      exact ⟨[], by simp [bind_all], fun x k hx => by simp at hx,
        fun x _ => by simp [append_env]⟩
    | tupleCons _ _ => simp [bind_all] at hb
  | p :: ps, _, vs, _, h, bs, hb => by
    cases h with
    | tupleNil => simp [bind_all] at hb
    | @tupleCons k ks v v' vs1 vs1' h hr =>
      rw [bind_all] at hb
      split at hb
      · next bs1 hbs1 =>
        cases hb
        obtain ⟨bs1', hb1', hl, hn⟩ := rel_bind_app vars vars' hr hbs1
        refine ⟨.Binding p v' :: bs1', by simp [bind_all, hb1'], fun x k2 hx => ?_,
          fun x hx => ?_⟩
        · by_cases hxp : x = p
          · subst hxp
            simp at hx
            subst hx
            exact ⟨v, v', by simp [lookup_var, append_env], by simp [lookup_var, append_env], h⟩
          · have hb : (x == p) = false := by simpa using hxp
            simp only [List.zip_cons_cons, List.lookup, hb] at hx
            obtain ⟨u, u', h1, h2, h3⟩ := hl x k2 hx
            exact ⟨u, u', by simp [lookup_var, append_env, hxp, h1],
              by simp [lookup_var, append_env, hxp, h2], h3⟩
        · by_cases hxp : x = p
          · subst hxp
            simp at hx
          · have hb : (x == p) = false := by simpa using hxp
            simp only [List.zip_cons_cons, List.lookup, hb] at hx
            obtain ⟨h1, h2⟩ := hn x hx
            exact ⟨by simp [lookup_var, append_env, hxp, h1],
              by simp [lookup_var, append_env, hxp, h2]⟩
      · cases hb
      · cases hb

/-- The variables that a function keeps have values that relate. -/
theorem rel_lookups {vars vars' : List Binding} :
    ∀ {Γ0 : List (Id × Kind)} {vs vs' : List Value},
    Rel O P N K E T0 S (.tuple (Γ0.map Prod.snd)) (.TupleV vs) (.TupleV vs') →
    (Γ0.map Prod.fst).map (lookup_var vars) = vs.map Result.Ok →
    (Γ0.map Prod.fst).map (lookup_var vars') = vs'.map Result.Ok →
    ∀ x k, Γ0.lookup x = some k → ∃ v v', lookup_var vars x = .Ok v ∧
      lookup_var vars' x = .Ok v' ∧ Rel O P N K E T0 S k v v'
  | [], _, _, _, _, _, x, k, hx => by simp at hx
  | (y, ky) :: Γ0, vs, vs', h, hv, hv', x, k, hx => by
    simp only [List.map] at h
    cases h with
    | tupleCons h hr =>
      simp only [List.map, List.cons.injEq] at hv hv'
      by_cases hxy : x = y
      · subst hxy
        simp at hx
        subst hx
        exact ⟨_, _, hv.1, hv'.1, h⟩
      · have hb : (x == y) = false := by simpa using hxy
        simp only [List.lookup, hb] at hx
        exact rel_lookups hr hv.2 hv'.2 x k hx

theorem rel_capture {vars vars' : List Binding} : ∀ (Γ0 : List (Id × Kind)),
    (∀ p ∈ Γ0, ∃ v v', lookup_var vars p.1 = .Ok v ∧ lookup_var vars' p.1 = .Ok v' ∧
      Rel O P N K E T0 S p.2 v v') →
    ∃ vs vs', Rel O P N K E T0 S (.tuple (Γ0.map Prod.snd)) (.TupleV vs) (.TupleV vs') ∧
      (Γ0.map Prod.fst).map (lookup_var vars) = vs.map Result.Ok ∧
      (Γ0.map Prod.fst).map (lookup_var vars') = vs'.map Result.Ok
  | [], _ => ⟨[], [], .tupleNil, rfl, rfl⟩
  | p :: Γ0, h => by
    obtain ⟨v, v', h1, h2, hR⟩ := h p (by simp)
    obtain ⟨vs, vs', hr, e1, e2⟩ := rel_capture Γ0 (fun q hq => h q (by simp [hq]))
    exact ⟨v :: vs, v' :: vs', .tupleCons hR hr, by simp [h1, e1], by simp [h2, e2]⟩

end Values

/-- The program interprets the uninterpreted function `f`, without type arguments. -/
def InterpIn (f : Id) (params : List Id) (body : Expr) : Program → Prop
  | .Program _ _ _ is _ => lookup_interpretation is f [] = .Ok (.Interpretation f [] params body)

/-- The functions of the encoded program are what the encoder makes of those of the input, and
so are the interpretations of its uninterpreted functions. -/
def Funs (O : Oracle) (Ps P : Program) (N : Names) (T0 : Ty) (S : Sig) : Prop :=
  (∀ f tparams Tf ks k, S.funs f = some (tparams, Tf, ks, k) →
    ∃ params body body', FunIn f tparams params body Ps ∧ FunIn f tparams params body' P ∧
      Encodes N S Tf (fun x => (params.zip ks).lookup x) body body' k (S.flat f) ∧
      (tparams = [] → O.resolve_all [] [Tf] = [T0])) ∧
  (∀ f ks k, S.unint f = some (ks, k) →
    ∃ params body body' Tu, InterpIn f params body Ps ∧ InterpIn f params body' P ∧
      Encodes N S Tu (fun x => (params.zip ks).lookup x) body body' k (S.flat f) ∧
      O.resolve_all [] [Tu] = [T0])

section Evaluation
variable {O : Oracle} {Ps P : Program} {N : Names} {K : Value → Prop}
  {E : Value → Value → Bool}
  {T0 : Ty} {S : Sig} {inv bi eq b1 b2 : Id}

theorem eval_tuple_inv {Q : Program} {fuel : Int} {env : Env} {es : List Expr}
    {vs : List Value} (h : eval O Q fuel env (.Tuple es) = .Ok (.TupleV vs)) :
    eval_list O Q fuel env es = .Ok vs := by
  simp only [eval] at h
  split at h
  · next ws hws => cases h; exact hws
  · cases h
  · cases h

theorem construct_ctor {Q : Program} {c s : Id} {fs : List (Id × Kind)} (h : CtorIn c s fs Q)
    (fuel : Int) (env : Env) (tps : List Ty) (vs : List Value) :
    construct O Q fuel env c tps vs = .Ok (.ADTV c (O.resolve_all (env_types env) tps) vs) := by
  cases Q with
  | Program fns cs ss is eqs =>
  obtain ⟨params, tparams, hc, _, hs⟩ := h
  rw [construct]
  simp only [hc, hs]

theorem sel_inv {Q : Program} {fuel : Int} {env : Env} {e : Expr} {sel : Id} {v : Value}
    (h : eval O Q fuel env (.ADTSelector e sel) = .Ok v) :
    ∃ w, eval O Q fuel env e = .Ok w := by
  simp only [eval] at h
  split at h
  · next w hw => exact ⟨w, hw⟩
  · cases h
  · cases h

/-- The fields of the constructor `c` of a program. -/
def fieldsOf : Program → Id → List Param
  | .Program _ cs _ _ _, c =>
    match lookup_ctor cs c with
    | .Ok (.Constructor _ _ ps) => ps
    | _ => []

theorem sel_eval {Q : Program} {c s : Id} {fs : List (Id × Kind)} (h : CtorIn c s fs Q)
    {fuel : Int} {env : Env} {e : Expr} {tps : List Ty} {vs : List Value}
    (he : eval O Q fuel env e = .Ok (.ADTV c tps vs)) (sel : Id) :
    paramNames (fieldsOf Q c) = fs.map Prod.fst ∧
      eval O Q fuel env (.ADTSelector e sel) = select_field (fieldsOf Q c) vs sel := by
  cases Q with
  | Program fns cs ss is eqs =>
  obtain ⟨params, tparams, hc, hp, hs⟩ := h
  exact ⟨by simp only [fieldsOf, hc, hp], by simp only [eval, he, hc, fieldsOf]⟩

theorem call_inv {Q : Program} {f : Id} {tparams params : List Id} {body : Expr}
    (h : FunIn f tparams params body Q) {fuel : Int} {tps : List Ty} {tenv : List TypeBinding}
    {vs : List Value} {v : Value} (hc : call O Q fuel f tps tenv vs = .Ok v) :
    0 < fuel ∧ ∃ bs, bind_all params vs = .Ok bs ∧
      eval O Q (fuel - 1) (Env.Env (bind_types tparams tps tenv) bs) body = .Ok v := by
  cases Q with
  | Program fns cs ss is eqs =>
  have h : lookup_fun fns f = .Ok (.FunDef f tparams params body) := h
  rw [call] at hc
  by_cases hf : fuel ≤ 0
  · rw [dite_eq_left_of_eq_true (eq_true hf)] at hc
    cases hc
  · rw [dite_eq_right_of_eq_false (eq_false hf)] at hc
    simp only [h] at hc
    split at hc
    · next bs hbs => exact ⟨by omega, bs, hbs, hc⟩
    · cases hc
    · cases hc

theorem call_fun {Q : Program} {f : Id} {tparams params : List Id} {body : Expr}
    (h : FunIn f tparams params body Q) {fuel : Int} (hf : 0 < fuel) (tps : List Ty)
    (tenv : List TypeBinding) {vs : List Value} {bs : List Binding}
    (hbs : bind_all params vs = .Ok bs) :
    call O Q fuel f tps tenv vs =
      eval O Q (fuel - 1) (Env.Env (bind_types tparams tps tenv) bs) body := by
  cases Q with
  | Program fns cs ss is eqs =>
  have h : lookup_fun fns f = .Ok (.FunDef f tparams params body) := h
  rw [call, dite_eq_right_of_eq_false (eq_false (by omega))]
  simp only [h, hbs]

theorem uninterp_inv (hO : O.Sound) {Q : Program} {f : Id} {params : List Id} {body : Expr}
    (h : InterpIn f params body Q) {fuel : Int} {env : Env} {es : List Expr} {v : Value}
    (hc : eval O Q fuel env (.UninterpretedCall f [] es) = .Ok v) :
    ∃ vs, eval_list O Q fuel env es = .Ok vs ∧ 0 < fuel ∧
      ∃ bs, bind_all params vs = .Ok bs ∧
        eval O Q (fuel - 1) (Env.Env [] bs) body = .Ok v := by
  cases Q with
  | Program fns cs ss is eqs =>
  have h : lookup_interpretation is f [] = .Ok (.Interpretation f [] params body) := h
  rw [eval] at hc
  split at hc
  · next vs hvs =>
    by_cases hf : fuel ≤ 0
    · rw [dite_eq_left_of_eq_true (eq_true hf)] at hc
      cases hc
    · rw [dite_eq_right_of_eq_false (eq_false hf)] at hc
      simp only [hO.resolve_all, h] at hc
      split at hc
      · next bs hbs => exact ⟨vs, hvs, by omega, bs, hbs, hc⟩
      · cases hc
      · cases hc
  · cases hc
  · cases hc

theorem uninterp_fun (hO : O.Sound) {Q : Program} {f : Id} {params : List Id} {body : Expr}
    (h : InterpIn f params body Q) {fuel : Int} {env : Env} {es : List Expr} {vs : List Value}
    (hvs : eval_list O Q fuel env es = .Ok vs) (hf : 0 < fuel) {bs : List Binding}
    (hbs : bind_all params vs = .Ok bs) :
    eval O Q fuel env (.UninterpretedCall f [] es) =
      eval O Q (fuel - 1) (Env.Env [] bs) body := by
  cases Q with
  | Program fns cs ss is eqs =>
  have h : lookup_interpretation is f [] = .Ok (.Interpretation f [] params body) := h
  rw [eval, hvs]
  simp only []
  rw [dite_eq_right_of_eq_false (eq_false (by omega))]
  simp only [hO.resolve_all, h, hbs]

theorem resolve_bind (hO : O.Sound) (A : Id) (Te : Ty) (tenv : List TypeBinding) :
    O.resolve_all (bind_types [A] [Te] tenv) [.TypeParameter A] = O.resolve_all tenv [Te] := by
  simp only [hO.resolve_all]
  rw [hO.resolve (bind_types [A] [Te] tenv) (.TypeParameter A)]
  simp [bind_types, lookup_type]

theorem lookup_type_size : ∀ {tenv : List TypeBinding} {x y : Id} {u : Ty}
    {uenv : List TypeBinding}, lookup_type tenv x = some (.TypeBinding y u uenv) →
      sizeOf uenv < sizeOf tenv
  | [], _, _, _, _, h => by simp [lookup_type] at h
  | .TypeBinding z w wenv :: rest, x, y, u, uenv, h => by
    simp only [lookup_type] at h
    split at h
    · cases h
      simp +arith
    · have := lookup_type_size h
      simp +arith only [List.cons.sizeOf_spec] at *
      omega

/-- Values of a simple type have it in an environment whatever the environment, when the type
resolves to it there. -/
theorem has_type_simple (hO : O.Sound) (Q : Program) {T0 : Ty} (hs : SimpleTy T0) (v : Value) :
    ∀ (tenv : List TypeBinding) (vars : List Binding) (T : Ty), O.resolve tenv T = T0 →
      O.has_type Q (.Env tenv vars) v T = O.has_type Q (.Env [] []) v T0
  | tenv, vars, T, h => by
    rw [hO.resolve] at h
    cases T <;> simp only [] at h
    case TypeParameter x =>
      cases hl : lookup_type tenv x with
      | none =>
        rw [hl] at h
        subst h
        rw [hO.has_type, hO.has_type]
        simp [env_types, hl, lookup_type]
      | some b =>
        cases b with
        | TypeBinding y u uenv =>
        rw [hl] at h
        have := lookup_type_size hl
        rw [hO.has_type]
        simp only [env_types, hl]
        exact has_type_simple hO Q hs v uenv [] u h
    all_goals first
      | (subst h; simp [SimpleTy] at hs; done)
      | (subst h; rw [hO.has_type, hO.has_type])
termination_by tenv => sizeOf tenv

/-- The values of the type of elements in the encoded program are the elements. -/
theorem elems_typed (hB : Base O Ps P N K E T0 S inv bi eq b1 b2) (v : Value) :
    O.has_type P (.Env [] []) v T0 = true ↔ K v := by
  have h := hB.elems [] [v]
  rw [hB.sound.params_have_types] at h
  simp only [Bool.and_eq_true] at h
  rw [hB.sound.params_have_types, hB.sound.has_type] at h
  simpa [env_types, bind_types, lookup_type, env_bind] using h

/-- Values of types of `PureTy` relate to themselves. -/
theorem rel_pure (hO : O.Sound) (hSo : S.Ok) {Q : Program} (hQ : SortsIn S.sorts Q) :
    ∀ (sz : Nat) (v : Value), sizeOf v ≤ sz → ∀ (n : Nat) {B : List Id} {T : Ty}
      {tenv : List TypeBinding} (vars : List Binding), PureTy S.sorts S.ok B T →
        Cond S.sorts S.ok n B tenv tenv → O.has_type Q (.Env tenv vars) v T = true →
          Rel O P N K E T0 S (pureKind S.elemKind T) v v := by
  intro sz
  induction sz using Nat.strongRecOn with
  | _ sz ihs =>
  intro v hv n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro B T tenv vars hT
  induction hT generalizing tenv vars with
  | int =>
    intro _ h
    rw [hO.has_type] at h
    cases v <;> simp at h
    exact .int _
  | bool =>
    intro _ h
    rw [hO.has_type] at h
    cases v <;> simp at h
    exact .bool _
  | @tparam a h =>
    intro hC hty
    cases n with
    | zero => simp only [Cond] at hC; subst hC; simp at h
    | succ m =>
      obtain ⟨y, u, uenv, uenv', B', h1, h2, hu, hok, hC'⟩ := hC a h
      rw [h1] at h2
      cases h2
      rw [hO.has_type] at hty
      simp only [env_types] at hty
      rw [h1] at hty
      have hr := ihn m (Nat.lt_succ_self m) [] hu hC' hty
      simp only [Sig.ok] at hok
      rw [hok] at hr
      simpa only [pureKind] using hr
  | @adt s args tps ctors hs hl ha hok iha =>
    intro hC hty
    cases v
    case ADTV c vtps vs =>
      obtain ⟨fs, hlc, _, hps⟩ := (has_type_adt hO hQ hs tenv vars c vtps vs args).1 hty
      have hc := hSo.2 s tps ctors hs c fs (mem_of_lookup' hlc)
      have hC2 := cond_bind (tenv := tenv) (tenv' := tenv) ha hok hl hC
      have hfs := hSo.1 s tps ctors hs c fs (mem_of_lookup' hlc)
      have hsz : ∀ w ∈ vs, sizeOf w < sz := by
        intro w hw
        have := List.sizeOf_lt_of_mem hw
        simp only [Value.ADTV.sizeOf_spec] at hv
        omega
      simp only [pureKind]
      refine .adt hc ?_
      simp only [List.map_map]
      clear hlc hv ihn iha hty hc
      generalize ([] : List Binding) = vars0 at hps
      revert hsz hfs hps
      induction vs generalizing fs vars0 with
      | nil =>
        intro _ _ hps
        cases fs with
        | nil => exact .tupleNil
        | cons _ _ => rw [hO.params_have_types] at hps; simp at hps
      | cons w rest ih =>
        intro hfs hsz hps
        cases fs with
        | nil => rw [hO.params_have_types] at hps; simp at hps
        | cons p fs =>
          cases p with
          | Param x t =>
          rw [hO.params_have_types] at hps
          simp only [Bool.and_eq_true, env_bind] at hps
          simp only [List.map_cons, Function.comp, paramTy]
          exact .tupleCons
            (ihs (sizeOf w) (hsz w (by simp)) w (Nat.le_refl _) (n + 1) vars0
              (by simpa [paramTy] using hfs (.Param x t) (by simp)) hC2 hps.1)
            (ih fs _ (fun p hp => hfs p (by simp [hp])) (fun w hw => hsz w (by simp [hw]))
              hps.2)
    all_goals rw [hO.has_type] at hty; simp at hty
  | refine ht hp ih =>
    intro hC hty
    rw [hO.has_type] at hty
    simp only [Bool.and_eq_true] at hty
    exact ih vars hC hty.1

/-- The parameters of a quantifier are typed alike in both programs, and their values relate to
themselves. -/
theorem params_same (hB : Base O Ps P N K E T0 S inv bi eq b1 b2) (hSo : S.Ok) {Te : Ty} :
    ∀ {ps : List Param} {ks : List Kind}, ParamsOk S Te ps ks →
      ∀ (tys tys' : List TypeBinding) (vars vars' : List Binding),
        O.resolve_all tys [Te] = [T0] → O.resolve_all tys' [Te] = [T0] → ∀ vs,
          O.params_have_types Ps (.Env tys vars) vs ps =
              O.params_have_types P (.Env tys' vars') vs ps ∧
            (O.params_have_types Ps (.Env tys vars) vs ps = true →
              Rel O P N K E T0 S (.tuple ks) (.TupleV vs) (.TupleV vs)) := by
  have hO := hB.sound
  intro ps ks h
  induction h with
  | nil =>
    intro tys tys' vars vars' _ _ vs
    cases vs with
    | nil =>
      rw [hO.params_have_types, hO.params_have_types]
      exact ⟨rfl, fun _ => .tupleNil⟩
    | cons _ _ =>
      rw [hO.params_have_types, hO.params_have_types]
      simp
  | @cons x t ps k ks hk hr ih =>
    intro tys tys' vars vars' hT hT' vs
    cases vs with
    | nil =>
      rw [hO.params_have_types, hO.params_have_types]
      simp
    | cons v rest =>
      rw [hO.params_have_types, hO.params_have_types]
      simp only [env_bind]
      obtain ⟨e2, r2⟩ := ih tys tys' (.Binding x v :: vars) (.Binding x v :: vars') hT hT' rest
      have h1 : O.has_type Ps (.Env tys vars) v t = O.has_type P (.Env tys' vars') v t ∧
          (O.has_type Ps (.Env tys vars) v t = true → Rel O P N K E T0 S k v v) := by
        cases hk with
        | @elem a h =>
          subst h
          have g1 : O.resolve tys (.TypeParameter a) = T0 := by
            simp only [hO.resolve_all, List.cons.injEq] at hT
            exact hT.1
          have g2 : O.resolve tys' (.TypeParameter a) = T0 := by
            simp only [hO.resolve_all, List.cons.injEq] at hT'
            exact hT'.1
          rw [has_type_simple hO Ps hB.simple v tys vars _ g1,
            has_type_simple hO P hB.simple v tys' vars' _ g2]
          exact ⟨Bool.eq_iff_iff.2 ((hB.elemsS v).trans (elems_typed hB v).symm),
            fun h => .elem v ((hB.elemsS v).1 h)⟩
        | pure h =>
          exact ⟨has_type_same hO hB.sortsS hB.sortsP hSo.1 (sizeOf v) v (Nat.le_refl _) 0
              vars vars' h (by simp [Cond]),
            fun hty => rel_pure hO hSo hB.sortsS (sizeOf v) v (Nat.le_refl _) 0 vars h
              (by simp [Cond]) hty⟩
      refine ⟨by rw [h1.1, e2], fun h => ?_⟩
      simp only [Bool.and_eq_true] at h
      exact .tupleCons (h1.2 h.1) (r2 h.2)

theorem param_ids_length : ∀ (ps : List Param), (param_ids ps).length = ps.length
  | [] => by simp [param_ids]
  | .Param _ _ :: ps => by simp [param_ids, param_ids_length ps]

theorem bind_len : ∀ (ids : List Id) (vs : List Value), ids.length = vs.length →
    ∃ bs, bind_all ids vs = .Ok bs
  | [], [], _ => ⟨[], by simp [bind_all]⟩
  | x :: ids, v :: vs, h => by
    obtain ⟨bs, hb⟩ := bind_len ids vs (by simpa using h)
    exact ⟨.Binding x v :: bs, by simp [bind_all, hb]⟩
  | [], _ :: _, h | _ :: _, [], h => by simp at h

theorem lookup_other : ∀ {ids : List Id} {vs : List Value} {bs : List Binding},
    bind_all ids vs = .Ok bs → ∀ (vars : List Binding) (x : Id), x ∉ ids →
      lookup_var (append_env bs vars) x = lookup_var vars x
  | [], [], bs, h, vars, x, _ => by simp [bind_all] at h; subst h; simp [append_env]
  | y :: ids, v :: vs, bs, h, vars, x, hx => by
    rw [bind_all] at h
    split at h
    · next bs1 h1 =>
      cases h
      have hxy : x ≠ y := fun e => hx (by simp [e])
      simp only [append_env, lookup_var, hxy, dite_false]
      exact lookup_other h1 vars x (fun e => hx (by simp [e]))
    · cases h
    · cases h
  | [], _ :: _, _, h, _, _, _ | _ :: _, [], _, h, _, _, _ => by simp [bind_all] at h

theorem pht_len (hO : O.Sound) (Q : Program) : ∀ (env : Env) (vs : List Value) (ps : List Param),
    O.params_have_types Q env vs ps = true → vs.length = ps.length
  | env, [], [], _ => rfl
  | env, v :: vs, .Param x t :: ps, h => by
    rw [hO.params_have_types] at h
    simp only [Bool.and_eq_true] at h
    simp [pht_len hO Q _ vs ps h.2]
  | env, [], _ :: _, h => by rw [hO.params_have_types] at h; simp at h
  | env, _ :: _, [], h => by rw [hO.params_have_types] at h; simp at h

theorem ht_len (hO : O.Sound) (Q : Program) : ∀ (env : Env) (vs : List Value) (ts : List Ty),
    O.have_types Q env vs ts = true → vs.length = ts.length
  | env, [], [], _ => rfl
  | env, v :: vs, t :: ts, h => by
    rw [hO.have_types] at h
    simp only [Bool.and_eq_true] at h
    simp [ht_len hO Q _ vs ts h.2]
  | env, [], _ :: _, h => by rw [hO.have_types] at h; simp at h
  | env, _ :: _, [], h => by rw [hO.have_types] at h; simp at h

/-- A value of a simple type, and a literal of it. -/
def valOf : Ty → Value
  | .BooleanType => .BoolV true
  | _ => .IntV 0

def litOf : Ty → Expr
  | .BooleanType => .BooleanLiteral true
  | _ => .IntegerLiteral 0

theorem valOf_typed (hO : O.Sound) (Q : Program) {T0 : Ty} (hs : SimpleTy T0) :
    O.has_type Q (.Env [] []) (valOf T0) T0 = true := by
  cases T0 <;> simp [SimpleTy] at hs <;> rw [hO.has_type] <;> simp [valOf, env_types, lookup_type]

theorem litOf_eval (Q : Program) (fuel : Int) (env : Env) (T : Ty) :
    eval O Q fuel env (litOf T) = .Ok (valOf T) := by
  cases T <;> simp [litOf, valOf, eval]

theorem same_arity_map : ∀ (ts : List Ty), same_arity (ts.map (Param.Param "_")) ts = true
  | [] => by simp [same_arity]
  | t :: ts => by simp [same_arity, same_arity_map ts]

open Classical in
/-- Types of `Inhab` have values in any program. -/
theorem inhab_typed (hO : O.Sound) {Te T0 : Ty} (hs : SimpleTy T0) {t : Ty} (h : Inhab Te t)
    (Q : Program) (tys : List TypeBinding) (vars : List Binding) (hT : O.resolve tys Te = T0) :
    ∃ v, O.has_type Q (.Env tys vars) v t = true := by
  cases h with
  | int => exact ⟨.IntV 0, by rw [hO.has_type]⟩
  | bool => exact ⟨.BoolV true, by rw [hO.has_type]⟩
  | @elem a h =>
    subst h
    exact ⟨valOf T0, by rw [has_type_simple hO Q hs _ tys vars _ hT]; exact valOf_typed hO Q hs⟩
  | @fn ts t ht =>
    have pick : ∃ T1, (∀ (Q : Program) (fuel : Int) (env : Env),
        eval O Q fuel env (litOf T1) = .Ok (valOf T1)) ∧
          O.has_type Q (.Env tys vars) (valOf T1) t = true := by
      rcases ht with rfl | rfl | rfl
      · exact ⟨.IntegerType, fun _ _ _ => litOf_eval _ _ _ _, by simp [valOf, hO.has_type]⟩
      · exact ⟨.BooleanType, fun _ _ _ => litOf_eval _ _ _ _, by simp [valOf, hO.has_type]⟩
      · exact ⟨T0, fun _ _ _ => litOf_eval _ _ _ _, by
          rw [has_type_simple hO Q hs _ tys vars _ hT]; exact valOf_typed hO Q hs⟩
    obtain ⟨T1, he, hty⟩ := pick
    refine ⟨.ClosureV (ts.map (Param.Param "_")) (litOf T1) (.Env [] []), ?_⟩
    rw [hO.has_type]
    simp only [same_arity_map, Bool.true_and]
    rw [hO.function_has_type]
    refine decide_eq_true (fun vs => ?_)
    cases hv : O.have_types Q (.Env tys vars) vs ts
    · simp
    · have hl := ht_len hO Q _ vs ts hv
      obtain ⟨bs, hbs⟩ := bind_len (param_ids (ts.map (Param.Param "_"))) vs
        (by rw [param_ids_length]; simp [hl])
      simp only [Bool.not_true, Bool.false_or]
      refine decide_eq_true ⟨1, valOf T1, ?_⟩
      simp only [apply, hbs, he, hty]
      simp

theorem params_inhab (hO : O.Sound) {Te T0 : Ty} (hs : SimpleTy T0) (Q : Program)
    (tys : List TypeBinding) (hT : O.resolve tys Te = T0) :
    ∀ (ps : List Param), (∀ p ∈ ps, Inhab Te (paramTy p)) → ∀ (vars : List Binding),
      ∃ vs, O.params_have_types Q (.Env tys vars) vs ps = true
  | [], _, vars => ⟨[], by rw [hO.params_have_types]⟩
  | .Param x t :: ps, h, vars => by
    obtain ⟨v, hv⟩ := inhab_typed hO hs (h (.Param x t) (by simp)) Q tys vars hT
    obtain ⟨vs, hvs⟩ := params_inhab hO hs Q tys hT ps (fun p hp => h p (by simp [hp]))
      (.Binding x v :: vars)
    have hv' : O.has_type Q (.Env tys vars) v t = true := by simpa [paramTy] using hv
    exact ⟨v :: vs, by rw [hO.params_have_types]; simp [env_bind, hv', hvs]⟩

/-- The bound on the fuel of an encoding without operations of bags, from those of its parts. -/
local macro "bnd" hu:ident : tactic => `(tactic| first
  | exact absurd $hu (by decide)
  | (subst $hu; (try simp only [eq_self_iff_true, true_implies, forall_const] at *); omega))

open Classical in
/-- An encoded expression evaluates, with enough fuel, to a value that relates to the value of
the expression, and with no more fuel than it does when it has no operations of bags. -/
theorem encodes_eval (hB : Base O Ps P N K E T0 S inv bi eq b1 b2) (hSo : S.Ok)
    (hF : Funs O Ps P N T0 S) :
    ∀ (n : Nat) {Te : Ty} {Γ : Id → Option Kind} {e e' : Expr} {k : Kind} {u : Bool},
      Encodes N S Te Γ e e' k u →
      ∀ (env env' : Env), O.resolve_all (env_types env) [Te] = [T0] ∧
        O.resolve_all (env_types env') [Te] = [T0] →
        (∀ x k, Γ x = some k → ∃ v v', lookup_var (env_vars env) x = .Ok v ∧
          lookup_var (env_vars env') x = .Ok v' ∧ Rel O P N K E T0 S k v v') →
        ∀ (fuel : Int), fuel ≤ n → ∀ (v : Value), eval O Ps fuel env e = .Ok v →
          ∃ (v' : Value) (m : Int), (u = true → m ≤ max fuel 0) ∧
            Rel O P N K E T0 S k v v' ∧
            ∀ fuel' : Int, m ≤ fuel' → eval O P fuel' env' e' = .Ok v' := by
  have hO := hB.sound
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro Te Γ e e' k u h
  induction h with
  | var x k hx =>
    intro env env' hT hΓ fuel hfn v hv
    obtain ⟨w, w', h1, h2, hR⟩ := hΓ x k hx
    simp only [eval, h1] at hv
    cases hv
    exact ⟨w', 0, fun hu => by bnd hu, hR, fun _ _ => by simp only [eval, h2]⟩
  | int n =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    cases hv
    exact ⟨_, 0, fun hu => by bnd hu, .int n, fun _ _ => by simp only [eval]⟩
  | bool b =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    cases hv
    exact ⟨_, 0, fun hu => by bnd hu, .bool b, fun _ _ => by simp only [eval]⟩
  | plus _ _ iha ihb =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨_, n1, bd1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨_, n2, bd2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        cases hR1
        cases hR2
        simp only [arith_plus] at hv
        cases hv
        exact ⟨_, max n1 n2, fun hu => by bnd hu, .int _, fun f hf => by
          simp only [eval, e1 f (by omega), e2 f (by omega), arith_plus]⟩
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | minus _ _ iha ihb =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨_, n1, bd1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨_, n2, bd2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        cases hR1
        cases hR2
        simp only [arith_minus] at hv
        cases hv
        exact ⟨_, max n1 n2, fun hu => by bnd hu, .int _, fun f hf => by
          simp only [eval, e1 f (by omega), e2 f (by omega), arith_minus]⟩
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | lt _ _ iha ihb =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨_, n1, bd1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨_, n2, bd2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        cases hR1
        cases hR2
        split at hv
        · next same hsame =>
          cases hv
          exact ⟨_, max n1 n2, fun hu => by bnd hu, .bool _, fun f hf => by
            simp only [eval, e1 f (by omega), e2 f (by omega), hsame]⟩
        · cases hv
        · cases hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | gt _ _ iha ihb =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨_, n1, bd1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨_, n2, bd2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        cases hR1
        cases hR2
        split at hv
        · next same hsame =>
          cases hv
          exact ⟨_, max n1 n2, fun hu => by bnd hu, .bool _, fun f hf => by
            simp only [eval, e1 f (by omega), e2 f (by omega), hsame]⟩
        · cases hv
        · cases hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | le _ _ iha ihb =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨_, n1, bd1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨_, n2, bd2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        cases hR1
        cases hR2
        split at hv
        · next same hsame =>
          cases hv
          exact ⟨_, max n1 n2, fun hu => by bnd hu, .bool _, fun f hf => by
            simp only [eval, e1 f (by omega), e2 f (by omega), hsame]⟩
        · cases hv
        · cases hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | ge _ _ iha ihb =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨_, n1, bd1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨_, n2, bd2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        cases hR1
        cases hR2
        split at hv
        · next same hsame =>
          cases hv
          exact ⟨_, max n1 n2, fun hu => by bnd hu, .bool _, fun f hf => by
            simp only [eval, e1 f (by omega), e2 f (by omega), hsame]⟩
        · cases hv
        · cases hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | eq hk hS _ _ iha ihb =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨va', n1, bd1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨vb', n2, bd2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        split at hv
        · next same hsame =>
          cases hv
          rw [rel_value_eq hB hS hR1 hk hR2] at hsame
          exact ⟨_, max n1 n2, fun hu => by bnd hu, .bool _, fun f hf => by
            simp only [eval, e1 f (by omega), e2 f (by omega), hsame]⟩
        · cases hv
        · cases hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | not _ iha =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next a ha =>
      cases hv
      obtain ⟨_, n1, bd1, hR, e1⟩ := iha env env' hT hΓ fuel hfn _ (eval_bool_ok ha)
      cases hR
      exact ⟨_, n1, fun hu => by bnd hu,
          .bool _, fun f hf => by simp only [eval, eval_bool, e1 f hf]⟩
    · cases hv
    · cases hv
  | andNil =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    rw [eval_and] at hv
    cases hv
    exact ⟨_, 0, fun hu => by bnd hu, .bool _, fun _ _ => by simp only [eval]; rw [eval_and]⟩
  | andCons _ _ iha ihr =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    rw [eval_and] at hv
    split at hv
    · next b hb =>
      obtain ⟨_, n1, bd1, hR, e1⟩ := iha env env' hT hΓ fuel hfn _ (eval_bool_ok hb)
      cases hR
      cases b with
      | true =>
        simp only [dite_true] at hv
        obtain ⟨v', n2, bd2, hR, e2⟩ :=
          ihr env env' hT hΓ fuel hfn v (by simp only [eval]; exact hv)
        refine ⟨v', max n1 n2, fun hu => by bnd hu, hR, fun f hf => ?_⟩
        have h2 := e2 f (by omega)
        simp only [eval] at h2 ⊢
        rw [eval_and]
        simp only [eval_bool, e1 f (by omega), dite_true, h2]
      | false =>
        simp at hv
        cases hv
        refine ⟨_, n1, fun hu => by bnd hu, .bool _, fun f hf => ?_⟩
        simp only [eval]
        rw [eval_and]
        simp [eval_bool, e1 f hf]
    · cases hv
    · cases hv
  | orNil =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    rw [eval_or] at hv
    cases hv
    exact ⟨_, 0, fun hu => by bnd hu, .bool _, fun _ _ => by simp only [eval]; rw [eval_or]⟩
  | orCons _ _ iha ihr =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    rw [eval_or] at hv
    split at hv
    · next b hb =>
      obtain ⟨_, n1, bd1, hR, e1⟩ := iha env env' hT hΓ fuel hfn _ (eval_bool_ok hb)
      cases hR
      cases b with
      | false =>
        simp at hv
        obtain ⟨v', n2, bd2, hR, e2⟩ :=
          ihr env env' hT hΓ fuel hfn v (by simp only [eval]; exact hv)
        refine ⟨v', max n1 n2, fun hu => by bnd hu, hR, fun f hf => ?_⟩
        have h2 := e2 f (by omega)
        simp only [eval] at h2 ⊢
        rw [eval_or]
        simp [eval_bool, e1 f (by omega), h2]
      | true =>
        simp only [dite_true] at hv
        cases hv
        refine ⟨_, n1, fun hu => by bnd hu, .bool _, fun f hf => ?_⟩
        simp only [eval]
        rw [eval_or]
        simp [eval_bool, e1 f hf]
    · cases hv
    · cases hv
  | implies _ _ iha ihb =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next a ha =>
      obtain ⟨_, n1, bd1, hR, e1⟩ := iha env env' hT hΓ fuel hfn _ (eval_bool_ok ha)
      cases hR
      cases a with
      | true =>
        simp only [dite_true] at hv
        split at hv
        · next b hb =>
          obtain ⟨_, n2, bd2, hR, e2⟩ := ihb env env' hT hΓ fuel hfn _ (eval_bool_ok hb)
          cases hR
          cases hv
          exact ⟨_, max n1 n2, fun hu => by bnd hu, .bool _, fun f hf => by
            simp [eval, eval_bool, e1 f (by omega), e2 f (by omega)]⟩
        · cases hv
        · cases hv
      | false =>
        simp at hv
        cases hv
        exact ⟨_, n1, fun hu => by bnd hu, .bool _,
          fun f hf => by simp [eval, eval_bool, e1 f hf]⟩
    · cases hv
    · cases hv
  | ite _ _ _ ihc iha ihb =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next c hc =>
      obtain ⟨_, n1, bd1, hR, e1⟩ := ihc env env' hT hΓ fuel hfn _ (eval_bool_ok hc)
      cases hR
      cases c with
      | true =>
        simp only [dite_true] at hv
        obtain ⟨v', n2, bd2, hR, e2⟩ := iha env env' hT hΓ fuel hfn v hv
        exact ⟨v', max n1 n2, fun hu => by bnd hu, hR, fun f hf => by
          simp [eval, eval_bool, e1 f (by omega), e2 f (by omega)]⟩
      | false =>
        simp at hv
        obtain ⟨v', n2, bd2, hR, e2⟩ := ihb env env' hT hΓ fuel hfn v hv
        exact ⟨v', max n1 n2, fun hu => by bnd hu, hR, fun f hf => by
          simp [eval, eval_bool, e1 f (by omega), e2 f (by omega)]⟩
    · cases hv
    · cases hv
  | let_ x _ _ iha ihb =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next w hw =>
      obtain ⟨w', n1, bd1, hR, e1⟩ := iha env env' hT hΓ fuel hfn w hw
      obtain ⟨v', n2, bd2, hR2, e2⟩ := ihb (env_bind env x w) (env_bind env' x w')
        (by cases env; cases env'; exact hT)
        (fun y k hy => by
          by_cases hyx : y = x
          · subst hyx
            simp only [if_true, Option.some.injEq] at hy
            subst hy
            cases env; cases env'
            exact ⟨w, w', by simp [env_bind, env_vars, lookup_var],
              by simp [env_bind, env_vars, lookup_var], hR⟩
          · simp only [hyx, if_false] at hy
            obtain ⟨u, u', h1, h2, hRu⟩ := hΓ y k hy
            cases env; cases env'
            exact ⟨u, u', by simpa [env_bind, env_vars, lookup_var, hyx] using h1,
              by simpa [env_bind, env_vars, lookup_var, hyx] using h2, hRu⟩)
        fuel hfn v hv
      exact ⟨v', max n1 n2, fun hu => by bnd hu, hR2, fun f hf => by
        simp only [eval, e1 f (by omega)]
        exact e2 f (by omega)⟩
    · cases hv
    · cases hv
  | assume _ _ ihp ihb =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next c hc =>
      obtain ⟨_, n1, bd1, hR, e1⟩ := ihp env env' hT hΓ fuel hfn _ (eval_bool_ok hc)
      cases hR
      cases c with
      | true =>
        simp only [dite_true] at hv
        obtain ⟨v', n2, bd2, hR, e2⟩ := ihb env env' hT hΓ fuel hfn v hv
        exact ⟨v', max n1 n2, fun hu => by bnd hu, hR, fun f hf => by
          simp [eval, eval_bool, e1 f (by omega), e2 f (by omega)]⟩
      | false =>
        simp at hv
    · cases hv
    · cases hv
  | empty base =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval, eval_bag_entries] at hv
    cases hv
    refine ⟨.ADTV N.leaf [T0] [], 1, fun hu => by bnd hu,
      .bag _ [] N.leaf [] trivial (enc_empty _)
      (Or.inr (Or.inr rfl)), fun f hf => ?_⟩
    simp only [eval, eval_list, construct_leaf hB.names hB.sort (show 0 < f by omega), hT]
  | add _ _ ihb ihe =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next vb hb =>
      split at hv
      · next ve he =>
        obtain ⟨hb, _⟩ := eval_bag_ok hb
        obtain ⟨vb', n1, bd1, hR1, e1⟩ := ihb env env' hT hΓ fuel hfn vb hb
        obtain ⟨ve', n2, bd2, hR2, e2⟩ := ihe env env' hT hΓ fuel hfn ve he
        cases hR1 with
        | bag t xs c args hxs henc hc =>
        cases hR2 with
        | elem _ hk =>
        simp only [bag_entries, bag_get_eq hO hB.keyS hxs hk, bag_set_eq hB.keyS hxs hk,
          bag_with] at hv
        cases hv
        refine ⟨.ADTV N.node [T0] [.IntV 0, .ADTV c [T0] args, .ADTV N.elem [T0] [ve, .IntV 1]],
          max (max n1 n2) 1, fun hu => by bnd hu, .bag _ _ N.node _ (canon_set hB.key hxs hk _)
            (enc_add hB.key hxs henc hk _ _) (Or.inl rfl), fun f hf => ?_⟩
        simp only [eval, eval_list, e1 f (by omega), e2 f (by omega),
          construct_elem hB.names hB.bags hB.sort (show 0 < f by omega) env' [Te] ve
            (show (0 : Int) ≤ 1 by omega),
          construct_node hB.names hB.bags hB.sort (show 0 < f by omega), hT]
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | union _ _ iha ihb =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨ha, _⟩ := eval_bag_ok ha
        obtain ⟨hb, _⟩ := eval_bag_ok hb
        obtain ⟨va', n1, bd1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨vb', n2, bd2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        cases hR1 with
        | bag t xs c args hxs hea hc =>
        cases hR2 with
        | bag u ys c2 args2 hys heb hc2 =>
        simp only [bag_entries, bag_add_all_eq hO hB.keyS hxs hys, bag_with] at hv
        cases hv
        refine ⟨.ADTV N.node [T0] [.IntV 0, .ADTV c [T0] args, .ADTV c2 [T0] args2],
          max (max n1 n2) 1, fun hu => by bnd hu, .bag _ _ N.node _ (canon_addAll hB.key hxs hys)
            (enc_union hB.key hxs hys hea heb _) (Or.inl rfl), fun f hf => ?_⟩
        simp only [eval, eval_list, e1 f (by omega), e2 f (by omega),
          construct_node hB.names hB.bags hB.sort (show 0 < f by omega), hT]
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | difference _ _ iha ihb =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨ha, _⟩ := eval_bag_ok ha
        obtain ⟨hb, _⟩ := eval_bag_ok hb
        obtain ⟨va', n1, bd1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨vb', n2, bd2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        cases hR1 with
        | bag t xs c args hxs hea hc =>
        cases hR2 with
        | bag u ys c2 args2 hys heb hc2 =>
        simp only [bag_entries,
          bag_merge_eq hO hB.keyS .DifferenceOp hys (acc := []) trivial hxs, bag_with] at hv
        cases hv
        refine ⟨.ADTV N.node [T0] [.IntV 1, .ADTV c [T0] args, .ADTV c2 [T0] args2],
          max (max n1 n2) 1, fun hu => by bnd hu,
              .bag _ _ N.node _ (canon_merge hB.key _ ys (acc := []) trivial hxs)
            (enc_difference hB.key hxs hys hea heb _) (Or.inl rfl), fun f hf => ?_⟩
        simp only [eval, eval_list, e1 f (by omega), e2 f (by omega),
          construct_node hB.names hB.bags hB.sort (show 0 < f by omega), hT]
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | intersection _ _ iha ihb =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨ha, _⟩ := eval_bag_ok ha
        obtain ⟨hb, _⟩ := eval_bag_ok hb
        obtain ⟨va', n1, bd1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨vb', n2, bd2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        cases hR1 with
        | bag t xs c args hxs hea hc =>
        cases hR2 with
        | bag u ys c2 args2 hys heb hc2 =>
        simp only [bag_entries,
          bag_merge_eq hO hB.keyS .IntersectionOp hys (acc := []) trivial hxs, bag_with] at hv
        cases hv
        refine ⟨.ADTV N.node [T0] [.IntV 2, .ADTV c [T0] args, .ADTV c2 [T0] args2],
          max (max n1 n2) 1, fun hu => by bnd hu,
              .bag _ _ N.node _ (canon_merge hB.key _ ys (acc := []) trivial hxs)
            (enc_intersection hB.key hxs hys hea heb _) (Or.inl rfl), fun f hf => ?_⟩
        simp only [eval, eval_list, e1 f (by omega), e2 f (by omega),
          construct_node hB.names hB.bags hB.sort (show 0 < f by omega), hT]
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | mult _ _ ihe ihb =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next ve he =>
      split at hv
      · next vb hb =>
        obtain ⟨hb, _⟩ := eval_bag_ok hb
        obtain ⟨vb', n1, bd1, hR1, e1⟩ := ihb env env' hT hΓ fuel hfn vb hb
        obtain ⟨ve', n2, bd2, hR2, e2⟩ := ihe env env' hT hΓ fuel hfn ve he
        cases hR1 with
        | bag t xs c args hxs henc hc =>
        cases hR2 with
        | elem _ hk =>
        obtain ⟨d, hd⟩ := henc
        simp only [bag_entries, bag_get_eq hO hB.keyS hxs hk] at hv
        cases hv
        refine ⟨_, max (max n1 n2) (d + 1), fun hu => by bnd hu, .int _, fun f hf => ?_⟩
        simp only [eval, eval_list, e1 f (by omega), e2 f (by omega)]
        exact get_eval hO hB.names hB.bags (hd ve hk) f _ _ (by omega)
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | tupleNil =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval, eval_list] at hv
    cases hv
    exact ⟨_, 0, fun hu => by bnd hu, .tupleNil, fun _ _ => by simp only [eval, eval_list]⟩
  | tupleCons _ _ ihe ihr =>
    intro env env' hT hΓ fuel hfn v hv
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
          obtain ⟨w', n1, bd1, hR1, e1⟩ := ihe env env' hT hΓ fuel hfn w hw
          obtain ⟨t', n2, bd2, hR2, e2⟩ :=
            ihr env env' hT hΓ fuel hfn (.TupleV ws) (by simp only [eval, hws])
          obtain ⟨_, ws', h1, rfl⟩ := rel_tuple_inv hR2 rfl
          cases h1
          refine ⟨_, max n1 n2, fun hu => by bnd hu, .tupleCons hR1 hR2, fun f hf => ?_⟩
          simp only [eval]
          rw [eval_list]
          simp only [e1 f (by omega), eval_tuple_inv (e2 f (by omega))]
        · cases hvs
        · cases hvs
      · cases hvs
      · cases hvs
    · cases hv
    · cases hv
  | tupleSelect i _ hk iht =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next tv htv =>
      obtain ⟨t', n1, bd1, hR, e1⟩ := iht env env' hT hΓ fuel hfn tv htv
      obtain ⟨vs, vs', rfl, rfl⟩ := rel_tuple_inv hR rfl
      simp only [] at hv
      obtain ⟨v', k2, hk2, hn, hRv⟩ := rel_nth hR hv
      rw [hk] at hk2
      cases hk2
      exact ⟨v', n1, fun hu => by bnd hu, hRv, fun f hf => by simp only [eval, e1 f hf, hn]⟩
    · cases hv
    · cases hv
  | adt tps tps' hc _ iha =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next vs hvs =>
      rw [construct_ctor (hB.ctorS _ _ _ hc)] at hv
      cases hv
      obtain ⟨t', n1, bd1, hR, e1⟩ :=
        iha env env' hT hΓ fuel hfn (.TupleV vs) (by simp only [eval, hvs])
      obtain ⟨_, vs', h1, rfl⟩ := rel_tuple_inv hR rfl
      cases h1
      exact ⟨.ADTV _ (O.resolve_all (env_types env') tps') vs', n1, fun hu => by bnd hu,
          .adt hc hR, fun f hf => by
        simp only [eval, eval_tuple_inv (e1 f hf), construct_ctor (hB.ctor _ _ _ hc)]⟩
    · cases hv
    · cases hv
  | sel sel _ hk ihe =>
    intro env env' hT hΓ fuel hfn v hv
    obtain ⟨w, hw⟩ := sel_inv hv
    obtain ⟨w', n1, bd1, hR, e1⟩ := ihe env env' hT hΓ fuel hfn w hw
    cases hR with
    | @adt c _ fs tps tps' vs vs' hc hr =>
    obtain ⟨hps, hsel⟩ := sel_eval (hB.ctorS _ _ _ hc) hw sel
    rw [hsel] at hv
    obtain ⟨hps', _⟩ := sel_eval (hB.ctor _ _ _ hc) (e1 n1 (Int.le_refl _)) sel
    obtain ⟨v', k2, hk2, hs', hRv⟩ := rel_select hps hps' hr hv
    cases hk c fs hc k2 hk2
    refine ⟨v', n1, fun hu => by bnd hu, hRv, fun f hf => ?_⟩
    rw [(sel_eval (hB.ctor _ _ _ hc) (e1 f hf) sel).2]
    exact hs'
  | isCtor c _ ihe =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next w hw =>
      obtain ⟨w', n1, bd1, hR, e1⟩ := ihe env env' hT hΓ fuel hfn w hw
      cases hR with
      | adt hc hr =>
      simp only [] at hv
      cases hv
      exact ⟨_, n1, fun hu => by bnd hu, .bool _, fun f hf => by simp only [eval, e1 f hf]⟩
    · cases hv
    · cases hv
  | @callPoly Γ u f A ks k es es' hf hu0 _ iha =>
    intro env env' hT hΓ fuel hfn v hv
    obtain ⟨params, body, body', hFS, hFP, hEnc, _⟩ := hF.1 _ _ _ _ _ hf
    simp only [eval] at hv
    split at hv
    · next vs hvs =>
      obtain ⟨hpos, bs, hbs, hbody⟩ := call_inv hFS hv
      obtain ⟨t', n1, bd1, hR, e1⟩ :=
        iha env env' hT hΓ fuel hfn (.TupleV vs) (by simp only [eval, hvs])
      obtain ⟨_, vs', h1, rfl⟩ := rel_tuple_inv hR rfl
      cases h1
      obtain ⟨bs', hbs', hl⟩ := rel_bind hR hbs
      cases n with
      | zero => omega
      | succ m =>
      obtain ⟨v', m2, bdm, hRv, e2⟩ := ihn m (Nat.lt_succ_self m) hEnc
        (Env.Env (bind_types [A] [Te] (env_types env)) bs)
        (Env.Env (bind_types [A] [Te] (env_types env')) bs')
        (by simpa [env_types, resolve_bind hO] using hT)
        (fun x k hx => hl x k hx) (fuel - 1) (by omega) v hbody
      refine ⟨v', max (max n1 (m2 + 1)) 1,
        fun hu => by have := bd1 hu; have := bdm (hu0 hu); omega, hRv, fun f' hf' => ?_⟩
      simp only [eval, eval_tuple_inv (e1 f' (by omega))]
      rw [call_fun hFP (by omega) _ _ hbs']
      exact e2 (f' - 1) (by omega)
    · cases hv
    · cases hv
  | @callMono Γ u f Tf ks k tps es es' hf hu0 _ iha =>
    intro env env' hT hΓ fuel hfn v hv
    obtain ⟨params, body, body', hFS, hFP, hEnc, hTf⟩ := hF.1 _ _ _ _ _ hf
    simp only [eval] at hv
    split at hv
    · next vs hvs =>
      obtain ⟨hpos, bs, hbs, hbody⟩ := call_inv hFS hv
      obtain ⟨t', n1, bd1, hR, e1⟩ :=
        iha env env' hT hΓ fuel hfn (.TupleV vs) (by simp only [eval, hvs])
      obtain ⟨_, vs', h1, rfl⟩ := rel_tuple_inv hR rfl
      cases h1
      obtain ⟨bs', hbs', hl⟩ := rel_bind hR hbs
      cases n with
      | zero => omega
      | succ m =>
      obtain ⟨v', m2, bdm, hRv, e2⟩ := ihn m (Nat.lt_succ_self m) hEnc
        (Env.Env (bind_types [] tps (env_types env)) bs)
        (Env.Env (bind_types [] [] (env_types env')) bs')
        (by simpa [env_types, bind_types] using And.intro (hTf rfl) (hTf rfl))
        (fun x k hx => hl x k hx) (fuel - 1) (by omega) v hbody
      refine ⟨v', max (max n1 (m2 + 1)) 1,
        fun hu => by have := bd1 hu; have := bdm (hu0 hu); omega, hRv, fun f' hf' => ?_⟩
      simp only [eval, eval_tuple_inv (e1 f' (by omega))]
      rw [call_fun hFP (by omega) _ _ hbs']
      exact e2 (f' - 1) (by omega)
    · cases hv
    · cases hv

  | lambda Γ0 hΓ0 hp _ _ =>
    intro env env' hT hΓ fuel hfn v hv
    cases env with
    | Env tys vars =>
    cases env' with
    | Env tys' vars' =>
    simp only [eval] at hv
    cases hv
    obtain ⟨vs, vs', hr, h1, h2⟩ := rel_capture (vars := vars) (vars' := vars') Γ0
      (fun p hp => hΓ p.1 p.2 (hΓ0 p hp))
    exact ⟨_, 0, fun hu => by bnd hu,
        .closure Γ0 hp (by simpa [env_types] using hT) (by assumption) hr h1 h2,
      fun _ _ => by rw [eval]⟩
  | app _ _ ihf iha =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next fv hfv =>
      split at hv
      · next vs hvs =>
        obtain ⟨fv', n1, bd1, hRf, e1⟩ := ihf env env' hT hΓ fuel hfn fv hfv
        obtain ⟨t', n2, bd2, hR, e2⟩ :=
          iha env env' hT hΓ fuel hfn (.TupleV vs) (by simp only [eval, hvs])
        obtain ⟨_, vs', h1, rfl⟩ := rel_tuple_inv hR rfl
        cases h1
        cases hRf with
        | @closure Tc Γ0 ps ps' body body' ks k tys tys' vars vars' cvs cvs' hp hTc hb hr
            hv1 hv2 =>
          rw [apply] at hv
          by_cases hf0 : fuel ≤ 0
          · rw [dite_eq_left_of_eq_true (eq_true hf0)] at hv
            cases hv
          · rw [dite_eq_right_of_eq_false (eq_false hf0)] at hv
            split at hv
            · next bs hbs =>
              obtain ⟨bs', hbs', hl, hn⟩ := rel_bind_app vars vars' hR hbs
              cases n with
              | zero => omega
              | succ m =>
              obtain ⟨v', m2, bdm, hRv, e3⟩ := ihn m (Nat.lt_succ_self m) hb
                (Env.Env tys (append_env bs vars)) (Env.Env tys' (append_env bs' vars'))
                (by simpa [env_types] using hTc)
                (fun x kx hx => by
                  simp only [List.lookup_append] at hx
                  simp only [env_vars]
                  rcases Option.or_eq_some_iff.mp hx with hz | ⟨hz, hx⟩
                  · exact hl x _ hz
                  · obtain ⟨u, u', h1, h2, h3⟩ := rel_lookups hr hv1 hv2 x kx hx
                    obtain ⟨g1, g2⟩ := hn x hz
                    exact ⟨u, u', by rw [g1, h1], by rw [g2, h2], h3⟩)
                (fuel - 1) (by omega) v hv
              refine ⟨v', max (max n1 n2) (max (m2 + 1) 1),
                fun hu => by have := bd1 hu; have := bd2 hu; have := bdm rfl; omega, hRv,
                fun f' hf' => ?_⟩
              simp only [eval, e1 f' (by omega), eval_tuple_inv (e2 f' (by omega))]
              rw [apply, dite_eq_right_of_eq_false (eq_false (by omega))]
              simp only [← hp, hbs']
              exact e3 (f' - 1) (by omega)
            · cases hv
            · cases hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv

  | @forall_ Γ u ps body body' ks hk _ ihb =>
    intro env env' hT hΓ fuel hfn v hv
    cases env with
    | Env tys vars =>
    cases env' with
    | Env tys' vars' =>
    have g := params_same hB hSo hk tys tys' vars vars' hT.1 hT.2
    have inst : ∀ vs, Rel O P N K E T0 S (.tuple ks) (.TupleV vs) (.TupleV vs) → ∀ w,
        instance_ O Ps fuel (.Env tys vars) ps vs body = .Ok w →
        ∃ w' m, m ≤ max fuel 0 ∧ Rel O P N K E T0 S .bool w w' ∧
          ∀ fuel', m ≤ fuel' →
            instance_ O P fuel' (.Env tys' vars') ps vs body' = .Ok w' := by
      intro vs hg w hw
      simp only [instance_] at hw ⊢
      split at hw
      · next bs hbs =>
        obtain ⟨bs', hbs', hl, hn⟩ := rel_bind_app vars vars' hg hbs
        obtain ⟨w', m, bd, hR, e⟩ := ihb (.Env tys (append_env bs vars))
          (.Env tys' (append_env bs' vars')) (by simpa [env_types] using hT)
          (fun x kx hx => by
            simp only [env_vars]
            rcases Option.or_eq_some_iff.mp hx with hz | ⟨hz, hx⟩
            · exact hl x _ hz
            · obtain ⟨u1, u1', h1, h2, h3⟩ := hΓ x kx hx
              obtain ⟨g1, g2⟩ := hn x hz
              exact ⟨u1, u1', by rw [g1]; exact h1, by rw [g2]; exact h2, h3⟩)
          fuel hfn w hw
        exact ⟨w', m, bd rfl, hR, fun f hf => by
          rw [hbs] at hbs'; cases hbs'; exact e f hf⟩
      · cases hw
      · cases hw
    simp only [eval] at hv
    rw [hO.forall_result] at hv
    split at hv
    · next hex =>
      cases hv
      obtain ⟨vs, hvs⟩ := of_decide_eq_true hex
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hvs
      obtain ⟨w', m, bd, hR, e⟩ := inst vs ((g vs).2 hvs.1) _ hvs.2
      cases hR
      refine ⟨_, m, fun _ => bd, .bool false, fun f hf => ?_⟩
      simp only [eval]
      rw [hO.forall_result, dite_eq_left_of_eq_true (eq_true (decide_eq_true
        ⟨vs, by simp [← (g vs).1, hvs.1, e f hf]⟩))]
    · split at hv
      · cases hv
      · split at hv
        · next hall =>
          cases hv
          have hall := of_decide_eq_true hall
          have hP : ∀ vs, O.params_have_types P (.Env tys' vars') vs ps = true → ∀ f,
              max fuel 0 ≤ f →
                instance_ O P f (.Env tys' vars') ps vs body' = .Ok (.BoolV true) := by
            intro vs hg f hf
            have hg' : O.params_have_types Ps (.Env tys vars) vs ps = true := by
              rw [(g vs).1]; exact hg
            have h1 := hall vs
            simp only [hg', Bool.not_true, Bool.false_or, decide_eq_true_eq] at h1
            obtain ⟨w', m, bd, hR, e⟩ := inst vs ((g vs).2 hg') _ h1
            cases hR
            exact e f (by omega)
          refine ⟨_, max fuel 0, fun _ => Int.le_refl _, .bool true, fun f hf => ?_⟩
          simp only [eval]
          rw [hO.forall_result]
          rw [dite_eq_right_of_eq_false (eq_false (fun h => by
            obtain ⟨vs, hvs⟩ := of_decide_eq_true h
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hvs
            rw [hP vs hvs.1 f hf] at hvs
            cases hvs.2))]
          rw [dite_eq_right_of_eq_false (eq_false (fun h => by
            obtain ⟨vs, hvs⟩ := of_decide_eq_true h
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hvs
            rw [hP vs hvs.1 f hf] at hvs
            cases hvs.2))]
          rw [dite_eq_left_of_eq_true (eq_true (decide_eq_true (fun vs => by
            cases h : O.params_have_types P (.Env tys' vars') vs ps
            · simp
            · simp [hP vs h f hf])))]
        · cases hv

  | @forallUnused Γ u ps body body' hps _ ihb =>
    intro env env' hT hΓ fuel hfn v hv
    cases env with
    | Env tys vars =>
    cases env' with
    | Env tys' vars' =>
    have r1 : O.resolve tys Te = T0 := by
      have := hT.1
      simp only [hO.resolve_all, env_types, List.cons.injEq] at this
      exact this.1
    have r2 : O.resolve tys' Te = T0 := by
      have := hT.2
      simp only [hO.resolve_all, env_types, List.cons.injEq] at this
      exact this.1
    obtain ⟨vsS, hvsS⟩ := params_inhab hO hB.simple Ps tys r1 ps hps vars
    obtain ⟨vsP, hvsP⟩ := params_inhab hO hB.simple P tys' r2 ps hps vars'
    have inst : ∀ vs vs', O.params_have_types P (.Env tys' vars') vs' ps = true → ∀ w,
        instance_ O Ps fuel (.Env tys vars) ps vs body = .Ok w →
        ∃ w' m, m ≤ max fuel 0 ∧ Rel O P N K E T0 S .bool w w' ∧
          ∀ fuel', m ≤ fuel' →
            instance_ O P fuel' (.Env tys' vars') ps vs' body' = .Ok w' := by
      intro vs vs' hg w hw
      obtain ⟨bs', hbs'⟩ := bind_len (param_ids ps) vs'
        (by rw [param_ids_length, pht_len hO P _ vs' ps hg])
      simp only [instance_] at hw ⊢
      split at hw
      · next bs hbs =>
        obtain ⟨w', m, bd, hR, e⟩ := ihb (.Env tys (append_env bs vars))
          (.Env tys' (append_env bs' vars')) (by simpa [env_types] using hT)
          (fun x kx hx => by
            simp only [env_vars]
            simp only [] at hx
            split at hx
            · cases hx
            · next hxn =>
              obtain ⟨u1, u1', h1, h2, h3⟩ := hΓ x kx hx
              exact ⟨u1, u1', by rw [lookup_other hbs vars x hxn]; exact h1,
                by rw [lookup_other hbs' vars' x hxn]; exact h2, h3⟩)
          fuel hfn w hw
        exact ⟨w', m, bd rfl, hR, fun f hf => by rw [hbs']; exact e f hf⟩
      · cases hw
      · cases hw
    simp only [eval] at hv
    rw [hO.forall_result] at hv
    split at hv
    · next hex =>
      cases hv
      obtain ⟨vs, hvs⟩ := of_decide_eq_true hex
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hvs
      obtain ⟨w', m, bd, hR, e⟩ := inst vs vsP hvsP _ hvs.2
      cases hR
      refine ⟨_, m, fun _ => bd, .bool false, fun f hf => ?_⟩
      simp only [eval]
      rw [hO.forall_result, dite_eq_left_of_eq_true (eq_true (decide_eq_true
        ⟨vsP, by simp [hvsP, e f hf]⟩))]
    · split at hv
      · cases hv
      · split at hv
        · next hall =>
          cases hv
          have hall := of_decide_eq_true hall
          have h1 := hall vsS
          simp only [hvsS, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h1
          have hP : ∀ vs, O.params_have_types P (.Env tys' vars') vs ps = true → ∀ f,
              max fuel 0 ≤ f →
                instance_ O P f (.Env tys' vars') ps vs body' = .Ok (.BoolV true) := by
            intro vs hg f hf
            obtain ⟨w', m, bd, hR, e⟩ := inst vsS vs hg _ h1
            cases hR
            exact e f (by omega)
          refine ⟨_, max fuel 0, fun _ => Int.le_refl _, .bool true, fun f hf => ?_⟩
          simp only [eval]
          rw [hO.forall_result]
          rw [dite_eq_right_of_eq_false (eq_false (fun h => by
            obtain ⟨vs, hvs⟩ := of_decide_eq_true h
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hvs
            rw [hP vs hvs.1 f hf] at hvs
            cases hvs.2))]
          rw [dite_eq_right_of_eq_false (eq_false (fun h => by
            obtain ⟨vs, hvs⟩ := of_decide_eq_true h
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hvs
            rw [hP vs hvs.1 f hf] at hvs
            cases hvs.2))]
          rw [dite_eq_left_of_eq_true (eq_true (decide_eq_true (fun vs => by
            cases h : O.params_have_types P (.Env tys' vars') vs ps
            · simp
            · simp [hP vs h f hf])))]
        · cases hv

  | @uninterp Γ u f ks k es es' hf hu0 _ iha =>
    intro env env' hT hΓ fuel hfn v hv
    obtain ⟨params, body, body', Tu, hIS, hIP, hEnc, hTu⟩ := hF.2 _ _ _ hf
    obtain ⟨vs, hvs, hpos, bs, hbs, hbody⟩ := uninterp_inv hO hIS hv
    obtain ⟨t', n1, bd1, hR, e1⟩ :=
      iha env env' hT hΓ fuel hfn (.TupleV vs) (by simp only [eval, hvs])
    obtain ⟨_, vs', h1, rfl⟩ := rel_tuple_inv hR rfl
    cases h1
    obtain ⟨bs', hbs', hl⟩ := rel_bind hR hbs
    cases n with
    | zero => omega
    | succ m =>
    obtain ⟨v', m2, bdm, hRv, e2⟩ := ihn m (Nat.lt_succ_self m) hEnc
      (Env.Env [] bs) (Env.Env [] bs') (by simpa [env_types] using And.intro hTu hTu)
      (fun x k hx => hl x k hx) (fuel - 1) (by omega) v hbody
    refine ⟨v', max (max n1 (m2 + 1)) 1,
      fun hu => by have := bd1 hu; have := bdm (hu0 hu); omega, hRv, fun f' hf' => ?_⟩
    rw [uninterp_fun hO hIP (eval_tuple_inv (e1 f' (by omega))) (by omega) hbs']
    exact e2 (f' - 1) (by omega)
  | error k =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    cases hv

end Evaluation

end Inox.Encoded
