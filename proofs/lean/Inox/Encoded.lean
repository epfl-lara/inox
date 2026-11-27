/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Bags

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

open Inox.Semantics Inox.Bags

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
kinds of its parameters and the kind of its result. -/
structure Sig where
  ctors : Id → Option (Id × List (Id × Kind))
  funs : Id → Option (List Id × Ty × List Kind × Kind)

mutual
/-- Whether a kind has no functions in it. -/
def foKind : Kind → Bool
  | .fn _ _ => false
  | .tuple ks => foKinds ks
  | _ => true
def foKinds : List Kind → Bool
  | [] => true
  | k :: ks => foKind k && foKinds ks
end

/-- No constructor of the signature has a function in its fields. -/
def Sig.fo (S : Sig) : Prop :=
  ∀ c s fs, S.ctors c = some (s, fs) → foKinds (fs.map Prod.snd) = true

/-- The kind of the component `i` of a tuple, counted from 1. -/
def nthKind : List Kind → Int → Option Kind
  | [], _ => none
  | k :: ks, i => if i = 1 then some k else nthKind ks (i - 1)

/-- The kind of the field `sel` of a constructor. -/
def fieldKind : List (Id × Kind) → Id → Option Kind
  | [], _ => none
  | (f, k) :: fs, sel => if f = sel then some k else fieldKind fs sel

/-- `e'` is what the encoder makes of `e`, an expression of the kind `k`, with `Te` the type
of the elements and `Γ` the kinds of the variables. A function keeps the kinds `Γ0` of the
variables of its body other than its parameters. -/
inductive Encodes (N : Names) (S : Sig) (Te : Ty) :
    (Id → Option Kind) → Expr → Expr → Kind → Prop where
  | var {Γ : Id → Option Kind} (x : Id) (k : Kind) (h : Γ x = some k) :
      Encodes N S Te Γ (.Variable x) (.Variable x) k
  | int {Γ : Id → Option Kind} (n : Int) :
      Encodes N S Te Γ (.IntegerLiteral n) (.IntegerLiteral n) .int
  | bool {Γ : Id → Option Kind} (b : Bool) :
      Encodes N S Te Γ (.BooleanLiteral b) (.BooleanLiteral b) .bool
  | plus {Γ : Id → Option Kind} {a a' b b' : Expr} (ha : Encodes N S Te Γ a a' .int)
      (hb : Encodes N S Te Γ b b' .int) : Encodes N S Te Γ (.Plus a b) (.Plus a' b') .int
  | minus {Γ : Id → Option Kind} {a a' b b' : Expr} (ha : Encodes N S Te Γ a a' .int)
      (hb : Encodes N S Te Γ b b' .int) : Encodes N S Te Γ (.Minus a b) (.Minus a' b') .int
  | lt {Γ : Id → Option Kind} {a a' b b' : Expr} (ha : Encodes N S Te Γ a a' .int)
      (hb : Encodes N S Te Γ b b' .int) :
      Encodes N S Te Γ (.LessThan a b) (.LessThan a' b') .bool
  | gt {Γ : Id → Option Kind} {a a' b b' : Expr} (ha : Encodes N S Te Γ a a' .int)
      (hb : Encodes N S Te Γ b b' .int) :
      Encodes N S Te Γ (.GreaterThan a b) (.GreaterThan a' b') .bool
  | le {Γ : Id → Option Kind} {a a' b b' : Expr} (ha : Encodes N S Te Γ a a' .int)
      (hb : Encodes N S Te Γ b b' .int) :
      Encodes N S Te Γ (.LessEquals a b) (.LessEquals a' b') .bool
  | ge {Γ : Id → Option Kind} {a a' b b' : Expr} (ha : Encodes N S Te Γ a a' .int)
      (hb : Encodes N S Te Γ b b' .int) :
      Encodes N S Te Γ (.GreaterEquals a b) (.GreaterEquals a' b') .bool
  | eq {Γ : Id → Option Kind} {a a' b b' : Expr} {k : Kind} (hk : foKind k = true)
      (hS : S.fo) (ha : Encodes N S Te Γ a a' k) (hb : Encodes N S Te Γ b b' k) :
      Encodes N S Te Γ (.Equals a b) (.Equals a' b') .bool
  | not {Γ : Id → Option Kind} {a a' : Expr} (ha : Encodes N S Te Γ a a' .bool) :
      Encodes N S Te Γ (.Not a) (.Not a') .bool
  | andNil {Γ : Id → Option Kind} : Encodes N S Te Γ (.And []) (.And []) .bool
  | andCons {Γ : Id → Option Kind} {a a' : Expr} {as as' : List Expr}
      (ha : Encodes N S Te Γ a a' .bool) (hr : Encodes N S Te Γ (.And as) (.And as') .bool) :
      Encodes N S Te Γ (.And (a :: as)) (.And (a' :: as')) .bool
  | orNil {Γ : Id → Option Kind} : Encodes N S Te Γ (.Or []) (.Or []) .bool
  | orCons {Γ : Id → Option Kind} {a a' : Expr} {as as' : List Expr}
      (ha : Encodes N S Te Γ a a' .bool) (hr : Encodes N S Te Γ (.Or as) (.Or as') .bool) :
      Encodes N S Te Γ (.Or (a :: as)) (.Or (a' :: as')) .bool
  | implies {Γ : Id → Option Kind} {a a' b b' : Expr} (ha : Encodes N S Te Γ a a' .bool)
      (hb : Encodes N S Te Γ b b' .bool) :
      Encodes N S Te Γ (.Implies a b) (.Implies a' b') .bool
  | ite {Γ : Id → Option Kind} {c c' a a' b b' : Expr} {k : Kind}
      (hc : Encodes N S Te Γ c c' .bool) (ha : Encodes N S Te Γ a a' k)
      (hb : Encodes N S Te Γ b b' k) : Encodes N S Te Γ (.IfExpr c a b) (.IfExpr c' a' b') k
  | let_ {Γ : Id → Option Kind} (x : Id) {a a' b b' : Expr} {kx k : Kind}
      (ha : Encodes N S Te Γ a a' kx)
      (hb : Encodes N S Te (fun y => if y = x then some kx else Γ y) b b' k) :
      Encodes N S Te Γ (.Let x a b) (.Let x a' b') k
  | assume {Γ : Id → Option Kind} {p p' b b' : Expr} {k : Kind}
      (hp : Encodes N S Te Γ p p' .bool) (hb : Encodes N S Te Γ b b' k) :
      Encodes N S Te Γ (.Assume p b) (.Assume p' b') k
  | empty {Γ : Id → Option Kind} (base : Ty) :
      Encodes N S Te Γ (.FiniteBag [] base) (.ADT N.leaf [Te] []) .bag
  | add {Γ : Id → Option Kind} {b b' e e' : Expr} (hb : Encodes N S Te Γ b b' .bag)
      (he : Encodes N S Te Γ e e' .elem) :
      Encodes N S Te Γ (.BagAdd b e)
        (.ADT N.node [Te] [.IntegerLiteral 0, b', .ADT N.elem [Te] [e', .IntegerLiteral 1]]) .bag
  | union {Γ : Id → Option Kind} {a a' b b' : Expr} (ha : Encodes N S Te Γ a a' .bag)
      (hb : Encodes N S Te Γ b b' .bag) :
      Encodes N S Te Γ (.BagUnion a b) (.ADT N.node [Te] [.IntegerLiteral 0, a', b']) .bag
  | difference {Γ : Id → Option Kind} {a a' b b' : Expr} (ha : Encodes N S Te Γ a a' .bag)
      (hb : Encodes N S Te Γ b b' .bag) :
      Encodes N S Te Γ (.BagDifference a b) (.ADT N.node [Te] [.IntegerLiteral 1, a', b']) .bag
  | intersection {Γ : Id → Option Kind} {a a' b b' : Expr} (ha : Encodes N S Te Γ a a' .bag)
      (hb : Encodes N S Te Γ b b' .bag) :
      Encodes N S Te Γ (.BagIntersection a b)
        (.ADT N.node [Te] [.IntegerLiteral 2, a', b']) .bag
  | mult {Γ : Id → Option Kind} {e e' b b' : Expr} (he : Encodes N S Te Γ e e' .elem)
      (hb : Encodes N S Te Γ b b' .bag) :
      Encodes N S Te Γ (.MultiplicityInBag e b) (.FunctionInvocation N.get [Te] [b', e']) .int
  | tupleNil {Γ : Id → Option Kind} : Encodes N S Te Γ (.Tuple []) (.Tuple []) (.tuple [])
  | tupleCons {Γ : Id → Option Kind} {e e' : Expr} {es es' : List Expr} {k : Kind}
      {ks : List Kind} (he : Encodes N S Te Γ e e' k)
      (hr : Encodes N S Te Γ (.Tuple es) (.Tuple es') (.tuple ks)) :
      Encodes N S Te Γ (.Tuple (e :: es)) (.Tuple (e' :: es')) (.tuple (k :: ks))
  | tupleSelect {Γ : Id → Option Kind} {t t' : Expr} {ks : List Kind} {k : Kind} (i : Int)
      (ht : Encodes N S Te Γ t t' (.tuple ks)) (hk : nthKind ks i = some k) :
      Encodes N S Te Γ (.TupleSelect t i) (.TupleSelect t' i) k
  | adt {Γ : Id → Option Kind} {c s : Id} {fs : List (Id × Kind)} (tps tps' : List Ty)
      {es es' : List Expr} (hc : S.ctors c = some (s, fs))
      (ha : Encodes N S Te Γ (.Tuple es) (.Tuple es') (.tuple (fs.map Prod.snd))) :
      Encodes N S Te Γ (.ADT c tps es) (.ADT c tps' es') (.adt s)
  | sel {Γ : Id → Option Kind} {e e' : Expr} {s : Id} (sel : Id) {k : Kind}
      (he : Encodes N S Te Γ e e' (.adt s))
      (hk : ∀ c fs, S.ctors c = some (s, fs) → ∀ k', fieldKind fs sel = some k' → k' = k) :
      Encodes N S Te Γ (.ADTSelector e sel) (.ADTSelector e' sel) k
  | isCtor {Γ : Id → Option Kind} {e e' : Expr} {s : Id} (c : Id)
      (he : Encodes N S Te Γ e e' (.adt s)) :
      Encodes N S Te Γ (.IsConstructor e c) (.IsConstructor e' c) .bool
  | callPoly {Γ : Id → Option Kind} {f A : Id} {ks : List Kind} {k : Kind} (tps : List Ty)
      {es es' : List Expr} (hf : S.funs f = some ([A], .TypeParameter A, ks, k))
      (ha : Encodes N S Te Γ (.Tuple es) (.Tuple es') (.tuple ks)) :
      Encodes N S Te Γ (.FunctionInvocation f tps es) (.FunctionInvocation f [Te] es') k
  | callMono {Γ : Id → Option Kind} {f : Id} {Tf : Ty} {ks : List Kind} {k : Kind}
      (tps : List Ty) {es es' : List Expr} (hf : S.funs f = some ([], Tf, ks, k))
      (ha : Encodes N S Te Γ (.Tuple es) (.Tuple es') (.tuple ks)) :
      Encodes N S Te Γ (.FunctionInvocation f tps es) (.FunctionInvocation f [] es') k
  | lambda {Γ : Id → Option Kind} (Γ0 : List (Id × Kind)) {ps ps' : List Param}
      {body body' : Expr} {ks : List Kind} {k : Kind} (hΓ : ∀ p ∈ Γ0, Γ p.1 = some p.2)
      (hp : param_ids ps = param_ids ps')
      (hb : Encodes N S Te (fun x => ((param_ids ps).zip ks ++ Γ0).lookup x) body body' k) :
      Encodes N S Te Γ (.Lambda ps body) (.Lambda ps' body') (.fn ks k)
  | app {Γ : Id → Option Kind} {f f' : Expr} {es es' : List Expr} {ks : List Kind} {k : Kind}
      (hf : Encodes N S Te Γ f f' (.fn ks k))
      (ha : Encodes N S Te Γ (.Tuple es) (.Tuple es') (.tuple ks)) :
      Encodes N S Te Γ (.Application f es) (.Application f' es') k

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
      (hT : O.resolve_all tys' [Te] = [T0])
      (hb : Encodes N S Te (fun x => ((param_ids ps).zip ks ++ Γ0).lookup x) body body' k)
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
theorem rel_value_eq (hB : Base O Ps P N K E T0 S inv bi eq b1 b2) (hS : S.fo) :
    ∀ {k : Kind} {a a' : Value}, Rel O P N K E T0 S k a a' → foKind k = true →
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
        have e := ih (by simpa [foKind] using hS _ _ _ h) hr2
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

/-- The functions of the encoded program are what the encoder makes of those of the input. -/
def Funs (O : Oracle) (Ps P : Program) (N : Names) (T0 : Ty) (S : Sig) : Prop :=
  ∀ f tparams Tf ks k, S.funs f = some (tparams, Tf, ks, k) →
    ∃ params body body', FunIn f tparams params body Ps ∧ FunIn f tparams params body' P ∧
      Encodes N S Tf (fun x => (params.zip ks).lookup x) body body' k ∧
      (tparams = [] → O.resolve_all [] [Tf] = [T0])

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

theorem resolve_bind (hO : O.Sound) (A : Id) (Te : Ty) (tenv : List TypeBinding) :
    O.resolve_all (bind_types [A] [Te] tenv) [.TypeParameter A] = O.resolve_all tenv [Te] := by
  simp only [hO.resolve_all]
  rw [hO.resolve (bind_types [A] [Te] tenv) (.TypeParameter A)]
  simp [bind_types, lookup_type]

/-- An encoded expression evaluates, with enough fuel, to a value that relates to the value of
the expression. -/
theorem encodes_eval (hB : Base O Ps P N K E T0 S inv bi eq b1 b2)
    (hF : Funs O Ps P N T0 S) :
    ∀ (n : Nat) {Te : Ty} {Γ : Id → Option Kind} {e e' : Expr} {k : Kind},
      Encodes N S Te Γ e e' k →
      ∀ (env env' : Env), O.resolve_all (env_types env') [Te] = [T0] →
        (∀ x k, Γ x = some k → ∃ v v', lookup_var (env_vars env) x = .Ok v ∧
          lookup_var (env_vars env') x = .Ok v' ∧ Rel O P N K E T0 S k v v') →
        ∀ (fuel : Int), fuel ≤ n → ∀ (v : Value), eval O Ps fuel env e = .Ok v →
          ∃ (v' : Value) (m : Int), Rel O P N K E T0 S k v v' ∧
            ∀ fuel' : Int, m ≤ fuel' → eval O P fuel' env' e' = .Ok v' := by
  have hO := hB.sound
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro Te Γ e e' k h
  induction h with
  | var x k hx =>
    intro env env' hT hΓ fuel hfn v hv
    obtain ⟨w, w', h1, h2, hR⟩ := hΓ x k hx
    simp only [eval, h1] at hv
    cases hv
    exact ⟨w', 0, hR, fun _ _ => by simp only [eval, h2]⟩
  | int n =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    cases hv
    exact ⟨_, 0, .int n, fun _ _ => by simp only [eval]⟩
  | bool b =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    cases hv
    exact ⟨_, 0, .bool b, fun _ _ => by simp only [eval]⟩
  | plus _ _ iha ihb =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨_, n1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨_, n2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        cases hR1
        cases hR2
        simp only [arith_plus] at hv
        cases hv
        exact ⟨_, max n1 n2, .int _, fun f hf => by
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
        obtain ⟨_, n1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨_, n2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        cases hR1
        cases hR2
        simp only [arith_minus] at hv
        cases hv
        exact ⟨_, max n1 n2, .int _, fun f hf => by
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
        obtain ⟨_, n1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨_, n2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        cases hR1
        cases hR2
        split at hv
        · next same hsame =>
          cases hv
          exact ⟨_, max n1 n2, .bool _, fun f hf => by
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
        obtain ⟨_, n1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨_, n2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        cases hR1
        cases hR2
        split at hv
        · next same hsame =>
          cases hv
          exact ⟨_, max n1 n2, .bool _, fun f hf => by
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
        obtain ⟨_, n1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨_, n2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        cases hR1
        cases hR2
        split at hv
        · next same hsame =>
          cases hv
          exact ⟨_, max n1 n2, .bool _, fun f hf => by
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
        obtain ⟨_, n1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨_, n2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        cases hR1
        cases hR2
        split at hv
        · next same hsame =>
          cases hv
          exact ⟨_, max n1 n2, .bool _, fun f hf => by
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
        obtain ⟨va', n1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨vb', n2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        split at hv
        · next same hsame =>
          cases hv
          rw [rel_value_eq hB hS hR1 hk hR2] at hsame
          exact ⟨_, max n1 n2, .bool _, fun f hf => by
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
      obtain ⟨_, n1, hR, e1⟩ := iha env env' hT hΓ fuel hfn _ (eval_bool_ok ha)
      cases hR
      exact ⟨_, n1, .bool _, fun f hf => by simp only [eval, eval_bool, e1 f hf]⟩
    · cases hv
    · cases hv
  | andNil =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    rw [eval_and] at hv
    cases hv
    exact ⟨_, 0, .bool _, fun _ _ => by simp only [eval]; rw [eval_and]⟩
  | andCons _ _ iha ihr =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    rw [eval_and] at hv
    split at hv
    · next b hb =>
      obtain ⟨_, n1, hR, e1⟩ := iha env env' hT hΓ fuel hfn _ (eval_bool_ok hb)
      cases hR
      cases b with
      | true =>
        simp only [dite_true] at hv
        obtain ⟨v', n2, hR, e2⟩ :=
          ihr env env' hT hΓ fuel hfn v (by simp only [eval]; exact hv)
        refine ⟨v', max n1 n2, hR, fun f hf => ?_⟩
        have h2 := e2 f (by omega)
        simp only [eval] at h2 ⊢
        rw [eval_and]
        simp only [eval_bool, e1 f (by omega), dite_true, h2]
      | false =>
        simp at hv
        cases hv
        refine ⟨_, n1, .bool _, fun f hf => ?_⟩
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
    exact ⟨_, 0, .bool _, fun _ _ => by simp only [eval]; rw [eval_or]⟩
  | orCons _ _ iha ihr =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    rw [eval_or] at hv
    split at hv
    · next b hb =>
      obtain ⟨_, n1, hR, e1⟩ := iha env env' hT hΓ fuel hfn _ (eval_bool_ok hb)
      cases hR
      cases b with
      | false =>
        simp at hv
        obtain ⟨v', n2, hR, e2⟩ :=
          ihr env env' hT hΓ fuel hfn v (by simp only [eval]; exact hv)
        refine ⟨v', max n1 n2, hR, fun f hf => ?_⟩
        have h2 := e2 f (by omega)
        simp only [eval] at h2 ⊢
        rw [eval_or]
        simp [eval_bool, e1 f (by omega), h2]
      | true =>
        simp only [dite_true] at hv
        cases hv
        refine ⟨_, n1, .bool _, fun f hf => ?_⟩
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
      obtain ⟨_, n1, hR, e1⟩ := iha env env' hT hΓ fuel hfn _ (eval_bool_ok ha)
      cases hR
      cases a with
      | true =>
        simp only [dite_true] at hv
        split at hv
        · next b hb =>
          obtain ⟨_, n2, hR, e2⟩ := ihb env env' hT hΓ fuel hfn _ (eval_bool_ok hb)
          cases hR
          cases hv
          exact ⟨_, max n1 n2, .bool _, fun f hf => by
            simp [eval, eval_bool, e1 f (by omega), e2 f (by omega)]⟩
        · cases hv
        · cases hv
      | false =>
        simp at hv
        cases hv
        exact ⟨_, n1, .bool _, fun f hf => by simp [eval, eval_bool, e1 f hf]⟩
    · cases hv
    · cases hv
  | ite _ _ _ ihc iha ihb =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next c hc =>
      obtain ⟨_, n1, hR, e1⟩ := ihc env env' hT hΓ fuel hfn _ (eval_bool_ok hc)
      cases hR
      cases c with
      | true =>
        simp only [dite_true] at hv
        obtain ⟨v', n2, hR, e2⟩ := iha env env' hT hΓ fuel hfn v hv
        exact ⟨v', max n1 n2, hR, fun f hf => by
          simp [eval, eval_bool, e1 f (by omega), e2 f (by omega)]⟩
      | false =>
        simp at hv
        obtain ⟨v', n2, hR, e2⟩ := ihb env env' hT hΓ fuel hfn v hv
        exact ⟨v', max n1 n2, hR, fun f hf => by
          simp [eval, eval_bool, e1 f (by omega), e2 f (by omega)]⟩
    · cases hv
    · cases hv
  | let_ x _ _ iha ihb =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next w hw =>
      obtain ⟨w', n1, hR, e1⟩ := iha env env' hT hΓ fuel hfn w hw
      obtain ⟨v', n2, hR2, e2⟩ := ihb (env_bind env x w) (env_bind env' x w')
        (by cases env'; exact hT)
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
      exact ⟨v', max n1 n2, hR2, fun f hf => by
        simp only [eval, e1 f (by omega)]
        exact e2 f (by omega)⟩
    · cases hv
    · cases hv
  | assume _ _ ihp ihb =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next c hc =>
      obtain ⟨_, n1, hR, e1⟩ := ihp env env' hT hΓ fuel hfn _ (eval_bool_ok hc)
      cases hR
      cases c with
      | true =>
        simp only [dite_true] at hv
        obtain ⟨v', n2, hR, e2⟩ := ihb env env' hT hΓ fuel hfn v hv
        exact ⟨v', max n1 n2, hR, fun f hf => by
          simp [eval, eval_bool, e1 f (by omega), e2 f (by omega)]⟩
      | false =>
        simp at hv
    · cases hv
    · cases hv
  | empty base =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval, eval_bag_entries] at hv
    cases hv
    refine ⟨.ADTV N.leaf [T0] [], 1, .bag _ [] N.leaf [] trivial (enc_empty _)
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
        obtain ⟨vb', n1, hR1, e1⟩ := ihb env env' hT hΓ fuel hfn vb hb
        obtain ⟨ve', n2, hR2, e2⟩ := ihe env env' hT hΓ fuel hfn ve he
        cases hR1 with
        | bag t xs c args hxs henc hc =>
        cases hR2 with
        | elem _ hk =>
        simp only [bag_entries, bag_get_eq hO hB.keyS hxs hk, bag_set_eq hB.keyS hxs hk,
          bag_with] at hv
        cases hv
        refine ⟨.ADTV N.node [T0] [.IntV 0, .ADTV c [T0] args, .ADTV N.elem [T0] [ve, .IntV 1]],
          max (max n1 n2) 1, .bag _ _ N.node _ (canon_set hB.key hxs hk _)
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
        obtain ⟨va', n1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨vb', n2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        cases hR1 with
        | bag t xs c args hxs hea hc =>
        cases hR2 with
        | bag u ys c2 args2 hys heb hc2 =>
        simp only [bag_entries, bag_add_all_eq hO hB.keyS hxs hys, bag_with] at hv
        cases hv
        refine ⟨.ADTV N.node [T0] [.IntV 0, .ADTV c [T0] args, .ADTV c2 [T0] args2],
          max (max n1 n2) 1, .bag _ _ N.node _ (canon_addAll hB.key hxs hys)
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
        obtain ⟨va', n1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨vb', n2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        cases hR1 with
        | bag t xs c args hxs hea hc =>
        cases hR2 with
        | bag u ys c2 args2 hys heb hc2 =>
        simp only [bag_entries,
          bag_merge_eq hO hB.keyS .DifferenceOp hys (acc := []) trivial hxs, bag_with] at hv
        cases hv
        refine ⟨.ADTV N.node [T0] [.IntV 1, .ADTV c [T0] args, .ADTV c2 [T0] args2],
          max (max n1 n2) 1, .bag _ _ N.node _ (canon_merge hB.key _ ys (acc := []) trivial hxs)
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
        obtain ⟨va', n1, hR1, e1⟩ := iha env env' hT hΓ fuel hfn va ha
        obtain ⟨vb', n2, hR2, e2⟩ := ihb env env' hT hΓ fuel hfn vb hb
        cases hR1 with
        | bag t xs c args hxs hea hc =>
        cases hR2 with
        | bag u ys c2 args2 hys heb hc2 =>
        simp only [bag_entries,
          bag_merge_eq hO hB.keyS .IntersectionOp hys (acc := []) trivial hxs, bag_with] at hv
        cases hv
        refine ⟨.ADTV N.node [T0] [.IntV 2, .ADTV c [T0] args, .ADTV c2 [T0] args2],
          max (max n1 n2) 1, .bag _ _ N.node _ (canon_merge hB.key _ ys (acc := []) trivial hxs)
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
        obtain ⟨vb', n1, hR1, e1⟩ := ihb env env' hT hΓ fuel hfn vb hb
        obtain ⟨ve', n2, hR2, e2⟩ := ihe env env' hT hΓ fuel hfn ve he
        cases hR1 with
        | bag t xs c args hxs henc hc =>
        cases hR2 with
        | elem _ hk =>
        obtain ⟨d, hd⟩ := henc
        simp only [bag_entries, bag_get_eq hO hB.keyS hxs hk] at hv
        cases hv
        refine ⟨_, max (max n1 n2) (d + 1), .int _, fun f hf => ?_⟩
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
    exact ⟨_, 0, .tupleNil, fun _ _ => by simp only [eval, eval_list]⟩
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
          obtain ⟨w', n1, hR1, e1⟩ := ihe env env' hT hΓ fuel hfn w hw
          obtain ⟨t', n2, hR2, e2⟩ :=
            ihr env env' hT hΓ fuel hfn (.TupleV ws) (by simp only [eval, hws])
          obtain ⟨_, ws', h1, rfl⟩ := rel_tuple_inv hR2 rfl
          cases h1
          refine ⟨_, max n1 n2, .tupleCons hR1 hR2, fun f hf => ?_⟩
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
      obtain ⟨t', n1, hR, e1⟩ := iht env env' hT hΓ fuel hfn tv htv
      obtain ⟨vs, vs', rfl, rfl⟩ := rel_tuple_inv hR rfl
      simp only [] at hv
      obtain ⟨v', k2, hk2, hn, hRv⟩ := rel_nth hR hv
      rw [hk] at hk2
      cases hk2
      exact ⟨v', n1, hRv, fun f hf => by simp only [eval, e1 f hf, hn]⟩
    · cases hv
    · cases hv
  | adt tps tps' hc _ iha =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next vs hvs =>
      rw [construct_ctor (hB.ctorS _ _ _ hc)] at hv
      cases hv
      obtain ⟨t', n1, hR, e1⟩ :=
        iha env env' hT hΓ fuel hfn (.TupleV vs) (by simp only [eval, hvs])
      obtain ⟨_, vs', h1, rfl⟩ := rel_tuple_inv hR rfl
      cases h1
      exact ⟨.ADTV _ (O.resolve_all (env_types env') tps') vs', n1, .adt hc hR, fun f hf => by
        simp only [eval, eval_tuple_inv (e1 f hf), construct_ctor (hB.ctor _ _ _ hc)]⟩
    · cases hv
    · cases hv
  | sel sel _ hk ihe =>
    intro env env' hT hΓ fuel hfn v hv
    obtain ⟨w, hw⟩ := sel_inv hv
    obtain ⟨w', n1, hR, e1⟩ := ihe env env' hT hΓ fuel hfn w hw
    cases hR with
    | @adt c _ fs tps tps' vs vs' hc hr =>
    obtain ⟨hps, hsel⟩ := sel_eval (hB.ctorS _ _ _ hc) hw sel
    rw [hsel] at hv
    obtain ⟨hps', _⟩ := sel_eval (hB.ctor _ _ _ hc) (e1 n1 (Int.le_refl _)) sel
    obtain ⟨v', k2, hk2, hs', hRv⟩ := rel_select hps hps' hr hv
    cases hk c fs hc k2 hk2
    refine ⟨v', n1, hRv, fun f hf => ?_⟩
    rw [(sel_eval (hB.ctor _ _ _ hc) (e1 f hf) sel).2]
    exact hs'
  | isCtor c _ ihe =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next w hw =>
      obtain ⟨w', n1, hR, e1⟩ := ihe env env' hT hΓ fuel hfn w hw
      cases hR with
      | adt hc hr =>
      simp only [] at hv
      cases hv
      exact ⟨_, n1, .bool _, fun f hf => by simp only [eval, e1 f hf]⟩
    · cases hv
    · cases hv
  | @callPoly Γ f A ks k tps es es' hf _ iha =>
    intro env env' hT hΓ fuel hfn v hv
    obtain ⟨params, body, body', hFS, hFP, hEnc, _⟩ := hF _ _ _ _ _ hf
    simp only [eval] at hv
    split at hv
    · next vs hvs =>
      obtain ⟨hpos, bs, hbs, hbody⟩ := call_inv hFS hv
      obtain ⟨t', n1, hR, e1⟩ :=
        iha env env' hT hΓ fuel hfn (.TupleV vs) (by simp only [eval, hvs])
      obtain ⟨_, vs', h1, rfl⟩ := rel_tuple_inv hR rfl
      cases h1
      obtain ⟨bs', hbs', hl⟩ := rel_bind hR hbs
      cases n with
      | zero => omega
      | succ m =>
      obtain ⟨v', m2, hRv, e2⟩ := ihn m (Nat.lt_succ_self m) hEnc
        (Env.Env (bind_types [A] tps (env_types env)) bs)
        (Env.Env (bind_types [A] [Te] (env_types env')) bs')
        (by simpa [env_types, resolve_bind hO] using hT)
        (fun x k hx => hl x k hx) (fuel - 1) (by omega) v hbody
      refine ⟨v', max (max n1 (m2 + 1)) 1, hRv, fun f' hf' => ?_⟩
      simp only [eval, eval_tuple_inv (e1 f' (by omega))]
      rw [call_fun hFP (by omega) _ _ hbs']
      exact e2 (f' - 1) (by omega)
    · cases hv
    · cases hv
  | @callMono Γ f Tf ks k tps es es' hf _ iha =>
    intro env env' hT hΓ fuel hfn v hv
    obtain ⟨params, body, body', hFS, hFP, hEnc, hTf⟩ := hF _ _ _ _ _ hf
    simp only [eval] at hv
    split at hv
    · next vs hvs =>
      obtain ⟨hpos, bs, hbs, hbody⟩ := call_inv hFS hv
      obtain ⟨t', n1, hR, e1⟩ :=
        iha env env' hT hΓ fuel hfn (.TupleV vs) (by simp only [eval, hvs])
      obtain ⟨_, vs', h1, rfl⟩ := rel_tuple_inv hR rfl
      cases h1
      obtain ⟨bs', hbs', hl⟩ := rel_bind hR hbs
      cases n with
      | zero => omega
      | succ m =>
      obtain ⟨v', m2, hRv, e2⟩ := ihn m (Nat.lt_succ_self m) hEnc
        (Env.Env (bind_types [] tps (env_types env)) bs)
        (Env.Env (bind_types [] [] (env_types env')) bs')
        (by simpa [env_types, bind_types] using hTf rfl)
        (fun x k hx => hl x k hx) (fuel - 1) (by omega) v hbody
      refine ⟨v', max (max n1 (m2 + 1)) 1, hRv, fun f' hf' => ?_⟩
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
    exact ⟨_, 0, .closure Γ0 hp (by simpa [env_types] using hT) (by assumption) hr h1 h2,
      fun _ _ => by rw [eval]⟩
  | app _ _ ihf iha =>
    intro env env' hT hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next fv hfv =>
      split at hv
      · next vs hvs =>
        obtain ⟨fv', n1, hRf, e1⟩ := ihf env env' hT hΓ fuel hfn fv hfv
        obtain ⟨t', n2, hR, e2⟩ :=
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
              obtain ⟨v', m2, hRv, e3⟩ := ihn m (Nat.lt_succ_self m) hb
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
              refine ⟨v', max (max n1 n2) (max (m2 + 1) 1), hRv, fun f' hf' => ?_⟩
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

end Evaluation

end Inox.Encoded
