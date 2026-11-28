/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Lowered

/-!
# The steps of the simplifications

Before it lowers an expression, Inox simplifies it, and the certificate records each step of the
simplification: its rule, the position of the subterm that it rewrites, and what the subterm
becomes. A step may only refine its subterm: wherever the subterm has a value, what it becomes
has the same value (`Refines`), under the facts that hold where evaluation reaches the position.

Rewriting a subterm into one that refines it refines the whole expression (`rewriteAt_refines`),
so that a sequence of steps of which each refines its subterm refines the expression that it
starts from (`stepsApply_refines`). The facts of a position are the conditions that hold where
evaluation reaches it, and in the body of a let, that its variable has the value of its binding.
In the body of a quantifier, whose instances refine those of the body that it is rewritten from
(`refines_Forall`), they are that its parameters of integers and booleans have primitive values
(`paramFacts`). In the body of a lambda that is an operand of an equality, a step must also have
its converse, so that the body has the same values as the one that it is rewritten from
(`revCheck`, `rewriteAt_rev`): functions are compared by their values (`refines_EqLam`).

The rules that are checked here:
- `logic`, three-valued propositional reasoning over the atoms of the subterm, under the facts
  of the path to it (`logicCheck`): the atoms are the operands of the connectives that are not
  connectives themselves, `(< a b)` is the negation of `(>= a b)` and `(<= a b)` that of
  `(> a b)`, and every value of the atoms (`true`, `false` or no value) where the facts hold,
  and where the subterm has a value, gives what it becomes the same value. The variables of the
  lets around the subterm are first their values (`unlet`, by `subst_eval`). A conditional
  whose branches are the same is its branch.
- `select`, the selection of a field of a construction is the argument of the field.
- `bind`, a let of a subterm that the term always evaluates, to a variable that it doesn't
  mention.
- `expand`, a variable is the value of its let.
- `arith`, a product with a factor `0` is `0`, a sum with an operand `0`, a difference with a
  right operand `0` and a product with a factor `1` are the other operand, and an equality of an
  expression with itself is `true` where its value is of a primitive type, which the equality of
  the semantics compares by identity (`value_eq_refl`): a literal, an arithmetic operation, an
  equality, or a free variable of the input (a fact `prim`), and an equality of a variable of
  a datatype without an equality of its own with itself is `true` (`typed_refl`).
- `evaluate`, a ground term of literals, arithmetic, comparisons, negations, conditionals and
  concatenations of strings is its value, two lambdas of a parameter of the integers are
  different where their bodies are different values at an integer around their literals
  (`lamNeCheck`), and two lambdas whose bodies are the same up to the name of their parameter,
  of the integers or the Booleans, of a primitive value, are equal (`alphaCheck`).
- `eta`, the construction of the fields of a variable of a datatype, in their order, is the
  variable, where its first field is of no other constructor: a free variable of the input has a
  value of its type (a fact `typed`), and the selections of its fields are its fields.
- `unused`, a quantifier, universal or existential, over parameters whose types have values, as
  integers, booleans and functions into them do (`witness`), of a ground body, is the body.
-/

namespace Inox.Simplified

open Inox.Semantics
open Inox.Lowered (exprEq exprEq_eq pick pick_eval pick_eq construct_ok)

mutual
/-- The type `T` where the type parameters of `σ` are their types. -/
def substTy (σ : List (Id × Ty)) : Ty → Ty
  | .TypeParameter a => (σ.lookup a).getD (.TypeParameter a)
  | .ADTType s args => .ADTType s (substTys σ args)
  | T => T
/-- The types `Ts` where the type parameters of `σ` are their types. -/
def substTys (σ : List (Id × Ty)) : List Ty → List Ty
  | [] => []
  | T :: Ts => substTy σ T :: substTys σ Ts
end

/-- The fields `fs` where the type parameters of `σ` are their types. -/
def substParams (σ : List (Id × Ty)) : List Param → List Param
  | [] => []
  | .Param f T :: fs => .Param f (substTy σ T) :: substParams σ fs

mutual
theorem substTy_nil : ∀ T : Ty, substTy [] T = T
  | .TypeParameter a => by simp [substTy]
  | .ADTType s args => by simp only [substTy, substTys_nil args]
  | .IntegerType | .BooleanType | .UnitType | .CharType | .RealType | .StringType
  | .BVType _ _ | .FPType _ _ | .RoundingModeType | .TupleType _ | .SetType _ | .BagType _
  | .MapType _ _ | .FunctionType _ _ | .RefinementType _ _ _ | .PropType | .PiType _ _
  | .SigmaType _ _ => rfl
theorem substTys_nil : ∀ Ts : List Ty, substTys [] Ts = Ts
  | [] => rfl
  | T :: Ts => by simp only [substTys, substTy_nil T, substTys_nil Ts]
end

theorem substParams_nil : ∀ fs : List Param, substParams [] fs = fs
  | [] => rfl
  | .Param _ T :: fs => by simp [substParams, substTy_nil T, substParams_nil fs]

theorem substParams_length (σ : List (Id × Ty)) :
    ∀ fs : List Param, (substParams σ fs).length = fs.length
  | [] => rfl
  | .Param _ _ :: fs => by simp [substParams, substParams_length σ fs]

mutual
/-- `v` is a value of the type `T` for the constructors `cs` and the sorts `ss`: an integer, a
boolean, a real, a bit-vector, or a construction of a datatype, of the type arguments of the
type, whose fields are of their types, where the type parameters of the datatype are its type
arguments. -/
inductive OfTy (cs : List Constructor) (ss : List ADTSort) : Ty → Value → Prop where
  | int (i : Int) : OfTy cs ss .IntegerType (.IntV i)
  | bool (b : Bool) : OfTy cs ss .BooleanType (.BoolV b)
  | real {n d : Int} (h : ∃ q : _root_.Rat, n = q.num ∧ d = q.den) :
      OfTy cs ss .RealType (.RealV n d)
  | adt {c s : Id} {tps : List Ty} {fs : List Param} {vs : List Value} {tparams : List Id}
      {inv eq : Option Id} (hc : lookup_ctor cs c = .Ok (.Constructor c s fs))
      (hs : lookup_sort ss s = .Ok (.Sort s tparams inv eq)) (hl : tparams.length = tps.length)
      (hvs : OfTys cs ss (substParams (tparams.zip tps) fs) vs) :
      OfTy cs ss (.ADTType s tps) (.ADTV c tps vs)
  | bv {s : Bool} {w x : Int} (h : 0 < w ∧ 0 ≤ x ∧ x < 2 ^ w.toNat) :
      OfTy cs ss (.BVType s w) (.BVV s w x)
/-- The values `vs` are of the types of the fields `fs`, position by position. -/
inductive OfTys (cs : List Constructor) (ss : List ADTSort) :
    List Param → List Value → Prop where
  | nil : OfTys cs ss [] []
  | cons {f : Id} {T : Ty} {fs : List Param} {v : Value} {vs : List Value} (h : OfTy cs ss T v)
      (hr : OfTys cs ss fs vs) : OfTys cs ss (.Param f T :: fs) (v :: vs)
end

/-- The constructors of a program. -/
def ctorsOf : Program → List Constructor
  | .Program _ cs _ _ _ => cs

/-- The sorts of a program. -/
def sortsOf : Program → List ADTSort
  | .Program _ _ ss _ _ => ss

/-- A fact that holds where evaluation reaches a position: an expression is `true`, the
variable `x` has the value of the expression `v`, that of its let, the variable `x` has a
value of a primitive type, or the variable `x` has a value of the type `T`, as a free variable
of the input does. -/
inductive Fact where
  | holds (e : Expr)
  | binds (x : Id) (v : Expr)
  | prim (x : Id)
  | typed (x : Id) (T : Ty)

/-- The expression of a fact that an expression is `true`. -/
def Fact.expr? : Fact → Option Expr
  | .holds e => some e
  | _ => none

/-- A value of a primitive type, which the equality of the semantics compares by identity. -/
def primValue : Value → Bool
  | .IntV _ | .BoolV _ | .UnitV | .CharV _ | .RealV _ _ | .StringV _ | .BVV _ _ _ => true
  | _ => false

section
variable (O : Oracle) (P : Program)

/-- The fact holds in `env`. -/
def Fact.Holds (fuel : Int) (env : Env) : Fact → Prop
  | .holds e => eval O P fuel env e = .Ok (.BoolV true)
  | .binds x v => ∃ w, lookup_var (env_vars env) x = .Ok w ∧ eval O P fuel env v = .Ok w
  | .prim x => ∃ w, lookup_var (env_vars env) x = .Ok w ∧ primValue w = true
  | .typed x T => ∃ w, lookup_var (env_vars env) x = .Ok w ∧ OfTy (ctorsOf P) (sortsOf P) T w

/-- `t'` refines `t` under the facts `Fs`: in every environment where the facts hold, wherever
`t` has a value, `t'` has the same value with the same fuel. -/
def Refines (Fs : List Fact) (t t' : Expr) : Prop :=
  ∀ (fuel : Int) (env : Env) (v : Value), (∀ f ∈ Fs, f.Holds O P fuel env) →
    eval O P fuel env t = .Ok v → eval O P fuel env t' = .Ok v

end

/-! ## Three-valued logic -/

/-- The Boolean that a result is, if it is one. -/
def boolOf : Result Value → Option Bool
  | .Ok (.BoolV b) => some b
  | _ => none

/-- The value of a proposition, where `ρ` gives those of its atoms: `some none` where it has
none, and `none` where `n` is not deep enough. -/
def aeval (ρ : Expr → Option Bool) : Nat → Expr → Option (Option Bool)
  | 0, _ => none
  | n + 1, e =>
    match e with
    | .BooleanLiteral b => some (some b)
    | .Not a => (aeval ρ n a).map (·.map (!·))
    | .And [] => some (some true)
    | .And (a :: es) =>
      match aeval ρ n a with
      | some (some true) => aeval ρ n (.And es)
      | some (some false) => some (some false)
      | some none => some none
      | none => none
    | .Or [] => some (some false)
    | .Or (a :: es) =>
      match aeval ρ n a with
      | some (some true) => some (some true)
      | some (some false) => aeval ρ n (.Or es)
      | some none => some none
      | none => none
    | .Implies a b =>
      match aeval ρ n a with
      | some (some true) => aeval ρ n b
      | some (some false) => some (some true)
      | some none => some none
      | none => none
    | .IfExpr c a b =>
      match aeval ρ n c with
      | some (some true) => aeval ρ n a
      | some (some false) => aeval ρ n b
      | some none => some none
      | none => none
    | .Assume p a =>
      match aeval ρ n p with
      | some (some true) => aeval ρ n a
      | some (some false) => some none
      | some none => some none
      | none => none
    | .LessThan a b => some ((ρ (.GreaterEquals a b)).map (!·))
    | .LessEquals a b => some ((ρ (.GreaterThan a b)).map (!·))
    | e => some (ρ e)

/-- The atoms that `aeval` gives values to in `e`, `n` deep. -/
def atoms : Nat → Expr → List Expr
  | 0, _ => []
  | n + 1, e =>
    match e with
    | .BooleanLiteral _ => []
    | .Not a => atoms n a
    | .And [] => []
    | .And (a :: es) => atoms n a ++ atoms n (.And es)
    | .Or [] => []
    | .Or (a :: es) => atoms n a ++ atoms n (.Or es)
    | .Implies a b => atoms n a ++ atoms n b
    | .IfExpr c a b => atoms n c ++ atoms n a ++ atoms n b
    | .Assume p a => atoms n p ++ atoms n a
    | .LessThan a b => [.GreaterEquals a b]
    | .LessEquals a b => [.GreaterThan a b]
    | e => [e]

theorem aeval_congr {ρ ρ' : Expr → Option Bool} :
    ∀ n e, (∀ a ∈ atoms n e, ρ a = ρ' a) → aeval ρ n e = aeval ρ' n e
  | 0, _, _ => rfl
  | n + 1, e, h => by
    have ih := aeval_congr (ρ := ρ) (ρ' := ρ') n
    unfold atoms at h
    unfold aeval
    split <;> simp_all

theorem ok_of_boolOf {r : Result Value} {b : Bool} (h : boolOf r = some b) :
    r = .Ok (.BoolV b) := by
  rcases r with ((_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) | _ | _) <;>
    simp_all [boolOf]

section
variable {O : Oracle} {P : Program}

/-- What `aeval` gives a proposition where its atoms have their values in `env` is its value. -/
theorem aeval_sound (fuel : Int) (env : Env) :
    ∀ n e r, aeval (fun a => boolOf (eval O P fuel env a)) n e = some r →
      boolOf (eval O P fuel env e) = r
  | 0, _, _, h => by simp [aeval] at h
  | n + 1, e, r, h => by
    have ih := aeval_sound fuel env n
    unfold aeval at h
    split at h
    · cases h; simp [eval, boolOf]
    · next a =>
      obtain ⟨r0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [← ih a r0 h0]
      simp only [eval, eval_bool]
      cases eval O P fuel env a with
      | Ok v => cases v <;> simp [boolOf]
      | Stuck => simp [boolOf]
      | OutOfFuel => simp [boolOf]
    · cases h; simp [eval, eval_and, boolOf]
    · next a es =>
      split at h
      · next h1 =>
        have hr := ih (.And es) r h
        simp only [eval] at hr ⊢
        rw [eval_and]
        simp only [eval_bool, ok_of_boolOf (ih a _ h1)]
        simpa using hr
      · next h1 =>
        cases h
        simp only [eval]
        rw [eval_and]
        simp [eval_bool, ok_of_boolOf (ih a _ h1), boolOf]
      · next h1 =>
        cases h
        have ha := ih a _ h1
        simp only [eval]
        rw [eval_and]
        simp only [eval_bool]
        revert ha
        cases eval O P fuel env a with
        | Ok v => cases v <;> simp [boolOf]
        | Stuck => simp [boolOf]
        | OutOfFuel => simp [boolOf]
      · cases h
    · cases h; simp [eval, eval_or, boolOf]
    · next a es =>
      split at h
      · next h1 =>
        cases h
        simp only [eval]
        rw [eval_or]
        simp [eval_bool, ok_of_boolOf (ih a _ h1), boolOf]
      · next h1 =>
        have hr := ih (.Or es) r h
        simp only [eval] at hr ⊢
        rw [eval_or]
        simp only [eval_bool, ok_of_boolOf (ih a _ h1)]
        simpa using hr
      · next h1 =>
        cases h
        have ha := ih a _ h1
        simp only [eval]
        rw [eval_or]
        simp only [eval_bool]
        revert ha
        cases eval O P fuel env a with
        | Ok v => cases v <;> simp [boolOf]
        | Stuck => simp [boolOf]
        | OutOfFuel => simp [boolOf]
      · cases h
    · next a b =>
      split at h
      · next h1 =>
        have hb := ih b r h
        simp only [eval, eval_bool, ok_of_boolOf (ih a _ h1)]
        revert hb
        cases eval O P fuel env b with
        | Ok v => cases v <;> simp [boolOf]
        | Stuck => simp [boolOf]
        | OutOfFuel => simp [boolOf]
      · next h1 =>
        cases h
        simp [eval, eval_bool, ok_of_boolOf (ih a _ h1), boolOf]
      · next h1 =>
        cases h
        have ha := ih a _ h1
        simp only [eval, eval_bool]
        revert ha
        cases eval O P fuel env a with
        | Ok v => cases v <;> simp [boolOf]
        | Stuck => simp [boolOf]
        | OutOfFuel => simp [boolOf]
      · cases h
    · next c a b =>
      split at h
      · next h1 =>
        simp only [eval, eval_bool, ok_of_boolOf (ih c _ h1)]
        simpa using ih a r h
      · next h1 =>
        simp only [eval, eval_bool, ok_of_boolOf (ih c _ h1)]
        simpa using ih b r h
      · next h1 =>
        cases h
        have hc := ih c _ h1
        simp only [eval, eval_bool]
        revert hc
        cases eval O P fuel env c with
        | Ok v => cases v <;> simp [boolOf]
        | Stuck => simp [boolOf]
        | OutOfFuel => simp [boolOf]
      · cases h
    · next p a =>
      split at h
      · next h1 =>
        simp only [eval, eval_bool, ok_of_boolOf (ih p _ h1)]
        simpa using ih a r h
      · next h1 =>
        cases h
        simp [eval, eval_bool, ok_of_boolOf (ih p _ h1), boolOf]
      · next h1 =>
        cases h
        have hp := ih p _ h1
        simp only [eval, eval_bool]
        revert hp
        cases eval O P fuel env p with
        | Ok v => cases v <;> simp [boolOf]
        | Stuck => simp [boolOf]
        | OutOfFuel => simp [boolOf]
      · cases h
    · next a b =>
      cases h
      simp only [eval, arith_le]
      cases eval O P fuel env a with
      | Ok va =>
        cases eval O P fuel env b with
        | Ok vb =>
          cases hx : arith_lt va vb <;> simp [boolOf, hx]
        | Stuck => simp [boolOf]
        | OutOfFuel => simp [boolOf]
      | Stuck => simp [boolOf]
      | OutOfFuel => simp [boolOf]
    · next a b =>
      cases h
      simp only [eval, arith_le]
      cases eval O P fuel env a with
      | Ok va =>
        cases eval O P fuel env b with
        | Ok vb =>
          cases hx : arith_lt vb va <;> simp [boolOf, hx]
        | Stuck => simp [boolOf]
        | OutOfFuel => simp [boolOf]
      | Stuck => simp [boolOf]
      | OutOfFuel => simp [boolOf]
    · cases h; rfl

end

/-- Whether every value of `e` is a Boolean, `n` deep. -/
def boolShaped : Nat → Expr → Bool
  | 0, _ => false
  | n + 1, e =>
    match e with
    | .BooleanLiteral _ => true
    | .Not _ => true
    | .And _ => true
    | .Or _ => true
    | .Implies _ _ => true
    | .LessThan _ _ => true
    | .GreaterThan _ _ => true
    | .LessEquals _ _ => true
    | .GreaterEquals _ _ => true
    | .Equals _ _ => true
    | .IsConstructor _ _ => true
    | .IfExpr _ a b => boolShaped n a && boolShaped n b
    | .Assume _ a => boolShaped n a
    | _ => false

section
variable {O : Oracle} {P : Program}

theorem eval_and_bool (fuel : Int) (env : Env) :
    ∀ (es : List Expr) {v : Value}, eval_and O P fuel env es = .Ok v → ∃ b, v = .BoolV b
  | [], v, h => by simp [eval_and] at h; exact ⟨true, h.symm⟩
  | a :: es, v, h => by
    rw [eval_and] at h
    split at h
    · split at h
      · exact eval_and_bool fuel env es h
      · cases h; exact ⟨false, rfl⟩
    · cases h
    · cases h

theorem eval_or_bool (fuel : Int) (env : Env) :
    ∀ (es : List Expr) {v : Value}, eval_or O P fuel env es = .Ok v → ∃ b, v = .BoolV b
  | [], v, h => by simp [eval_or] at h; exact ⟨false, h.symm⟩
  | a :: es, v, h => by
    rw [eval_or] at h
    split at h
    · split at h
      · cases h; exact ⟨true, rfl⟩
      · exact eval_or_bool fuel env es h
    · cases h
    · cases h

/-- The values of an expression of Boolean shape are Booleans. -/
theorem boolShaped_bool (fuel : Int) (env : Env) :
    ∀ n e {v : Value}, boolShaped n e = true → eval O P fuel env e = .Ok v → ∃ b, v = .BoolV b
  | 0, _, _, h, _ => by simp [boolShaped] at h
  | n + 1, e, v, h, hv => by
    have ih := boolShaped_bool fuel env n
    unfold boolShaped at h
    split at h
    · simp only [eval] at hv; cases hv; exact ⟨_, rfl⟩
    · simp only [eval] at hv
      repeat' (split at hv)
      all_goals first | (cases hv; exact ⟨_, rfl⟩) | cases hv
    · simp only [eval] at hv; exact eval_and_bool fuel env _ hv
    · simp only [eval] at hv; exact eval_or_bool fuel env _ hv
    all_goals try (simp only [eval] at hv
                   repeat' (split at hv)
                   all_goals first | (cases hv; exact ⟨_, rfl⟩) | cases hv
                   done)
    · next c a b =>
      simp only [Bool.and_eq_true] at h
      simp only [eval] at hv
      split at hv
      · split at hv
        · exact ih a h.1 hv
        · exact ih b h.2 hv
      · cases hv
      · cases hv
    · next p a =>
      simp only [eval] at hv
      split at hv
      · split at hv
        · exact ih a h hv
        · cases hv
      · cases hv
      · cases hv
    · cases h

end

/-- All the lists of `k` values of atoms. -/
def assigns : Nat → List (List (Option Bool))
  | 0 => [[]]
  | k + 1 => (assigns k).flatMap fun l => [none :: l, some true :: l, some false :: l]

theorem mem_assigns : ∀ (vals : List (Option Bool)), vals ∈ assigns vals.length
  | [] => by simp [assigns]
  | v :: vs => by
    simp only [assigns, List.length_cons, List.mem_flatMap]
    refine ⟨vs, mem_assigns vs, ?_⟩
    rcases v with _ | _ | _ <;> simp

/-- The value of the atom `a` in `A`, those of the atoms that `A` lists. -/
def lookupAtom (A : List (Expr × Option Bool)) (a : Expr) : Option Bool :=
  match A.find? (fun p => exprEq 1000 p.1 a) with
  | some p => p.2
  | none => none

/-- `l` without the expressions that it has before. -/
def dedup (l : List Expr) : List Expr :=
  l.foldl (fun acc a => if acc.any (exprEq 1000 · a) then acc else acc ++ [a]) []

/-- Whether `t'` refines `t` under the facts `Fs` in three-valued logic: `t` is of Boolean shape,
the atoms of the terms are told apart, and wherever the atoms have values under which the facts
are `true` and `t` has a value, `t'` has the same. -/
def logicCheck (Fs : List Expr) (t t' : Expr) : Bool :=
  let all := Fs.flatMap (atoms 1000) ++ atoms 1000 t ++ atoms 1000 t'
  let A := dedup all
  boolShaped 1000 t &&
  all.all (fun a => A.any fun b => exprEq 1000 b a) &&
  (assigns A.length).all fun vals =>
    let ρ := lookupAtom (A.zip vals)
    match aeval ρ 1000 t with
    | some (some b) =>
      Fs.all (fun f => (aeval ρ 1000 f).isSome) &&
        (!(Fs.all fun f => aeval ρ 1000 f == some (some true)) ||
          aeval ρ 1000 t' == some (some b))
    | some none => true
    | none => false

theorem zip_map_self (f : Expr → Option Bool) :
    ∀ A : List Expr, A.zip (A.map f) = A.map fun a => (a, f a)
  | [] => rfl
  | a :: A => by simp [zip_map_self f A]

theorem lookupAtom_zip {f : Expr → Option Bool} {A : List Expr} {a : Expr}
    (h : A.any (fun b => exprEq 1000 b a) = true) : lookupAtom (A.zip (A.map f)) a = f a := by
  unfold lookupAtom
  rw [zip_map_self]
  split
  · next p hp =>
    have hm := List.mem_of_find?_eq_some hp
    have he := exprEq_eq _ _ _ (by simpa using List.find?_some hp)
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
    simp only at he ⊢
    rw [he]
  · next hn =>
    exfalso
    obtain ⟨b, hb, hab⟩ := List.any_eq_true.mp h
    have := List.find?_eq_none.mp hn (b, f b) (List.mem_map.mpr ⟨b, hb, rfl⟩)
    simp_all

section
variable {O : Oracle} {P : Program}

theorem logicCheck_refines {Gs : List Fact} {t t' : Expr}
    (h : logicCheck (Gs.filterMap Fact.expr?) t t' = true) : Refines O P Gs t t' := by
  intro fuel env v hGs hv
  generalize hFs' : Gs.filterMap Fact.expr? = Fs at h
  have hFs : ∀ f ∈ Fs, eval O P fuel env f = .Ok (.BoolV true) := by
    intro f hf
    rw [← hFs'] at hf
    obtain ⟨g, hg, he⟩ := List.mem_filterMap.mp hf
    cases g with
    | holds e => cases he; exact hGs _ hg
    | binds _ _ => cases he
    | prim _ => cases he
    | typed _ _ => cases he
  unfold logicCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hshape, hall⟩, hvals⟩ := h
  obtain ⟨b, rfl⟩ := boolShaped_bool fuel env _ _ hshape hv
  generalize hL : Fs.flatMap (atoms 1000) ++ atoms 1000 t ++ atoms 1000 t' = L at hall hvals
  generalize hA : dedup L = A at hall hvals
  let val := fun a => boolOf (eval O P fuel env a)
  have hρ : ∀ a ∈ L, lookupAtom (A.zip (A.map val)) a = val a :=
    fun a ha => lookupAtom_zip (hall a ha)
  have hc := hvals (A.map val) (by have := mem_assigns (A.map val); rwa [List.length_map] at this)
  have ht : aeval (lookupAtom (A.zip (A.map val))) 1000 t = aeval val 1000 t :=
    aeval_congr _ _ fun a ha => hρ a (by rw [← hL]; simp [ha])
  have ht' : aeval (lookupAtom (A.zip (A.map val))) 1000 t' = aeval val 1000 t' :=
    aeval_congr _ _ fun a ha => hρ a (by rw [← hL]; simp [ha])
  have hf : ∀ f ∈ Fs, aeval (lookupAtom (A.zip (A.map val))) 1000 f = aeval val 1000 f := by
    intro f hf
    refine aeval_congr _ _ fun a ha => hρ a ?_
    rw [← hL]
    simp only [List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl ⟨f, hf, ha⟩)
  simp only [ht] at hc
  have hb : boolOf (eval O P fuel env t) = some b := by rw [hv]; rfl
  split at hc
  · next b' hb' =>
    have := aeval_sound fuel env _ _ _ hb'
    rw [hb] at this
    cases this
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true,
      beq_iff_eq] at hc
    obtain ⟨hsome, hc⟩ := hc
    rcases hc with hc | hc
    · exfalso
      obtain ⟨f, hfm, hne⟩ := List.all_eq_false.mp hc
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hsome f hfm)
      rw [hf f hfm] at hr
      have := aeval_sound fuel env _ _ _ hr
      rw [hFs f hfm] at this
      rw [hf f hfm, hr, ← this] at hne
      simp [boolOf] at hne
    · rw [ht'] at hc
      exact ok_of_boolOf (aeval_sound fuel env _ _ _ hc)
  · next hn =>
    have := aeval_sound fuel env _ _ _ hn
    rw [hb] at this
    cases this
  · cases hc

end


/-! ## Substitution -/

/-- `e` where the variable `x` is the expression `w`, for the expressions without binders, `n`
deep, or nothing. -/
def subst (x : Id) (w : Expr) : Nat → Expr → Option Expr
  | 0, _ => none
  | n + 1, e =>
    match e with
    | .Variable y => some (if y = x then w else .Variable y)
    | .IntegerLiteral i => some (.IntegerLiteral i)
    | .BooleanLiteral b => some (.BooleanLiteral b)
    | .FractionLiteral a b => some (.FractionLiteral a b)
    | .Error => some .Error
    | .Not a => (subst x w n a).map .Not
    | .UMinus a => (subst x w n a).map .UMinus
    | .IsConstructor a c => (subst x w n a).map (.IsConstructor · c)
    | .ADTSelector a f => (subst x w n a).map (.ADTSelector · f)
    | .Plus a b =>
      match subst x w n a, subst x w n b with
      | some a', some b' => some (.Plus a' b')
      | _, _ => none
    | .Minus a b =>
      match subst x w n a, subst x w n b with
      | some a', some b' => some (.Minus a' b')
      | _, _ => none
    | .Times a b =>
      match subst x w n a, subst x w n b with
      | some a', some b' => some (.Times a' b')
      | _, _ => none
    | .Division a b =>
      match subst x w n a, subst x w n b with
      | some a', some b' => some (.Division a' b')
      | _, _ => none
    | .Remainder a b =>
      match subst x w n a, subst x w n b with
      | some a', some b' => some (.Remainder a' b')
      | _, _ => none
    | .Modulo a b =>
      match subst x w n a, subst x w n b with
      | some a', some b' => some (.Modulo a' b')
      | _, _ => none
    | .LessThan a b =>
      match subst x w n a, subst x w n b with
      | some a', some b' => some (.LessThan a' b')
      | _, _ => none
    | .GreaterThan a b =>
      match subst x w n a, subst x w n b with
      | some a', some b' => some (.GreaterThan a' b')
      | _, _ => none
    | .LessEquals a b =>
      match subst x w n a, subst x w n b with
      | some a', some b' => some (.LessEquals a' b')
      | _, _ => none
    | .GreaterEquals a b =>
      match subst x w n a, subst x w n b with
      | some a', some b' => some (.GreaterEquals a' b')
      | _, _ => none
    | .Equals a b =>
      match subst x w n a, subst x w n b with
      | some a', some b' => some (.Equals a' b')
      | _, _ => none
    | .Implies a b =>
      match subst x w n a, subst x w n b with
      | some a', some b' => some (.Implies a' b')
      | _, _ => none
    | .Assume a b =>
      match subst x w n a, subst x w n b with
      | some a', some b' => some (.Assume a' b')
      | _, _ => none
    | .IfExpr c a b =>
      match subst x w n c, subst x w n a, subst x w n b with
      | some c', some a', some b' => some (.IfExpr c' a' b')
      | _, _, _ => none
    | .And es => (es.mapM (subst x w n)).map .And
    | .Or es => (es.mapM (subst x w n)).map .Or
    | .FunctionInvocation f tps es => (es.mapM (subst x w n)).map (.FunctionInvocation f tps)
    | .ADT c tps es => (es.mapM (subst x w n)).map (.ADT c tps)
    | _ => none

theorem env_types_bind (env : Env) (x : Id) (v : Value) :
    env_types (env_bind env x v) = env_types env := by
  cases env; rfl

section
variable {O : Oracle} {P : Program}

theorem construct_bind (fuel : Int) (env : Env) (x : Id) (v : Value) (c : Id) (tps : List Ty)
    (vs : List Value) :
    construct O P fuel (env_bind env x v) c tps vs = construct O P fuel env c tps vs := by
  rw [construct, construct, env_types_bind]

theorem subst_list {x : Id} {w : Expr} {n : Nat} {fuel : Int} {env env' : Env}
    (ih : ∀ e e', subst x w n e = some e' → eval O P fuel env' e = eval O P fuel env e') :
    ∀ (es es' : List Expr), es.mapM (subst x w n) = some es' →
      eval_list O P fuel env' es = eval_list O P fuel env es' ∧
      eval_and O P fuel env' es = eval_and O P fuel env es' ∧
      eval_or O P fuel env' es = eval_or O P fuel env es'
  | [], es', h => by
    simp at h; subst h
    refine ⟨?_, ?_, ?_⟩
    · rw [eval_list, eval_list]
    · rw [eval_and, eval_and]
    · rw [eval_or, eval_or]
  | a :: as, es', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨a', ha, as', has, rfl⟩ := h
    obtain ⟨h1, h2, h3⟩ := subst_list ih as as' has
    have hae := ih a a' ha
    refine ⟨?_, ?_, ?_⟩
    · rw [eval_list, eval_list, hae, h1]
    · rw [eval_and, eval_and, eval_bool, eval_bool, hae, h2]
    · rw [eval_or, eval_or, eval_bool, eval_bool, hae, h3]

theorem construct_types (fuel : Int) {env env' : Env} (h : env_types env' = env_types env)
    (c : Id) (tps : List Ty) (vs : List Value) :
    construct O P fuel env' c tps vs = construct O P fuel env c tps vs := by
  rw [construct, construct, h]

/-- Where the variables of `env'` are those of `env`, other than `x`, which is the value of `w`
in `env`, an expression has in `env'` the value of the expression where `x` is `w` in `env`. -/
theorem subst_eval_gen {x : Id} {w : Expr} {fuel : Int} {env env' : Env}
    (htys : env_types env' = env_types env)
    (hvar : ∀ y, eval O P fuel env' (.Variable y) =
      eval O P fuel env (if y = x then w else .Variable y)) :
    ∀ n e e', subst x w n e = some e' → eval O P fuel env' e = eval O P fuel env e'
  | 0, _, _, h => by simp [subst] at h
  | n + 1, e, e', h => by
    have ih := subst_eval_gen (x := x) htys hvar n
    unfold subst at h
    split at h
    · next y =>
      cases h
      exact hvar y
    all_goals first
      | (cases h; simp only [eval]; done)
      | skip
    · obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [eval, eval_bool, ih _ _ ha]
    · obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [eval, eval_bool, ih _ _ ha]
    · obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [eval, eval_bool, ih _ _ ha]
    · obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [eval, eval_bool, ih _ _ ha]
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next a' b' ha hb => cases h; simp only [eval, eval_bool, ih _ _ ha, ih _ _ hb]
      · cases h
    · split at h
      · next c' a' b' hc ha hb =>
        cases h; simp only [eval, eval_bool, ih _ _ hc, ih _ _ ha, ih _ _ hb]
      · cases h
    · obtain ⟨es', hes, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [eval]
      exact (subst_list ih _ _ hes).2.1
    · obtain ⟨es', hes, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [eval]
      exact (subst_list ih _ _ hes).2.2
    · obtain ⟨es', hes, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [eval, (subst_list ih _ _ hes).1, htys]
    · obtain ⟨es', hes, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [eval, (subst_list ih _ _ hes).1, construct_types fuel htys]
    · cases h


/-- Where `w` has the value `vw`, an expression where the variable `x` is `vw` has the value of
the expression where `x` is `w`. -/
theorem subst_eval {x : Id} {w : Expr} {fuel : Int} {env : Env} {vw : Value}
    (hw : eval O P fuel env w = .Ok vw) :
    ∀ n e e', subst x w n e = some e' →
      eval O P fuel (env_bind env x vw) e = eval O P fuel env e' :=
  subst_eval_gen (env_types_bind env x vw) fun y => by
    by_cases hy : y = x
    · subst hy
      cases env
      simp [eval, env_bind, env_vars, lookup_var, hw]
    · cases env
      simp [eval, env_bind, env_vars, lookup_var, hy]

end

/-! ## Rewriting at a position -/

/-- The facts in the body of `(let ((x v)) b)`: that `x` has the value of `v`, where `v` doesn't
mention `x`. The facts around the let may mention `x`, which it rebinds, and are not kept. -/
def letFacts (x : Id) (v : Expr) : List Fact :=
  if (subst x v 1000 v).any (exprEq 1000 · v) then [.binds x v] else []

/-- The facts of the parameters of a quantifier, where their names are distinct: those of
integers and booleans have primitive values. -/
def paramFacts (ps : List Param) : List Fact :=
  if (param_ids ps).Nodup then ps.filterMap fun
    | .Param x .IntegerType | .Param x .BooleanType => some (.prim x)
    | _ => none
  else []

/-- `e` where the subterm at the position `p` is what `r` makes of it, under the facts `Fs` that
hold in the environment of `e`, with those of the path to the position. The positions are those
of the S-expressions that the certificate writes: the operands of an application are at `1` and
after, and the value of `(let ((x v)) b)` is at `1 0 1`. -/
def rewriteAt (r : List Fact → Expr → Option Expr) (qr : List Fact → Expr → Expr → Bool) :
    List Fact → List Nat → Expr → Option Expr
  | Fs, [], e => r Fs e
  | Fs, i :: p, e =>
    match i, e with
    | 1, .Not a => (rewriteAt r qr Fs p a).map .Not
    | 1, .Plus a b => (rewriteAt r qr Fs p a).map (.Plus · b)
    | 2, .Plus a b => (rewriteAt r qr Fs p b).map (.Plus a ·)
    | 1, .Minus a b => (rewriteAt r qr Fs p a).map (.Minus · b)
    | 2, .Minus a b => (rewriteAt r qr Fs p b).map (.Minus a ·)
    | 1, .Times a b => (rewriteAt r qr Fs p a).map (.Times · b)
    | 2, .Times a b => (rewriteAt r qr Fs p b).map (.Times a ·)
    | 1, .Division a b => (rewriteAt r qr Fs p a).map (.Division · b)
    | 2, .Division a b => (rewriteAt r qr Fs p b).map (.Division a ·)
    | 1, .Remainder a b => (rewriteAt r qr Fs p a).map (.Remainder · b)
    | 2, .Remainder a b => (rewriteAt r qr Fs p b).map (.Remainder a ·)
    | 1, .Modulo a b => (rewriteAt r qr Fs p a).map (.Modulo · b)
    | 2, .Modulo a b => (rewriteAt r qr Fs p b).map (.Modulo a ·)
    | 1, .LessThan a b => (rewriteAt r qr Fs p a).map (.LessThan · b)
    | 2, .LessThan a b => (rewriteAt r qr Fs p b).map (.LessThan a ·)
    | 1, .GreaterThan a b => (rewriteAt r qr Fs p a).map (.GreaterThan · b)
    | 2, .GreaterThan a b => (rewriteAt r qr Fs p b).map (.GreaterThan a ·)
    | 1, .LessEquals a b => (rewriteAt r qr Fs p a).map (.LessEquals · b)
    | 2, .LessEquals a b => (rewriteAt r qr Fs p b).map (.LessEquals a ·)
    | 1, .GreaterEquals a b => (rewriteAt r qr Fs p a).map (.GreaterEquals · b)
    | 2, .GreaterEquals a b => (rewriteAt r qr Fs p b).map (.GreaterEquals a ·)
    | 1, .Equals (.Lambda ps b) c =>
      match hp : p with
      | 2 :: p' =>
        (rewriteAt (fun Fs t => (r Fs t).filter (qr Fs t)) qr (paramFacts ps) p' b).map fun b' =>
          .Equals (.Lambda ps b') c
      | _ => (rewriteAt r qr Fs p (.Lambda ps b)).map (.Equals · c)
    | 1, .Equals a b => (rewriteAt r qr Fs p a).map (.Equals · b)
    | 2, .Equals a b => (rewriteAt r qr Fs p b).map (.Equals a ·)
    | 1, .UMinus a => (rewriteAt r qr Fs p a).map .UMinus
    | 1, .IsConstructor a c => (rewriteAt r qr Fs p a).map (.IsConstructor · c)
    | 1, .ADTSelector a f => (rewriteAt r qr Fs p a).map (.ADTSelector · f)
    | 1, .Implies a b => (rewriteAt r qr Fs p a).map (.Implies · b)
    | 2, .Implies a b => (rewriteAt r qr (Fs ++ [.holds a]) p b).map (.Implies a ·)
    | 1, .IfExpr c a b => (rewriteAt r qr Fs p c).map (.IfExpr · a b)
    | 2, .IfExpr c a b => (rewriteAt r qr (Fs ++ [.holds c]) p a).map (.IfExpr c · b)
    | 3, .IfExpr c a b => (rewriteAt r qr (Fs ++ [.holds (.Not c)]) p b).map (.IfExpr c a ·)
    | 1, .Assume q a => (rewriteAt r qr Fs p q).map (.Assume · a)
    | 2, .Assume q a => (rewriteAt r qr (Fs ++ [.holds q]) p a).map (.Assume q ·)
    | 2, .Let x v b => (rewriteAt r qr (letFacts x v) p b).map (.Let x v ·)
    | 1, .Let x v b =>
      match p with
      | 0 :: 1 :: p' => (rewriteAt r qr Fs p' v).map (.Let x · b)
      | _ => none
    | i + 1, .And es =>
      match es.drop i with
      | t :: post =>
        (rewriteAt r qr (Fs ++ (es.take i).map .holds) p t).map fun t' =>
          .And (es.take i ++ t' :: post)
      | [] => none
    | i + 1, .Or es =>
      match es.drop i with
      | t :: post =>
        (rewriteAt r qr (Fs ++ (es.take i).map fun e => .holds (.Not e)) p t).map fun t' =>
          .Or (es.take i ++ t' :: post)
      | [] => none
    | i + 1, .FunctionInvocation f tps es =>
      match es.drop i with
      | t :: post =>
        (rewriteAt r qr Fs p t).map fun t' => .FunctionInvocation f tps (es.take i ++ t' :: post)
      | [] => none
    | i + 1, .ADT c tps es =>
      match es.drop i with
      | t :: post => (rewriteAt r qr Fs p t).map fun t' => .ADT c tps (es.take i ++ t' :: post)
      | [] => none
    | 2, .Forall ps b => (rewriteAt r qr (paramFacts ps) p b).map (.Forall ps ·)
    | 2, .Not (.Forall ps (.Not b)) =>
      (rewriteAt r qr (paramFacts ps) p b).map fun b' => .Not (.Forall ps (.Not b'))
    | _, _ => none
termination_by _ p _ => p.length


section
variable {O : Oracle} {P : Program}

theorem eval_bool_ok {fuel : Int} {env : Env} {a : Expr} {b : Bool} :
    eval_bool O P fuel env a = .Ok b ↔ eval O P fuel env a = .Ok (.BoolV b) := by
  unfold eval_bool
  cases eval O P fuel env a with
  | Ok v => cases v <;> simp
  | Stuck => simp
  | OutOfFuel => simp

theorem bool_refines {Fs : List Fact} {a a' : Expr} (h : Refines O P Fs a a') {fuel : Int}
    {env : Env} (hF : ∀ f ∈ Fs, f.Holds O P fuel env) {b : Bool}
    (ha : eval_bool O P fuel env a = .Ok b) : eval_bool O P fuel env a' = .Ok b :=
  eval_bool_ok.mpr (h fuel env _ hF (eval_bool_ok.mp ha))

theorem facts_append {fuel : Int} {env : Env} {Fs Gs : List Fact}
    (h1 : ∀ f ∈ Fs, f.Holds O P fuel env) (h2 : ∀ f ∈ Gs, f.Holds O P fuel env) :
    ∀ f ∈ Fs ++ Gs, f.Holds O P fuel env := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · exact h1 f hf
  · exact h2 f hf

theorem refines_Plus_1 {Fs : List Fact} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.Plus a b) (.Plus a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Plus_2 {Fs : List Fact} {a b b' : Expr} (h : Refines O P Fs b b') :
    Refines O P Fs (.Plus a b) (.Plus a b') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha =>
    split at hv
    · next vb hb => rw [h fuel env vb hF hb]; exact hv
    · cases hv
    · cases hv
  · cases hv
  · cases hv

theorem refines_Minus_1 {Fs : List Fact} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.Minus a b) (.Minus a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Minus_2 {Fs : List Fact} {a b b' : Expr} (h : Refines O P Fs b b') :
    Refines O P Fs (.Minus a b) (.Minus a b') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha =>
    split at hv
    · next vb hb => rw [h fuel env vb hF hb]; exact hv
    · cases hv
    · cases hv
  · cases hv
  · cases hv

theorem refines_Times_1 {Fs : List Fact} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.Times a b) (.Times a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Times_2 {Fs : List Fact} {a b b' : Expr} (h : Refines O P Fs b b') :
    Refines O P Fs (.Times a b) (.Times a b') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha =>
    split at hv
    · next vb hb => rw [h fuel env vb hF hb]; exact hv
    · cases hv
    · cases hv
  · cases hv
  · cases hv

theorem refines_Division_1 {Fs : List Fact} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.Division a b) (.Division a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Division_2 {Fs : List Fact} {a b b' : Expr} (h : Refines O P Fs b b') :
    Refines O P Fs (.Division a b) (.Division a b') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha =>
    split at hv
    · next vb hb => rw [h fuel env vb hF hb]; exact hv
    · cases hv
    · cases hv
  · cases hv
  · cases hv

theorem refines_Remainder_1 {Fs : List Fact} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.Remainder a b) (.Remainder a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Remainder_2 {Fs : List Fact} {a b b' : Expr} (h : Refines O P Fs b b') :
    Refines O P Fs (.Remainder a b) (.Remainder a b') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha =>
    split at hv
    · next vb hb => rw [h fuel env vb hF hb]; exact hv
    · cases hv
    · cases hv
  · cases hv
  · cases hv

theorem refines_Modulo_1 {Fs : List Fact} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.Modulo a b) (.Modulo a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Modulo_2 {Fs : List Fact} {a b b' : Expr} (h : Refines O P Fs b b') :
    Refines O P Fs (.Modulo a b) (.Modulo a b') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha =>
    split at hv
    · next vb hb => rw [h fuel env vb hF hb]; exact hv
    · cases hv
    · cases hv
  · cases hv
  · cases hv

theorem refines_LessThan_1 {Fs : List Fact} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.LessThan a b) (.LessThan a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_LessThan_2 {Fs : List Fact} {a b b' : Expr} (h : Refines O P Fs b b') :
    Refines O P Fs (.LessThan a b) (.LessThan a b') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha =>
    split at hv
    · next vb hb => rw [h fuel env vb hF hb]; exact hv
    · cases hv
    · cases hv
  · cases hv
  · cases hv

theorem refines_GreaterThan_1 {Fs : List Fact} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.GreaterThan a b) (.GreaterThan a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_GreaterThan_2 {Fs : List Fact} {a b b' : Expr} (h : Refines O P Fs b b') :
    Refines O P Fs (.GreaterThan a b) (.GreaterThan a b') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha =>
    split at hv
    · next vb hb => rw [h fuel env vb hF hb]; exact hv
    · cases hv
    · cases hv
  · cases hv
  · cases hv

theorem refines_LessEquals_1 {Fs : List Fact} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.LessEquals a b) (.LessEquals a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_LessEquals_2 {Fs : List Fact} {a b b' : Expr} (h : Refines O P Fs b b') :
    Refines O P Fs (.LessEquals a b) (.LessEquals a b') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha =>
    split at hv
    · next vb hb => rw [h fuel env vb hF hb]; exact hv
    · cases hv
    · cases hv
  · cases hv
  · cases hv

theorem refines_GreaterEquals_1 {Fs : List Fact} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.GreaterEquals a b) (.GreaterEquals a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_GreaterEquals_2 {Fs : List Fact} {a b b' : Expr} (h : Refines O P Fs b b') :
    Refines O P Fs (.GreaterEquals a b) (.GreaterEquals a b') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha =>
    split at hv
    · next vb hb => rw [h fuel env vb hF hb]; exact hv
    · cases hv
    · cases hv
  · cases hv
  · cases hv

theorem refines_Equals_1 {Fs : List Fact} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.Equals a b) (.Equals a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Equals_2 {Fs : List Fact} {a b b' : Expr} (h : Refines O P Fs b b') :
    Refines O P Fs (.Equals a b) (.Equals a b') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha =>
    split at hv
    · next vb hb => rw [h fuel env vb hF hb]; exact hv
    · cases hv
    · cases hv
  · cases hv
  · cases hv

theorem refines_UMinus {Fs : List Fact} {a a' : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.UMinus a) (.UMinus a') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_IsConstructor {Fs : List Fact} {a a' : Expr} {c : Id} (h : Refines O P Fs a a') :
    Refines O P Fs (.IsConstructor a c) (.IsConstructor a' c) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_ADTSelector {Fs : List Fact} {a a' : Expr} {f : Id} (h : Refines O P Fs a a') :
    Refines O P Fs (.ADTSelector a f) (.ADTSelector a' f) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Not {Fs : List Fact} {a a' : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.Not a) (.Not a') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [bool_refines h hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Implies_1 {Fs : List Fact} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.Implies a b) (.Implies a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [bool_refines h hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_IfExpr_1 {Fs : List Fact} {c c' a b : Expr} (h : Refines O P Fs c c') :
    Refines O P Fs (.IfExpr c a b) (.IfExpr c' a b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [bool_refines h hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Assume_1 {Fs : List Fact} {q q' a : Expr} (h : Refines O P Fs q q') :
    Refines O P Fs (.Assume q a) (.Assume q' a) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [bool_refines h hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Implies_2 {Fs : List Fact} {a b b' : Expr}
    (h : Refines O P (Fs ++ [.holds a]) b b') :
    Refines O P Fs (.Implies a b) (.Implies a b') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next x ha =>
    split at hv
    · next hx =>
      subst hx
      have hF' :=
        facts_append (Gs := [.holds a]) hF (by simpa [Fact.Holds] using eval_bool_ok.mp ha)
      simp only [dite_true] at hv ⊢
      split at hv
      · next y hb => rw [bool_refines h hF' hb]; exact hv
      · cases hv
      · cases hv
    · next hx => simp only [hx] at hv ⊢; exact hv
  · cases hv
  · cases hv

theorem refines_IfExpr_2 {Fs : List Fact} {c a a' b : Expr}
    (h : Refines O P (Fs ++ [.holds c]) a a') :
    Refines O P Fs (.IfExpr c a b) (.IfExpr c a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next x hc =>
    split at hv
    · next hx =>
      subst hx
      simp only [dite_true] at hv ⊢
      exact h fuel env v (facts_append hF (by simpa [Fact.Holds] using eval_bool_ok.mp hc)) hv
    · next hx => simp only [hx] at hv ⊢; exact hv
  · cases hv
  · cases hv

theorem refines_IfExpr_3 {Fs : List Fact} {c a b b' : Expr}
    (h : Refines O P (Fs ++ [.holds (.Not c)]) b b') :
    Refines O P Fs (.IfExpr c a b) (.IfExpr c a b') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next x hc =>
    split at hv
    · next hx => subst hx; simp only [dite_true] at hv ⊢; exact hv
    · next hx =>
      have hx' : x = false := by simpa using hx
      subst hx'
      simp only [Bool.false_eq_true, dite_false] at hv ⊢
      refine h fuel env v (facts_append hF ?_) hv
      intro f hf
      simp only [List.mem_singleton] at hf
      subst hf
      simp [Fact.Holds, eval, hc]
  · cases hv
  · cases hv

theorem refines_Assume_2 {Fs : List Fact} {q a a' : Expr}
    (h : Refines O P (Fs ++ [.holds q]) a a') :
    Refines O P Fs (.Assume q a) (.Assume q a') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next x hq =>
    split at hv
    · next hx =>
      subst hx
      simp only [dite_true] at hv ⊢
      exact h fuel env v (facts_append hF (by simpa [Fact.Holds] using eval_bool_ok.mp hq)) hv
    · cases hv
  · cases hv
  · cases hv

theorem refines_Let_2 {Fs : List Fact} {x : Id} {v b b' : Expr}
    (h : Refines O P (letFacts x v) b b') : Refines O P Fs (.Let x v b) (.Let x v b') := by
  intro fuel env w hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next vv hvv =>
    refine h fuel _ w ?_ hv
    unfold letFacts
    split
    · next hs =>
      intro f hf
      simp only [List.mem_singleton] at hf
      subst hf
      obtain ⟨v', hv', he⟩ : ∃ v', subst x v 1000 v = some v' ∧ exprEq 1000 v' v = true := by
        cases hs' : subst x v 1000 v with
        | none => simp [hs'] at hs
        | some v' => simp only [hs', Option.any_some] at hs; exact ⟨v', rfl, hs⟩
      refine ⟨vv, ?_, ?_⟩
      · cases env; simp [env_bind, env_vars, lookup_var]
      · rw [subst_eval hvv 1000 v v' hv', exprEq_eq _ _ _ he, hvv]
    · simp
  · cases hv
  · cases hv

theorem refines_Let_1 {Fs : List Fact} {x : Id} {v v' b : Expr} (h : Refines O P Fs v v') :
    Refines O P Fs (.Let x v b) (.Let x v' b) := by
  intro fuel env w hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next vv hvv => rw [h fuel env vv hF hvv]; exact hv
  · cases hv
  · cases hv

theorem refines_list {Fs : List Fact} {t t' : Expr} {post : List Expr} (h : Refines O P Fs t t')
    {fuel : Int} {env : Env} (hF : ∀ f ∈ Fs, f.Holds O P fuel env) :
    ∀ (pre : List Expr) {vs : List Value}, eval_list O P fuel env (pre ++ t :: post) = .Ok vs →
      eval_list O P fuel env (pre ++ t' :: post) = .Ok vs
  | [], vs, hv => by
    simp only [List.nil_append] at hv ⊢
    rw [eval_list] at hv ⊢
    split at hv
    · next vt ht => rw [h fuel env vt hF ht]; exact hv
    · cases hv
    · cases hv
  | q :: pre, vs, hv => by
    simp only [List.cons_append] at hv ⊢
    rw [eval_list] at hv ⊢
    split at hv
    · next vq hq =>
      split at hv
      · next ws hws => rw [refines_list h hF pre hws]; exact hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv

theorem refines_call {Fs : List Fact} {t t' : Expr} {f : Id} {tps : List Ty} {pre post : List Expr}
    (h : Refines O P Fs t t') :
    Refines O P Fs (.FunctionInvocation f tps (pre ++ t :: post))
      (.FunctionInvocation f tps (pre ++ t' :: post)) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next vs hvs => rw [refines_list h hF pre hvs]; exact hv
  · cases hv
  · cases hv

theorem refines_adt {Fs : List Fact} {t t' : Expr} {c : Id} {tps : List Ty} {pre post : List Expr}
    (h : Refines O P Fs t t') :
    Refines O P Fs (.ADT c tps (pre ++ t :: post)) (.ADT c tps (pre ++ t' :: post)) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next vs hvs => rw [refines_list h hF pre hvs]; exact hv
  · cases hv
  · cases hv

theorem refines_And {t t' : Expr} {post : List Expr} :
    ∀ (pre : List Expr) (Fs : List Fact), Refines O P (Fs ++ pre.map .holds) t t' →
      Refines O P Fs (.And (pre ++ t :: post)) (.And (pre ++ t' :: post))
  | [], Fs, h => by
    intro fuel env v hF hv
    simp only [eval, List.nil_append] at hv ⊢
    rw [eval_and] at hv ⊢
    split at hv
    · next x ht => rw [bool_refines h (by simpa using hF) ht]; exact hv
    · cases hv
    · cases hv
  | q :: pre, Fs, h => by
    intro fuel env v hF hv
    simp only [eval, List.cons_append] at hv ⊢
    rw [eval_and] at hv ⊢
    split at hv
    · next x hq =>
      split at hv
      · next hx =>
        subst hx
        simp only [dite_true] at hv ⊢
        have ih := refines_And (post := post) pre (Fs ++ [.holds q]) (by simpa using h)
        have := ih fuel env v (facts_append hF (by simpa [Fact.Holds] using eval_bool_ok.mp hq))
          (by simpa only [eval] using hv)
        simpa only [eval] using this
      · next hx => simp only [hx] at hv ⊢; exact hv
    · cases hv
    · cases hv

theorem refines_Or {t t' : Expr} {post : List Expr} :
    ∀ (pre : List Expr) (Fs : List Fact),
      Refines O P (Fs ++ pre.map fun e => .holds (.Not e)) t t' →
      Refines O P Fs (.Or (pre ++ t :: post)) (.Or (pre ++ t' :: post))
  | [], Fs, h => by
    intro fuel env v hF hv
    simp only [eval, List.nil_append] at hv ⊢
    rw [eval_or] at hv ⊢
    split at hv
    · next x ht => rw [bool_refines h (by simpa using hF) ht]; exact hv
    · cases hv
    · cases hv
  | q :: pre, Fs, h => by
    intro fuel env v hF hv
    simp only [eval, List.cons_append] at hv ⊢
    rw [eval_or] at hv ⊢
    split at hv
    · next x hq =>
      split at hv
      · next hx => subst hx; simp only [dite_true] at hv ⊢; exact hv
      · next hx =>
        have hx' : x = false := by simpa using hx
        subst hx'
        simp only [Bool.false_eq_true, dite_false] at hv ⊢
        have ih := refines_Or (post := post) pre (Fs ++ [.holds (.Not q)]) (by simpa using h)
        have hn : ∀ f ∈ [Fact.holds (.Not q)], f.Holds O P fuel env := by
          intro f hf
          simp only [List.mem_singleton] at hf
          subst hf
          simp [Fact.Holds, eval, hq]
        have := ih fuel env v (facts_append hF hn) (by simpa only [eval] using hv)
        simpa only [eval] using this
    · cases hv
    · cases hv

end

section
variable {O : Oracle} {P : Program}

theorem param_ids_mem {x : Id} {T : Ty} : ∀ {ps : List Param}, Param.Param x T ∈ ps →
    x ∈ param_ids ps
  | .Param y U :: ps, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h; simp [param_ids]
    · simp [param_ids, param_ids_mem h]

theorem lookup_param (hO : O.Sound) {vars : List Binding} : ∀ (ps : List Param)
    (vs : List Value) (bs : List Binding) (env : Env), (param_ids ps).Nodup →
    O.params_have_types P env vs ps = true → bind_all (param_ids ps) vs = .Ok bs →
    ∀ x T, Param.Param x T ∈ ps → ∃ w env', lookup_var (append_env bs vars) x = .Ok w ∧
      O.has_type P env' w T = true
  | [], _, _, _, _, _, _, x, T, hm => by simp at hm
  | .Param y U :: ps, v :: vs, bs, env, hnd, hty, hbs, x, T, hm => by
    rw [hO.params_have_types] at hty
    simp only [Bool.and_eq_true] at hty
    simp only [param_ids] at hbs hnd
    rw [bind_all] at hbs
    split at hbs
    · next bs' hbs' =>
      cases hbs
      by_cases hxy : x = y
      · subst hxy
        have hT : T = U := by
          rcases List.mem_cons.mp hm with h | h
          · cases h; rfl
          · have := (List.nodup_cons.mp hnd).1
            exact absurd (param_ids_mem h) this
        subst hT
        exact ⟨v, env, by simp [append_env, lookup_var], hty.1⟩
      · have hm' : Param.Param x T ∈ ps := by
          rcases List.mem_cons.mp hm with h | h
          · cases h; exact absurd rfl hxy
          · exact h
        obtain ⟨w, env', hw, hwt⟩ :=
          lookup_param hO ps vs bs' (env_bind env y v) (List.nodup_cons.mp hnd).2 hty.2 hbs' x T hm'
        exact ⟨w, env', by simp only [append_env, lookup_var, hxy, dite_false]; exact hw, hwt⟩
    · cases hbs
    · cases hbs
  | .Param _ _ :: _, [], _, _, _, hty, _, _, _, _ => by
    rw [hO.params_have_types] at hty; simp at hty

/-- The facts of the parameters hold of the values of their types. -/
theorem paramFacts_hold (hO : O.Sound) {ps : List Param} {vs : List Value} {bs : List Binding}
    {env : Env} {tys : List TypeBinding} {vars : List Binding} {fuel : Int}
    (hty : O.params_have_types P env vs ps = true) (hbs : bind_all (param_ids ps) vs = .Ok bs) :
    ∀ f ∈ paramFacts ps, f.Holds O P fuel (Env.Env tys (append_env bs vars)) := by
  intro f hf
  unfold paramFacts at hf
  split at hf
  · next hnd =>
    obtain ⟨⟨x, T⟩, hm, hf⟩ := List.mem_filterMap.mp hf
    obtain ⟨w, env', hw, hwt⟩ := lookup_param (vars := vars) hO ps vs bs env hnd hty hbs x T hm
    rw [hO.has_type] at hwt
    cases T
    all_goals first | (simp at hf; done) | skip
    all_goals
      simp only [Option.some.injEq] at hf
      subst hf
      refine ⟨w, hw, ?_⟩
      cases w <;> simp at hwt <;> rfl
  · simp at hf

/-- A quantifier of a body that refines another refines the quantifier of the other. -/
theorem refines_Forall (hO : O.Sound) {Fs : List Fact} {ps : List Param} {b b' : Expr}
    (h : Refines O P (paramFacts ps) b b') : Refines O P Fs (.Forall ps b) (.Forall ps b') := by
  intro fuel env v _ hv
  simp only [eval] at hv ⊢
  rw [hO.forall_result] at hv ⊢
  have hi : ∀ vs w, O.params_have_types P env vs ps = true →
      instance_ O P fuel env ps vs b = .Ok w → instance_ O P fuel env ps vs b' = .Ok w := by
    intro vs w hvs hw
    cases env with
    | Env tys vars =>
    simp only [instance_] at hw ⊢
    split at hw
    · next bs hbs =>
      try simp only [hbs]
      exact h fuel _ w (paramFacts_hold hO hvs hbs) hw
    · cases hw
    · cases hw
  split at hv
  · next hex =>
    cases hv
    simp only [decide_eq_true_eq, Bool.and_eq_true] at hex
    obtain ⟨vs, hvs, hf⟩ := hex
    rw [dif_pos]
    simp only [decide_eq_true_eq, Bool.and_eq_true]
    exact ⟨vs, hvs, hi vs _ hvs hf⟩
  · split at hv
    · cases hv
    · split at hv
      · next hall =>
        cases hv
        simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hall
        have hall' : ∀ vs, O.params_have_types P env vs ps = true →
            instance_ O P fuel env ps vs b' = .Ok (.BoolV true) := by
          intro vs hvs
          rcases hall vs with h0 | h0
          · rw [hvs] at h0; cases h0
          · exact hi vs _ hvs h0
        rw [dif_neg, dif_neg, dif_pos]
        · simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true']
          intro vs
          by_cases hvs : O.params_have_types P env vs ps = true
          · exact .inr (hall' vs hvs)
          · exact .inl (by simpa using hvs)
        · simp only [decide_eq_true_eq, Bool.and_eq_true, not_exists, not_and]
          intro vs hvs h0
          rw [hall' vs hvs] at h0; cases h0
        · simp only [decide_eq_true_eq, Bool.and_eq_true, not_exists, not_and]
          intro vs hvs h0
          rw [hall' vs hvs] at h0; cases h0
      · cases hv

/-- An equality of a lambda, whose body has the same values as another, has the value of the
equality of the lambda of the other: the closures are compared by their values. -/
theorem refines_EqLam (hO : O.Sound) {Fs : List Fact} {ps : List Param} {b b' c : Expr}
    (h1 : Refines O P (paramFacts ps) b b') (h2 : Refines O P (paramFacts ps) b' b) :
    Refines O P Fs (.Equals (.Lambda ps b) c) (.Equals (.Lambda ps b') c) := by
  intro fuel env v _ hv
  have key : ∀ vs, O.params_have_types P env vs ps = true → ∀ f a,
      apply O P f (.ClosureV ps b env) vs = .Ok a ↔
        apply O P f (.ClosureV ps b' env) vs = .Ok a := by
    intro vs hvs f a
    cases env with
    | Env tys vars =>
    simp only [apply]
    split
    · simp
    · split
      · next bs hbs =>
        exact ⟨h1 _ _ a (paramFacts_hold hO hvs hbs), h2 _ _ a (paramFacts_hold hO hvs hbs)⟩
      · simp
      · simp
  have hce : ∀ d, O.closures_equal P (.ClosureV ps b env) d =
      O.closures_equal P (.ClosureV ps b' env) d := by
    intro d
    rw [hO.closures_equal, hO.closures_equal]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
      decide_eq_false_iff_not]
    refine forall_congr' fun vs => ?_
    by_cases hvs : O.params_have_types P env vs ps = true
    · simp only [hvs, key vs hvs]
    · simp [hvs]
  have hL : ∀ bb, eval O P fuel env (.Lambda ps bb) = .Ok (.ClosureV ps bb env) := by
    intro bb; rw [eval]
  rw [eval, hL] at hv
  rw [eval, hL]
  revert hv
  cases eval O P fuel env c with
  | Ok d =>
    simp only
    rw [hO.value_eq, hO.value_eq]
    cases P with
    | Program fs cs ss is eqm =>
      cases eqm
      · simp
      · simp only [hce d]; exact id
  | _ => simp

theorem filter_some {o : Option Expr} {f : Expr → Bool} {t' : Expr} (h : o.filter f = some t') :
    o = some t' ∧ f t' = true := by
  cases o with
  | none => simp at h
  | some a =>
    simp only [Option.filter] at h
    split at h
    · next hf => cases h; exact ⟨rfl, hf⟩
    · cases h

theorem filter_fwd {r : List Fact → Expr → Option Expr} {q : List Fact → Expr → Expr → Bool}
    (hr : ∀ Fs t t', r Fs t = some t' → Refines O P Fs t t') :
    ∀ Fs t t', (r Fs t).filter (q Fs t) = some t' → Refines O P Fs t t' :=
  fun Fs t t' h => hr Fs t t' (filter_some h).1

theorem filter_bwd {r : List Fact → Expr → Option Expr} {q : List Fact → Expr → Expr → Bool}
    (hq : ∀ Fs t t', r Fs t = some t' → q Fs t t' = true → Refines O P Fs t' t) :
    ∀ Fs t t', (r Fs t).filter (q Fs t) = some t' → Refines O P Fs t' t :=
  fun Fs t t' h => hq Fs t t' (filter_some h).1 (filter_some h).2

theorem filter_q {r : List Fact → Expr → Option Expr} {q : List Fact → Expr → Expr → Bool}
    (hq : ∀ Fs t t', r Fs t = some t' → q Fs t t' = true → Refines O P Fs t' t) :
    ∀ Fs t t', (r Fs t).filter (q Fs t) = some t' → q Fs t t' = true → Refines O P Fs t' t :=
  fun Fs t t' h hq' => hq Fs t t' (filter_some h).1 hq'

set_option maxHeartbeats 2000000 in
mutual
/-- Rewriting the subterm at a position into one that refines it refines the expression. -/
theorem rewriteAt_refines (hO : O.Sound) {r : List Fact → Expr → Option Expr}
    {q : List Fact → Expr → Expr → Bool} (hr : ∀ Fs t t', r Fs t = some t' → Refines O P Fs t t')
    (hq : ∀ Fs t t', r Fs t = some t' → q Fs t t' = true → Refines O P Fs t' t) :
    ∀ (Fs : List Fact) (p : List Nat) (e e' : Expr), rewriteAt r q Fs p e = some e' →
      Refines O P Fs e e'
  | Fs, [], e, e', h => hr Fs e e' (by simpa [rewriteAt] using h)
  | Fs, i :: p, e, e', h => by
    unfold rewriteAt at h
    split at h
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Not (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Plus_1 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Plus_2 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Minus_1 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Minus_2 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Times_1 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Times_2 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Division_1 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Division_2 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Remainder_1 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Remainder_2 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Modulo_1 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Modulo_2 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_LessThan_1 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_LessThan_2 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_GreaterThan_1 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_GreaterThan_2 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_LessEquals_1 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_LessEquals_2 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_GreaterEquals_1 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_GreaterEquals_2 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · next ps b c =>
      split at h
      · obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h
        exact refines_EqLam hO (rewriteAt_refines hO (filter_fwd hr) (filter_q hq) _ _ _ _ hb)
          (rewriteAt_rev hO (filter_fwd hr) (filter_bwd hq) (filter_q hq) _ _ _ _ hb)
      · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
        exact refines_Equals_1 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Equals_1 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Equals_2 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_UMinus (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_IsConstructor (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_ADTSelector (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Implies_1 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Implies_2 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_IfExpr_1 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_IfExpr_2 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_IfExpr_3 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Assume_1 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Assume_2 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Let_2 (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · next x v b =>
      split at h
      · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
        exact refines_Let_1 (rewriteAt_refines hO hr hq _ _ _ _ ht)
      · cases h
    · next j es =>
      split at h
      · next t post hd =>
        obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
        have hes : es = es.take j ++ t :: post := by rw [← hd, List.take_append_drop]
        have := refines_And (post := post) (es.take j) Fs (rewriteAt_refines hO hr hq _ _ _ _ ht)
        rwa [← hes] at this
      · cases h
    · next j es =>
      split at h
      · next t post hd =>
        obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
        have hes : es = es.take j ++ t :: post := by rw [← hd, List.take_append_drop]
        have := refines_Or (post := post) (es.take j) Fs (rewriteAt_refines hO hr hq _ _ _ _ ht)
        rwa [← hes] at this
      · cases h
    · next j f tps es =>
      split at h
      · next t post hd =>
        obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
        have hes : es = es.take j ++ t :: post := by rw [← hd, List.take_append_drop]
        have := refines_call (f := f) (tps := tps) (pre := es.take j) (post := post)
          (rewriteAt_refines hO hr hq _ _ _ _ ht)
        rwa [← hes] at this
      · cases h
    · next j c tps es =>
      split at h
      · next t post hd =>
        obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
        have hes : es = es.take j ++ t :: post := by rw [← hd, List.take_append_drop]
        have := refines_adt (c := c) (tps := tps) (pre := es.take j) (post := post)
          (rewriteAt_refines hO hr hq _ _ _ _ ht)
        rwa [← hes] at this
      · cases h
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Forall hO (rewriteAt_refines hO hr hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Not (refines_Forall hO (refines_Not (rewriteAt_refines hO hr hq _ _ _ _ ht)))
    · cases h

/-- Rewriting the subterm at a position into one that it refines makes the expression refine the
expression after the rewriting. -/
theorem rewriteAt_rev (hO : O.Sound) {r : List Fact → Expr → Option Expr}
    {q : List Fact → Expr → Expr → Bool} (hr : ∀ Fs t t', r Fs t = some t' → Refines O P Fs t t')
    (hb : ∀ Fs t t', r Fs t = some t' → Refines O P Fs t' t)
    (hq : ∀ Fs t t', r Fs t = some t' → q Fs t t' = true → Refines O P Fs t' t) :
    ∀ (Fs : List Fact) (p : List Nat) (e e' : Expr), rewriteAt r q Fs p e = some e' →
      Refines O P Fs e' e
  | Fs, [], e, e', h => hb Fs e e' (by simpa [rewriteAt] using h)
  | Fs, i :: p, e, e', h => by
    unfold rewriteAt at h
    split at h
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Not (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Plus_1 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Plus_2 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Minus_1 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Minus_2 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Times_1 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Times_2 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Division_1 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Division_2 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Remainder_1 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Remainder_2 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Modulo_1 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Modulo_2 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_LessThan_1 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_LessThan_2 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_GreaterThan_1 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_GreaterThan_2 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_LessEquals_1 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_LessEquals_2 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_GreaterEquals_1 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_GreaterEquals_2 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · next ps b c =>
      split at h
      · obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h
        exact refines_EqLam hO
          (rewriteAt_rev hO (filter_fwd hr) (filter_bwd hq) (filter_q hq) _ _ _ _ hb)
          (rewriteAt_refines hO (filter_fwd hr) (filter_q hq) _ _ _ _ hb)
      · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
        exact refines_Equals_1 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Equals_1 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Equals_2 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_UMinus (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_IsConstructor (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_ADTSelector (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Implies_1 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Implies_2 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_IfExpr_1 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_IfExpr_2 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_IfExpr_3 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Assume_1 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Assume_2 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Let_2 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · next x v b =>
      split at h
      · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
        exact refines_Let_1 (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
      · cases h
    · next j es =>
      split at h
      · next t post hd =>
        obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
        have hes : es = es.take j ++ t :: post := by rw [← hd, List.take_append_drop]
        have := refines_And (post := post) (es.take j) Fs (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
        rwa [← hes] at this
      · cases h
    · next j es =>
      split at h
      · next t post hd =>
        obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
        have hes : es = es.take j ++ t :: post := by rw [← hd, List.take_append_drop]
        have := refines_Or (post := post) (es.take j) Fs (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
        rwa [← hes] at this
      · cases h
    · next j f tps es =>
      split at h
      · next t post hd =>
        obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
        have hes : es = es.take j ++ t :: post := by rw [← hd, List.take_append_drop]
        have := refines_call (f := f) (tps := tps) (pre := es.take j) (post := post)
          (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
        rwa [← hes] at this
      · cases h
    · next j c tps es =>
      split at h
      · next t post hd =>
        obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
        have hes : es = es.take j ++ t :: post := by rw [← hd, List.take_append_drop]
        have := refines_adt (c := c) (tps := tps) (pre := es.take j) (post := post)
          (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
        rwa [← hes] at this
      · cases h
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Forall hO (rewriteAt_rev hO hr hb hq _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Not (refines_Forall hO (refines_Not (rewriteAt_rev hO hr hb hq _ _ _ _ ht)))
    · cases h

end

theorem refines_trans {Fs : List Fact} {a b c : Expr} (h1 : Refines O P Fs a b)
    (h2 : Refines O P Fs b c) : Refines O P Fs a c :=
  fun fuel env v hF hv => h2 fuel env v hF (h1 fuel env v hF hv)

theorem refines_refl {Fs : List Fact} {a : Expr} : Refines O P Fs a a :=
  fun _ _ _ _ hv => hv

end

section
variable {O : Oracle} {P : Program}

/-- A let without its binding, where its body has the value of the binding for the variable,
`n` lets deep. -/
def unlet : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e =>
    match e with
    | .Let x v b =>
      match subst x v 1000 b with
      | some b' => unlet n b'
      | none => e
    | _ => e

theorem unlet_refines {Fs : List Fact} : ∀ n e, Refines O P Fs e (unlet n e)
  | 0, e => refines_refl
  | n + 1, e => by
    unfold unlet
    split
    · next x v b =>
      split
      · next b' hb =>
        intro fuel env r hF hr
        refine unlet_refines n b' fuel env r hF ?_
        simp only [eval] at hr
        split at hr
        · next vv hv => rw [← subst_eval hv 1000 b b' hb]; exact hr
        · cases hr
        · cases hr
      · exact refines_refl
    · exact refines_refl

end


/-! ## The rules -/

/-- `select`: the selection of a field of a construction is the argument of the field. -/
def selectCheck (cs : List Constructor) (t t' : Expr) : Bool :=
  match t with
  | .ADTSelector (.ADT c _ args) sel =>
    match lookup_ctor cs c with
    | .Ok (.Constructor _ _ fields) => (pick fields args sel).any (exprEq 1000 · t')
    | _ => false
  | _ => false

/-- The operands that an expression always evaluates. -/
def strictKids : Expr → List Expr
  | .Not a => [a]
  | .UMinus a => [a]
  | .IsConstructor a _ => [a]
  | .ADTSelector a _ => [a]
  | .Plus a b => [a, b]
  | .Minus a b => [a, b]
  | .Times a b => [a, b]
  | .Division a b => [a, b]
  | .Remainder a b => [a, b]
  | .Modulo a b => [a, b]
  | .LessThan a b => [a, b]
  | .GreaterThan a b => [a, b]
  | .LessEquals a b => [a, b]
  | .GreaterEquals a b => [a, b]
  | .Equals a b => [a, b]
  | .Implies a _ => [a]
  | .IfExpr c _ _ => [c]
  | .Assume p _ => [p]
  | .Let _ v _ => [v]
  | .And (a :: _) => [a]
  | .Or (a :: _) => [a]
  | .FunctionInvocation _ _ es => es
  | .ADT _ _ es => es
  | _ => []

/-- Whether `e` always evaluates `a`, `n` deep. -/
def evaluated (a : Expr) : Nat → Expr → Bool
  | 0, _ => false
  | n + 1, e => exprEq 1000 a e || (strictKids e).any (evaluated a n)

/-- `bind`: binding a subterm that the term always evaluates, to a variable that it doesn't
mention. -/
def bindCheck (t t' : Expr) : Bool :=
  match t' with
  | .Let x a b => exprEq 1000 b t && evaluated a 1000 t && (subst x a 1000 t).any (exprEq 1000 · t)
  | _ => false

/-- `expand`: a variable is the value of its let. -/
def expandCheck (Fs : List Fact) (t t' : Expr) : Bool :=
  match t with
  | .Variable x => Fs.any fun
    | .binds y v => y == x && exprEq 1000 v t'
    | _ => false
  | _ => false

section
variable {O : Oracle} {P : Program}

theorem eval_list_ok {fuel : Int} {env : Env} :
    ∀ (es : List Expr) {vs : List Value}, eval_list O P fuel env es = .Ok vs →
      ∀ k ∈ es, ∃ vk, eval O P fuel env k = .Ok vk
  | [], _, _, k, hk => by simp at hk
  | a :: es, vs, h, k, hk => by
    rw [eval_list] at h
    split at h
    · next va ha =>
      split at h
      · next ws hws =>
        rcases List.mem_cons.mp hk with rfl | hk
        · exact ⟨va, ha⟩
        · exact eval_list_ok es hws k hk
      · cases h
      · cases h
    · cases h
    · cases h

theorem strictKids_eval {fuel : Int} {env : Env} {e : Expr} {v : Value}
    (hv : eval O P fuel env e = .Ok v) :
    ∀ k ∈ strictKids e, ∃ vk, eval O P fuel env k = .Ok vk := by
  intro k hk
  unfold strictKids at hk
  split at hk
  · simp only [List.mem_singleton] at hk; subst hk
    simp only [eval] at hv
    split at hv
    · exact ⟨_, eval_bool_ok.mp ‹_›⟩
    · cases hv
    · cases hv
  · simp only [List.mem_singleton] at hk; subst hk
    simp only [eval] at hv
    split at hv
    · exact ⟨_, ‹_›⟩
    · cases hv
    · cases hv
  · simp only [List.mem_singleton] at hk; subst hk
    simp only [eval] at hv
    split at hv
    · exact ⟨_, ‹_›⟩
    · cases hv
    · cases hv
  · simp only [List.mem_singleton] at hk; subst hk
    simp only [eval] at hv
    split at hv
    · exact ⟨_, ‹_›⟩
    · cases hv
    · cases hv
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb => rcases hk with rfl | rfl; exact ⟨_, ha⟩; exact ⟨_, hb⟩
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb => rcases hk with rfl | rfl; exact ⟨_, ha⟩; exact ⟨_, hb⟩
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb => rcases hk with rfl | rfl; exact ⟨_, ha⟩; exact ⟨_, hb⟩
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb => rcases hk with rfl | rfl; exact ⟨_, ha⟩; exact ⟨_, hb⟩
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb => rcases hk with rfl | rfl; exact ⟨_, ha⟩; exact ⟨_, hb⟩
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb => rcases hk with rfl | rfl; exact ⟨_, ha⟩; exact ⟨_, hb⟩
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb => rcases hk with rfl | rfl; exact ⟨_, ha⟩; exact ⟨_, hb⟩
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb => rcases hk with rfl | rfl; exact ⟨_, ha⟩; exact ⟨_, hb⟩
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb => rcases hk with rfl | rfl; exact ⟨_, ha⟩; exact ⟨_, hb⟩
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb => rcases hk with rfl | rfl; exact ⟨_, ha⟩; exact ⟨_, hb⟩
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb => rcases hk with rfl | rfl; exact ⟨_, ha⟩; exact ⟨_, hb⟩
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  · simp only [List.mem_singleton] at hk; subst hk
    simp only [eval] at hv
    split at hv
    · exact ⟨_, eval_bool_ok.mp ‹_›⟩
    · cases hv
    · cases hv
  · simp only [List.mem_singleton] at hk; subst hk
    simp only [eval] at hv
    split at hv
    · exact ⟨_, eval_bool_ok.mp ‹_›⟩
    · cases hv
    · cases hv
  · simp only [List.mem_singleton] at hk; subst hk
    simp only [eval] at hv
    split at hv
    · exact ⟨_, eval_bool_ok.mp ‹_›⟩
    · cases hv
    · cases hv
  · simp only [List.mem_singleton] at hk; subst hk
    simp only [eval] at hv
    split at hv
    · exact ⟨_, ‹_›⟩
    · cases hv
    · cases hv
  · simp only [List.mem_singleton] at hk; subst hk
    simp only [eval] at hv
    rw [eval_and] at hv
    split at hv
    · exact ⟨_, eval_bool_ok.mp ‹_›⟩
    · cases hv
    · cases hv
  · simp only [List.mem_singleton] at hk; subst hk
    simp only [eval] at hv
    rw [eval_or] at hv
    split at hv
    · exact ⟨_, eval_bool_ok.mp ‹_›⟩
    · cases hv
    · cases hv
  · simp only [eval] at hv
    split at hv
    · exact eval_list_ok _ ‹_› k hk
    · cases hv
    · cases hv
  · simp only [eval] at hv
    split at hv
    · exact eval_list_ok _ ‹_› k hk
    · cases hv
    · cases hv
  · simp at hk

theorem evaluated_eval {fuel : Int} {env : Env} {a : Expr} :
    ∀ n e {v : Value}, evaluated a n e = true → eval O P fuel env e = .Ok v →
      ∃ va, eval O P fuel env a = .Ok va
  | 0, _, _, h, _ => by simp [evaluated] at h
  | n + 1, e, v, h, hv => by
    simp only [evaluated, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with h | ⟨k, hk, hka⟩
    · rw [exprEq_eq _ _ _ h]; exact ⟨v, hv⟩
    · obtain ⟨vk, hvk⟩ := strictKids_eval hv k hk
      exact evaluated_eval n k hka hvk

theorem selectCheck_refines {cs : List Constructor} {Fs : List Fact} {t t' : Expr}
    (hP : ∃ fs ss is eqm, P = .Program fs cs ss is eqm) (h : selectCheck cs t t' = true) :
    Refines O P Fs t t' := by
  obtain ⟨fs, ss, is, eqm, rfl⟩ := hP
  intro fuel env v _ hv
  unfold selectCheck at h
  split at h
  · next c tps args sel =>
    split at h
    · next d s fields hl =>
      obtain ⟨a, hp, he⟩ : ∃ a, pick fields args sel = some a ∧ exprEq 1000 a t' = true := by
        cases hp : pick fields args sel with
        | none => simp [hp] at h
        | some a => simp only [hp, Option.any_some] at h; exact ⟨a, rfl, h⟩
      rw [← exprEq_eq _ _ _ he]
      rw [eval] at hv
      split at hv
      · next w hw =>
        rw [eval] at hw
        split at hw
        · next vs hvs =>
          obtain ⟨tps', rfl⟩ := construct_ok hw
          simp only [hl] at hv
          exact pick_eval fields args vs sel hv hvs hp
        · cases hw
        · cases hw
      · cases hv
      · cases hv
    · cases h
  · cases h

theorem bindCheck_refines {Fs : List Fact} {t t' : Expr} (h : bindCheck t t' = true) :
    Refines O P Fs t t' := by
  intro fuel env v _ hv
  unfold bindCheck at h
  split at h
  · next x a b =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hb, hev⟩, hs⟩ := h
    rw [exprEq_eq _ _ _ hb]
    obtain ⟨va, hva⟩ := evaluated_eval 1000 t hev hv
    obtain ⟨t0, ht0, he⟩ : ∃ t0, subst x a 1000 t = some t0 ∧ exprEq 1000 t0 t = true := by
      cases hs' : subst x a 1000 t with
      | none => simp [hs'] at hs
      | some t0 => simp only [hs', Option.any_some] at hs; exact ⟨t0, rfl, hs⟩
    simp only [eval, hva]
    rw [subst_eval hva 1000 t t0 ht0, exprEq_eq _ _ _ he, hv]
  · cases h

theorem expandCheck_refines {Fs : List Fact} {t t' : Expr} (h : expandCheck Fs t t' = true) :
    Refines O P Fs t t' := by
  intro fuel env v hF hv
  unfold expandCheck at h
  split at h
  · next x =>
    obtain ⟨f, hf, hm⟩ := List.any_eq_true.mp h
    cases f with
    | holds _ => simp at hm
    | prim _ => simp at hm
    | typed _ _ => simp at hm
    | binds y w =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      obtain ⟨rfl, he⟩ := hm
      obtain ⟨u, hu, hw⟩ := hF _ hf
      rw [← exprEq_eq _ _ _ he, hw]
      simp only [eval, hu] at hv
      rw [hv]
  · cases h

end

/-! ## Arithmetic -/

/-- `e` is the integer literal `i`. -/
def isInt : Expr → Int → Bool
  | .IntegerLiteral j, i => j == i
  | _, _ => false

/-- `e` is the literal `true`. -/
def isTrue : Expr → Bool
  | .BooleanLiteral b => b
  | _ => false

/-- The value of `e`, if it has one, is of a primitive type, under the facts `Fs`. -/
def primShaped (Fs : List Fact) : Expr → Bool
  | .IntegerLiteral _ | .BooleanLiteral _ | .StringLiteral _ | .BVLiteral _ _ _ | .CharLiteral _
  | .UnitLiteral | .Equals _ _ | .Plus _ _ | .Minus _ _ | .Times _ _ | .LessThan _ _
  | .GreaterThan _ _ | .LessEquals _ _ | .GreaterEquals _ _ | .Not _ => true
  | .Variable x => Fs.any fun
    | .prim y => y == x
    | _ => false
  | _ => false

/-- `arith`: a product with a factor `0` is `0`, a sum with an operand `0`, a difference with a
right operand `0` and a product with a factor `1` are their other operand, and an equality of an
expression of a primitive type with itself is `true`. -/
def arithCheck (Fs : List Fact) (t t' : Expr) : Bool :=
  match t with
  | .Times a b => (isInt t' 0 && (isInt a 0 || isInt b 0)) ||
      (isInt a 1 && exprEq 1000 b t') || (isInt b 1 && exprEq 1000 a t')
  | .Plus a b => (isInt a 0 && exprEq 1000 b t') || (isInt b 0 && exprEq 1000 a t')
  | .Minus a b => isInt b 0 && exprEq 1000 a t'
  | .Equals a b => isTrue t' && exprEq 1000 a b && primShaped Fs a
  | _ => false

theorem isInt_eq {e : Expr} {i : Int} (h : isInt e i = true) : e = .IntegerLiteral i := by
  unfold isInt at h
  split at h
  · simp only [beq_iff_eq] at h; rw [h]
  · cases h

theorem isTrue_eq {e : Expr} (h : isTrue e = true) : e = .BooleanLiteral true := by
  unfold isTrue at h
  split at h
  · rw [h]
  · cases h

theorem value_eq_refl {O : Oracle} (hO : O.Sound) (P : Program) {v : Value}
    (h : primValue v = true) : O.value_eq P v v = .Ok true := by
  rw [hO.value_eq]
  cases v <;> simp_all [primValue]

theorem real_prim {n d : Int} {v : Value} (h : real n d = .Ok v) : primValue v = true := by
  unfold real at h
  split at h
  · cases h
  · cases h; rfl

section
variable {O : Oracle} {P : Program}

theorem eval_plus_ok {fuel : Int} {env : Env} {a b : Expr} {v : Value}
    (h : eval O P fuel env (.Plus a b) = .Ok v) :
    ∃ x y, eval O P fuel env a = .Ok x ∧ eval O P fuel env b = .Ok y ∧ arith_plus x y = .Ok v := by
  rw [eval] at h
  split at h
  · next x hx =>
    split at h
    · next y hy => exact ⟨x, y, hx, hy, h⟩
    · cases h
    · cases h
  · cases h
  · cases h

theorem eval_minus_ok {fuel : Int} {env : Env} {a b : Expr} {v : Value}
    (h : eval O P fuel env (.Minus a b) = .Ok v) :
    ∃ x y, eval O P fuel env a = .Ok x ∧ eval O P fuel env b = .Ok y ∧ arith_minus x y = .Ok v := by
  rw [eval] at h
  split at h
  · next x hx =>
    split at h
    · next y hy => exact ⟨x, y, hx, hy, h⟩
    · cases h
    · cases h
  · cases h
  · cases h

theorem eval_times_ok {fuel : Int} {env : Env} {a b : Expr} {v : Value}
    (h : eval O P fuel env (.Times a b) = .Ok v) :
    ∃ x y, eval O P fuel env a = .Ok x ∧ eval O P fuel env b = .Ok y ∧ arith_times x y = .Ok v := by
  rw [eval] at h
  split at h
  · next x hx =>
    split at h
    · next y hy => exact ⟨x, y, hx, hy, h⟩
    · cases h
    · cases h
  · cases h
  · cases h

theorem eval_equals_ok {fuel : Int} {env : Env} {a b : Expr} {v : Value}
    (h : eval O P fuel env (.Equals a b) = .Ok v) :
    ∃ x y s, eval O P fuel env a = .Ok x ∧ eval O P fuel env b = .Ok y ∧
      O.value_eq P x y = .Ok s ∧ v = .BoolV s := by
  rw [eval] at h
  split at h
  · next x hx =>
    split at h
    · next y hy =>
      split at h
      · next s hs => cases h; exact ⟨x, y, s, hx, hy, hs, rfl⟩
      · cases h
      · cases h
    · cases h
    · cases h
  · cases h
  · cases h

theorem eval_int {fuel : Int} {env : Env} {i : Int} {v : Value}
    (h : eval O P fuel env (.IntegerLiteral i) = .Ok v) : v = .IntV i := by
  rw [eval] at h; cases h; rfl

theorem arith_prim {x y v : Value} {f : Value → Value → Result Value}
    (hf : f = arith_plus ∨ f = arith_minus ∨ f = arith_times) (h : f x y = .Ok v) :
    primValue v = true := by
  rcases hf with rfl | rfl | rfl
  all_goals
    cases x <;> cases y <;> simp only [arith_plus, arith_minus, arith_times] at h <;>
      first
      | (cases h; rfl)
      | exact real_prim h
      | (split at h <;> cases h; rfl)
      | cases h

theorem primShaped_prim {Fs : List Fact} {fuel : Int} {env : Env} {a : Expr} {v : Value}
    (hs : primShaped Fs a = true) (hF : ∀ f ∈ Fs, f.Holds O P fuel env)
    (hv : eval O P fuel env a = .Ok v) : primValue v = true := by
  cases a
  case Variable x =>
    obtain ⟨f, hf, hm⟩ := List.any_eq_true.mp hs
    cases f with
    | prim y =>
      simp only [beq_iff_eq] at hm
      subst hm
      obtain ⟨w, hw, hp⟩ := hF _ hf
      rw [eval] at hv
      rw [hv] at hw; cases hw; exact hp
    | _ => simp at hm
  case Equals => obtain ⟨x, y, s, -, -, -, rfl⟩ := eval_equals_ok hv; rfl
  case Plus => obtain ⟨x, y, -, -, h⟩ := eval_plus_ok hv; exact arith_prim (.inl rfl) h
  case Minus => obtain ⟨x, y, -, -, h⟩ := eval_minus_ok hv; exact arith_prim (.inr (.inl rfl)) h
  case Times => obtain ⟨x, y, -, -, h⟩ := eval_times_ok hv; exact arith_prim (.inr (.inr rfl)) h
  case LessThan | GreaterThan | LessEquals | GreaterEquals =>
    rw [eval] at hv
    repeat' split at hv
    all_goals first | (cases hv; rfl) | cases hv
  case Not =>
    rw [eval] at hv
    repeat' split at hv
    all_goals first | (cases hv; rfl) | cases hv
  all_goals first
    | (rw [eval] at hv; cases hv; rfl)
    | simp [primShaped] at hs

theorem arithCheck_refines (hO : O.Sound) {Fs : List Fact} {t t' : Expr}
    (h : arithCheck Fs t t' = true) : Refines O P Fs t t' := by
  intro fuel env v hF hv
  unfold arithCheck at h
  split at h
  · next a b =>
    obtain ⟨x, y, hx, hy, hxy⟩ := eval_times_ok hv
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (⟨h0, h | h⟩ | ⟨h1, he⟩) | ⟨h1, he⟩
    · rw [isInt_eq h0]; rw [isInt_eq h] at hx; rw [eval_int hx] at hxy
      cases y <;> simp [arith_times] at hxy
      subst hxy; simp [eval]
    · rw [isInt_eq h0]; rw [isInt_eq h] at hy; rw [eval_int hy] at hxy
      cases x <;> simp [arith_times] at hxy
      · subst hxy; simp [eval]
      all_goals (split at hxy <;> cases hxy)
    · rw [← exprEq_eq _ _ _ he, hy]; rw [isInt_eq h1] at hx; rw [eval_int hx] at hxy
      cases y <;> simp [arith_times] at hxy
      rw [← hxy]
    · rw [← exprEq_eq _ _ _ he, hx]; rw [isInt_eq h1] at hy; rw [eval_int hy] at hxy
      cases x <;> simp [arith_times] at hxy
      · rw [← hxy]
      all_goals (split at hxy <;> cases hxy)
  · next a b =>
    obtain ⟨x, y, hx, hy, hxy⟩ := eval_plus_ok hv
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h0, he⟩ | ⟨h0, he⟩
    · rw [← exprEq_eq _ _ _ he, hy]; rw [isInt_eq h0] at hx; rw [eval_int hx] at hxy
      cases y <;> simp [arith_plus] at hxy
      rw [← hxy]
    · rw [← exprEq_eq _ _ _ he, hx]; rw [isInt_eq h0] at hy; rw [eval_int hy] at hxy
      cases x <;> simp [arith_plus] at hxy
      · rw [← hxy]
      all_goals (split at hxy <;> cases hxy)
  · next a b =>
    obtain ⟨x, y, hx, hy, hxy⟩ := eval_minus_ok hv
    simp only [Bool.and_eq_true] at h
    obtain ⟨h0, he⟩ := h
    rw [← exprEq_eq _ _ _ he, hx]; rw [isInt_eq h0] at hy; rw [eval_int hy] at hxy
    cases x <;> simp [arith_minus] at hxy
    · rw [← hxy]
    all_goals (split at hxy <;> cases hxy)
  · next a b =>
    obtain ⟨x, y, s, hx, hy, hs, rfl⟩ := eval_equals_ok hv
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨ht, he⟩, hp⟩ := h
    rw [← exprEq_eq _ _ _ he, hx] at hy
    cases hy
    rw [value_eq_refl hO P (primShaped_prim hp hF hx)] at hs
    cases hs
    rw [isTrue_eq ht]; simp [eval]
  · cases h

end

/-! ## Ground terms -/

/-- The value of a result, if it has one. -/
def okOf : Result Value → Option Value
  | .Ok v => some v
  | _ => none

/-- The Boolean of a result, if it has one. -/
def okB : Result Bool → Option Bool
  | .Ok b => some b
  | _ => none

/-- Whether two values are equal, where the first is an integer or a Boolean, which the
semantics compares by their equality. -/
def eqLit : Value → Value → Option Value
  | .IntV a, .IntV b => some (.BoolV (a == b))
  | .IntV _, _ => some (.BoolV false)
  | .BoolV a, .BoolV b => some (.BoolV (a == b))
  | .BoolV _, _ => some (.BoolV false)
  | _, _ => none

/-- The value of a ground term of literals, arithmetic, comparisons, conditionals and
concatenations of strings, which it has in every environment, `n` deep. -/
def geval : Nat → Expr → Option Value
  | 0, _ => none
  | n + 1, e =>
    match e with
    | .IntegerLiteral i => some (.IntV i)
    | .BooleanLiteral b => some (.BoolV b)
    | .StringLiteral cs => some (.StringV cs)
    | .BVLiteral s w x => some (.BVV s w x)
    | .Plus a b => (geval n a).bind fun x => (geval n b).bind fun y => okOf (arith_plus x y)
    | .Minus a b => (geval n a).bind fun x => (geval n b).bind fun y => okOf (arith_minus x y)
    | .Times a b => (geval n a).bind fun x => (geval n b).bind fun y => okOf (arith_times x y)
    | .StringConcat a b =>
      (geval n a).bind fun
        | .StringV x => (geval n b).bind fun
          | .StringV y => some (.StringV (append_chars x y))
          | _ => none
        | _ => none
    | .Not a => (geval n a).bind fun
      | .BoolV b => some (.BoolV !b)
      | _ => none
    | .Equals a b => (geval n a).bind fun x => (geval n b).bind fun y => eqLit x y
    | .LessThan a b =>
      (geval n a).bind fun x => (geval n b).bind fun y => (okB (arith_lt x y)).map .BoolV
    | .GreaterThan a b =>
      (geval n a).bind fun x => (geval n b).bind fun y => (okB (arith_lt y x)).map .BoolV
    | .LessEquals a b =>
      (geval n a).bind fun x => (geval n b).bind fun y => (okB (arith_le x y)).map .BoolV
    | .GreaterEquals a b =>
      (geval n a).bind fun x => (geval n b).bind fun y => (okB (arith_le y x)).map .BoolV
    | .IfExpr c a b => (geval n c).bind fun
      | .BoolV true => geval n a
      | .BoolV false => geval n b
      | _ => none
    | _ => none

/-- Two values of literals that are the same. -/
def litEq : Value → Value → Bool
  | .IntV a, .IntV b => a == b
  | .BoolV a, .BoolV b => a == b
  | .StringV a, .StringV b => a == b
  | .BVV s w x, .BVV s' w' x' => s == s' && w == w' && x == x'
  | _, _ => false

/-- `evaluate`: a ground term is its value. -/
def evaluateCheck (t t' : Expr) : Bool :=
  match geval 100 t, geval 100 t' with
  | some v, some w => litEq v w
  | _, _ => false

theorem okOf_eq {r : Result Value} {v : Value} (h : okOf r = some v) : r = .Ok v := by
  unfold okOf at h; split at h <;> cases h; rfl

theorem litEq_eq {v w : Value} (h : litEq v w = true) : v = w := by
  unfold litEq at h
  split at h <;> simp_all

section
variable {O : Oracle} {P : Program}

theorem geval_not {n : Nat} {a : Expr} {b : Bool} (h : geval n a = some (.BoolV b)) :
    geval (n + 1) (.Not a) = some (.BoolV !b) := by
  simp [geval, h]

theorem okB_eq {r : Result Bool} {b : Bool} (h : okB r = some b) : r = .Ok b := by
  unfold okB at h; split at h <;> cases h; rfl

theorem geval_eval (hO : O.Sound) {fuel : Int} {env : Env} :
    ∀ n e {v : Value}, geval n e = some v → eval O P fuel env e = .Ok v
  | 0, _, _, h => by simp [geval] at h
  | n + 1, e, v, h => by
    have ih := @geval_eval hO fuel env n
    unfold geval at h
    split at h
    all_goals first
      | (cases h; rw [eval])
      | skip
    · obtain ⟨x, hx, y, hy, h⟩ : ∃ x, geval n _ = some x ∧ ∃ y, geval n _ = some y ∧ _ := by
        simpa only [Option.bind_eq_some_iff] using h
      rw [eval, ih _ hx, ih _ hy]; exact okOf_eq h
    · obtain ⟨x, hx, y, hy, h⟩ : ∃ x, geval n _ = some x ∧ ∃ y, geval n _ = some y ∧ _ := by
        simpa only [Option.bind_eq_some_iff] using h
      rw [eval, ih _ hx, ih _ hy]; exact okOf_eq h
    · obtain ⟨x, hx, y, hy, h⟩ : ∃ x, geval n _ = some x ∧ ∃ y, geval n _ = some y ∧ _ := by
        simpa only [Option.bind_eq_some_iff] using h
      rw [eval, ih _ hx, ih _ hy]; exact okOf_eq h
    · next a b =>
      obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · next cs =>
        obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
        split at h
        · next ds =>
          cases h
          rw [eval]
          simp only [eval_string, ih _ hx, ih _ hy]
        · cases h
      · cases h
    · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · cases h
        rw [eval]
        simp [eval_bool, ih _ hx]
      · cases h
    · obtain ⟨x, hx, y, hy, h⟩ : ∃ x, geval n _ = some x ∧ ∃ y, geval n _ = some y ∧ _ := by
        simpa only [Option.bind_eq_some_iff] using h
      rw [eval, ih _ hx, ih _ hy]
      cases x <;> cases y <;> simp [eqLit] at h <;> subst h <;> simp [hO.value_eq] <;> rfl
    · obtain ⟨x, hx, y, hy, h⟩ : ∃ x, geval n _ = some x ∧ ∃ y, geval n _ = some y ∧ _ := by
        simpa only [Option.bind_eq_some_iff] using h
      rw [eval, ih _ hx, ih _ hy]
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [okB_eq hb]
    · obtain ⟨x, hx, y, hy, h⟩ : ∃ x, geval n _ = some x ∧ ∃ y, geval n _ = some y ∧ _ := by
        simpa only [Option.bind_eq_some_iff] using h
      rw [eval, ih _ hx, ih _ hy]
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [okB_eq hb]
    · obtain ⟨x, hx, y, hy, h⟩ : ∃ x, geval n _ = some x ∧ ∃ y, geval n _ = some y ∧ _ := by
        simpa only [Option.bind_eq_some_iff] using h
      rw [eval, ih _ hx, ih _ hy]
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [okB_eq hb]
    · obtain ⟨x, hx, y, hy, h⟩ : ∃ x, geval n _ = some x ∧ ∃ y, geval n _ = some y ∧ _ := by
        simpa only [Option.bind_eq_some_iff] using h
      rw [eval, ih _ hx, ih _ hy]
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [okB_eq hb]
    · next c a b =>
      obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rw [eval]; simp [eval_bool, ih _ hx, ih _ h]
      · rw [eval]; simp [eval_bool, ih _ hx, ih _ h]
      · cases h
    · cases h

theorem evaluateCheck_refines (hO : O.Sound) {Fs : List Fact} {t t' : Expr}
    (h : evaluateCheck t t' = true) : Refines O P Fs t t' := by
  intro fuel env v _ hv
  unfold evaluateCheck at h
  split at h
  · next v0 w h1 h2 =>
    rw [geval_eval hO _ _ h1] at hv
    cases hv
    rw [geval_eval hO _ _ h2, litEq_eq h]
  · cases h

end

/-! ## Lambdas that differ at a witness -/

/-- The integer literals of `e`, `n` deep. -/
def intLits : Nat → Expr → List Int
  | 0, _ => []
  | _ + 1, .IntegerLiteral i => [i]
  | n + 1, e => match Inox.Lowered.kids e with
    | some (_, es) => es.flatMap (intLits n)
    | none => []

/-- Two values that the semantics compares as different: integers or Booleans. -/
def distinctLits : Value → Value → Bool
  | .IntV a, .IntV b => a != b
  | .BoolV a, .BoolV b => a != b
  | _, _ => false

/-- The body `b` of a lambda of the parameter `x` is the ground value `v` at the integer `i`. -/
def bodyAt (x : Id) (b : Expr) (i : Int) : Option Value :=
  (subst x (.IntegerLiteral i) 100 b).bind (geval 100)

/-- `evaluate`: two lambdas of a parameter of the integers are different where their bodies
are different values at an integer, which is looked for around the literals of the bodies. -/
def lamNeCheck (t t' : Expr) : Bool :=
  match t, t' with
  | .Equals (.Lambda [.Param x .IntegerType] b) (.Lambda [.Param y .IntegerType] b'),
      .BooleanLiteral false =>
    ((0 :: intLits 100 b ++ intLits 100 b').flatMap fun i => [i - 1, i, i + 1]).any fun i =>
      match bodyAt x b i, bodyAt y b' i with
      | some v, some w => distinctLits v w
      | _, _ => false
  | _, _ => false

section
variable {O : Oracle} {P : Program}

/-- A closure of a parameter of the integers, whose body is the ground value `w` at `i`, has
that value at `i` wherever it has one, and with fuel. -/
theorem apply_at (hO : O.Sound) {x : Id} {b : Expr} {i : Int} {w : Value} {tys : List TypeBinding}
    {vars : List Binding} (h : bodyAt x b i = some w) :
    apply O P 1 (.ClosureV [.Param x .IntegerType] b (.Env tys vars)) [.IntV i] = .Ok w ∧
    ∀ fuel a, apply O P fuel (.ClosureV [.Param x .IntegerType] b (.Env tys vars)) [.IntV i] =
      .Ok a → a = w := by
  obtain ⟨e, he, hg⟩ := Option.bind_eq_some_iff.mp h
  have key : ∀ fuel : Int, eval O P fuel (Env.Env tys (append_env [.Binding x (.IntV i)] vars)) b =
      .Ok w := by
    intro fuel
    have hs := subst_eval (O := O) (P := P) (fuel := fuel) (env := .Env tys vars)
      (x := x) (vw := .IntV i) (by rw [eval]) 100 b e he
    simp only [env_bind] at hs
    simp only [append_env]
    rw [hs, geval_eval hO 100 e hg]
  refine ⟨?_, fun fuel a ha => ?_⟩
  · simp only [apply, param_ids, bind_all]
    simpa using key 0
  · simp only [apply, param_ids, bind_all] at ha
    split at ha
    · cases ha
    · try simp only at ha
      rw [key] at ha
      cases ha; rfl

theorem lamNeCheck_refines (hO : O.Sound) {Fs : List Fact} {t t' : Expr}
    (h : lamNeCheck t t' = true) : Refines O P Fs t t' := by
  intro fuel env v _ hv
  unfold lamNeCheck at h
  split at h
  · next x b y b' =>
    obtain ⟨i, -, hi⟩ := List.any_eq_true.mp h
    split at hi
    · next w w' h1 h2 =>
      cases env with
      | Env tys vars =>
      simp only [eval] at hv
      rw [hO.value_eq] at hv
      cases P with
      | Program fs cs ss is eqm =>
      cases eqm
      · cases hv
      · obtain ⟨a1, a2⟩ := apply_at (P := .Program fs cs ss is .ExtensionalEquality) hO
          (tys := tys) (vars := vars) h1
        obtain ⟨b1, b2⟩ := apply_at (P := .Program fs cs ss is .ExtensionalEquality) hO
          (tys := tys) (vars := vars) h2
        have hce : O.closures_equal (.Program fs cs ss is .ExtensionalEquality)
            (.ClosureV [.Param x .IntegerType] b (.Env tys vars))
            (.ClosureV [.Param y .IntegerType] b' (.Env tys vars)) = false := by
          rw [hO.closures_equal]
          simp only [decide_eq_false_iff_not]
          intro hall
          have ht : O.params_have_types (.Program fs cs ss is .ExtensionalEquality) (.Env tys vars)
              [.IntV i] [.Param x .IntegerType] = true := by
            rw [hO.params_have_types]
            simp only [Bool.and_eq_true]
            rw [hO.params_have_types, hO.has_type]
            simp
          have h0 := hall [.IntV i]
          simp only [ht, Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at h0
          rcases h0 with h0 | h0
          · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h0
            exact (h0 1 w).1 a1
          · obtain ⟨f, a, c, hac⟩ := h0
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hac
            obtain ⟨⟨ha, hc⟩, he⟩ := hac
            rw [a2 f a ha, b2 f c hc] at he
            cases w <;> cases w' <;> simp [distinctLits] at hi <;> simp [hO.value_eq, hi] at he
        simp only [hce] at hv
        cases hv
        rw [eval]
    · cases hi
  · cases h

end

/-! ## Lambdas that are the same up to the names of their parameters -/

/-- `evaluate`: two lambdas of a parameter of the integers or the Booleans whose bodies are the
same up to the name of the parameter, of a primitive value, are equal. -/
def alphaCheck (t t' : Expr) : Bool :=
  match t, t' with
  | .Equals (.Lambda [.Param x T] b) (.Lambda [.Param y T'] b'), .BooleanLiteral true =>
    (match T with
      | .IntegerType | .BooleanType => true
      | _ => false) && Inox.Lowered.tyEq 100 T T' && primShaped [.prim x] b &&
      (subst x (.Variable y) 100 b).any (exprEq 1000 · b') &&
      (subst y (.Variable x) 100 b).any (exprEq 1000 · b)
  | _, _ => false

section
variable {O : Oracle} {P : Program}

/-- The body of a lambda and its renaming have the same values. -/
theorem alpha_eval {x y : Id} {b b' : Expr} {fuel : Int} {tys : List TypeBinding}
    {vars : List Binding} {v : Value} (h1 : subst x (.Variable y) 100 b = some b')
    (h2 : subst y (.Variable x) 100 b = some b) :
    eval O P fuel (.Env tys (.Binding x v :: vars)) b =
      eval O P fuel (.Env tys (.Binding y v :: vars)) b' := by
  have hA := subst_eval_gen (O := O) (P := P) (fuel := fuel)
    (env' := .Env tys (.Binding x v :: .Binding y v :: vars))
    (env := .Env tys (.Binding y v :: vars))
    (x := x) (w := .Variable y) rfl (fun z => by
      by_cases hzx : z = x
      · subst hzx; simp [eval, env_vars, lookup_var]
      · by_cases hzy : z = y
        · subst hzy; simp [eval, env_vars, lookup_var, hzx]
        · simp [eval, env_vars, lookup_var, hzx, hzy]) 100 b b' h1
  have hB := subst_eval_gen (O := O) (P := P) (fuel := fuel)
    (env' := .Env tys (.Binding x v :: .Binding y v :: vars))
    (env := .Env tys (.Binding x v :: vars))
    (x := y) (w := .Variable x) rfl (fun z => by
      by_cases hzx : z = x
      · subst hzx
        by_cases hzy : z = y
        · subst hzy; simp [eval, env_vars, lookup_var]
        · simp [eval, env_vars, lookup_var, hzy]
      · by_cases hzy : z = y
        · subst hzy; simp [eval, env_vars, lookup_var, hzx]
        · simp [eval, env_vars, lookup_var, hzx, hzy]) 100 b b h2
  rw [← hB, hA]

theorem alphaCheck_refines (hO : O.Sound) {Fs : List Fact} {t t' : Expr}
    (h : alphaCheck t t' = true) : Refines O P Fs t t' := by
  intro fuel env v _ hv
  unfold alphaCheck at h
  split at h
  · next x T b y T' b' =>
    simp only [Bool.and_eq_true, Option.any_eq_true] at h
    obtain ⟨⟨⟨⟨hT, hTT⟩, hp⟩, ⟨b1, hb1, he1⟩⟩, ⟨b2, hb2, he2⟩⟩ := h
    rw [exprEq_eq _ _ _ he1] at hb1
    rw [exprEq_eq _ _ _ he2] at hb2
    rw [← Inox.Lowered.tyEq_eq _ _ _ hTT] at hv
    cases env with
    | Env tys vars =>
    simp only [eval] at hv
    rw [hO.value_eq] at hv
    cases P with
    | Program fs cs ss is eqm =>
    cases eqm
    · cases hv
    · have hap : ∀ fuel vs, apply O (.Program fs cs ss is .ExtensionalEquality) fuel
          (.ClosureV [.Param x T] b (.Env tys vars)) vs =
          apply O (.Program fs cs ss is .ExtensionalEquality) fuel
          (.ClosureV [.Param y T] b' (.Env tys vars)) vs := by
        intro fuel vs
        simp only [apply, param_ids]
        split
        · rfl
        · cases vs with
          | nil => simp [bind_all]
          | cons v vs =>
            cases vs with
            | nil => simp only [bind_all, append_env]; exact alpha_eval hb1 hb2
            | cons _ _ => simp [bind_all]
      have hce : O.closures_equal (.Program fs cs ss is .ExtensionalEquality)
          (.ClosureV [.Param x T] b (.Env tys vars))
          (.ClosureV [.Param y T] b' (.Env tys vars)) = true := by
        rw [hO.closures_equal]
        simp only [decide_eq_true_eq]
        intro vs
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
        by_cases hty : O.params_have_types (.Program fs cs ss is .ExtensionalEquality)
          (.Env tys vars) vs [.Param x T] = true
        · right
          by_cases hex : ∃ fuel a, apply O (.Program fs cs ss is .ExtensionalEquality) fuel
              (.ClosureV [.Param x T] b (.Env tys vars)) vs = .Ok a
          · right
            obtain ⟨f, a, ha⟩ := hex
            refine ⟨f, a, a, ?_⟩
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            refine ⟨⟨ha, by rw [← hap]; exact ha⟩, value_eq_refl hO _ ?_⟩
            -- the value of the body is primitive
            rw [hO.params_have_types] at hty
            cases vs with
            | nil => simp at hty
            | cons w ws =>
              simp only [Bool.and_eq_true] at hty
              obtain ⟨hw, -⟩ := hty
              simp only [apply] at ha
              split at ha
              · cases ha
              · cases ws with
                | cons _ _ =>
                  simp [param_ids, bind_all] at ha
                | nil =>
                  simp only [param_ids, bind_all, append_env] at ha
                  refine primShaped_prim hp (fun f hf => ?_) ha
                  simp only [List.mem_singleton] at hf
                  subst hf
                  refine ⟨w, by simp [env_vars, lookup_var], ?_⟩
                  rw [hO.has_type] at hw
                  split at hT <;> simp at hT
                  all_goals (cases w <;> simp at hw <;> rfl)
          · left
            intro f a
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
            have hn : ¬ apply O (.Program fs cs ss is .ExtensionalEquality) f
                (.ClosureV [.Param x T] b (.Env tys vars)) vs = .Ok a := fun h => hex ⟨f, a, h⟩
            exact ⟨hn, by rw [← hap]; exact hn⟩
        · first | (left; left; simpa using hty) | (left; simpa using hty) | simp [hty]
      simp only [hce] at hv
      cases hv
      rw [eval]
  · cases h

end

/-! ## Quantifiers over variables that the body doesn't mention -/

/-- Parameters of the types `Ts`. -/
def witParams : List Ty → List Param
  | [] => []
  | T :: Ts => .Param "w" T :: witParams Ts

/-- An expression whose value is of the type `T`: a literal. -/
def baseWitness : Ty → Option Expr
  | .IntegerType => some (.IntegerLiteral 0)
  | .BooleanType => some (.BooleanLiteral true)
  | _ => none

/-- An expression whose value is of the type `T`: a literal, or a constant function. -/
def witness : Ty → Option Expr
  | .FunctionType Ts U => (baseWitness U).map (.Lambda (witParams Ts))
  | T => baseWitness T

/-- The types of the parameters have values. -/
def inhabited : List Param → Bool
  | [] => true
  | .Param _ T :: ps => (witness T).isSome && inhabited ps

/-- `unused`: a quantifier over parameters whose types have values, of a ground body, is the
body. -/
def unusedCheck (t t' : Expr) : Bool :=
  match t with
  | .Forall ps b => exprEq 1000 b t' && inhabited ps && (geval 1000 b).isSome
  | .Not (.Forall ps (.Not b)) =>
    exprEq 1000 b t' && inhabited ps &&
      match geval 1000 b with
      | some (.BoolV _) => true
      | _ => false
  | _ => false

section
variable {O : Oracle} {P : Program}

theorem same_arity_wit : ∀ Ts : List Ty, same_arity (witParams Ts) Ts = true
  | [] => by simp [witParams, same_arity]
  | T :: Ts => by simp [witParams, same_arity, same_arity_wit Ts]

theorem have_types_length (hO : O.Sound) {env : Env} :
    ∀ {vs : List Value} {Ts : List Ty}, O.have_types P env vs Ts = true → vs.length = Ts.length
  | [], [], _ => rfl
  | [], _ :: _, h => by rw [hO.have_types] at h; simp at h
  | _ :: _, [], h => by rw [hO.have_types] at h; simp at h
  | _ :: _, _ :: _, h => by
    rw [hO.have_types] at h
    simp only [Bool.and_eq_true] at h
    simp [have_types_length hO h.2]

theorem params_length (hO : O.Sound) :
    ∀ {env : Env} {vs : List Value} {ps : List Param}, O.params_have_types P env vs ps = true →
      vs.length = ps.length
  | _, [], [], _ => rfl
  | _, [], _ :: _, h => by rw [hO.params_have_types] at h; simp at h
  | _, _ :: _, [], h => by rw [hO.params_have_types] at h; simp at h
  | _, _ :: _, .Param _ _ :: _, h => by
    rw [hO.params_have_types] at h
    simp only [Bool.and_eq_true] at h
    simp [params_length hO h.2]

theorem bind_of_length : ∀ (ids : List Id) (vs : List Value), vs.length = ids.length →
    ∃ bs, bind_all ids vs = .Ok bs
  | [], [], _ => ⟨[], by simp [bind_all]⟩
  | x :: ids, v :: vs, h => by
    obtain ⟨bs, hbs⟩ := bind_of_length ids vs (by simpa using h)
    exact ⟨.Binding x v :: bs, by simp [bind_all, hbs]⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem param_ids_length : ∀ ps : List Param, (param_ids ps).length = ps.length
  | [] => rfl
  | .Param _ _ :: ps => by simp [param_ids, param_ids_length ps]

theorem witParams_length : ∀ Ts : List Ty, (witParams Ts).length = Ts.length
  | [] => rfl
  | _ :: Ts => by simp [witParams, witParams_length Ts]

theorem baseWitness_typed (hO : O.Sound) {T : Ty} {w : Expr} (h : baseWitness T = some w)
    (fuel : Int) (env : Env) :
    ∃ v, eval O P fuel env w = .Ok v ∧ ∀ env', O.has_type P env' v T = true := by
  unfold baseWitness at h
  split at h
  · cases h; exact ⟨.IntV 0, by simp only [eval], fun env' => by rw [hO.has_type]⟩
  · cases h; exact ⟨.BoolV true, by simp only [eval], fun env' => by rw [hO.has_type]⟩
  · cases h

/-- A witness has a value of its type. -/
theorem witness_typed (hO : O.Sound) {T : Ty} {w : Expr} (h : witness T = some w)
    (fuel : Int) (env : Env) :
    ∃ v, eval O P fuel env w = .Ok v ∧ ∀ env', O.has_type P env' v T = true := by
  unfold witness at h
  split at h
  · next Ts U =>
    obtain ⟨wu, hu, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨.ClosureV (witParams Ts) wu env, by simp only [eval], fun env' => ?_⟩
    rw [hO.has_type]
    simp only [same_arity_wit, Bool.true_and]
    rw [hO.function_has_type]
    simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true]
    intro vs
    by_cases hvs : O.have_types P env' vs Ts = true
    · right
      obtain ⟨bs, hbs⟩ := bind_of_length (param_ids (witParams Ts)) vs
        (by rw [param_ids_length, witParams_length]; exact have_types_length hO hvs)
      cases env with
      | Env tys vars =>
      obtain ⟨r, hr, hrt⟩ := baseWitness_typed hO hu 0 (Env.Env tys (append_env bs vars))
      refine ⟨1, r, ?_, hrt env'⟩
      simp only [apply, hbs]
      simpa using hr
    · left; simpa using hvs
  · exact baseWitness_typed hO h fuel env

/-- Parameters whose types have values have values of their types. -/
theorem inhabited_vals (hO : O.Sound) : ∀ (ps : List Param), inhabited ps = true →
    ∀ env, ∃ vs, O.params_have_types P env vs ps = true
  | [], _, env => ⟨[], by rw [hO.params_have_types]⟩
  | .Param x T :: ps, h, env => by
    simp only [inhabited, Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨⟨w, hw⟩, hps⟩ := h
    obtain ⟨v, _, hv⟩ := witness_typed (P := P) hO hw 0 env
    obtain ⟨vs, hvs⟩ := inhabited_vals hO ps hps (env_bind env x v)
    exact ⟨v :: vs, by rw [hO.params_have_types]; simp [hv env, hvs]⟩

/-- A quantifier over parameters whose types have values, of a body that has the same value in
every environment, has that value. -/
theorem forall_const (hO : O.Sound) {ps : List Param} {c : Expr} {vc : Value} {fuel : Int}
    {env : Env} (hc : ∀ env', eval O P fuel env' c = .Ok vc) (hinh : inhabited ps = true)
    {w : Value} (hv : eval O P fuel env (.Forall ps c) = .Ok w) : vc = w := by
  have hinst : ∀ vs, O.params_have_types P env vs ps = true →
      instance_ O P fuel env ps vs c = .Ok vc := by
    intro vs hvs
    obtain ⟨bs, hbs⟩ := bind_of_length (param_ids ps) vs
      (by rw [param_ids_length]; exact params_length hO hvs)
    cases env
    simp only [instance_, hbs]
    exact hc _
  obtain ⟨vs0, hvs0⟩ := inhabited_vals hO ps hinh env
  simp only [eval] at hv
  rw [hO.forall_result] at hv
  split at hv
  · next hex =>
    cases hv
    simp only [decide_eq_true_eq, Bool.and_eq_true] at hex
    obtain ⟨vs, hvs, hf⟩ := hex
    rw [hinst vs hvs] at hf
    cases hf; rfl
  · split at hv
    · cases hv
    · split at hv
      · next hall =>
        cases hv
        simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hall
        rcases hall vs0 with h0 | h0
        · rw [hvs0] at h0; cases h0
        · rw [hinst vs0 hvs0] at h0; cases h0; rfl
      · cases hv

theorem unusedCheck_refines (hO : O.Sound) {Fs : List Fact} {t t' : Expr}
    (h : unusedCheck t t' = true) : Refines O P Fs t t' := by
  intro fuel env v _ hv
  unfold unusedCheck at h
  split at h
  · next ps b =>
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨⟨hb, hinh⟩, vb, hg⟩ := h
    rw [← exprEq_eq _ _ _ hb, geval_eval hO 1000 b hg]
    rw [forall_const hO (fun _ => geval_eval hO 1000 b hg) hinh hv]
  · next ps b =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hb, hinh⟩, hg⟩ := h
    split at hg
    · next bb hgb =>
      have hnb : geval 1001 (.Not b) = some (.BoolV !bb) := by
        exact geval_not hgb
      simp only [eval] at hv
      split at hv
      · next w hw =>
        rw [eval_bool_ok] at hw
        have := forall_const hO (fun _ => geval_eval hO 1001 (.Not b) hnb) hinh hw
        cases this
        cases hv
        rw [← exprEq_eq _ _ _ hb, geval_eval hO 1000 b hgb]
        simp
      · cases hv
      · cases hv
    · cases hg
  · cases h
end

/-! ## Values of datatypes -/

/-- The variable `x` has a value of a type, under the facts `Fs`. -/
def typedVar (Fs : List Fact) (x : Id) : Bool :=
  Fs.any fun
    | .typed y _ => y == x
    | _ => false

/-- No datatype of `ss` has an equality of its own. -/
def noEq (ss : List ADTSort) : Bool :=
  ss.all fun | .Sort _ _ _ eq => eq.isNone

/-- The datatype `s` of `ss` has no invariant. -/
def noInvOf (ss : List ADTSort) (s : Id) : Bool :=
  match lookup_sort ss s with
  | .Ok (.Sort _ [] none _) => true
  | _ => false

/-- The name of a field. -/
def fieldName : Param → Id
  | .Param f _ => f

/-- `e` selects the field `p` of the variable `x`. -/
def isSel (x : Id) (p : Param) (e : Expr) : Bool :=
  match e with
  | .ADTSelector (.Variable y) f => y == x && f == fieldName p
  | _ => false

/-- `eta`: the construction of the fields of a variable of a datatype, in their order, is the
variable, where the first field is of no other constructor. -/
def etaCheck (cs : List Constructor) (ss : List ADTSort) (Fs : List Fact) (t t' : Expr) :
    Bool :=
  match t, t' with
  | .ADT c [] es, .Variable x =>
    typedVar Fs x &&
    match lookup_ctor cs c with
    | .Ok (.Constructor _ s fs) =>
      noInvOf ss s && decide (fs.map fieldName).Nodup && es.length == fs.length &&
        (es.zip fs).all (fun (e, p) => isSel x p e) &&
        match fs with
        | [] => false
        | p :: _ => cs.all fun
          | .Constructor d _ gs => d == c || !((gs.map fieldName).contains (fieldName p))
    | _ => false
  | _, _ => false

theorem lookup_sort_mem : ∀ {ss : List ADTSort} {s : Id} {srt : ADTSort},
    lookup_sort ss s = .Ok srt → srt ∈ ss
  | [], _, _, h => by simp [lookup_sort] at h
  | .Sort t a b c :: ss, s, srt, h => by
    rw [lookup_sort] at h
    split at h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_sort_mem h)

theorem lookup_ctor_mem : ∀ {cs : List Constructor} {c : Id} {k : Constructor},
    lookup_ctor cs c = .Ok k → k ∈ cs ∧ ∃ s fs, k = .Constructor c s fs
  | [], _, _, h => by simp [lookup_ctor] at h
  | .Constructor d a b :: cs, c, k, h => by
    rw [lookup_ctor] at h
    split at h
    · next hc => cases h; subst hc; exact ⟨List.mem_cons_self, a, b, rfl⟩
    · obtain ⟨hm, hk⟩ := lookup_ctor_mem h
      exact ⟨List.mem_cons_of_mem _ hm, hk⟩

theorem sort_equality_none {fs : List FunDef} {cs : List Constructor} {ss : List ADTSort}
    {is : List Interpretation} {eqm : FunctionEquality} (h : noEq ss = true) (c : Id) :
    sort_equality (.Program fs cs ss is eqm) c = none := by
  simp only [sort_equality]
  repeat' split
  all_goals first
    | rfl
    | (rename_i hs
       have := List.all_eq_true.mp h _ (lookup_sort_mem hs)
       simpa using this)

section
variable {O : Oracle} {P : Program}

mutual
theorem typed_refl (hO : O.Sound) (hEq : ∀ c, sort_equality P c = none)
    {cs : List Constructor} {ss : List ADTSort} :
    ∀ {T : Ty} {v : Value}, OfTy cs ss T v → O.value_eq P v v = .Ok true
  | _, _, .int _ => by rw [hO.value_eq]; simp
  | _, _, .bool _ => by rw [hO.value_eq]; simp
  | _, _, .real _ => by rw [hO.value_eq]; simp
  | _, _, .bv _ => by rw [hO.value_eq]; simp
  | _, _, .adt _ _ _ hvs => by
    rw [hO.value_eq]
    simp only [hEq, dite_true]
    exact fields_refl hO hEq hvs
theorem fields_refl (hO : O.Sound) (hEq : ∀ c, sort_equality P c = none)
    {cs : List Constructor} {ss : List ADTSort} :
    ∀ {fs : List Param} {vs : List Value}, OfTys cs ss fs vs →
      O.values_eq P vs vs = .Ok true
  | _, _, .nil => by rw [hO.values_eq]
  | _, _, .cons h hr => by
    rw [hO.values_eq]
    simp only [typed_refl hO hEq h, dite_true]
    exact fields_refl hO hEq hr
end

theorem fields_length {cs : List Constructor} {ss : List ADTSort} :
    ∀ {fs : List Param} {vs : List Value},
    OfTys cs ss fs vs → vs.length = fs.length
  | _, _, .nil => rfl
  | _, _, .cons _ hr => by simp [fields_length hr]

theorem select_mem : ∀ {fs : List Param} {vs : List Value} {f : Id} {v : Value},
    select_field fs vs f = .Ok v → f ∈ fs.map fieldName
  | [], _, _, _, h => by simp [select_field] at h
  | .Param g _ :: fs, [], f, v, h => by simp [select_field] at h
  | .Param g _ :: fs, w :: vs, f, v, h => by
    simp only [select_field] at h
    split at h
    · next he => subst he; simp [fieldName]
    · exact List.mem_cons_of_mem _ (select_mem h)

theorem select_app : ∀ {pre : List Param} {vpre : List Value} {f : Id} {T : Ty}
    {suf : List Param} {v : Value} {vsuf : List Value}, pre.length = vpre.length →
    f ∉ pre.map fieldName →
      select_field (pre ++ .Param f T :: suf) (vpre ++ v :: vsuf) f = .Ok v
  | [], [], _, _, _, _, _, _, _ => by simp [select_field]
  | .Param g _ :: pre, w :: vpre, f, T, suf, v, vsuf, hl, hf => by
    simp only [List.map_cons, List.mem_cons, not_or, fieldName] at hf
    simp only [List.cons_append, select_field, Ne.symm hf.1, dite_false]
    exact select_app (by simpa using hl) hf.2
  | [], _ :: _, _, _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, _, _, hl, _ => by simp at hl

theorem eval_sels {fuel : Int} {env : Env} {x c s : Id} {fs : List Param} {w : List Value}
    (hx : lookup_var (env_vars env) x = .Ok (.ADTV c [] w))
    (hcs : lookup_ctor (ctorsOf P) c = .Ok (.Constructor c s fs))
    (hnd : (fs.map fieldName).Nodup) (hlen : w.length = fs.length) :
    ∀ (pre suf : List Param) (vpre vsuf : List Value) (es : List Expr), fs = pre ++ suf →
      w = vpre ++ vsuf → pre.length = vpre.length → es.length = suf.length →
      (es.zip suf).all (fun (e, p) => isSel x p e) = true →
        eval_list O P fuel env es = .Ok vsuf
  | _, [], _, [], [], _, _, _, _, _ => by rw [eval_list]
  | pre, .Param f T :: suf, vpre, v :: vsuf, e :: es, hfs, hw, hl, hle, hall => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨he, hall⟩ := hall
    unfold isSel at he
    split at he
    · next y g =>
      simp only [Bool.and_eq_true, beq_iff_eq, fieldName] at he
      obtain ⟨rfl, rfl⟩ := he
      have hnd' : g ∉ pre.map fieldName := by
        rw [hfs] at hnd
        simp only [List.map_append, List.map_cons, fieldName] at hnd
        exact fun hm => (List.nodup_append.mp hnd).2.2 _ hm _ List.mem_cons_self rfl
      have hsel : eval O P fuel env (.ADTSelector (.Variable y) g) = .Ok v := by
        cases P with
        | Program fns cs ss is eqm =>
        simp only [ctorsOf] at hcs
        rw [eval]
        simp only [eval, hx, hcs]
        rw [hfs, hw]
        exact select_app hl hnd'
      rw [eval_list, hsel]
      simp only
      rw [eval_sels hx hcs hnd hlen (pre ++ [.Param g T]) suf (vpre ++ [v]) vsuf es (by simp [hfs])
        (by simp [hw]) (by simp [hl]) (by simpa using hle) hall]
    · cases he
  | _, [], _, _ :: _, _, hfs, hw, hl, _, _ => by
    subst hfs hw; simp at hlen; omega
  | _, _ :: _, _, [], _, hfs, hw, hl, _, _ => by
    subst hfs hw; simp at hlen; omega
  | _, [], _, [], _ :: _, _, _, _, hle, _ => by simp at hle
  | _, _ :: _, _, _ :: _, [], _, _, _, hle, _ => by simp at hle

theorem typedVar_holds {Fs : List Fact} {x : Id} {fuel : Int} {env : Env}
    (h : typedVar Fs x = true) (hF : ∀ f ∈ Fs, f.Holds O P fuel env) :
    ∃ T w, lookup_var (env_vars env) x = .Ok w ∧ OfTy (ctorsOf P) (sortsOf P) T w := by
  obtain ⟨f, hf, hm⟩ := List.any_eq_true.mp h
  cases f with
  | typed y T =>
    simp only [beq_iff_eq] at hm
    subst hm
    obtain ⟨w, hw, ht⟩ := hF _ hf
    exact ⟨T, w, hw, ht⟩
  | _ => simp at hm

theorem noInvOf_eq {ss : List ADTSort} {s : Id} (h : noInvOf ss s = true) :
    ∃ t eq, lookup_sort ss s = .Ok (.Sort t [] none eq) := by
  unfold noInvOf at h
  split at h
  · next t eq hs => exact ⟨t, eq, hs⟩
  · cases h

/-- `arith` on the equality of a variable of a datatype without an equality of its own with
itself, which is `true`. -/
def reflCheck (ss : List ADTSort) (Fs : List Fact) (t t' : Expr) : Bool :=
  match t with
  | .Equals a b =>
    isTrue t' && exprEq 1000 a b && noEq ss &&
      match a with
      | .Variable x => typedVar Fs x
      | _ => false
  | _ => false

theorem reflCheck_refines (hO : O.Sound) {fns : List FunDef} {cs : List Constructor}
    {ss : List ADTSort} {is : List Interpretation} {eqm : FunctionEquality}
    (hP : P = .Program fns cs ss is eqm) {Fs : List Fact} {t t' : Expr}
    (h : reflCheck ss Fs t t' = true) : Refines O P Fs t t' := by
  intro fuel env v hF hv
  unfold reflCheck at h
  split at h
  · next a b =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨ht, he⟩, hq⟩, hx⟩ := h
    split at hx
    · next x =>
      obtain ⟨T, w, hw, hty⟩ := typedVar_holds hx hF
      obtain ⟨x1, y1, s1, hx1, hy1, hs1, rfl⟩ := eval_equals_ok hv
      rw [← exprEq_eq _ _ _ he, hx1] at hy1
      cases hy1
      rw [eval] at hx1
      rw [hw] at hx1
      cases hx1
      have hEq : ∀ c, sort_equality P c = none := by
        subst hP; exact sort_equality_none hq
      rw [typed_refl hO hEq hty] at hs1
      cases hs1
      rw [isTrue_eq ht]; simp [eval]
    · cases hx
  · cases h

theorem etaCheck_refines (hO : O.Sound) {fns : List FunDef} {cs : List Constructor}
    {ss : List ADTSort} {is : List Interpretation} {eqm : FunctionEquality}
    (hP : P = .Program fns cs ss is eqm) {Fs : List Fact} {t t' : Expr}
    (h : etaCheck cs ss Fs t t' = true) : Refines O P Fs t t' := by
  subst hP
  intro fuel env v hF hv
  unfold etaCheck at h
  split at h
  · next c es x =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨htv, h⟩ := h
    obtain ⟨T, w, hx, ht⟩ := typedVar_holds htv hF
    split at h
    · next c1 s fs hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨hinv, hnd⟩, hle⟩, hall⟩, hu⟩ := h
      cases fs with
      | nil => simp at hu
      | cons p fs' =>
      cases es with
      | nil => simp at hle
      | cons e0 es' =>
      have hall' := hall
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall'
      have hsel0 := hall'.1
      rw [eval] at hv
      split at hv
      · next ws hws =>
        obtain ⟨w0, hw0⟩ := eval_list_ok _ hws e0 List.mem_cons_self
        unfold isSel at hsel0
        split at hsel0
        · next y g =>
          simp only [Bool.and_eq_true, beq_iff_eq] at hsel0
          obtain ⟨rfl, rfl⟩ := hsel0
          rw [eval] at hw0
          simp only [eval, hx] at hw0
          cases ht with
          | int _ => simp at hw0
          | bool _ => simp at hw0
          | real _ => simp at hw0
          | bv _ => simp at hw0
          | @adt c0 s0 tps0 fs0 vs0 tparams0 inv0 eq0 hc0 hs0 hl0 hvs0 =>
            simp only [ctorsOf] at hc0
            simp only [hc0] at hw0
            have hm := select_mem hw0
            have hcc : c0 = c := by
              have := List.all_eq_true.mp hu _ (lookup_ctor_mem hc0).1
              simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
              rcases this with h1 | h1
              · exact h1
              · exact absurd hm (by simpa using h1)
            subst hcc
            rw [hc0] at hc
            cases hc
            obtain ⟨t0, eq0', hs0'⟩ := noInvOf_eq hinv
            simp only [sortsOf] at hs0
            rw [hs0'] at hs0
            cases hs0
            cases tps0 with
            | cons _ _ => simp at hl0
            | nil =>
            simp only [List.zip_nil_left, substParams_nil] at hvs0
            have hl := eval_sels (O := O) (P := .Program fns cs ss is eqm) (fuel := fuel) hx hc0
              hnd (fields_length hvs0) [] (p :: fs') [] vs0 _ rfl rfl rfl hle hall
            rw [hl] at hws
            cases hws
            simp only [construct, hc0, hs0', hO.resolve_all] at hv
            cases hv
            rw [eval]
            exact hx
        · simp at hsel0
      · cases hv
      · cases hv
    · cases h
  · cases h

end



/-- `logic` on a conditional whose branches are the same, which is its branch. -/
def iteCheck (t t' : Expr) : Bool :=
  match t with
  | .IfExpr _ a b => exprEq 1000 a b && exprEq 1000 a t'
  | _ => false

theorem iteCheck_refines {O : Oracle} {P : Program} {Fs : List Fact} {t t' : Expr}
    (h : iteCheck t t' = true) : Refines O P Fs t t' := by
  intro fuel env v _ hv
  unfold iteCheck at h
  split at h
  · next c a b =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨hab, ha⟩ := h
    rw [← exprEq_eq _ _ _ ha]
    rw [← exprEq_eq _ _ _ hab] at hv
    rw [eval] at hv
    split at hv
    · split at hv <;> exact hv
    · cases hv
    · cases hv
  · cases h


/-! ## The steps -/

/-- A step of a simplification: its rule, the position of the subterm that it rewrites, and what
the subterm becomes. -/
structure Step where
  rule : String
  pos : List Nat
  result : Expr

/-- Whether the step of the rule `rule` that rewrites `t` into `t'` under the facts `Fs` holds,
for the rules that are checked, in a program whose constructors are `cs`. A step of `logic`
first binds the variables of the lets around its subterm to their values. -/
def ruleCheck (cs : List Constructor) (ss : List ADTSort) :
    String → List Fact → Expr → Expr → Bool
  | "logic", Fs, t, t' =>
    exprEq 1000 (unlet 100 t) t' || logicCheck (Fs.filterMap Fact.expr?) (unlet 100 t) t' ||
      iteCheck t t'
  | "select", _, t, t' => selectCheck cs t t'
  | "bind", _, t, t' => bindCheck t t'
  | "expand", Fs, t, t' => expandCheck Fs t t'
  | "arith", Fs, t, t' => arithCheck Fs t t' || reflCheck ss Fs t t'
  | "eta", Fs, t, t' => etaCheck cs ss Fs t t'
  | "evaluate", _, t, t' => evaluateCheck t t' || lamNeCheck t t' || alphaCheck t t'
  | "unused", _, t, t' => unusedCheck t t'
  | _, _, _, _ => false

theorem ruleCheck_refines {O : Oracle} {P : Program} {cs : List Constructor}
    {ss : List ADTSort} (hO : O.Sound) (hP : ∃ fs is eqm, P = .Program fs cs ss is eqm)
    {rule : String} {Fs : List Fact} {t t' : Expr} (h : ruleCheck cs ss rule Fs t t' = true) :
    Refines O P Fs t t' := by
  obtain ⟨fns, is, eqm, hP'⟩ := hP
  unfold ruleCheck at h
  split at h
  · simp only [Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · exact refines_trans (unlet_refines 100 t) (by rw [exprEq_eq _ _ _ h]; exact refines_refl)
    · exact refines_trans (unlet_refines 100 t) (logicCheck_refines h)
    · exact iteCheck_refines h
  · exact selectCheck_refines ⟨fns, ss, is, eqm, hP'⟩ h
  · exact bindCheck_refines h
  · exact expandCheck_refines h
  · simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact arithCheck_refines hO h
    · exact reflCheck_refines hO hP' h
  · exact etaCheck_refines hO hP' h
  · simp only [Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · exact evaluateCheck_refines hO h
    · exact lamNeCheck_refines hO h
    · exact alphaCheck_refines hO h
  · exact unusedCheck_refines hO h
  · cases h

/-! ## Steps that keep the values both ways -/

/-- An expression that always has the same value: a literal, or a construction of them of a sort
without invariants, `n` deep. -/
def closedLit (cs : List Constructor) (ss : List ADTSort) : Nat → Expr → Bool
  | 0, _ => false
  | _ + 1, .IntegerLiteral _ | _ + 1, .BooleanLiteral _ => true
  | n + 1, .ADT c _ es => (match lookup_ctor cs c with
      | .Ok (.Constructor _ s _) => noInvOf ss s
      | _ => false) && es.all (closedLit cs ss n)
  | _ + 1, _ => false

/-- `select`, where the subterm also has a value wherever the selected argument has: the other
arguments always have values, and the sort has no invariant. -/
def selectRev (cs : List Constructor) (ss : List ADTSort) (t t' : Expr) : Bool :=
  match t with
  | .ADTSelector (.ADT c _ args) sel =>
    match lookup_ctor cs c with
    | .Ok (.Constructor _ s fields) =>
      noInvOf ss s && (pick fields args sel).any (exprEq 1000 · t') &&
        args.all fun a => exprEq 1000 a t' || closedLit cs ss 100 a
    | _ => false
  | _ => false

/-- Whether the step of the rule `rule` that rewrites `t` into `t'` also has the converse: `t`
has the value of `t'` wherever `t'` has one, as the steps in the bodies of lambdas need. -/
def revCheck (cs : List Constructor) (ss : List ADTSort) :
    String → List Fact → Expr → Expr → Bool
  | "logic", Fs, t, t' => exprEq 1000 t t' || logicCheck (Fs.filterMap Fact.expr?) t' t
  | "select", _, t, t' => selectRev cs ss t t'
  | _, _, _, _ => false

section
variable {O : Oracle} {P : Program}

theorem eval_list_all {fuel : Int} {env : Env} : ∀ (es : List Expr),
    (∀ a ∈ es, ∃ v, eval O P fuel env a = .Ok v) → ∃ vs, eval_list O P fuel env es = .Ok vs
  | [], _ => ⟨[], by rw [eval_list]⟩
  | a :: es, h => by
    obtain ⟨v, hv⟩ := h a List.mem_cons_self
    obtain ⟨vs, hvs⟩ := eval_list_all es fun b hb => h b (List.mem_cons_of_mem _ hb)
    exact ⟨v :: vs, by rw [eval_list, hv, hvs]⟩

theorem closedLit_eval {fns : List FunDef} {cs : List Constructor} {ss : List ADTSort}
    {is : List Interpretation} {eqm : FunctionEquality} {fuel : Int} {env : Env} :
    ∀ n e, closedLit cs ss n e = true →
      ∃ v, eval O (.Program fns cs ss is eqm) fuel env e = .Ok v
  | 0, _, h => by simp [closedLit] at h
  | n + 1, e, h => by
    cases e
    case IntegerLiteral => exact ⟨_, by rw [eval]⟩
    case BooleanLiteral => exact ⟨_, by rw [eval]⟩
    case ADT c tps es =>
      simp only [closedLit, Bool.and_eq_true, List.all_eq_true] at h
      obtain ⟨hc, hes⟩ := h
      split at hc
      · next d s fs hl =>
        obtain ⟨t0, eq0, hs⟩ := noInvOf_eq hc
        obtain ⟨vs, hvs⟩ := eval_list_all (O := O) (P := .Program fns cs ss is eqm) (fuel := fuel)
          (env := env) es fun a ha => closedLit_eval n a (hes a ha)
        refine ⟨.ADTV c (O.resolve_all (env_types env) tps) vs, ?_⟩
        rw [eval, hvs]
        simp only [construct, hl, hs]
      · cases hc
    all_goals simp [closedLit] at h

theorem selectRev_refines {fns : List FunDef} {cs : List Constructor} {ss : List ADTSort}
    {is : List Interpretation} {eqm : FunctionEquality} {Fs : List Fact} {t t' : Expr}
    (hP : P = .Program fns cs ss is eqm) (h : selectRev cs ss t t' = true) :
    Refines O P Fs t' t := by
  subst hP
  intro fuel env v _ hv
  unfold selectRev at h
  split at h
  · next c tps args sel =>
    split at h
    · next d s fields hl =>
      simp only [Bool.and_eq_true, Option.any_eq_true, List.all_eq_true, Bool.or_eq_true] at h
      obtain ⟨⟨hinv, a, hp, he⟩, hall⟩ := h
      rw [exprEq_eq _ _ _ he] at hp
      obtain ⟨vs, hvs⟩ := eval_list_all (O := O) (P := .Program fns cs ss is eqm) (fuel := fuel)
        (env := env) args fun b hb => by
          rcases hall b hb with hb' | hb'
          · rw [exprEq_eq _ _ _ hb']; exact ⟨v, hv⟩
          · exact closedLit_eval 100 b hb'
      obtain ⟨t0, eq0, hs⟩ := noInvOf_eq hinv
      have hsel := pick_eq fields args vs sel hvs hp
      rw [hv] at hsel
      rw [eval, eval, hvs]
      simp only [construct, hl, hs, ← hsel]
    · cases h
  · cases h

theorem revCheck_refines {fns : List FunDef} {cs : List Constructor} {ss : List ADTSort}
    {is : List Interpretation} {eqm : FunctionEquality} (hP : P = .Program fns cs ss is eqm)
    {rule : String} {Fs : List Fact} {t t' : Expr} (h : revCheck cs ss rule Fs t t' = true) :
    Refines O P Fs t' t := by
  unfold revCheck at h
  split at h
  · simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [exprEq_eq _ _ _ h]; exact refines_refl
    · exact logicCheck_refines h
  · exact selectRev_refines hP h
  · cases h

end

/-- `e` after the steps `ss`, if each of them holds, in a program whose constructors are
`cs`, where the facts `Fs` hold. -/
def stepsApply (cs : List Constructor) (ss : List ADTSort) (Fs : List Fact) :
    List Step → Expr → Option Expr
  | [], e => some e
  | s :: steps, e =>
    (rewriteAt (fun Fs t => if ruleCheck cs ss s.rule Fs t s.result then some s.result else none)
      (fun Fs t t' => revCheck cs ss s.rule Fs t t') Fs s.pos e).bind (stepsApply cs ss Fs steps)

/-- The steps that hold refine the expression that they start from. -/
theorem stepsApply_refines {O : Oracle} {P : Program} {cs : List Constructor}
    {ss : List ADTSort} (hO : O.Sound) (hP : ∃ fs is eqm, P = .Program fs cs ss is eqm)
    (Fs : List Fact) :
    ∀ (steps : List Step) (e e' : Expr), stepsApply cs ss Fs steps e = some e' →
      Refines O P Fs e e'
  | [], e, e', h => by simp [stepsApply] at h; subst h; exact refines_refl
  | s :: steps, e, e', h => by
    simp only [stepsApply, Option.bind_eq_some_iff] at h
    obtain ⟨e1, h1, h2⟩ := h
    refine refines_trans (rewriteAt_refines hO ?_ ?_ Fs s.pos e e1 h1)
      (stepsApply_refines hO hP Fs steps e1 e' h2)
    · intro Fs t t' ht
      split at ht
      · next hc => cases ht; exact ruleCheck_refines hO hP hc
      · cases ht
    · intro Fs t t' ht hq
      obtain ⟨fns, is, eqm, hP'⟩ := hP
      split at ht
      · cases ht; exact revCheck_refines hP' hq
      · cases ht

end Inox.Simplified
