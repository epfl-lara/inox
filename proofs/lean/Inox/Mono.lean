/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Semantics

/-!
# Fuel monotonicity of the generated evaluator, on a first-order fragment

`eval O P fuel env e` and `call O P fuel f tps tenv vs` (`proofs/semantics/Inox/Semantics.lean`,
generated from `semantics.md`) answer `OutOfFuel` when the fuel runs out. This module proves that
more fuel never changes another result (`eval_mono`, `call_mono'`), for the expressions of `Frag`
in a program whose function bodies are in `Frag` (`ProgFrag`). So a call has at most one value,
whatever fuel finds it (`call_ok_unique`), which is what makes the interpretation of a function
by its calls well defined (`Inox/Bridge.lean`).

`Frag` leaves out `Application`, which calls the body of a closure through `apply`, `Forall` and
`UninterpretedCall`, which go through the oracle, and the operations on strings, bit-vectors and
floating-point numbers.
-/

namespace Inox.Bridge
open Inox.Semantics

/-- `r'` is `r`, unless `r` is `OutOfFuel`: what a result becomes with more fuel. -/
def Le {α : Type} (r r' : Result α) : Prop := r = .OutOfFuel ∨ r' = r

theorem Le.ok {α : Type} {r r' : Result α} {v : α} (h : Le r r') (e : r = .Ok v) :
    r' = .Ok v := by
  rcases h with h | h <;> subst e <;> first | exact h | cases h

theorem Le.stuck {α : Type} {r r' : Result α} (h : Le r r') (e : r = .Stuck) : r' = .Stuck := by
  rcases h with h | h <;> subst e <;> first | exact h | cases h

theorem Le.refl {α : Type} (r : Result α) : Le r r := Or.inr rfl

macro "le_step " h:term : tactic => `(tactic| (split <;> rename_i heq <;> first
  | exact Or.inl rfl
  | (rw [Le.ok $h heq]; dsimp only)
  | (rw [Le.stuck $h heq]; exact Le.refl _)))


/-- The fragment on which fuel monotonicity is proved. -/
inductive Frag : Expr → Prop where
  | assume {p b} : Frag p → Frag b → Frag (.Assume p b)
  | var {x} : Frag (.Variable x)
  | let_ {x v b} : Frag v → Frag b → Frag (.Let x v b)
  | lambda {ps b} : Frag (.Lambda ps b)
  | error : Frag .Error
  | invoke {f tps args} : (∀ a ∈ args, Frag a) → Frag (.FunctionInvocation f tps args)
  | ite {c t e} : Frag c → Frag t → Frag e → Frag (.IfExpr c t e)
  | char {c} : Frag (.CharLiteral c)
  | bv {s w x} : Frag (.BVLiteral s w x)
  | int {i} : Frag (.IntegerLiteral i)
  | frac {n d} : Frag (.FractionLiteral n d)
  | bool {b} : Frag (.BooleanLiteral b)
  | string {cs} : Frag (.StringLiteral cs)
  | unit : Frag .UnitLiteral
  | adt {c tps args} : (∀ a ∈ args, Frag a) → Frag (.ADT c tps args)
  | isCons {a c} : Frag a → Frag (.IsConstructor a c)
  | select {a s} : Frag a → Frag (.ADTSelector a s)
  | equals {a b} : Frag a → Frag b → Frag (.Equals a b)
  | and {es} : (∀ a ∈ es, Frag a) → Frag (.And es)
  | or {es} : (∀ a ∈ es, Frag a) → Frag (.Or es)
  | implies {a b} : Frag a → Frag b → Frag (.Implies a b)
  | not {a} : Frag a → Frag (.Not a)
  | plus {a b} : Frag a → Frag b → Frag (.Plus a b)
  | minus {a b} : Frag a → Frag b → Frag (.Minus a b)
  | uminus {a} : Frag a → Frag (.UMinus a)
  | times {a b} : Frag a → Frag b → Frag (.Times a b)
  | div {a b} : Frag a → Frag b → Frag (.Division a b)
  | rem {a b} : Frag a → Frag b → Frag (.Remainder a b)
  | mod {a b} : Frag a → Frag b → Frag (.Modulo a b)
  | lt {a b} : Frag a → Frag b → Frag (.LessThan a b)
  | gt {a b} : Frag a → Frag b → Frag (.GreaterThan a b)
  | le {a b} : Frag a → Frag b → Frag (.LessEquals a b)
  | ge {a b} : Frag a → Frag b → Frag (.GreaterEquals a b)
  | bvnot {a} : Frag a → Frag (.BVNot a)
  | u2s {a} : Frag a → Frag (.BVUnsignedToSigned a)
  | s2u {a} : Frag a → Frag (.BVSignedToUnsigned a)

/-- Every function of the program has a body in the fragment. -/
def ProgFrag : Program → Prop
  | .Program fs _ _ _ _ => ∀ g tps ps body, FunDef.FunDef g tps ps body ∈ fs → Frag body

theorem lookup_fun_mem {fs : List FunDef} {f : Id} {fd : FunDef} (h : lookup_fun fs f = .Ok fd) :
    fd ∈ fs := by
  induction fs with
  | nil => rw [lookup_fun] at h; cases h
  | cons g rest ih =>
    rw [lookup_fun] at h
    split at h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

section
variable {O : Oracle} {P : Program} {n m : Int}

theorem le_bool {env : Env} {e : Expr} (h : Le (eval O P n env e) (eval O P m env e)) :
    Le (eval_bool O P n env e) (eval_bool O P m env e) := by
  rw [eval_bool, eval_bool]
  le_step h
  exact Le.refl _

theorem le_list {env : Env} {es : List Expr}
    (h : ∀ a ∈ es, Le (eval O P n env a) (eval O P m env a)) :
    Le (eval_list O P n env es) (eval_list O P m env es) := by
  induction es with
  | nil => rw [eval_list, eval_list]; exact Le.refl _
  | cons e rest ih =>
    rw [eval_list, eval_list]
    le_step (h e List.mem_cons_self)
    le_step (ih fun a ha => h a (List.mem_cons_of_mem _ ha))
    exact Le.refl _

theorem le_and {env : Env} {es : List Expr}
    (h : ∀ a ∈ es, Le (eval O P n env a) (eval O P m env a)) :
    Le (eval_and O P n env es) (eval_and O P m env es) := by
  induction es with
  | nil => rw [eval_and, eval_and]; exact Le.refl _
  | cons e rest ih =>
    rw [eval_and, eval_and]
    le_step (le_bool (h e List.mem_cons_self))
    split
    · exact ih fun a ha => h a (List.mem_cons_of_mem _ ha)
    · exact Le.refl _

theorem le_or {env : Env} {es : List Expr}
    (h : ∀ a ∈ es, Le (eval O P n env a) (eval O P m env a)) :
    Le (eval_or O P n env es) (eval_or O P m env es) := by
  induction es with
  | nil => rw [eval_or, eval_or]; exact Le.refl _
  | cons e rest ih =>
    rw [eval_or, eval_or]
    le_step (le_bool (h e List.mem_cons_self))
    split
    · exact Le.refl _
    · exact ih fun a ha => h a (List.mem_cons_of_mem _ ha)

/-- Monotonicity of `eval` on the fragment, given that of `call` at the same fuels. -/
theorem frag_mono
    (hcall : ∀ f tps tenv vs, Le (call O P n f tps tenv vs) (call O P m f tps tenv vs))
    {e : Expr} (he : Frag e) : ∀ env, Le (eval O P n env e) (eval O P m env e) := by
  induction he with
  | assume _ _ ihp ihb =>
    intro env; rw [eval, eval]; le_step (le_bool (ihp env)); split
    · exact ihb env
    · exact Le.refl _
  | let_ _ _ ihv ihb =>
    intro env; rw [eval, eval]; le_step (ihv env); exact ihb _
  | invoke _ ih =>
    intro env; rw [eval, eval]; le_step (le_list fun a ha => ih a ha env); exact hcall _ _ _ _
  | ite _ _ _ ihc iht ihe =>
    intro env; rw [eval, eval]; le_step (le_bool (ihc env)); split
    · exact iht env
    · exact ihe env
  | adt _ ih =>
    intro env; rw [eval, eval]; le_step (le_list fun a ha => ih a ha env)
    rw [construct, construct]
    repeat' (first | exact Le.refl _ | exact Or.inl rfl | le_step (hcall _ _ _ _) | split)
  | isCons _ ih => intro env; rw [eval, eval]; le_step (ih env); exact Le.refl _
  | select _ ih => intro env; rw [eval, eval]; le_step (ih env); exact Le.refl _
  | equals _ _ iha ihb =>
    intro env; rw [eval, eval]; le_step (iha env); le_step (ihb env); exact Le.refl _
  | and _ ih => intro env; rw [eval, eval]; exact le_and fun a ha => ih a ha env
  | or _ ih => intro env; rw [eval, eval]; exact le_or fun a ha => ih a ha env
  | implies _ _ iha ihb =>
    intro env; rw [eval, eval]; le_step (le_bool (iha env)); split
    · le_step (le_bool (ihb env)); exact Le.refl _
    · exact Le.refl _
  | not _ ih => intro env; rw [eval, eval]; le_step (le_bool (ih env)); exact Le.refl _
  | uminus _ ih | bvnot _ ih | u2s _ ih | s2u _ ih =>
    intro env; rw [eval, eval]; le_step (ih env); exact Le.refl _
  | plus _ _ iha ihb | minus _ _ iha ihb | times _ _ iha ihb | div _ _ iha ihb
  | rem _ _ iha ihb | mod _ _ iha ihb | lt _ _ iha ihb | gt _ _ iha ihb | le _ _ iha ihb
  | ge _ _ iha ihb =>
    intro env; rw [eval, eval]; le_step (iha env); le_step (ihb env); exact Le.refl _
  | _ => intro env; rw [eval, eval]; exact Le.refl _

theorem call_zero (h : n ≤ 0) (f tps tenv vs) :
    Le (call O P n f tps tenv vs) (call O P m f tps tenv vs) := by
  rw [call, dite_eq_left_of_eq_true (eq_true h)]; exact Or.inl rfl

theorem call_mono (hP : ProgFrag P) (k : Nat)
    (ih : ∀ n m : Int, n.toNat ≤ k → n ≤ m → ∀ e, Frag e → ∀ env,
      Le (eval O P n env e) (eval O P m env e))
    (hn : n.toNat ≤ k + 1) (hnm : n ≤ m) (f tps tenv vs) :
    Le (call O P n f tps tenv vs) (call O P m f tps tenv vs) := by
  by_cases h0 : n ≤ 0
  · exact call_zero h0 _ _ _ _
  have h1 : ¬m ≤ 0 := by omega
  cases P with
  | Program fs cs ss is eq =>
    rw [call, call, dite_eq_right_of_eq_false (eq_false h0),
      dite_eq_right_of_eq_false (eq_false h1)]
    dsimp only
    split
    · rename_i fd hfd
      obtain ⟨g, tparams, params, body⟩ := fd
      dsimp only
      split
      · exact ih (n - 1) (m - 1) (by omega) (by omega) _ (hP _ _ _ _ (lookup_fun_mem hfd)) _
      · exact Le.refl _
      · exact Le.refl _
    · exact Le.refl _
    · exact Le.refl _

/-- Fuel monotonicity on the fragment: with more fuel, `eval` gives the same result unless it ran
out of fuel. -/
theorem eval_mono_k (hP : ProgFrag P) :
    ∀ k : Nat, ∀ n m : Int, n.toNat ≤ k → n ≤ m → ∀ e, Frag e →
    ∀ env, Le (eval O P n env e) (eval O P m env e)
  | 0 => fun _ _ hn _ _ he => frag_mono (call_zero (by omega)) he
  | k + 1 => fun _ _ hn hnm _ he => frag_mono (call_mono hP k (eval_mono_k hP k) hn hnm) he

theorem eval_mono (hP : ProgFrag P) (hnm : n ≤ m) {e : Expr} (he : Frag e) (env : Env) :
    Le (eval O P n env e) (eval O P m env e) :=
  eval_mono_k hP _ n m (Nat.le_refl _) hnm e he env

theorem call_mono' (hP : ProgFrag P) (hnm : n ≤ m) (f tps tenv vs) :
    Le (call O P n f tps tenv vs) (call O P m f tps tenv vs) :=
  call_mono hP n.toNat (eval_mono_k hP n.toNat) (Nat.le_succ _) hnm f tps tenv vs

theorem eval_ok_mono (hP : ProgFrag P) (hnm : n ≤ m) {e : Expr} (he : Frag e) {env : Env}
    {v : Value}
    (h : eval O P n env e = .Ok v) : eval O P m env e = .Ok v :=
  (eval_mono hP hnm he env).ok h

theorem call_ok_mono (hP : ProgFrag P) (hnm : n ≤ m) {f tps tenv vs} {v : Value}
    (h : call O P n f tps tenv vs = .Ok v) : call O P m f tps tenv vs = .Ok v :=
  (call_mono' hP hnm f tps tenv vs).ok h

/-- A call has at most one value, whatever the fuel. -/
theorem call_ok_unique (hP : ProgFrag P) {f tps tenv vs} {v v' : Value}
    (h : call O P n f tps tenv vs = .Ok v) (h' : call O P m f tps tenv vs = .Ok v') : v = v' := by
  rcases Int.le_total n m with hnm | hnm
  · have := call_ok_mono hP hnm h; rw [h'] at this; cases this; rfl
  · have := call_ok_mono hP hnm h'; rw [h] at this; cases this; rfl

theorem eval_ok_unique (hP : ProgFrag P) {e : Expr} (he : Frag e) {env : Env} {v v' : Value}
    (h : eval O P n env e = .Ok v) (h' : eval O P m env e = .Ok v') : v = v' := by
  rcases Int.le_total n m with hnm | hnm
  · have := eval_ok_mono hP hnm he h; rw [h'] at this; cases this; rfl
  · have := eval_ok_mono hP hnm he h'; rw [h] at this; cases this; rfl

end

end Inox.Bridge
