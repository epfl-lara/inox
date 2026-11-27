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

The rules that are checked here:
- `logic`, three-valued propositional reasoning over the atoms of the subterm, under the facts
  of the path to it (`logicCheck`): the atoms are the operands of the connectives that are not
  connectives themselves, `(< a b)` is the negation of `(>= a b)` and `(<= a b)` that of
  `(> a b)`, and every value of the atoms (`true`, `false` or no value) where the facts hold,
  and where the subterm has a value, gives what it becomes the same value. The variables of the
  lets around the subterm are first their values (`unlet`, by `subst_eval`).
- `select`, the selection of a field of a construction is the argument of the field.
- `bind`, a let of a subterm that the term always evaluates, to a variable that it doesn't
  mention.
- `expand`, a variable is the value of its let.
- `arith`, a product with a factor `0` is `0`, a sum with an operand `0`, a difference with a
  right operand `0` and a product with a factor `1` are the other operand, and an equality of an
  expression with itself is `true` where its value is of a primitive type, which the equality of
  the semantics compares by identity (`value_eq_refl`): a literal, an arithmetic operation, an
  equality, or a free variable of the input (a fact `prim`).
- `evaluate`, a ground term of literals, arithmetic and concatenations of strings is its value.
-/

namespace Inox.Simplified

open Inox.Semantics
open Inox.Lowered (exprEq exprEq_eq)

/-- A fact that holds where evaluation reaches a position: an expression is `true`, the
variable `x` has the value of the expression `v`, that of its let, or the variable `x` has a
value of a primitive type, as a free variable of the input does. -/
inductive Fact where
  | holds (e : Expr)
  | binds (x : Id) (v : Expr)
  | prim (x : Id)

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

/-- Where `w` has the value `vw`, an expression where the variable `x` is `vw` has the value of
the expression where `x` is `w`. -/
theorem subst_eval {x : Id} {w : Expr} {fuel : Int} {env : Env} {vw : Value}
    (hw : eval O P fuel env w = .Ok vw) :
    ∀ n e e', subst x w n e = some e' → eval O P fuel (env_bind env x vw) e = eval O P fuel env e'
  | 0, _, _, h => by simp [subst] at h
  | n + 1, e, e', h => by
    have ih := subst_eval (x := x) hw n
    unfold subst at h
    split at h
    · next y =>
      cases h
      by_cases hy : y = x
      · subst hy
        cases env
        simp [eval, env_bind, env_vars, lookup_var, hw]
      · cases env
        simp [eval, env_bind, env_vars, lookup_var, hy]
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
      simp only [eval, (subst_list ih _ _ hes).1, env_types_bind]
    · obtain ⟨es', hes, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [eval, (subst_list ih _ _ hes).1, construct_bind]
    · cases h

end

/-! ## Rewriting at a position -/

/-- The facts in the body of `(let ((x v)) b)`: that `x` has the value of `v`, where `v` doesn't
mention `x`. The facts around the let may mention `x`, which it rebinds, and are not kept. -/
def letFacts (x : Id) (v : Expr) : List Fact :=
  if (subst x v 1000 v).any (exprEq 1000 · v) then [.binds x v] else []

/-- `e` where the subterm at the position `p` is what `r` makes of it, under the facts `Fs` that
hold in the environment of `e`, with those of the path to the position. The positions are those
of the S-expressions that the certificate writes: the operands of an application are at `1` and
after, and the value of `(let ((x v)) b)` is at `1 0 1`. -/
def rewriteAt (r : List Fact → Expr → Option Expr) : List Fact → List Nat → Expr → Option Expr
  | Fs, [], e => r Fs e
  | Fs, i :: p, e =>
    match i, e with
    | 1, .Not a => (rewriteAt r Fs p a).map .Not
    | 1, .Plus a b => (rewriteAt r Fs p a).map (.Plus · b)
    | 2, .Plus a b => (rewriteAt r Fs p b).map (.Plus a ·)
    | 1, .Minus a b => (rewriteAt r Fs p a).map (.Minus · b)
    | 2, .Minus a b => (rewriteAt r Fs p b).map (.Minus a ·)
    | 1, .Times a b => (rewriteAt r Fs p a).map (.Times · b)
    | 2, .Times a b => (rewriteAt r Fs p b).map (.Times a ·)
    | 1, .Division a b => (rewriteAt r Fs p a).map (.Division · b)
    | 2, .Division a b => (rewriteAt r Fs p b).map (.Division a ·)
    | 1, .Remainder a b => (rewriteAt r Fs p a).map (.Remainder · b)
    | 2, .Remainder a b => (rewriteAt r Fs p b).map (.Remainder a ·)
    | 1, .Modulo a b => (rewriteAt r Fs p a).map (.Modulo · b)
    | 2, .Modulo a b => (rewriteAt r Fs p b).map (.Modulo a ·)
    | 1, .LessThan a b => (rewriteAt r Fs p a).map (.LessThan · b)
    | 2, .LessThan a b => (rewriteAt r Fs p b).map (.LessThan a ·)
    | 1, .GreaterThan a b => (rewriteAt r Fs p a).map (.GreaterThan · b)
    | 2, .GreaterThan a b => (rewriteAt r Fs p b).map (.GreaterThan a ·)
    | 1, .LessEquals a b => (rewriteAt r Fs p a).map (.LessEquals · b)
    | 2, .LessEquals a b => (rewriteAt r Fs p b).map (.LessEquals a ·)
    | 1, .GreaterEquals a b => (rewriteAt r Fs p a).map (.GreaterEquals · b)
    | 2, .GreaterEquals a b => (rewriteAt r Fs p b).map (.GreaterEquals a ·)
    | 1, .Equals a b => (rewriteAt r Fs p a).map (.Equals · b)
    | 2, .Equals a b => (rewriteAt r Fs p b).map (.Equals a ·)
    | 1, .UMinus a => (rewriteAt r Fs p a).map .UMinus
    | 1, .IsConstructor a c => (rewriteAt r Fs p a).map (.IsConstructor · c)
    | 1, .ADTSelector a f => (rewriteAt r Fs p a).map (.ADTSelector · f)
    | 1, .Implies a b => (rewriteAt r Fs p a).map (.Implies · b)
    | 2, .Implies a b => (rewriteAt r (Fs ++ [.holds a]) p b).map (.Implies a ·)
    | 1, .IfExpr c a b => (rewriteAt r Fs p c).map (.IfExpr · a b)
    | 2, .IfExpr c a b => (rewriteAt r (Fs ++ [.holds c]) p a).map (.IfExpr c · b)
    | 3, .IfExpr c a b => (rewriteAt r (Fs ++ [.holds (.Not c)]) p b).map (.IfExpr c a ·)
    | 1, .Assume q a => (rewriteAt r Fs p q).map (.Assume · a)
    | 2, .Assume q a => (rewriteAt r (Fs ++ [.holds q]) p a).map (.Assume q ·)
    | 2, .Let x v b => (rewriteAt r (letFacts x v) p b).map (.Let x v ·)
    | 1, .Let x v b =>
      match p with
      | 0 :: 1 :: p' => (rewriteAt r Fs p' v).map (.Let x · b)
      | _ => none
    | i + 1, .And es =>
      match es.drop i with
      | t :: post =>
        (rewriteAt r (Fs ++ (es.take i).map .holds) p t).map fun t' =>
          .And (es.take i ++ t' :: post)
      | [] => none
    | i + 1, .Or es =>
      match es.drop i with
      | t :: post =>
        (rewriteAt r (Fs ++ (es.take i).map fun e => .holds (.Not e)) p t).map fun t' =>
          .Or (es.take i ++ t' :: post)
      | [] => none
    | i + 1, .FunctionInvocation f tps es =>
      match es.drop i with
      | t :: post =>
        (rewriteAt r Fs p t).map fun t' => .FunctionInvocation f tps (es.take i ++ t' :: post)
      | [] => none
    | i + 1, .ADT c tps es =>
      match es.drop i with
      | t :: post => (rewriteAt r Fs p t).map fun t' => .ADT c tps (es.take i ++ t' :: post)
      | [] => none
    | _, _ => none

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

/-- Rewriting the subterm at a position into one that refines it refines the expression. -/
theorem rewriteAt_refines {r : List Fact → Expr → Option Expr}
    (hr : ∀ Fs t t', r Fs t = some t' → Refines O P Fs t t') :
    ∀ (Fs : List Fact) (p : List Nat) (e e' : Expr), rewriteAt r Fs p e = some e' →
      Refines O P Fs e e'
  | Fs, [], e, e', h => hr Fs e e' (by simpa [rewriteAt] using h)
  | Fs, i :: p, e, e', h => by
    unfold rewriteAt at h
    split at h
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Not (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Plus_1 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Plus_2 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Minus_1 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Minus_2 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Times_1 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Times_2 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Division_1 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Division_2 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Remainder_1 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Remainder_2 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Modulo_1 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Modulo_2 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_LessThan_1 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_LessThan_2 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_GreaterThan_1 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_GreaterThan_2 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_LessEquals_1 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_LessEquals_2 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_GreaterEquals_1 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_GreaterEquals_2 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Equals_1 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Equals_2 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_UMinus (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_IsConstructor (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_ADTSelector (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Implies_1 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Implies_2 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_IfExpr_1 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_IfExpr_2 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_IfExpr_3 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Assume_1 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Assume_2 (rewriteAt_refines hr _ _ _ _ ht)
    · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact refines_Let_2 (rewriteAt_refines hr _ _ _ _ ht)
    · next x v b =>
      split at h
      · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
        exact refines_Let_1 (rewriteAt_refines hr _ _ _ _ ht)
      · cases h
    · next j es =>
      split at h
      · next t post hd =>
        obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
        have hes : es = es.take j ++ t :: post := by rw [← hd, List.take_append_drop]
        have := refines_And (post := post) (es.take j) Fs (rewriteAt_refines hr _ _ _ _ ht)
        rwa [← hes] at this
      · cases h
    · next j es =>
      split at h
      · next t post hd =>
        obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
        have hes : es = es.take j ++ t :: post := by rw [← hd, List.take_append_drop]
        have := refines_Or (post := post) (es.take j) Fs (rewriteAt_refines hr _ _ _ _ ht)
        rwa [← hes] at this
      · cases h
    · next j f tps es =>
      split at h
      · next t post hd =>
        obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
        have hes : es = es.take j ++ t :: post := by rw [← hd, List.take_append_drop]
        have := refines_call (f := f) (tps := tps) (pre := es.take j) (post := post)
          (rewriteAt_refines hr _ _ _ _ ht)
        rwa [← hes] at this
      · cases h
    · next j c tps es =>
      split at h
      · next t post hd =>
        obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
        have hes : es = es.take j ++ t :: post := by rw [← hd, List.take_append_drop]
        have := refines_adt (c := c) (tps := tps) (pre := es.take j) (post := post)
          (rewriteAt_refines hr _ _ _ _ ht)
        rwa [← hes] at this
      · cases h
    · cases h

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

/-- The argument of the field `sel` among the arguments `args` of a construction whose fields
are `fields`. -/
def pick : List Param → List Expr → Id → Option Expr
  | .Param f _ :: fs, a :: as, sel => if f = sel then some a else pick fs as sel
  | _, _, _ => none

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
  | .UnitLiteral | .Equals _ _ | .Plus _ _ | .Minus _ _ | .Times _ _ => true
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

/-- The value of a ground term of literals, arithmetic and concatenations of strings, which it
has in every environment, `n` deep. -/
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

theorem geval_eval {fuel : Int} {env : Env} :
    ∀ n e {v : Value}, geval n e = some v → eval O P fuel env e = .Ok v
  | 0, _, _, h => by simp [geval] at h
  | n + 1, e, v, h => by
    have ih := @geval_eval fuel env n
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
    · cases h

theorem evaluateCheck_refines {Fs : List Fact} {t t' : Expr} (h : evaluateCheck t t' = true) :
    Refines O P Fs t t' := by
  intro fuel env v _ hv
  unfold evaluateCheck at h
  split at h
  · next v0 w h1 h2 =>
    rw [geval_eval _ _ h1] at hv
    cases hv
    rw [geval_eval _ _ h2, litEq_eq h]
  · cases h

end


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
def ruleCheck (cs : List Constructor) : String → List Fact → Expr → Expr → Bool
  | "logic", Fs, t, t' =>
    exprEq 1000 (unlet 100 t) t' || logicCheck (Fs.filterMap Fact.expr?) (unlet 100 t) t'
  | "select", _, t, t' => selectCheck cs t t'
  | "bind", _, t, t' => bindCheck t t'
  | "expand", Fs, t, t' => expandCheck Fs t t'
  | "arith", Fs, t, t' => arithCheck Fs t t'
  | "evaluate", _, t, t' => evaluateCheck t t'
  | _, _, _, _ => false

theorem ruleCheck_refines {O : Oracle} {P : Program} {cs : List Constructor} (hO : O.Sound)
    (hP : ∃ fs ss is eqm, P = .Program fs cs ss is eqm) {rule : String} {Fs : List Fact}
    {t t' : Expr} (h : ruleCheck cs rule Fs t t' = true) : Refines O P Fs t t' := by
  unfold ruleCheck at h
  split at h
  · refine refines_trans (unlet_refines 100 t) ?_
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [exprEq_eq _ _ _ h]; exact refines_refl
    · exact logicCheck_refines h
  · exact selectCheck_refines hP h
  · exact bindCheck_refines h
  · exact expandCheck_refines h
  · exact arithCheck_refines hO h
  · exact evaluateCheck_refines h
  · cases h

/-- `e` after the steps `ss`, if each of them holds, in a program whose constructors are
`cs`, where the facts `Fs` hold. -/
def stepsApply (cs : List Constructor) (Fs : List Fact) : List Step → Expr → Option Expr
  | [], e => some e
  | s :: ss, e =>
    (rewriteAt (fun Fs t => if ruleCheck cs s.rule Fs t s.result then some s.result else none) Fs
      s.pos e).bind (stepsApply cs Fs ss)

/-- The steps that hold refine the expression that they start from. -/
theorem stepsApply_refines {O : Oracle} {P : Program} {cs : List Constructor} (hO : O.Sound)
    (hP : ∃ fs ss is eqm, P = .Program fs cs ss is eqm) (Fs : List Fact) :
    ∀ (ss : List Step) (e e' : Expr), stepsApply cs Fs ss e = some e' → Refines O P Fs e e'
  | [], e, e', h => by simp [stepsApply] at h; subst h; exact refines_refl
  | s :: ss, e, e', h => by
    simp only [stepsApply, Option.bind_eq_some_iff] at h
    obtain ⟨e1, h1, h2⟩ := h
    refine refines_trans (rewriteAt_refines ?_ Fs s.pos e e1 h1)
      (stepsApply_refines hO hP Fs ss e1 e' h2)
    intro Fs t t' ht
    split at ht
    · next hc => cases ht; exact ruleCheck_refines hO hP hc
    · cases ht

end Inox.Simplified
