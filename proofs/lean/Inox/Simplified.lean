/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Lowered

/-!
# The steps of the simplifications

Before it lowers an expression, Inox simplifies it, and the certificate records each step of the
simplification: its rule, the position of the subterm that it rewrites, and what the subterm
becomes. A step may only refine its subterm: wherever the subterm has a value, what it becomes
has the same value (`Refines`), under the facts that hold where evaluation reaches the position.

Rewriting a subterm into one that refines it refines the whole expression (`replaceAt_refines`),
so that a sequence of steps of which each refines its subterm refines the expression that it
starts from (`stepsCheck_refines`).

The rules that are checked here:
- `logic`, three-valued propositional reasoning over the atoms of the subterm, under the facts
  of the path to it (`logicCheck`): the atoms are the operands of the connectives that are not
  connectives themselves, `(< a b)` is the negation of `(>= a b)` and `(<= a b)` that of
  `(> a b)`, and every value of the atoms (`true`, `false` or no value) where the facts hold,
  and where the subterm has a value, gives what it becomes the same value.
-/

namespace Inox.Simplified

open Inox.Semantics
open Inox.Lowered (exprEq exprEq_eq)

section
variable (O : Oracle) (P : Program)

/-- `t'` refines `t` under the facts `Fs`: in every environment where the facts are `true`,
wherever `t` has a value, `t'` has the same value with the same fuel. -/
def Refines (Fs : List Expr) (t t' : Expr) : Prop :=
  ∀ (fuel : Int) (env : Env) (v : Value), (∀ f ∈ Fs, eval O P fuel env f = .Ok (.BoolV true)) →
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

theorem logicCheck_refines {Fs : List Expr} {t t' : Expr} (h : logicCheck Fs t t' = true) :
    Refines O P Fs t t' := by
  intro fuel env v hFs hv
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

/-! ## Rewriting at a position -/

/-- `e` where the subterm at the position `p` is what `r` makes of it, under the facts `Fs` that
hold in the environment of `e`, with those of the path to the position. The positions are those
of the S-expressions that the certificate writes: the operands of an application are at `1` and
after, and the value of `(let ((x v)) b)` is at `1 0 1`. -/
def rewriteAt (r : List Expr → Expr → Option Expr) : List Expr → List Nat → Expr → Option Expr
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
    | 2, .Implies a b => (rewriteAt r (Fs ++ [a]) p b).map (.Implies a ·)
    | 1, .IfExpr c a b => (rewriteAt r Fs p c).map (.IfExpr · a b)
    | 2, .IfExpr c a b => (rewriteAt r (Fs ++ [c]) p a).map (.IfExpr c · b)
    | 3, .IfExpr c a b => (rewriteAt r (Fs ++ [.Not c]) p b).map (.IfExpr c a ·)
    | 1, .Assume q a => (rewriteAt r Fs p q).map (.Assume · a)
    | 2, .Assume q a => (rewriteAt r (Fs ++ [q]) p a).map (.Assume q ·)
    | 2, .Let x v b => (rewriteAt r [] p b).map (.Let x v ·)
    | i + 1, .And es =>
      match es.drop i with
      | t :: post =>
        (rewriteAt r (Fs ++ es.take i) p t).map fun t' => .And (es.take i ++ t' :: post)
      | [] => none
    | i + 1, .Or es =>
      match es.drop i with
      | t :: post =>
        (rewriteAt r (Fs ++ (es.take i).map .Not) p t).map fun t' => .Or (es.take i ++ t' :: post)
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

theorem bool_refines {Fs : List Expr} {a a' : Expr} (h : Refines O P Fs a a') {fuel : Int}
    {env : Env} (hF : ∀ f ∈ Fs, eval O P fuel env f = .Ok (.BoolV true)) {b : Bool}
    (ha : eval_bool O P fuel env a = .Ok b) : eval_bool O P fuel env a' = .Ok b :=
  eval_bool_ok.mpr (h fuel env _ hF (eval_bool_ok.mp ha))

theorem facts_append {fuel : Int} {env : Env} {Fs Gs : List Expr}
    (h1 : ∀ f ∈ Fs, eval O P fuel env f = .Ok (.BoolV true))
    (h2 : ∀ f ∈ Gs, eval O P fuel env f = .Ok (.BoolV true)) :
    ∀ f ∈ Fs ++ Gs, eval O P fuel env f = .Ok (.BoolV true) := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · exact h1 f hf
  · exact h2 f hf

theorem refines_Plus_1 {Fs : List Expr} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.Plus a b) (.Plus a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Plus_2 {Fs : List Expr} {a b b' : Expr} (h : Refines O P Fs b b') :
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

theorem refines_Minus_1 {Fs : List Expr} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.Minus a b) (.Minus a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Minus_2 {Fs : List Expr} {a b b' : Expr} (h : Refines O P Fs b b') :
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

theorem refines_Times_1 {Fs : List Expr} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.Times a b) (.Times a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Times_2 {Fs : List Expr} {a b b' : Expr} (h : Refines O P Fs b b') :
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

theorem refines_Division_1 {Fs : List Expr} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.Division a b) (.Division a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Division_2 {Fs : List Expr} {a b b' : Expr} (h : Refines O P Fs b b') :
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

theorem refines_Remainder_1 {Fs : List Expr} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.Remainder a b) (.Remainder a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Remainder_2 {Fs : List Expr} {a b b' : Expr} (h : Refines O P Fs b b') :
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

theorem refines_Modulo_1 {Fs : List Expr} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.Modulo a b) (.Modulo a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Modulo_2 {Fs : List Expr} {a b b' : Expr} (h : Refines O P Fs b b') :
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

theorem refines_LessThan_1 {Fs : List Expr} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.LessThan a b) (.LessThan a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_LessThan_2 {Fs : List Expr} {a b b' : Expr} (h : Refines O P Fs b b') :
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

theorem refines_GreaterThan_1 {Fs : List Expr} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.GreaterThan a b) (.GreaterThan a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_GreaterThan_2 {Fs : List Expr} {a b b' : Expr} (h : Refines O P Fs b b') :
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

theorem refines_LessEquals_1 {Fs : List Expr} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.LessEquals a b) (.LessEquals a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_LessEquals_2 {Fs : List Expr} {a b b' : Expr} (h : Refines O P Fs b b') :
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

theorem refines_GreaterEquals_1 {Fs : List Expr} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.GreaterEquals a b) (.GreaterEquals a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_GreaterEquals_2 {Fs : List Expr} {a b b' : Expr} (h : Refines O P Fs b b') :
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

theorem refines_Equals_1 {Fs : List Expr} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.Equals a b) (.Equals a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Equals_2 {Fs : List Expr} {a b b' : Expr} (h : Refines O P Fs b b') :
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

theorem refines_UMinus {Fs : List Expr} {a a' : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.UMinus a) (.UMinus a') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_IsConstructor {Fs : List Expr} {a a' : Expr} {c : Id} (h : Refines O P Fs a a') :
    Refines O P Fs (.IsConstructor a c) (.IsConstructor a' c) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_ADTSelector {Fs : List Expr} {a a' : Expr} {f : Id} (h : Refines O P Fs a a') :
    Refines O P Fs (.ADTSelector a f) (.ADTSelector a' f) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [h fuel env va hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Not {Fs : List Expr} {a a' : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.Not a) (.Not a') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [bool_refines h hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Implies_1 {Fs : List Expr} {a a' b : Expr} (h : Refines O P Fs a a') :
    Refines O P Fs (.Implies a b) (.Implies a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [bool_refines h hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_IfExpr_1 {Fs : List Expr} {c c' a b : Expr} (h : Refines O P Fs c c') :
    Refines O P Fs (.IfExpr c a b) (.IfExpr c' a b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [bool_refines h hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Assume_1 {Fs : List Expr} {q q' a : Expr} (h : Refines O P Fs q q') :
    Refines O P Fs (.Assume q a) (.Assume q' a) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next va ha => rw [bool_refines h hF ha]; exact hv
  · cases hv
  · cases hv

theorem refines_Implies_2 {Fs : List Expr} {a b b' : Expr} (h : Refines O P (Fs ++ [a]) b b') :
    Refines O P Fs (.Implies a b) (.Implies a b') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next x ha =>
    split at hv
    · next hx =>
      subst hx
      have hF' := facts_append (Gs := [a]) hF (by simpa using eval_bool_ok.mp ha)
      simp only [dite_true] at hv ⊢
      split at hv
      · next y hb => rw [bool_refines h hF' hb]; exact hv
      · cases hv
      · cases hv
    · next hx => simp only [hx] at hv ⊢; exact hv
  · cases hv
  · cases hv

theorem refines_IfExpr_2 {Fs : List Expr} {c a a' b : Expr} (h : Refines O P (Fs ++ [c]) a a') :
    Refines O P Fs (.IfExpr c a b) (.IfExpr c a' b) := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next x hc =>
    split at hv
    · next hx =>
      subst hx
      simp only [dite_true] at hv ⊢
      exact h fuel env v (facts_append hF (by simpa using eval_bool_ok.mp hc)) hv
    · next hx => simp only [hx] at hv ⊢; exact hv
  · cases hv
  · cases hv

theorem refines_IfExpr_3 {Fs : List Expr} {c a b b' : Expr}
    (h : Refines O P (Fs ++ [.Not c]) b b') :
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
      simp [eval, hc]
  · cases hv
  · cases hv

theorem refines_Assume_2 {Fs : List Expr} {q a a' : Expr} (h : Refines O P (Fs ++ [q]) a a') :
    Refines O P Fs (.Assume q a) (.Assume q a') := by
  intro fuel env v hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next x hq =>
    split at hv
    · next hx =>
      subst hx
      simp only [dite_true] at hv ⊢
      exact h fuel env v (facts_append hF (by simpa using eval_bool_ok.mp hq)) hv
    · cases hv
  · cases hv
  · cases hv

theorem refines_Let_2 {Fs : List Expr} {x : Id} {v b b' : Expr} (h : Refines O P [] b b') :
    Refines O P Fs (.Let x v b) (.Let x v b') := by
  intro fuel env w hF hv
  simp only [eval] at hv ⊢
  split at hv
  · next vv hvv => exact h fuel _ w (by simp) hv
  · cases hv
  · cases hv

theorem refines_And {t t' : Expr} {post : List Expr} :
    ∀ (pre Fs : List Expr), Refines O P (Fs ++ pre) t t' →
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
        have ih := refines_And (post := post) pre (Fs ++ [q]) (by simpa using h)
        have := ih fuel env v (facts_append hF (by simpa using eval_bool_ok.mp hq))
          (by simpa only [eval] using hv)
        simpa only [eval] using this
      · next hx => simp only [hx] at hv ⊢; exact hv
    · cases hv
    · cases hv

theorem refines_Or {t t' : Expr} {post : List Expr} :
    ∀ (pre Fs : List Expr), Refines O P (Fs ++ pre.map .Not) t t' →
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
        have ih := refines_Or (post := post) pre (Fs ++ [.Not q]) (by simpa using h)
        have hn : ∀ f ∈ [Expr.Not q], eval O P fuel env f = .Ok (.BoolV true) := by
          intro f hf
          simp only [List.mem_singleton] at hf
          subst hf
          simp [eval, hq]
        have := ih fuel env v (facts_append hF hn) (by simpa only [eval] using hv)
        simpa only [eval] using this
    · cases hv
    · cases hv

end

section
variable {O : Oracle} {P : Program}

/-- Rewriting the subterm at a position into one that refines it refines the expression. -/
theorem rewriteAt_refines {r : List Expr → Expr → Option Expr}
    (hr : ∀ Fs t t', r Fs t = some t' → Refines O P Fs t t') :
    ∀ (Fs : List Expr) (p : List Nat) (e e' : Expr), rewriteAt r Fs p e = some e' →
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
    · cases h

theorem refines_trans {Fs : List Expr} {a b c : Expr} (h1 : Refines O P Fs a b)
    (h2 : Refines O P Fs b c) : Refines O P Fs a c :=
  fun fuel env v hF hv => h2 fuel env v hF (h1 fuel env v hF hv)

theorem refines_refl {Fs : List Expr} {a : Expr} : Refines O P Fs a a :=
  fun _ _ _ _ hv => hv

end

/-! ## The steps -/

/-- A step of a simplification: its rule, the position of the subterm that it rewrites, and what
the subterm becomes. -/
structure Step where
  rule : String
  pos : List Nat
  result : Expr

/-- Whether the step of the rule `rule` that rewrites `t` into `t'` under the facts `Fs` holds,
for the rules that are checked. -/
def ruleCheck : String → List Expr → Expr → Expr → Bool
  | "logic", Fs, t, t' => logicCheck Fs t t'
  | _, _, _, _ => false

theorem ruleCheck_refines {O : Oracle} {P : Program} {rule : String} {Fs : List Expr}
    {t t' : Expr} (h : ruleCheck rule Fs t t' = true) : Refines O P Fs t t' := by
  unfold ruleCheck at h
  split at h
  · exact logicCheck_refines h
  · cases h

/-- `e` after the steps `ss`, if each of them holds. -/
def stepsApply : List Step → Expr → Option Expr
  | [], e => some e
  | s :: ss, e =>
    (rewriteAt (fun Fs t => if ruleCheck s.rule Fs t s.result then some s.result else none) []
      s.pos e).bind (stepsApply ss)

/-- The steps that hold refine the expression that they start from. -/
theorem stepsApply_refines {O : Oracle} {P : Program} :
    ∀ (ss : List Step) (e e' : Expr), stepsApply ss e = some e' → Refines O P [] e e'
  | [], e, e', h => by simp [stepsApply] at h; subst h; exact refines_refl
  | s :: ss, e, e', h => by
    simp only [stepsApply, Option.bind_eq_some_iff] at h
    obtain ⟨e1, h1, h2⟩ := h
    refine refines_trans (rewriteAt_refines ?_ [] s.pos e e1 h1) (stepsApply_refines ss e1 e' h2)
    intro Fs t t' ht
    split at ht
    · next hc => cases ht; exact ruleCheck_refines hc
    · cases ht

end Inox.Simplified
