/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Encoded

/-!
# What the lowering to SMT-LIB makes of an expression

The query of `Inox/Reached.lean` is read back from the terms of Logos (`back`), which aren't
the expressions of the input: their symbols have other names, an error is an assumption that
fails, and a sum of two terms has a trailing `+ 0`, as Logos reads the sums of SMT-LIB. An
expression of the input relates to what it is lowered to (`Lowers`) up to these, and where an
expression of the input evaluates to a value, the expression that it is lowered to evaluates to
the same value with enough fuel (`lowers_eval`), in a program whose functions are what those of
the input are lowered to (`Funs`).

The relation is of first-order expressions over integers and other primitive values, with calls
of functions without type parameters: no datatypes, no lets and no lambdas yet.
-/

namespace Inox.Lowered

open Inox.Semantics
open Inox.Encoded (IsPrim FunIn call_inv call_fun eval_tuple_inv)
open Inox.Bags (eval_bool_ok)

/-- The kinds of values that the relation follows: integers, which a trailing `+ 0` keeps,
primitive values, whose equality is that of the values whatever the program, any value, and
tuples, of the arguments of calls. -/
inductive LK where
  | int
  | prim
  | any
  | tuple (ks : List LK)

/-- The value `v` is of the kind `k`. -/
inductive Has : LK → Value → Prop where
  | int (n : Int) : Has .int (.IntV n)
  | prim {v : Value} (h : IsPrim v = true) : Has .prim v
  | any (v : Value) : Has .any v
  | tupleNil : Has (.tuple []) (.TupleV [])
  | tupleCons {k : LK} {ks : List LK} {v : Value} {vs : List Value} (h : Has k v)
      (hr : Has (.tuple ks) (.TupleV vs)) : Has (.tuple (k :: ks)) (.TupleV (v :: vs))

/-- The kind `k` is in the kind `k'`. -/
def Sub : LK → LK → Bool
  | .int, .int | .int, .prim | .int, .any | .prim, .prim | .prim, .any | .any, .any => true
  | _, _ => false

theorem has_sub {k k' : LK} (hs : Sub k k' = true) {v : Value} (h : Has k v) : Has k' v := by
  cases k <;> cases k' <;> simp [Sub] at hs
  all_goals first
    | exact h
    | exact .any v
    | (cases h; exact .prim rfl)

/-- The functions of the input, each with the function that it is lowered to, the kinds of its
parameters and the kind of its result. -/
abbrev LSig := Id → Option (Id × List LK × LK)

/-- `Lowers S Γ e e' k`: the expression `e` of the input is lowered to `e'`, and its values are
of the kind `k`, where each variable `x` of `Γ` is the variable `y` of `Γ x = some (y, k)`, of
the kind `k`, and each function `f` of `S` is the function of `S f`. -/
inductive Lowers (S : LSig) : (Id → Option (Id × LK)) → Expr → Expr → LK → Prop where
  | var {Γ : Id → Option (Id × LK)} {x y : Id} {k : LK} (h : Γ x = some (y, k)) :
      Lowers S Γ (.Variable x) (.Variable y) k
  | int {Γ : Id → Option (Id × LK)} (n : Int) :
      Lowers S Γ (.IntegerLiteral n) (.IntegerLiteral n) .int
  | bool {Γ : Id → Option (Id × LK)} (b : Bool) :
      Lowers S Γ (.BooleanLiteral b) (.BooleanLiteral b) .prim
  | frac {Γ : Id → Option (Id × LK)} (n d : Int) :
      Lowers S Γ (.FractionLiteral n d) (.FractionLiteral n d) .prim
  /-- An error has no value, whatever it is lowered to. -/
  | error {Γ : Id → Option (Id × LK)} (e' : Expr) (k : LK) : Lowers S Γ .Error e' k
  | weaken {Γ : Id → Option (Id × LK)} {e e' : Expr} {k k' : LK} (h : Lowers S Γ e e' k)
      (hs : Sub k k' = true) : Lowers S Γ e e' k'
  | plusInt {Γ : Id → Option (Id × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .int)
      (hb : Lowers S Γ b b' .int) : Lowers S Γ (.Plus a b) (.Plus a' b') .int
  /-- A sum of two integers, as Logos reads it. -/
  | plusZero {Γ : Id → Option (Id × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .int)
      (hb : Lowers S Γ b b' .int) :
      Lowers S Γ (.Plus a b) (.Plus a' (.Plus b' (.IntegerLiteral 0))) .int
  | plus {Γ : Id → Option (Id × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.Plus a b) (.Plus a' b') .prim
  | minusInt {Γ : Id → Option (Id × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .int)
      (hb : Lowers S Γ b b' .int) : Lowers S Γ (.Minus a b) (.Minus a' b') .int
  | minus {Γ : Id → Option (Id × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.Minus a b) (.Minus a' b') .prim
  | timesInt {Γ : Id → Option (Id × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .int)
      (hb : Lowers S Γ b b' .int) : Lowers S Γ (.Times a b) (.Times a' b') .int
  | times {Γ : Id → Option (Id × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.Times a b) (.Times a' b') .prim
  | uminusInt {Γ : Id → Option (Id × LK)} {a a' : Expr} (ha : Lowers S Γ a a' .int) :
      Lowers S Γ (.UMinus a) (.UMinus a') .int
  | uminus {Γ : Id → Option (Id × LK)} {a a' : Expr} (ha : Lowers S Γ a a' .any) :
      Lowers S Γ (.UMinus a) (.UMinus a') .prim
  | div {Γ : Id → Option (Id × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.Division a b) (.Division a' b') .prim
  | rem {Γ : Id → Option (Id × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.Remainder a b) (.Remainder a' b') .prim
  | mod {Γ : Id → Option (Id × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.Modulo a b) (.Modulo a' b') .prim
  | lt {Γ : Id → Option (Id × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.LessThan a b) (.LessThan a' b') .prim
  | gt {Γ : Id → Option (Id × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.GreaterThan a b) (.GreaterThan a' b') .prim
  | le {Γ : Id → Option (Id × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.LessEquals a b) (.LessEquals a' b') .prim
  | ge {Γ : Id → Option (Id × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.GreaterEquals a b) (.GreaterEquals a' b') .prim
  /-- Primitive values are equal alike in both programs. -/
  | eq {Γ : Id → Option (Id × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .prim)
      (hb : Lowers S Γ b b' .prim) : Lowers S Γ (.Equals a b) (.Equals a' b') .prim
  | not {Γ : Id → Option (Id × LK)} {a a' : Expr} (ha : Lowers S Γ a a' .any) :
      Lowers S Γ (.Not a) (.Not a') .prim
  | implies {Γ : Id → Option (Id × LK)} {a a' b b' : Expr} (ha : Lowers S Γ a a' .any)
      (hb : Lowers S Γ b b' .any) : Lowers S Γ (.Implies a b) (.Implies a' b') .prim
  | andNil {Γ : Id → Option (Id × LK)} : Lowers S Γ (.And []) (.And []) .prim
  | andCons {Γ : Id → Option (Id × LK)} {a a' : Expr} {es es' : List Expr}
      (ha : Lowers S Γ a a' .any) (hr : Lowers S Γ (.And es) (.And es') .prim) :
      Lowers S Γ (.And (a :: es)) (.And (a' :: es')) .prim
  | orNil {Γ : Id → Option (Id × LK)} : Lowers S Γ (.Or []) (.Or []) .prim
  | orCons {Γ : Id → Option (Id × LK)} {a a' : Expr} {es es' : List Expr}
      (ha : Lowers S Γ a a' .any) (hr : Lowers S Γ (.Or es) (.Or es') .prim) :
      Lowers S Γ (.Or (a :: es)) (.Or (a' :: es')) .prim
  | ite {Γ : Id → Option (Id × LK)} {c c' a a' b b' : Expr} {k : LK}
      (hc : Lowers S Γ c c' .any) (ha : Lowers S Γ a a' k) (hb : Lowers S Γ b b' k) :
      Lowers S Γ (.IfExpr c a b) (.IfExpr c' a' b') k
  | assume {Γ : Id → Option (Id × LK)} {p p' a a' : Expr} {k : LK}
      (hp : Lowers S Γ p p' .any) (ha : Lowers S Γ a a' k) :
      Lowers S Γ (.Assume p a) (.Assume p' a') k
  | tupleNil {Γ : Id → Option (Id × LK)} : Lowers S Γ (.Tuple []) (.Tuple []) (.tuple [])
  | tupleCons {Γ : Id → Option (Id × LK)} {e e' : Expr} {es es' : List Expr} {k : LK}
      {ks : List LK} (he : Lowers S Γ e e' k)
      (hr : Lowers S Γ (.Tuple es) (.Tuple es') (.tuple ks)) :
      Lowers S Γ (.Tuple (e :: es)) (.Tuple (e' :: es')) (.tuple (k :: ks))
  /-- A call of a function without type parameters, whatever its type arguments. -/
  | call {Γ : Id → Option (Id × LK)} {f g : Id} {ks : List LK} {k : LK} {tps tps' : List Ty}
      {es es' : List Expr} (hf : S f = some (g, ks, k))
      (ha : Lowers S Γ (.Tuple es) (.Tuple es') (.tuple ks)) :
      Lowers S Γ (.FunctionInvocation f tps es) (.FunctionInvocation g tps' es') k

/-- The variables of the body of a function: its parameters `params`, which are the parameters
`params'` of the function that it is lowered to, of the kinds `ks`. -/
def paramsCtx (params params' : List Id) (ks : List LK) : Id → Option (Id × LK) :=
  fun x => (params.zip (params'.zip ks)).lookup x

/-- The functions of `S` are those of `Ps`, without type parameters, and their bodies are
lowered to those of their functions in `P`, whose parameters are distinct. -/
def Funs (Ps P : Program) (S : LSig) : Prop :=
  ∀ f g ks k, S f = some (g, ks, k) → ∃ params params' body body',
    FunIn f [] params body Ps ∧ FunIn g [] params' body' P ∧ params'.Nodup ∧
      params.length = ks.length ∧ params'.length = ks.length ∧
      Lowers S (paramsCtx params params' ks) body body' k

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

/-- Binding the arguments of a call to the parameters of a function and to those of the
function that it is lowered to gives the variables of its body their values. -/
theorem bind_lowered : ∀ {params params' : List Id} {ks : List LK} {vs : List Value},
    params'.Nodup → params.length = ks.length → params'.length = ks.length →
    Has (.tuple ks) (.TupleV vs) → ∀ {bs : List Binding}, bind_all params vs = .Ok bs →
      ∃ bs', bind_all params' vs = .Ok bs' ∧
        ∀ x y k, paramsCtx params params' ks x = some (y, k) →
          ∃ v, lookup_var bs x = .Ok v ∧ lookup_var bs' y = .Ok v ∧ Has k v
  | [], [], [], [], _, _, _, _, bs, hb => by
    simp [bind_all] at hb
    subst hb
    exact ⟨[], by simp [bind_all], fun x y k hx => by simp [paramsCtx] at hx⟩
  | p :: ps, p' :: ps', k :: ks, v :: vs, hnd, hl1, hl2, h, bs, hb => by
    cases h with
    | tupleCons hv hr =>
      rw [bind_all] at hb
      split at hb
      · next bs1 hbs1 =>
        cases hb
        have hnd' := (List.nodup_cons.mp hnd)
        obtain ⟨bs1', hb1', hl⟩ :=
          bind_lowered hnd'.2 (by simpa using hl1) (by simpa using hl2) hr hbs1
        refine ⟨.Binding p' v :: bs1', by simp [bind_all, hb1'], fun x y k2 hx => ?_⟩
        by_cases hxp : x = p
        · subst hxp
          simp [paramsCtx] at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact ⟨v, by simp [lookup_var], by simp [lookup_var], hv⟩
        · have hb : (x == p) = false := by simpa using hxp
          have hx' : paramsCtx ps ps' ks x = some (y, k2) := by
            simpa only [paramsCtx, List.zip_cons_cons, List.lookup, hb] using hx
          obtain ⟨u, h1, h2, h3⟩ := hl x y k2 hx'
          have hy : y ∈ ps' := (List.of_mem_zip (List.of_mem_zip (mem_of_lookup hx')).2).1
          have hyp : y ≠ p' := fun e => hnd'.1 (e ▸ hy)
          exact ⟨u, by simp [lookup_var, hxp, h1], by simp [lookup_var, hyp, h2], h3⟩
      · cases hb
      · cases hb
  | [], [], [], _ :: _, _, _, _, h, _, _ => by cases h
  | [], _ :: _, _, _, _, hl1, hl2, _, _, _ => by simp at hl1 hl2; omega
  | _ :: _, [], _, _, _, hl1, hl2, _, _, _ => by simp at hl1 hl2; omega
  | [], [], _ :: _, _, _, hl1, _, _, _, _ => by simp at hl1
  | _ :: _, _ :: _, [], _, _, hl1, _, _, _, _ => by simp at hl1
  | _ :: _, _ :: _, _ :: _, [], _, _, _, h, _, _ => by cases h

/-! ## Evaluation -/

section Evaluation
variable {O : Oracle} {Ps P : Program} {S : LSig}

/-- The variables of `Γ` have the same values in `env` and `env'`, of their kinds. -/
def EnvOk (Γ : Id → Option (Id × LK)) (env env' : Env) : Prop :=
  ∀ x y k, Γ x = some (y, k) → ∃ v, lookup_var (env_vars env) x = .Ok v ∧
    lookup_var (env_vars env') y = .Ok v ∧ Has k v

/-- Where an expression of the input evaluates to a value, the expression that it is lowered
to evaluates to the same value with enough fuel, and it is of the kind of the relation. -/
theorem lowers_eval (hO : O.Sound) (hF : Funs Ps P S) :
    ∀ (n : Nat) {Γ : Id → Option (Id × LK)} {e e' : Expr} {k : LK}, Lowers S Γ e e' k →
      ∀ (env env' : Env), EnvOk Γ env env' →
        ∀ (fuel : Int), fuel ≤ n → ∀ (v : Value), eval O Ps fuel env e = .Ok v →
          Has k v ∧
            ∃ m : Int, ∀ fuel' : Int, m ≤ fuel' → eval O P fuel' env' e' = .Ok v := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro Γ e e' k h
  induction h with
  | var hx =>
    intro env env' hΓ fuel hfn v hv
    obtain ⟨w, h1, h2, hk⟩ := hΓ _ _ _ hx
    simp only [eval, h1] at hv
    cases hv
    exact ⟨hk, 0, fun _ _ => by simp only [eval, h2]⟩
  | int n =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    cases hv
    exact ⟨.int n, 0, fun _ _ => by simp only [eval]⟩
  | bool b =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    cases hv
    exact ⟨.prim rfl, 0, fun _ _ => by simp only [eval]⟩
  | frac n d =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    exact ⟨.prim (real_prim hv), 0, fun _ _ => by simp only [eval]; exact hv⟩
  | error e' k =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    cases hv
  | weaken _ hs ih =>
    intro env env' hΓ fuel hfn v hv
    obtain ⟨hk, m, e1⟩ := ih env env' hΓ fuel hfn v hv
    exact ⟨has_sub hs hk, m, e1⟩
  | plusInt _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨hka, n1, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, n2, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        cases hka; cases hkb
        simp only [arith_plus] at hv; cases hv
        refine ⟨.int _, max n1 n2, fun f hf => ?_⟩
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
        obtain ⟨hka, n1, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, n2, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        cases hka; cases hkb
        simp only [arith_plus] at hv; cases hv
        refine ⟨.int _, max n1 n2, fun f hf => ?_⟩
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
        obtain ⟨hka, n1, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, n2, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        refine ⟨.prim (plus_prim hv), max n1 n2, fun f hf => ?_⟩
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
        obtain ⟨hka, n1, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, n2, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        cases hka; cases hkb
        simp only [arith_minus] at hv; cases hv
        refine ⟨.int _, max n1 n2, fun f hf => ?_⟩
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
        obtain ⟨hka, n1, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, n2, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        refine ⟨.prim (minus_prim hv), max n1 n2, fun f hf => ?_⟩
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
        obtain ⟨hka, n1, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, n2, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        cases hka; cases hkb
        simp only [arith_times] at hv; cases hv
        refine ⟨.int _, max n1 n2, fun f hf => ?_⟩
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
        obtain ⟨hka, n1, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, n2, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        refine ⟨.prim (times_prim hv), max n1 n2, fun f hf => ?_⟩
        simp only [eval, e1 f (by omega), e2 f (by omega)]
        exact hv
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
        obtain ⟨hka, n1, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, n2, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        refine ⟨.prim (div_prim hv), max n1 n2, fun f hf => ?_⟩
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
        obtain ⟨hka, n1, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, n2, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        refine ⟨.prim (rem_prim hv), max n1 n2, fun f hf => ?_⟩
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
        obtain ⟨hka, n1, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, n2, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        refine ⟨.prim (mod_prim hv), max n1 n2, fun f hf => ?_⟩
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
        obtain ⟨hka, n1, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, n2, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        split at hv
        · next r hr =>
          cases hv
          refine ⟨.prim rfl, max n1 n2, fun f hf => ?_⟩
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
        obtain ⟨hka, n1, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, n2, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        split at hv
        · next r hr =>
          cases hv
          refine ⟨.prim rfl, max n1 n2, fun f hf => ?_⟩
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
        obtain ⟨hka, n1, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, n2, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        split at hv
        · next r hr =>
          cases hv
          refine ⟨.prim rfl, max n1 n2, fun f hf => ?_⟩
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
        obtain ⟨hka, n1, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, n2, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        split at hv
        · next r hr =>
          cases hv
          refine ⟨.prim rfl, max n1 n2, fun f hf => ?_⟩
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
        obtain ⟨hka, n1, e1⟩ := iha env env' hΓ fuel hfn va ha
        obtain ⟨hkb, n2, e2⟩ := ihb env env' hΓ fuel hfn vb hb
        split at hv
        · next r hr =>
          cases hv
          have hr' : O.value_eq P va vb = .Ok r := by
            rw [← hr, hO.value_eq, hO.value_eq (P := Ps)]
            cases hka with
            | prim hp => cases va <;> simp_all [IsPrim]
          refine ⟨.prim rfl, max n1 n2, fun f hf => ?_⟩
          simp only [eval, e1 f (by omega), e2 f (by omega), hr']
        · cases hv
        · cases hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | uminusInt _ iha =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      obtain ⟨hka, n1, e1⟩ := iha env env' hΓ fuel hfn va ha
      cases hka
      simp only [arith_neg] at hv; cases hv
      exact ⟨.int _, n1, fun f hf => by simp only [eval, e1 f hf, arith_neg]⟩
    · cases hv
    · cases hv
  | uminus _ iha =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      obtain ⟨hka, n1, e1⟩ := iha env env' hΓ fuel hfn va ha
      exact ⟨.prim (neg_prim hv), n1, fun f hf => by simp only [eval, e1 f hf]; exact hv⟩
    · cases hv
    · cases hv
  | not _ iha =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next b hb =>
      obtain ⟨_, n1, e1⟩ := iha env env' hΓ fuel hfn _ (eval_bool_ok hb)
      cases hv
      exact ⟨.prim rfl, n1, fun f hf => by simp [eval, eval_bool, e1 f hf]⟩
    · cases hv
    · cases hv
  | implies _ _ iha ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next a ha =>
      obtain ⟨_, n1, e1⟩ := iha env env' hΓ fuel hfn _ (eval_bool_ok ha)
      cases a with
      | true =>
        simp only [dite_true] at hv
        split at hv
        · next b hb =>
          obtain ⟨_, n2, e2⟩ := ihb env env' hΓ fuel hfn _ (eval_bool_ok hb)
          cases hv
          exact ⟨.prim rfl, max n1 n2, fun f hf => by
            simp [eval, eval_bool, e1 f (by omega), e2 f (by omega)]⟩
        · cases hv
        · cases hv
      | false =>
        simp at hv
        cases hv
        exact ⟨.prim rfl, n1, fun f hf => by simp [eval, eval_bool, e1 f hf]⟩
    · cases hv
    · cases hv
  | andNil =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    rw [eval_and] at hv
    cases hv
    exact ⟨.prim rfl, 0, fun _ _ => by simp only [eval]; rw [eval_and]⟩
  | andCons _ _ iha ihr =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    rw [eval_and] at hv
    split at hv
    · next b hb =>
      obtain ⟨_, n1, e1⟩ := iha env env' hΓ fuel hfn _ (eval_bool_ok hb)
      cases b with
      | true =>
        simp only [dite_true] at hv
        obtain ⟨hk, n2, e2⟩ := ihr env env' hΓ fuel hfn v (by simp only [eval]; exact hv)
        refine ⟨hk, max n1 n2, fun f hf => ?_⟩
        have h2 := e2 f (by omega)
        simp only [eval] at h2 ⊢
        rw [eval_and]
        simp only [eval_bool, e1 f (by omega), dite_true, h2]
      | false =>
        simp at hv
        cases hv
        refine ⟨.prim rfl, n1, fun f hf => ?_⟩
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
    exact ⟨.prim rfl, 0, fun _ _ => by simp only [eval]; rw [eval_or]⟩
  | orCons _ _ iha ihr =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    rw [eval_or] at hv
    split at hv
    · next b hb =>
      obtain ⟨_, n1, e1⟩ := iha env env' hΓ fuel hfn _ (eval_bool_ok hb)
      cases b with
      | false =>
        simp at hv
        obtain ⟨hk, n2, e2⟩ := ihr env env' hΓ fuel hfn v (by simp only [eval]; exact hv)
        refine ⟨hk, max n1 n2, fun f hf => ?_⟩
        have h2 := e2 f (by omega)
        simp only [eval] at h2 ⊢
        rw [eval_or]
        simp [eval_bool, e1 f (by omega), h2]
      | true =>
        simp only [dite_true] at hv
        cases hv
        refine ⟨.prim rfl, n1, fun f hf => ?_⟩
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
      obtain ⟨_, n1, e1⟩ := ihc env env' hΓ fuel hfn _ (eval_bool_ok hc)
      cases c with
      | true =>
        simp only [dite_true] at hv
        obtain ⟨hk, n2, e2⟩ := iha env env' hΓ fuel hfn v hv
        exact ⟨hk, max n1 n2, fun f hf => by
          simp [eval, eval_bool, e1 f (by omega), e2 f (by omega)]⟩
      | false =>
        simp at hv
        obtain ⟨hk, n2, e2⟩ := ihb env env' hΓ fuel hfn v hv
        exact ⟨hk, max n1 n2, fun f hf => by
          simp [eval, eval_bool, e1 f (by omega), e2 f (by omega)]⟩
    · cases hv
    · cases hv
  | assume _ _ ihp ihb =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval] at hv
    split at hv
    · next c hc =>
      obtain ⟨_, n1, e1⟩ := ihp env env' hΓ fuel hfn _ (eval_bool_ok hc)
      cases c with
      | true =>
        simp only [dite_true] at hv
        obtain ⟨hk, n2, e2⟩ := ihb env env' hΓ fuel hfn v hv
        exact ⟨hk, max n1 n2, fun f hf => by
          simp [eval, eval_bool, e1 f (by omega), e2 f (by omega)]⟩
      | false =>
        simp at hv
    · cases hv
    · cases hv
  | tupleNil =>
    intro env env' hΓ fuel hfn v hv
    simp only [eval, eval_list] at hv
    cases hv
    exact ⟨.tupleNil, 0, fun _ _ => by simp only [eval, eval_list]⟩
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
          obtain ⟨hk1, n1, e1⟩ := ihe env env' hΓ fuel hfn w hw
          obtain ⟨hk2, n2, e2⟩ :=
            ihr env env' hΓ fuel hfn (.TupleV ws) (by simp only [eval, hws])
          refine ⟨.tupleCons hk1 hk2, max n1 n2, fun f hf => ?_⟩
          simp only [eval]
          rw [eval_list]
          simp only [e1 f (by omega), eval_tuple_inv (e2 f (by omega))]
        · cases hvs
        · cases hvs
      · cases hvs
      · cases hvs
    · cases hv
    · cases hv
  | @call f g ks k tps tps' es es' hf _ iha =>
    intro env env' hΓ fuel hfn v hv
    obtain ⟨params, params', body, body', hFS, hFP, hnd, hl1, hl2, hlow⟩ := hF f g ks k hf
    simp only [eval] at hv
    split at hv
    · next vs hvs =>
      obtain ⟨hpos, bs, hbs, hbody⟩ := call_inv hFS hv
      obtain ⟨hHas, n1, e1⟩ := iha env env' hΓ fuel hfn (.TupleV vs) (by simp only [eval, hvs])
      obtain ⟨bs', hbs', hl⟩ := bind_lowered hnd hl1 hl2 hHas hbs
      cases n with
      | zero => omega
      | succ m =>
      obtain ⟨hk, m2, e2⟩ := ihn m (Nat.lt_succ_self m) hlow
        (Env.Env (bind_types [] tps (env_types env)) bs)
        (Env.Env (bind_types [] tps' (env_types env')) bs') hl (fuel - 1) (by omega) v hbody
      refine ⟨hk, max (max n1 (m2 + 1)) 1, fun f' hf' => ?_⟩
      simp only [eval, eval_tuple_inv (e1 f' (by omega))]
      rw [call_fun hFP (by omega) _ _ hbs']
      exact e2 (f' - 1) (by omega)
    · cases hv
    · cases hv

end Evaluation

/-! ## The check -/

mutual
/-- Whether `e` is lowered to `e'` with values of the kind `k`, in at most `n` steps of the
check. -/
def lowersCheck (S : LSig) : Nat → (Id → Option (Id × LK)) → Expr → Expr → LK → Bool
  | 0, _, _, _, _ => false
  | n + 1, Γ, e, e', k =>
    match e, e' with
    | .Error, _ => true
    | .Variable x, .Variable y =>
      match Γ x with
      | some (y0, k0) => y0 == y && Sub k0 k
      | none => false
    | .IntegerLiteral a, .IntegerLiteral b => a == b && Sub .int k
    | .BooleanLiteral a, .BooleanLiteral b => a == b && Sub .prim k
    | .FractionLiteral a b, .FractionLiteral c d => a == c && b == d && Sub .prim k
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
      (Sub .int k && lowersCheck S n Γ a a' .int && lowersCheck S n Γ b b' .int) ||
      (Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any)
    | .UMinus a, .UMinus a' =>
      (Sub .int k && lowersCheck S n Γ a a' .int) || (Sub .prim k && lowersCheck S n Γ a a' .any)
    | .Division a b, .Division a' b' =>
      Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any
    | .Remainder a b, .Remainder a' b' =>
      Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any
    | .Modulo a b, .Modulo a' b' =>
      Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any
    | .LessThan a b, .LessThan a' b' =>
      Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any
    | .GreaterThan a b, .GreaterThan a' b' =>
      Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any
    | .LessEquals a b, .LessEquals a' b' =>
      Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any
    | .GreaterEquals a b, .GreaterEquals a' b' =>
      Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any
    | .Equals a b, .Equals a' b' =>
      Sub .prim k && lowersCheck S n Γ a a' .prim && lowersCheck S n Γ b b' .prim
    | .Not a, .Not a' => Sub .prim k && lowersCheck S n Γ a a' .any
    | .Implies a b, .Implies a' b' =>
      Sub .prim k && lowersCheck S n Γ a a' .any && lowersCheck S n Γ b b' .any
    | .And es, .And es' => Sub .prim k && lowersAll S n Γ es es'
    | .Or es, .Or es' => Sub .prim k && lowersAll S n Γ es es'
    | .IfExpr c a b, .IfExpr c' a' b' =>
      lowersCheck S n Γ c c' .any && lowersCheck S n Γ a a' k && lowersCheck S n Γ b b' k
    | .Assume p a, .Assume p' a' => lowersCheck S n Γ p p' .any && lowersCheck S n Γ a a' k
    | .FunctionInvocation f _ es, .FunctionInvocation g _ es' =>
      match S f with
      | some (g0, ks, k0) => g0 == g && Sub k0 k && lowersArgs S n Γ es es' ks
      | none => false
    | _, _ => false

/-- Whether each of `es` is lowered to the expression of `es'` at its position, with any
values. -/
def lowersAll (S : LSig) : Nat → (Id → Option (Id × LK)) → List Expr → List Expr → Bool
  | 0, _, _, _ => false
  | _ + 1, _, [], [] => true
  | n + 1, Γ, a :: es, a' :: es' => lowersCheck S n Γ a a' .any && lowersAll S n Γ es es'
  | _ + 1, _, _, _ => false

/-- Whether each of the arguments `es` is lowered to that of `es'` at its position, of the kind
of `ks` at its position. -/
def lowersArgs (S : LSig) :
    Nat → (Id → Option (Id × LK)) → List Expr → List Expr → List LK → Bool
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
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨rfl, hs⟩ := h
          exact .weaken (.var hx) hs
        · cases h
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, hs⟩ := h
        exact .weaken (.int _) hs
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, hs⟩ := h
        exact .weaken (.bool _) hs
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨rfl, rfl⟩, hs⟩ := h
        exact .weaken (.frac _ _) hs
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
      · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
        rcases h with ⟨⟨hs, ha⟩, hb⟩ | ⟨⟨hs, ha⟩, hb⟩
        · exact .weaken (.timesInt (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
        · exact .weaken (.times (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
      · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
        rcases h with ⟨hs, ha⟩ | ⟨hs, ha⟩
        · exact .weaken (.uminusInt (ih _ _ _ _ ha)) hs
        · exact .weaken (.uminus (ih _ _ _ _ ha)) hs
      · simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hs, ha⟩, hb⟩ := h
        exact .weaken (.div (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
      · simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hs, ha⟩, hb⟩ := h
        exact .weaken (.rem (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
      · simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hs, ha⟩, hb⟩ := h
        exact .weaken (.mod (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
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
      · simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hs, ha⟩, hb⟩ := h
        exact .weaken (.eq (ih _ _ _ _ ha) (ih _ _ _ _ hb)) hs
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
