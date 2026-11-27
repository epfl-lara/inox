/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Sexp
import Inox.Bags

/-!
# The input of a certificate in the semantics

The `input` section of a certificate holds each constraint that the solver was given with the
term that the encoders make of it. This module reads both as expressions of the semantics
(`readExpr`), for the expressions that the theorem on the encoder of bags covers
(`Inox.Bags.Encodes`), decides whether the second is what the encoder makes of the first
(`encodesCheck`), and states what that gives (`input_encoded`): where the constraints of the
input all evaluate to `true`, so do their encoded terms, in a program that defines the
datatype of the encoder as the encoder does and on values of the free variables that relate.

`covers` says of a certificate how many of its constraints the theorem covers, and what the
first of the others has that isn't read. It reads nothing else than variables, integer
literals, sums, negations, equalities and the operations of bags, so it tells which
expressions the theorem has to cover next.
-/

namespace Inox.Input

open Inox.Semantics Inox.Bags Logos

/-- The types of elements that are read: `Int` and type parameters. -/
def sameTy : Ty → Ty → Bool
  | .IntegerType, .IntegerType => true
  | .TypeParameter a, .TypeParameter b => a == b
  | _, _ => false

theorem sameTy_eq : ∀ {a b : Ty}, sameTy a b = true → a = b
  | .IntegerType, .IntegerType, _ => rfl
  | .TypeParameter a, .TypeParameter b, h => by
    simp only [sameTy, beq_iff_eq] at h
    rw [h]

/-- Whether `e'` is what the encoder of bags makes of `e`, an expression of the kind `k`. -/
def encodesCheck (N : Names) (Γ : List (Id × Kind)) (Te : Ty) : Expr → Expr → Kind → Bool
  | .Variable x, .Variable y, k => x == y && Γ.lookup x == some k
  | .IntegerLiteral n, .IntegerLiteral m, .int => n == m
  | .Plus a b, .Plus a' b', .int => encodesCheck N Γ Te a a' .int && encodesCheck N Γ Te b b' .int
  | .FiniteBag [] _, .ADT c [t] [], .bag => c == N.leaf && sameTy t Te
  | .BagAdd b e, .ADT c [t] [.IntegerLiteral op, b', .ADT c2 [t2] [e', .IntegerLiteral one]],
      .bag =>
    c == N.node && sameTy t Te && op == 0 && c2 == N.elem && sameTy t2 Te && one == 1 &&
      encodesCheck N Γ Te b b' .bag && encodesCheck N Γ Te e e' .elem
  | .BagUnion a b, .ADT c [t] [.IntegerLiteral op, a', b'], .bag =>
    c == N.node && sameTy t Te && op == 0 &&
      encodesCheck N Γ Te a a' .bag && encodesCheck N Γ Te b b' .bag
  | .BagDifference a b, .ADT c [t] [.IntegerLiteral op, a', b'], .bag =>
    c == N.node && sameTy t Te && op == 1 &&
      encodesCheck N Γ Te a a' .bag && encodesCheck N Γ Te b b' .bag
  | .BagIntersection a b, .ADT c [t] [.IntegerLiteral op, a', b'], .bag =>
    c == N.node && sameTy t Te && op == 2 &&
      encodesCheck N Γ Te a a' .bag && encodesCheck N Γ Te b b' .bag
  | .MultiplicityInBag e b, .FunctionInvocation g [t] [b', e'], .int =>
    g == N.get && sameTy t Te && encodesCheck N Γ Te e e' .elem && encodesCheck N Γ Te b b' .bag
  | .Equals a b, .Equals a' b', .bool =>
    (encodesCheck N Γ Te a a' .bag && encodesCheck N Γ Te b b' .bag) ||
      (encodesCheck N Γ Te a a' .int && encodesCheck N Γ Te b b' .int)
  | .Not a, .Not a', .bool => encodesCheck N Γ Te a a' .bool
  | _, _, _ => false

theorem encodesCheck_sound {N : Names} {Γ : List (Id × Kind)} {Te : Ty} {e e' : Expr} {k : Kind} :
    encodesCheck N Γ Te e e' k = true → Encodes N (fun x => Γ.lookup x) Te e e' k := by
  fun_induction encodesCheck N Γ Te e e' k <;> intro h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hk⟩ := h
    exact .var _ _ hk
  · simp only [beq_iff_eq] at h
    subst h
    exact .int _
  · next iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .plus (iha h.1) (ihb h.2)
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, ht⟩ := h
    cases sameTy_eq ht
    exact .empty _
  · next ihb ihe =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨rfl, ht⟩, rfl⟩, rfl⟩, ht2⟩, rfl⟩, hb⟩, he⟩ := h
    cases sameTy_eq ht
    cases sameTy_eq ht2
    exact .add (ihb hb) (ihe he)
  · next iha ihb =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨rfl, ht⟩, rfl⟩, ha⟩, hb⟩ := h
    cases sameTy_eq ht
    exact .union (iha ha) (ihb hb)
  · next iha ihb =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨rfl, ht⟩, rfl⟩, ha⟩, hb⟩ := h
    cases sameTy_eq ht
    exact .difference (iha ha) (ihb hb)
  · next iha ihb =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨rfl, ht⟩, rfl⟩, ha⟩, hb⟩ := h
    cases sameTy_eq ht
    exact .intersection (iha ha) (ihb hb)
  · next ihe ihb =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, ht⟩, he⟩, hb⟩ := h
    cases sameTy_eq ht
    exact .mult (ihe he) (ihb hb)
  · next iha ihb iha' ihb' =>
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact .eqBag (iha ha) (ihb hb)
    · exact .eqInt (iha' ha) (ihb' hb)
  · next iha => exact .not (iha h)
  · cases h

/-- Where the constraints of the input all evaluate to `true`, so do their encoded terms: the
program defines the datatype of the encoder, its `get`, its invariant and its equality as the
encoder does, and the values of the free variables are the same in both, or a bag and its
encoding (`hΓ`). -/
theorem input_encoded {O : Oracle} (hO : O.Sound) {P : Program} {N : Names} (hN : N.Distinct)
    (hP : HasBags N P) {inv bi eq b1 b2 : Id} (hS : HasSort N inv bi eq P)
    (hQ : HasEquals N eq b1 b2 P) (h1x : b1 ≠ N.x) (h2x : b2 ≠ N.x) (h12 : b1 ≠ b2)
    {K : Value → Prop} {E : Value → Value → Bool} (hE : KeyEq O P K E) {T0 Te : Ty}
    (hK : ∀ bs vs, O.params_have_types P (Env.Env (bind_types [N.T] [T0] []) bs) vs
        [.Param N.x (.TypeParameter N.T)] = true ↔ ∃ v, vs = [v] ∧ K v)
    {env env' : Env} (hT : O.resolve_all (env_types env') [Te] = [T0])
    {Γ : List (Id × Kind)}
    (hΓ : ∀ x k, Γ.lookup x = some k → ∃ v v', lookup_var (env_vars env) x = .Ok v ∧
      lookup_var (env_vars env') x = .Ok v' ∧ Rel O P N K E T0 k v v')
    {cs : List (Expr × Expr)} (hc : ∀ p ∈ cs, encodesCheck N Γ Te p.1 p.2 .bool = true)
    (hsol : ∀ p ∈ cs, ∃ n, eval O P n env p.1 = .Ok (.BoolV true)) :
    ∀ p ∈ cs, ∃ n, eval O P n env' p.2 = .Ok (.BoolV true) := by
  intro p hp
  obtain ⟨n, hn⟩ := hsol p hp
  obtain ⟨_, m, ⟨rfl, _⟩, hm⟩ := encodes_eval hO hN hP hS hQ h1x h2x h12 hE hK hT hΓ
    (encodesCheck_sound (hc p hp)) n _ hn
  exact ⟨m, hm m (Int.le_refl m)⟩

/-! ## Reading the input -/

/-- A symbol without its number. -/
def base (a : String) : String := String.ofList (a.toList.takeWhile (· != '!'))

/-- The type of the elements that `s` reads as. -/
def readTy : Sexp → Except String Ty
  | .atom "Int" => .ok .IntegerType
  | .atom a => if a.contains '!' then .ok (.TypeParameter a) else .error a
  | .expr (.atom a :: _) => .error a
  | _ => .error "a type"

/-- The expression that `s` reads as, or what it has that isn't read. -/
def readExpr : Nat → Sexp → Except String Expr
  | 0, _ => .error "a term too deep"
  | n + 1, s =>
    match s with
    | .atom a =>
      if !a.isEmpty && a.all Char.isDigit then .ok (.IntegerLiteral a.toNat!)
      else if a.contains '!' then .ok (.Variable a)
      else .error a
    | .expr [.atom "not", a] => do pure (.Not (← readExpr n a))
    | .expr [.atom "+", a, b] => do pure (.Plus (← readExpr n a) (← readExpr n b))
    | .expr [.atom "=", a, b] => do pure (.Equals (← readExpr n a) (← readExpr n b))
    | .expr [.atom "as", .atom "bag.empty", t] => do pure (.FiniteBag [] (← readTy t))
    | .expr [.atom "bag.insert", b, e] => do pure (.BagAdd (← readExpr n b) (← readExpr n e))
    | .expr [.atom "bag.union", a, b] => do pure (.BagUnion (← readExpr n a) (← readExpr n b))
    | .expr [.atom "bag.difference", a, b] => do
      pure (.BagDifference (← readExpr n a) (← readExpr n b))
    | .expr [.atom "bag.intersection", a, b] => do
      pure (.BagIntersection (← readExpr n a) (← readExpr n b))
    | .expr [.atom "bag.multiplicity", e, b] => do
      pure (.MultiplicityInBag (← readExpr n e) (← readExpr n b))
    | .expr [.atom "as", .atom c, .expr [.atom _, t]] => do pure (.ADT c [← readTy t] [])
    | .expr (.expr [.atom "as", .atom c, .expr [.atom _, t]] :: args) => do
      pure (.ADT c [← readTy t] (← args.mapM (readExpr n)))
    | .expr (.expr [.atom "as", .atom f, .expr [t]] :: args) => do
      pure (.FunctionInvocation f [← readTy t] (← args.mapM (readExpr n)))
    | .expr (.atom a :: _) => .error a
    | .expr (.expr [.atom "as", .atom a, _] :: _) => .error (base a)
    | .expr (.expr [.atom "as", .expr (.atom "_" :: .atom a :: _), _] :: _) => .error a
    | _ => .error "a term"

/-- The kinds that the variables of `e`, of the kind `k`, have to have. An equality is of bags
when a side is an operation of bags, and of integers otherwise. -/
def kinds : Expr → Kind → List (Id × Kind)
  | .Variable x, k => [(x, k)]
  | .Plus a b, _ => kinds a .int ++ kinds b .int
  | .BagAdd b e, _ => kinds b .bag ++ kinds e .elem
  | .BagUnion a b, _ => kinds a .bag ++ kinds b .bag
  | .BagDifference a b, _ => kinds a .bag ++ kinds b .bag
  | .BagIntersection a b, _ => kinds a .bag ++ kinds b .bag
  | .MultiplicityInBag e b, _ => kinds e .elem ++ kinds b .bag
  | .Equals a b, _ =>
    let isBag : Expr → Bool
      | .FiniteBag _ _ | .BagAdd _ _ | .BagUnion _ _ | .BagDifference _ _
      | .BagIntersection _ _ => true
      | _ => false
    let k := if isBag a || isBag b then Kind.bag else Kind.int
    kinds a k ++ kinds b k
  | .Not a, _ => kinds a .bool
  | _, _ => []

/-- The atoms of `s`. -/
def atoms : Nat → Sexp → List String
  | 0, _ => []
  | _ + 1, .atom a => [a]
  | n + 1, .expr l => l.flatMap (atoms n)

/-- The names of the encoder in the encoded terms: the symbols `Node`, `Elem`, `Leaf` and
`get`, whatever their numbers. The other names are not in the terms of constraints. -/
def namesOf (encoded : List Sexp) : Names :=
  let all := encoded.flatMap (atoms 1000)
  let find (name : String) := (all.find? fun a => base a == name).getD name
  { bag := "Bag", node := find "Node", elem := find "Elem", leaf := find "Leaf", op := "op",
    left := "left", right := "right", key := "key", value := "value", get := find "get",
    T := "T", b := "b", x := "x", v1 := "v1", v2 := "v2" }

/-- The constraints of the `input` section of a certificate, each with its encoded term. -/
def constraintsOf (certificate : Sexp) : List (Sexp × Sexp) :=
  match certificate with
  | .expr sections => sections.flatMap fun
    | .expr (.atom "input" :: input) => input.filterMap fun
      | .expr (.atom "constraint" :: i :: .expr [.atom "encoded", e] :: _) => some (i, e)
      | _ => none
    | _ => []
  | _ => []

/-- The type of the elements of the bags of an encoded expression: that of its first value of
the encoder's datatype or call of `get`. -/
def elemTy : Expr → Option Ty
  | .ADT _ [t] _ => some t
  | .FunctionInvocation _ [t] _ => some t
  | .Not a => elemTy a
  | .Equals a b => (elemTy a).orElse fun _ => elemTy b
  | .Plus a b => (elemTy a).orElse fun _ => elemTy b
  | _ => none

/-- What `input_encoded` is about for a certificate: the names of the encoder, the kinds of
the free variables, the type of the elements, and the constraints that are read and that the
check accepts. It also gives the number of constraints, and what the first that isn't covered
has that isn't read. -/
structure Coverage where
  names : Names
  vars : List (Id × Kind)
  elem : Ty
  covered : List (Expr × Expr)
  constraints : Nat
  first : Option String

def covers (certificate : Sexp) : Coverage :=
  let cs := constraintsOf certificate
  let N := namesOf (cs.map (·.2))
  let read := cs.map fun (i, e) => do
    let i ← readExpr 1000 i
    let e ← readExpr 1000 e
    pure (i, e)
  let pairs := read.filterMap fun r => r.toOption
  let Γ := (pairs.flatMap fun p => kinds p.1 .bool).eraseDups
  let Te := (pairs.findSome? fun p => elemTy p.2).getD .IntegerType
  let checked := read.map fun
    | .error what => Except.error s!"`{what}` is not read"
    | .ok p => if encodesCheck N Γ Te p.1 p.2 .bool then .ok p
      else .error "it is read, and its encoded term is not what the theorem expects"
  { names := N, vars := Γ, elem := Te, covered := checked.filterMap fun r => r.toOption,
    constraints := cs.length,
    first := checked.findSome? fun | .error why => some why | .ok _ => none }

theorem covers_check (certificate : Sexp) :
    ∀ p ∈ (covers certificate).covered,
      encodesCheck (covers certificate).names (covers certificate).vars (covers certificate).elem
        p.1 p.2 .bool = true := by
  intro p hp
  simp only [covers, List.mem_filterMap, List.mem_map] at hp
  obtain ⟨r, ⟨q, _, rfl⟩, hr⟩ := hp
  split at hr
  · cases hr
  · next p' _ =>
    split at hr
    · next hc => cases hr; exact hc
    · cases hr

/-- `input_encoded` for the constraints of a certificate that `covers` gives. -/
theorem covers_encoded (certificate : Sexp) {O : Oracle} (hO : O.Sound) {P : Program}
    (hN : (covers certificate).names.Distinct) (hP : HasBags (covers certificate).names P)
    {inv bi eq b1 b2 : Id} (hS : HasSort (covers certificate).names inv bi eq P)
    (hQ : HasEquals (covers certificate).names eq b1 b2 P)
    (h1x : b1 ≠ (covers certificate).names.x) (h2x : b2 ≠ (covers certificate).names.x)
    (h12 : b1 ≠ b2) {K : Value → Prop} {E : Value → Value → Bool} (hE : KeyEq O P K E)
    {T0 : Ty}
    (hK : ∀ bs vs, O.params_have_types P
        (Env.Env (bind_types [(covers certificate).names.T] [T0] []) bs) vs
        [.Param (covers certificate).names.x (.TypeParameter (covers certificate).names.T)] =
          true ↔ ∃ v, vs = [v] ∧ K v)
    {env env' : Env} (hT : O.resolve_all (env_types env') [(covers certificate).elem] = [T0])
    (hΓ : ∀ x k, (covers certificate).vars.lookup x = some k → ∃ v v',
      lookup_var (env_vars env) x = .Ok v ∧ lookup_var (env_vars env') x = .Ok v' ∧
        Rel O P (covers certificate).names K E T0 k v v')
    (hsol : ∀ p ∈ (covers certificate).covered, ∃ n, eval O P n env p.1 = .Ok (.BoolV true)) :
    ∀ p ∈ (covers certificate).covered, ∃ n, eval O P n env' p.2 = .Ok (.BoolV true) :=
  input_encoded hO hN hP hS hQ h1x h2x h12 hE hK hT hΓ (covers_check certificate) hsol

end Inox.Input
