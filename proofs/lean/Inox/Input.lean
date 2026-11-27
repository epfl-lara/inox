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
first of the others has that isn't read. It reads nothing else than variables, literals,
sums, differences, comparisons, connectives, conditionals, lets, equalities and the operations
of bags, so it tells which expressions the theorem has to cover next.
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

theorem lookup_cons (x y : Id) (kx : Kind) (Γ : List (Id × Kind)) :
    ((x, kx) :: Γ).lookup y = if y = x then some kx else Γ.lookup y := by
  by_cases h : y = x
  · simp [List.lookup, h]
  · have hb : (y == x) = false := by simpa using h
    simp [List.lookup, h, hb]

/-- Whether `e'` is what the encoder of bags makes of `e`, an expression of the kind `k`. -/
def encodesCheck (N : Names) (Te : Ty) : List (Id × Kind) → Expr → Expr → Kind → Bool
  | Γ, .Variable x, .Variable y, k => x == y && Γ.lookup x == some k
  | _, .IntegerLiteral n, .IntegerLiteral m, .int => n == m
  | _, .BooleanLiteral b, .BooleanLiteral c, .bool => b == c
  | Γ, .Plus a b, .Plus a' b', .int =>
    encodesCheck N Te Γ a a' .int && encodesCheck N Te Γ b b' .int
  | Γ, .Minus a b, .Minus a' b', .int =>
    encodesCheck N Te Γ a a' .int && encodesCheck N Te Γ b b' .int
  | Γ, .LessThan a b, .LessThan a' b', .bool =>
    encodesCheck N Te Γ a a' .int && encodesCheck N Te Γ b b' .int
  | Γ, .GreaterThan a b, .GreaterThan a' b', .bool =>
    encodesCheck N Te Γ a a' .int && encodesCheck N Te Γ b b' .int
  | Γ, .LessEquals a b, .LessEquals a' b', .bool =>
    encodesCheck N Te Γ a a' .int && encodesCheck N Te Γ b b' .int
  | Γ, .GreaterEquals a b, .GreaterEquals a' b', .bool =>
    encodesCheck N Te Γ a a' .int && encodesCheck N Te Γ b b' .int
  | _, .FiniteBag [] _, .ADT c [t] [], .bag => c == N.leaf && sameTy t Te
  | Γ, .BagAdd b e,
      .ADT c [t] [.IntegerLiteral op, b', .ADT c2 [t2] [e', .IntegerLiteral one]], .bag =>
    c == N.node && sameTy t Te && op == 0 && c2 == N.elem && sameTy t2 Te && one == 1 &&
      encodesCheck N Te Γ b b' .bag && encodesCheck N Te Γ e e' .elem
  | Γ, .BagUnion a b, .ADT c [t] [.IntegerLiteral op, a', b'], .bag =>
    c == N.node && sameTy t Te && op == 0 &&
      encodesCheck N Te Γ a a' .bag && encodesCheck N Te Γ b b' .bag
  | Γ, .BagDifference a b, .ADT c [t] [.IntegerLiteral op, a', b'], .bag =>
    c == N.node && sameTy t Te && op == 1 &&
      encodesCheck N Te Γ a a' .bag && encodesCheck N Te Γ b b' .bag
  | Γ, .BagIntersection a b, .ADT c [t] [.IntegerLiteral op, a', b'], .bag =>
    c == N.node && sameTy t Te && op == 2 &&
      encodesCheck N Te Γ a a' .bag && encodesCheck N Te Γ b b' .bag
  | Γ, .MultiplicityInBag e b, .FunctionInvocation g [t] [b', e'], .int =>
    g == N.get && sameTy t Te && encodesCheck N Te Γ e e' .elem && encodesCheck N Te Γ b b' .bag
  | Γ, .Equals a b, .Equals a' b', .bool =>
    (encodesCheck N Te Γ a a' .bag && encodesCheck N Te Γ b b' .bag) ||
      (encodesCheck N Te Γ a a' .int && encodesCheck N Te Γ b b' .int)
  | Γ, .Not a, .Not a', .bool => encodesCheck N Te Γ a a' .bool
  | _, .And [], .And [], .bool => true
  | Γ, .And (a :: as), .And (a' :: as'), .bool =>
    encodesCheck N Te Γ a a' .bool && encodesCheck N Te Γ (.And as) (.And as') .bool
  | _, .Or [], .Or [], .bool => true
  | Γ, .Or (a :: as), .Or (a' :: as'), .bool =>
    encodesCheck N Te Γ a a' .bool && encodesCheck N Te Γ (.Or as) (.Or as') .bool
  | Γ, .Implies a b, .Implies a' b', .bool =>
    encodesCheck N Te Γ a a' .bool && encodesCheck N Te Γ b b' .bool
  | Γ, .IfExpr c a b, .IfExpr c' a' b', k =>
    encodesCheck N Te Γ c c' .bool && encodesCheck N Te Γ a a' k && encodesCheck N Te Γ b b' k
  | Γ, .Let x a b, .Let y a' b', k =>
    x == y &&
      ((encodesCheck N Te Γ a a' .elem && encodesCheck N Te ((x, .elem) :: Γ) b b' k) ||
        (encodesCheck N Te Γ a a' .int && encodesCheck N Te ((x, .int) :: Γ) b b' k) ||
        (encodesCheck N Te Γ a a' .bool && encodesCheck N Te ((x, .bool) :: Γ) b b' k) ||
        (encodesCheck N Te Γ a a' .bag && encodesCheck N Te ((x, .bag) :: Γ) b b' k))
  | _, _, _, _ => false
termination_by _ e => sizeOf e
decreasing_by all_goals (simp_wf; try omega)

theorem encodesCheck_sound {N : Names} {Γ : List (Id × Kind)} {Te : Ty} {e e' : Expr} {k : Kind} :
    encodesCheck N Te Γ e e' k = true → Encodes N Te (fun x => Γ.lookup x) e e' k := by
  fun_induction encodesCheck N Te Γ e e' k <;> intro h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hk⟩ := h
    exact .var _ _ hk
  · simp only [beq_iff_eq] at h
    subst h
    exact .int _
  · simp only [beq_iff_eq] at h
    subst h
    exact .bool _
  · next iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .plus (iha h.1) (ihb h.2)
  · next iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .minus (iha h.1) (ihb h.2)
  · next iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .lt (iha h.1) (ihb h.2)
  · next iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .gt (iha h.1) (ihb h.2)
  · next iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .le (iha h.1) (ihb h.2)
  · next iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .ge (iha h.1) (ihb h.2)
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
  · exact .andNil
  · next iha ihr =>
    simp only [Bool.and_eq_true] at h
    exact .andCons (iha h.1) (ihr h.2)
  · exact .orNil
  · next iha ihr =>
    simp only [Bool.and_eq_true] at h
    exact .orCons (iha h.1) (ihr h.2)
  · next iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .implies (iha h.1) (ihb h.2)
  · next ihc iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .ite (ihc h.1.1) (iha h.1.2) (ihb h.2)
  · next a1 b1 a2 b2 a3 b3 a4 b4 =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [lookup_cons] at b1 b2 b3 b4
    rcases h with ((⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨ha, hb⟩) | ⟨ha, hb⟩
    · exact .let_ _ (a1 ha) (b1 hb)
    · exact .let_ _ (a2 ha) (b2 hb)
    · exact .let_ _ (a3 ha) (b3 hb)
    · exact .let_ _ (a4 ha) (b4 hb)
  · cases h

/-- Where the constraints of the input all evaluate to `true` in the program `Ps` of the input,
so do their encoded terms in the encoded program `P`: it defines the datatype of the encoder,
its `get`, its invariant and its equality as the encoder does, the values of the free variables
are the same in both, or a bag and its encoding (`hΓ`), and both programs have the same
equality on the elements. -/
theorem input_encoded {O : Oracle} (hO : O.Sound) {P : Program} {N : Names} (hN : N.Distinct)
    (hP : HasBags N P) {inv bi eq b1 b2 : Id} (hS : HasSort N inv bi eq P)
    (hQ : HasEquals N eq b1 b2 P) (h1x : b1 ≠ N.x) (h2x : b2 ≠ N.x) (h12 : b1 ≠ b2)
    {K : Value → Prop} {E : Value → Value → Bool} (hE : KeyEq O P K E) {Ps : Program}
    (hEs : KeyEq O Ps K E) {T0 Te : Ty}
    (hK : ∀ bs vs, O.params_have_types P (Env.Env (bind_types [N.T] [T0] []) bs) vs
        [.Param N.x (.TypeParameter N.T)] = true ↔ ∃ v, vs = [v] ∧ K v)
    {env env' : Env} (hT : O.resolve_all (env_types env') [Te] = [T0])
    {Γ : List (Id × Kind)}
    (hΓ : ∀ x k, Γ.lookup x = some k → ∃ v v', lookup_var (env_vars env) x = .Ok v ∧
      lookup_var (env_vars env') x = .Ok v' ∧ Rel O P N K E T0 k v v')
    {cs : List (Expr × Expr)} (hc : ∀ p ∈ cs, encodesCheck N Te Γ p.1 p.2 .bool = true)
    (hsol : ∀ p ∈ cs, ∃ n, eval O Ps n env p.1 = .Ok (.BoolV true)) :
    ∀ p ∈ cs, ∃ n, eval O P n env' p.2 = .Ok (.BoolV true) := by
  intro p hp
  obtain ⟨n, hn⟩ := hsol p hp
  obtain ⟨_, m, ⟨rfl, _⟩, hm⟩ := encodes_eval hO hN hP hS hQ h1x h2x h12 hE hEs hK
    (encodesCheck_sound (hc p hp)) env env' hT hΓ n _ hn
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
      else if a == "true" then .ok (.BooleanLiteral true)
      else if a == "false" then .ok (.BooleanLiteral false)
      else if a.contains '!' then .ok (.Variable a)
      else .error a
    | .expr [.atom "not", a] => do pure (.Not (← readExpr n a))
    | .expr [.atom "+", a, b] => do pure (.Plus (← readExpr n a) (← readExpr n b))
    | .expr [.atom "-", a, b] => do pure (.Minus (← readExpr n a) (← readExpr n b))
    | .expr [.atom "<", a, b] => do pure (.LessThan (← readExpr n a) (← readExpr n b))
    | .expr [.atom ">", a, b] => do pure (.GreaterThan (← readExpr n a) (← readExpr n b))
    | .expr [.atom "<=", a, b] => do pure (.LessEquals (← readExpr n a) (← readExpr n b))
    | .expr [.atom ">=", a, b] => do pure (.GreaterEquals (← readExpr n a) (← readExpr n b))
    | .expr (.atom "and" :: as) => do pure (.And (← as.mapM (readExpr n)))
    | .expr (.atom "or" :: as) => do pure (.Or (← as.mapM (readExpr n)))
    | .expr [.atom "=>", a, b] => do pure (.Implies (← readExpr n a) (← readExpr n b))
    | .expr [.atom "ite", c, a, b] => do
      pure (.IfExpr (← readExpr n c) (← readExpr n a) (← readExpr n b))
    | .expr [.atom "let", .expr [.expr [.atom x, a]], b] => do
      pure (.Let x (← readExpr n a) (← readExpr n b))
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

/-- The kinds that the free variables of `e`, of the kind `k`, have to have. An equality is of
bags when a side is an operation of bags, and of integers otherwise. -/
partial def kinds : Expr → Kind → List (Id × Kind)
  | .Variable x, k => [(x, k)]
  | .Plus a b, _ | .Minus a b, _ | .LessThan a b, _ | .GreaterThan a b, _ | .LessEquals a b, _
  | .GreaterEquals a b, _ => kinds a .int ++ kinds b .int
  | .BagAdd b e, _ => kinds b .bag ++ kinds e .elem
  | .BagUnion a b, _ | .BagDifference a b, _ | .BagIntersection a b, _ =>
    kinds a .bag ++ kinds b .bag
  | .MultiplicityInBag e b, _ => kinds e .elem ++ kinds b .bag
  | .Equals a b, _ =>
    let isBag : Expr → Bool
      | .FiniteBag _ _ | .BagAdd _ _ | .BagUnion _ _ | .BagDifference _ _
      | .BagIntersection _ _ => true
      | _ => false
    let k := if isBag a || isBag b then Kind.bag else Kind.int
    kinds a k ++ kinds b k
  | .Not a, _ => kinds a .bool
  | .And as, _ | .Or as, _ => as.flatMap (kinds · .bool)
  | .Implies a b, _ => kinds a .bool ++ kinds b .bool
  | .IfExpr c a b, k => kinds c .bool ++ kinds a k ++ kinds b k
  | .Let x a b, k =>
    let body := kinds b k
    kinds a ((body.lookup x).getD .int) ++ body.filter (·.1 != x)
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
partial def elemTy : Expr → Option Ty
  | .ADT _ [t] _ => some t
  | .FunctionInvocation _ [t] _ => some t
  | .Not a => elemTy a
  | .Equals a b | .Plus a b | .Minus a b | .LessThan a b | .GreaterThan a b | .LessEquals a b
  | .GreaterEquals a b | .Implies a b | .Let _ a b => (elemTy a).orElse fun _ => elemTy b
  | .And as | .Or as => as.findSome? elemTy
  | .IfExpr c a b => (elemTy c).orElse fun _ => (elemTy a).orElse fun _ => elemTy b
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
    | .ok p => if encodesCheck N Te Γ p.1 p.2 .bool then .ok p
      else .error "it is read, and its encoded term is not what the theorem expects"
  { names := N, vars := Γ, elem := Te, covered := checked.filterMap fun r => r.toOption,
    constraints := cs.length,
    first := checked.findSome? fun | .error why => some why | .ok _ => none }

theorem covers_check (certificate : Sexp) :
    ∀ p ∈ (covers certificate).covered,
      encodesCheck (covers certificate).names (covers certificate).elem (covers certificate).vars
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
    {Ps : Program} (hEs : KeyEq O Ps K E) {T0 : Ty}
    (hK : ∀ bs vs, O.params_have_types P
        (Env.Env (bind_types [(covers certificate).names.T] [T0] []) bs) vs
        [.Param (covers certificate).names.x (.TypeParameter (covers certificate).names.T)] =
          true ↔ ∃ v, vs = [v] ∧ K v)
    {env env' : Env} (hT : O.resolve_all (env_types env') [(covers certificate).elem] = [T0])
    (hΓ : ∀ x k, (covers certificate).vars.lookup x = some k → ∃ v v',
      lookup_var (env_vars env) x = .Ok v ∧ lookup_var (env_vars env') x = .Ok v' ∧
        Rel O P (covers certificate).names K E T0 k v v')
    (hsol : ∀ p ∈ (covers certificate).covered,
      ∃ n, eval O Ps n env p.1 = .Ok (.BoolV true)) :
    ∀ p ∈ (covers certificate).covered, ∃ n, eval O P n env' p.2 = .Ok (.BoolV true) :=
  input_encoded hO hN hP hS hQ h1x h2x h12 hE hEs hK hT hΓ (covers_check certificate) hsol

end Inox.Input
