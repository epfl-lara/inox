/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Semantics

/-!
The encoder of bags (`inox.solvers.theories.BagEncoder`), in the semantics of Inox.

The encoder makes a bag a value of the datatype

    Bag[T] = Node(op: BigInt, left: Bag[T], right: Bag[T]) | Elem(key: T, value: BigInt) | Leaf

and its operations constructors of it: the empty bag is `Leaf`, a union, a difference and an
intersection are `Node`s of the operations 0, 1 and another, and adding an element to a bag is
the union with an `Elem`. The multiplicity of an element is the function `get` of the encoder,
which the certificate checkers check the source definition of (`Inox.Encoders`).

This file states what `get` computes: `Mult` is the multiplicity of an element in a value of
that datatype, and `get_eval` shows that a call of `get` evaluates to it, in any program that
has the encoder's datatype and function. It then relates the datatype to the bags of the
semantics: `Enc` says that a value encodes a bag, each element having the same multiplicity in
both, and the constructors that the encoder makes of the operations of bags encode their
results (`enc_empty`, `enc_add`, `enc_union`, `enc_difference` and `enc_intersection`), so that
`get` evaluates to the multiplicities of the bag (`enc_get`).
-/

-- the cases of a proof share the lemmas that they simplify with
set_option linter.unusedSimpArgs false

namespace Inox.Bags

open Inox.Semantics

/-- The names of the encoder: of its datatype, of its function `get`, and of the parameters and
local variables of `get`. -/
structure Names where
  bag : Id
  node : Id
  elem : Id
  leaf : Id
  op : Id
  left : Id
  right : Id
  key : Id
  value : Id
  get : Id
  T : Id
  b : Id
  x : Id
  v1 : Id
  v2 : Id

/-- The names are those of distinct constructors and variables. -/
structure Names.Distinct (N : Names) : Prop where
  node_elem : N.node ≠ N.elem
  node_leaf : N.node ≠ N.leaf
  elem_leaf : N.elem ≠ N.leaf
  op_left : N.op ≠ N.left
  op_right : N.op ≠ N.right
  left_right : N.left ≠ N.right
  key_value : N.key ≠ N.value
  b_x : N.b ≠ N.x
  b_v1 : N.b ≠ N.v1
  b_v2 : N.b ≠ N.v2
  x_v1 : N.x ≠ N.v1
  x_v2 : N.x ≠ N.v2
  v1_v2 : N.v1 ≠ N.v2

/-- The body of `get`, as the encoder defines it. -/
def getBody (N : Names) : Expr :=
  let b := Expr.Variable N.b
  let x := Expr.Variable N.x
  let v1 := Expr.Variable N.v1
  let v2 := Expr.Variable N.v2
  let T := Ty.TypeParameter N.T
  .IfExpr (.IsConstructor b N.node)
    (.Let N.v1 (.FunctionInvocation N.get [T] [.ADTSelector b N.left, x])
      (.Let N.v2 (.FunctionInvocation N.get [T] [.ADTSelector b N.right, x])
        (.IfExpr (.Equals (.ADTSelector b N.op) (.IntegerLiteral 0))
          (.Plus v1 v2)
          (.IfExpr (.Equals (.ADTSelector b N.op) (.IntegerLiteral 1))
            (.IfExpr (.LessEquals v1 v2) (.IntegerLiteral 0) (.Minus v1 v2))
            (.IfExpr (.LessEquals v1 v2) v1 v2)))))
    (.IfExpr (.And [.IsConstructor b N.elem, .Equals (.ADTSelector b N.key) x])
      (.ADTSelector b N.value)
      (.IntegerLiteral 0))

/-- The program has the constructors of the encoder's datatype and its function `get`. -/
def HasBags (N : Names) : Program → Prop
  | .Program fs cs _ _ _ =>
    lookup_fun fs N.get = .Ok (.FunDef N.get [N.T] [N.b, N.x] (getBody N)) ∧
    lookup_ctor cs N.node = .Ok (.Constructor N.node N.bag
      [.Param N.op .IntegerType, .Param N.left (.ADTType N.bag [.TypeParameter N.T]),
       .Param N.right (.ADTType N.bag [.TypeParameter N.T])]) ∧
    lookup_ctor cs N.elem = .Ok (.Constructor N.elem N.bag
      [.Param N.key (.TypeParameter N.T), .Param N.value .IntegerType])

/-- The multiplicity that the node of the operation `op` gives to an element of the
multiplicities `m1` and `m2` in its operands. -/
def combine (op m1 m2 : Int) : Int :=
  if op = 0 then m1 + m2
  else if op = 1 then (if m1 ≤ m2 then 0 else m1 - m2)
  else (if m1 ≤ m2 then m1 else m2)

/-- `Mult O P N t x d m`: the element `x` has the multiplicity `m` in the value `t` of the
encoder's datatype, whose depth is `d`. An element of an `Elem` is compared with its key as the
program compares values. -/
inductive Mult (O : Oracle) (P : Program) (N : Names) :
    Value → Value → Nat → Int → Prop where
  | leaf (tps : List Ty) (x : Value) : Mult O P N (.ADTV N.leaf tps []) x 0 0
  | elem (tps : List Ty) (k x : Value) (n : Int) (same : Bool)
      (h : O.value_eq P k x = .Ok same) :
      Mult O P N (.ADTV N.elem tps [k, .IntV n]) x 0 (if same then n else 0)
  | node (tps : List Ty) (op : Int) (l r x : Value) (d1 d2 : Nat) (m1 m2 : Int)
      (h1 : Mult O P N l x d1 m1) (h2 : Mult O P N r x d2 m2) :
      Mult O P N (.ADTV N.node tps [.IntV op, l, r]) x (max d1 d2 + 1) (combine op m1 m2)

/-- A call of `get` on a value of the encoder's datatype and an element evaluates to the
multiplicity of the element, with more fuel than the depth of the value. -/
theorem get_eval {O : Oracle} (hO : O.Sound) {P : Program} {N : Names} (hN : N.Distinct)
    (hP : HasBags N P) {t x : Value} {d : Nat} {m : Int} (h : Mult O P N t x d m) :
    ∀ (fuel : Int) (tps : List Ty) (tenv : List TypeBinding), (d : Int) < fuel →
      call O P fuel N.get tps tenv [t, x] = .Ok (.IntV m) := by
  induction h with
  | leaf tps x =>
    intro fuel tps' tenv hf
    cases P with
    | Program fs cs ss is eq =>
    obtain ⟨hget, hnode, helem⟩ := hP
    rw [call, dite_eq_right_of_eq_false (eq_false (by omega))]
    simp only [hget, bind_all, getBody]
    simp [eval, eval_bool, eval_and, lookup_var, env_vars, hN.node_leaf, hN.elem_leaf]
  | elem tps k x n same hsame =>
    intro fuel tps' tenv hf
    cases P with
    | Program fs cs ss is eq =>
    obtain ⟨hget, hnode, helem⟩ := hP
    rw [call, dite_eq_right_of_eq_false (eq_false (by omega))]
    simp only [hget, bind_all, getBody]
    cases same <;>
      simp [eval, eval_bool, eval_and, lookup_var, env_vars, hN.node_elem, helem, select_field,
        hN.key_value, hN.b_x, hN.b_x.symm, hsame]
  | node tps op l r x d1 d2 m1 m2 _ _ ih1 ih2 =>
    intro fuel tps' tenv hf
    have hf1 : (d1 : Int) < fuel - 1 := by omega
    have hf2 : (d2 : Int) < fuel - 1 := by omega
    cases P with
    | Program fs cs ss is eq =>
    obtain ⟨hget, hnode, helem⟩ := hP
    rw [call, dite_eq_right_of_eq_false (eq_false (by omega))]
    simp only [hget, bind_all, getBody]
    have e1 := fun tenv' => ih1 (fuel - 1) [Ty.TypeParameter N.T] tenv' hf1
    have e2 := fun tenv' => ih2 (fuel - 1) [Ty.TypeParameter N.T] tenv' hf2
    by_cases h0 : op = 0
    · by_cases hle : m1 ≤ m2 <;>
        simp [eval, eval_bool, eval_list, lookup_var, env_vars, env_bind, env_types, hnode,
          select_field, hN.op_left, hN.op_right, hN.left_right, hN.b_x, hN.b_x.symm, hN.b_v1,
          hN.b_v1.symm, hN.b_v2, hN.b_v2.symm, hN.x_v1, hN.x_v1.symm, hN.x_v2, hN.x_v2.symm,
          hN.v1_v2, hN.v1_v2.symm, hN.op_left.symm, hN.op_right.symm, hN.left_right.symm, e1, e2,
          hO.value_eq, arith_plus, arith_minus, arith_le, arith_lt, combine, h0, hle]
    · by_cases h1 : op = 1 <;> by_cases hle : m1 ≤ m2 <;>
        simp [eval, eval_bool, eval_list, lookup_var, env_vars, env_bind, env_types, hnode,
          select_field, hN.op_left, hN.op_right, hN.left_right, hN.b_x, hN.b_x.symm, hN.b_v1,
          hN.b_v1.symm, hN.b_v2, hN.b_v2.symm, hN.x_v1, hN.x_v1.symm, hN.x_v2, hN.x_v2.symm,
          hN.v1_v2, hN.v1_v2.symm, hN.op_left.symm, hN.op_right.symm, hN.left_right.symm, e1, e2,
          hO.value_eq, arith_plus, arith_minus, arith_le, arith_lt, combine, h0, h1, hle]

/-- A call of `get` evaluates to nothing else than the multiplicity, whatever the fuel. -/
theorem get_eval_any {O : Oracle} (hO : O.Sound) {P : Program} {N : Names} (hN : N.Distinct)
    (hP : HasBags N P) {t x : Value} {d : Nat} {m : Int} (h : Mult O P N t x d m) :
    ∀ (fuel : Int) (tps : List Ty) (tenv : List TypeBinding),
      call O P fuel N.get tps tenv [t, x] = .Ok (.IntV m) ∨
        call O P fuel N.get tps tenv [t, x] = .OutOfFuel := by
  induction h with
  | leaf tps x =>
    intro fuel tps' tenv
    by_cases hf : fuel ≤ 0
    · right; rw [call, dite_eq_left_of_eq_true (eq_true hf)]
    · left; exact get_eval hO hN hP (Mult.leaf tps x) fuel tps' tenv (by simp; omega)
  | elem tps k x n same hsame =>
    intro fuel tps' tenv
    by_cases hf : fuel ≤ 0
    · right; rw [call, dite_eq_left_of_eq_true (eq_true hf)]
    · left; exact get_eval hO hN hP (Mult.elem tps k x n same hsame) fuel tps' tenv
        (by simp; omega)
  | node tps op l r x d1 d2 m1 m2 _ _ ih1 ih2 =>
    intro fuel tps' tenv
    by_cases hf : fuel ≤ 0
    · right; rw [call, dite_eq_left_of_eq_true (eq_true hf)]
    cases P with
    | Program fs cs ss is eq =>
    obtain ⟨hget, hnode, helem⟩ := hP
    rw [call, dite_eq_right_of_eq_false (eq_false hf)]
    simp only [hget, bind_all, getBody]
    rcases ih1 (fuel - 1) [Ty.TypeParameter N.T] (bind_types [N.T] tps' tenv) with e1 | e1 <;>
      rcases ih2 (fuel - 1) [Ty.TypeParameter N.T] (bind_types [N.T] tps' tenv) with e2 | e2 <;>
      by_cases h0 : op = 0 <;> by_cases h1 : op = 1 <;> by_cases hle : m1 ≤ m2 <;>
        simp [eval, eval_bool, eval_list, lookup_var, env_vars, env_bind, env_types, hnode,
          select_field, hN.op_left, hN.op_right, hN.left_right, hN.b_x, hN.b_x.symm, hN.b_v1,
          hN.b_v1.symm, hN.b_v2, hN.b_v2.symm, hN.x_v1, hN.x_v1.symm, hN.x_v2, hN.x_v2.symm,
          hN.v1_v2, hN.v1_v2.symm, hN.op_left.symm, hN.op_right.symm, hN.left_right.symm, e1, e2,
          hO.value_eq, arith_plus, arith_minus, arith_le, arith_lt, combine, h0, h1, hle]

/-! ## The equality of the encoder's datatype -/

/-- The body of the encoder's `equals` on the parameters `b1` and `b2`. -/
def equalsBody (N : Names) (b1 b2 : Id) : Expr :=
  .Forall [.Param N.x (.TypeParameter N.T)]
    (.Equals (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b1, .Variable N.x])
      (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b2, .Variable N.x]))

/-- The program defines `equals` as the encoder does. -/
def HasEquals (N : Names) (eq b1 b2 : Id) : Program → Prop
  | .Program fs _ _ _ _ =>
    lookup_fun fs eq = .Ok (.FunDef eq [N.T] [b1, b2] (equalsBody N b1 b2))

/-- The instance of the body of `equals` on an element compares its multiplicities. -/
theorem equals_instance {O : Oracle} (hO : O.Sound) {P : Program} {N : Names} (hN : N.Distinct)
    (hP : HasBags N P) {b1 b2 : Id} (h1x : b1 ≠ N.x) (h2x : b2 ≠ N.x) (h12 : b1 ≠ b2)
    {a b w : Value} {d1 d2 : Nat} {m1 m2 : Int} (ha : Mult O P N a w d1 m1)
    (hb : Mult O P N b w d2 m2) (fuel : Int) (tys : List TypeBinding) :
    (instance_ O P fuel (Env.Env tys [.Binding b1 a, .Binding b2 b])
        [.Param N.x (.TypeParameter N.T)] [w]
        (.Equals (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b1, .Variable N.x])
          (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b2, .Variable N.x]))
        = .Ok (.BoolV (decide (m1 = m2))) ∨
      instance_ O P fuel (Env.Env tys [.Binding b1 a, .Binding b2 b])
        [.Param N.x (.TypeParameter N.T)] [w]
        (.Equals (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b1, .Variable N.x])
          (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b2, .Variable N.x]))
        = .OutOfFuel) ∧
    ((d1 : Int) < fuel → (d2 : Int) < fuel →
      instance_ O P fuel (Env.Env tys [.Binding b1 a, .Binding b2 b])
        [.Param N.x (.TypeParameter N.T)] [w]
        (.Equals (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b1, .Variable N.x])
          (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b2, .Variable N.x]))
        = .Ok (.BoolV (decide (m1 = m2)))) := by
  constructor
  · rcases get_eval_any hO hN hP ha fuel [Ty.TypeParameter N.T] tys with e1 | e1 <;>
      rcases get_eval_any hO hN hP hb fuel [Ty.TypeParameter N.T] tys with e2 | e2 <;>
      simp [instance_, param_ids, bind_all, append_env, eval, eval_list, lookup_var, env_vars,
        env_types, h1x, h2x, h12, h1x.symm, h2x.symm, h12.symm, e1, e2, hO.value_eq]
  · intro f1 f2
    have e1 := get_eval hO hN hP ha fuel [Ty.TypeParameter N.T] tys f1
    have e2 := get_eval hO hN hP hb fuel [Ty.TypeParameter N.T] tys f2
    simp [instance_, param_ids, bind_all, append_env, eval, eval_list, lookup_var, env_vars,
      env_types, h1x, h2x, h12, h1x.symm, h2x.symm, h12.symm, e1, e2, hO.value_eq]

open Classical in
/-- The encoder's `equals` decides whether two values of its datatype give the same
multiplicity to every element of `K`, the values of the type of the elements. -/
theorem equals_eval {O : Oracle} (hO : O.Sound) {P : Program} {N : Names} (hN : N.Distinct)
    (hP : HasBags N P) {eq b1 b2 : Id} (hE : HasEquals N eq b1 b2 P) (h1x : b1 ≠ N.x)
    (h2x : b2 ≠ N.x) (h12 : b1 ≠ b2) {a b : Value} {tps : List Ty} {K : Value → Prop}
    (hK : ∀ vs, O.params_have_types P
        (Env.Env (bind_types [N.T] tps []) [.Binding b1 a, .Binding b2 b]) vs
        [.Param N.x (.TypeParameter N.T)] = true ↔ ∃ v, vs = [v] ∧ K v)
    {f g : Value → Int} {d1 d2 : Nat} (ha : ∀ w, K w → Mult O P N a w d1 (f w))
    (hb : ∀ w, K w → Mult O P N b w d2 (g w)) :
    (∀ fuel : Int,
      call O P fuel eq tps [] [a, b] = .Ok (.BoolV (decide (∀ w, K w → f w = g w))) ∨
        call O P fuel eq tps [] [a, b] = .OutOfFuel) ∧
    call O P (max d1 d2 + 2) eq tps [] [a, b] =
      .Ok (.BoolV (decide (∀ w, K w → f w = g w))) := by
  have key : ∀ fuel : Int,
      (O.forall_result P fuel (Env.Env (bind_types [N.T] tps []) [.Binding b1 a, .Binding b2 b])
          [.Param N.x (.TypeParameter N.T)]
          (.Equals
            (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b1, .Variable N.x])
            (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b2, .Variable N.x]))
          = .Ok (.BoolV (decide (∀ w, K w → f w = g w))) ∨
        O.forall_result P fuel (Env.Env (bind_types [N.T] tps []) [.Binding b1 a, .Binding b2 b])
          [.Param N.x (.TypeParameter N.T)]
          (.Equals
            (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b1, .Variable N.x])
            (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b2, .Variable N.x]))
          = .OutOfFuel) ∧
      ((d1 : Int) < fuel → (d2 : Int) < fuel →
        O.forall_result P fuel (Env.Env (bind_types [N.T] tps []) [.Binding b1 a, .Binding b2 b])
          [.Param N.x (.TypeParameter N.T)]
          (.Equals
            (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b1, .Variable N.x])
            (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b2, .Variable N.x]))
          = .Ok (.BoolV (decide (∀ w, K w → f w = g w)))) := by
    intro fuel
    have hI := fun w (hw : K w) => equals_instance hO hN hP h1x h2x h12 (ha w hw) (hb w hw) fuel
      (bind_types [N.T] tps [])
    rw [hO.forall_result]
    by_cases c1 : ∃ vs, (O.params_have_types P
        (Env.Env (bind_types [N.T] tps []) [.Binding b1 a, .Binding b2 b]) vs
        [.Param N.x (.TypeParameter N.T)] && decide (instance_ O P fuel
          (Env.Env (bind_types [N.T] tps []) [.Binding b1 a, .Binding b2 b])
          [.Param N.x (.TypeParameter N.T)] vs
          (.Equals
            (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b1, .Variable N.x])
            (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b2, .Variable N.x]))
          = .Ok (.BoolV false))) = true
    · rw [dite_eq_left_of_eq_true (eq_true (decide_eq_true c1))]
      obtain ⟨vs, h⟩ := c1
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨v, rfl, hv⟩ := (hK vs).1 h.1
      have hne : ¬ (∀ w, K w → f w = g w) := by
        intro hall
        rcases (hI v hv).1 with e | e
        · rw [e] at h; simp [hall v hv] at h
        · rw [e] at h; simp at h
      simp [hne]
    · rw [dite_eq_right_of_eq_false (eq_false (fun h => c1 (of_decide_eq_true h)))]
      by_cases c2 : ∃ vs, (O.params_have_types P
          (Env.Env (bind_types [N.T] tps []) [.Binding b1 a, .Binding b2 b]) vs
          [.Param N.x (.TypeParameter N.T)] && decide (instance_ O P fuel
            (Env.Env (bind_types [N.T] tps []) [.Binding b1 a, .Binding b2 b])
            [.Param N.x (.TypeParameter N.T)] vs
            (.Equals
              (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b1, .Variable N.x])
              (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b2, .Variable N.x]))
            = .OutOfFuel)) = true
      · rw [dite_eq_left_of_eq_true (eq_true (decide_eq_true c2))]
        refine ⟨Or.inr rfl, fun hf1 hf2 => ?_⟩
        obtain ⟨vs, h⟩ := c2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨v, rfl, hv⟩ := (hK vs).1 h.1
        rw [(hI v hv).2 hf1 hf2] at h
        simp at h
      · rw [dite_eq_right_of_eq_false (eq_false (fun h => c2 (of_decide_eq_true h)))]
        have hall : ∀ w, K w → f w = g w := by
          intro w hw
          have hw' := (hK [w]).2 ⟨w, rfl, hw⟩
          rcases (hI w hw).1 with e | e
          · apply Classical.byContradiction
            intro hne
            exact c1 ⟨[w], by simp [hw', e, hne]⟩
          · exact absurd ⟨[w], by simp [hw', e]⟩ c2
        have c3 : ∀ vs, (!(O.params_have_types P
            (Env.Env (bind_types [N.T] tps []) [.Binding b1 a, .Binding b2 b]) vs
            [.Param N.x (.TypeParameter N.T)]) || decide (instance_ O P fuel
              (Env.Env (bind_types [N.T] tps []) [.Binding b1 a, .Binding b2 b])
              [.Param N.x (.TypeParameter N.T)] vs
              (.Equals
                (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b1, .Variable N.x])
                (.FunctionInvocation N.get [.TypeParameter N.T] [.Variable b2, .Variable N.x]))
              = .Ok (.BoolV true))) = true := by
          intro vs
          by_cases ht : O.params_have_types P
              (Env.Env (bind_types [N.T] tps []) [.Binding b1 a, .Binding b2 b]) vs
              [.Param N.x (.TypeParameter N.T)] = true
          · obtain ⟨v, rfl, hv⟩ := (hK vs).1 ht
            rcases (hI v hv).1 with e | e
            · simp [e, hall v hv]
            · exact absurd ⟨[v], by simp [ht, e]⟩ c2
          · simp [ht]
        rw [dite_eq_left_of_eq_true (eq_true (decide_eq_true c3)), decide_eq_true hall]
        exact ⟨Or.inl rfl, fun _ _ => rfl⟩
  cases P with
  | Program fs cs ss is eqs =>
  have hE' : lookup_fun fs eq = .Ok (.FunDef eq [N.T] [b1, b2] (equalsBody N b1 b2)) := hE
  constructor
  · intro fuel
    by_cases hf : fuel ≤ 0
    · right; rw [call, dite_eq_left_of_eq_true (eq_true hf)]
    · rw [call, dite_eq_right_of_eq_false (eq_false hf)]
      simp only [hE', bind_all, equalsBody, eval]
      exact (key (fuel - 1)).1
  · rw [call, dite_eq_right_of_eq_false (eq_false (by omega))]
    simp only [hE', bind_all, equalsBody, eval]
    exact (key _).2 (by omega) (by omega)

open Classical in
/-- The equality of the encoder's datatype is the equality of multiplicities. -/
theorem adt_equal_eq {O : Oracle} (hO : O.Sound) {P : Program} {N : Names} (hN : N.Distinct)
    (hP : HasBags N P) {eq b1 b2 : Id} (hE : HasEquals N eq b1 b2 P) (h1x : b1 ≠ N.x)
    (h2x : b2 ≠ N.x) (h12 : b1 ≠ b2) {a b : Value} {tps : List Ty} {K : Value → Prop}
    (hK : ∀ vs, O.params_have_types P
        (Env.Env (bind_types [N.T] tps []) [.Binding b1 a, .Binding b2 b]) vs
        [.Param N.x (.TypeParameter N.T)] = true ↔ ∃ v, vs = [v] ∧ K v)
    {f g : Value → Int} {d1 d2 : Nat} (ha : ∀ w, K w → Mult O P N a w d1 (f w))
    (hb : ∀ w, K w → Mult O P N b w d2 (g w)) :
    O.adt_equal P eq tps a b = .Ok (decide (∀ w, K w → f w = g w)) := by
  obtain ⟨hany, hd⟩ := equals_eval hO hN hP hE h1x h2x h12 hK ha hb
  rw [hO.adt_equal]
  by_cases hall : ∀ w, K w → f w = g w
  · rw [decide_eq_true hall] at hany hd ⊢
    rw [dite_eq_left_of_eq_true (eq_true (decide_eq_true ⟨_, decide_eq_true hd⟩))]
  · rw [decide_eq_false hall] at hany hd ⊢
    have h1 : ¬ ∃ fuel : Int,
        decide (call O P fuel eq tps [] [a, b] = .Ok (.BoolV true)) = true := by
      rintro ⟨fuel, h⟩
      have h := of_decide_eq_true h
      rcases hany fuel with e | e <;> rw [e] at h <;> simp at h
    rw [dite_eq_right_of_eq_false (eq_false (fun h => h1 (of_decide_eq_true h))),
      dite_eq_left_of_eq_true (eq_true (decide_eq_true ⟨_, decide_eq_true hd⟩))]

/-! ## The construction of the encoder's values -/

/-- The body of the invariant of the encoder's datatype on the parameter `bi`. -/
def invBody (N : Names) (bi : Id) : Expr :=
  .IfExpr (.IsConstructor (.Variable bi) N.elem)
    (.GreaterEquals (.ADTSelector (.Variable bi) N.value) (.IntegerLiteral 0))
    (.BooleanLiteral true)

/-- The program defines the encoder's sort, with its invariant `inv` and its equality `eq`,
and the constructor `Leaf`. -/
def HasSort (N : Names) (inv bi eq : Id) : Program → Prop
  | .Program fs cs ss _ _ =>
    lookup_fun fs inv = .Ok (.FunDef inv [N.T] [bi] (invBody N bi)) ∧
    lookup_sort ss N.bag = .Ok (.Sort N.bag [N.T] (some inv) (some eq)) ∧
    lookup_ctor cs N.leaf = .Ok (.Constructor N.leaf N.bag [])

section Construct
variable {O : Oracle} {P : Program} {N : Names} {inv bi eq : Id}

theorem construct_leaf (hN : N.Distinct) (hS : HasSort N inv bi eq P) {fuel : Int}
    (hf : 0 < fuel) (env : Env) (tps : List Ty) :
    construct O P fuel env N.leaf tps [] =
      .Ok (.ADTV N.leaf (O.resolve_all (env_types env) tps) []) := by
  cases P with
  | Program fs cs ss is eqs =>
  obtain ⟨hinv, hsort, hleaf⟩ := hS
  rw [construct]
  simp only [hleaf, hsort]
  rw [call, dite_eq_right_of_eq_false (eq_false (by omega))]
  simp only [hinv, bind_all, invBody]
  simp [eval, eval_bool, lookup_var, env_vars, hN.elem_leaf]

theorem construct_node (hN : N.Distinct) (hP : HasBags N P) (hS : HasSort N inv bi eq P)
    {fuel : Int} (hf : 0 < fuel) (env : Env) (tps : List Ty) (vs : List Value) :
    construct O P fuel env N.node tps vs =
      .Ok (.ADTV N.node (O.resolve_all (env_types env) tps) vs) := by
  cases P with
  | Program fs cs ss is eqs =>
  obtain ⟨hinv, hsort, hleaf⟩ := hS
  obtain ⟨hget, hnode, helem⟩ := hP
  rw [construct]
  simp only [hnode, hsort]
  rw [call, dite_eq_right_of_eq_false (eq_false (by omega))]
  simp only [hinv, bind_all, invBody]
  simp [eval, eval_bool, lookup_var, env_vars, hN.node_elem, hN.node_elem.symm]

theorem construct_elem (hN : N.Distinct) (hP : HasBags N P) (hS : HasSort N inv bi eq P)
    {fuel : Int} (hf : 0 < fuel) (env : Env) (tps : List Ty) (k : Value) {n : Int}
    (hn : 0 ≤ n) :
    construct O P fuel env N.elem tps [k, .IntV n] =
      .Ok (.ADTV N.elem (O.resolve_all (env_types env) tps) [k, .IntV n]) := by
  cases P with
  | Program fs cs ss is eqs =>
  obtain ⟨hinv, hsort, hleaf⟩ := hS
  obtain ⟨hget, hnode, helem⟩ := hP
  rw [construct]
  simp only [helem, hsort]
  rw [call, dite_eq_right_of_eq_false (eq_false (by omega))]
  simp only [hinv, bind_all, invBody]
  simp [eval, eval_bool, lookup_var, env_vars, helem, select_field, hN.key_value, arith_le,
    arith_lt, Int.not_lt.2 hn]

end Construct

/-! ## The bags of the semantics

A bag of the semantics is a list of entries, which its operations build without two equal
elements and with positive multiplicities. They compare elements with the equality of the
program, which is given by an oracle: the lemmas below are about elements `K` on which it is an
equivalence `E` that never gets stuck. Under it, each operation is a function of the entries,
and the multiplicities of its result are those that the encoder's `get` computes. -/

/-- The equality of the program on the elements `K`: it decides the equivalence `E`. -/
structure KeyEq (O : Oracle) (P : Program) (K : Value → Prop) (E : Value → Value → Bool) :
    Prop where
  eq : ∀ a b, K a → K b → O.value_eq P a b = .Ok (E a b)
  refl : ∀ a, K a → E a a = true
  symm : ∀ a b, K a → K b → E a b = true → E b a = true
  trans : ∀ a b c, K a → K b → K c → E a b = true → E b c = true → E a c = true

section Entries
variable (E : Value → Value → Bool)

/-- The multiplicity of `v` in the entries. -/
def mult : List BagEntry → Value → Int
  | [], _ => 0
  | .BagEntry x n :: rest, v => if E x v then n else mult rest v

/-- The entries without that of `v`. -/
def remove : List BagEntry → Value → List BagEntry
  | [], _ => []
  | .BagEntry x n :: rest, v => if E x v then rest else .BagEntry x n :: remove rest v

/-- The entries where `v` has the multiplicity `n`, when it is positive, and none otherwise. -/
def set (xs : List BagEntry) (v : Value) (n : Int) : List BagEntry :=
  if 0 < n then .BagEntry v n :: remove E xs v else remove E xs v

/-- The entries of the sum of two bags. -/
def addAll : List BagEntry → List BagEntry → List BagEntry
  | acc, [] => acc
  | acc, .BagEntry x n :: rest => addAll (set E acc x (mult E acc x + n)) rest

/-- The entries that `bag-merge` adds to `acc`: those of `xs`, each with its multiplicity
combined with that in `ys`. -/
def merge (op : BagOp) : List BagEntry → List BagEntry → List BagEntry → List BagEntry
  | acc, [], _ => acc
  | acc, .BagEntry x n :: rest, ys =>
    merge op (set E acc x (bag_combine op n (mult E ys x))) rest ys

/-- Entries as the operations build them: elements of `K`, no two of which are equal, with
positive multiplicities. -/
def Canon (K : Value → Prop) : List BagEntry → Prop
  | [] => True
  | .BagEntry x n :: rest => K x ∧ 0 < n ∧ mult E rest x = 0 ∧ Canon K rest

variable {E} {O : Oracle} {P : Program} {K : Value → Prop}

theorem keyEq_iff (hE : KeyEq O P K E) {a b c : Value} (ha : K a) (hb : K b) (hc : K c)
    (h : E a b = true) : E c a = E c b := by
  cases h1 : E c a <;> cases h2 : E c b <;> try rfl
  · exact absurd (hE.trans c b a hc hb ha h2 (hE.symm a b ha hb h)) (by simp [h1])
  · exact absurd (hE.trans c a b hc ha hb h1 h) (by simp [h2])

theorem mult_congr (hE : KeyEq O P K E) : ∀ {xs : List BagEntry}, Canon E K xs →
    ∀ {v w : Value}, K v → K w → E v w = true → mult E xs v = mult E xs w
  | [], _, _, _, _, _, _ => rfl
  | .BagEntry x n :: rest, ⟨hx, _, _, hrest⟩, v, w, hv, hw, h => by
    simp only [mult, keyEq_iff hE hv hw hx h, mult_congr hE hrest hv hw h]

theorem mult_nonneg : ∀ {xs : List BagEntry}, Canon E K xs → ∀ v, 0 ≤ mult E xs v
  | [], _, _ => Int.le_refl 0
  | .BagEntry x n :: rest, ⟨_, hn, _, hrest⟩, v => by
    simp only [mult]
    split
    · omega
    · exact mult_nonneg hrest v

theorem mult_remove (hE : KeyEq O P K E) : ∀ {xs : List BagEntry}, Canon E K xs →
    ∀ {v w : Value}, K v → K w →
      mult E (remove E xs v) w = if E v w then 0 else mult E xs w
  | [], _, _, _, _, _ => by simp [remove, mult]
  | .BagEntry x n :: rest, ⟨hx, _, hfresh, hrest⟩, v, w, hv, hw => by
    have ih := mult_remove hE hrest hv hw
    simp only [remove]
    by_cases hxv : E x v = true
    · rw [if_pos hxv]
      by_cases hvw : E v w = true
      · rw [if_pos hvw, ← mult_congr hE hrest hx hw (hE.trans x v w hx hv hw hxv hvw), hfresh]
      · rw [if_neg hvw]
        have : ¬ E x w = true := fun h =>
          hvw (hE.trans v x w hv hx hw (hE.symm x v hx hv hxv) h)
        simp only [mult, if_neg this]
    · rw [if_neg hxv]
      simp only [mult, ih]
      by_cases hvw : E v w = true
      · have : ¬ E x w = true := fun h =>
          hxv (hE.trans x w v hx hw hv h (hE.symm v w hv hw hvw))
        rw [if_neg this, if_pos hvw, if_pos hvw]
      · rw [if_neg hvw, if_neg hvw]

theorem canon_remove (hE : KeyEq O P K E) : ∀ {xs : List BagEntry}, Canon E K xs →
    ∀ {v : Value}, K v → Canon E K (remove E xs v)
  | [], _, _, _ => trivial
  | .BagEntry x n :: rest, ⟨hx, hn, hfresh, hrest⟩, v, hv => by
    simp only [remove]
    split
    · exact hrest
    · refine ⟨hx, hn, ?_, canon_remove hE hrest hv⟩
      rw [mult_remove hE hrest hv hx, hfresh]
      split <;> rfl

theorem canon_set (hE : KeyEq O P K E) {xs : List BagEntry} (hxs : Canon E K xs) {v : Value}
    (hv : K v) (n : Int) : Canon E K (set E xs v n) := by
  simp only [set]
  split
  · next hn =>
    refine ⟨hv, hn, ?_, canon_remove hE hxs hv⟩
    rw [mult_remove hE hxs hv hv, if_pos (hE.refl v hv)]
  · exact canon_remove hE hxs hv

theorem mult_set (hE : KeyEq O P K E) {xs : List BagEntry} (hxs : Canon E K xs) {v w : Value}
    (hv : K v) (hw : K w) (n : Int) :
    mult E (set E xs v n) w = if E v w then (if 0 < n then n else 0) else mult E xs w := by
  simp only [set]
  by_cases hn : 0 < n
  · rw [if_pos hn, if_pos hn]
    simp only [mult, mult_remove hE hxs hv hw]
    split <;> rfl
  · rw [if_neg hn, if_neg hn, mult_remove hE hxs hv hw]

theorem canon_addAll (hE : KeyEq O P K E) : ∀ {xs acc : List BagEntry}, Canon E K acc →
    Canon E K xs → Canon E K (addAll E acc xs)
  | [], _, hacc, _ => hacc
  | .BagEntry x n :: rest, acc, hacc, ⟨hx, _, _, hrest⟩ =>
    canon_addAll hE (acc := set E acc x (mult E acc x + n)) (canon_set hE hacc hx _) hrest

theorem mult_addAll (hE : KeyEq O P K E) : ∀ {xs acc : List BagEntry}, Canon E K acc →
    Canon E K xs → ∀ {w : Value}, K w →
      mult E (addAll E acc xs) w = mult E acc w + mult E xs w
  | [], _, _, _, _, _ => by simp [addAll, mult]
  | .BagEntry x n :: rest, acc, hacc, ⟨hx, hn, hfresh, hrest⟩, w, hw => by
    simp only [addAll]
    rw [mult_addAll hE (canon_set hE hacc hx _) hrest hw, mult_set hE hacc hx hw]
    have h0 := mult_nonneg hacc x
    by_cases hxw : E x w = true
    · simp only [mult, if_pos hxw]
      rw [if_pos (by omega), ← mult_congr hE hrest hx hw hxw, hfresh,
        mult_congr hE hacc hx hw hxw]
      omega
    · simp only [mult, if_neg hxw]

theorem canon_merge (hE : KeyEq O P K E) (op : BagOp) (ys : List BagEntry) :
    ∀ {xs acc : List BagEntry}, Canon E K acc → Canon E K xs →
      Canon E K (merge E op acc xs ys)
  | [], _, hacc, _ => hacc
  | .BagEntry x n :: rest, acc, hacc, ⟨hx, _, _, hrest⟩ =>
    canon_merge hE op ys (acc := set E acc x (bag_combine op n (mult E ys x)))
      (canon_set hE hacc hx _) hrest

theorem mult_merge (hE : KeyEq O P K E) (op : BagOp) {ys : List BagEntry}
    (hys : Canon E K ys) : ∀ {xs acc : List BagEntry}, Canon E K acc → Canon E K xs →
      ∀ {w : Value}, K w → mult E (merge E op acc xs ys) w =
        if 0 < mult E xs w then
          (if 0 < bag_combine op (mult E xs w) (mult E ys w) then
            bag_combine op (mult E xs w) (mult E ys w) else 0)
        else mult E acc w
  | [], _, _, _, _, _ => by simp [merge, mult]
  | .BagEntry x n :: rest, acc, hacc, ⟨hx, hn, hfresh, hrest⟩, w, hw => by
    simp only [merge]
    rw [mult_merge hE op hys (canon_set hE hacc hx _) hrest hw, mult_set hE hacc hx hw]
    by_cases hxw : E x w = true
    · have h0 : mult E rest w = 0 := by rw [← mult_congr hE hrest hx hw hxw, hfresh]
      simp only [mult, if_pos hxw, h0, Int.lt_irrefl, if_false, if_pos hn,
        mult_congr hE hys hx hw hxw]
    · simp only [mult, if_neg hxw]

/-- The operations of the semantics compute these functions of the entries. -/
theorem bag_get_eq (hO : O.Sound) (hE : KeyEq O P K E) : ∀ {xs : List BagEntry},
    Canon E K xs → ∀ {v : Value}, K v → O.bag_get P xs v = .Ok (mult E xs v)
  | [], _, _, _ => by rw [hO.bag_get]; rfl
  | .BagEntry x n :: rest, ⟨hx, _, _, hrest⟩, v, hv => by
    rw [hO.bag_get]
    simp only [hE.eq x v hx hv, mult]
    split
    · rfl
    · exact bag_get_eq hO hE hrest hv

theorem bag_remove_eq (hE : KeyEq O P K E) : ∀ {xs : List BagEntry},
    Canon E K xs → ∀ {v : Value}, K v → bag_remove O P xs v = .Ok (remove E xs v)
  | [], _, _, _ => by rw [bag_remove]; rfl
  | .BagEntry x n :: rest, ⟨hx, _, _, hrest⟩, v, hv => by
    rw [bag_remove]
    simp only [hE.eq x v hx hv, remove]
    split
    · rfl
    · rw [bag_remove_eq hE hrest hv]

theorem bag_set_eq (hE : KeyEq O P K E) {xs : List BagEntry} (hxs : Canon E K xs) {v : Value}
    (hv : K v) (n : Int) : bag_set O P xs v n = .Ok (set E xs v n) := by
  rw [bag_set, bag_remove_eq hE hxs hv]
  simp only [set]
  split <;> rfl

theorem bag_add_all_eq (hO : O.Sound) (hE : KeyEq O P K E) : ∀ {xs acc : List BagEntry},
    Canon E K acc → Canon E K xs → bag_add_all O P acc xs = .Ok (addAll E acc xs)
  | [], _, _, _ => by rw [bag_add_all]; rfl
  | .BagEntry x n :: rest, acc, hacc, ⟨hx, _, _, hrest⟩ => by
    rw [bag_add_all]
    simp only [bag_get_eq hO hE hacc hx, bag_set_eq hE hacc hx, addAll]
    exact bag_add_all_eq hO hE (canon_set hE hacc hx _) hrest

theorem bag_merge_eq (hO : O.Sound) (hE : KeyEq O P K E) (op : BagOp) {ys : List BagEntry}
    (hys : Canon E K ys) : ∀ {xs acc : List BagEntry}, Canon E K acc → Canon E K xs →
      bag_merge O P op acc xs ys = .Ok (merge E op acc xs ys)
  | [], _, _, _ => by rw [bag_merge]; rfl
  | .BagEntry x n :: rest, acc, hacc, ⟨hx, _, _, hrest⟩ => by
    rw [bag_merge]
    simp only [bag_get_eq hO hE hys hx, bag_set_eq hE hacc hx, merge]
    exact bag_merge_eq hO hE op hys (canon_set hE hacc hx _) hrest

/-! ### The equality of bags -/

/-- Each entry of `xs` has its multiplicity in `ys`. -/
def sub (E : Value → Value → Bool) : List BagEntry → List BagEntry → Bool
  | [], _ => true
  | .BagEntry x n :: rest, ys => decide (n = mult E ys x) && sub E rest ys

theorem sub_bag_eq (hO : O.Sound) (hE : KeyEq O P K E) {ys : List BagEntry}
    (hys : Canon E K ys) : ∀ {xs : List BagEntry}, Canon E K xs →
    O.sub_bag P xs ys = .Ok (sub E xs ys)
  | [], _ => by rw [hO.sub_bag]; rfl
  | .BagEntry x n :: rest, ⟨hx, _, _, hrest⟩ => by
    rw [hO.sub_bag]
    simp only [bag_get_eq hO hE hys hx, sub]
    by_cases h : n = mult E ys x
    · simp [h, sub_bag_eq hO hE hys hrest]
    · simp [h]

theorem sub_iff {ys : List BagEntry} : ∀ {xs : List BagEntry},
    sub E xs ys = true ↔ ∀ x n, BagEntry.BagEntry x n ∈ xs → n = mult E ys x
  | [] => by simp [sub]
  | .BagEntry x n :: rest => by
    simp only [sub, Bool.and_eq_true, decide_eq_true_eq, sub_iff (xs := rest), List.mem_cons]
    constructor
    · rintro ⟨h1, h2⟩ y m (h | h)
      · cases h; exact h1
      · exact h2 y m h
    · exact fun h => ⟨h x n (Or.inl rfl), fun y m hm => h y m (Or.inr hm)⟩

theorem canon_key : ∀ {xs : List BagEntry}, Canon E K xs →
    ∀ {x : Value} {n : Int}, BagEntry.BagEntry x n ∈ xs → K x
  | .BagEntry y m :: rest, ⟨hy, _, _, hrest⟩, x, n, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h; exact hy
    · exact canon_key hrest h

theorem canon_pos : ∀ {xs : List BagEntry}, Canon E K xs →
    ∀ {x : Value} {n : Int}, BagEntry.BagEntry x n ∈ xs → 0 < n
  | .BagEntry y m :: rest, ⟨_, hm, _, hrest⟩, x, n, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h; exact hm
    · exact canon_pos hrest h

/-- An element with a multiplicity has an entry. -/
theorem mult_entry : ∀ {xs : List BagEntry} {w : Value}, mult E xs w ≠ 0 →
    ∃ x n, BagEntry.BagEntry x n ∈ xs ∧ E x w = true ∧ n = mult E xs w
  | [], _, h => absurd rfl h
  | .BagEntry y m :: rest, w, h => by
    by_cases c : E y w = true
    · exact ⟨y, m, List.mem_cons_self, c, by simp [mult, c]⟩
    · have hm : mult E (.BagEntry y m :: rest) w = mult E rest w := by simp [mult, c]
      obtain ⟨x, n, hmem, hx, hn⟩ := mult_entry (xs := rest) (w := w) (hm ▸ h)
      exact ⟨x, n, List.mem_cons_of_mem _ hmem, hx, hm ▸ hn⟩

/-- The key of an entry has the multiplicity of the entry. -/
theorem mult_mem (hE : KeyEq O P K E) : ∀ {xs : List BagEntry}, Canon E K xs →
    ∀ {x : Value} {n : Int}, BagEntry.BagEntry x n ∈ xs → mult E xs x = n
  | .BagEntry y m :: rest, ⟨hy, hm, h0, hrest⟩, x, n, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h; simp [mult, hE.refl _ hy]
    · have hx := canon_key hrest h
      have ih := mult_mem hE hrest h
      by_cases c : E y x = true
      · have := mult_congr hE hrest hy hx c
        have hc := canon_pos hrest h
        omega
      · simp [mult, c, ih]

open Classical in
/-- Two bags are equal when every element has the same multiplicity in both. -/
theorem bag_value_eq (hO : O.Sound) (hE : KeyEq O P K E) {xs ys : List BagEntry}
    (hxs : Canon E K xs) (hys : Canon E K ys) (t u : Ty) :
    O.value_eq P (.BagV t xs) (.BagV u ys) =
      .Ok (decide (∀ w, K w → mult E xs w = mult E ys w)) := by
  have half : ∀ {xs ys : List BagEntry}, Canon E K xs → Canon E K ys →
      sub E xs ys = true → ∀ w, K w → mult E xs w ≠ 0 → mult E xs w = mult E ys w := by
    intro xs ys hxs hys hsub w hw hne
    obtain ⟨x, n, hmem, hx, hn⟩ := mult_entry hne
    rw [← hn, sub_iff.1 hsub x n hmem]
    exact mult_congr hE hys (canon_key hxs hmem) hw hx
  rw [hO.value_eq]
  simp only [sub_bag_eq hO hE hys hxs, sub_bag_eq hO hE hxs hys]
  by_cases h : ∀ w, K w → mult E xs w = mult E ys w
  · have h1 : sub E xs ys = true :=
      sub_iff.2 fun x n hmem => by
        rw [← h x (canon_key hxs hmem), mult_mem hE hxs hmem]
    have h2 : sub E ys xs = true :=
      sub_iff.2 fun x n hmem => by
        rw [h x (canon_key hys hmem), mult_mem hE hys hmem]
    simp [h1, h2, decide_eq_true h]
  · rw [decide_eq_false h]
    by_cases h1 : sub E xs ys = true
    · by_cases h2 : sub E ys xs = true
      · exfalso
        apply h
        intro w hw
        by_cases c1 : mult E xs w = 0
        · by_cases c2 : mult E ys w = 0
          · omega
          · exact (half hys hxs h2 w hw c2).symm
        · exact half hxs hys h1 w hw c1
      · simp [h1, h2]
    · simp [h1]

end Entries

/-! ## The encoding of a bag -/

/-- `t`, a value of the encoder's datatype, encodes the bag of the entries `xs`: each element
of `K` has the same multiplicity in both. -/
def Enc (O : Oracle) (P : Program) (N : Names) (K : Value → Prop) (E : Value → Value → Bool)
    (xs : List BagEntry) (t : Value) : Prop :=
  ∃ d, ∀ w, K w → Mult O P N t w d (mult E xs w)

section Encoding
variable {O : Oracle} {P : Program} {N : Names} {K : Value → Prop} {E : Value → Value → Bool}

/-- The multiplicity of an element in a bag is what `get` evaluates to on its encoding. -/
theorem enc_get (hO : O.Sound) (hN : N.Distinct) (hP : HasBags N P) (hE : KeyEq O P K E)
    {xs : List BagEntry} (hxs : Canon E K xs) {t w : Value} (h : Enc O P N K E xs t) (hw : K w)
    (tps : List Ty) (tenv : List TypeBinding) :
    ∃ m, O.bag_get P xs w = .Ok m ∧
      ∃ fuel, call O P fuel N.get tps tenv [t, w] = .Ok (.IntV m) := by
  obtain ⟨d, hd⟩ := h
  exact ⟨_, bag_get_eq hO hE hxs hw, d + 1, get_eval hO hN hP (hd w hw) _ tps tenv (by omega)⟩

/-- The empty bag is `Leaf`. -/
theorem enc_empty (tps : List Ty) : Enc O P N K E [] (.ADTV N.leaf tps []) :=
  ⟨0, fun w _ => Mult.leaf tps w⟩

/-- The sum of two bags is the `Node` of the operation 0 of their encodings. -/
theorem enc_union (hE : KeyEq O P K E) {xs ys : List BagEntry} (hxs : Canon E K xs)
    (hys : Canon E K ys) {a b : Value} (ha : Enc O P N K E xs a) (hb : Enc O P N K E ys b)
    (tps : List Ty) : Enc O P N K E (addAll E xs ys) (.ADTV N.node tps [.IntV 0, a, b]) := by
  obtain ⟨d1, h1⟩ := ha
  obtain ⟨d2, h2⟩ := hb
  refine ⟨max d1 d2 + 1, fun w hw => ?_⟩
  have h1 := h1 w hw
  have h2 := h2 w hw
  have := Mult.node tps 0 a b w d1 d2 _ _ h1 h2
  rw [mult_addAll hE hxs hys hw]
  simpa [combine] using this

/-- A bag with one more occurrence of `v` is the sum of its encoding and the `Elem` of `v`
with the multiplicity 1. -/
theorem enc_add (hE : KeyEq O P K E) {xs : List BagEntry} (hxs : Canon E K xs) {a v : Value}
    (ha : Enc O P N K E xs a) (hv : K v) (tps tps' : List Ty) :
    Enc O P N K E (set E xs v (mult E xs v + 1))
      (.ADTV N.node tps [.IntV 0, a, .ADTV N.elem tps' [v, .IntV 1]]) := by
  obtain ⟨d1, h1⟩ := ha
  refine ⟨max d1 0 + 1, fun w hw => ?_⟩
  have h1 := h1 w hw
  have h2 := Mult.elem (N := N) tps' v w 1 (E v w) (hE.eq v w hv hw)
  have := Mult.node tps 0 a _ w d1 0 _ _ h1 h2
  rw [mult_set hE hxs hv hw]
  have h0 := mult_nonneg hxs v
  by_cases hvw : E v w = true
  · rw [if_pos hvw, if_pos (by omega), mult_congr hE hxs hv hw hvw]
    simpa [combine, hvw] using this
  · rw [if_neg hvw]
    simpa [combine, hvw] using this

/-- The difference of two bags is the `Node` of the operation 1 of their encodings. -/
theorem enc_difference (hE : KeyEq O P K E) {xs ys : List BagEntry} (hxs : Canon E K xs)
    (hys : Canon E K ys) {a b : Value} (ha : Enc O P N K E xs a) (hb : Enc O P N K E ys b)
    (tps : List Ty) :
    Enc O P N K E (merge E .DifferenceOp [] xs ys) (.ADTV N.node tps [.IntV 1, a, b]) := by
  obtain ⟨d1, h1⟩ := ha
  obtain ⟨d2, h2⟩ := hb
  refine ⟨max d1 d2 + 1, fun w hw => ?_⟩
  have h1 := h1 w hw
  have h2 := h2 w hw
  have := Mult.node tps 1 a b w d1 d2 _ _ h1 h2
  rw [mult_merge hE _ hys (acc := []) (by trivial) hxs hw]
  have hx := mult_nonneg hxs w
  have hy := mult_nonneg hys w
  have e : (if 0 < mult E xs w then
      (if 0 < bag_combine .DifferenceOp (mult E xs w) (mult E ys w) then
        bag_combine .DifferenceOp (mult E xs w) (mult E ys w) else 0)
      else mult E [] w) = combine 1 (mult E xs w) (mult E ys w) := by
    generalize mult E xs w = p at hx
    generalize mult E ys w = q at hy
    by_cases c1 : 0 < p <;> by_cases c2 : p ≤ q <;> by_cases c3 : p < q <;>
      by_cases c4 : 0 < p - q <;>
      simp [bag_combine, Semantics.min, combine, mult, c1, c2, c3, c4] <;> omega
  rw [e]; exact this

/-- The intersection of two bags is the `Node` of the operation 2 of their encodings. -/
theorem enc_intersection (hE : KeyEq O P K E) {xs ys : List BagEntry} (hxs : Canon E K xs)
    (hys : Canon E K ys) {a b : Value} (ha : Enc O P N K E xs a) (hb : Enc O P N K E ys b)
    (tps : List Ty) :
    Enc O P N K E (merge E .IntersectionOp [] xs ys) (.ADTV N.node tps [.IntV 2, a, b]) := by
  obtain ⟨d1, h1⟩ := ha
  obtain ⟨d2, h2⟩ := hb
  refine ⟨max d1 d2 + 1, fun w hw => ?_⟩
  have h1 := h1 w hw
  have h2 := h2 w hw
  have := Mult.node tps 2 a b w d1 d2 _ _ h1 h2
  rw [mult_merge hE _ hys (acc := []) (by trivial) hxs hw]
  have hx := mult_nonneg hxs w
  have hy := mult_nonneg hys w
  have e : (if 0 < mult E xs w then
      (if 0 < bag_combine .IntersectionOp (mult E xs w) (mult E ys w) then
        bag_combine .IntersectionOp (mult E xs w) (mult E ys w) else 0)
      else mult E [] w) = combine 2 (mult E xs w) (mult E ys w) := by
    generalize mult E xs w = p at hx
    generalize mult E ys w = q at hy
    by_cases c1 : 0 < p <;> by_cases c2 : p ≤ q <;> by_cases c3 : p < q <;>
      by_cases c4 : 0 < p - q <;>
      simp [bag_combine, Semantics.min, combine, mult, c1, c2, c3, c4] <;> omega
  rw [e]; exact this

open Classical in
/-- The equality of the encoder's datatype on the encodings of two bags is the equality of
the bags. -/
theorem enc_equal {O : Oracle} (hO : O.Sound) {P : Program} {N : Names} (hN : N.Distinct)
    (hP : HasBags N P) {eq b1 b2 : Id} (hQ : HasEquals N eq b1 b2 P) (h1x : b1 ≠ N.x)
    (h2x : b2 ≠ N.x) (h12 : b1 ≠ b2) {K : Value → Prop} {E : Value → Value → Bool}
    (hE : KeyEq O P K E) {a b : Value} {tps : List Ty}
    (hK : ∀ vs, O.params_have_types P
        (Env.Env (bind_types [N.T] tps []) [.Binding b1 a, .Binding b2 b]) vs
        [.Param N.x (.TypeParameter N.T)] = true ↔ ∃ v, vs = [v] ∧ K v)
    {xs ys : List BagEntry} (hxs : Canon E K xs) (hys : Canon E K ys)
    (ha : Enc O P N K E xs a) (hb : Enc O P N K E ys b) (t u : Ty) :
    O.adt_equal P eq tps a b = O.value_eq P (.BagV t xs) (.BagV u ys) := by
  obtain ⟨d1, h1⟩ := ha
  obtain ⟨d2, h2⟩ := hb
  rw [bag_value_eq hO hE hxs hys]
  exact adt_equal_eq hO hN hP hQ h1x h2x h12 hK h1 h2

end Encoding

/-! ## Expressions

What the encoder makes of an expression evaluates to the encoding of the value of the
expression, for expressions of integers, of elements and of bags of them. -/

/-- The kinds of expressions that the theorem covers. -/
inductive Kind where
  | elem
  | int
  | bool
  | bag

/-- The value `v` of the input and the value `v'` of the encoded program are the same value,
or `v'` encodes the bag `v`. -/
def Rel (O : Oracle) (P : Program) (N : Names) (K : Value → Prop) (E : Value → Value → Bool)
    (T0 : Ty) : Kind → Value → Value → Prop
  | .elem, v, v' => v' = v ∧ K v
  | .int, v, v' => v' = v ∧ ∃ n, v = .IntV n
  | .bool, v, v' => v' = v ∧ ∃ b, v = .BoolV b
  | .bag, v, v' => ∃ t xs c args, v = .BagV t xs ∧ Canon E K xs ∧ Enc O P N K E xs v' ∧
      v' = .ADTV c [T0] args ∧ (c = N.node ∨ c = N.elem ∨ c = N.leaf)

/-- `e'` is what the encoder makes of `e`, an expression of the kind `k`, with `Te` the type
of the elements and `Γ` the kinds of the variables. -/
inductive Encodes (N : Names) (Γ : Id → Option Kind) (Te : Ty) :
    Expr → Expr → Kind → Prop where
  | var (x : Id) (k : Kind) (h : Γ x = some k) : Encodes N Γ Te (.Variable x) (.Variable x) k
  | int (n : Int) : Encodes N Γ Te (.IntegerLiteral n) (.IntegerLiteral n) .int
  | plus {a a' b b' : Expr} (ha : Encodes N Γ Te a a' .int) (hb : Encodes N Γ Te b b' .int) :
      Encodes N Γ Te (.Plus a b) (.Plus a' b') .int
  | empty (base : Ty) : Encodes N Γ Te (.FiniteBag [] base) (.ADT N.leaf [Te] []) .bag
  | add {b b' e e' : Expr} (hb : Encodes N Γ Te b b' .bag) (he : Encodes N Γ Te e e' .elem) :
      Encodes N Γ Te (.BagAdd b e)
        (.ADT N.node [Te] [.IntegerLiteral 0, b', .ADT N.elem [Te] [e', .IntegerLiteral 1]]) .bag
  | union {a a' b b' : Expr} (ha : Encodes N Γ Te a a' .bag) (hb : Encodes N Γ Te b b' .bag) :
      Encodes N Γ Te (.BagUnion a b) (.ADT N.node [Te] [.IntegerLiteral 0, a', b']) .bag
  | difference {a a' b b' : Expr} (ha : Encodes N Γ Te a a' .bag)
      (hb : Encodes N Γ Te b b' .bag) :
      Encodes N Γ Te (.BagDifference a b) (.ADT N.node [Te] [.IntegerLiteral 1, a', b']) .bag
  | intersection {a a' b b' : Expr} (ha : Encodes N Γ Te a a' .bag)
      (hb : Encodes N Γ Te b b' .bag) :
      Encodes N Γ Te (.BagIntersection a b) (.ADT N.node [Te] [.IntegerLiteral 2, a', b']) .bag
  | mult {e e' b b' : Expr} (he : Encodes N Γ Te e e' .elem) (hb : Encodes N Γ Te b b' .bag) :
      Encodes N Γ Te (.MultiplicityInBag e b) (.FunctionInvocation N.get [Te] [b', e']) .int
  | eqBag {a a' b b' : Expr} (ha : Encodes N Γ Te a a' .bag) (hb : Encodes N Γ Te b b' .bag) :
      Encodes N Γ Te (.Equals a b) (.Equals a' b') .bool
  | eqInt {a a' b b' : Expr} (ha : Encodes N Γ Te a a' .int) (hb : Encodes N Γ Te b b' .int) :
      Encodes N Γ Te (.Equals a b) (.Equals a' b') .bool

section Expressions
variable {O : Oracle} {P : Program} {N : Names} {K : Value → Prop} {E : Value → Value → Bool}

theorem eval_bag_ok {fuel : Int} {env : Env} {e : Expr} {b : Value}
    (h : eval_bag O P fuel env e = .Ok b) :
    eval O P fuel env e = .Ok b ∧ ∃ t xs, b = .BagV t xs := by
  rw [eval_bag] at h
  split at h
  · next v hv =>
    split at h
    · next t xs => cases h; exact ⟨hv, t, xs, rfl⟩
    · cases h
  · cases h
  · cases h

theorem sort_equality_bag {inv bi eq : Id} (hP : HasBags N P) (hS : HasSort N inv bi eq P)
    {c : Id} (hc : c = N.node ∨ c = N.elem ∨ c = N.leaf) : sort_equality P c = some eq := by
  cases P with
  | Program fs cs ss is eqs =>
  obtain ⟨hinv, hsort, hleaf⟩ := hS
  obtain ⟨hget, hnode, helem⟩ := hP
  rcases hc with rfl | rfl | rfl <;> simp [sort_equality, hnode, helem, hleaf, hsort]

/-- An encoded expression evaluates, with enough fuel, to a value that relates to the value
of the expression. -/
theorem encodes_eval (hO : O.Sound) (hN : N.Distinct) (hP : HasBags N P) {inv bi eq b1 b2 : Id}
    (hS : HasSort N inv bi eq P) (hQ : HasEquals N eq b1 b2 P) (h1x : b1 ≠ N.x)
    (h2x : b2 ≠ N.x) (h12 : b1 ≠ b2) (hE : KeyEq O P K E) {T0 Te : Ty}
    (hK : ∀ bs vs, O.params_have_types P (Env.Env (bind_types [N.T] [T0] []) bs) vs
        [.Param N.x (.TypeParameter N.T)] = true ↔ ∃ v, vs = [v] ∧ K v)
    {env env' : Env} (hT : O.resolve_all (env_types env') [Te] = [T0])
    {Γ : Id → Option Kind}
    (hΓ : ∀ x k, Γ x = some k → ∃ v v', lookup_var (env_vars env) x = .Ok v ∧
      lookup_var (env_vars env') x = .Ok v' ∧ Rel O P N K E T0 k v v')
    {e e' : Expr} {k : Kind} (h : Encodes N Γ Te e e' k) :
    ∀ (fuel : Int) (v : Value), eval O P fuel env e = .Ok v →
      ∃ (v' : Value) (n : Int), Rel O P N K E T0 k v v' ∧
        ∀ fuel' : Int, n ≤ fuel' → eval O P fuel' env' e' = .Ok v' := by
  induction h with
  | var x k hx =>
    intro fuel v hv
    obtain ⟨w, w', h1, h2, hR⟩ := hΓ x k hx
    simp only [eval, h1] at hv
    cases hv
    exact ⟨w', 0, hR, fun _ _ => by simp only [eval, h2]⟩
  | int n =>
    intro fuel v hv
    simp only [eval] at hv
    cases hv
    exact ⟨_, 0, ⟨rfl, n, rfl⟩, fun _ _ => by simp only [eval]⟩
  | plus _ _ iha ihb =>
    intro fuel v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨_, n1, ⟨rfl, p, rfl⟩, e1⟩ := iha fuel va ha
        obtain ⟨_, n2, ⟨rfl, q, rfl⟩, e2⟩ := ihb fuel vb hb
        simp only [arith_plus] at hv
        cases hv
        exact ⟨_, max n1 n2, ⟨rfl, _, rfl⟩, fun f hf => by
          simp only [eval, e1 f (by omega), e2 f (by omega), arith_plus]⟩
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | empty base =>
    intro fuel v hv
    simp only [eval, eval_bag_entries] at hv
    cases hv
    refine ⟨.ADTV N.leaf [T0] [], 1, ⟨_, [], N.leaf, [], rfl, trivial, enc_empty _, rfl,
      Or.inr (Or.inr rfl)⟩, fun f hf => ?_⟩
    simp only [eval, eval_list, construct_leaf hN hS (show 0 < f by omega), hT]
  | add _ _ ihb ihe =>
    intro fuel v hv
    simp only [eval] at hv
    split at hv
    · next vb hb =>
      split at hv
      · next ve he =>
        obtain ⟨hb, _⟩ := eval_bag_ok hb
        obtain ⟨vb', n1, ⟨t, xs, c, args, rfl, hxs, henc, rfl, hc⟩, e1⟩ := ihb fuel vb hb
        obtain ⟨ve', n2, ⟨hve, hk⟩, e2⟩ := ihe fuel ve he
        rw [hve] at e2
        simp only [bag_entries, bag_get_eq hO hE hxs hk, bag_set_eq hE hxs hk, bag_with] at hv
        cases hv
        refine ⟨.ADTV N.node [T0] [.IntV 0, .ADTV c [T0] args, .ADTV N.elem [T0] [ve, .IntV 1]],
          max (max n1 n2) 1, ⟨_, _, N.node, _, rfl, canon_set hE hxs hk _,
            enc_add hE hxs henc hk _ _, rfl, Or.inl rfl⟩, fun f hf => ?_⟩
        simp only [eval, eval_list, e1 f (by omega), e2 f (by omega),
          construct_elem hN hP hS (show 0 < f by omega) env' [Te] ve
            (show (0 : Int) ≤ 1 by omega),
          construct_node hN hP hS (show 0 < f by omega), hT]
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | union _ _ iha ihb =>
    intro fuel v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨ha, _⟩ := eval_bag_ok ha
        obtain ⟨hb, _⟩ := eval_bag_ok hb
        obtain ⟨va', n1, ⟨t, xs, c, args, rfl, hxs, hea, rfl, hc⟩, e1⟩ := iha fuel va ha
        obtain ⟨vb', n2, ⟨u, ys, c2, args2, rfl, hys, heb, rfl, hc2⟩, e2⟩ := ihb fuel vb hb
        simp only [bag_entries, bag_add_all_eq hO hE hxs hys, bag_with] at hv
        cases hv
        refine ⟨.ADTV N.node [T0] [.IntV 0, .ADTV c [T0] args, .ADTV c2 [T0] args2],
          max (max n1 n2) 1, ⟨_, _, N.node, _, rfl, canon_addAll hE hxs hys,
            enc_union hE hxs hys hea heb _, rfl, Or.inl rfl⟩, fun f hf => ?_⟩
        simp only [eval, eval_list, e1 f (by omega), e2 f (by omega),
          construct_node hN hP hS (show 0 < f by omega), hT]
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | difference _ _ iha ihb =>
    intro fuel v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨ha, _⟩ := eval_bag_ok ha
        obtain ⟨hb, _⟩ := eval_bag_ok hb
        obtain ⟨va', n1, ⟨t, xs, c, args, rfl, hxs, hea, rfl, hc⟩, e1⟩ := iha fuel va ha
        obtain ⟨vb', n2, ⟨u, ys, c2, args2, rfl, hys, heb, rfl, hc2⟩, e2⟩ := ihb fuel vb hb
        simp only [bag_entries, bag_merge_eq hO hE .DifferenceOp hys (acc := []) trivial hxs,
          bag_with] at hv
        cases hv
        refine ⟨.ADTV N.node [T0] [.IntV 1, .ADTV c [T0] args, .ADTV c2 [T0] args2],
          max (max n1 n2) 1, ⟨_, _, N.node, _, rfl, canon_merge hE _ ys (acc := []) trivial hxs,
            enc_difference hE hxs hys hea heb _, rfl, Or.inl rfl⟩, fun f hf => ?_⟩
        simp only [eval, eval_list, e1 f (by omega), e2 f (by omega),
          construct_node hN hP hS (show 0 < f by omega), hT]
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | intersection _ _ iha ihb =>
    intro fuel v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨ha, _⟩ := eval_bag_ok ha
        obtain ⟨hb, _⟩ := eval_bag_ok hb
        obtain ⟨va', n1, ⟨t, xs, c, args, rfl, hxs, hea, rfl, hc⟩, e1⟩ := iha fuel va ha
        obtain ⟨vb', n2, ⟨u, ys, c2, args2, rfl, hys, heb, rfl, hc2⟩, e2⟩ := ihb fuel vb hb
        simp only [bag_entries, bag_merge_eq hO hE .IntersectionOp hys (acc := []) trivial hxs,
          bag_with] at hv
        cases hv
        refine ⟨.ADTV N.node [T0] [.IntV 2, .ADTV c [T0] args, .ADTV c2 [T0] args2],
          max (max n1 n2) 1, ⟨_, _, N.node, _, rfl, canon_merge hE _ ys (acc := []) trivial hxs,
            enc_intersection hE hxs hys hea heb _, rfl, Or.inl rfl⟩, fun f hf => ?_⟩
        simp only [eval, eval_list, e1 f (by omega), e2 f (by omega),
          construct_node hN hP hS (show 0 < f by omega), hT]
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | mult _ _ ihe ihb =>
    intro fuel v hv
    simp only [eval] at hv
    split at hv
    · next ve he =>
      split at hv
      · next vb hb =>
        obtain ⟨hb, _⟩ := eval_bag_ok hb
        obtain ⟨vb', n1, ⟨t, xs, c, args, rfl, hxs, ⟨d, hd⟩, rfl, hc⟩, e1⟩ :=
          ihb fuel vb hb
        obtain ⟨ve', n2, ⟨hve, hk⟩, e2⟩ := ihe fuel ve he
        rw [hve] at e2
        simp only [bag_entries, bag_get_eq hO hE hxs hk] at hv
        cases hv
        refine ⟨_, max (max n1 n2) (d + 1), ⟨rfl, _, rfl⟩, fun f hf => ?_⟩
        simp only [eval, eval_list, e1 f (by omega), e2 f (by omega)]
        exact get_eval hO hN hP (hd ve hk) f _ _ (by omega)
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | eqBag _ _ iha ihb =>
    intro fuel v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨va', n1, ⟨t, xs, c, args, rfl, hxs, hea, rfl, hc⟩, e1⟩ := iha fuel va ha
        obtain ⟨vb', n2, ⟨u, ys, c2, args2, rfl, hys, heb, rfl, hc2⟩, e2⟩ := ihb fuel vb hb
        split at hv
        · next same hsame =>
          cases hv
          refine ⟨_, max n1 n2, ⟨rfl, _, rfl⟩, fun f hf => ?_⟩
          have heq := enc_equal hO hN hP hQ h1x h2x h12 hE (hK _) hxs hys hea heb t u
          simp only [eval, e1 f (by omega), e2 f (by omega)]
          rw [hO.value_eq]
          simp only [sort_equality_bag hP hS hc, heq, hsame]
        · cases hv
        · cases hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv
  | eqInt _ _ iha ihb =>
    intro fuel v hv
    simp only [eval] at hv
    split at hv
    · next va ha =>
      split at hv
      · next vb hb =>
        obtain ⟨_, n1, ⟨rfl, _⟩, e1⟩ := iha fuel va ha
        obtain ⟨_, n2, ⟨rfl, _⟩, e2⟩ := ihb fuel vb hb
        split at hv
        · next same hsame =>
          cases hv
          exact ⟨_, max n1 n2, ⟨rfl, _, rfl⟩, fun f hf => by
            simp only [eval, e1 f (by omega), e2 f (by omega), hsame]⟩
        · cases hv
        · cases hv
      · cases hv
      · cases hv
    · cases hv
    · cases hv

end Expressions

end Inox.Bags
