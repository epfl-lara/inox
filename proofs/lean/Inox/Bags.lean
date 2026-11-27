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
has the encoder's datatype and function.
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
inductive Mult (O : Oracle) (P : Program) (N : Names) : Value → Value → Nat → Int → Prop where
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
    rw [call, dif_neg (by omega)]
    simp only [hget, bind_all, getBody]
    simp [eval, eval_bool, eval_and, lookup_var, env_vars, hN.node_leaf, hN.elem_leaf]
  | elem tps k x n same hsame =>
    intro fuel tps' tenv hf
    cases P with
    | Program fs cs ss is eq =>
    obtain ⟨hget, hnode, helem⟩ := hP
    rw [call, dif_neg (by omega)]
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
    rw [call, dif_neg (by omega)]
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

end Inox.Bags
