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

end Encoding

end Inox.Bags
