# Inox semantics

This file defines what an Inox expression means, independently of any proof
checker. Proofs of Inox's answers state their theorems against it: an UNSAT
answer means that no values of the free variables make the query evaluate to
`true`.

It is written to be read by people and by a code generator. Only the fenced
blocks tagged `inox-sem` are normative; the prose around them is commentary.
The generator (`inox.semantics.Codegen`) reads those blocks and writes the
semantics for each checker or tool that needs it: today, a Scala evaluator that
the tests compare with Inox's `RecursiveEvaluator`, and Lean definitions that
proofs are stated against. The language of the blocks
is described at the end of this file.

This version covers integers, Booleans, unit, characters, reals, strings,
bit-vectors, tuples, algebraic datatypes (with their invariants), recursive
functions, first-class functions, `let`, `if`, `assume` and
`error`, sets, bags and maps, quantifiers, and the uninterpreted functions of
models, floating point, and the dependent types (`PiType` and `SigmaType`).
`--function-equality=intensional`, which compares normalized lambdas, stays
outside the semantics.

## Evaluation with fuel

Evaluation is a function `eval P fuel env e` of a program `P`, an amount of
fuel, an environment `env` that gives values to the free variables, and an
expression `e`. Its result is one of:

- `(Ok v)`: `e` evaluates to the value `v`;
- `Stuck`: evaluation fails, at an `error`, an assumption that doesn't hold,
  an invariant that doesn't hold, a division by zero, or a selector applied to
  a value built with another constructor;
- `OutOfFuel`: evaluation needs more fuel.

Fuel bounds the depth of nested function calls and applications: a call
evaluates the callee's body with one less fuel, and so does the application of
a first-class function, since a function stored in a value can apply itself,
and the call of an uninterpreted function, whose interpretation in a model can
call it again; nothing else consumes fuel. Inox has no
non-deterministic construct, so evaluation is a function, and more fuel never
changes a result other than `OutOfFuel`. An expression whose evaluation
diverges is one that runs out of fuel for every amount of fuel, and Inox
doesn't distinguish it from one that gets stuck: both have no value. The fuel
a call needs is its rank, the measure that Inox's termination clauses use.

Types play a role in three places only: a quantifier ranges over the values of
its parameters' types, so does the extensional equality of functions, and a
set, a bag or a map carries the types of its elements or of its keys and
values, as Inox's do, which is what tells two empty ones of different types
apart. The expressions below keep the types that these need, and evaluation
carries the types that the type parameters in scope stand for. The values of a type
parameter that nothing instantiates can only be compared for equality, so
they are read as integers: Inox's generic value `T#n` is the integer `n`.

```inox-sem
(datatype (List T)
  (Nil)
  (Cons (head T) (tail (List T))))

(datatype (Option T)
  (None)
  (Some (value T)))

(datatype (Result T)
  (Ok (value T))
  (Stuck)
  (OutOfFuel))
```

## Values

A value is an integer, a Boolean, the unit value, a character (its code), a
real (a fraction in lowest terms with a positive denominator), a string (the
list of its characters' codes), a bit-vector, a floating-point number, a
rounding mode, a tuple, a closure, a set, a
bag, a map, or a constructor applied to values.

A bit-vector of `width` bits holds them as the integer `bits`, with
`0 <= bits < 2^width`; whether it is `signed` decides how operations read it.
A closure is a function value: the parameters and body of a `Lambda`, and the
environment in which it was evaluated, types included.

A set is the list of its elements, without repetitions, in any order. A bag
is a list of elements, without repetitions, each with its multiplicity, which
is positive. A map is a list of keys, without repetitions, each with its
value, and the default value of the other keys. Since their order is
arbitrary, they are compared by their contents rather than structurally (see
Equality below).

```inox-sem
(datatype Value
  (IntV (value Int))
  (BoolV (value Bool))
  (UnitV)
  (CharV (code Int))
  (RealV (num Int) (den Int))
  (StringV (chars (List Int)))
  (BVV (signed Bool) (width Int) (bits Int))
  (FPV (exponent Int) (significand Int) (bits Int))
  (RoundingModeV (mode RoundingMode))
  (TupleV (elems (List Value)))
  (ClosureV (params (List Param)) (body Expr) (env Env))
  (SetV (base Type) (elems (List Value)))
  (BagV (base Type) (entries (List BagEntry)))
  (MapV (keys Type) (values Type) (entries (List MapEntry)) (default Value))
  (ADTV (ctor Id) (args (List Value))))

(datatype BagEntry
  (BagEntry (elem Value) (count Int)))

(datatype MapEntry
  (MapEntry (key Value) (value Value)))
```

## Expressions and programs

The expressions, with the fields of Inox's trees that evaluation uses, in the
same order (`inox.ast.Expressions`), and the types (`inox.ast.Types`). A
refinement type `{x: base | prop}` holds the values of `base` for which
`prop` evaluates to `true`.

```inox-sem
(datatype Type
  (IntegerType)
  (BooleanType)
  (UnitType)
  (CharType)
  (RealType)
  (StringType)
  (BVType (signed Bool) (width Int))
  (FPType (exponent Int) (significand Int))
  (RoundingModeType)
  (TypeParameter (id Id))
  (TupleType (elems (List Type)))
  (SetType (elem Type))
  (BagType (elem Type))
  (MapType (from Type) (to Type))
  (FunctionType (from (List Type)) (to Type))
  (ADTType (sort Id) (args (List Type)))
  (RefinementType (id Id) (base Type) (prop Expr))
  (PropType)
  (PiType (params (List Param)) (to Type))
  (SigmaType (params (List Param)) (to Type)))

(datatype Param
  (Param (id Id) (tpe Type)))
```

```inox-sem
(datatype Expr
  (Assume (pred Expr) (body Expr))
  (Variable (id Id))
  (Let (id Id) (value Expr) (body Expr))
  (Application (callee Expr) (args (List Expr)))
  (Lambda (params (List Param)) (body Expr))
  (Forall (params (List Param)) (body Expr))
  (UninterpretedCall (id Id) (tps (List Type)) (args (List Expr)))
  (Error)
  (FunctionInvocation (id Id) (tps (List Type)) (args (List Expr)))
  (IfExpr (cond Expr) (thenn Expr) (elze Expr))
  (CharLiteral (code Int))
  (BVLiteral (signed Bool) (width Int) (bits Int))
  (IntegerLiteral (value Int))
  (FractionLiteral (num Int) (den Int))
  (FPLiteral (exponent Int) (significand Int) (bits Int))
  (BooleanLiteral (value Bool))
  (StringLiteral (chars (List Int)))
  (UnitLiteral)
  (RoundNearestTiesToEven)
  (RoundNearestTiesToAway)
  (RoundTowardPositive)
  (RoundTowardNegative)
  (RoundTowardZero)
  (ADT (id Id) (tps (List Type)) (args (List Expr)))
  (IsConstructor (expr Expr) (id Id))
  (ADTSelector (adt Expr) (selector Id))
  (Equals (lhs Expr) (rhs Expr))
  (And (exprs (List Expr)))
  (Or (exprs (List Expr)))
  (Implies (lhs Expr) (rhs Expr))
  (Not (expr Expr))
  (StringConcat (lhs Expr) (rhs Expr))
  (SubString (expr Expr) (start Expr) (end Expr))
  (StringLength (expr Expr))
  (Plus (lhs Expr) (rhs Expr))
  (Minus (lhs Expr) (rhs Expr))
  (UMinus (expr Expr))
  (Times (lhs Expr) (rhs Expr))
  (Division (lhs Expr) (rhs Expr))
  (Remainder (lhs Expr) (rhs Expr))
  (Modulo (lhs Expr) (rhs Expr))
  (LessThan (lhs Expr) (rhs Expr))
  (GreaterThan (lhs Expr) (rhs Expr))
  (LessEquals (lhs Expr) (rhs Expr))
  (GreaterEquals (lhs Expr) (rhs Expr))
  (BVNot (expr Expr))
  (BVAnd (lhs Expr) (rhs Expr))
  (BVOr (lhs Expr) (rhs Expr))
  (BVXor (lhs Expr) (rhs Expr))
  (BVShiftLeft (lhs Expr) (rhs Expr))
  (BVAShiftRight (lhs Expr) (rhs Expr))
  (BVLShiftRight (lhs Expr) (rhs Expr))
  (BVNarrowingCast (expr Expr) (width Int))
  (BVWideningCast (expr Expr) (width Int))
  (BVUnsignedToSigned (expr Expr))
  (BVSignedToUnsigned (expr Expr))
  (BVToInt (expr Expr))
  (IntToBV (width Int) (signed Bool) (expr Expr))
  (FPEquals (lhs Expr) (rhs Expr))
  (FPAdd (rm Expr) (lhs Expr) (rhs Expr))
  (FPSub (rm Expr) (lhs Expr) (rhs Expr))
  (FPUMinus (expr Expr))
  (FPFMA (rm Expr) (e1 Expr) (e2 Expr) (e3 Expr))
  (FPMul (rm Expr) (lhs Expr) (rhs Expr))
  (FPDiv (rm Expr) (lhs Expr) (rhs Expr))
  (FPAbs (expr Expr))
  (FPMax (lhs Expr) (rhs Expr))
  (FPMin (lhs Expr) (rhs Expr))
  (FPRound (rm Expr) (expr Expr))
  (Sqrt (rm Expr) (expr Expr))
  (FPCast (exponent Int) (significand Int) (rm Expr) (expr Expr))
  (FPFromBinary (exponent Int) (significand Int) (expr Expr))
  (FPToBV (width Int) (signed Bool) (rm Expr) (expr Expr))
  (FPToReal (expr Expr))
  (FPLessThan (lhs Expr) (rhs Expr))
  (FPGreaterThan (lhs Expr) (rhs Expr))
  (FPLessEquals (lhs Expr) (rhs Expr))
  (FPGreaterEquals (lhs Expr) (rhs Expr))
  (FPIsZero (expr Expr))
  (FPIsInfinite (expr Expr))
  (FPIsNaN (expr Expr))
  (FPIsNegative (expr Expr))
  (FPIsPositive (expr Expr))
  (FPIsNormal (expr Expr))
  (FPIsSubnormal (expr Expr))
  (Tuple (exprs (List Expr)))
  (TupleSelect (tuple Expr) (index Int))
  (FiniteSet (elems (List Expr)) (base Type))
  (SetAdd (set Expr) (elem Expr))
  (ElementOfSet (elem Expr) (set Expr))
  (SubsetOf (lhs Expr) (rhs Expr))
  (SetIntersection (lhs Expr) (rhs Expr))
  (SetUnion (lhs Expr) (rhs Expr))
  (SetDifference (lhs Expr) (rhs Expr))
  (FiniteBag (elems (List ExprPair)) (base Type))
  (BagAdd (bag Expr) (elem Expr))
  (MultiplicityInBag (elem Expr) (bag Expr))
  (BagIntersection (lhs Expr) (rhs Expr))
  (BagUnion (lhs Expr) (rhs Expr))
  (BagDifference (lhs Expr) (rhs Expr))
  (FiniteMap (pairs (List ExprPair)) (default Expr) (keys Type) (values Type))
  (MapApply (map Expr) (key Expr))
  (MapUpdated (map Expr) (key Expr) (value Expr))
  (MapMerge (mask Expr) (map1 Expr) (map2 Expr)))

(datatype ExprPair
  (ExprPair (fst Expr) (snd Expr)))
```

A program gives each function its type parameters, parameters and body, each
constructor its sort and fields, and each sort its type parameters and its
invariant, a function of one argument, if it has one. It also gives the
uninterpreted functions of a model, one function of the arguments for each
instantiation, and how functions are compared: under `NoFunctionEquality`
(Inox's default) comparing two functions gets stuck, and under
`ExtensionalEquality` they are equal when they agree on every input.

```inox-sem
(datatype FunDef
  (FunDef (id Id) (tparams (List Id)) (params (List Id)) (body Expr)))

(datatype Constructor
  (Constructor (id Id) (sort Id) (fields (List Param))))

(datatype Sort
  (Sort (id Id) (tparams (List Id)) (invariant (Option Id))))

(datatype Interpretation
  (Interpretation (id Id) (tps (List Type)) (params (List Id)) (body Expr)))

(datatype FunctionEquality
  (NoFunctionEquality)
  (ExtensionalEquality))

(datatype Program
  (Program
    (functions (List FunDef))
    (constructors (List Constructor))
    (sorts (List Sort))
    (interpretations (List Interpretation))
    (equality FunctionEquality)))
```

An environment gives values to the variables in scope, and types to the type
parameters in scope. A type is given with the environment of type parameters
in which it was written, so that types are never substituted.

```inox-sem
(datatype Binding
  (Binding (id Id) (value Value)))

(datatype TypeBinding
  (TypeBinding (id Id) (tpe Type) (env (List TypeBinding))))

(datatype Env
  (Env (types (List TypeBinding)) (vars (List Binding))))
```

## Looking things up

Bindings are listed most recent first. A variable without a binding, or a
name that the program doesn't define, gets evaluation stuck; a well-typed
program never does.

```inox-sem
(define (lookup-var (vars (List Binding)) (x Id)) (Result Value)
  (match vars
    ((Nil) (Stuck))
    ((Cons (Binding y v) rest) (if (= x y) (Ok v) (lookup-var rest x)))))

(define (lookup-type (types (List TypeBinding)) (x Id)) (Option TypeBinding)
  (match types
    ((Nil) (None))
    ((Cons b rest)
      (match b
        ((TypeBinding y _ _) (if (= x y) (Some b) (lookup-type rest x)))))))

(define (bind-types (ids (List Id)) (tps (List Type)) (env (List TypeBinding))) (List TypeBinding)
  (match ids
    ((Nil) (Nil))
    ((Cons x xs)
      (match tps
        ((Nil) (Nil))
        ((Cons t ts) (Cons (TypeBinding x t env) (bind-types xs ts env)))))))

(define (env-types (env Env)) (List TypeBinding)
  (match env
    ((Env tys _) tys)))

(define (env-vars (env Env)) (List Binding)
  (match env
    ((Env _ vars) vars)))

(define (env-bind (env Env) (x Id) (v Value)) Env
  (match env
    ((Env tys vars) (Env tys (Cons (Binding x v) vars)))))

(define (param-ids (ps (List Param))) (List Id)
  (match ps
    ((Nil) (Nil))
    ((Cons (Param x _) rest) (Cons x (param-ids rest)))))

(define (bind-all (ids (List Id)) (vs (List Value))) (Result (List Binding))
  (match ids
    ((Nil)
      (match vs
        ((Nil) (Ok (Nil)))
        (_ (Stuck))))
    ((Cons x xs)
      (match vs
        ((Nil) (Stuck))
        ((Cons v rest)
          (let! ((bs (bind-all xs rest)))
            (Ok (Cons (Binding x v) bs))))))))

(define (lookup-fun (fs (List FunDef)) (f Id)) (Result FunDef)
  (match fs
    ((Nil) (Stuck))
    ((Cons fd rest)
      (match fd
        ((FunDef g _ _ _) (if (= f g) (Ok fd) (lookup-fun rest f)))))))

(define (lookup-ctor (cs (List Constructor)) (c Id)) (Result Constructor)
  (match cs
    ((Nil) (Stuck))
    ((Cons k rest)
      (match k
        ((Constructor d _ _) (if (= c d) (Ok k) (lookup-ctor rest c)))))))

(define (lookup-sort (ss (List Sort)) (s Id)) (Result Sort)
  (match ss
    ((Nil) (Stuck))
    ((Cons srt rest)
      (match srt
        ((Sort t _ _) (if (= s t) (Ok srt) (lookup-sort rest s)))))))

(define (select-field (fields (List Param)) (args (List Value)) (sel Id)) (Result Value)
  (match fields
    ((Nil) (Stuck))
    ((Cons (Param f _) fs)
      (match args
        ((Nil) (Stuck))
        ((Cons v vs) (if (= f sel) (Ok v) (select-field fs vs sel)))))))
```

## Calls

A call evaluates its callee's body in an environment that binds only its type
parameters, to the type arguments as written in the caller's environment
`tenv`, and its parameters, with one less fuel. Inox functions have no free
variables other than their parameters.

```inox-sem
(define (call (P Program) (fuel Int) (f Id) (tps (List Type)) (tenv (List TypeBinding)) (vs (List Value))) (Result Value)
  (if (<= fuel 0)
    (OutOfFuel)
    (match P
      ((Program fs _ _ _ _)
        (let! ((fd (lookup-fun fs f)))
          (match fd
            ((FunDef _ tparams params body)
              (let! ((bs (bind-all params vs)))
                (eval P (- fuel 1) (Env (bind-types tparams tps tenv) bs) body)))))))))
```

## Evaluation

Each Inox expression form has one equation. The arguments of an operation and
of a call are evaluated from left to right, and `And`, `Or` and `Implies`
evaluate their operands only as far as they need.

```inox-sem
(define (eval (P Program) (fuel Int) (env Env) (e Expr)) (Result Value)
  :cases e)

(define (eval-list (P Program) (fuel Int) (env Env) (es (List Expr))) (Result (List Value))
  (match es
    ((Nil) (Ok (Nil)))
    ((Cons e rest)
      (let! ((v (eval P fuel env e))
             (vs (eval-list P fuel env rest)))
        (Ok (Cons v vs))))))

(define (eval-int (P Program) (fuel Int) (env Env) (e Expr)) (Result Int)
  (let! ((v (eval P fuel env e)))
    (match v
      ((IntV i) (Ok i))
      (_ (Stuck)))))

(define (eval-bool (P Program) (fuel Int) (env Env) (e Expr)) (Result Bool)
  (let! ((v (eval P fuel env e)))
    (match v
      ((BoolV b) (Ok b))
      (_ (Stuck)))))
```

Variables, literals, `let`, `if`, `assume` and `error`:

```inox-sem
(case eval (Variable x)
  (lookup-var (env-vars env) x))

(case eval (IntegerLiteral i)
  (Ok (IntV i)))

(case eval (BooleanLiteral b)
  (Ok (BoolV b)))

(case eval (UnitLiteral)
  (Ok (UnitV)))

(case eval (Let x value body)
  (let! ((v (eval P fuel env value)))
    (eval P fuel (env-bind env x v) body)))

(case eval (IfExpr cond thenn elze)
  (let! ((b (eval-bool P fuel env cond)))
    (if b (eval P fuel env thenn) (eval P fuel env elze))))

(case eval (Assume pred body)
  (let! ((b (eval-bool P fuel env pred)))
    (if b (eval P fuel env body) (Stuck))))

(case eval (Error)
  (Stuck))
```

A function call evaluates its arguments, then the call (see Calls above).

```inox-sem
(case eval (FunctionInvocation f tps args)
  (let! ((vs (eval-list P fuel env args)))
    (call P fuel f tps (env-types env) vs)))
```

Building a value of a sort that has an invariant calls the invariant on it,
and gets stuck unless it holds. Testing a constructor never gets stuck, and
selecting a field of a value built with a constructor that doesn't have it
does.

```inox-sem
(case eval (ADT c tps args)
  (let! ((vs (eval-list P fuel env args)))
    (construct P fuel env c tps vs)))

(define (construct (P Program) (fuel Int) (env Env) (c Id) (tps (List Type)) (vs (List Value))) (Result Value)
  (match P
    ((Program _ cs ss _ _)
      (let! ((k (lookup-ctor cs c)))
        (match k
          ((Constructor _ s _)
            (let! ((srt (lookup-sort ss s)))
              (match srt
                ((Sort _ _ (None)) (Ok (ADTV c vs)))
                ((Sort _ _ (Some inv))
                  (let! ((holds (call P fuel inv tps (env-types env) (Cons (ADTV c vs) (Nil)))))
                    (match holds
                      ((BoolV true) (Ok (ADTV c vs)))
                      (_ (Stuck)))))))))))))

(case eval (IsConstructor adt c)
  (let! ((v (eval P fuel env adt)))
    (match v
      ((ADTV d _) (Ok (BoolV (= c d))))
      (_ (Stuck)))))

(case eval (ADTSelector adt sel)
  (let! ((v (eval P fuel env adt)))
    (match v
      ((ADTV c vs)
        (match P
          ((Program _ cs _ _ _)
            (let! ((k (lookup-ctor cs c)))
              (match k
                ((Constructor _ _ fields) (select-field fields vs sel)))))))
      (_ (Stuck)))))
```

Equality compares values structurally, from left to right, and stops at the
first difference, except for sets, bags and maps, which are equal when they
have the same contents, and functions, which are compared as the program says
(see Quantifiers below).

```inox-sem
(define (value-eq (P Program) (a Value) (b Value)) (Result Bool)
  :cases a)

(case value-eq (IntV _) (Ok (= a b)))
(case value-eq (BoolV _) (Ok (= a b)))
(case value-eq (UnitV) (Ok (= a b)))
(case value-eq (CharV _) (Ok (= a b)))
(case value-eq (RealV _ _) (Ok (= a b)))
(case value-eq (StringV _) (Ok (= a b)))
(case value-eq (BVV _ _ _) (Ok (= a b)))
(case value-eq (FPV _ _ _) (Ok (= a b)))
(case value-eq (RoundingModeV _) (Ok (= a b)))

(case value-eq (ClosureV _ _ _)
  (match P
    ((Program _ _ _ _ eq)
      (match eq
        ((NoFunctionEquality) (Stuck))
        ((ExtensionalEquality) (Ok (closures-equal P a b)))))))

(case value-eq (ADTV c xs)
  (match b
    ((ADTV d ys) (if (= c d) (values-eq P xs ys) (Ok false)))
    (_ (Ok false))))

(case value-eq (TupleV xs)
  (match b
    ((TupleV ys) (values-eq P xs ys))
    (_ (Ok false))))

(case value-eq (SetV _ xs)
  (match b
    ((SetV _ ys)
      (let! ((sub (subset P xs ys)))
        (if sub (subset P ys xs) (Ok false))))
    (_ (Ok false))))

(case value-eq (BagV _ xs)
  (match b
    ((BagV _ ys)
      (let! ((sub (sub-bag P xs ys)))
        (if sub (sub-bag P ys xs) (Ok false))))
    (_ (Ok false))))

(case value-eq (MapV _ _ xs d)
  (match b
    ((MapV _ _ ys e)
      (let! ((same (value-eq P d e)))
        (if same
          (let! ((l (same-entries P xs xs d ys e)))
            (if l (same-entries P ys xs d ys e) (Ok false)))
          (Ok false))))
    (_ (Ok false))))

(define (values-eq (P Program) (xs (List Value)) (ys (List Value))) (Result Bool)
  (match xs
    ((Nil)
      (match ys
        ((Nil) (Ok true))
        (_ (Ok false))))
    ((Cons x xr)
      (match ys
        ((Nil) (Ok false))
        ((Cons y yr)
          (let! ((same (value-eq P x y)))
            (if same (values-eq P xr yr) (Ok false))))))))

(case eval (Equals lhs rhs)
  (let! ((a (eval P fuel env lhs))
         (b (eval P fuel env rhs))
         (same (value-eq P a b)))
    (Ok (BoolV same))))
```

The Boolean connectives:

```inox-sem
(define (eval-and (P Program) (fuel Int) (env Env) (es (List Expr))) (Result Value)
  (match es
    ((Nil) (Ok (BoolV true)))
    ((Cons e rest)
      (let! ((b (eval-bool P fuel env e)))
        (if b (eval-and P fuel env rest) (Ok (BoolV false)))))))

(define (eval-or (P Program) (fuel Int) (env Env) (es (List Expr))) (Result Value)
  (match es
    ((Nil) (Ok (BoolV false)))
    ((Cons e rest)
      (let! ((b (eval-bool P fuel env e)))
        (if b (Ok (BoolV true)) (eval-or P fuel env rest))))))

(case eval (And es)
  (eval-and P fuel env es))

(case eval (Or es)
  (eval-or P fuel env es))

(case eval (Implies lhs rhs)
  (let! ((a (eval-bool P fuel env lhs)))
    (if a (let! ((b (eval-bool P fuel env rhs))) (Ok (BoolV b))) (Ok (BoolV true)))))

(case eval (Not expr)
  (let! ((a (eval-bool P fuel env expr)))
    (Ok (BoolV (not a)))))
```

Literals evaluate to themselves. A fraction literal is put in lowest terms.

```inox-sem
(case eval (CharLiteral c)
  (Ok (CharV c)))

(case eval (BVLiteral s w x)
  (Ok (BVV s w x)))

(case eval (FractionLiteral n d)
  (real n d))

(case eval (StringLiteral cs)
  (Ok (StringV cs)))
```

### First-class functions

A `Lambda` evaluates to a closure, which captures the environment. Applying a
closure evaluates the callee, then the arguments, then the closure's body in
its environment extended with its parameters, with one less fuel.

```inox-sem
(case eval (Lambda params body)
  (Ok (ClosureV params body env)))

(define (apply (P Program) (fuel Int) (f Value) (vs (List Value))) (Result Value)
  (match f
    ((ClosureV params body (Env tys vars))
      (if (<= fuel 0)
        (OutOfFuel)
        (let! ((bs (bind-all (param-ids params) vs)))
          (eval P (- fuel 1) (Env tys (append-env bs vars)) body))))
    (_ (Stuck))))

(case eval (Application callee args)
  (let! ((f (eval P fuel env callee))
         (vs (eval-list P fuel env args)))
    (apply P fuel f vs)))

(define (append-env (bs (List Binding)) (env (List Binding))) (List Binding)
  (match bs
    ((Nil) env)
    ((Cons b rest) (Cons b (append-env rest env)))))
```

### Tuples

`TupleSelect` counts from 1.

```inox-sem
(case eval (Tuple es)
  (let! ((vs (eval-list P fuel env es)))
    (Ok (TupleV vs))))

(case eval (TupleSelect tuple i)
  (let! ((t (eval P fuel env tuple)))
    (match t
      ((TupleV vs) (nth vs i))
      (_ (Stuck)))))

(define (nth (vs (List Value)) (i Int)) (Result Value)
  (match vs
    ((Nil) (Stuck))
    ((Cons v rest) (if (= i 1) (Ok v) (nth rest (- i 1))))))
```

### Integer helpers

Euclid's algorithm, powers of two, and the bitwise operations on non-negative
integers, one bit at a time.

```inox-sem
(define (abs (a Int)) Int
  (if (< a 0) (- 0 a) a))

(define (gcd (a Int) (b Int)) Int
  (if (= b 0) a (gcd b (mod a b))))

(define (pow2 (n Int)) Int
  (if (<= n 0) 1 (* 2 (pow2 (- n 1)))))

(define (bit (a Int)) Int
  (mod a 2))

(define (bit-and (a Int) (b Int)) Int
  (if (or (<= a 0) (<= b 0))
    0
    (+ (* 2 (bit-and (div a 2) (div b 2))) (* (bit a) (bit b)))))

(define (bit-or (a Int) (b Int)) Int
  (if (<= a 0)
    b
    (if (<= b 0)
      a
      (+ (* 2 (bit-or (div a 2) (div b 2))) (- (+ (bit a) (bit b)) (* (bit a) (bit b)))))))

(define (bit-xor (a Int) (b Int)) Int
  (if (<= a 0)
    b
    (if (<= b 0)
      a
      (+ (* 2 (bit-xor (div a 2) (div b 2))) (mod (+ (bit a) (bit b)) 2)))))
```

The quotient of a division rounded toward zero, and its remainder, which has
the sign of the dividend:

```inox-sem
(define (tdiv (a Int) (b Int)) Int
  (if (<= 0 a) (div a b) (- 0 (div (- 0 a) b))))

(define (trem (a Int) (b Int)) Int
  (- a (* b (tdiv a b))))
```

### Reals

A real is a fraction in lowest terms with a positive denominator, so that
equal reals are structurally equal.

```inox-sem
(define (real (n Int) (d Int)) (Result Value)
  (if (= d 0)
    (Stuck)
    (let ((g (gcd (abs n) (abs d)))
          (s (if (< d 0) (- 0 1) 1)))
      (Ok (RealV (* s (div n g)) (* s (div d g)))))))
```

### Bit-vectors

A bit-vector's integer value is its bits read as an unsigned number, or for a
signed one as a two's complement number. The arithmetic operations wrap
around: they compute on the integer values and keep the low `width` bits.

```inox-sem
(define (bv (s Bool) (w Int) (x Int)) Value
  (BVV s w (mod x (pow2 w))))

(define (twos (w Int) (x Int)) Int
  (if (<= (pow2 (- w 1)) x) (- x (pow2 w)) x))

(define (bv-int (s Bool) (w Int) (x Int)) Int
  (if s (twos w x) x))

(define (same-bv (s Bool) (w Int) (t Bool) (v Int)) Bool
  (and (= s t) (= w v)))
```

### Arithmetic

`Plus`, `Minus`, `Times`, `Division`, `Remainder`, `Modulo`, `UMinus` and the
comparisons apply to integers, reals and bit-vectors of the same signedness
and width, and the comparisons to characters too.

On integers, arithmetic is on mathematical integers. Division is SMT-LIB's
euclidean division, and `Remainder` and `Modulo` both give its remainder, which
is never negative; all three get stuck on a zero divisor. Real division also
gets stuck on zero.

On bit-vectors, as in SMT-LIB, division rounds toward zero and `Remainder`
has the sign of the dividend, while `Modulo` has the sign of the divisor.
Dividing by zero is defined: an unsigned quotient has all its bits set, a
signed one is `-1` for a non-negative dividend and `1` otherwise, and both
remainders are the dividend.

```inox-sem
(define (arith-plus (a Value) (b Value)) (Result Value)
  (match a
    ((IntV x) (match b ((IntV y) (Ok (IntV (+ x y)))) (_ (Stuck))))
    ((RealV n d) (match b ((RealV m e) (real (+ (* n e) (* m d)) (* d e))) (_ (Stuck))))
    ((BVV s w x)
      (match b
        ((BVV t v y) (if (same-bv s w t v) (Ok (bv s w (+ x y))) (Stuck)))
        (_ (Stuck))))
    (_ (Stuck))))

(define (arith-minus (a Value) (b Value)) (Result Value)
  (match a
    ((IntV x) (match b ((IntV y) (Ok (IntV (- x y)))) (_ (Stuck))))
    ((RealV n d) (match b ((RealV m e) (real (- (* n e) (* m d)) (* d e))) (_ (Stuck))))
    ((BVV s w x)
      (match b
        ((BVV t v y) (if (same-bv s w t v) (Ok (bv s w (- x y))) (Stuck)))
        (_ (Stuck))))
    (_ (Stuck))))

(define (arith-times (a Value) (b Value)) (Result Value)
  (match a
    ((IntV x) (match b ((IntV y) (Ok (IntV (* x y)))) (_ (Stuck))))
    ((RealV n d) (match b ((RealV m e) (real (* n m) (* d e))) (_ (Stuck))))
    ((BVV s w x)
      (match b
        ((BVV t v y) (if (same-bv s w t v) (Ok (bv s w (* x y))) (Stuck)))
        (_ (Stuck))))
    (_ (Stuck))))

(define (arith-div (a Value) (b Value)) (Result Value)
  (match a
    ((IntV x)
      (match b
        ((IntV y) (if (= y 0) (Stuck) (Ok (IntV (div x y)))))
        (_ (Stuck))))
    ((RealV n d)
      (match b
        ((RealV m e) (if (= m 0) (Stuck) (real (* n e) (* d m))))
        (_ (Stuck))))
    ((BVV s w x)
      (match b
        ((BVV t v y)
          (if (same-bv s w t v)
            (let ((i (bv-int s w x)) (j (bv-int s w y)))
              (if (= j 0)
                (if s
                  (Ok (bv s w (if (<= 0 i) (- 0 1) 1)))
                  (Ok (bv s w (- (pow2 w) 1))))
                (Ok (bv s w (tdiv i j)))))
            (Stuck)))
        (_ (Stuck))))
    (_ (Stuck))))

(define (arith-rem (a Value) (b Value)) (Result Value)
  (match a
    ((IntV x)
      (match b
        ((IntV y) (if (= y 0) (Stuck) (Ok (IntV (mod x y)))))
        (_ (Stuck))))
    ((BVV s w x)
      (match b
        ((BVV t v y)
          (if (same-bv s w t v)
            (let ((i (bv-int s w x)) (j (bv-int s w y)))
              (if (= j 0) (Ok a) (Ok (bv s w (trem i j)))))
            (Stuck)))
        (_ (Stuck))))
    (_ (Stuck))))

(define (arith-mod (a Value) (b Value)) (Result Value)
  (match a
    ((IntV x)
      (match b
        ((IntV y) (if (= y 0) (Stuck) (Ok (IntV (mod x y)))))
        (_ (Stuck))))
    ((BVV s w x)
      (match b
        ((BVV t v y)
          (if (same-bv s w t v)
            (let ((i (bv-int s w x)) (j (bv-int s w y)))
              (if (= j 0)
                (Ok a)
                (let ((r (mod i j)))
                  (Ok (bv s w (if (and (< j 0) (not (= r 0))) (+ r j) r))))))
            (Stuck)))
        (_ (Stuck))))
    (_ (Stuck))))

(define (arith-neg (a Value)) (Result Value)
  (match a
    ((IntV x) (Ok (IntV (- 0 x))))
    ((RealV n d) (Ok (RealV (- 0 n) d)))
    ((BVV s w x) (Ok (bv s w (- 0 x))))
    (_ (Stuck))))

(define (arith-lt (a Value) (b Value)) (Result Bool)
  (match a
    ((IntV x) (match b ((IntV y) (Ok (< x y))) (_ (Stuck))))
    ((RealV n d) (match b ((RealV m e) (Ok (< (* n e) (* m d)))) (_ (Stuck))))
    ((CharV x) (match b ((CharV y) (Ok (< x y))) (_ (Stuck))))
    ((BVV s w x)
      (match b
        ((BVV t v y) (if (same-bv s w t v) (Ok (< (bv-int s w x) (bv-int s w y))) (Stuck)))
        (_ (Stuck))))
    (_ (Stuck))))

(define (arith-le (a Value) (b Value)) (Result Bool)
  (let! ((lt (arith-lt b a)))
    (Ok (not lt))))

(case eval (Plus lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (arith-plus a b)))

(case eval (Minus lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (arith-minus a b)))

(case eval (UMinus expr)
  (let! ((a (eval P fuel env expr)))
    (arith-neg a)))

(case eval (Times lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (arith-times a b)))

(case eval (Division lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (arith-div a b)))

(case eval (Remainder lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (arith-rem a b)))

(case eval (Modulo lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (arith-mod a b)))

(case eval (LessThan lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)) (r (arith-lt a b)))
    (Ok (BoolV r))))

(case eval (GreaterThan lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)) (r (arith-lt b a)))
    (Ok (BoolV r))))

(case eval (LessEquals lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)) (r (arith-le a b)))
    (Ok (BoolV r))))

(case eval (GreaterEquals lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)) (r (arith-le b a)))
    (Ok (BoolV r))))
```

### Bitwise operations and conversions

The bitwise operations and shifts take bit-vectors of the same signedness and
width. As in SMT-LIB, a shift amount is read as an unsigned number, and
shifting by `width` or more vacates every bit. An arithmetic right shift
copies the most significant bit, whatever the signedness. Casts keep the
integer value modulo the new width, so they sign-extend a signed bit-vector
and zero-extend an unsigned one.

```inox-sem
(datatype BitOp
  (AndOp)
  (OrOp)
  (XorOp)
  (ShiftLeftOp)
  (AShiftRightOp)
  (LShiftRightOp))

(define (shift-amount (w Int) (y Int)) Int
  (if (<= w y) w y))

(define (bit-op (op BitOp) (s Bool) (w Int) (x Int) (y Int)) Value
  (let ((k (pow2 (shift-amount w y))))
    (match op
      ((AndOp) (BVV s w (bit-and x y)))
      ((OrOp) (BVV s w (bit-or x y)))
      ((XorOp) (BVV s w (bit-xor x y)))
      ((ShiftLeftOp) (bv s w (* x k)))
      ((AShiftRightOp) (bv s w (div (twos w x) k)))
      ((LShiftRightOp) (BVV s w (div x k))))))

(define (bv-binary (op BitOp) (a Value) (b Value)) (Result Value)
  (match a
    ((BVV s w x)
      (match b
        ((BVV t v y) (if (same-bv s w t v) (Ok (bit-op op s w x y)) (Stuck)))
        (_ (Stuck))))
    (_ (Stuck))))

(case eval (BVNot expr)
  (let! ((a (eval P fuel env expr)))
    (match a
      ((BVV s w x) (Ok (BVV s w (- (- (pow2 w) 1) x))))
      (_ (Stuck)))))

(case eval (BVAnd lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (bv-binary (AndOp) a b)))

(case eval (BVOr lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (bv-binary (OrOp) a b)))

(case eval (BVXor lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (bv-binary (XorOp) a b)))

(case eval (BVShiftLeft lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (bv-binary (ShiftLeftOp) a b)))

(case eval (BVAShiftRight lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (bv-binary (AShiftRightOp) a b)))

(case eval (BVLShiftRight lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (bv-binary (LShiftRightOp) a b)))

(define (bv-cast (a Value) (v Int)) (Result Value)
  (match a
    ((BVV s w x) (Ok (bv s v (bv-int s w x))))
    (_ (Stuck))))

(case eval (BVNarrowingCast expr w)
  (let! ((a (eval P fuel env expr)))
    (bv-cast a w)))

(case eval (BVWideningCast expr w)
  (let! ((a (eval P fuel env expr)))
    (bv-cast a w)))

(case eval (BVUnsignedToSigned expr)
  (let! ((a (eval P fuel env expr)))
    (match a
      ((BVV false w x) (Ok (BVV true w x)))
      (_ (Stuck)))))

(case eval (BVSignedToUnsigned expr)
  (let! ((a (eval P fuel env expr)))
    (match a
      ((BVV true w x) (Ok (BVV false w x)))
      (_ (Stuck)))))

(case eval (BVToInt expr)
  (let! ((a (eval P fuel env expr)))
    (match a
      ((BVV s w x) (Ok (IntV (bv-int s w x))))
      (_ (Stuck)))))

(case eval (IntToBV w s expr)
  (let! ((i (eval-int P fuel env expr)))
    (Ok (bv s w i))))
```

### Floating point

A floating-point number of `e` exponent bits and `s` significand bits (the
hidden bit included, as in SMT-LIB) is held as its `e + s` bits, in IEEE 754's
layout: the sign, then the biased exponent, then the fraction. There is a
single NaN, the quiet NaN with only the top fraction bit set, as in SMT-LIB and
as the JVM gives it. Every operation that IEEE 754 defines as rounding an exact
result computes the exact result as a fraction, or for the square root as an
integer square root with enough bits, and rounds it with the rounding mode.

```inox-sem
(datatype RoundingMode
  (RNE)
  (RNA)
  (RTP)
  (RTN)
  (RTZ))

(datatype Rat
  (Rat (num Int) (den Int)))

(define (rat-add (a Rat) (b Rat)) Rat
  (match a ((Rat n d) (match b ((Rat m k) (Rat (+ (* n k) (* m d)) (* d k)))))))

(define (rat-mul (a Rat) (b Rat)) Rat
  (match a ((Rat n d) (match b ((Rat m k) (Rat (* n m) (* d k)))))))

(define (rat-div (a Rat) (b Rat)) Rat
  (match a
    ((Rat n d)
      (match b
        ((Rat m k) (if (< m 0) (Rat (- 0 (* n k)) (- 0 (* d m))) (Rat (* n k) (* d m))))))))

(define (rat-num (a Rat)) Int
  (match a ((Rat n _) n)))

(define (rat-cmp (a Rat) (b Rat)) Int
  (match a
    ((Rat n d)
      (match b
        ((Rat m k) (if (< (* n k) (* m d)) (- 0 1) (if (= (* n k) (* m d)) 0 1)))))))

(define (bitlen (n Int)) Int
  (if (<= n 0) 0 (+ 1 (bitlen (div n 2)))))

(define (rat-ilog2 (a Rat)) Int
  (match a
    ((Rat n d)
      (let ((k (- (bitlen n) (bitlen d))))
        (if (< k 0)
          (if (< (* n (pow2 (- 0 k))) d) (- k 1) k)
          (if (< n (* d (pow2 k))) (- k 1) k))))))

(define (isqrt-from (n Int) (x Int)) Int
  (let ((y (div (+ x (div n x)) 2)))
    (if (and (< 0 y) (< y x)) (isqrt-from n y) x)))

(define (isqrt (n Int)) Int
  (if (<= n 0) 0 (isqrt-from n (pow2 (div (+ (bitlen n) 1) 2)))))

(define (fp-bias (e Int)) Int
  (- (pow2 (- e 1)) 1))

(define (fp-max-exp (e Int)) Int
  (- (pow2 e) 1))

(define (fp-sign (e Int) (s Int) (x Int)) Bool
  (<= (pow2 (- (+ e s) 1)) x))

(define (fp-exp (e Int) (s Int) (x Int)) Int
  (mod (div x (pow2 (- s 1))) (pow2 e)))

(define (fp-frac (s Int) (x Int)) Int
  (mod x (pow2 (- s 1))))

(define (fp-nan (e Int) (s Int) (x Int)) Bool
  (and (= (fp-exp e s x) (fp-max-exp e)) (not (= (fp-frac s x) 0))))

(define (fp-inf (e Int) (s Int) (x Int)) Bool
  (and (= (fp-exp e s x) (fp-max-exp e)) (= (fp-frac s x) 0)))

(define (fp-zero (e Int) (s Int) (x Int)) Bool
  (and (= (fp-exp e s x) 0) (= (fp-frac s x) 0)))

(define (fp-bits (e Int) (s Int) (neg Bool) (be Int) (f Int)) Int
  (+ (if neg (pow2 (- (+ e s) 1)) 0) (+ (* be (pow2 (- s 1))) f)))

(define (fp-nan-bits (e Int) (s Int)) Int
  (fp-bits e s false (fp-max-exp e) (pow2 (- s 2))))

(define (fp-inf-bits (e Int) (s Int) (neg Bool)) Int
  (fp-bits e s neg (fp-max-exp e) 0))

(define (fp-zero-bits (e Int) (s Int) (neg Bool)) Int
  (fp-bits e s neg 0 0))

(define (fp-canonical (e Int) (s Int) (x Int)) Int
  (if (fp-nan e s x) (fp-nan-bits e s) x))

(define (fp-rat (e Int) (s Int) (x Int)) Rat
  (let ((be (fp-exp e s x))
        (f (fp-frac s x)))
    (let ((m (if (= be 0) f (+ f (pow2 (- s 1)))))
          (k (- (- (if (= be 0) 1 be) (fp-bias e)) (- s 1)))
          (sg (if (fp-sign e s x) (- 0 1) 1)))
      (if (< k 0) (Rat (* sg m) (pow2 (- 0 k))) (Rat (* sg (* m (pow2 k))) 1)))))
```

Rounding: `c` compares the dropped fraction with one half, and `inexact` says
whether anything was dropped.

```inox-sem
(define (round-up (rm RoundingMode) (neg Bool) (i Int) (c Int) (inexact Bool)) Bool
  (if (not inexact)
    false
    (match rm
      ((RNE) (or (< 0 c) (and (= c 0) (= (mod i 2) 1))))
      ((RNA) (<= 0 c))
      ((RTP) (not neg))
      ((RTN) neg)
      ((RTZ) false))))

(define (sign-cmp (a Int) (b Int)) Int
  (if (< a b) (- 0 1) (if (= a b) 0 1)))

(define (fp-overflow (rm RoundingMode) (e Int) (s Int) (neg Bool)) Int
  (if (match rm ((RNE) true) ((RNA) true) ((RTP) (not neg)) ((RTN) neg) ((RTZ) false))
    (fp-inf-bits e s neg)
    (fp-bits e s neg (- (fp-max-exp e) 1) (- (pow2 (- s 1)) 1))))

(define (fp-pack (rm RoundingMode) (e Int) (s Int) (neg Bool) (qe Int) (m Int)) Int
  (let ((carry (= m (pow2 s))))
    (let ((m2 (if carry (pow2 (- s 1)) m))
          (qe2 (if carry (+ qe 1) qe)))
      (if (= m2 0)
        (fp-zero-bits e s neg)
        (if (< m2 (pow2 (- s 1)))
          (fp-bits e s neg 0 m2)
          (let ((be (+ (+ qe2 (- s 1)) (fp-bias e))))
            (if (<= (fp-max-exp e) be)
              (fp-overflow rm e s neg)
              (fp-bits e s neg be (- m2 (pow2 (- s 1)))))))))))

(define (scaled (n Int) (d Int) (p Int)) Rat
  (if (< p 0) (Rat n (* d (pow2 (- 0 p)))) (Rat (* n (pow2 p)) d)))

(define (fp-round (rm RoundingMode) (e Int) (s Int) (q Rat)) Int
  (match q
    ((Rat n d)
      (let ((neg (< n 0)))
        (let ((a (Rat (abs n) d))
              (emin (- 1 (fp-bias e))))
          (let ((k (rat-ilog2 a)))
            (let ((qe (- (if (< k emin) emin k) (- s 1))))
              (match (scaled (abs n) d (- 0 qe))
                ((Rat sn sd)
                  (let ((i (div sn sd)) (r (mod sn sd)))
                    (fp-pack rm e s neg qe
                      (+ i (if (round-up rm neg i (sign-cmp (* 2 r) sd) (not (= r 0))) 1 0)))))))))))))

(define (fp-of-rat (rm RoundingMode) (e Int) (s Int) (q Rat)) Int
  (if (= (rat-num q) 0) (fp-zero-bits e s false) (fp-round rm e s q)))

(define (round-rat-int (rm RoundingMode) (q Rat)) Int
  (match q
    ((Rat n d)
      (let ((neg (< n 0)))
        (let ((i (div (abs n) d)) (r (mod (abs n) d)))
          (let ((m (+ i (if (round-up rm neg i (sign-cmp (* 2 r) d) (not (= r 0))) 1 0))))
            (if neg (- 0 m) m)))))))
```

The operations. A sum or difference that is exactly zero is `+0`, or `-0`
when rounding toward negative, unless both operands are zeros of the same
sign. `min` and `max` ignore a NaN operand unless both are NaN, and order `-0`
below `+0`.

```inox-sem
(define (is-rtn (rm RoundingMode)) Bool
  (match rm ((RTN) true) (_ false)))

(define (fp-add (rm RoundingMode) (e Int) (s Int) (x Int) (y Int)) Int
  (if (or (fp-nan e s x) (fp-nan e s y))
    (fp-nan-bits e s)
    (if (fp-inf e s x)
      (if (and (fp-inf e s y) (not (= (fp-sign e s x) (fp-sign e s y)))) (fp-nan-bits e s) x)
      (if (fp-inf e s y)
        y
        (let ((q (rat-add (fp-rat e s x) (fp-rat e s y))))
          (if (= (rat-num q) 0)
            (if (and (and (fp-zero e s x) (fp-zero e s y)) (= (fp-sign e s x) (fp-sign e s y)))
              x
              (fp-zero-bits e s (is-rtn rm)))
            (fp-round rm e s q)))))))

(define (fp-neg (e Int) (s Int) (x Int)) Int
  (if (fp-nan e s x)
    (fp-nan-bits e s)
    (if (fp-sign e s x) (- x (pow2 (- (+ e s) 1))) (+ x (pow2 (- (+ e s) 1))))))

(define (fp-abs (e Int) (s Int) (x Int)) Int
  (if (fp-sign e s x) (fp-neg e s x) (fp-canonical e s x)))

(define (fp-mul (rm RoundingMode) (e Int) (s Int) (x Int) (y Int)) Int
  (let ((neg (not (= (fp-sign e s x) (fp-sign e s y)))))
    (if (or (fp-nan e s x) (fp-nan e s y))
      (fp-nan-bits e s)
      (if (or (fp-inf e s x) (fp-inf e s y))
        (if (or (fp-zero e s x) (fp-zero e s y)) (fp-nan-bits e s) (fp-inf-bits e s neg))
        (if (or (fp-zero e s x) (fp-zero e s y))
          (fp-zero-bits e s neg)
          (fp-round rm e s (rat-mul (fp-rat e s x) (fp-rat e s y))))))))

(define (fp-div (rm RoundingMode) (e Int) (s Int) (x Int) (y Int)) Int
  (let ((neg (not (= (fp-sign e s x) (fp-sign e s y)))))
    (if (or (or (fp-nan e s x) (fp-nan e s y))
            (or (and (fp-inf e s x) (fp-inf e s y)) (and (fp-zero e s x) (fp-zero e s y))))
      (fp-nan-bits e s)
      (if (fp-inf e s x)
        (fp-inf-bits e s neg)
        (if (fp-inf e s y)
          (fp-zero-bits e s neg)
          (if (fp-zero e s y)
            (fp-inf-bits e s neg)
            (if (fp-zero e s x)
              (fp-zero-bits e s neg)
              (fp-round rm e s (rat-div (fp-rat e s x) (fp-rat e s y))))))))))

(define (fp-fma (rm RoundingMode) (e Int) (s Int) (x Int) (y Int) (z Int)) Int
  (let ((neg (not (= (fp-sign e s x) (fp-sign e s y)))))
    (if (or (or (fp-nan e s x) (fp-nan e s y)) (fp-nan e s z))
      (fp-nan-bits e s)
      (if (or (fp-inf e s x) (fp-inf e s y))
        (if (or (or (fp-zero e s x) (fp-zero e s y))
                (and (fp-inf e s z) (not (= (fp-sign e s z) neg))))
          (fp-nan-bits e s)
          (fp-inf-bits e s neg))
        (if (fp-inf e s z)
          z
          (let ((q (rat-add (rat-mul (fp-rat e s x) (fp-rat e s y)) (fp-rat e s z))))
            (if (= (rat-num q) 0)
              (if (and (or (fp-zero e s x) (fp-zero e s y)) (and (fp-zero e s z) (= (fp-sign e s z) neg)))
                z
                (fp-zero-bits e s (is-rtn rm)))
              (fp-round rm e s q))))))))

(define (fp-sqrt (rm RoundingMode) (e Int) (s Int) (x Int)) Int
  (if (fp-nan e s x)
    (fp-nan-bits e s)
    (if (fp-zero e s x)
      x
      (if (fp-sign e s x)
        (fp-nan-bits e s)
        (if (fp-inf e s x)
          x
          (match (fp-rat e s x)
            ((Rat n d)
              (let ((k (div (rat-ilog2 (Rat n d)) 2))
                    (emin (- 1 (fp-bias e))))
                (let ((qe (- (if (< k emin) emin k) (- s 1))))
                  (match (scaled n d (- 2 (* 2 qe)))
                    ((Rat sn sd)
                      (let ((m (div sn sd)) (exact (= (mod sn sd) 0)))
                        (let ((t (isqrt m)))
                          (let ((i (div t 2))
                                (half (= (mod t 2) 1))
                                (sticky (or (not exact) (not (= (* t t) m)))))
                            (let ((c (if half (if sticky 1 0) (- 0 1))))
                              (fp-pack rm e s false qe
                                (+ i (if (round-up rm false i c (or half sticky)) 1 0))))))))))))))))))

(define (fp-round-integral (rm RoundingMode) (e Int) (s Int) (x Int)) Int
  (if (or (or (fp-nan e s x) (fp-inf e s x)) (fp-zero e s x))
    (fp-canonical e s x)
    (let ((m (round-rat-int rm (fp-rat e s x))))
      (if (= m 0) (fp-zero-bits e s (fp-sign e s x)) (fp-round rm e s (Rat m 1))))))

(define (fp-cmp (e Int) (s Int) (x Int) (y Int)) Int
  (if (fp-inf e s x)
    (if (and (fp-inf e s y) (= (fp-sign e s x) (fp-sign e s y))) 0 (if (fp-sign e s x) (- 0 1) 1))
    (if (fp-inf e s y)
      (if (fp-sign e s y) 1 (- 0 1))
      (rat-cmp (fp-rat e s x) (fp-rat e s y)))))

(define (fp-max (e Int) (s Int) (x Int) (y Int) (max Bool)) Int
  (if (fp-nan e s x)
    (fp-canonical e s y)
    (if (fp-nan e s y)
      x
      (if (and (fp-zero e s x) (fp-zero e s y))
        (if (= max (fp-sign e s x)) y x)
        (if (= max (< (fp-cmp e s x y) 0)) y x)))))
```

Conversions. Casting to a floating-point format rounds the value of a
floating-point number, a bit-vector (read as signed or unsigned, as its type
says) or a real. Converting to a bit-vector rounds to an integer and saturates
at the bounds of the target, with NaN converting to zero, as on the JVM, where
SMT-LIB leaves these cases open. Converting NaN or an infinity to a real gets
stuck.

```inox-sem
(define (fp-to-int (rm RoundingMode) (e Int) (s Int) (x Int) (lo Int) (hi Int)) Int
  (if (fp-nan e s x)
    0
    (if (fp-inf e s x)
      (if (fp-sign e s x) lo hi)
      (let ((m (round-rat-int rm (fp-rat e s x))))
        (if (< m lo) lo (if (< hi m) hi m))))))

(define (fp-cast (rm RoundingMode) (e Int) (s Int) (v Value)) (Result Int)
  (match v
    ((FPV e2 s2 x)
      (if (fp-nan e2 s2 x)
        (Ok (fp-nan-bits e s))
        (if (fp-inf e2 s2 x)
          (Ok (fp-inf-bits e s (fp-sign e2 s2 x)))
          (if (fp-zero e2 s2 x)
            (Ok (fp-zero-bits e s (fp-sign e2 s2 x)))
            (Ok (fp-round rm e s (fp-rat e2 s2 x)))))))
    ((BVV sg w x) (Ok (fp-of-rat rm e s (Rat (bv-int sg w x) 1))))
    ((RealV n d) (Ok (fp-of-rat rm e s (Rat n d))))
    (_ (Stuck))))
```

```inox-sem
(define (eval-rm (P Program) (fuel Int) (env Env) (e Expr)) (Result RoundingMode)
  (let! ((v (eval P fuel env e)))
    (match v
      ((RoundingModeV rm) (Ok rm))
      (_ (Stuck)))))

(datatype FPOp
  (FPAddOp)
  (FPSubOp)
  (FPMulOp)
  (FPDivOp)
  (FPMinOp)
  (FPMaxOp))

(define (fp-op (op FPOp) (rm RoundingMode) (e Int) (s Int) (x Int) (y Int)) Int
  (match op
    ((FPAddOp) (fp-add rm e s x y))
    ((FPSubOp) (fp-add rm e s x (fp-neg e s y)))
    ((FPMulOp) (fp-mul rm e s x y))
    ((FPDivOp) (fp-div rm e s x y))
    ((FPMinOp) (fp-max e s x y false))
    ((FPMaxOp) (fp-max e s x y true))))

(define (fp-binary (op FPOp) (rm RoundingMode) (a Value) (b Value)) (Result Value)
  (match a
    ((FPV e s x)
      (match b
        ((FPV e2 s2 y)
          (if (and (= e e2) (= s s2)) (Ok (FPV e s (fp-op op rm e s x y))) (Stuck)))
        (_ (Stuck))))
    (_ (Stuck))))

(datatype FPRel
  (FPEqRel)
  (FPLtRel)
  (FPLeRel))

(define (fp-rel (rel FPRel) (a Value) (b Value)) (Result Value)
  (match a
    ((FPV e s x)
      (match b
        ((FPV e2 s2 y)
          (if (and (= e e2) (= s s2))
            (if (or (fp-nan e s x) (fp-nan e s y))
              (Ok (BoolV false))
              (let ((c (fp-cmp e s x y)))
                (match rel
                  ((FPEqRel) (Ok (BoolV (= c 0))))
                  ((FPLtRel) (Ok (BoolV (< c 0))))
                  ((FPLeRel) (Ok (BoolV (<= c 0)))))))
            (Stuck)))
        (_ (Stuck))))
    (_ (Stuck))))

(datatype FPClass
  (ZeroClass)
  (InfiniteClass)
  (NaNClass)
  (NegativeClass)
  (PositiveClass)
  (NormalClass)
  (SubnormalClass))

(define (fp-class (k FPClass) (v Value)) (Result Value)
  (match v
    ((FPV e s x)
      (let ((be (fp-exp e s x)) (nan (fp-nan e s x)))
        (match k
          ((ZeroClass) (Ok (BoolV (fp-zero e s x))))
          ((InfiniteClass) (Ok (BoolV (fp-inf e s x))))
          ((NaNClass) (Ok (BoolV nan)))
          ((NegativeClass) (Ok (BoolV (and (not nan) (fp-sign e s x)))))
          ((PositiveClass) (Ok (BoolV (and (not nan) (not (fp-sign e s x))))))
          ((NormalClass) (Ok (BoolV (and (not (= be 0)) (not (= be (fp-max-exp e)))))))
          ((SubnormalClass) (Ok (BoolV (and (= be 0) (not (fp-zero e s x)))))))))
    (_ (Stuck))))

(case eval (FPLiteral e s x)
  (Ok (FPV e s (fp-canonical e s x))))

(case eval (RoundNearestTiesToEven)
  (Ok (RoundingModeV (RNE))))

(case eval (RoundNearestTiesToAway)
  (Ok (RoundingModeV (RNA))))

(case eval (RoundTowardPositive)
  (Ok (RoundingModeV (RTP))))

(case eval (RoundTowardNegative)
  (Ok (RoundingModeV (RTN))))

(case eval (RoundTowardZero)
  (Ok (RoundingModeV (RTZ))))

(case eval (FPEquals lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (fp-rel (FPEqRel) a b)))

(case eval (FPAdd rm lhs rhs)
  (let! ((m (eval-rm P fuel env rm)) (a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (fp-binary (FPAddOp) m a b)))

(case eval (FPSub rm lhs rhs)
  (let! ((m (eval-rm P fuel env rm)) (a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (fp-binary (FPSubOp) m a b)))

(case eval (FPMul rm lhs rhs)
  (let! ((m (eval-rm P fuel env rm)) (a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (fp-binary (FPMulOp) m a b)))

(case eval (FPDiv rm lhs rhs)
  (let! ((m (eval-rm P fuel env rm)) (a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (fp-binary (FPDivOp) m a b)))

(case eval (FPMin lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (fp-binary (FPMinOp) (RNE) a b)))

(case eval (FPMax lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (fp-binary (FPMaxOp) (RNE) a b)))

(case eval (FPUMinus expr)
  (let! ((a (eval P fuel env expr)))
    (match a
      ((FPV e s x) (Ok (FPV e s (fp-neg e s x))))
      (_ (Stuck)))))

(case eval (FPAbs expr)
  (let! ((a (eval P fuel env expr)))
    (match a
      ((FPV e s x) (Ok (FPV e s (fp-abs e s x))))
      (_ (Stuck)))))

(case eval (FPFMA rm e1 e2 e3)
  (let! ((m (eval-rm P fuel env rm))
         (a (eval P fuel env e1))
         (b (eval P fuel env e2))
         (c (eval P fuel env e3)))
    (match a
      ((FPV e s x)
        (match b
          ((FPV e2 s2 y)
            (match c
              ((FPV e3 s3 z)
                (if (and (and (= e e2) (= s s2)) (and (= e e3) (= s s3)))
                  (Ok (FPV e s (fp-fma m e s x y z)))
                  (Stuck)))
              (_ (Stuck))))
          (_ (Stuck))))
      (_ (Stuck)))))

(case eval (FPRound rm expr)
  (let! ((m (eval-rm P fuel env rm)) (a (eval P fuel env expr)))
    (match a
      ((FPV e s x) (Ok (FPV e s (fp-round-integral m e s x))))
      (_ (Stuck)))))

(case eval (Sqrt rm expr)
  (let! ((m (eval-rm P fuel env rm)) (a (eval P fuel env expr)))
    (match a
      ((FPV e s x) (Ok (FPV e s (fp-sqrt m e s x))))
      (_ (Stuck)))))

(case eval (FPCast e s rm expr)
  (let! ((m (eval-rm P fuel env rm))
         (a (eval P fuel env expr))
         (x (fp-cast m e s a)))
    (Ok (FPV e s x))))

(case eval (FPFromBinary e s expr)
  (let! ((a (eval P fuel env expr)))
    (match a
      ((BVV _ w x) (if (= w (+ e s)) (Ok (FPV e s (fp-canonical e s x))) (Stuck)))
      (_ (Stuck)))))

(case eval (FPToBV w sg rm expr)
  (let! ((m (eval-rm P fuel env rm)) (a (eval P fuel env expr)))
    (match a
      ((FPV e s x)
        (let ((lo (if sg (- 0 (pow2 (- w 1))) 0))
              (hi (if sg (- (pow2 (- w 1)) 1) (- (pow2 w) 1))))
          (Ok (bv sg w (fp-to-int m e s x lo hi)))))
      (_ (Stuck)))))

(case eval (FPToReal expr)
  (let! ((a (eval P fuel env expr)))
    (match a
      ((FPV e s x)
        (if (or (fp-nan e s x) (fp-inf e s x))
          (Stuck)
          (match (fp-rat e s x) ((Rat n d) (real n d)))))
      (_ (Stuck)))))

(case eval (FPLessThan lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (fp-rel (FPLtRel) a b)))

(case eval (FPGreaterThan lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (fp-rel (FPLtRel) b a)))

(case eval (FPLessEquals lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (fp-rel (FPLeRel) a b)))

(case eval (FPGreaterEquals lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (fp-rel (FPLeRel) b a)))

(case eval (FPIsZero expr)
  (let! ((a (eval P fuel env expr))) (fp-class (ZeroClass) a)))

(case eval (FPIsInfinite expr)
  (let! ((a (eval P fuel env expr))) (fp-class (InfiniteClass) a)))

(case eval (FPIsNaN expr)
  (let! ((a (eval P fuel env expr))) (fp-class (NaNClass) a)))

(case eval (FPIsNegative expr)
  (let! ((a (eval P fuel env expr))) (fp-class (NegativeClass) a)))

(case eval (FPIsPositive expr)
  (let! ((a (eval P fuel env expr))) (fp-class (PositiveClass) a)))

(case eval (FPIsNormal expr)
  (let! ((a (eval P fuel env expr))) (fp-class (NormalClass) a)))

(case eval (FPIsSubnormal expr)
  (let! ((a (eval P fuel env expr))) (fp-class (SubnormalClass) a)))
```

### Strings

A string is the list of its characters' codes. As SMT-LIB's `str.substr`,
`SubString` gives the characters from `start` up to `end`, excluded, and the
empty string when `start` is out of bounds or `end` isn't after it.

```inox-sem
(define (append-chars (xs (List Int)) (ys (List Int))) (List Int)
  (match xs
    ((Nil) ys)
    ((Cons x rest) (Cons x (append-chars rest ys)))))

(define (length (xs (List Int))) Int
  (match xs
    ((Nil) 0)
    ((Cons _ rest) (+ 1 (length rest)))))

(define (take (n Int) (xs (List Int))) (List Int)
  (if (<= n 0)
    (Nil)
    (match xs
      ((Nil) (Nil))
      ((Cons x rest) (Cons x (take (- n 1) rest))))))

(define (drop (n Int) (xs (List Int))) (List Int)
  (if (<= n 0)
    xs
    (match xs
      ((Nil) (Nil))
      ((Cons _ rest) (drop (- n 1) rest)))))

(define (eval-string (P Program) (fuel Int) (env Env) (e Expr)) (Result (List Int))
  (let! ((v (eval P fuel env e)))
    (match v
      ((StringV cs) (Ok cs))
      (_ (Stuck)))))

(case eval (StringConcat lhs rhs)
  (let! ((a (eval-string P fuel env lhs)) (b (eval-string P fuel env rhs)))
    (Ok (StringV (append-chars a b)))))

(case eval (SubString expr start end)
  (let! ((cs (eval-string P fuel env expr))
         (b (eval-int P fuel env start))
         (c (eval-int P fuel env end)))
    (if (or (< b 0) (<= c b))
      (Ok (StringV (Nil)))
      (Ok (StringV (take (- c b) (drop b cs)))))))

(case eval (StringLength expr)
  (let! ((cs (eval-string P fuel env expr)))
    (Ok (IntV (length cs)))))
```

### Sets, bags and maps

Elements and keys are compared with `value-eq`, so a set of closures gets
stuck as soon as two of them are compared. The arguments of an operation are
evaluated from left to right, so `ElementOfSet` and `MultiplicityInBag`
evaluate the element before the collection. A collection carries the types
that its literal gives, with the type parameters in scope replaced by what
they stand for, and an operation gives a collection of the types of its first
operand. Equality doesn't look at them.

```inox-sem
(define (set-contains (P Program) (xs (List Value)) (v Value)) (Result Bool)
  (match xs
    ((Nil) (Ok false))
    ((Cons x rest)
      (let! ((same (value-eq P x v)))
        (if same (Ok true) (set-contains P rest v))))))

(define (set-insert (P Program) (xs (List Value)) (v Value)) (Result (List Value))
  (let! ((in (set-contains P xs v)))
    (if in (Ok xs) (Ok (Cons v xs)))))

(define (set-insert-all (P Program) (xs (List Value)) (vs (List Value))) (Result (List Value))
  (match vs
    ((Nil) (Ok xs))
    ((Cons v rest)
      (let! ((ys (set-insert P xs v)))
        (set-insert-all P ys rest)))))

(define (subset (P Program) (xs (List Value)) (ys (List Value))) (Result Bool)
  (match xs
    ((Nil) (Ok true))
    ((Cons x rest)
      (let! ((in (set-contains P ys x)))
        (if in (subset P rest ys) (Ok false))))))

(define (set-filter (P Program) (xs (List Value)) (ys (List Value)) (keep Bool)) (Result (List Value))
  (match xs
    ((Nil) (Ok (Nil)))
    ((Cons x rest)
      (let! ((in (set-contains P ys x))
             (zs (set-filter P rest ys keep)))
        (if (= in keep) (Ok (Cons x zs)) (Ok zs))))))

(define (eval-set (P Program) (fuel Int) (env Env) (e Expr)) (Result Value)
  (let! ((v (eval P fuel env e)))
    (match v
      ((SetV _ _) (Ok v))
      (_ (Stuck)))))

(define (set-elems (v Value)) (List Value)
  (match v
    ((SetV _ xs) xs)
    (_ (Nil))))

(define (set-with (v Value) (xs (List Value))) Value
  (match v
    ((SetV base _) (SetV base xs))
    (_ v)))

(case eval (FiniteSet es base)
  (let! ((vs (eval-list P fuel env es))
         (xs (set-insert-all P (Nil) vs)))
    (Ok (SetV (resolve (env-types env) base) xs))))

(case eval (SetAdd set elem)
  (let! ((s (eval-set P fuel env set))
         (v (eval P fuel env elem))
         (ys (set-insert P (set-elems s) v)))
    (Ok (set-with s ys))))

(case eval (ElementOfSet elem set)
  (let! ((v (eval P fuel env elem))
         (s (eval-set P fuel env set))
         (in (set-contains P (set-elems s) v)))
    (Ok (BoolV in))))

(case eval (SubsetOf lhs rhs)
  (let! ((s (eval-set P fuel env lhs))
         (u (eval-set P fuel env rhs))
         (sub (subset P (set-elems s) (set-elems u))))
    (Ok (BoolV sub))))

(case eval (SetIntersection lhs rhs)
  (let! ((s (eval-set P fuel env lhs))
         (u (eval-set P fuel env rhs))
         (zs (set-filter P (set-elems s) (set-elems u) true)))
    (Ok (set-with s zs))))

(case eval (SetUnion lhs rhs)
  (let! ((s (eval-set P fuel env lhs))
         (u (eval-set P fuel env rhs))
         (zs (set-insert-all P (set-elems s) (set-elems u))))
    (Ok (set-with s zs))))

(case eval (SetDifference lhs rhs)
  (let! ((s (eval-set P fuel env lhs))
         (u (eval-set P fuel env rhs))
         (zs (set-filter P (set-elems s) (set-elems u) false)))
    (Ok (set-with s zs))))
```

A bag maps each element to its multiplicity, and leaves out the elements of
multiplicity zero or less. Building a bag keeps the last multiplicity given
for an element. The union adds multiplicities, the intersection takes the
smaller one, and the difference subtracts them.

```inox-sem
(define (bag-get (P Program) (xs (List BagEntry)) (v Value)) (Result Int)
  (match xs
    ((Nil) (Ok 0))
    ((Cons (BagEntry x n) rest)
      (let! ((same (value-eq P x v)))
        (if same (Ok n) (bag-get P rest v))))))

(define (bag-remove (P Program) (xs (List BagEntry)) (v Value)) (Result (List BagEntry))
  (match xs
    ((Nil) (Ok (Nil)))
    ((Cons (BagEntry x n) rest)
      (let! ((same (value-eq P x v)))
        (if same
          (Ok rest)
          (let! ((ys (bag-remove P rest v)))
            (Ok (Cons (BagEntry x n) ys))))))))

(define (bag-set (P Program) (xs (List BagEntry)) (v Value) (n Int)) (Result (List BagEntry))
  (let! ((ys (bag-remove P xs v)))
    (if (< 0 n) (Ok (Cons (BagEntry v n) ys)) (Ok ys))))

(define (min (a Int) (b Int)) Int
  (if (< a b) a b))

(datatype BagOp
  (IntersectionOp)
  (UnionOp)
  (DifferenceOp))

(define (bag-combine (op BagOp) (a Int) (b Int)) Int
  (match op
    ((IntersectionOp) (min a b))
    ((UnionOp) (+ a b))
    ((DifferenceOp) (- a b))))

(define (bag-merge (P Program) (op BagOp) (acc (List BagEntry)) (xs (List BagEntry)) (ys (List BagEntry))) (Result (List BagEntry))
  (match xs
    ((Nil) (Ok acc))
    ((Cons (BagEntry x n) rest)
      (let! ((m (bag-get P ys x))
             (acc2 (bag-set P acc x (bag-combine op n m))))
        (bag-merge P op acc2 rest ys)))))

(define (bag-add-all (P Program) (acc (List BagEntry)) (xs (List BagEntry))) (Result (List BagEntry))
  (match xs
    ((Nil) (Ok acc))
    ((Cons (BagEntry x n) rest)
      (let! ((m (bag-get P acc x))
             (acc2 (bag-set P acc x (+ m n))))
        (bag-add-all P acc2 rest)))))

(define (sub-bag (P Program) (xs (List BagEntry)) (ys (List BagEntry))) (Result Bool)
  (match xs
    ((Nil) (Ok true))
    ((Cons (BagEntry x n) rest)
      (let! ((m (bag-get P ys x)))
        (if (= n m) (sub-bag P rest ys) (Ok false))))))

(define (eval-bag (P Program) (fuel Int) (env Env) (e Expr)) (Result Value)
  (let! ((v (eval P fuel env e)))
    (match v
      ((BagV _ _) (Ok v))
      (_ (Stuck)))))

(define (bag-entries (v Value)) (List BagEntry)
  (match v
    ((BagV _ xs) xs)
    (_ (Nil))))

(define (bag-with (v Value) (xs (List BagEntry))) Value
  (match v
    ((BagV base _) (BagV base xs))
    (_ v)))

(define (eval-bag-entries (P Program) (fuel Int) (env Env) (acc (List BagEntry)) (es (List ExprPair))) (Result (List BagEntry))
  (match es
    ((Nil) (Ok acc))
    ((Cons (ExprPair k c) rest)
      (let! ((v (eval P fuel env k))
             (n (eval-int P fuel env c))
             (acc2 (bag-set P acc v n)))
        (eval-bag-entries P fuel env acc2 rest)))))

(case eval (FiniteBag es base)
  (let! ((xs (eval-bag-entries P fuel env (Nil) es)))
    (Ok (BagV (resolve (env-types env) base) xs))))

(case eval (BagAdd bag elem)
  (let! ((b (eval-bag P fuel env bag))
         (v (eval P fuel env elem))
         (n (bag-get P (bag-entries b) v))
         (ys (bag-set P (bag-entries b) v (+ n 1))))
    (Ok (bag-with b ys))))

(case eval (MultiplicityInBag elem bag)
  (let! ((v (eval P fuel env elem))
         (b (eval-bag P fuel env bag))
         (n (bag-get P (bag-entries b) v)))
    (Ok (IntV n))))

(case eval (BagIntersection lhs rhs)
  (let! ((b (eval-bag P fuel env lhs))
         (c (eval-bag P fuel env rhs))
         (zs (bag-merge P (IntersectionOp) (Nil) (bag-entries b) (bag-entries c))))
    (Ok (bag-with b zs))))

(case eval (BagUnion lhs rhs)
  (let! ((b (eval-bag P fuel env lhs))
         (c (eval-bag P fuel env rhs))
         (zs (bag-add-all P (bag-entries b) (bag-entries c))))
    (Ok (bag-with b zs))))

(case eval (BagDifference lhs rhs)
  (let! ((b (eval-bag P fuel env lhs))
         (c (eval-bag P fuel env rhs))
         (zs (bag-merge P (DifferenceOp) (Nil) (bag-entries b) (bag-entries c))))
    (Ok (bag-with b zs))))
```

A map gives each key its value, or the default value. Building a map keeps
the last value given for a key, and evaluates the pairs before the default.
`MapMerge` takes the keys of the set `mask` from the first map, and the
others, and the default, from the second.

```inox-sem
(define (map-get (P Program) (xs (List MapEntry)) (k Value) (d Value)) (Result Value)
  (match xs
    ((Nil) (Ok d))
    ((Cons (MapEntry x v) rest)
      (let! ((same (value-eq P x k)))
        (if same (Ok v) (map-get P rest k d))))))

(define (map-remove (P Program) (xs (List MapEntry)) (k Value)) (Result (List MapEntry))
  (match xs
    ((Nil) (Ok (Nil)))
    ((Cons (MapEntry x v) rest)
      (let! ((same (value-eq P x k)))
        (if same
          (Ok rest)
          (let! ((ys (map-remove P rest k)))
            (Ok (Cons (MapEntry x v) ys))))))))

(define (map-put (P Program) (xs (List MapEntry)) (k Value) (v Value)) (Result (List MapEntry))
  (let! ((ys (map-remove P xs k)))
    (Ok (Cons (MapEntry k v) ys))))

(define (same-entries (P Program) (ks (List MapEntry)) (xs (List MapEntry)) (d Value) (ys (List MapEntry)) (e Value)) (Result Bool)
  (match ks
    ((Nil) (Ok true))
    ((Cons (MapEntry k _) rest)
      (let! ((a (map-get P xs k d))
             (b (map-get P ys k e))
             (same (value-eq P a b)))
        (if same (same-entries P rest xs d ys e) (Ok false))))))

(define (map-without (P Program) (xs (List MapEntry)) (ks (List Value))) (Result (List MapEntry))
  (match xs
    ((Nil) (Ok (Nil)))
    ((Cons (MapEntry k v) rest)
      (let! ((in (set-contains P ks k))
             (ys (map-without P rest ks)))
        (if in (Ok ys) (Ok (Cons (MapEntry k v) ys)))))))

(define (map-take (P Program) (acc (List MapEntry)) (ks (List Value)) (xs (List MapEntry)) (d Value)) (Result (List MapEntry))
  (match ks
    ((Nil) (Ok acc))
    ((Cons k rest)
      (let! ((v (map-get P xs k d))
             (acc2 (map-put P acc k v)))
        (map-take P acc2 rest xs d)))))

(define (eval-map-entries (P Program) (fuel Int) (env Env) (acc (List MapEntry)) (es (List ExprPair))) (Result (List MapEntry))
  (match es
    ((Nil) (Ok acc))
    ((Cons (ExprPair k v) rest)
      (let! ((kv (eval P fuel env k))
             (vv (eval P fuel env v))
             (acc2 (map-put P acc kv vv)))
        (eval-map-entries P fuel env acc2 rest)))))

(case eval (FiniteMap pairs default kt vt)
  (let! ((xs (eval-map-entries P fuel env (Nil) pairs))
         (d (eval P fuel env default)))
    (Ok (MapV (resolve (env-types env) kt) (resolve (env-types env) vt) xs d))))

(case eval (MapApply map key)
  (let! ((m (eval P fuel env map))
         (k (eval P fuel env key)))
    (match m
      ((MapV _ _ xs d) (map-get P xs k d))
      (_ (Stuck)))))

(case eval (MapUpdated map key value)
  (let! ((m (eval P fuel env map))
         (k (eval P fuel env key))
         (v (eval P fuel env value)))
    (match m
      ((MapV kt vt xs d)
        (let! ((ys (map-put P xs k v)))
          (Ok (MapV kt vt ys d))))
      (_ (Stuck)))))

(case eval (MapMerge mask map1 map2)
  (let! ((ks (eval-set P fuel env mask))
         (m1 (eval P fuel env map1))
         (m2 (eval P fuel env map2)))
    (match m1
      ((MapV _ _ xs d1)
        (match m2
          ((MapV kt vt ys d2)
            (let! ((rest (map-without P ys (set-elems ks)))
                   (zs (map-take P rest (set-elems ks) xs d1)))
              (Ok (MapV kt vt zs d2))))
          (_ (Stuck))))
      (_ (Stuck)))))
```

### Uninterpreted functions

A model gives each instantiation of an uninterpreted function as a function of
its arguments, whose body is evaluated in an environment that binds only its
parameters. Calling one doesn't consume fuel, as its body is fixed by the
model rather than by the program.

```inox-sem
(define (resolve (tenv (List TypeBinding)) (t Type)) Type
  (match t
    ((TypeParameter x)
      (match (lookup-type tenv x)
        ((Some (TypeBinding _ u uenv)) (resolve uenv u))
        ((None) t)))
    ((TupleType ts) (TupleType (resolve-all tenv ts)))
    ((SetType u) (SetType (resolve tenv u)))
    ((BagType u) (BagType (resolve tenv u)))
    ((MapType u w) (MapType (resolve tenv u) (resolve tenv w)))
    ((FunctionType ts u) (FunctionType (resolve-all tenv ts) (resolve tenv u)))
    ((ADTType s ts) (ADTType s (resolve-all tenv ts)))
    ((RefinementType x u prop) (RefinementType x (resolve tenv u) prop))
    ((PiType ps u) (PiType (resolve-params tenv ps) (resolve tenv u)))
    ((SigmaType ps u) (SigmaType (resolve-params tenv ps) (resolve tenv u)))
    (_ t)))

(define (resolve-params (tenv (List TypeBinding)) (ps (List Param))) (List Param)
  (match ps
    ((Nil) (Nil))
    ((Cons (Param x t) rest) (Cons (Param x (resolve tenv t)) (resolve-params tenv rest)))))

(define (resolve-all (tenv (List TypeBinding)) (ts (List Type))) (List Type)
  (match ts
    ((Nil) (Nil))
    ((Cons t rest) (Cons (resolve tenv t) (resolve-all tenv rest)))))

(define (lookup-interpretation (is (List Interpretation)) (f Id) (tps (List Type))) (Result Interpretation)
  (match is
    ((Nil) (Stuck))
    ((Cons i rest)
      (match i
        ((Interpretation g us _ _)
          (if (and (= f g) (= tps us)) (Ok i) (lookup-interpretation rest f tps)))))))

(case eval (UninterpretedCall f tps args)
  (let! ((vs (eval-list P fuel env args)))
    (if (<= fuel 0)
      (OutOfFuel)
      (match P
        ((Program _ _ _ is _)
          (let! ((i (lookup-interpretation is f (resolve-all (env-types env) tps))))
            (match i
              ((Interpretation _ _ params body)
                (let! ((bs (bind-all params vs)))
                  (eval P (- fuel 1) (Env (Nil) bs) body))))))))))
```

### Types

A value has a type when it has the type's shape, and is in the canonical form
that the operations above build: a real in lowest terms, a set, a bag or a map
without repeated elements or keys, a bag with positive multiplicities, a
character code below 2^16, and string characters at most `0x2FFFF`, as in
SMT-LIB. A value of an ADT type also satisfies its sort's invariant, and a
value of a refinement type its predicate, for some fuel. A type parameter
stands for the type it is bound to, and for the integers if it isn't bound.
`PropType`, the type of propositions, has the Booleans as values.

A value of a function type is a closure that, on every input of its parameter
types, evaluates to a value of its result type, for some fuel. Function values
are total, as the functions of SMT-LIB's models are: Inox's lambdas can get
stuck when applied, but quantifiers and free variables range over total
functions only.

Types are checked in an environment, as the predicates of refinements can
refer to variables. The dependent types bind their parameters in it: a value
of `(PiType params to)` is a closure that, on every input of the parameters'
types, evaluates to a value of `to` with the parameters bound to the input,
and a value of `(SigmaType params to)` is a tuple whose first elements have the
parameters' types, each with the previous ones bound, and whose last element
has type `to` with all of them bound. A type that a type parameter is bound to
is checked in the environment of its binding, without variables.

The quantifiers over values and fuel are in their own functions, so that
`has-type` itself is computable from them.

```inox-sem
(define (has-type (P Program) (env Env) (v Value) (t Type)) Bool
  :cases t)

(case has-type (IntegerType)
  (match v ((IntV _) true) (_ false)))

(case has-type (BooleanType)
  (match v ((BoolV _) true) (_ false)))

(case has-type (PropType)
  (match v ((BoolV _) true) (_ false)))

(case has-type (UnitType)
  (match v ((UnitV) true) (_ false)))

(case has-type (CharType)
  (match v ((CharV c) (and (<= 0 c) (< c 65536))) (_ false)))

(case has-type (RealType)
  (match v ((RealV n d) (and (< 0 d) (= (gcd (abs n) d) 1))) (_ false)))

(case has-type (StringType)
  (match v ((StringV cs) (valid-chars cs)) (_ false)))

(case has-type (BVType s w)
  (match v
    ((BVV s2 w2 x) (and (and (= s s2) (= w w2)) (and (<= 0 x) (< x (pow2 w)))))
    (_ false)))

(case has-type (FPType e s)
  (match v
    ((FPV e2 s2 x)
      (and (and (= e e2) (= s s2)) (and (and (<= 0 x) (< x (pow2 (+ e s)))) (= x (fp-canonical e s x)))))
    (_ false)))

(case has-type (RoundingModeType)
  (match v ((RoundingModeV _) true) (_ false)))

(case has-type (TypeParameter x)
  (match (lookup-type (env-types env) x)
    ((Some (TypeBinding _ u uenv)) (has-type P (Env uenv (Nil)) v u))
    ((None) (match v ((IntV _) true) (_ false)))))

(case has-type (TupleType ts)
  (match v ((TupleV vs) (have-types P env vs ts)) (_ false)))

(case has-type (SetType u)
  (match v
    ((SetV _ xs) (and (all-have-type P env xs u) (distinct-values P xs)))
    (_ false)))

(case has-type (BagType u)
  (match v
    ((BagV _ xs) (and (bag-has-type P env xs u) (distinct-values P (bag-elems xs))))
    (_ false)))

(case has-type (MapType u w)
  (match v
    ((MapV _ _ xs d)
      (and (has-type P env d w)
        (and (map-has-type P env xs u w) (distinct-values P (map-keys xs)))))
    (_ false)))

(case has-type (FunctionType from to)
  (match v
    ((ClosureV params _ _) (and (same-arity params from) (function-has-type P env v from to)))
    (_ false)))

(case has-type (PiType ps to)
  (match v
    ((ClosureV params _ _) (and (same-arity params (param-types ps)) (pi-has-type P env v ps to)))
    (_ false)))

(case has-type (SigmaType ps to)
  (match v
    ((TupleV vs) (sigma-has-type P env vs ps to))
    (_ false)))

(case has-type (ADTType s args)
  (match v
    ((ADTV c vs)
      (match P
        ((Program _ cs ss _ _)
          (match (lookup-ctor cs c)
            ((Ok (Constructor _ s2 fields))
              (match (lookup-sort ss s)
                ((Ok (Sort _ tparams inv))
                  (and (= s s2)
                    (and (params-have-types P (Env (bind-types tparams args (env-types env)) (Nil)) vs fields)
                      (match inv
                        ((None) true)
                        ((Some f) (invariant-holds P f args (env-types env) v))))))
                (_ false)))
            (_ false)))))
    (_ false)))

(case has-type (RefinementType x u prop)
  (and (has-type P env v u) (holds P (env-bind env x v) prop)))

(define (holds (P Program) (env Env) (prop Expr)) Bool
  (exists ((fuel Int))
    (= (eval P fuel env prop) (Ok (BoolV true)))))

(define (invariant-holds (P Program) (f Id) (args (List Type)) (tenv (List TypeBinding)) (v Value)) Bool
  (exists ((fuel Int))
    (= (call P fuel f args tenv (Cons v (Nil))) (Ok (BoolV true)))))

(define (function-has-type (P Program) (env Env) (f Value) (from (List Type)) (to Type)) Bool
  (forall ((vs (List Value)))
    (or (not (have-types P env vs from))
      (exists ((fuel Int) (r Value))
        (and (= (apply P fuel f vs) (Ok r)) (has-type P env r to))))))

(define (pi-has-type (P Program) (env Env) (f Value) (ps (List Param)) (to Type)) Bool
  (forall ((vs (List Value)))
    (or (not (params-have-types P env vs ps))
      (exists ((fuel Int) (r Value) (bs (List Binding)))
        (and (and (= (bind-all (param-ids ps) vs) (Ok bs)) (= (apply P fuel f vs) (Ok r)))
          (has-type P (Env (env-types env) (append-env bs (env-vars env))) r to))))))

(define (sigma-has-type (P Program) (env Env) (vs (List Value)) (ps (List Param)) (to Type)) Bool
  (match ps
    ((Nil) (match vs ((Cons v (Nil)) (has-type P env v to)) (_ false)))
    ((Cons (Param x t) more)
      (match vs
        ((Cons v rest) (and (has-type P env v t) (sigma-has-type P (env-bind env x v) rest more to)))
        (_ false)))))

(define (param-types (ps (List Param))) (List Type)
  (match ps
    ((Nil) (Nil))
    ((Cons (Param _ t) rest) (Cons t (param-types rest)))))

(define (have-types (P Program) (env Env) (vs (List Value)) (ts (List Type))) Bool
  (match vs
    ((Nil) (match ts ((Nil) true) (_ false)))
    ((Cons v rest)
      (match ts
        ((Nil) false)
        ((Cons t more) (and (has-type P env v t) (have-types P env rest more)))))))

;; each parameter is bound for the types of the next ones, which may depend on it
(define (params-have-types (P Program) (env Env) (vs (List Value)) (ps (List Param))) Bool
  (match vs
    ((Nil) (match ps ((Nil) true) (_ false)))
    ((Cons v rest)
      (match ps
        ((Nil) false)
        ((Cons (Param x t) more) (and (has-type P env v t) (params-have-types P (env-bind env x v) rest more)))))))

(define (all-have-type (P Program) (env Env) (vs (List Value)) (t Type)) Bool
  (match vs
    ((Nil) true)
    ((Cons v rest) (and (has-type P env v t) (all-have-type P env rest t)))))

(define (bag-has-type (P Program) (env Env) (xs (List BagEntry)) (t Type)) Bool
  (match xs
    ((Nil) true)
    ((Cons (BagEntry x n) rest) (and (and (< 0 n) (has-type P env x t)) (bag-has-type P env rest t)))))

(define (map-has-type (P Program) (env Env) (xs (List MapEntry)) (t Type) (u Type)) Bool
  (match xs
    ((Nil) true)
    ((Cons (MapEntry k v) rest)
      (and (and (has-type P env k t) (has-type P env v u)) (map-has-type P env rest t u)))))

(define (valid-chars (cs (List Int))) Bool
  (match cs
    ((Nil) true)
    ((Cons c rest) (and (and (<= 0 c) (<= c 196607)) (valid-chars rest)))))

(define (distinct-values (P Program) (xs (List Value))) Bool
  (match xs
    ((Nil) true)
    ((Cons x rest) (and (= (set-contains P rest x) (Ok false)) (distinct-values P rest)))))

(define (bag-elems (xs (List BagEntry))) (List Value)
  (match xs
    ((Nil) (Nil))
    ((Cons (BagEntry x _) rest) (Cons x (bag-elems rest)))))

(define (map-keys (xs (List MapEntry))) (List Value)
  (match xs
    ((Nil) (Nil))
    ((Cons (MapEntry k _) rest) (Cons k (map-keys rest)))))

(define (same-arity (ps (List Param)) (ts (List Type))) Bool
  (match ps
    ((Nil) (match ts ((Nil) true) (_ false)))
    ((Cons _ rest)
      (match ts
        ((Nil) false)
        ((Cons _ more) (same-arity rest more))))))
```

### Quantifiers

`(Forall params body)` holds when `body` evaluates to `true` for all the
values of the parameters' types, and is false as soon as it evaluates to
`false` for some. Otherwise, it runs out of fuel when the body does for some
values, and gets stuck when it gets stuck for some, or evaluates to something
else than a Boolean. More fuel never turns `false` or `Stuck` into anything
else, since `false` takes precedence.

```inox-sem
(define (instance (P Program) (fuel Int) (env Env) (params (List Param)) (vs (List Value)) (body Expr)) (Result Value)
  (match env
    ((Env tys vars)
      (let! ((bs (bind-all (param-ids params) vs)))
        (eval P fuel (Env tys (append-env bs vars)) body)))))

(define (forall-result (P Program) (fuel Int) (env Env) (params (List Param)) (body Expr)) (Result Value)
  (if (exists ((vs (List Value)))
        (and (params-have-types P env vs params)
          (= (instance P fuel env params vs body) (Ok (BoolV false)))))
    (Ok (BoolV false))
    (if (exists ((vs (List Value)))
          (and (params-have-types P env vs params)
            (= (instance P fuel env params vs body) (OutOfFuel))))
      (OutOfFuel)
      (if (forall ((vs (List Value)))
            (or (not (params-have-types P env vs params))
              (= (instance P fuel env params vs body) (Ok (BoolV true)))))
        (Ok (BoolV true))
        (Stuck)))))

(case eval (Forall params body)
  (forall-result P fuel env params body))
```

Under `ExtensionalEquality`, two closures are equal when, on every input of
the first one's parameter types, either neither has a value, or both have
equal values, for some fuel. They differ on an input on which only one of
them has a value, as in Inox.

```inox-sem
(define (closures-equal (P Program) (f Value) (g Value)) Bool
  (match f
    ((ClosureV params _ cenv)
      (forall ((vs (List Value)))
        (or (not (params-have-types P cenv vs params))
          (or
            (forall ((fuel Int) (a Value))
              (and (not (= (apply P fuel f vs) (Ok a))) (not (= (apply P fuel g vs) (Ok a)))))
            (exists ((fuel Int) (a Value) (b Value))
              (and (and (= (apply P fuel f vs) (Ok a)) (= (apply P fuel g vs) (Ok b)))
                (= (value-eq P a b) (Ok true))))))))
    (_ false)))
```

## The language of the blocks

Every backend translates each construct below, so the language stays small,
and the meaning of a generated definition should be plain from its text here.

A block holds S-expressions of three kinds:

- `(datatype Name (Ctor (field Type) ...) ...)` declares an algebraic datatype,
  and `(datatype (Name T ...) ...)` one with type parameters. Constructor and
  type names start with a capital letter.
- `(define (name (x Type) ...) Type body)` declares a function. Functions may
  call each other recursively, in any order.
- `(define (name (x Type) ...) Type :cases x)` declares a function defined by
  one `(case name (Ctor y ...) body)` per constructor of the type of `x`, which
  binds the constructor's fields to `y ...`. Every constructor needs exactly
  one case, and the cases may be spread over several blocks.

A semantics that extends this one, such as that of a language that compiles to
Inox, is written in its own file, which starts with `(import "path.md")`, the
path relative to it, and may then use two more forms:

- `(extend-datatype Name (Ctor (field Type) ...) ...)` adds constructors to a
  datatype of an imported file; a function defined by `:cases` on it then
  needs a case for each of them too. `eval` on expressions, `value-eq` on values
  and `has-type` on types are defined by `:cases`, so that an extension can
  add expressions, values and types.
- Extending `Result` adds outcomes of evaluation, which `let!` propagates as it
  does `Stuck` and `OutOfFuel`. They can't hold a value of the result's type.

Imports are read once each, before the file that imports them first, and only
by `Spec.load`. An extension only adds cases for the constructors it adds, and
changes none, so the expressions of the imported file keep their meaning.

The built-in types are `Int` (mathematical integers), `Bool`, and `Id`, the
names of variables, functions, constructors, sorts and fields, which can only
be compared for equality.

A body is a term:

- a variable, an integer numeral, `true` or `false`;
- `(Ctor t ...)`, a constructor applied to its fields, and `(f t ...)`, a call;
- `(let ((x t) ...) body)`, binding in sequence;
- `(let! ((x t) ...) body)`, where each `t` has a type `(Result T)`: if every
  `t` is `(Ok v)`, `body` with `x` bound to `v`, and otherwise the first
  `Stuck` or `OutOfFuel`, in sequence;
- `(if c t e)`;
- `(match t (pattern body) ...)`, where a pattern is `_`, a variable, `true`,
  `false`, or `(Ctor pattern ...)`, and the first matching case applies; the
  cases must cover every value;
- a built-in operation: `(+ a b)`, `(- a b)`, `(* a b)`, `(< a b)` and
  `(<= a b)` on integers; `(div a b)` and `(mod a b)`, the euclidean quotient
  and remainder for a nonzero `b`, with `0 <= (mod a b) < |b|`; `(and a b)`,
  `(or a b)` and `(not a)` on Booleans; and `(= a b)`, structural equality,
  on values of any type;
- `(forall ((x Type) ...) body)` and `(exists ((x Type) ...) body)`, where
  `body` is a Boolean term: whether it holds for all, or for some, values of
  the types.

A function whose body quantifies can't be computed. An executable backend
leaves it abstract, for an oracle to give, and the functions that call it
compute relative to that oracle. A proof checker defines it as written, unless
it is defined in terms of itself: the equality of two functions and the type
of a function evaluate their bodies, which compare and type values in turn.
Such a function is then also given by an oracle, of which the proofs assume
that it satisfies the function's definition.

Every function is total: its definition must terminate on all its arguments,
also on those it is never called with, since a proof checker only accepts a
recursion that it sees end. The helpers on non-negative integers therefore
stop on negative ones.
