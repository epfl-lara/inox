# Inox semantics

This file defines what an Inox expression means, independently of any proof
checker. Proofs of Inox's answers state their theorems against it: an UNSAT
answer means that no values of the free variables make the query evaluate to
`true`.

It is written to be read by people and by a code generator. Only the fenced
blocks tagged `inox-sem` are normative; the prose around them is commentary.
The generator (`inox.semantics.Codegen`) reads those blocks and writes the
semantics for each checker or tool that needs it: today, a Scala evaluator that
the tests compare with Inox's `RecursiveEvaluator`. The language of the blocks
is described at the end of this file.

This version covers the first-order core of Inox: integers, Booleans, unit,
algebraic datatypes (with their invariants), first-order recursive functions,
`let`, `if`, `assume` and `error`. Bit-vectors, lambdas, quantifiers, the
theories (strings, sets, bags, maps, reals) and uninterpreted functions come
later.

## Evaluation with fuel

Evaluation is a function `eval P fuel env e` of a program `P`, an amount of
fuel, an environment `env` that gives values to the free variables, and an
expression `e`. Its result is one of:

- `(Ok v)`: `e` evaluates to the value `v`;
- `Stuck`: evaluation fails, at an `error`, an assumption that doesn't hold,
  an invariant that doesn't hold, a division by zero, or a selector applied to
  a value built with another constructor;
- `OutOfFuel`: evaluation needs more fuel.

Fuel bounds the depth of nested function calls: a call evaluates the callee's
body with one less fuel, and nothing else consumes fuel. Inox has no
non-deterministic construct, so evaluation is a function, and more fuel never
changes a result other than `OutOfFuel`. An expression whose evaluation
diverges is one that runs out of fuel for every amount of fuel, and Inox
doesn't distinguish it from one that gets stuck: both have no value. The fuel
a call needs is its rank, the measure that Inox's termination clauses use.

Evaluation is the same under every type instantiation: types play no role in
it, so the expressions below leave them out.

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

A value is an integer, a Boolean, the unit value, or a constructor applied to
values. Two values are equal when they are structurally equal.

```inox-sem
(datatype Value
  (IntV (value Int))
  (BoolV (value Bool))
  (UnitV)
  (ADTV (ctor Id) (args (List Value))))
```

## Expressions and programs

The expressions of the core, with the fields of Inox's trees that evaluation
uses, in the same order (`inox.ast.Expressions`).

```inox-sem
(datatype Expr
  (Variable (id Id))
  (IntegerLiteral (value Int))
  (BooleanLiteral (value Bool))
  (UnitLiteral)
  (Let (id Id) (value Expr) (body Expr))
  (IfExpr (cond Expr) (thenn Expr) (elze Expr))
  (Assume (pred Expr) (body Expr))
  (Error)
  (FunctionInvocation (id Id) (args (List Expr)))
  (ADT (id Id) (args (List Expr)))
  (IsConstructor (expr Expr) (id Id))
  (ADTSelector (adt Expr) (selector Id))
  (Equals (lhs Expr) (rhs Expr))
  (And (exprs (List Expr)))
  (Or (exprs (List Expr)))
  (Implies (lhs Expr) (rhs Expr))
  (Not (expr Expr))
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
  (GreaterEquals (lhs Expr) (rhs Expr)))
```

A program gives each function its parameters and body, each constructor its
sort and fields, and each sort its invariant, a function of one argument, if
it has one.

```inox-sem
(datatype FunDef
  (FunDef (id Id) (params (List Id)) (body Expr)))

(datatype Constructor
  (Constructor (id Id) (sort Id) (fields (List Id))))

(datatype Sort
  (Sort (id Id) (invariant (Option Id))))

(datatype Program
  (Program (functions (List FunDef)) (constructors (List Constructor)) (sorts (List Sort))))

(datatype Binding
  (Binding (id Id) (value Value)))
```

## Looking things up

An environment is a list of bindings, the most recent first. A variable
without a binding, or a name that the program doesn't define, gets evaluation
stuck; a well-typed program never does.

```inox-sem
(define (lookup-var (env (List Binding)) (x Id)) (Result Value)
  (match env
    ((Nil) (Stuck))
    ((Cons (Binding y v) rest) (if (= x y) (Ok v) (lookup-var rest x)))))

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
        ((FunDef g _ _) (if (= f g) (Ok fd) (lookup-fun rest f)))))))

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
        ((Sort t _) (if (= s t) (Ok srt) (lookup-sort rest s)))))))

(define (select-field (fields (List Id)) (args (List Value)) (sel Id)) (Result Value)
  (match fields
    ((Nil) (Stuck))
    ((Cons f fs)
      (match args
        ((Nil) (Stuck))
        ((Cons v vs) (if (= f sel) (Ok v) (select-field fs vs sel)))))))
```

## Calls

A call evaluates its callee's body in an environment that binds only the
parameters, with one less fuel. Inox functions have no free variables other
than their parameters.

```inox-sem
(define (call (P Program) (fuel Int) (f Id) (vs (List Value))) (Result Value)
  (if (<= fuel 0)
    (OutOfFuel)
    (match P
      ((Program fs _ _)
        (let! ((fd (lookup-fun fs f)))
          (match fd
            ((FunDef _ params body)
              (let! ((env (bind-all params vs)))
                (eval P (- fuel 1) env body)))))))))
```

## Evaluation

Each Inox expression form has one equation. The arguments of an operation and
of a call are evaluated from left to right, and `And`, `Or` and `Implies`
evaluate their operands only as far as they need.

```inox-sem
(define (eval (P Program) (fuel Int) (env (List Binding)) (e Expr)) (Result Value)
  :cases e)

(define (eval-list (P Program) (fuel Int) (env (List Binding)) (es (List Expr))) (Result (List Value))
  (match es
    ((Nil) (Ok (Nil)))
    ((Cons e rest)
      (let! ((v (eval P fuel env e))
             (vs (eval-list P fuel env rest)))
        (Ok (Cons v vs))))))

(define (eval-int (P Program) (fuel Int) (env (List Binding)) (e Expr)) (Result Int)
  (let! ((v (eval P fuel env e)))
    (match v
      ((IntV i) (Ok i))
      (_ (Stuck)))))

(define (eval-bool (P Program) (fuel Int) (env (List Binding)) (e Expr)) (Result Bool)
  (let! ((v (eval P fuel env e)))
    (match v
      ((BoolV b) (Ok b))
      (_ (Stuck)))))
```

Variables, literals, `let`, `if`, `assume` and `error`:

```inox-sem
(case eval (Variable x)
  (lookup-var env x))

(case eval (IntegerLiteral i)
  (Ok (IntV i)))

(case eval (BooleanLiteral b)
  (Ok (BoolV b)))

(case eval (UnitLiteral)
  (Ok (UnitV)))

(case eval (Let x value body)
  (let! ((v (eval P fuel env value)))
    (eval P fuel (Cons (Binding x v) env) body)))

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
(case eval (FunctionInvocation f args)
  (let! ((vs (eval-list P fuel env args)))
    (call P fuel f vs)))
```

Building a value of a sort that has an invariant calls the invariant on it,
and gets stuck unless it holds. Testing a constructor never gets stuck, and
selecting a field of a value built with a constructor that doesn't have it
does.

```inox-sem
(case eval (ADT c args)
  (let! ((vs (eval-list P fuel env args)))
    (match P
      ((Program _ cs ss)
        (let! ((k (lookup-ctor cs c)))
          (match k
            ((Constructor _ s _)
              (let! ((srt (lookup-sort ss s)))
                (match srt
                  ((Sort _ (None)) (Ok (ADTV c vs)))
                  ((Sort _ (Some inv))
                    (let! ((holds (call P fuel inv (Cons (ADTV c vs) (Nil)))))
                      (match holds
                        ((BoolV true) (Ok (ADTV c vs)))
                        (_ (Stuck))))))))))))))

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
          ((Program _ cs _)
            (let! ((k (lookup-ctor cs c)))
              (match k
                ((Constructor _ _ fields) (select-field fields vs sel)))))))
      (_ (Stuck)))))
```

Equality compares values structurally.

```inox-sem
(case eval (Equals lhs rhs)
  (let! ((a (eval P fuel env lhs))
         (b (eval P fuel env rhs)))
    (Ok (BoolV (= a b)))))
```

The Boolean connectives:

```inox-sem
(define (eval-and (P Program) (fuel Int) (env (List Binding)) (es (List Expr))) (Result Value)
  (match es
    ((Nil) (Ok (BoolV true)))
    ((Cons e rest)
      (let! ((b (eval-bool P fuel env e)))
        (if b (eval-and P fuel env rest) (Ok (BoolV false)))))))

(define (eval-or (P Program) (fuel Int) (env (List Binding)) (es (List Expr))) (Result Value)
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

Integer arithmetic is on mathematical integers. Division is SMT-LIB's
euclidean division, and `Remainder` and `Modulo` both give its remainder, which
is never negative; all three get stuck on a zero divisor.

```inox-sem
(case eval (Plus lhs rhs)
  (let! ((a (eval-int P fuel env lhs)) (b (eval-int P fuel env rhs)))
    (Ok (IntV (+ a b)))))

(case eval (Minus lhs rhs)
  (let! ((a (eval-int P fuel env lhs)) (b (eval-int P fuel env rhs)))
    (Ok (IntV (- a b)))))

(case eval (UMinus expr)
  (let! ((a (eval-int P fuel env expr)))
    (Ok (IntV (- 0 a)))))

(case eval (Times lhs rhs)
  (let! ((a (eval-int P fuel env lhs)) (b (eval-int P fuel env rhs)))
    (Ok (IntV (* a b)))))

(case eval (Division lhs rhs)
  (let! ((a (eval-int P fuel env lhs)) (b (eval-int P fuel env rhs)))
    (if (= b 0) (Stuck) (Ok (IntV (div a b))))))

(case eval (Remainder lhs rhs)
  (let! ((a (eval-int P fuel env lhs)) (b (eval-int P fuel env rhs)))
    (if (= b 0) (Stuck) (Ok (IntV (mod a b))))))

(case eval (Modulo lhs rhs)
  (let! ((a (eval-int P fuel env lhs)) (b (eval-int P fuel env rhs)))
    (if (= b 0) (Stuck) (Ok (IntV (mod a b))))))

(case eval (LessThan lhs rhs)
  (let! ((a (eval-int P fuel env lhs)) (b (eval-int P fuel env rhs)))
    (Ok (BoolV (< a b)))))

(case eval (GreaterThan lhs rhs)
  (let! ((a (eval-int P fuel env lhs)) (b (eval-int P fuel env rhs)))
    (Ok (BoolV (< b a)))))

(case eval (LessEquals lhs rhs)
  (let! ((a (eval-int P fuel env lhs)) (b (eval-int P fuel env rhs)))
    (Ok (BoolV (<= a b)))))

(case eval (GreaterEquals lhs rhs)
  (let! ((a (eval-int P fuel env lhs)) (b (eval-int P fuel env rhs)))
    (Ok (BoolV (<= b a)))))
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
  on values of any type without functions.
