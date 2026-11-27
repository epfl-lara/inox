/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Sexp
import Inox.Encoded

/-!
# The input of a certificate in the semantics

The `input` section of a certificate holds the definitions of the program that the solver was
given and each constraint with the term that the encoders make of it, and the body of each
function after the encoders. This module reads them as expressions of the semantics
(`readExpr`), for the expressions that the theorem on the encoder of bags covers
(`Inox.Encoded.Encodes`), decides whether an encoded expression is what the encoder makes of
its expression (`encodesCheck`), and states what that gives for a certificate
(`covers_encoded`): where its constraints all evaluate to `true` in a program that has the
functions of the input, so do their encoded terms in a program that has their bodies after the
encoders and that defines the datatype of the encoder as the encoder does, on values of the
free variables that relate.

`covers` says of a certificate which of its constraints the theorem covers, and what the first
of the others has that isn't read.
-/

namespace Inox.Input

open Inox.Semantics Inox.Bags Inox.Encoded Logos

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

/-- A signature as the checks compute with it. -/
structure CSig where
  ctors : List (Id × Id × List (Id × Kind))
  funs : List (Id × List Id × Ty × List Kind × Kind)
  unint : List (Id × List Kind × Kind)
  flat : List Id

def CSig.sig (S : CSig) : Sig where
  ctors c := S.ctors.lookup c
  funs f := S.funs.lookup f
  unint f := S.unint.lookup f
  flat f := S.flat.contains f

/-- Every constructor of the sort `s` that has the field `sel` has it of the kind `k`. -/
def selOk (S : CSig) (s sel : Id) (k : Kind) : Bool :=
  S.ctors.all fun (_, s2, fs) => s2 != s ||
    match fieldKind fs sel with
    | none => true
    | some k' => kindEq k' k

theorem selOk_sound {S : CSig} {s sel : Id} {k : Kind} (h : selOk S s sel k = true) :
    ∀ c fs, S.sig.ctors c = some (s, fs) → ∀ k', fieldKind fs sel = some k' → k' = k := by
  intro c fs hc k' hk'
  have hmem : (c, s, fs) ∈ S.ctors := mem_of_lookup hc
  have := List.all_eq_true.1 h _ hmem
  simp [hk'] at this
  exact kindEq_eq this

theorem sizeOf_string_pos (c : String) : 0 < sizeOf c := by
  cases c; simp +arith

theorem sizeOf_expr_pos (e : Expr) : 0 < sizeOf e := by
  cases e <;> simp +arith

/-- Whether no constructor of the signature has a function in its fields. -/
def foSig (S : CSig) : Bool :=
  S.ctors.all fun (_, _, fs) => foKinds (fs.map Prod.snd)

theorem foSig_sound {S : CSig} (h : foSig S = true) : S.sig.fo := by
  intro c s fs hc
  have hmem : (c, s, fs) ∈ S.ctors := mem_of_lookup hc
  simpa using List.all_eq_true.1 h _ hmem

/-- The variables that a function keeps: those that have the kind that they are listed with. -/
def keep (Γ : List (Id × Kind)) : List (Id × Kind) :=
  Γ.filter fun p => match Γ.lookup p.1 with | some k => kindEq k p.2 | none => false

theorem keep_sound {Γ : List (Id × Kind)} : ∀ p ∈ keep Γ, Γ.lookup p.1 = some p.2 := by
  intro p hp
  have h := (List.mem_filter.1 hp).2
  split at h
  · next k hl => rw [hl, kindEq_eq h]
  · cases h

/-- Whether `e'` is what the encoder of bags makes of `e`, an expression of the kind `k`.
`g` gives the kinds of subexpressions where the check needs one: the check holds for any `g`,
and accepts more with one that gives the right kinds. -/
def encodesCheck (N : Names) (S : CSig) (Te : Ty) (g : List (Id × Kind) → Expr → Kind) :
    List (Id × Kind) → Expr → Expr → Kind → Bool → Bool
  | Γ, .Variable x, .Variable y, k, _ =>
    x == y && (match Γ.lookup x with | some k' => kindEq k' k | none => false)
  | _, .IntegerLiteral n, .IntegerLiteral m, .int, _ => n == m
  | _, .BooleanLiteral b, .BooleanLiteral c, .bool, _ => b == c
  | Γ, .Plus a b, .Plus a' b', .int, u =>
    encodesCheck N S Te g Γ a a' .int u && encodesCheck N S Te g Γ b b' .int u
  | Γ, .Minus a b, .Minus a' b', .int, u =>
    encodesCheck N S Te g Γ a a' .int u && encodesCheck N S Te g Γ b b' .int u
  | Γ, .LessThan a b, .LessThan a' b', .bool, u =>
    encodesCheck N S Te g Γ a a' .int u && encodesCheck N S Te g Γ b b' .int u
  | Γ, .GreaterThan a b, .GreaterThan a' b', .bool, u =>
    encodesCheck N S Te g Γ a a' .int u && encodesCheck N S Te g Γ b b' .int u
  | Γ, .LessEquals a b, .LessEquals a' b', .bool, u =>
    encodesCheck N S Te g Γ a a' .int u && encodesCheck N S Te g Γ b b' .int u
  | Γ, .GreaterEquals a b, .GreaterEquals a' b', .bool, u =>
    encodesCheck N S Te g Γ a a' .int u && encodesCheck N S Te g Γ b b' .int u
  | Γ, .Equals a b, .Equals a' b', .bool, u =>
    foKind (g Γ a) && foSig S && encodesCheck N S Te g Γ a a' (g Γ a) u &&
      encodesCheck N S Te g Γ b b' (g Γ a) u
  | Γ, .Not a, .Not a', .bool, u => encodesCheck N S Te g Γ a a' .bool u
  | _, .And [], .And [], .bool, _ => true
  | Γ, .And (a :: as), .And (a' :: as'), .bool, u =>
    encodesCheck N S Te g Γ a a' .bool u && encodesCheck N S Te g Γ (.And as) (.And as') .bool u
  | _, .Or [], .Or [], .bool, _ => true
  | Γ, .Or (a :: as), .Or (a' :: as'), .bool, u =>
    encodesCheck N S Te g Γ a a' .bool u && encodesCheck N S Te g Γ (.Or as) (.Or as') .bool u
  | Γ, .Implies a b, .Implies a' b', .bool, u =>
    encodesCheck N S Te g Γ a a' .bool u && encodesCheck N S Te g Γ b b' .bool u
  | Γ, .IfExpr c a b, .IfExpr c' a' b', k, u =>
    encodesCheck N S Te g Γ c c' .bool u && encodesCheck N S Te g Γ a a' k u &&
      encodesCheck N S Te g Γ b b' k u
  | Γ, .Let x a b, .Let y a' b', k, u =>
    x == y && encodesCheck N S Te g Γ a a' (g Γ a) u &&
      encodesCheck N S Te g ((x, g Γ a) :: Γ) b b' k u
  | Γ, .Assume p b, .Assume p' b', k, u =>
    encodesCheck N S Te g Γ p p' .bool u && encodesCheck N S Te g Γ b b' k u
  | _, .FiniteBag [] _, .ADT c [t] [], .bag, false => c == N.leaf && sameTy t Te
  | Γ, .BagAdd b e,
      .ADT c [t] [.IntegerLiteral op, b', .ADT c2 [t2] [e', .IntegerLiteral one]], .bag, false =>
    c == N.node && sameTy t Te && op == 0 && c2 == N.elem && sameTy t2 Te && one == 1 &&
      encodesCheck N S Te g Γ b b' .bag false && encodesCheck N S Te g Γ e e' .elem false
  | Γ, .BagUnion a b, .ADT c [t] [.IntegerLiteral op, a', b'], .bag, false =>
    c == N.node && sameTy t Te && op == 0 &&
      encodesCheck N S Te g Γ a a' .bag false && encodesCheck N S Te g Γ b b' .bag false
  | Γ, .BagDifference a b, .ADT c [t] [.IntegerLiteral op, a', b'], .bag, false =>
    c == N.node && sameTy t Te && op == 1 &&
      encodesCheck N S Te g Γ a a' .bag false && encodesCheck N S Te g Γ b b' .bag false
  | Γ, .BagIntersection a b, .ADT c [t] [.IntegerLiteral op, a', b'], .bag, false =>
    c == N.node && sameTy t Te && op == 2 &&
      encodesCheck N S Te g Γ a a' .bag false && encodesCheck N S Te g Γ b b' .bag false
  | Γ, .MultiplicityInBag e b, .FunctionInvocation f [t] [b', e'], .int, false =>
    f == N.get && sameTy t Te && encodesCheck N S Te g Γ e e' .elem false &&
      encodesCheck N S Te g Γ b b' .bag false
  | _, .Tuple [], .Tuple [], .tuple [], _ => true
  | Γ, .Tuple (e :: es), .Tuple (e' :: es'), .tuple (k :: ks), u =>
    encodesCheck N S Te g Γ e e' k u &&
      encodesCheck N S Te g Γ (.Tuple es) (.Tuple es') (.tuple ks) u
  | Γ, .TupleSelect t i, .TupleSelect t' j, k, u =>
    i == j && (match g Γ t with
      | .tuple ks =>
        (match nthKind ks i with | some k' => kindEq k' k | none => false) &&
          encodesCheck N S Te g Γ t t' (.tuple ks) u
      | _ => false)
  | Γ, .ADT c _ es, .ADT c' _ es', .adt s, u =>
    c == c' && (match S.ctors.lookup c with
      | some (s2, fs) =>
        s == s2 && encodesCheck N S Te g Γ (.Tuple es) (.Tuple es') (.tuple (fs.map Prod.snd)) u
      | none => false)
  | Γ, .ADTSelector e sel, .ADTSelector e' sel', k, u =>
    sel == sel' && (match g Γ e with
      | .adt s => selOk S s sel k && encodesCheck N S Te g Γ e e' (.adt s) u
      | _ => false)
  | Γ, .IsConstructor e c, .IsConstructor e' c', .bool, u =>
    c == c' && (match g Γ e with
      | .adt s => encodesCheck N S Te g Γ e e' (.adt s) u
      | _ => false)
  | Γ, .FunctionInvocation f _ es, .FunctionInvocation f' tps' es', k, u =>
    (!u || S.flat.contains f) && f == f' && (match S.funs.lookup f, tps' with
      | some ([A], .TypeParameter B, ks, k2), [t] =>
        A == B && sameTy t Te && kindEq k2 k &&
          encodesCheck N S Te g Γ (.Tuple es) (.Tuple es') (.tuple ks) u
      | some ([], _, ks, k2), [] =>
        kindEq k2 k && encodesCheck N S Te g Γ (.Tuple es) (.Tuple es') (.tuple ks) u
      | _, _ => false)
  | Γ, .Lambda ps body, .Lambda ps' body', .fn ks k, u =>
    decide (param_ids ps = param_ids ps') &&
      encodesCheck N S Te g ((param_ids ps).zip ks ++ keep Γ) body body' k true
  | Γ, .Application callee es, .Application callee' es', k, u =>
    (match g Γ callee with
      | .fn ks k2 =>
        kindEq k2 k && encodesCheck N S Te g Γ callee callee' (.fn ks k2) u &&
          encodesCheck N S Te g Γ (.Tuple es) (.Tuple es') (.tuple ks) u
      | _ => false)
  | Γ, .UninterpretedCall f [] es, .UninterpretedCall f' [] es', k, u =>
    (!u || S.flat.contains f) && f == f' && (match S.unint.lookup f with
      | some (ks, k2) =>
        kindEq k2 k && encodesCheck N S Te g Γ (.Tuple es) (.Tuple es') (.tuple ks) u
      | none => false)
  | _, .Error, .Error, _, _ => true
  | Γ, .Forall ps body, .Forall ps' body', .bool, _ =>
    (match paramKinds ps, paramKinds ps' with
      | some ks, some ks' => kindsEq ks ks' && decide (param_ids ps = param_ids ps') &&
          encodesCheck N S Te g ((param_ids ps).zip ks ++ Γ) body body' .bool true
      | _, _ => false)
  | _, _, _, _, _ => false
termination_by _ e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := sizeOf_string_pos c; omega)
    | (have := sizeOf_string_pos f; omega)
    | (have := sizeOf_expr_pos callee; omega)

theorem encodesCheck_sound {N : Names} {S : CSig} {Te : Ty}
    {g : List (Id × Kind) → Expr → Kind} {Γ : List (Id × Kind)} {e e' : Expr} {k : Kind}
    {u : Bool} : encodesCheck N S Te g Γ e e' k u = true →
      Encodes N S.sig Te (fun x => Γ.lookup x) e e' k u := by
  fun_induction encodesCheck N S Te g Γ e e' k u <;> intro h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hk⟩ := h
    split at hk
    · next k' hl => cases kindEq_eq hk; exact .var _ _ hl
    · cases hk
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
  · next iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .eq h.1.1.1 (foSig_sound h.1.1.2) (iha h.1.2) (ihb h.2)
  · next iha => exact .not (iha h)
  · exact .andNil
  · next iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .andCons (iha h.1) (ihb h.2)
  · exact .orNil
  · next iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .orCons (iha h.1) (ihb h.2)
  · next iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .implies (iha h.1) (ihb h.2)
  · next ihc iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .ite (ihc h.1.1) (iha h.1.2) (ihb h.2)
  · next iha ihb =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, ha⟩, hb⟩ := h
    simp only [lookup_cons] at ihb
    exact .let_ _ (iha ha) (ihb hb)
  · next iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .assume (iha h.1) (ihb h.2)
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
  · exact .tupleNil
  · next iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .tupleCons (iha h.1) (ihb h.2)
  · next ih =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    split at h
    · next ks hg =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨hk, ht⟩ := h
      split at hk
      · next k' hn => cases kindEq_eq hk; exact .tupleSelect _ (ih ks ht) hn
      · cases hk
    · cases h
  · next ih =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    split at h
    · next s2 fs hl =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, ha⟩ := h
      exact .adt _ _ hl (ih fs ha)
    · cases h
  · next ih =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    split at h
    · next s hg =>
      simp only [Bool.and_eq_true] at h
      exact .sel _ (ih s h.2) (selOk_sound h.1)
    · cases h
  · next ih =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    split at h
    · next s hg => exact .isCtor _ (ih s h)
    · cases h
  · next ih =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hu, rfl⟩, h⟩ := h
    split at h
    · next A B ks k2 t hl =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨rfl, ht⟩, hk⟩, ha⟩ := h
      cases sameTy_eq ht
      cases kindEq_eq hk
      exact .callPoly _ hl (fun h1 => by subst h1; simpa [CSig.sig] using hu) (ih ks ha)
    · next Tf ks k2 hl =>
      simp only [Bool.and_eq_true] at h
      cases kindEq_eq h.1
      exact .callMono _ hl (fun h1 => by subst h1; simpa [CSig.sig] using hu) (ih ks h.2)
    · cases h
  · next ih =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact .lambda _ (fun p hp => keep_sound p hp) h.1 (ih h.2)
  · next ihf iha =>
    simp only [Bool.and_eq_true] at h
    cases kindEq_eq h.1.1
    exact .app (ihf h.1.2) (iha h.2)
  · cases h
  · next ih =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hu, rfl⟩, h⟩ := h
    split at h
    · next ks k2 hl =>
      simp only [Bool.and_eq_true] at h
      cases kindEq_eq h.1
      exact .uninterp hl (fun h1 => by subst h1; simpa [CSig.sig] using hu) (ih ks h.2)
    · cases h
  · exact .error _
  · next ih =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hks, hp⟩, hb⟩ := h
    cases kindsEq_eq hks
    have hb := ih hb
    simp only [List.lookup_append] at hb
    exact .forall_ (by assumption) (by assumption) hp hb
  · cases h
  · cases h

/-! ## Reading the input -/

instance : Inhabited Kind := ⟨.int⟩

/-- The text of a string literal, up to a `[`. -/
def described (d : String) : String :=
  String.ofList (((d.toList.drop 1).dropLast).takeWhile (· != '['))

/-- A table of symbols: each symbol with its kind and what it is described with. -/
structure Table where
  rows : List (String × String × List String)

def Table.of (symbols : List Sexp) : Table :=
  ⟨symbols.filterMap fun
    | .expr (.atom a :: .atom kind :: rest) =>
      some (a, kind, rest.filterMap fun | .atom d => some (described d) | _ => none)
    | _ => none⟩

def Table.kind (t : Table) (a : String) : String := ((t.rows.lookup a).map (·.1)).getD ""

/-- The identifier of a constructor, a sort or a function, and the symbol itself otherwise. -/
def Table.id (t : Table) (a : String) : Id :=
  match t.rows.lookup a with
  | some (kind, d :: _) => if kind == "variable" then a else d
  | _ => a

/-- The name of the field of a selector: its constructor and its index. -/
def Table.field (t : Table) (a : String) : Id :=
  match t.rows.lookup a with
  | some (_, c :: rest) => c ++ "." ++ rest.getLast!
  | _ => a

/-- What an expression is read with: the table of its symbols and the sort of the elements. -/
structure Ctx where
  table : Table
  elem : String
  /-- Whether the elements are integers, which are then of the kind of integers. -/
  ints : Bool

/-- The kind of a sort of the input. -/
def kindOfSort (c : Ctx) : Nat → Sexp → Except String Kind
  | 0, _ => .error "a sort too deep"
  | n + 1, s =>
    match s with
    | .atom "Int" => .ok .int
    | .atom "Bool" => .ok .bool
    | .atom a =>
      if a == c.elem then .ok (if c.ints then .int else .elem) else .error s!"the sort {a}"
    | .expr [.atom "Bag", x] =>
      if x == .atom c.elem then .ok .bag else .error "a bag of other than elements"
    | .expr (.atom "Tuple" :: xs) => do pure (.tuple (← xs.mapM (kindOfSort c n)))
    -- the kind of a refinement is that of its base
    | .expr (.atom "!" :: base :: _) => kindOfSort c n base
    | .expr (.atom "->" :: xs) => do
      let ks ← xs.mapM (kindOfSort c n)
      match ks.reverse with
      | k :: rest => pure (.fn rest.reverse k)
      | [] => .error "a sort"
    | .expr (.atom a :: xs) =>
      if c.table.kind a == "sort" && xs.all (· == .atom c.elem) then .ok (.adt (c.table.id a))
      else .error s!"the sort {a}"
    | _ => .error "a sort"

/-- The type that a sort is read as, where the checks compare types: `Int` and the atoms. -/
def readTy : Sexp → Ty
  | .atom "Int" => .IntegerType
  | .atom a => .TypeParameter a
  | _ => .UnitType

mutual
/-- The type of the values of a kind, with `elem` the type parameter of the elements. -/
def kindTy (elem : Id) : Kind → Ty
  | .elem => .TypeParameter elem
  | .int => .IntegerType
  | .bool => .BooleanType
  | .bag => .BagType (.TypeParameter elem)
  | .adt s => .ADTType s [.TypeParameter elem]
  | .tuple ks => .TupleType (kindTys elem ks)
  | .fn ks k => .FunctionType (kindTys elem ks) (kindTy elem k)
def kindTys (elem : Id) : List Kind → List Ty
  | [] => []
  | k :: ks => kindTy elem k :: kindTys elem ks
end

/-- The kind of the values of a type that `kindTy` gives. -/
partial def tyKind : Ty → Kind
  | .IntegerType => .int
  | .BooleanType => .bool
  | .BagType _ => .bag
  | .ADTType s _ => .adt s
  | .TupleType ts => .tuple (ts.map tyKind)
  | .FunctionType ts t => .fn (ts.map tyKind) (tyKind t)
  | _ => .elem

/-- The expression that `s` reads as, or what it has that isn't read. -/
def readExpr (c : Ctx) : Nat → Sexp → Except String Expr
  | 0, _ => .error "a term too deep"
  | n + 1, s =>
    match s with
    | .atom a =>
      if !a.isEmpty && a.all Char.isDigit then .ok (.IntegerLiteral a.toNat!)
      else if a == "true" then .ok (.BooleanLiteral true)
      else if a == "false" then .ok (.BooleanLiteral false)
      else if c.table.kind a == "uninterpreted" then .ok (.UninterpretedCall (c.table.id a) [] [])
      else if c.table.kind a == "function" then .ok (.FunctionInvocation (c.table.id a) [] [])
      else if a.contains '!' then .ok (.Variable a)
      else .error a
    | .expr [.atom "not", a] => do pure (.Not (← readExpr c n a))
    | .expr [.atom "+", a, b] => do pure (.Plus (← readExpr c n a) (← readExpr c n b))
    | .expr [.atom "-", a, b] => do pure (.Minus (← readExpr c n a) (← readExpr c n b))
    | .expr [.atom "<", a, b] => do pure (.LessThan (← readExpr c n a) (← readExpr c n b))
    | .expr [.atom ">", a, b] => do pure (.GreaterThan (← readExpr c n a) (← readExpr c n b))
    | .expr [.atom "<=", a, b] => do pure (.LessEquals (← readExpr c n a) (← readExpr c n b))
    | .expr [.atom ">=", a, b] => do
      pure (.GreaterEquals (← readExpr c n a) (← readExpr c n b))
    | .expr [.atom "=", a, b] => do pure (.Equals (← readExpr c n a) (← readExpr c n b))
    | .expr (.atom "and" :: as) => do pure (.And (← as.mapM (readExpr c n)))
    | .expr (.atom "or" :: as) => do pure (.Or (← as.mapM (readExpr c n)))
    | .expr [.atom "=>", a, b] => do pure (.Implies (← readExpr c n a) (← readExpr c n b))
    | .expr [.atom "ite", i, a, b] => do
      pure (.IfExpr (← readExpr c n i) (← readExpr c n a) (← readExpr c n b))
    | .expr [.atom "let", .expr [.expr [.atom x, a]], b] => do
      pure (.Let x (← readExpr c n a) (← readExpr c n b))
    | .expr [.atom "assume", p, b] => do pure (.Assume (← readExpr c n p) (← readExpr c n b))
    | .expr [.atom "as", .atom "bag.empty", t] => pure (.FiniteBag [] (readTy t))
    | .expr [.atom "bag.insert", b, e] => do
      pure (.BagAdd (← readExpr c n b) (← readExpr c n e))
    | .expr [.atom "bag.union", a, b] => do
      pure (.BagUnion (← readExpr c n a) (← readExpr c n b))
    | .expr [.atom "bag.difference", a, b] => do
      pure (.BagDifference (← readExpr c n a) (← readExpr c n b))
    | .expr [.atom "bag.intersection", a, b] => do
      pure (.BagIntersection (← readExpr c n a) (← readExpr c n b))
    | .expr [.atom "bag.multiplicity", e, b] => do
      pure (.MultiplicityInBag (← readExpr c n e) (← readExpr c n b))
    | .expr [.expr [.atom "as", .expr [.atom "_", .atom "is", .atom k], _], e] => do
      pure (.IsConstructor (← readExpr c n e) (c.table.id k))
    | .expr [.expr [.atom "as", .expr [.atom "_", .atom "tuple.select", .atom i], _], e] => do
      pure (.TupleSelect (← readExpr c n e) (i.toNat! + 1))
    | .expr (.expr [.atom "as", .atom "tuple", _] :: args) => do
      pure (.Tuple (← args.mapM (readExpr c n)))
    | .expr [.atom "lambda", .expr ps, b] => do
      let ps ← ps.mapM fun
        | .expr [.atom x, .expr (.atom "!" :: _)] => .error s!"the refined parameter {x}"
        | .expr [.atom x, sort] => do pure (Param.Param x (kindTy c.elem (← kindOfSort c n sort)))
        | _ => .error "a parameter"
      pure (.Lambda ps (← readExpr c n b))
    | .expr [.atom "forall", .expr ps, b] => do
      let ps ← ps.mapM fun
        | .expr [.atom x, .expr (.atom "!" :: _)] => .error s!"the refined parameter {x}"
        | .expr [.atom x, sort] => do pure (Param.Param x (kindTy c.elem (← kindOfSort c n sort)))
        | _ => .error "a parameter"
      pure (.Forall ps (← readExpr c n b))
    | .expr (.expr [.atom "as", .atom "@", _] :: f :: args) => do
      pure (.Application (← readExpr c n f) (← args.mapM (readExpr c n)))
    | .expr [.atom "as", .atom k, .expr (.atom _ :: ts)] =>
      if c.table.kind k == "constructor" then pure (.ADT (c.table.id k) (ts.map readTy) [])
      else .error (c.table.kind k ++ " " ++ k)
    | .expr (.expr [.atom "as", .atom k, .expr ts] :: args) => do
      let args ← args.mapM (readExpr c n)
      match c.table.kind k, args with
      | "constructor", _ => pure (.ADT (c.table.id k) ((ts.drop 1).map readTy) args)
      | "selector", [e] => pure (.ADTSelector e (c.table.field k))
      | "function", _ => pure (.FunctionInvocation (c.table.id k) (ts.map readTy) args)
      | kind, _ => .error (kind ++ " " ++ k)
    | .expr [.atom "error", _, _] => pure .Error
    | .expr (.atom k :: args) =>
      if c.table.kind k == "function" then do
        pure (.FunctionInvocation (c.table.id k) [] (← args.mapM (readExpr c n)))
      else if c.table.kind k == "uninterpreted" then do
        pure (.UninterpretedCall (c.table.id k) [] (← args.mapM (readExpr c n)))
      else .error k
    | .expr (.expr [.atom "as", .atom a, _] :: _) => .error a
    | .expr (.expr [.atom "as", .expr (.atom "_" :: .atom a :: _), _] :: _) => .error a
    | _ => .error "a term"

/-- The kind of a field of some constructor of the sort `s`. -/
def fieldOf (S : CSig) (s sel : Id) : Option Kind :=
  S.ctors.findSome? fun (_, s2, fs) => if s2 == s then fieldKind fs sel else none

/-- The kind that an expression of the input has, where it is of the fragment. -/
partial def kindOf (S : CSig) (Γ : List (Id × Kind)) : Expr → Kind
  | .Variable x => (Γ.lookup x).getD .int
  | .BooleanLiteral _ | .LessThan _ _ | .GreaterThan _ _ | .LessEquals _ _
  | .GreaterEquals _ _ | .Equals _ _ | .Not _ | .And _ | .Or _ | .Implies _ _
  | .IsConstructor _ _ | .Forall _ _ => .bool
  | .FiniteBag _ _ | .BagAdd _ _ | .BagUnion _ _ | .BagDifference _ _
  | .BagIntersection _ _ => .bag
  | .IfExpr _ a b => match a with | .Error => kindOf S Γ b | _ => kindOf S Γ a
  | .Let x a b => kindOf S ((x, kindOf S Γ a) :: Γ) b
  | .Assume _ b => kindOf S Γ b
  | .Tuple es => .tuple (es.map (kindOf S Γ))
  | .TupleSelect t i =>
    match kindOf S Γ t with
    | .tuple ks => (nthKind ks i).getD .int
    | _ => .int
  | .ADT c _ _ => .adt (((S.ctors.lookup c).map (·.1)).getD "")
  | .ADTSelector e sel =>
    match kindOf S Γ e with
    | .adt s => (fieldOf S s sel).getD .int
    | _ => .int
  | .FunctionInvocation f _ _ => ((S.funs.lookup f).map (·.2.2.2)).getD .int
  | .UninterpretedCall f _ _ => ((S.unint.lookup f).map (·.2)).getD .int
  | .Lambda ps b =>
    let ks := ps.map fun | .Param _ t => tyKind t
    .fn ks (kindOf S ((param_ids ps).zip ks ++ Γ) b)
  | .Application f _ =>
    match kindOf S Γ f with
    | .fn _ k => k
    | _ => .int
  | _ => .int

/-- The sections of a certificate of the given name. -/
def sectionOf (certificate : Sexp) (name : String) : List Sexp :=
  match certificate with
  | .expr sections => sections.flatMap fun
    | .expr (.atom a :: rest) => if a == name then rest else []
    | _ => []
  | _ => []

/-- The constructors that the declarations of datatypes of the input give, with their sort
and the names and the kinds of their fields. -/
def ctorsOf (t : Table) (ints : Bool) (definitions : List Sexp) :
    List (Id × Id × List (Id × Kind)) :=
  definitions.flatMap fun
    | .expr [.atom "declare-datatypes", .expr [.expr [.atom sort, _]], .expr [decl]] =>
      let (elem, ctors) := match decl with
        | .expr [.atom "par", .expr [.atom a], .expr ctors] => (a, ctors)
        | .expr ctors => ("", ctors)
        | _ => ("", [])
      ctors.filterMap fun
        | .expr (.atom k :: fields) =>
          let fs := fields.mapM fun
            | .expr [.atom f, sort] =>
              match kindOfSort ⟨t, elem, ints⟩ 100 sort with
              | .ok kind => some (t.field f, kind)
              | .error _ => none
            | _ => none
          fs.map fun fs => (t.id k, t.id sort, fs)
        | _ => none
    | _ => []

/-- A function of the input as it is read: its name, its type parameters, the type of the
elements in its body, the kinds of its parameters and of its result, its parameters and its
body. -/
structure Fun where
  name : Id
  tparams : List Id
  elem : Ty
  kinds : List Kind
  kind : Kind
  params : List Id
  body : Sexp
  ctx : Ctx

/-- The entry of a function in a signature. -/
def Fun.entry (f : Fun) : Id × List Id × Ty × List Kind × Kind :=
  (f.name, f.tparams, f.elem, f.kinds, f.kind)

/-- The functions that the definitions of the input give, where their sorts have kinds. -/
def funsOf (t : Table) (ints : Bool) (top : String) (definitions : List Sexp) : List Fun :=
  definitions.filterMap fun d =>
    let read (tparams : List String) (elem : String) (f : String) (params : List Sexp)
        (ret body : Sexp) : Option Fun :=
      let c : Ctx := ⟨t, elem, ints⟩
      match params.mapM fun
        | .expr [.atom p, sort] => (kindOfSort c 100 sort).toOption.map fun k => (p, k)
        | _ => none, (kindOfSort c 100 ret).toOption with
      | some ps, some k =>
        some ⟨t.id f, tparams, readTy (.atom elem), ps.map (·.2), k, ps.map (·.1), body, c⟩
      | _, _ => none
    match d with
    | .expr [.atom def_, .expr [.atom "par", .expr [.atom a],
        .expr [.atom f, .expr params, ret, body]]] =>
      if def_ == "define-fun" || def_ == "define-fun-rec" then read [a] a f params ret body
      else none
    | .expr [.atom def_, .atom f, .expr params, ret, body] =>
      if def_ == "define-fun" || def_ == "define-fun-rec" then read [] top f params ret body
      else none
    | _ => none

/-- The body of each function after the encoders, as the `function` lines of the input give
it, by the symbol of the function. -/
def encodedBodies (input : List Sexp) : List (String × Sexp) :=
  input.filterMap fun
    | .expr (.atom "function" :: head :: .expr [.atom "encoded", body] :: _) =>
      let name := match head with
        | .expr (.expr [.atom "as", .atom f, _] :: _) => some f
        | .expr [.atom "as", .atom f, _] => some f
        | .expr (.atom f :: _) => some f
        | .atom f => some f
        | _ => none
      name.map fun f => (f, body)
    | _ => none

/-- The first sort of a free variable of the input that is a symbol without a declaration:
the type parameter that the elements are of. -/
def elemOf (symbols : List Sexp) : String :=
  let rec atoms : Nat → Sexp → List String
    | 0, _ => []
    | _ + 1, .atom a => [a]
    | n + 1, .expr l => l.flatMap (atoms n)
  let t := Table.of symbols
  let sorts := symbols.flatMap fun
    | .expr [.atom _, .atom "variable", _, _, sort] => atoms 100 sort
    | _ => []
  (sorts.find? fun a => a.contains '!' && t.kind a == "").getD ""

/-- The names of the encoder: the identifiers of its constructors and of `get` in the table
of the encoded program. The other names are not in the terms that are checked. -/
def namesOf (t : Table) : Names :=
  let find (kind name : String) :=
    ((t.rows.find? fun (_, k, ds) => k == kind &&
      (ds.head?.map fun d => String.ofList (d.toList.takeWhile (· != '$'))) == some name).bind
        fun (_, _, ds) => ds.head?).getD name
  { bag := "Bag", node := find "constructor" "Node", elem := find "constructor" "Elem",
    leaf := find "constructor" "Leaf", op := "op", left := "left", right := "right",
    key := "key", value := "value", get := find "function" "get", T := "T", b := "b",
    x := "x", v1 := "v1", v2 := "v2" }

/-- What `covers_encoded` is about for a certificate: the names of the encoder, the signature
of the input, its functions with their bodies in the input and after the encoders, the type
of the elements and the kinds of the free variables of the constraints, and the constraints
that are read and that the check accepts, with their encoded terms. It also gives the number
of constraints, and what the first that isn't covered has that isn't read. -/
structure Coverage where
  names : Names
  sig : CSig
  defs : List (Id × List Id × Expr × Expr)
  elem : Ty
  vars : List (Id × Kind)
  covered : List (Expr × Expr)
  constraints : Nat
  first : Option String

/-- Whether the body after the encoders of each function of the signature is what the
encoder makes of its body in the input. -/
def defsCheck (N : Names) (S : CSig) (defs : List (Id × List Id × Expr × Expr)) : Bool :=
  S.funs.all fun (f, _, Tf, ks, k) =>
    match defs.lookup f with
    | some (params, body, body') =>
      encodesCheck N S Tf (kindOf S) (params.zip ks) body body' k (S.flat.contains f)
    | none => false

def Coverage.none (n : Nat) (why : String) : Coverage :=
  { names := namesOf ⟨[]⟩, sig := ⟨[], [], [], []⟩, defs := [], elem := .UnitType,
    vars := [],
    covered := [], constraints := n, first := some why }

/-- What the checks give of a coverage. -/
def Coverage.Ok (C : Coverage) : Prop :=
  defsCheck C.names C.sig C.defs = true ∧
    ∀ p ∈ C.covered,
      encodesCheck C.names C.sig C.elem (kindOf C.sig) C.vars p.1 p.2 .bool false = true

/-- The coverage of the constraints among `pairs` that the check accepts, where the functions
are checked. -/
def gate (N : Names) (S : CSig) (defs : List (Id × List Id × Expr × Expr)) (Te : Ty)
    (Γ : List (Id × Kind)) (pairs : List (Expr × Expr)) (n : Nat) (first : Option String) :
    Coverage :=
  if defsCheck N S defs then
    { names := N, sig := S, defs := defs, elem := Te, vars := Γ,
      covered := pairs.filter fun p => encodesCheck N S Te (kindOf S) Γ p.1 p.2 .bool false,
      constraints := n, first := first }
  else Coverage.none n "its functions are not checked"

theorem gate_ok (N : Names) (S : CSig) (defs : List (Id × List Id × Expr × Expr)) (Te : Ty)
    (Γ : List (Id × Kind)) (pairs : List (Expr × Expr)) (n : Nat) (first : Option String) :
    (gate N S defs Te Γ pairs n first).Ok := by
  unfold gate
  split
  · next h => exact ⟨h, fun p hp => (List.mem_filter.1 hp).2⟩
  · exact ⟨by simp [Coverage.none, defsCheck], fun p hp => by simp [Coverage.none] at hp⟩

def covers (certificate : Sexp) : Coverage :=
  let input := sectionOf certificate "input"
  let symbols := input.flatMap fun | .expr (.atom "symbols" :: rows) => rows | _ => []
  let definitions := input.flatMap fun | .expr (.atom "definitions" :: ds) => ds | _ => []
  let constraints := input.filterMap fun
    | .expr (.atom "constraint" :: i :: .expr [.atom "encoded", e] :: _) => some (i, e)
    | _ => none
  let tin := Table.of symbols
  let tout := Table.of (sectionOf certificate "source-symbols")
  -- the elements are integers where no sort of the variables is a type parameter
  let top := match elemOf symbols with | "" => "Int" | a => a
  let N := namesOf tout
  let ints := top == "Int"
  let ctors := ctorsOf tin ints definitions
  let bodies := encodedBodies input
  -- the uninterpreted functions without type parameters
  let unints := definitions.filterMap fun
    | .expr [.atom "declare-fun", .atom f, .expr params, ret] =>
      let c : Ctx := ⟨tin, top, ints⟩
      let sortOf : Sexp → Sexp := fun | .expr [.atom _, sort] => sort | sort => sort
      match params.mapM (fun p => (kindOfSort c 100 (sortOf p)).toOption),
        (kindOfSort c 100 ret).toOption
      with
      | some ks, some k => some (tin.id f, ks, k)
      | _, _ => none
    | _ => none
  -- the functions whose bodies are read on both sides
  let read := (funsOf tin ints top definitions).filterMap fun f =>
    let symbol := (tin.rows.find? fun (_, k, ds) => k == "function" && ds.head? == some f.name)
    match symbol.bind fun (a, _, _) => bodies.lookup a, readExpr f.ctx 1000 f.body with
    | some body', .ok body =>
      match readExpr ⟨tout, f.ctx.elem, ints⟩ 1000 body' with
      | .ok body' => some (f, body, body')
      | .error _ => none
    | _, _ => none
  -- those whose encoded bodies are what the encoder makes of them, given the others
  let rec keep : Nat → List (Fun × Expr × Expr) → List (Fun × Expr × Expr)
    | 0, fs => fs
    | n + 1, fs =>
      let S : CSig := ⟨ctors, fs.map (fun (f, _, _) => f.entry), unints, []⟩
      let kept := fs.filter fun (f, body, body') =>
        encodesCheck N S f.elem (kindOf S) (f.params.zip f.kinds) body body' f.kind false
      if kept.length == fs.length then fs else keep n kept
  let funs := keep read.length read
  -- those whose bodies have no operations of bags, given the others
  let rec flat : Nat → List Id → List Id
    | 0, fs => fs
    | n + 1, fs =>
      let S : CSig := ⟨ctors, funs.map (fun (f, _, _) => f.entry), unints, fs⟩
      let kept := fs.filter fun name => unints.any (·.1 == name) ||
        funs.any fun (f, body, body') => f.name == name &&
          encodesCheck N S f.elem (kindOf S) (f.params.zip f.kinds) body body' f.kind true
      if kept.length == fs.length then fs else flat n kept
  let S : CSig := ⟨ctors, funs.map (fun (f, _, _) => f.entry), unints,
    flat (funs.length + 1) (unints.map (·.1) ++ funs.map fun (f, _, _) => f.name)⟩
  let defs := funs.map fun (f, body, body') => (f.name, f.params, body, body')
  let cin : Ctx := ⟨tin, top, ints⟩
  let Γ := symbols.filterMap fun
    | .expr [.atom x, .atom "variable", _, _, sort] =>
      (kindOfSort cin 100 sort).toOption.map fun k => (x, k)
    | _ => none
  let Te := readTy (.atom top)
  let checked := constraints.map fun (i, e) =>
    match readExpr cin 1000 i, readExpr ⟨tout, top, ints⟩ 1000 e with
    | .error what, _ => Except.error s!"`{what}` is not read"
    | _, .error what => Except.error s!"`{what}` is not read in its encoded term"
    | .ok i, .ok e =>
      if encodesCheck N S Te (kindOf S) Γ i e .bool false then .ok (i, e)
      else .error "it is read, and its encoded term is not what the theorem expects"
  gate N S defs Te Γ (checked.filterMap fun r => r.toOption) constraints.length
    (checked.findSome? fun | .error why => some why | .ok _ => none)

theorem covers_ok (certificate : Sexp) : (covers certificate).Ok := by
  unfold covers
  exact gate_ok _ _ _ _ _ _ _ _

/-- Where the constraints of the input that are covered all evaluate to `true` in the program
`Ps` of the input, so do their encoded terms in the encoded program `P`: `P` defines the
datatype of the encoder as the encoder does, both programs have the constructors that are
read and each function that is read, with its body in the input for `Ps` and its body after
the encoders for `P` (`hdefs`), and the values of the free variables relate (`hΓ`). -/
theorem Coverage.encoded {C : Coverage} (hC : C.Ok) {O : Oracle} {Ps P : Program}
    {K : Value → Prop} {E : Value → Value → Bool} {T0 : Ty} {inv bi eq b1 b2 : Id}
    (hB : Base O Ps P C.names K E T0 C.sig.sig inv bi eq b1 b2)
    (hdefs : ∀ f tparams Tf ks k params body body',
      C.sig.funs.lookup f = some (tparams, Tf, ks, k) →
      C.defs.lookup f = some (params, body, body') →
        FunIn f tparams params body Ps ∧ FunIn f tparams params body' P ∧
          (tparams = [] → O.resolve_all [] [Tf] = [T0]))
    (hints : ∀ f ks k, C.sig.unint.lookup f = some (ks, k) →
      ∃ params body body' Tu, InterpIn f params body Ps ∧ InterpIn f params body' P ∧
        Encodes C.names C.sig.sig Tu (fun x => (params.zip ks).lookup x) body body' k
          (C.sig.flat.contains f) ∧ O.resolve_all [] [Tu] = [T0])
    {env env' : Env} (hT : O.resolve_all (env_types env') [C.elem] = [T0])
    (hΓ : ∀ x k, C.vars.lookup x = some k → ∃ v v', lookup_var (env_vars env) x = .Ok v ∧
      lookup_var (env_vars env') x = .Ok v' ∧ Rel O P C.names K E T0 C.sig.sig k v v')
    (hsol : ∀ p ∈ C.covered, ∃ n, eval O Ps n env p.1 = .Ok (.BoolV true)) :
    ∀ p ∈ C.covered, ∃ n, eval O P n env' p.2 = .Ok (.BoolV true) := by
  have hF : Funs O Ps P C.names T0 C.sig.sig := by
    refine ⟨fun f tparams Tf ks k hf => ?_, hints⟩
    have hall := List.all_eq_true.1 hC.1 _ (mem_of_lookup hf)
    simp only [] at hall
    split at hall
    · next params body body' hd =>
      obtain ⟨h1, h2, h3⟩ := hdefs f tparams Tf ks k params body body' hf hd
      exact ⟨params, body, body', h1, h2, encodesCheck_sound hall, h3⟩
    · cases hall
  intro p hp
  obtain ⟨n, hn⟩ := hsol p hp
  obtain ⟨v', m, _, hR, hm⟩ := encodes_eval hB hF n.toNat (encodesCheck_sound (hC.2 p hp))
    env env' hT hΓ n (Int.self_le_toNat n) _ hn
  cases hR
  exact ⟨m, hm m (Int.le_refl m)⟩

/-- `Coverage.encoded` for the constraints of a certificate that `covers` gives. -/
theorem covers_encoded (certificate : Sexp) {O : Oracle} {Ps P : Program}
    {K : Value → Prop} {E : Value → Value → Bool} {T0 : Ty} {inv bi eq b1 b2 : Id}
    (hB : Base O Ps P (covers certificate).names K E T0 (covers certificate).sig.sig
      inv bi eq b1 b2)
    (hdefs : ∀ f tparams Tf ks k params body body',
      (covers certificate).sig.funs.lookup f = some (tparams, Tf, ks, k) →
      (covers certificate).defs.lookup f = some (params, body, body') →
        FunIn f tparams params body Ps ∧ FunIn f tparams params body' P ∧
          (tparams = [] → O.resolve_all [] [Tf] = [T0]))
    (hints : ∀ f ks k, (covers certificate).sig.unint.lookup f = some (ks, k) →
      ∃ params body body' Tu, InterpIn f params body Ps ∧ InterpIn f params body' P ∧
        Encodes (covers certificate).names (covers certificate).sig.sig Tu
          (fun x => (params.zip ks).lookup x) body body' k
          ((covers certificate).sig.flat.contains f) ∧ O.resolve_all [] [Tu] = [T0])
    {env env' : Env} (hT : O.resolve_all (env_types env') [(covers certificate).elem] = [T0])
    (hΓ : ∀ x k, (covers certificate).vars.lookup x = some k → ∃ v v',
      lookup_var (env_vars env) x = .Ok v ∧ lookup_var (env_vars env') x = .Ok v' ∧
        Rel O P (covers certificate).names K E T0 (covers certificate).sig.sig k v v')
    (hsol : ∀ p ∈ (covers certificate).covered,
      ∃ n, eval O Ps n env p.1 = .Ok (.BoolV true)) :
    ∀ p ∈ (covers certificate).covered, ∃ n, eval O P n env' p.2 = .Ok (.BoolV true) :=
  Coverage.encoded (covers_ok certificate) hB hdefs hints hT hΓ hsol

end Inox.Input
