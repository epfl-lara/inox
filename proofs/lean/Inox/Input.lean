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

open Inox.Semantics Inox.Bags Inox.Encoded Inox.Typing Logos

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

/-- The type arguments `tps` are those of a call of an uninterpreted function with a type
parameter at the elements `Te` (`p`), or none (otherwise). -/
def tpsCheck (Te : Ty) : Bool → List Ty → Bool
  | true, [t] => sameTy t Te
  | false, [] => true
  | _, _ => false

theorem tpsCheck_eq {Te : Ty} {p : Bool} {tps : List Ty} (h : tpsCheck Te p tps = true) :
    tps = if p then [Te] else [] := by
  match p, tps, h with
  | true, [t], h => simp [sameTy_eq (show sameTy t Te = true from h)]
  | false, [], _ => rfl

/-- The kind `k` is that of the elements of bags (`BagKind`). -/
def bagKindCheck (κ k : Kind) : Bool := kindEq k .elem || (kindEq k .int && kindEq κ .int)

theorem bagKindCheck_sound {κ k : Kind} (h : bagKindCheck κ k = true) : BagKind κ k := by
  simp only [bagKindCheck, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨h1, h2⟩
  · exact .inl (kindEq_eq h)
  · exact .inr ⟨kindEq_eq h1, kindEq_eq h2⟩

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
  unint : List (Id × Bool × List Kind × Kind)
  flat : List Id
  sorts : List (Id × List Id × List (Id × List Param))
  elemKind : Kind

def CSig.sig (S : CSig) : Sig where
  ctors c := S.ctors.lookup c
  funs f := S.funs.lookup f
  unint f := S.unint.lookup f
  flat f := S.flat.contains f
  sorts s := S.sorts.lookup s
  elemKind := S.elemKind

mutual
/-- The equality of types of `PureTy`. -/
def tyEq : Ty → Ty → Bool
  | .IntegerType, .IntegerType => true
  | .BooleanType, .BooleanType => true
  | .TypeParameter a, .TypeParameter b => a == b
  | .ADTType s as, .ADTType s' bs => s == s' && tysEq as bs
  | .RefinementType x t p, .RefinementType x' t' p' => x == x' && tyEq t t' && exprEq p p'
  | .FunctionType ts t, .FunctionType ts' t' => tysEq ts ts' && tyEq t t'
  | _, _ => false
def tysEq : List Ty → List Ty → Bool
  | [], [] => true
  | t :: ts, t' :: ts' => tyEq t t' && tysEq ts ts'
  | _, _ => false
/-- The equality of the predicates of `PureExpr`. -/
def exprEq : Expr → Expr → Bool
  | .Variable x, .Variable y => x == y
  | .IntegerLiteral n, .IntegerLiteral m => n == m
  | .BooleanLiteral a, .BooleanLiteral b => a == b
  | .Plus a b, .Plus a' b' => exprEq a a' && exprEq b b'
  | .Minus a b, .Minus a' b' => exprEq a a' && exprEq b b'
  | .LessThan a b, .LessThan a' b' => exprEq a a' && exprEq b b'
  | .GreaterThan a b, .GreaterThan a' b' => exprEq a a' && exprEq b b'
  | .LessEquals a b, .LessEquals a' b' => exprEq a a' && exprEq b b'
  | .GreaterEquals a b, .GreaterEquals a' b' => exprEq a a' && exprEq b b'
  | .Not a, .Not a' => exprEq a a'
  | _, _ => false
end

mutual
theorem tyEq_eq : ∀ {a b : Ty}, tyEq a b = true → a = b
  | .IntegerType, .IntegerType, _ => rfl
  | .BooleanType, .BooleanType, _ => rfl
  | .TypeParameter a, .TypeParameter b, h => by
    simp only [tyEq, beq_iff_eq] at h
    rw [h]
  | .ADTType s as, .ADTType s' bs, h => by
    simp only [tyEq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, tysEq_eq h.2]
  | .RefinementType x t p, .RefinementType x' t' p', h => by
    simp only [tyEq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, tyEq_eq h.1.2, exprEq_eq h.2]
  | .FunctionType ts t, .FunctionType ts' t', h => by
    simp only [tyEq, Bool.and_eq_true] at h
    rw [tysEq_eq h.1, tyEq_eq h.2]
theorem tysEq_eq : ∀ {a b : List Ty}, tysEq a b = true → a = b
  | [], [], _ => rfl
  | t :: ts, t' :: ts', h => by
    simp only [tysEq, Bool.and_eq_true] at h
    rw [tyEq_eq h.1, tysEq_eq h.2]
theorem exprEq_eq : ∀ {a b : Expr}, exprEq a b = true → a = b
  | .Variable x, .Variable y, h => by simp only [exprEq, beq_iff_eq] at h; rw [h]
  | .IntegerLiteral n, .IntegerLiteral m, h => by simp only [exprEq, beq_iff_eq] at h; rw [h]
  | .BooleanLiteral a, .BooleanLiteral b, h => by simp only [exprEq, beq_iff_eq] at h; rw [h]
  | .Plus a b, .Plus a' b', h => by
    simp only [exprEq, Bool.and_eq_true] at h; rw [exprEq_eq h.1, exprEq_eq h.2]
  | .Minus a b, .Minus a' b', h => by
    simp only [exprEq, Bool.and_eq_true] at h; rw [exprEq_eq h.1, exprEq_eq h.2]
  | .LessThan a b, .LessThan a' b', h => by
    simp only [exprEq, Bool.and_eq_true] at h; rw [exprEq_eq h.1, exprEq_eq h.2]
  | .GreaterThan a b, .GreaterThan a' b', h => by
    simp only [exprEq, Bool.and_eq_true] at h; rw [exprEq_eq h.1, exprEq_eq h.2]
  | .LessEquals a b, .LessEquals a' b', h => by
    simp only [exprEq, Bool.and_eq_true] at h; rw [exprEq_eq h.1, exprEq_eq h.2]
  | .GreaterEquals a b, .GreaterEquals a' b', h => by
    simp only [exprEq, Bool.and_eq_true] at h; rw [exprEq_eq h.1, exprEq_eq h.2]
  | .Not a, .Not a', h => by simp only [exprEq] at h; rw [exprEq_eq h]
end

/-- Whether an expression is a predicate on `x` of `PureExpr`. -/
def pureExprCheck (x : Id) : Expr → Bool
  | .Variable y => y == x
  | .IntegerLiteral _ | .BooleanLiteral _ => true
  | .Plus a b | .Minus a b | .LessThan a b | .GreaterThan a b | .LessEquals a b
  | .GreaterEquals a b => pureExprCheck x a && pureExprCheck x b
  | .Not a => pureExprCheck x a
  | _ => false

theorem pureExprCheck_sound {x : Id} : ∀ {e : Expr}, pureExprCheck x e = true → PureExpr x e
  | .Variable y, h => by simp only [pureExprCheck, beq_iff_eq] at h; subst h; exact .var
  | .IntegerLiteral _, _ => .int _
  | .BooleanLiteral _, _ => .bool _
  | .Plus a b, h => by
    simp only [pureExprCheck, Bool.and_eq_true] at h
    exact .plus (pureExprCheck_sound h.1) (pureExprCheck_sound h.2)
  | .Minus a b, h => by
    simp only [pureExprCheck, Bool.and_eq_true] at h
    exact .minus (pureExprCheck_sound h.1) (pureExprCheck_sound h.2)
  | .LessThan a b, h => by
    simp only [pureExprCheck, Bool.and_eq_true] at h
    exact .lt (pureExprCheck_sound h.1) (pureExprCheck_sound h.2)
  | .GreaterThan a b, h => by
    simp only [pureExprCheck, Bool.and_eq_true] at h
    exact .gt (pureExprCheck_sound h.1) (pureExprCheck_sound h.2)
  | .LessEquals a b, h => by
    simp only [pureExprCheck, Bool.and_eq_true] at h
    exact .le (pureExprCheck_sound h.1) (pureExprCheck_sound h.2)
  | .GreaterEquals a b, h => by
    simp only [pureExprCheck, Bool.and_eq_true] at h
    exact .ge (pureExprCheck_sound h.1) (pureExprCheck_sound h.2)
  | .Not a, h => by
    simp only [pureExprCheck] at h
    exact .not (pureExprCheck_sound h)

mutual
/-- Whether a type is of `PureTy`, with the type parameters `B`. -/
def pureCheck (S : CSig) (B : List Id) : Ty → Bool
  | .IntegerType | .BooleanType => true
  | .TypeParameter a => B.contains a
  | .ADTType s args =>
    (match S.sorts.lookup s with
      | some (tps, _) => args.length == tps.length
      | none => false) && pureChecks S B args
  | .RefinementType x t p => pureCheck S B t && pureExprCheck x p
  | _ => false
def pureChecks (S : CSig) (B : List Id) : List Ty → Bool
  | [] => true
  | t :: ts => pureCheck S B t && kindEq (pureKind S.elemKind t) S.elemKind && pureChecks S B ts
end

mutual
theorem pureCheck_sound {S : CSig} {B : List Id} :
    ∀ {t : Ty}, pureCheck S B t = true → PureTy S.sig.sorts S.sig.ok B t
  | .IntegerType, _ => .int B
  | .BooleanType, _ => .bool B
  | .TypeParameter a, h => .tparam (by simpa [pureCheck] using h)
  | .ADTType s args, h => by
    simp only [pureCheck, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    split at h1
    · next tps ctors hl =>
      obtain ⟨ha, hok⟩ := pureChecks_sound h2
      exact .adt (by simpa [CSig.sig] using hl) (by simpa using h1) ha hok
    · cases h1
  | .RefinementType x t p, h => by
    simp only [pureCheck, Bool.and_eq_true] at h
    exact .refine (pureCheck_sound h.1) (pureExprCheck_sound h.2)
termination_by t _ => sizeOf t
decreasing_by all_goals simp_wf; all_goals omega
theorem pureChecks_sound {S : CSig} {B : List Id} :
    ∀ {ts : List Ty}, pureChecks S B ts = true →
      (∀ t ∈ ts, PureTy S.sig.sorts S.sig.ok B t) ∧ (∀ t ∈ ts, S.sig.ok t)
  | [], _ => ⟨by simp, by simp⟩
  | t :: ts, h => by
    simp only [pureChecks, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨g1, g2⟩ := pureChecks_sound h3
    have p1 := pureCheck_sound h1
    refine ⟨fun t' ht' => ?_, fun t' ht' => ?_⟩
    · rcases List.mem_cons.1 ht' with rfl | ht'
      · exact p1
      · exact g1 t' ht'
    · rcases List.mem_cons.1 ht' with rfl | ht'
      · exact kindEq_eq h2
      · exact g2 t' ht'
termination_by ts _ => sizeOf ts
decreasing_by all_goals simp_wf; all_goals omega
end

/-- The equality of lists of fields. -/
def fieldsEq : List (Id × Kind) → List (Id × Kind) → Bool
  | [], [] => true
  | (f, k) :: r, (f', k') :: r' => f == f' && kindEq k k' && fieldsEq r r'
  | _, _ => false

theorem fieldsEq_eq : ∀ {a b : List (Id × Kind)}, fieldsEq a b = true → a = b
  | [], [], _ => rfl
  | (f, k) :: r, (f', k') :: r', h => by
    simp only [fieldsEq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, kindEq_eq h.1.2, fieldsEq_eq h.2]

/-- Whether the sorts of the signature are well formed and their constructors have the kinds of
their fields. -/
def sortOk (S : CSig) : Id × List Id × List (Id × List Param) → Bool
  | (s, tps, ctors) => ctors.all fun (c, ps) =>
    ps.all (fun p => pureCheck S tps (paramTy p)) &&
      match S.ctors.lookup c with
      | some (s', fs) => s' == s &&
          fieldsEq fs (ps.map fun p => (paramId p, pureKind S.elemKind (paramTy p)))
      | none => false

def sigOk (S : CSig) : Bool := S.sorts.all (sortOk S)

theorem sigOk_sound {S : CSig} (h : sigOk S = true) : S.sig.Ok := by
  have get : ∀ s tps ctors, S.sig.sorts s = some (tps, ctors) → ∀ c ps, (c, ps) ∈ ctors →
      (ps.all (fun p => pureCheck S tps (paramTy p)) &&
        match S.ctors.lookup c with
        | some (s', fs) => s' == s &&
            fieldsEq fs (ps.map fun p => (paramId p, pureKind S.elemKind (paramTy p)))
        | none => false) = true := by
    intro s tps ctors hs c ps hc
    have h1 := List.all_eq_true.1 h _ (mem_of_lookup (by simpa [CSig.sig] using hs))
    exact List.all_eq_true.1 h1 _ hc
  refine ⟨fun s tps ctors hs c ps hc p hp => ?_, fun s tps ctors hs c ps hc => ?_⟩
  · have h2 := get s tps ctors hs c ps hc
    simp only [Bool.and_eq_true, List.all_eq_true] at h2
    exact pureCheck_sound (h2.1 p hp)
  · have h2 := get s tps ctors hs c ps hc
    simp only [Bool.and_eq_true] at h2
    obtain ⟨_, h2⟩ := h2
    split at h2
    · next s' fs hl =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      obtain ⟨rfl, h3⟩ := h2
      simp only [CSig.sig, hl, fieldsEq_eq h3]
    · cases h2

/-- The equality of parameters. -/
def paramsEq : List Param → List Param → Bool
  | [], [] => true
  | .Param x t :: ps, .Param x' t' :: ps' => x == x' && tyEq t t' && paramsEq ps ps'
  | _, _ => false

theorem paramsEq_eq : ∀ {a b : List Param}, paramsEq a b = true → a = b
  | [], [], _ => rfl
  | .Param x t :: ps, .Param x' t' :: ps', h => by
    simp only [paramsEq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, tyEq_eq h.1.2, paramsEq_eq h.2]

/-- Whether a type is of `Inhab`. -/
def inhabCheck (Te : Ty) : Ty → Bool
  | .IntegerType | .BooleanType => true
  | .TypeParameter a => match Te with
    | .TypeParameter b => a == b
    | _ => false
  | .FunctionType _ t => match t with
    | .IntegerType | .BooleanType => true
    | t => tyEq t Te
  | _ => false

theorem inhabCheck_sound {Te : Ty} : ∀ {t : Ty}, inhabCheck Te t = true → Inhab Te t
  | .IntegerType, _ => .int
  | .BooleanType, _ => .bool
  | .TypeParameter a, h => by
    simp only [inhabCheck] at h
    split at h
    · next b =>
      simp only [beq_iff_eq] at h
      subst h
      exact .elem rfl
    · cases h
  | .FunctionType ts t, h => by
    simp only [inhabCheck] at h
    split at h
    · exact .fn (.inl rfl)
    · exact .fn (.inr (.inl rfl))
    · exact .fn (.inr (.inr (tyEq_eq h)))

/-- The variables other than `ids`. -/
def dropIds (ids : List Id) (Γ : List (Id × Kind)) : List (Id × Kind) :=
  Γ.filter fun p => !ids.contains p.1

theorem lookup_drop (ids : List Id) : ∀ (Γ : List (Id × Kind)) (x : Id),
    (dropIds ids Γ).lookup x = if x ∈ ids then none else Γ.lookup x
  | [], x => by simp [dropIds]
  | (y, k) :: Γ, x => by
    have ih := lookup_drop ids Γ x
    simp only [dropIds] at ih ⊢
    rw [List.filter_cons]
    by_cases hy : y ∈ ids
    · have hc : ids.contains y = true := by simpa using hy
      simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false, ih]
      by_cases hx : x ∈ ids
      · simp [hx]
      · have hb : (x == y) = false := by simpa using (fun e : x = y => hx (e ▸ hy))
        simp [hx, List.lookup, hb]
    · have hc : ids.contains y = false := by simpa using hy
      simp only [hc, Bool.not_false, ite_true]
      by_cases hxy : x = y
      · subst hxy
        simp [List.lookup, hy]
      · have hb : (x == y) = false := by simpa using hxy
        simp only [List.lookup, hb, ih]

/-- The kinds of the parameters of a quantifier, the same on both sides, of the type of
elements `Te` or of `PureTy`. -/
def paramsCheck (S : CSig) (Te : Ty) : List Param → List Param → Option (List Kind)
  | [], [] => some []
  | .Param x t :: ps, .Param x' t' :: ps' =>
    if x == x' && tyEq t t' then
      let k : Option Kind := match t, Te with
        | .TypeParameter a, .TypeParameter b => if a == b then some .elem else none
        | _, _ => if pureCheck S [] t then some (pureKind S.elemKind t) else none
      k.bind fun k => (paramsCheck S Te ps ps').map (k :: ·)
    else none
  | _, _ => none

theorem paramsCheck_sound {S : CSig} {Te : Ty} : ∀ {ps ps' : List Param} {ks : List Kind},
    paramsCheck S Te ps ps' = some ks → ps' = ps ∧ ParamsOk S.sig Te ps ks
  | [], [], ks, h => by
    simp only [paramsCheck, Option.some.injEq] at h
    subst h
    exact ⟨rfl, .nil⟩
  | .Param x t :: ps, .Param x' t' :: ps', ks, h => by
    simp only [paramsCheck] at h
    split at h
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, ht⟩ := hc
      cases tyEq_eq ht
      obtain ⟨k, hk, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨ks', h', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨rfl, hr⟩ := paramsCheck_sound h'
      refine ⟨rfl, .cons ?_ hr⟩
      split at hk
      · next a b =>
        split at hk
        · next hab =>
          simp only [beq_iff_eq] at hab
          subst hab
          cases hk
          exact .elem rfl
        · cases hk
      · split at hk
        · next hp =>
          cases hk
          exact .pure (pureCheck_sound hp)
        · cases hk
    · cases h
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [paramsCheck] at h

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

/-- Whether no constructor of the sorts `A` has a function in its fields. -/
def foSig (S : CSig) (A : List Id) : Bool :=
  S.ctors.all fun (_, s, fs) => !A.contains s || foKinds A.contains (fs.map Prod.snd)

theorem foSig_sound {S : CSig} {A : List Id} (h : foSig S A = true) :
    S.sig.fo A.contains := by
  intro c s fs hc hs
  have hmem : (c, s, fs) ∈ S.ctors := mem_of_lookup hc
  have h := List.all_eq_true.1 h _ hmem
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
  rw [hs] at h
  simpa using h

/-- The sorts that have no functions in them, removing those that do until none is left. -/
def foSorts (S : CSig) : List Id :=
  go (S.ctors.length + 1) (S.ctors.map (·.2.1))
where
  go : Nat → List Id → List Id
    | 0, A => A
    | n + 1, A =>
      let A' := A.filter fun s =>
        S.ctors.all fun (_, s', fs) => s' != s || foKinds A.contains (fs.map Prod.snd)
      if A'.length == A.length then A else go n A'

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
    foKind (foSorts S).contains (g Γ a) && foSig S (foSorts S) &&
      encodesCheck N S Te g Γ a a' (g Γ a) u && encodesCheck N S Te g Γ b b' (g Γ a) u
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
      encodesCheck N S Te g Γ b b' .bag false && bagKindCheck S.elemKind (g Γ e) &&
        encodesCheck N S Te g Γ e e' (g Γ e) false
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
    f == N.get && sameTy t Te && bagKindCheck S.elemKind (g Γ e) &&
      encodesCheck N S Te g Γ e e' (g Γ e) false && encodesCheck N S Te g Γ b b' .bag false
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
  | Γ, .FunctionInvocation f tps es, .FunctionInvocation f' tps' es', k, u =>
    (!u || S.flat.contains f) && f == f' && (match S.funs.lookup f, tps, tps' with
      | some ([A], .TypeParameter B, ks, k2), [t0], [t] =>
        A == B && sameTy t0 Te && sameTy t Te && kindEq k2 k &&
          encodesCheck N S Te g Γ (.Tuple es) (.Tuple es') (.tuple ks) u
      | some ([], _, ks, k2), _, [] =>
        kindEq k2 k && encodesCheck N S Te g Γ (.Tuple es) (.Tuple es') (.tuple ks) u
      | _, _, _ => false)
  | Γ, .Lambda ps body, .Lambda ps' body', .fn ks k, u =>
    decide (param_ids ps = param_ids ps') &&
      encodesCheck N S Te g ((param_ids ps).zip ks ++ keep Γ) body body' k true
  | Γ, .Application callee es, .Application callee' es', k, u =>
    (match g Γ callee with
      | .fn ks k2 =>
        kindEq k2 k && encodesCheck N S Te g Γ callee callee' (.fn ks k2) u &&
          encodesCheck N S Te g Γ (.Tuple es) (.Tuple es') (.tuple ks) u
      | _ => false)
  | Γ, .UninterpretedCall f tps es, .UninterpretedCall f' tps' es', k, u =>
    (!u || S.flat.contains f) && f == f' && (match S.unint.lookup f with
      | some (p, ks, k2) =>
        tpsCheck Te p tps && tpsCheck Te p tps' && kindEq k2 k &&
          encodesCheck N S Te g Γ (.Tuple es) (.Tuple es') (.tuple ks) u
      | none => false)
  | _, .Error, .Error, _, _ => true
  | Γ, .Forall ps body, .Forall ps' body', .bool, _ =>
    (match paramsCheck S Te ps ps' with
      | some ks => encodesCheck N S Te g ((param_ids ps).zip ks ++ Γ) body body' .bool true
      | none => paramsEq ps ps' && ps.all (fun p => inhabCheck Te (paramTy p)) &&
          encodesCheck N S Te g (dropIds (param_ids ps) Γ) body body' .bool true)
  | _, .FractionLiteral n d, .FractionLiteral n' d', .prim, _ => n == n' && d == d'
  | _, .BVLiteral sg w x, .BVLiteral sg' w' x', .prim, _ => sg == sg' && w == w' && x == x'
  | Γ, .Division a b, .Division a' b', .prim, u =>
    encodesCheck N S Te g Γ a a' .prim u && encodesCheck N S Te g Γ b b' .prim u
  | Γ, .BVUnsignedToSigned a, .BVUnsignedToSigned a', .prim, u =>
    encodesCheck N S Te g Γ a a' .prim u
  | Γ, .BVSignedToUnsigned a, .BVSignedToUnsigned a', .prim, u =>
    encodesCheck N S Te g Γ a a' .prim u
  | _, .FiniteSet [] t, .FiniteSet [] t', .set k, _ => sameTy t Te && sameTy t' Te && setKind k
  | Γ, .SetAdd a e, .SetAdd a' e', .set k, u =>
    encodesCheck N S Te g Γ a a' (.set k) u && encodesCheck N S Te g Γ e e' k u
  | Γ, .ElementOfSet e a, .ElementOfSet e' a', .bool, u =>
    encodesCheck N S Te g Γ e e' (g Γ e) u && encodesCheck N S Te g Γ a a' (.set (g Γ e)) u
  | Γ, .SetUnion a b, .SetUnion a' b', .set k, u =>
    encodesCheck N S Te g Γ a a' (.set k) u && encodesCheck N S Te g Γ b b' (.set k) u
  | Γ, .SetIntersection a b, .SetIntersection a' b', .set k, u =>
    encodesCheck N S Te g Γ a a' (.set k) u && encodesCheck N S Te g Γ b b' (.set k) u
  | Γ, .SetDifference a b, .SetDifference a' b', .set k, u =>
    encodesCheck N S Te g Γ a a' (.set k) u && encodesCheck N S Te g Γ b b' (.set k) u
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
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨rfl, ht⟩, rfl⟩, rfl⟩, ht2⟩, rfl⟩, hb⟩, hk⟩, he⟩ := h
    cases sameTy_eq ht
    cases sameTy_eq ht2
    exact .add (bagKindCheck_sound hk) (ihb hb) (ihe he)
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
    obtain ⟨⟨⟨⟨rfl, ht⟩, hk⟩, he⟩, hb⟩ := h
    cases sameTy_eq ht
    exact .mult (bagKindCheck_sound hk) (ihe he) (ihb hb)
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
    · next A B ks k2 t0 t hl =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨rfl, ht0⟩, ht⟩, hk⟩, ha⟩ := h
      cases sameTy_eq ht0
      cases sameTy_eq ht
      cases kindEq_eq hk
      exact .callPoly hl (fun h1 => by subst h1; simpa [CSig.sig] using hu) 
        (by simp only [hl] at ih; exact ih ha)
    · next Tf ks k2 _ hl =>
      simp only [Bool.and_eq_true] at h
      cases kindEq_eq h.1
      exact .callMono _ hl (fun h1 => by subst h1; simpa [CSig.sig] using hu) 
        (by simp only [hl] at ih; exact ih h.2)
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
    · next p ks k2 hl =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      cases tpsCheck_eq h1
      cases tpsCheck_eq h2
      cases kindEq_eq h3
      exact .uninterp hl (fun h1 => by subst h1; simpa [CSig.sig] using hu) (ih ks h4)
    · cases h
  · exact .error _
  · next ih =>
    obtain ⟨rfl, hok⟩ := paramsCheck_sound ‹paramsCheck S Te _ _ = some _›
    have hb := ih h
    simp only [List.lookup_append] at hb
    exact .forall_ hok hb
  · next ih =>
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨hp, hi⟩, hb⟩ := h
    cases paramsEq_eq hp
    have hb := ih hb
    simp only [lookup_drop] at hb
    exact .forallUnused (fun p hp => inhabCheck_sound (hi p hp)) hb
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .frac _ _
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact .bvLit _ _ _
  · next iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .div (iha h.1) (ihb h.2)
  · next iha => exact .toSigned (iha h)
  · next iha => exact .toUnsigned (iha h)
  · simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases sameTy_eq h1
    cases sameTy_eq h2
    exact .setEmpty h3
  · next iha ihe =>
    simp only [Bool.and_eq_true] at h
    exact .setAdd (iha h.1) (ihe h.2)
  · next ihe iha =>
    simp only [Bool.and_eq_true] at h
    exact .member (ihe h.1) (iha h.2)
  · next iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .setUnion (iha h.1) (ihb h.2)
  · next iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .setInter (iha h.1) (ihb h.2)
  · next iha ihb =>
    simp only [Bool.and_eq_true] at h
    exact .setDiff (iha h.1) (ihb h.2)
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
    | .atom "Real" => .ok .prim
    | .expr [.atom "_", .atom "BitVec", _] => .ok .prim
    | .atom a =>
      if a == c.elem then .ok (if c.ints then .int else .elem)
      else if c.table.kind a == "sort" then .ok (.adt (c.table.id a))
      else .error s!"the sort {a}"
    | .expr [.atom "Bag", x] =>
      if x == .atom c.elem then .ok .bag else .error "a bag of other than elements"
    | .expr [.atom "Set", x] => do
      let k ← kindOfSort c n x
      if setKind k then pure (.set k) else .error "a set of other than elements"
    | .expr (.atom "Tuple" :: xs) => do pure (.tuple (← xs.mapM (kindOfSort c n)))
    -- the kind of a refinement is that of its base
    | .expr (.atom "!" :: base :: _) => kindOfSort c n base
    | .expr (.atom "->" :: xs) => do
      let ks ← xs.mapM (kindOfSort c n)
      match ks.reverse with
      | k :: rest => pure (.fn rest.reverse k)
      | [] => .error "a sort"
    | .expr (.atom a :: xs) =>
      let base : Sexp → Sexp := fun | .expr (.atom "!" :: b :: _) => b | b => b
      if c.table.kind a == "sort" && xs.all (base · == .atom c.elem) then .ok (.adt (c.table.id a))
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
  | .set k => .SetType (kindTy elem k)
  | .prim => .UnitType
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
  | .SetType t => .set (tyKind t)
  | _ => .elem

/-- The predicate of a refinement, of `PureExpr`. -/
def readPure : Nat → Sexp → Option Expr
  | 0, _ => none
  | n + 1, s =>
    match s with
    | .atom a =>
      if !a.isEmpty && a.all Char.isDigit then some (.IntegerLiteral a.toNat!)
      else if a == "true" then some (.BooleanLiteral true)
      else if a == "false" then some (.BooleanLiteral false)
      else if a.contains '!' then some (.Variable a)
      else none
    | .expr [.atom "not", a] => do pure (.Not (← readPure n a))
    | .expr [.atom "+", a, b] => do pure (.Plus (← readPure n a) (← readPure n b))
    | .expr [.atom "-", a, b] => do pure (.Minus (← readPure n a) (← readPure n b))
    | .expr [.atom "<", a, b] => do pure (.LessThan (← readPure n a) (← readPure n b))
    | .expr [.atom ">", a, b] => do pure (.GreaterThan (← readPure n a) (← readPure n b))
    | .expr [.atom "<=", a, b] => do pure (.LessEquals (← readPure n a) (← readPure n b))
    | .expr [.atom ">=", a, b] => do pure (.GreaterEquals (← readPure n a) (← readPure n b))
    | _ => none

/-- The type that a sort reads as, of integers, booleans, the type parameters `B`, the elements,
sorts and refinements, where it is one of these. -/
def readSortTy (c : Ctx) (B : List String) : Nat → Sexp → Option Ty
  | 0, _ => none
  | n + 1, s =>
    match s with
    | .atom "Int" => some .IntegerType
    | .atom "Bool" => some .BooleanType
    | .atom a =>
      if B.contains a then some (.TypeParameter a)
      else if a == c.elem then some (if c.ints then .IntegerType else .TypeParameter a)
      else if c.table.kind a == "sort" then some (.ADTType (c.table.id a) [])
      else none
    | .expr [.atom "!", base, .atom ":var", .atom y, .atom ":restrict", p] => do
      pure (.RefinementType y (← readSortTy c B n base) (← readPure 100 p))
    | .expr (.atom a :: args) =>
      if c.table.kind a == "sort" then do
        pure (.ADTType (c.table.id a) (← args.mapM (readSortTy c B n)))
      else none
    | _ => none

/-- The expression that `s` reads as, or what it has that isn't read. -/
def readExpr (c : Ctx) : Nat → Sexp → Except String Expr
  | 0, _ => .error "a term too deep"
  | n + 1, s =>
    match s with
    | .atom a =>
      if !a.isEmpty && a.all Char.isDigit then .ok (.IntegerLiteral a.toNat!)
      else if a == "true" then .ok (.BooleanLiteral true)
      else if a == "false" then .ok (.BooleanLiteral false)
      else if a.startsWith "#b" then
        let bits := a.toList.drop 2
        .ok (.BVLiteral true bits.length
          (bits.foldl (fun n b => 2 * n + if b == '1' then 1 else 0) 0))
      else if c.table.kind a == "uninterpreted" then .ok (.UninterpretedCall (c.table.id a) [] [])
      else if c.table.kind a == "function" then .ok (.FunctionInvocation (c.table.id a) [] [])
      else if c.table.kind a == "constructor" then .ok (.ADT (c.table.id a) [] [])
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
    | .expr [.atom "as", .atom "emptyset", t] => pure (.FiniteSet [] (readTy t))
    | .expr [.atom "/", .atom a, .atom b] =>
      if !a.isEmpty && a.all Char.isDigit && !b.isEmpty && b.all Char.isDigit then
        pure (.FractionLiteral a.toNat! b.toNat!)
      else do pure (.Division (← readExpr c n (.atom a)) (← readExpr c n (.atom b)))
    | .expr [.atom "/", a, b] => do pure (.Division (← readExpr c n a) (← readExpr c n b))
    | .expr [.atom "bvudiv", a, b] | .expr [.atom "bvsdiv", a, b] => do
      pure (.Division (← readExpr c n a) (← readExpr c n b))
    | .expr [.atom "!", e, .atom ":unsigned"] => do pure (.BVSignedToUnsigned (← readExpr c n e))
    | .expr [.atom "!", e, .atom ":signed"] => do pure (.BVUnsignedToSigned (← readExpr c n e))
    | .expr [.atom "insert", a, e] => do pure (.SetAdd (← readExpr c n a) (← readExpr c n e))
    | .expr [.atom "member", e, a] => do
      pure (.ElementOfSet (← readExpr c n e) (← readExpr c n a))
    | .expr [.atom "union", a, b] => do pure (.SetUnion (← readExpr c n a) (← readExpr c n b))
    | .expr [.atom "intersection", a, b] => do
      pure (.SetIntersection (← readExpr c n a) (← readExpr c n b))
    | .expr [.atom "setminus", a, b] => do
      pure (.SetDifference (← readExpr c n a) (← readExpr c n b))
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
    | .expr [.expr [.atom "_", .atom "is", .atom k], e] => do
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
        | .expr [.atom x, sort] =>
          match readSortTy c [] 100 sort, sort with
          | some t, _ => pure (Param.Param x t)
          | none, .expr (.atom "!" :: _) => .error s!"the refined parameter {x}"
          | none, _ => do pure (Param.Param x (kindTy c.elem (← kindOfSort c n sort)))
        | _ => .error "a parameter"
      pure (.Forall ps (← readExpr c n b))
    | .expr (.expr [.atom "as", .atom "@", _] :: f :: args) => do
      pure (.Application (← readExpr c n f) (← args.mapM (readExpr c n)))
    | .expr [.atom "as", .atom k, .expr (.atom t :: ts)] =>
      if c.table.kind k == "constructor" then pure (.ADT (c.table.id k) (ts.map readTy) [])
      else if c.table.kind k == "function" then
        pure (.FunctionInvocation (c.table.id k) ((Sexp.atom t :: ts).map readTy) [])
      else if c.table.kind k == "uninterpreted" then
        pure (.UninterpretedCall (c.table.id k) ((Sexp.atom t :: ts).map readTy) [])
      else .error (c.table.kind k ++ " " ++ k)
    | .expr (.expr [.atom "as", .atom k, .expr ts] :: args) => do
      let args ← args.mapM (readExpr c n)
      match c.table.kind k, args with
      | "constructor", _ => pure (.ADT (c.table.id k) ((ts.drop 1).map readTy) args)
      | "selector", [e] => pure (.ADTSelector e (c.table.field k))
      | "function", _ => pure (.FunctionInvocation (c.table.id k) (ts.map readTy) args)
      | "uninterpreted", _ => pure (.UninterpretedCall (c.table.id k) (ts.map readTy) args)
      | kind, _ => .error (kind ++ " " ++ k)
    | .expr [.atom "error", _, _] => pure .Error
    | .expr (.atom k :: args) =>
      if c.table.kind k == "function" then do
        pure (.FunctionInvocation (c.table.id k) [] (← args.mapM (readExpr c n)))
      else if c.table.kind k == "uninterpreted" then do
        pure (.UninterpretedCall (c.table.id k) [] (← args.mapM (readExpr c n)))
      else if c.table.kind k == "constructor" then do
        pure (.ADT (c.table.id k) [] (← args.mapM (readExpr c n)))
      else if c.table.kind k == "selector" then do
        match ← args.mapM (readExpr c n) with
        | [e] => pure (.ADTSelector e (c.table.field k))
        | _ => .error k
      else .error k
    | .expr (.expr [.atom "as", .atom a, _] :: _) => .error a
    | .expr (.expr [.atom "as", .expr (.atom "_" :: .atom a :: _), _] :: _) => .error a
    | _ => .error s!"the term {String.ofList (s.serialize.toList.take 60)}"

/-- The kind of a field of some constructor of the sort `s`. -/
def fieldOf (S : CSig) (s sel : Id) : Option Kind :=
  S.ctors.findSome? fun (_, s2, fs) => if s2 == s then fieldKind fs sel else none

/-- The kind that an expression of the input has, where it is of the fragment. -/
partial def kindOf (S : CSig) (Γ : List (Id × Kind)) : Expr → Kind
  | .Variable x => (Γ.lookup x).getD .int
  | .BooleanLiteral _ | .LessThan _ _ | .GreaterThan _ _ | .LessEquals _ _
  | .GreaterEquals _ _ | .Equals _ _ | .Not _ | .And _ | .Or _ | .Implies _ _
  | .IsConstructor _ _ | .Forall _ _ | .ElementOfSet _ _ => .bool
  | .FiniteSet _ t => .set (tyKind t)
  | .FractionLiteral _ _ | .BVLiteral _ _ _ | .BVUnsignedToSigned _ | .BVSignedToUnsigned _ =>
    .prim
  | .Division a _ => kindOf S Γ a
  | .SetAdd a _ | .SetUnion a _ | .SetIntersection a _ | .SetDifference a _ => kindOf S Γ a
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
  | .UninterpretedCall f _ _ => ((S.unint.lookup f).map (·.2.2)).getD .int
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

/-- The sorts of the input whose fields are read as types, with their type parameters and
their constructors. -/
def sortsOf (t : Table) (ints : Bool) (top : String) (definitions : List Sexp) :
    List (Id × List Id × List (Id × List Param)) :=
  definitions.filterMap fun
    | .expr [.atom "declare-datatypes", .expr [.expr [.atom sort, _]], .expr [decl]] =>
      let (tps, ctors) : List String × List Sexp := match decl with
        | .expr [.atom "par", .expr tps, .expr ctors] =>
          (tps.filterMap fun | .atom a => some a | _ => none, ctors)
        | .expr ctors => ([], ctors)
        | _ => ([], [])
      let ctors := ctors.mapM fun (ctor : Sexp) => match ctor with
        | .expr (.atom k :: fields) => do
          let ps ← fields.mapM fun (field : Sexp) => match field with
            | .expr [.atom f, s] =>
              (readSortTy ⟨t, top, ints⟩ tps 100 s).map (Param.Param (t.field f))
            | _ => none
          pure (t.id k, ps)
        | _ => none
      ctors.map fun ctors => (t.id sort, tps, ctors)
    | _ => none

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
    | n + 1, .expr (.atom "!" :: base :: _) => atoms n base
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
  { names := namesOf ⟨[]⟩, sig := ⟨[], [], [], [], [], .int⟩, defs := [], elem := .UnitType,
    vars := [],
    covered := [], constraints := n, first := some why }

/-- What the checks give of a coverage. -/
def Coverage.Ok (C : Coverage) : Prop :=
  sigOk C.sig = true ∧ defsCheck C.names C.sig C.defs = true ∧
    ∀ p ∈ C.covered,
      encodesCheck C.names C.sig C.elem (kindOf C.sig) C.vars p.1 p.2 .bool false = true

/-- The coverage of the constraints among `pairs` that the check accepts, where the functions
are checked. -/
def gate (N : Names) (S : CSig) (defs : List (Id × List Id × Expr × Expr)) (Te : Ty)
    (Γ : List (Id × Kind)) (pairs : List (Expr × Expr)) (n : Nat) (first : Option String) :
    Coverage :=
  if sigOk S && defsCheck N S defs then
    { names := N, sig := S, defs := defs, elem := Te, vars := Γ,
      covered := pairs.filter fun p => encodesCheck N S Te (kindOf S) Γ p.1 p.2 .bool false,
      constraints := n, first := first }
  else Coverage.none n "its functions are not checked"

theorem gate_ok (N : Names) (S : CSig) (defs : List (Id × List Id × Expr × Expr)) (Te : Ty)
    (Γ : List (Id × Kind)) (pairs : List (Expr × Expr)) (n : Nat) (first : Option String) :
    (gate N S defs Te Γ pairs n first).Ok := by
  unfold gate
  split
  · next h =>
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1, h.2, fun p hp => (List.mem_filter.1 hp).2⟩
  · exact ⟨by simp [Coverage.none, sigOk], by simp [Coverage.none, defsCheck],
      fun p hp => by simp [Coverage.none] at hp⟩

/-- `covers` where the elements are of the sort `top`. -/
def coversAt (certificate : Sexp) (top : String) : Coverage :=
  let input := sectionOf certificate "input"
  let symbols := input.flatMap fun | .expr (.atom "symbols" :: rows) => rows | _ => []
  let definitions := input.flatMap fun | .expr (.atom "definitions" :: ds) => ds | _ => []
  let constraints := input.filterMap fun
    | .expr (.atom "constraint" :: i :: .expr [.atom "encoded", e] :: _) => some (i, e)
    | _ => none
  let tin := Table.of symbols
  let tout := Table.of (sectionOf certificate "source-symbols")
  let N := namesOf tout
  let ints := top == "Int"
  let ctors := ctorsOf tin ints definitions
  let κ : Kind := if ints then .int else .elem
  -- the sorts that are checked, removing the others until none is removed
  let rec okSorts : Nat → List (Id × List Id × List (Id × List Param)) →
      List (Id × List Id × List (Id × List Param))
    | 0, ss => ss
    | n + 1, ss =>
      let kept := ss.filter (sortOk ⟨ctors, [], [], [], ss, κ⟩)
      if kept.length == ss.length then ss else okSorts n kept
  let sorts := okSorts (definitions.length + 1) (sortsOf tin ints top definitions)
  let bodies := encodedBodies input
  -- the uninterpreted functions, and whether they have a type parameter
  let unint (poly : Bool) (elem f : String) (params : List Sexp) (ret : Sexp) :=
    let c : Ctx := ⟨tin, elem, ints⟩
    let sortOf : Sexp → Sexp := fun | .expr [.atom _, sort] => sort | sort => sort
    match params.mapM (fun p => (kindOfSort c 100 (sortOf p)).toOption),
      (kindOfSort c 100 ret).toOption
    with
    | some ks, some k => some (tin.id f, poly, ks, k)
    | _, _ => none
  let unints := definitions.filterMap fun
    | .expr [.atom "declare-fun", .atom f, .expr params, ret] => unint false top f params ret
    | .expr [.atom "declare-fun", .expr [.atom "par", .expr [.atom a],
        .expr [.atom f, .expr params, ret]]] => unint true a f params ret
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
  -- those whose encoded bodies are what the encoder makes of them, given the others, and
  -- among them those whose bodies have no operations of bags (`flat`)
  let rec keep : Nat → List (Fun × Expr × Expr) → List Id →
      List (Fun × Expr × Expr) × List Id
    | 0, fs, flat => (fs, flat)
    | n + 1, fs, flat =>
      let S : CSig := ⟨ctors, fs.map (fun (f, _, _) => f.entry), unints, flat, sorts, κ⟩
      let check (u : Bool) : Fun × Expr × Expr → Bool := fun (f, body, body') =>
        encodesCheck N S f.elem (kindOf S) (f.params.zip f.kinds) body body' f.kind u
      let flat' := unints.map (·.1) ++ (fs.filter (check true)).map (·.1.name)
      let kept := fs.filter fun p => check (flat'.contains p.1.name) p
      if kept.length == fs.length && flat'.length == flat.length then (fs, flat)
      else keep n kept flat'
  let (funs, flat) := keep (2 * read.length + 2) read
    (unints.map (·.1) ++ read.map fun (f, _, _) => f.name)
  let S : CSig := ⟨ctors, funs.map (fun (f, _, _) => f.entry), unints, flat, sorts, κ⟩
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

theorem coversAt_ok (certificate : Sexp) (top : String) : (coversAt certificate top).Ok := by
  unfold coversAt
  exact gate_ok _ _ _ _ _ _ _ _

/-- The elements are of the first sort of the variables that is a type parameter, or else
integers. Where no variable has one, they may be of the type parameter of an uninterpreted
function instead, if more constraints are covered so. -/
def covers (certificate : Sexp) : Coverage :=
  let symbols := (sectionOf certificate "input").flatMap fun
    | .expr (.atom "symbols" :: rows) => rows
    | _ => []
  match elemOf symbols with
  | "" =>
    let C := coversAt certificate "Int"
    let tparams := symbols.filterMap fun
      | .expr [.atom _, .atom "uninterpreted", _, .expr [.atom a]] => some a
      | _ => none
    match tparams with
    | a :: _ =>
      let C' := coversAt certificate a
      if C.covered.length < C'.covered.length then C' else C
    | [] => C
  | a => coversAt certificate a

theorem covers_ok (certificate : Sexp) : (covers certificate).Ok := by
  unfold covers
  dsimp only
  split
  · split
    · split
      · exact coversAt_ok _ _
      · exact coversAt_ok _ _
    · exact coversAt_ok _ _
  · exact coversAt_ok _ _

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
    (hints : ∀ f p ks k, C.sig.unint.lookup f = some (p, ks, k) →
      ∃ params body body' Tu, InterpIn f (if p then [T0] else []) params body Ps ∧
        InterpIn f (if p then [T0] else []) params body' P ∧
        Encodes C.names C.sig.sig Tu (fun x => (params.zip ks).lookup x) body body' k
          (C.sig.flat.contains f) ∧ O.resolve_all [] [Tu] = [T0])
    {env env' : Env}
    (hT : O.resolve_all (env_types env) [C.elem] = [T0] ∧
      O.resolve_all (env_types env') [C.elem] = [T0])
    (hΓ : ∀ x k, C.vars.lookup x = some k → ∃ v v', lookup_var (env_vars env) x = .Ok v ∧
      lookup_var (env_vars env') x = .Ok v' ∧ Rel O P C.names K E T0 C.sig.sig k v v')
    (hsol : ∀ p ∈ C.covered, ∃ n, eval O Ps n env p.1 = .Ok (.BoolV true)) :
    ∀ p ∈ C.covered, ∃ n, eval O P n env' p.2 = .Ok (.BoolV true) := by
  have hF : Funs O Ps P C.names T0 C.sig.sig := by
    refine ⟨fun f tparams Tf ks k hf => ?_, hints⟩
    have hall := List.all_eq_true.1 hC.2.1 _ (mem_of_lookup hf)
    simp only [] at hall
    split at hall
    · next params body body' hd =>
      obtain ⟨h1, h2, h3⟩ := hdefs f tparams Tf ks k params body body' hf hd
      exact ⟨params, body, body', h1, h2, encodesCheck_sound hall, h3⟩
    · cases hall
  intro p hp
  obtain ⟨n, hn⟩ := hsol p hp
  obtain ⟨v', m, _, hR, hm⟩ := encodes_eval hB (sigOk_sound hC.1) hF n.toNat
    (encodesCheck_sound (hC.2.2 p hp))
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
    (hints : ∀ f p ks k, (covers certificate).sig.unint.lookup f = some (p, ks, k) →
      ∃ params body body' Tu, InterpIn f (if p then [T0] else []) params body Ps ∧
        InterpIn f (if p then [T0] else []) params body' P ∧
        Encodes (covers certificate).names (covers certificate).sig.sig Tu
          (fun x => (params.zip ks).lookup x) body body' k
          ((covers certificate).sig.flat.contains f) ∧ O.resolve_all [] [Tu] = [T0])
    {env env' : Env}
    (hT : O.resolve_all (env_types env) [(covers certificate).elem] = [T0] ∧
      O.resolve_all (env_types env') [(covers certificate).elem] = [T0])
    (hΓ : ∀ x k, (covers certificate).vars.lookup x = some k → ∃ v v',
      lookup_var (env_vars env) x = .Ok v ∧ lookup_var (env_vars env') x = .Ok v' ∧
        Rel O P (covers certificate).names K E T0 (covers certificate).sig.sig k v v')
    (hsol : ∀ p ∈ (covers certificate).covered,
      ∃ n, eval O Ps n env p.1 = .Ok (.BoolV true)) :
    ∀ p ∈ (covers certificate).covered, ∃ n, eval O P n env' p.2 = .Ok (.BoolV true) :=
  Coverage.encoded (covers_ok certificate) hB hdefs hints hT hΓ hsol

end Inox.Input
