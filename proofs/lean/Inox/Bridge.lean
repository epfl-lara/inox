/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Data
import Inox.Bits
import Inox.Relative
import Cpc.Proofs.TypePreservation.Helpers

/-!
# From the generated semantics to the intended model, on a first-order fragment

The semantics of Inox is `eval` and `call` of `proofs/semantics/Inox/Semantics.lean`, generated
from `semantics.md`. This module ties it to the models that the certificate checker is about, for
the first-order expressions over integers, Booleans, reals, bit-vectors, datatypes and sets
(`HasTy`):

- `tr D S Γ e` is the term of Logos of an expression, and `trV` the value of a value;
- `ev`, the agreement theorem: where `eval` gives a value, the term evaluates to it in each model
  whose function constants agree with `call` (`CallsOk`) and whose variable constants agree with
  the environment (`VarsOk`);
- the intended model is `Model.star` with the calls as the interpretation of the functions
  (`interpOf`, well defined by fuel monotonicity, `Inox/Mono.lean`, and because the calls to
  values that are the same values of Logos give the same value of Logos, `call_congr`). It agrees
  with `call` at every fuel (`callsOk_star`), and satisfies the defining equations on the arguments where the
  calls give values (`goodOn_star`, for the equations that are the translations of the bodies,
  `EqFor`);
- `no_star_model`: an accepted certificate whose equations are those of the program excludes the
  intended model, by `no_good_model_of_unfold_on` (`Inox/Relative.lean`), whose hypothesis on the
  facts stays. `guardOk_total` discharges its guard obligation for the programs whose calls all
  give values.

That a solution of the query gives an intended model that satisfies the base clauses, and the
facts other than unfoldings, are not proved here.
-/

namespace Inox.Bridge

open Eo
open SmtEval
open Smtm
open Inox.Fresh
open Inox.Extend
open Inox.Model
open Inox.Semantics

theorem fragTy_wf_arrow : ∀ {ps : List (native_String × SmtType)} {R : SmtType},
    (∀ p ∈ ps, __smtx_type_wf_component p.2 = true) → __smtx_type_wf R = true →
    __smtx_type_wf (arrow ps R) = true
  | [], _, _, hR => hR
  | p :: ps, _, h, hR => by
    simp only [arrow, __smtx_type_wf, native_and, Bool.and_eq_true]
    exact ⟨h p (.head _), fragTy_wf_arrow (fun q hq => h q (.tail _ hq)) hR⟩

/-! ## The functions of the program -/

/-- A function of the program, with the types of its parameters and of its result. -/
structure Sig where
  name : Id
  params : List (Id × Ty)
  ret : Ty

/-- The parameters `ps`, as the constants that stand for them. -/
def ptys (D : List Data) (ps : List (Id × Ty)) : List (native_String × SmtType) :=
  ps.map fun p => (nm p.1, trT D p.2)

/-- The function of the model that `s` is: the constant named after it, of the function sort from
the sorts of its parameters to that of its result. -/
def Sig.toDef (D : List Data) (s : Sig) : Def where
  name := nm s.name
  ty := arrow (ptys D s.params) (trT D s.ret)
  params := ptys D s.params
  ret := trT D s.ret

/-- The signature of the function `f`. -/
def findSig (S : List Sig) (f : Id) : Option Sig := S.find? (·.name == f)

/-- The signatures `S` are of types of the fragment, and of functions of distinct names. -/
structure SigOk (D : List Data) (S : List Sig) : Prop where
  /-- The datatypes are as the bridge asks. -/
  data : DataOk D
  params : ∀ s ∈ S, ∀ p ∈ s.params, FragTy D p.2
  ret : ∀ s ∈ S, FragTy D s.ret
  nodup : (S.map Sig.name).Nodup
  /-- The parameters of a function have distinct names. -/
  pnodup : ∀ s ∈ S, (s.params.map Prod.fst).Nodup
  /-- No parameter is named after a function. -/
  fresh : ∀ s ∈ S, ∀ p ∈ s.params, ∀ s' ∈ S, p.1 ≠ s'.name

theorem findSig_spec {S : List Sig} {f : Id} {s : Sig} (h : findSig S f = some s) :
    s ∈ S ∧ s.name = f := by
  have hp := List.find?_some h
  simp only [beq_iff_eq] at hp
  exact ⟨List.mem_of_find?_eq_some h, hp⟩

/-! ## The fragment and its typing -/

/-- `e` is an expression of type `T` of the fragment that the bridge covers, where the functions
have the signatures `S` and the variables the types `Γ`. -/
inductive HasTy (D : List Data) (S : List Sig) (Γ : List (Id × Ty)) : Expr → Ty → Prop where
  | var {x : Id} {T : Ty} : Γ.lookup x = some T → FragTy D T → HasTy D S Γ (.Variable x) T
  | int (i : Int) : HasTy D S Γ (.IntegerLiteral i) .IntegerType
  | bool (b : Bool) : HasTy D S Γ (.BooleanLiteral b) .BooleanType
  | ite {c a b : Expr} {T : Ty} :
      HasTy D S Γ c .BooleanType → HasTy D S Γ a T → HasTy D S Γ b T →
      HasTy D S Γ (.IfExpr c a b) T
  | and {es : List Expr} :
      (∀ e ∈ es, HasTy D S Γ e .BooleanType) → HasTy D S Γ (.And es) .BooleanType
  | or {es : List Expr} :
      (∀ e ∈ es, HasTy D S Γ e .BooleanType) → HasTy D S Γ (.Or es) .BooleanType
  | not {a : Expr} : HasTy D S Γ a .BooleanType → HasTy D S Γ (.Not a) .BooleanType
  | implies {a b : Expr} : HasTy D S Γ a .BooleanType → HasTy D S Γ b .BooleanType →
      HasTy D S Γ (.Implies a b) .BooleanType
  | equals {a b : Expr} {T : Ty} : HasTy D S Γ a T → HasTy D S Γ b T →
      HasTy D S Γ (.Equals a b) .BooleanType
  | plus {a b : Expr} : HasTy D S Γ a .IntegerType → HasTy D S Γ b .IntegerType →
      HasTy D S Γ (.Plus a b) .IntegerType
  | minus {a b : Expr} : HasTy D S Γ a .IntegerType → HasTy D S Γ b .IntegerType →
      HasTy D S Γ (.Minus a b) .IntegerType
  | times {a b : Expr} : HasTy D S Γ a .IntegerType → HasTy D S Γ b .IntegerType →
      HasTy D S Γ (.Times a b) .IntegerType
  | div {a b : Expr} : HasTy D S Γ a .IntegerType → HasTy D S Γ b .IntegerType →
      HasTy D S Γ (.Division a b) .IntegerType
  | rem {a b : Expr} : HasTy D S Γ a .IntegerType → HasTy D S Γ b .IntegerType →
      HasTy D S Γ (.Remainder a b) .IntegerType
  | mod {a b : Expr} : HasTy D S Γ a .IntegerType → HasTy D S Γ b .IntegerType →
      HasTy D S Γ (.Modulo a b) .IntegerType
  | uminus {a : Expr} : HasTy D S Γ a .IntegerType → HasTy D S Γ (.UMinus a) .IntegerType
  | lt {a b : Expr} : HasTy D S Γ a .IntegerType → HasTy D S Γ b .IntegerType →
      HasTy D S Γ (.LessThan a b) .BooleanType
  | gt {a b : Expr} : HasTy D S Γ a .IntegerType → HasTy D S Γ b .IntegerType →
      HasTy D S Γ (.GreaterThan a b) .BooleanType
  | le {a b : Expr} : HasTy D S Γ a .IntegerType → HasTy D S Γ b .IntegerType →
      HasTy D S Γ (.LessEquals a b) .BooleanType
  | ge {a b : Expr} : HasTy D S Γ a .IntegerType → HasTy D S Γ b .IntegerType →
      HasTy D S Γ (.GreaterEquals a b) .BooleanType
  | bvLit {s : Bool} {w x : Int} : 0 < w → 0 ≤ x → x < 2 ^ w.toNat →
      HasTy D S Γ (.BVLiteral s w x) (.BVType s w)
  | bvPlus {a b : Expr} {s : Bool} {w : Int} :
      HasTy D S Γ a (.BVType s w) → HasTy D S Γ b (.BVType s w) →
      HasTy D S Γ (.Plus a b) (.BVType s w)
  | bvMinus {a b : Expr} {s : Bool} {w : Int} :
      HasTy D S Γ a (.BVType s w) → HasTy D S Γ b (.BVType s w) →
      HasTy D S Γ (.Minus a b) (.BVType s w)
  | bvTimes {a b : Expr} {s : Bool} {w : Int} :
      HasTy D S Γ a (.BVType s w) → HasTy D S Γ b (.BVType s w) →
      HasTy D S Γ (.Times a b) (.BVType s w)
  | bvDiv {a b : Expr} {w : Int} :
      HasTy D S Γ a (.BVType false w) → HasTy D S Γ b (.BVType false w) →
      HasTy D S Γ (.Division a b) (.BVType false w)
  | bvRem {a b : Expr} {w : Int} :
      HasTy D S Γ a (.BVType false w) → HasTy D S Γ b (.BVType false w) →
      HasTy D S Γ (.Remainder a b) (.BVType false w)
  | bvNeg {a : Expr} {s : Bool} {w : Int} : HasTy D S Γ a (.BVType s w) →
      HasTy D S Γ (.UMinus a) (.BVType s w)
  | bvNot {a : Expr} {s : Bool} {w : Int} : HasTy D S Γ a (.BVType s w) →
      HasTy D S Γ (.BVNot a) (.BVType s w)
  | bvLt {a b : Expr} {w : Int} :
      HasTy D S Γ a (.BVType false w) → HasTy D S Γ b (.BVType false w) →
      HasTy D S Γ (.LessThan a b) .BooleanType
  | bvGt {a b : Expr} {w : Int} :
      HasTy D S Γ a (.BVType false w) → HasTy D S Γ b (.BVType false w) →
      HasTy D S Γ (.GreaterThan a b) .BooleanType
  | bvLe {a b : Expr} {w : Int} :
      HasTy D S Γ a (.BVType false w) → HasTy D S Γ b (.BVType false w) →
      HasTy D S Γ (.LessEquals a b) .BooleanType
  | bvGe {a b : Expr} {w : Int} :
      HasTy D S Γ a (.BVType false w) → HasTy D S Γ b (.BVType false w) →
      HasTy D S Γ (.GreaterEquals a b) .BooleanType
  | bvMod {a b : Expr} {w : Int} :
      HasTy D S Γ a (.BVType false w) → HasTy D S Γ b (.BVType false w) →
      HasTy D S Γ (.Modulo a b) (.BVType false w)
  | sDiv {a b : Expr} {w : Int} :
      HasTy D S Γ a (.BVType true w) → HasTy D S Γ b (.BVType true w) →
      HasTy D S Γ (.Division a b) (.BVType true w)
  | sRem {a b : Expr} {w : Int} :
      HasTy D S Γ a (.BVType true w) → HasTy D S Γ b (.BVType true w) →
      HasTy D S Γ (.Remainder a b) (.BVType true w)
  | sMod {a b : Expr} {w : Int} :
      HasTy D S Γ a (.BVType true w) → HasTy D S Γ b (.BVType true w) →
      HasTy D S Γ (.Modulo a b) (.BVType true w)
  | sLt {a b : Expr} {w : Int} :
      HasTy D S Γ a (.BVType true w) → HasTy D S Γ b (.BVType true w) →
      HasTy D S Γ (.LessThan a b) .BooleanType
  | sGt {a b : Expr} {w : Int} :
      HasTy D S Γ a (.BVType true w) → HasTy D S Γ b (.BVType true w) →
      HasTy D S Γ (.GreaterThan a b) .BooleanType
  | sLe {a b : Expr} {w : Int} :
      HasTy D S Γ a (.BVType true w) → HasTy D S Γ b (.BVType true w) →
      HasTy D S Γ (.LessEquals a b) .BooleanType
  | sGe {a b : Expr} {w : Int} :
      HasTy D S Γ a (.BVType true w) → HasTy D S Γ b (.BVType true w) →
      HasTy D S Γ (.GreaterEquals a b) .BooleanType
  | u2s {a : Expr} {w : Int} : HasTy D S Γ a (.BVType false w) →
      HasTy D S Γ (.BVUnsignedToSigned a) (.BVType true w)
  | s2u {a : Expr} {w : Int} : HasTy D S Γ a (.BVType true w) →
      HasTy D S Γ (.BVSignedToUnsigned a) (.BVType false w)
  | bvAnd {a b : Expr} {s : Bool} {w : Int} :
      HasTy D S Γ a (.BVType s w) → HasTy D S Γ b (.BVType s w) →
      HasTy D S Γ (.BVAnd a b) (.BVType s w)
  | bvOr {a b : Expr} {s : Bool} {w : Int} :
      HasTy D S Γ a (.BVType s w) → HasTy D S Γ b (.BVType s w) →
      HasTy D S Γ (.BVOr a b) (.BVType s w)
  | bvXor {a b : Expr} {s : Bool} {w : Int} :
      HasTy D S Γ a (.BVType s w) → HasTy D S Γ b (.BVType s w) →
      HasTy D S Γ (.BVXor a b) (.BVType s w)
  | bvShl {a b : Expr} {s : Bool} {w : Int} :
      HasTy D S Γ a (.BVType s w) → HasTy D S Γ b (.BVType s w) →
      HasTy D S Γ (.BVShiftLeft a b) (.BVType s w)
  | bvAShr {a b : Expr} {s : Bool} {w : Int} :
      HasTy D S Γ a (.BVType s w) → HasTy D S Γ b (.BVType s w) →
      HasTy D S Γ (.BVAShiftRight a b) (.BVType s w)
  | bvLShr {a b : Expr} {s : Bool} {w : Int} :
      HasTy D S Γ a (.BVType s w) → HasTy D S Γ b (.BVType s w) →
      HasTy D S Γ (.BVLShiftRight a b) (.BVType s w)
  | narrow {a : Expr} {s : Bool} {w v : Int} : HasTy D S Γ a (.BVType s w) → 0 < v → v < w →
      HasTy D S Γ (.BVNarrowingCast a v) (.BVType s v)
  | widen {a : Expr} {s : Bool} {w v : Int} : HasTy D S Γ a (.BVType s w) → w < v →
      HasTy D S Γ (.BVWideningCast a v) (.BVType s v)
  | frac {n d : Int} : d ≠ 0 → HasTy D S Γ (.FractionLiteral n d) .RealType
  | rPlus {a b : Expr} : HasTy D S Γ a .RealType → HasTy D S Γ b .RealType →
      HasTy D S Γ (.Plus a b) .RealType
  | rMinus {a b : Expr} : HasTy D S Γ a .RealType → HasTy D S Γ b .RealType →
      HasTy D S Γ (.Minus a b) .RealType
  | rTimes {a b : Expr} : HasTy D S Γ a .RealType → HasTy D S Γ b .RealType →
      HasTy D S Γ (.Times a b) .RealType
  | rDiv {a b : Expr} : HasTy D S Γ a .RealType → HasTy D S Γ b .RealType →
      HasTy D S Γ (.Division a b) .RealType
  | rNeg {a : Expr} : HasTy D S Γ a .RealType → HasTy D S Γ (.UMinus a) .RealType
  | rLt {a b : Expr} : HasTy D S Γ a .RealType → HasTy D S Γ b .RealType →
      HasTy D S Γ (.LessThan a b) .BooleanType
  | rGt {a b : Expr} : HasTy D S Γ a .RealType → HasTy D S Γ b .RealType →
      HasTy D S Γ (.GreaterThan a b) .BooleanType
  | rLe {a b : Expr} : HasTy D S Γ a .RealType → HasTy D S Γ b .RealType →
      HasTy D S Γ (.LessEquals a b) .BooleanType
  | rGe {a b : Expr} : HasTy D S Γ a .RealType → HasTy D S Γ b .RealType →
      HasTy D S Γ (.GreaterEquals a b) .BooleanType
  | invoke {s : Sig} {args : List Expr} : findSig S s.name = some s →
      args.length = s.params.length →
      (∀ p ∈ args.zip (s.params.map Prod.snd), HasTy D S Γ p.1 p.2) →
      HasTy D S Γ (.FunctionInvocation s.name [] args) s.ret
  | assume {p b : Expr} {T : Ty} : HasTy D S Γ p .BooleanType → HasTy D S Γ b T →
      HasTy D S Γ (.Assume p b) T
  | adt {c : Id} {d : Data} {i : Nat} {fs : List (Id × Ty)} {args : List Expr} :
      findCtor D c = some (d, i, fs) → args.length = fs.length →
      (∀ p ∈ args.zip (fs.map Prod.snd), HasTy D S Γ p.1 p.2) →
      HasTy D S Γ (.ADT c [] args) (.ADTType d.name [])
  | isCons {a : Expr} {c : Id} {d : Data} {i : Nat} {fs : List (Id × Ty)} :
      findCtor D c = some (d, i, fs) → HasTy D S Γ a (.ADTType d.name []) →
      HasTy D S Γ (.IsConstructor a c) .BooleanType
  | sel {a : Expr} {x : Id} {d : Data} {i j : Nat} {T : Ty} :
      findSel D x = some (d, i, j, T) → HasTy D S Γ a (.ADTType d.name []) →
      HasTy D S Γ (.ADTSelector a x) T
  | setEmpty {A : Ty} : FragTy D A → HasTy D S Γ (.FiniteSet [] A) (.SetType A)
  | setOne {a : Expr} {A : Ty} : HasTy D S Γ a A → HasTy D S Γ (.FiniteSet [a] A) (.SetType A)
  | setAdd {s a : Expr} {A : Ty} : HasTy D S Γ s (.SetType A) → HasTy D S Γ a A →
      HasTy D S Γ (.SetAdd s a) (.SetType A)
  | elementOf {a s : Expr} {A : Ty} : HasTy D S Γ a A → HasTy D S Γ s (.SetType A) →
      HasTy D S Γ (.ElementOfSet a s) .BooleanType
  | subsetOf {s u : Expr} {A : Ty} : HasTy D S Γ s (.SetType A) → HasTy D S Γ u (.SetType A) →
      HasTy D S Γ (.SubsetOf s u) .BooleanType
  | setUnion {s u : Expr} {A : Ty} : HasTy D S Γ s (.SetType A) → HasTy D S Γ u (.SetType A) →
      HasTy D S Γ (.SetUnion s u) (.SetType A)
  | setInter {s u : Expr} {A : Ty} : HasTy D S Γ s (.SetType A) → HasTy D S Γ u (.SetType A) →
      HasTy D S Γ (.SetIntersection s u) (.SetType A)
  | setDiff {s u : Expr} {A : Ty} : HasTy D S Γ s (.SetType A) → HasTy D S Γ u (.SetType A) →
      HasTy D S Γ (.SetDifference s u) (.SetType A)

theorem HasTy.fragTy {S : List Sig} (hS : SigOk D S) {Γ : List (Id × Ty)} {e : Expr} {T : Ty}
    (h : HasTy D S Γ e T) : FragTy D T := by
  induction h with
  | var _ hT => exact hT
  | ite _ _ _ _ iha _ => exact iha
  | invoke hs _ _ _ => exact hS.ret _ (findSig_spec hs).1
  | assume _ _ _ ihb => exact ihb
  | adt hc _ _ _ => exact fragTy_data hS.data (findCtor_spec hc).1
  | sel hx _ _ =>
    obtain ⟨hd, c, fs, hi, hj⟩ := findSel_spec hx
    exact hS.data.fields _ hd (c, fs) (List.mem_of_getElem? hi) _ (List.mem_of_getElem? hj)
  | bvLit hw _ _ => exact hw
  | bvPlus _ _ ih _ | bvMinus _ _ ih _ | bvTimes _ _ ih _ | bvDiv _ _ ih _ | bvRem _ _ ih _
    | bvNeg _ ih | bvNot _ ih | bvMod _ _ ih _ | sDiv _ _ ih _ | sRem _ _ ih _ | sMod _ _ ih _
    | u2s _ ih | s2u _ ih | bvAnd _ _ ih _ | bvOr _ _ ih _ | bvXor _ _ ih _ | bvShl _ _ ih _
    | bvAShr _ _ ih _ | bvLShr _ _ ih _ => exact ih
  | narrow _ hv _ _ => exact hv
  | widen _ hwv ih => exact Int.lt_trans ih hwv
  | setEmpty hA => exact hA
  | setOne _ ih => exact ih
  | setAdd _ _ ih _ | setUnion _ _ ih _ | setInter _ _ ih _ | setDiff _ _ ih _ => exact ih
  | _ => trivial

/-- The program `P` has the functions of `S`, of bodies of their types, with no type parameters. -/
def ProgTy (D : List Data) (S : List Sig) : Program → Prop
  | .Program fs cs ss is eq => (∀ s ∈ S, ∃ body, lookup_fun fs s.name =
      .Ok (.FunDef s.name [] (s.params.map Prod.fst) body) ∧ HasTy D S s.params body s.ret) ∧
    ProgData D (.Program fs cs ss is eq)

theorem ProgTy.data {D : List Data} {S : List Sig} {P : Program} (h : ProgTy D S P) :
    ProgData D P := by
  cases P; exact h.2

/-! ## The translation -/

/-- The application of `f` to the arguments `as`, one at a time. -/
def spine (f : SmtTerm) : List SmtTerm → SmtTerm
  | [] => f
  | a :: as => spine (.Apply f a) as

/-- The conjunction of `ts`. -/
def andT : List SmtTerm → SmtTerm
  | [] => .Boolean true
  | t :: ts => .and t (andT ts)

/-- The disjunction of `ts`. -/
def orT : List SmtTerm → SmtTerm
  | [] => .Boolean false
  | t :: ts => .or t (orT ts)

/-- Whether a type is of bit-vectors. -/
def _root_.Inox.Semantics.Ty.isBv : Ty → Bool
  | .BVType _ _ => true
  | _ => false

/-- Whether the expression `e` of the fragment is of a type of bit-vectors, which chooses the
operators of its term: SMT-LIB has others for the bit-vectors than for the integers. -/
def isBv (D : List Data) (S : List Sig) (Γ : List (Id × Ty)) : Expr → Bool
  | .Variable x =>
    match Γ.lookup x with
    | some T => T.isBv
    | none => false
  | .BVLiteral _ _ _ => true
  | .IfExpr _ a _ => isBv D S Γ a
  | .Plus a _ | .Minus a _ | .Times a _ | .Division a _ | .Remainder a _ | .Modulo a _
  | .UMinus a | .BVNot a => isBv D S Γ a
  | .BVUnsignedToSigned _ | .BVSignedToUnsigned _ | .BVAnd _ _ | .BVOr _ _ | .BVXor _ _
  | .BVShiftLeft _ _ | .BVAShiftRight _ _ | .BVLShiftRight _ _ | .BVNarrowingCast _ _
  | .BVWideningCast _ _ => true
  | .FunctionInvocation f _ _ =>
    match findSig S f with
    | some s => s.ret.isBv
    | none => false
  | .Assume _ b => isBv D S Γ b
  | .ADTSelector _ x =>
    match findSel D x with
    | some (_, _, _, T) => T.isBv
    | none => false
  | _ => false

theorem isBv_eq {S : List Sig} {Γ : List (Id × Ty)} {e : Expr} {T : Ty}
    (h : HasTy D S Γ e T) : isBv D S Γ e = T.isBv := by
  induction h with
  | var hx _ => simp only [isBv, hx]
  | ite _ _ _ _ iha _ => simpa only [isBv] using iha
  | invoke hs _ _ _ => simp only [isBv, hs]
  | assume _ _ _ ihb => simpa only [isBv] using ihb
  | sel hx _ _ => simp only [isBv, hx]
  | plus _ _ iha _ | minus _ _ iha _ | times _ _ iha _ | div _ _ iha _ | rem _ _ iha _
    | mod _ _ iha _
    | uminus _ iha | bvPlus _ _ iha _ | bvMinus _ _ iha _ | bvTimes _ _ iha _
    | bvDiv _ _ iha _ | bvRem _ _ iha _ | bvNeg _ iha | bvNot _ iha | rPlus _ _ iha _
    | rMinus _ _ iha _ | rTimes _ _ iha _ | rDiv _ _ iha _ | rNeg _ iha | bvMod _ _ iha _
    | sDiv _ _ iha _ | sRem _ _ iha _ | sMod _ _ iha _ =>
    simpa only [isBv] using iha
  | _ => rfl

/-- Whether a type is of signed bit-vectors. -/
def _root_.Inox.Semantics.Ty.isSigned : Ty → Bool
  | .BVType true _ => true
  | _ => false

/-- Whether the expression `e` of the fragment is of a type of signed bit-vectors, which chooses
the division, the remainder, the modulo and the comparisons of its term. -/
def isSigned (D : List Data) (S : List Sig) (Γ : List (Id × Ty)) : Expr → Bool
  | .Variable x =>
    match Γ.lookup x with
    | some T => T.isSigned
    | none => false
  | .BVLiteral s _ _ => s
  | .IfExpr _ a _ => isSigned D S Γ a
  | .Plus a _ | .Minus a _ | .Times a _ | .Division a _ | .Remainder a _ | .Modulo a _
  | .UMinus a | .BVNot a | .BVAnd a _ | .BVOr a _ | .BVXor a _ | .BVShiftLeft a _
  | .BVAShiftRight a _ | .BVLShiftRight a _ | .BVNarrowingCast a _ | .BVWideningCast a _ =>
    isSigned D S Γ a
  | .BVUnsignedToSigned _ => true
  | .FunctionInvocation f _ _ =>
    match findSig S f with
    | some s => s.ret.isSigned
    | none => false
  | .Assume _ b => isSigned D S Γ b
  | .ADTSelector _ x =>
    match findSel D x with
    | some (_, _, _, T) => T.isSigned
    | none => false
  | _ => false

theorem isSigned_eq {S : List Sig} {Γ : List (Id × Ty)} {e : Expr} {T : Ty}
    (h : HasTy D S Γ e T) : isSigned D S Γ e = T.isSigned := by
  induction h with
  | var hx _ => simp only [isSigned, hx]
  | ite _ _ _ _ iha _ => simpa only [isSigned] using iha
  | invoke hs _ _ _ => simp only [isSigned, hs]
  | assume _ _ _ ihb => simpa only [isSigned] using ihb
  | sel hx _ _ => simp only [isSigned, hx]
  | @bvLit s _ _ _ _ _ => cases s <;> rfl
  | plus _ _ iha _ | minus _ _ iha _ | times _ _ iha _ | div _ _ iha _ | rem _ _ iha _
    | mod _ _ iha _
    | uminus _ iha | bvPlus _ _ iha _ | bvMinus _ _ iha _ | bvTimes _ _ iha _
    | bvDiv _ _ iha _ | bvRem _ _ iha _ | bvNeg _ iha | bvNot _ iha | rPlus _ _ iha _
    | rMinus _ _ iha _ | rTimes _ _ iha _ | rDiv _ _ iha _ | rNeg _ iha | bvMod _ _ iha _
    | sDiv _ _ iha _ | sRem _ _ iha _ | sMod _ _ iha _ | bvAnd _ _ iha _ | bvOr _ _ iha _
    | bvXor _ _ iha _ | bvShl _ _ iha _ | bvAShr _ _ iha _ | bvLShr _ _ iha _ =>
    simpa only [isSigned] using iha
  | @narrow _ s _ _ _ _ _ iha | @widen _ s _ _ _ _ iha =>
    cases s <;> simpa only [isSigned, Ty.isSigned] using iha
  | _ => rfl

/-- The width of a type of bit-vectors. -/
def _root_.Inox.Semantics.Ty.width : Ty → Int
  | .BVType _ w => w
  | _ => 0

/-- The width of the expression `e` of the fragment, when it is of a type of bit-vectors, which
gives the number of bits that a widening adds. -/
def width (D : List Data) (S : List Sig) (Γ : List (Id × Ty)) : Expr → Int
  | .Variable x =>
    match Γ.lookup x with
    | some T => T.width
    | none => 0
  | .BVLiteral _ w _ => w
  | .IfExpr _ a _ => width D S Γ a
  | .Plus a _ | .Minus a _ | .Times a _ | .Division a _ | .Remainder a _ | .Modulo a _
  | .UMinus a | .BVNot a | .BVAnd a _ | .BVOr a _ | .BVXor a _ | .BVShiftLeft a _
  | .BVAShiftRight a _ | .BVLShiftRight a _ | .BVUnsignedToSigned a | .BVSignedToUnsigned a =>
    width D S Γ a
  | .BVNarrowingCast _ v | .BVWideningCast _ v => v
  | .FunctionInvocation f _ _ =>
    match findSig S f with
    | some s => s.ret.width
    | none => 0
  | .Assume _ b => width D S Γ b
  | .ADTSelector _ x =>
    match findSel D x with
    | some (_, _, _, T) => T.width
    | none => 0
  | _ => 0

theorem width_eq {S : List Sig} {Γ : List (Id × Ty)} {e : Expr} {T : Ty}
    (h : HasTy D S Γ e T) : width D S Γ e = T.width := by
  induction h with
  | var hx _ => simp only [width, hx]
  | ite _ _ _ _ iha _ => simpa only [width] using iha
  | invoke hs _ _ _ => simp only [width, hs]
  | assume _ _ _ ihb => simpa only [width] using ihb
  | sel hx _ _ => simp only [width, hx]
  | plus _ _ iha _ | minus _ _ iha _ | times _ _ iha _ | div _ _ iha _ | rem _ _ iha _
    | mod _ _ iha _
    | uminus _ iha | bvPlus _ _ iha _ | bvMinus _ _ iha _ | bvTimes _ _ iha _
    | bvDiv _ _ iha _ | bvRem _ _ iha _ | bvNeg _ iha | bvNot _ iha | rPlus _ _ iha _
    | rMinus _ _ iha _ | rTimes _ _ iha _ | rDiv _ _ iha _ | rNeg _ iha | bvMod _ _ iha _
    | sDiv _ _ iha _ | sRem _ _ iha _ | sMod _ _ iha _ | bvAnd _ _ iha _ | bvOr _ _ iha _
    | bvXor _ _ iha _ | bvShl _ _ iha _ | bvAShr _ _ iha _ | bvLShr _ _ iha _ =>
    simpa only [width] using iha
  | u2s _ iha | s2u _ iha => simpa only [width, Ty.width] using iha
  | _ => rfl

/-- Whether a type is that of the reals. -/
def _root_.Inox.Semantics.Ty.isReal : Ty → Bool
  | .RealType => true
  | _ => false

/-- Whether the expression `e` of the fragment is a real, which chooses the division of its
term. -/
def isReal (D : List Data) (S : List Sig) (Γ : List (Id × Ty)) : Expr → Bool
  | .Variable x =>
    match Γ.lookup x with
    | some T => T.isReal
    | none => false
  | .FractionLiteral _ _ => true
  | .IfExpr _ a _ => isReal D S Γ a
  | .Plus a _ | .Minus a _ | .Times a _ | .Division a _ | .Remainder a _ | .UMinus a
  | .BVNot a => isReal D S Γ a
  | .FunctionInvocation f _ _ =>
    match findSig S f with
    | some s => s.ret.isReal
    | none => false
  | .Assume _ b => isReal D S Γ b
  | .ADTSelector _ x =>
    match findSel D x with
    | some (_, _, _, T) => T.isReal
    | none => false
  | _ => false

theorem isReal_eq {S : List Sig} {Γ : List (Id × Ty)} {e : Expr} {T : Ty}
    (h : HasTy D S Γ e T) : isReal D S Γ e = T.isReal := by
  induction h with
  | var hx _ => simp only [isReal, hx]
  | ite _ _ _ _ iha _ => simpa only [isReal] using iha
  | invoke hs _ _ _ => simp only [isReal, hs]
  | assume _ _ _ ihb => simpa only [isReal] using ihb
  | sel hx _ _ => simp only [isReal, hx]
  | plus _ _ iha _ | minus _ _ iha _ | times _ _ iha _ | div _ _ iha _ | rem _ _ iha _
    | uminus _ iha | bvPlus _ _ iha _ | bvMinus _ _ iha _ | bvTimes _ _ iha _
    | bvDiv _ _ iha _ | bvRem _ _ iha _ | bvNeg _ iha | bvNot _ iha | rPlus _ _ iha _
    | rMinus _ _ iha _ | rTimes _ _ iha _ | rDiv _ _ iha _ | rNeg _ iha | sDiv _ _ iha _
    | sRem _ _ iha _ =>
    simpa only [isReal] using iha
  | _ => rfl

/-- The term of an integer of a fraction, as Inox prints it: the opposite of a numeral when it is
negative. -/
def lit (k : Int) : SmtTerm := if 0 ≤ k then .Numeral k else .uneg (.Numeral (-k))

theorem lit_typeof (k : Int) : __smtx_typeof (lit k) = .Int := by
  unfold lit; split <;> rfl

theorem lit_eval (M : SmtModel) (k : Int) : __smtx_model_eval M (lit k) = .Numeral k := by
  unfold lit; split <;> simp [__smtx_model_eval, __smtx_model_eval_uneg, native_zneg]

mutual
/-- The term of the expression `e` of the fragment: a variable is the constant named after it, of
the sort of its type, and a call the application of the constant named after the function. -/
def tr (D : List Data) (S : List Sig) (Γ : List (Id × Ty)) : Expr → SmtTerm
  | .Variable x =>
    match Γ.lookup x with
    | some T => .UConst (nm x) (trT D T)
    | none => .Boolean false
  | .IntegerLiteral i => .Numeral i
  | .BooleanLiteral b => .Boolean b
  | .IfExpr c a b => .ite (tr D S Γ c) (tr D S Γ a) (tr D S Γ b)
  | .And es => andT (trs D S Γ es)
  | .Or es => orT (trs D S Γ es)
  | .Not a => .not (tr D S Γ a)
  | .Implies a b => .imp (tr D S Γ a) (tr D S Γ b)
  | .Equals a b => .eq (tr D S Γ a) (tr D S Γ b)
  | .BVLiteral _ w x => .Binary w x
  | .FractionLiteral n d => .qdiv (lit n) (lit d)
  | .Plus a b =>
    if isBv D S Γ a then .bvadd (tr D S Γ a) (tr D S Γ b) else .plus (tr D S Γ a) (tr D S Γ b)
  | .Minus a b =>
    if isBv D S Γ a then .bvsub (tr D S Γ a) (tr D S Γ b) else .neg (tr D S Γ a) (tr D S Γ b)
  | .Times a b =>
    if isBv D S Γ a then .bvmul (tr D S Γ a) (tr D S Γ b) else .mult (tr D S Γ a) (tr D S Γ b)
  | .Division a b =>
    if isBv D S Γ a then
      if isSigned D S Γ a then .bvsdiv (tr D S Γ a) (tr D S Γ b)
      else .bvudiv (tr D S Γ a) (tr D S Γ b)
    else if isReal D S Γ a then .qdiv (tr D S Γ a) (tr D S Γ b)
    else .div (tr D S Γ a) (tr D S Γ b)
  | .Remainder a b =>
    if isBv D S Γ a then
      if isSigned D S Γ a then .bvsrem (tr D S Γ a) (tr D S Γ b)
      else .bvurem (tr D S Γ a) (tr D S Γ b)
    else .mod (tr D S Γ a) (tr D S Γ b)
  | .Modulo a b =>
    if isBv D S Γ a then
      if isSigned D S Γ a then .bvsmod (tr D S Γ a) (tr D S Γ b)
      else .bvurem (tr D S Γ a) (tr D S Γ b)
    else .mod (tr D S Γ a) (tr D S Γ b)
  | .BVUnsignedToSigned a | .BVSignedToUnsigned a => tr D S Γ a
  | .UMinus a => if isBv D S Γ a then .bvneg (tr D S Γ a) else .uneg (tr D S Γ a)
  | .BVNot a => .bvnot (tr D S Γ a)
  | .BVAnd a b => .bvand (tr D S Γ a) (tr D S Γ b)
  | .BVOr a b => .bvor (tr D S Γ a) (tr D S Γ b)
  | .BVXor a b => .bvxor (tr D S Γ a) (tr D S Γ b)
  | .BVShiftLeft a b => .bvshl (tr D S Γ a) (tr D S Γ b)
  | .BVAShiftRight a b => .bvashr (tr D S Γ a) (tr D S Γ b)
  | .BVLShiftRight a b => .bvlshr (tr D S Γ a) (tr D S Γ b)
  | .BVNarrowingCast a v => .extract (.Numeral (v - 1)) (.Numeral 0) (tr D S Γ a)
  | .BVWideningCast a v =>
    if isSigned D S Γ a then .sign_extend (.Numeral (v - width D S Γ a)) (tr D S Γ a)
    else .zero_extend (.Numeral (v - width D S Γ a)) (tr D S Γ a)
  | .LessThan a b =>
    if isBv D S Γ a then
      if isSigned D S Γ a then .bvslt (tr D S Γ a) (tr D S Γ b)
      else .bvult (tr D S Γ a) (tr D S Γ b)
    else .lt (tr D S Γ a) (tr D S Γ b)
  | .GreaterThan a b =>
    if isBv D S Γ a then
      if isSigned D S Γ a then .bvsgt (tr D S Γ a) (tr D S Γ b)
      else .bvugt (tr D S Γ a) (tr D S Γ b)
    else .gt (tr D S Γ a) (tr D S Γ b)
  | .LessEquals a b =>
    if isBv D S Γ a then
      if isSigned D S Γ a then .bvsle (tr D S Γ a) (tr D S Γ b)
      else .bvule (tr D S Γ a) (tr D S Γ b)
    else .leq (tr D S Γ a) (tr D S Γ b)
  | .GreaterEquals a b =>
    if isBv D S Γ a then
      if isSigned D S Γ a then .bvsge (tr D S Γ a) (tr D S Γ b)
      else .bvuge (tr D S Γ a) (tr D S Γ b)
    else .geq (tr D S Γ a) (tr D S Γ b)
  | .FunctionInvocation f _ args =>
    match findSig S f with
    | some s => spine (.UConst (nm f) (s.toDef D).ty) (trs D S Γ args)
    | none => .Boolean false
  | .Assume _ b => tr D S Γ b
  | .ADT c _ args =>
    match findCtor D c with
    | some (d, i, _) => spine (.DtCons (nm d.name) d.decl i) (trs D S Γ args)
    | none => .Boolean false
  | .IsConstructor a c =>
    match findCtor D c with
    | some (d, i, _) => .Apply (.DtTester (nm d.name) d.decl i) (tr D S Γ a)
    | none => .Boolean false
  | .ADTSelector a x =>
    match findSel D x with
    | some (d, i, j, _) => .Apply (.DtSel (nm d.name) d.decl i j) (tr D S Γ a)
    | none => .Boolean false
  | .FiniteSet es A =>
    match trs D S Γ es with
    | [] => .set_empty (trT D A)
    | [t] => .set_singleton t
    | _ => .Boolean false
  | .SetAdd s a => .set_union (.set_singleton (tr D S Γ a)) (tr D S Γ s)
  | .ElementOfSet a s => .set_member (tr D S Γ a) (tr D S Γ s)
  | .SubsetOf s u => .set_subset (tr D S Γ s) (tr D S Γ u)
  | .SetUnion s u => .set_union (tr D S Γ s) (tr D S Γ u)
  | .SetIntersection s u => .set_inter (tr D S Γ s) (tr D S Γ u)
  | .SetDifference s u => .set_minus (tr D S Γ s) (tr D S Γ u)
  | _ => .Boolean false

def trs (D : List Data) (S : List Sig) (Γ : List (Id × Ty)) : List Expr → List SmtTerm
  | [] => []
  | e :: es => tr D S Γ e :: trs D S Γ es
end

theorem trs_eq (S : List Sig) (Γ : List (Id × Ty)) :
    ∀ es : List Expr, trs D S Γ es = es.map (tr D S Γ)
  | [] => by simp [trs]
  | e :: es => by simp [trs, trs_eq S Γ es]

/-! ## Lists of pairs -/

theorem forall₂_of_zip {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, l.length = m.length → (∀ p ∈ l.zip m, R p.1 p.2) →
      List.Forall₂ R l m
  | [], [], _, _ => .nil
  | a :: l, b :: m, hl, h =>
    .cons (h (a, b) (.head _))
      (forall₂_of_zip (by simpa using hl) (fun p hp => h p (.tail _ hp)))

theorem forall₂_of_zip_map {α β γ : Type} {R : α → γ → Prop} {Q : β → Prop}
    {g : β → γ} :
    ∀ {l : List α} {m : List β}, l.length = m.length →
      (∀ p ∈ l.zip (m.map g), R p.1 p.2) →
      (∀ b ∈ m, Q b) → List.Forall₂ (fun a b => R a (g b) ∧ Q b) l m
  | [], [], _, _, _ => .nil
  | a :: l, b :: m, hl, h, hQ =>
    .cons ⟨h (a, g b) (.head _), hQ b (.head _)⟩
      (forall₂_of_zip_map (by simpa using hl) (fun p hp => h p (.tail _ hp))
        (fun c hc => hQ c (.tail _ hc)))

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {m : List β} {j : Nat}
    {a : α} {b : β}, List.Forall₂ R l m → l[j]? = some a → m[j]? = some b → R a b
  | _ :: _, _ :: _, 0, _, _, .cons h _, ha, hb => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
    subst ha; subst hb; exact h
  | _ :: _, _ :: _, j + 1, _, _, .cons _ hs, ha, hb => by
    simp only [List.getElem?_cons_succ] at ha hb
    exact forall₂_getElem? hs ha hb

theorem forall₂_map_left {α β γ : Type} {R : γ → β → Prop} {f : α → γ} :
    ∀ {l : List α} {m : List β}, List.Forall₂ (fun a b => R (f a) b) l m →
      List.Forall₂ R (l.map f) m
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => .cons h (forall₂_map_left hs)

theorem forall₂_imp {α β : Type} {R Q : α → β → Prop} (hRQ : ∀ a b, R a b → Q a b) :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → List.Forall₂ Q l m
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => .cons (hRQ _ _ h) (forall₂_imp hRQ hs)

/-! ## The sorts of the translation -/

theorem typeof_uconst_wf {s : native_String} {T : SmtType} (h : __smtx_type_wf T = true) :
    __smtx_typeof (.UConst s T) = T := by
  simp only [__smtx_typeof, __smtx_typeof_guard_wf, native_ite, h, ↓reduceIte]

theorem toDef_ty_wf {D : List Data} (hD : DataOk D) {s : Sig}
    (hp : ∀ p ∈ s.params, FragTy D p.2) (hr : FragTy D s.ret) :
    __smtx_type_wf (s.toDef D).ty = true := by
  apply fragTy_wf_arrow _ (trT_wf hD hr)
  intro p hp'
  simp only [ptys, List.mem_map] at hp'
  obtain ⟨q, hq, rfl⟩ := hp'
  exact trT_component hD (hp q hq)

set_option linter.internalConstructors false in
theorem typeof_apply_plain {f : SmtTerm} (h : plainHead f = true) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply f x) =
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
  cases f <;> first | (simp [plainHead] at h; done) | simp only [__smtx_typeof]

theorem typeof_spine {D : List Data} (hD : DataOk D) {R : SmtType} :
    ∀ (ps : List (Id × Ty)) (f : SmtTerm) (ts : List SmtTerm), plainHead f = true →
      __smtx_typeof f = arrow (ptys D ps) R →
      List.Forall₂ (fun t p => __smtx_typeof t = trT D p.2 ∧ FragTy D p.2) ts ps →
      __smtx_typeof (spine f ts) = R
  | [], _, [], _, hf, .nil => hf
  | p :: ps, f, t :: ts, hpl, hf, .cons ⟨ht, hp⟩ hs => by
    apply typeof_spine hD ps (.Apply f t) ts rfl _ hs
    rw [typeof_apply_plain hpl, hf, ht]
    simp only [ptys, List.map_cons, arrow, __smtx_typeof_apply, __smtx_typeof_guard, native_ite,
      native_Teq, trT_ne hD hp, decide_false, decide_true, Bool.false_eq_true, ↓reduceIte]

theorem typeof_andT : ∀ ts : List SmtTerm, (∀ t ∈ ts, __smtx_typeof t = .Bool) →
    __smtx_typeof (andT ts) = .Bool
  | [], _ => rfl
  | t :: ts, h => by
    simp only [andT, __smtx_typeof, native_ite, native_Teq, h t (.head _),
      typeof_andT ts (fun u hu => h u (.tail _ hu)), decide_true, ↓reduceIte]

theorem typeof_orT : ∀ ts : List SmtTerm, (∀ t ∈ ts, __smtx_typeof t = .Bool) →
    __smtx_typeof (orT ts) = .Bool
  | [], _ => rfl
  | t :: ts, h => by
    simp only [orT, __smtx_typeof, native_ite, native_Teq, h t (.head _),
      typeof_orT ts (fun u hu => h u (.tail _ hu)), decide_true, ↓reduceIte]

theorem typeof_spine_chain {T0 : SmtType} :
    ∀ (Us : List SmtType) (f : SmtTerm) (ts : List SmtTerm), plainHead f = true →
      __smtx_typeof f = chainT T0 Us →
      List.Forall₂ (fun t U => __smtx_typeof t = U ∧ U ≠ .None) ts Us →
      __smtx_typeof (spine f ts) = T0
  | [], _, [], _, hf, .nil => hf
  | U :: Us, f, t :: ts, hpl, hf, .cons ⟨ht, hU⟩ hs => by
    apply typeof_spine_chain Us (.Apply f t) ts rfl _ hs
    rw [typeof_apply_plain hpl, hf, ht]
    simp [chainT, __smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hU]

/-- The sort of the constructor of index `i` of a datatype of `D`. -/
theorem typeof_dtCons {D : List Data} (hD : DataOk D) {d : Data} (hd : d ∈ D) {c : Id}
    {i : Nat} {fs : List (Id × Ty)} (hi : d.ctors[i]? = some (c, fs)) :
    __smtx_typeof (.DtCons (nm d.name) d.decl i) =
      chainT (.Datatype (nm d.name) d.decl) (fs.map fun f => trT D f.2) := by
  simp only [__smtx_typeof, __smtx_typeof_guard_wf, native_ite, hD.wf d hd, ↓reduceIte, cons_rec,
    ctorFields_data hD hd, hi, Option.map_some, Option.getD_some]

/-- The translation of an expression of type `T` is a term of the sort of `T`. -/
theorem tr_typeof {S : List Sig} (hS : SigOk D S) {Γ : List (Id × Ty)} {e : Expr} {T : Ty}
    (h : HasTy D S Γ e T) : __smtx_typeof (tr D S Γ e) = trT D T := by
  induction h with
  | var hx hT => simp only [tr, hx]; exact typeof_uconst_wf (trT_wf hS.data hT)
  | int i => rfl
  | bool b => rfl
  | ite hc ha hb ihc iha ihb =>
    simp only [tr, __smtx_typeof, ihc, iha, ihb, trT, __smtx_typeof_ite, native_ite, native_Teq,
      decide_true, ↓reduceIte]
  | and _ ih =>
    simp only [tr, trs_eq]; apply typeof_andT
    intro t ht; simp only [List.mem_map] at ht; obtain ⟨e, he, rfl⟩ := ht; exact ih e he
  | or _ ih =>
    simp only [tr, trs_eq]; apply typeof_orT
    intro t ht; simp only [List.mem_map] at ht; obtain ⟨e, he, rfl⟩ := ht; exact ih e he
  | not _ ih => simp only [tr, __smtx_typeof, ih, trT, native_ite, native_Teq, decide_true,
      ↓reduceIte]
  | implies _ _ iha ihb => simp only [tr, __smtx_typeof, iha, ihb, trT, native_ite, native_Teq,
      decide_true, ↓reduceIte]
  | equals ha _ iha ihb =>
    simp only [tr, __smtx_typeof, iha, ihb, __smtx_typeof_eq, __smtx_typeof_guard, native_ite,
      native_Teq, trT_ne hS.data (ha.fragTy hS), decide_false, decide_true, Bool.false_eq_true,
      ↓reduceIte]
    rfl
  | plus ha _ iha ihb | minus ha _ iha ihb | times ha _ iha ihb | div ha _ iha ihb
    | rem ha _ iha ihb | mod ha _ iha ihb | rPlus ha _ iha ihb | rMinus ha _ iha ihb
    | rTimes ha _ iha ihb | rDiv ha _ iha ihb =>
    simp only [tr, isBv_eq ha, isReal_eq ha, Ty.isBv, Ty.isReal, Bool.false_eq_true, ↓reduceIte,
      __smtx_typeof, iha, ihb, trT]
    rfl
  | frac _ => simp only [tr, __smtx_typeof, lit_typeof]; rfl
  | uminus ha ih | rNeg ha ih =>
    simp only [tr, isBv_eq ha, Ty.isBv, Bool.false_eq_true, ↓reduceIte, __smtx_typeof, ih, trT]
    rfl
  | lt ha _ iha ihb | gt ha _ iha ihb | le ha _ iha ihb | ge ha _ iha ihb | rLt ha _ iha ihb
    | rGt ha _ iha ihb | rLe ha _ iha ihb | rGe ha _ iha ihb =>
    simp only [tr, isBv_eq ha, Ty.isBv, Bool.false_eq_true, ↓reduceIte, __smtx_typeof, iha, ihb,
      trT]
    rfl
  | @bvLit _ w x hw h0 hx =>
    have hm : native_zeq x (native_mod_total x (native_int_pow2 w)) = true := by
      simp [native_zeq, native_mod_total, int_pow2_eq (Int.le_of_lt hw), Int.emod_eq_of_lt h0 hx]
    simp [tr, trT, __smtx_typeof, native_ite, native_and, native_zleq, Int.le_of_lt hw, hm,
      native_int_to_nat]
  | bvPlus ha _ iha ihb | bvMinus ha _ iha ihb | bvTimes ha _ iha ihb | bvDiv ha _ iha ihb
    | bvRem ha _ iha ihb | bvMod ha _ iha ihb | sDiv ha _ iha ihb | sRem ha _ iha ihb
    | sMod ha _ iha ihb | bvAnd ha _ iha ihb | bvOr ha _ iha ihb | bvXor ha _ iha ihb
    | bvShl ha _ iha ihb | bvAShr ha _ iha ihb | bvLShr ha _ iha ihb =>
    simp [tr, isBv_eq ha, isSigned_eq ha, Ty.isBv, Ty.isSigned, __smtx_typeof, iha, ihb, trT,
      __smtx_typeof_bv_op_2, native_ite, native_nateq]
  | @narrow _ _ w v ha hv hvw ih =>
    simp [tr, __smtx_typeof, ih, trT, __smtx_typeof_extract, native_ite, native_zleq,
      native_zlt, native_zplus, native_zneg, native_nat_to_int, native_int_to_nat, hv]
    have h2 : v - 1 < w := by omega
    exact fun h => absurd h (Int.not_le.mpr h2)
  | @widen _ s w v ha hwv ih =>
    have hw : 0 < w := ha.fragTy hS
    cases s <;>
      simp [tr, isSigned_eq ha, width_eq ha, Ty.width, Ty.isSigned, __smtx_typeof, ih, trT,
        __smtx_typeof_zero_extend, __smtx_typeof_sign_extend, native_ite, native_zleq,
        native_zplus, native_nat_to_int, native_int_to_nat, Int.le_of_lt hwv] <;>
      rw [max_eq_left (Int.le_of_lt hw), Int.sub_add_cancel]
  | u2s _ ih | s2u _ ih => simpa only [tr, trT] using ih
  | bvNeg ha ih | bvNot ha ih =>
    simp [tr, isBv_eq ha, Ty.isBv, __smtx_typeof, ih, trT, __smtx_typeof_bv_op_1]
  | bvLt ha _ iha ihb | bvGt ha _ iha ihb | bvLe ha _ iha ihb | bvGe ha _ iha ihb
    | sLt ha _ iha ihb | sGt ha _ iha ihb | sLe ha _ iha ihb | sGe ha _ iha ihb =>
    simp [tr, isBv_eq ha, isSigned_eq ha, Ty.isBv, Ty.isSigned, __smtx_typeof, iha, ihb, trT,
      __smtx_typeof_bv_op_2_ret, native_ite, native_nateq]
  | @invoke s args hs hl _ ih =>
    have hmem := (findSig_spec hs).1
    simp only [tr, hs, trs_eq]
    apply typeof_spine hS.data s.params _ _ rfl
      (typeof_uconst_wf (toDef_ty_wf hS.data (hS.params s hmem) (hS.ret s hmem)))
    apply forall₂_map_left
    exact forall₂_of_zip_map (g := Prod.snd) (R := fun a T => __smtx_typeof (tr D S Γ a) = trT D T)
      (by simpa using hl) ih (hS.params s hmem)
  | assume _ _ _ ihb => simpa only [tr] using ihb
  | @adt c d i fs args hc hl _ ih =>
    obtain ⟨hd, hi⟩ := findCtor_spec hc
    simp only [tr, hc, trs_eq]
    rw [trT_data hS.data hd]
    apply typeof_spine_chain _ _ _ rfl (typeof_dtCons hS.data hd hi)
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact (forall₂_of_zip_map (g := Prod.snd)
      (R := fun a T => __smtx_typeof (tr D S Γ a) = trT D T) hl ih
      (hS.data.fields d hd (c, fs) (List.mem_of_getElem? hi))).imp
      fun _ _ h => ⟨h.1, trT_ne hS.data h.2⟩
  | @setEmpty A hA =>
    have hwf := trT_wf hS.data (T := .SetType A) hA
    simp only [trT] at hwf
    simp [tr, trs, __smtx_typeof, __smtx_typeof_guard_wf, hwf, native_ite, trT]
  | @setOne a A ha ih =>
    have hwf := trT_wf hS.data (T := .SetType A) (ha.fragTy hS)
    simp only [trT] at hwf
    simp [tr, trs, __smtx_typeof, ih, __smtx_typeof_guard_wf, hwf, native_ite, trT]
  | @setAdd s a A hs ha ihs iha =>
    have hwf := trT_wf hS.data (T := .SetType A) (ha.fragTy hS)
    simp only [trT] at hwf ihs
    simp [tr, __smtx_typeof, ihs, iha, __smtx_typeof_guard_wf, hwf, native_ite, trT,
      __smtx_typeof_sets_op_2, native_Teq]
  | elementOf _ _ iha ihs =>
    simp only [trT] at ihs
    simp [tr, __smtx_typeof, ihs, iha, __smtx_typeof_set_member, native_ite, native_Teq, trT]
  | subsetOf _ _ ihs ihu =>
    simp only [trT] at ihs ihu
    simp [tr, __smtx_typeof, ihs, ihu, __smtx_typeof_sets_op_2_ret, native_ite, native_Teq, trT]
  | setUnion _ _ ihs ihu | setInter _ _ ihs ihu | setDiff _ _ ihs ihu =>
    simp only [trT] at ihs ihu
    simp [tr, __smtx_typeof, ihs, ihu, __smtx_typeof_sets_op_2, native_ite, native_Teq, trT]
  | @isCons a c d i fs hc _ ih =>
    obtain ⟨hd, hi⟩ := findCtor_spec hc
    rw [trT_data hS.data hd] at ih
    have hne : chainT (.Datatype (nm d.name) d.decl) (fs.map fun f => trT D f.2) ≠ .None :=
      chainT_ne (by simp) _
    show _ = SmtType.Bool
    simp [tr, hc, __smtx_typeof, ih, cons_rec, ctorFields_data hS.data hd, hi,
      __smtx_typeof_guard, __smtx_typeof_apply, native_ite, native_Teq, hne]
  | @sel a x d i j T hx ha ih =>
    obtain ⟨hd, c, fs, hi, hj⟩ := findSel_spec hx
    have hT : FragTy D T :=
      hS.data.fields _ hd (c, fs) (List.mem_of_getElem? hi) _ (List.mem_of_getElem? hj)
    rw [trT_data hS.data hd] at ih
    have hret : __smtx_ret_typeof_sel (nm d.name) d.decl i j = trT D T := by
      simp [__smtx_ret_typeof_sel, ret_typeof_sel_rec, ctorFields_data hS.data hd, hi, hj]
    simp [tr, hx, __smtx_typeof, ih, hret, __smtx_typeof_guard_wf, trT_wf hS.data hT,
      __smtx_typeof_guard, __smtx_typeof_apply, native_ite, native_Teq]

/-! ## Evaluation, inverted -/

/-- Close the branches of a match on a result in `h` where `h` says it is a value but the branch
gives no value. -/
macro "ok_split " h:ident : tactic =>
  `(tactic| (split at $h:ident <;> try contradiction))

section Eval
variable {O : Oracle} {P : Program} {n : Int}

theorem eval_bool_ok {env : Env} {e : Expr} {b : Bool} (h : eval_bool O P n env e = .Ok b) :
    eval O P n env e = .Ok (.BoolV b) := by
  rw [Semantics.eval_bool] at h
  ok_split h
  rename_i v hv
  split at h
  · cases h; exact hv
  · contradiction

theorem eval_set_ok {env : Env} {e : Expr} {v : Value} (h : eval_set O P n env e = .Ok v) :
    eval O P n env e = .Ok v := by
  rw [Semantics.eval_set] at h
  ok_split h
  rename_i w hw
  split at h
  · cases h; exact hw
  · contradiction

theorem lookup_var_det {bs : List Binding} {x : Id} {v v' : Value}
    (h : lookup_var bs x = .Ok v) (h' : lookup_var bs x = .Ok v') : v = v' := by
  rw [h] at h'; cases h'; rfl

/-- What binding the parameters `ps` to typed values gives. -/
theorem bind_lookup : ∀ (ps : List (Id × Ty)) (vs : List Value) (bs : List Binding),
    bind_all (ps.map Prod.fst) vs = .Ok bs → List.Forall₂ (HasV D) vs (ps.map Prod.snd) →
    ∀ x T, ps.lookup x = some T → ∃ v, lookup_var bs x = .Ok v ∧ HasV D v T
  | [], _, _, _, _, x, T, hx => by simp at hx
  | (y, U) :: ps, v :: vs, bs, h, .cons hv hvs, x, T, hx => by
    simp only [List.map_cons] at h
    rw [bind_all] at h
    ok_split h
    rename_i bs' hbs'
    cases h
    by_cases hxy : x = y
    · subst hxy
      simp only [List.lookup_cons_self, Option.some.injEq] at hx
      subst hx
      exact ⟨v, by rw [lookup_var, dite_eq_left_of_eq_true (eq_true rfl)], hv⟩
    · have hx' : ps.lookup x = some T := by
        have hb : (x == y) = false := beq_false_of_ne hxy
        simp only [List.lookup, hb] at hx
        exact hx
      obtain ⟨w, hw, hwT⟩ := bind_lookup ps vs bs' hbs' hvs x T hx'
      exact ⟨w, by rw [lookup_var, dite_eq_right_of_eq_false (eq_false hxy)]; exact hw, hwT⟩

end Eval

/-! ## Agreement -/

/-- The application of the value `fv` to the values `vs`, one at a time. -/
noncomputable def applyAll (M : SmtModel) : SmtValue → List SmtValue → SmtValue
  | fv, [] => fv
  | fv, v :: vs => applyAll M (__smtx_model_eval_apply M fv v) vs

theorem eval_spine (M : SmtModel) : ∀ (f : SmtTerm) (ts : List SmtTerm), plainHead f = true →
    __smtx_model_eval M (spine f ts) =
      applyAll M (__smtx_model_eval M f) (ts.map (__smtx_model_eval M))
  | _, [], _ => rfl
  | f, t :: ts, h => by
    simp only [spine, List.map_cons, applyAll]
    rw [eval_spine M (.Apply f t) ts rfl, eval_apply_plain M h t]

section Agree
variable (O : Oracle) (P : Program) (D : List Data) (S : List Sig)

/-- The variables of `Γ` have values of their types in `env`. -/
def EnvTy (Γ : List (Id × Ty)) (env : Env) : Prop :=
  ∀ x T, Γ.lookup x = some T → ∀ v, lookup_var (env_vars env) x = .Ok v → HasV D v T

/-- The constants of the variables of `Γ` have their values in `env`. -/
def VarsOk (Γ : List (Id × Ty)) (env : Env) (M : SmtModel) : Prop :=
  ∀ x T, Γ.lookup x = some T → ∀ v, lookup_var (env_vars env) x = .Ok v →
    __smtx_model_eval M (.UConst (nm x) (trT D T)) = trV D v

/-- The calls with `n` fuel of the functions of `S` to arguments of their types give values of
their types. -/
def CallTy (n : Int) : Prop :=
  ∀ s ∈ S, ∀ tenv vs v, List.Forall₂ (HasV D) vs (s.params.map Prod.snd) →
    call O P n s.name [] tenv vs = .Ok v → HasV D v s.ret

/-- The calls with `n` fuel of the functions of `S` agree with the constants of the functions in
`M`. -/
def CallsOk (n : Int) (M : SmtModel) : Prop :=
  ∀ s ∈ S, ∀ tenv vs v, List.Forall₂ (HasV D) vs (s.params.map Prod.snd) →
    call O P n s.name [] tenv vs = .Ok v →
    applyAll M (__smtx_model_eval M (.UConst (nm s.name) (s.toDef D).ty)) (vs.map (trV D)) = trV D v

/-- What the agreement says of `e`: its values are of type `T`, and are those of its term in the
models where the calls and the variables agree. -/
def Ev (n : Int) (Γ : List (Id × Ty)) (e : Expr) (T : Ty) : Prop :=
  ∀ env v, EnvTy D Γ env → eval O P n env e = .Ok v →
    HasV D v T ∧ ∀ M, model_wf M → CallsOk O P D S n M → VarsOk D Γ env M →
      __smtx_model_eval M (tr D S Γ e) = trV D v

variable {O P D S}

theorem ev_list {n : Int} {Γ : List (Id × Ty)} {env : Env} (hE : EnvTy D Γ env) :
    ∀ (args : List Expr) (Ts : List Ty) (vs : List Value), args.length = Ts.length →
      (∀ p ∈ args.zip Ts, Ev O P D S n Γ p.1 p.2) → eval_list O P n env args = .Ok vs →
      List.Forall₂ (HasV D) vs Ts ∧ ∀ M, model_wf M → CallsOk O P D S n M → VarsOk D Γ env M →
        (args.map (tr D S Γ)).map (__smtx_model_eval M) = vs.map (trV D)
  | [], [], vs, _, _, h => by
    rw [eval_list] at h; cases h; exact ⟨.nil, fun _ _ _ _ => rfl⟩
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | a :: args, T :: Ts, vs, hl, hev, h => by
    rw [eval_list] at h
    ok_split h
    rename_i v hv
    ok_split h
    rename_i ws hws
    cases h
    obtain ⟨hvT, hvM⟩ := hev (a, T) (.head _) env v hE hv
    obtain ⟨hwT, hwM⟩ := ev_list hE args Ts ws (by simpa using hl)
      (fun p hp => hev p (.tail _ hp)) hws
    exact ⟨.cons hvT hwT, fun M hw hc hV => by
      simp only [List.map_cons, hvM M hw hc hV, hwM M hw hc hV]⟩

theorem ev_and (hty : LogosTyping) {n : Int} {Γ : List (Id × Ty)} {env : Env}
    (hE : EnvTy D Γ env) :
    ∀ (es : List Expr) (v : Value), (∀ e ∈ es, HasTy D S Γ e .BooleanType) →
      (∀ e ∈ es, Ev O P D S n Γ e .BooleanType) → (hS : SigOk D S) →
      eval_and O P n env es = .Ok v →
      HasV D v .BooleanType ∧ ∀ M, model_wf M → CallsOk O P D S n M → VarsOk D Γ env M →
        __smtx_model_eval M (andT (es.map (tr D S Γ))) = trV D v
  | [], v, _, _, _, h => by rw [eval_and] at h; cases h; exact ⟨trivial, fun _ _ _ _ => rfl⟩
  | e :: es, v, hty', hev, hS, h => by
    rw [eval_and] at h
    ok_split h
    rename_i b hb
    obtain ⟨_, heM⟩ := hev e (.head _) env _ hE (eval_bool_ok hb)
    cases b
    · rw [dite_eq_right_of_eq_false (eq_false Bool.false_ne_true)] at h
      cases h
      refine ⟨trivial, fun M hw hc hV => ?_⟩
      have hrest : __smtx_typeof (andT (es.map (tr D S Γ))) = .Bool := by
        apply typeof_andT
        intro t ht
        simp only [List.mem_map] at ht
        obtain ⟨e', he', rfl⟩ := ht
        exact tr_typeof hS (hty' e' (.tail _ he'))
      obtain ⟨b', hb'⟩ := Inox.Extend.eval_bool hty hw hrest
      simp only [List.map_cons, andT, __smtx_model_eval, heM M hw hc hV, hb', trV]
      rfl
    · rw [dite_eq_left_of_eq_true (eq_true rfl)] at h
      obtain ⟨hv, hvM⟩ := ev_and hty hE es v (fun e' he' => hty' e' (.tail _ he'))
        (fun e' he' => hev e' (.tail _ he')) hS h
      refine ⟨hv, fun M hw hc hV => ?_⟩
      obtain ⟨b', rfl⟩ := hasV_bool hv
      simp only [List.map_cons, andT, __smtx_model_eval, heM M hw hc hV, hvM M hw hc hV, trV]
      rfl

theorem ev_or (hty : LogosTyping) {n : Int} {Γ : List (Id × Ty)} {env : Env}
    (hE : EnvTy D Γ env) :
    ∀ (es : List Expr) (v : Value), (∀ e ∈ es, HasTy D S Γ e .BooleanType) →
      (∀ e ∈ es, Ev O P D S n Γ e .BooleanType) → (hS : SigOk D S) →
      eval_or O P n env es = .Ok v →
      HasV D v .BooleanType ∧ ∀ M, model_wf M → CallsOk O P D S n M → VarsOk D Γ env M →
        __smtx_model_eval M (orT (es.map (tr D S Γ))) = trV D v
  | [], v, _, _, _, h => by rw [eval_or] at h; cases h; exact ⟨trivial, fun _ _ _ _ => rfl⟩
  | e :: es, v, hty', hev, hS, h => by
    rw [eval_or] at h
    ok_split h
    rename_i b hb
    obtain ⟨_, heM⟩ := hev e (.head _) env _ hE (eval_bool_ok hb)
    cases b
    · rw [dite_eq_right_of_eq_false (eq_false Bool.false_ne_true)] at h
      obtain ⟨hv, hvM⟩ := ev_or hty hE es v (fun e' he' => hty' e' (.tail _ he'))
        (fun e' he' => hev e' (.tail _ he')) hS h
      refine ⟨hv, fun M hw hc hV => ?_⟩
      obtain ⟨b', rfl⟩ := hasV_bool hv
      simp only [List.map_cons, orT, __smtx_model_eval, heM M hw hc hV, hvM M hw hc hV, trV]
      rfl
    · rw [dite_eq_left_of_eq_true (eq_true rfl)] at h
      cases h
      refine ⟨trivial, fun M hw hc hV => ?_⟩
      have hrest : __smtx_typeof (orT (es.map (tr D S Γ))) = .Bool := by
        apply typeof_orT
        intro t ht
        simp only [List.mem_map] at ht
        obtain ⟨e', he', rfl⟩ := ht
        exact tr_typeof hS (hty' e' (.tail _ he'))
      obtain ⟨b', hb'⟩ := Inox.Extend.eval_bool hty hw hrest
      simp only [List.map_cons, orT, __smtx_model_eval, heM M hw hc hV, hb', trV]
      rfl

/-- A value is not a regular language, so the equality of the models on it is that of the
values. -/
theorem eval_eq_veq {a : SmtValue} (h : __smtx_typeof_value a ≠ .RegLan) (b : SmtValue) :
    __smtx_model_eval_eq a b = .Boolean (native_veq a b) := by
  cases a <;> first | (simp [__smtx_typeof_value] at h; done) | simp [__smtx_model_eval_eq]

open Classical in
/-- The equality of the models on the values of a type is that of their SMT values. -/
theorem eval_eq_trV {D : List Data} (hD : DataOk D) {x y : Value} {T : Ty} (hx : HasV D x T) :
    __smtx_model_eval_eq (trV D x) (trV D y) = trV D (.BoolV (decide (trV D x = trV D y))) := by
  have hne : __smtx_typeof_value (trV D x) ≠ .RegLan := by
    rw [(agrees_trV hD default x T hx).1]
    rcases fragTy_cases (hasV_fragTy hx) with
      rfl | rfl | rfl | ⟨sg, w, _, rfl⟩ | ⟨d, hd, rfl⟩ | ⟨A, _, rfl⟩
    · simp [trT]
    · simp [trT]
    · simp [trT]
    · simp [trT]
    · rw [trT_data hD hd]; simp
    · simp [trT]
  rw [eval_eq_veq hne]
  simp only [native_veq, trV]

/-! The operations of the sets, on the lists of their elements. -/

section Sets
variable {O : Oracle}

theorem resolve_fragTy {D : List Data} (hO : O.Sound) (tenv : List TypeBinding) :
    ∀ T, FragTy D T → O.resolve tenv T = T :=
  fragTy_induct (by rw [hO.resolve]) (by rw [hO.resolve]) (by rw [hO.resolve])
    (fun _ _ _ => by rw [hO.resolve])
    (fun d _ => by rw [hO.resolve]; dsimp only; rw [hO.resolve_all])
    (fun A _ ih => by rw [hO.resolve]; dsimp only; rw [ih])

open Classical in
theorem set_insert_hasV {D : List Data} (hD : DataOk D) (hO : O.Sound) (P : Program)
    (hPD : ProgData D P)
    {xs ys : List Value} {v : Value} {A : Ty} (hxs : ∀ x ∈ xs, HasV D x A) (hv : HasV D v A)
    (h : set_insert O P xs v = .Ok ys) :
    (∀ y ∈ ys, HasV D y A) ∧
      ∀ w, w ∈ ys.map (trV D) ↔ w = trV D v ∨ w ∈ xs.map (trV D) := by
  rw [set_insert, set_contains_hasV hD hO P hPD hxs hv] at h
  dsimp only at h
  by_cases hin : trV D v ∈ xs.map (trV D)
  · rw [dite_eq_left_of_eq_true (by simp only [decide_eq_true hin])] at h
    cases h
    exact ⟨hxs, fun w => ⟨.inr, fun h => h.elim (fun e => e ▸ hin) id⟩⟩
  · rw [dite_eq_right_of_eq_false (by simp only [decide_eq_false hin]; simp)] at h
    cases h
    refine ⟨fun y hy => ?_, fun w => by simp⟩
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact hv
    · exact hxs y hy'

theorem set_insert_all_hasV {D : List Data} (hD : DataOk D) (hO : O.Sound) (P : Program)
    (hPD : ProgData D P)
    {A : Ty} : ∀ (vs xs zs : List Value), (∀ x ∈ xs, HasV D x A) →
      (∀ v ∈ vs, HasV D v A) → set_insert_all O P xs vs = .Ok zs →
      (∀ z ∈ zs, HasV D z A) ∧
        ∀ w, w ∈ zs.map (trV D) ↔ w ∈ xs.map (trV D) ∨ w ∈ vs.map (trV D)
  | [], xs, zs, hxs, _, h => by
    rw [set_insert_all] at h
    cases h
    exact ⟨hxs, fun w => by simp⟩
  | v :: vs, xs, zs, hxs, hvs, h => by
    rw [set_insert_all] at h
    ok_split h
    rename_i ys hys
    obtain ⟨hy, hym⟩ := set_insert_hasV hD hO P hPD hxs (hvs v (.head _)) hys
    obtain ⟨hz, hzm⟩ := set_insert_all_hasV hD hO P hPD vs ys zs hy
      (fun a ha => hvs a (.tail _ ha)) h
    refine ⟨hz, fun w => ?_⟩
    rw [hzm, hym]
    simp only [List.map_cons, List.mem_cons]
    tauto

open Classical in
theorem set_filter_hasV {D : List Data} (hD : DataOk D) (hO : O.Sound) (P : Program)
    (hPD : ProgData D P) {A : Ty}
    (ys : List Value) (keep : Bool) (hys : ∀ y ∈ ys, HasV D y A) :
    ∀ xs zs : List Value, (∀ x ∈ xs, HasV D x A) → set_filter O P xs ys keep = .Ok zs →
      zs = xs.filter fun x => decide (trV D x ∈ ys.map (trV D)) == keep
  | [], zs, _, h => by
    rw [set_filter] at h
    cases h
    rfl
  | x :: xs, zs, hxs, h => by
    rw [set_filter, set_contains_hasV hD hO P hPD hys (hxs x (.head _))] at h
    dsimp only at h
    ok_split h
    rename_i ws hws
    have ih := set_filter_hasV hD hO P hPD ys keep hys xs ws (fun a ha => hxs a (.tail _ ha)) hws
    subst ih
    by_cases hk : decide (trV D x ∈ ys.map (trV D)) = keep
    · rw [dite_eq_left_of_eq_true (eq_true hk)] at h
      cases h
      rw [List.filter_cons, if_pos (beq_iff_eq.mpr hk)]
    · rw [dite_eq_right_of_eq_false (eq_false hk)] at h
      cases h
      rw [List.filter_cons, if_neg fun e => hk (beq_iff_eq.mp e)]

end Sets

/-- A constructor, or one applied to values. -/
def ctorLike : SmtValue → Prop
  | .DtCons _ _ _ => True
  | .Apply _ _ => True
  | _ => False

theorem applyAll_ctor (M : SmtModel) : ∀ (as : List SmtValue) (f : SmtValue), ctorLike f →
    (∀ a ∈ as, a ≠ .NotValue) → applyAll M f as = applyVs f as
  | [], _, _, _ => rfl
  | a :: as, f, hf, h => by
    have ha := h a (.head _)
    have : __smtx_model_eval_apply M f a = .Apply f a := by
      cases f <;> first | exact absurd hf id | (cases a <;> first | rfl | exact absurd rfl ha)
    simp only [applyAll, this]
    rw [applyAll_ctor M as (.Apply f a) trivial (fun b hb => h b (.tail _ hb))]
    simp [applyVs]

/-! The operators of the bit-vectors, on the values. -/

theorem bvadd_eq {s : Bool} {w : Int} (hw : 0 < w) (i j : Int) :
    __smtx_model_eval_bvadd (.Binary w i) (.Binary w j) = trV D (bv s w (i + j)) := by
  rw [trV_bvmk hw]
  simp [__smtx_model_eval_bvadd, native_mod_total, native_zplus, int_pow2_eq (Int.le_of_lt hw)]

theorem bvmul_eq {s : Bool} {w : Int} (hw : 0 < w) (i j : Int) :
    __smtx_model_eval_bvmul (.Binary w i) (.Binary w j) = trV D (bv s w (i * j)) := by
  rw [trV_bvmk hw]
  simp [__smtx_model_eval_bvmul, native_mod_total, native_zmult, int_pow2_eq (Int.le_of_lt hw)]

theorem bvneg_eq {s : Bool} {w : Int} (hw : 0 < w) (i : Int) :
    __smtx_model_eval_bvneg (.Binary w i) = trV D (bv s w (0 - i)) := by
  rw [trV_bvmk hw]
  simp [__smtx_model_eval_bvneg, native_mod_total, native_zneg, int_pow2_eq (Int.le_of_lt hw)]

theorem bvsub_eq {s : Bool} {w : Int} (hw : 0 < w) (i j : Int) :
    __smtx_model_eval_bvsub (.Binary w i) (.Binary w j) = trV D (bv s w (i - j)) := by
  rw [trV_bvmk hw]
  simp only [__smtx_model_eval_bvsub, __smtx_model_eval_bvneg, __smtx_model_eval_bvadd,
    native_mod_total, native_zplus, native_zneg, int_pow2_eq (Int.le_of_lt hw)]
  rw [Int.add_emod_emod, Int.sub_eq_add_neg]

theorem bvudiv_eq {w : Int} (hw : 0 < w) {i : Int} (hi : 0 ≤ i) (j : Int) :
    __smtx_model_eval_bvudiv (.Binary w i) (.Binary w j) =
      trV D (if j = 0 then bv false w (pow2 w - 1) else bv false w (tdiv i j)) := by
  by_cases hj : j = 0
  · rw [if_pos hj, trV_bvmk hw, pow2_eq (Int.le_of_lt hw)]
    simp [__smtx_model_eval_bvudiv, native_mod_total, native_ite, native_zeq, hj,
      native_binary_max, native_zplus, native_zneg, int_pow2_eq (Int.le_of_lt hw),
      Int.sub_eq_add_neg]
  · rw [if_neg hj, trV_bvmk hw]
    simp [__smtx_model_eval_bvudiv, native_mod_total, native_ite, native_zeq, hj,
      native_div_total, int_pow2_eq (Int.le_of_lt hw), tdiv, hi]

theorem bvurem_eq {w : Int} (hw : 0 < w) {i : Int} (hi0 : 0 ≤ i) (hi : i < 2 ^ w.toNat)
    (j : Int) :
    __smtx_model_eval_bvurem (.Binary w i) (.Binary w j) =
      trV D (if j = 0 then .BVV false w i else bv false w (trem i j)) := by
  by_cases hj : j = 0
  · rw [if_pos hj]
    simp [__smtx_model_eval_bvurem, native_mod_total, native_ite, native_zeq, hj, trV,
      int_pow2_eq (Int.le_of_lt hw), Int.emod_eq_of_lt hi0 hi]
  · rw [if_neg hj, trV_bvmk hw]
    simp [__smtx_model_eval_bvurem, native_mod_total, native_ite, native_zeq, hj,
      int_pow2_eq (Int.le_of_lt hw), trem, tdiv, hi0, Int.emod_def]

theorem bvnot_eq {s : Bool} {w : Int} (hw : 0 < w) {i : Int} (hi0 : 0 ≤ i)
    (hi : i < 2 ^ w.toNat) :
    __smtx_model_eval_bvnot (.Binary w i) = trV D (.BVV s w (pow2 w - 1 - i)) := by
  rw [pow2_eq (Int.le_of_lt hw)]
  have h : (2 ^ w.toNat + -(i + 1)) % 2 ^ w.toNat = 2 ^ w.toNat - 1 - i := by
    rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
  simp only [__smtx_model_eval_bvnot, native_mod_total, native_binary_not, native_zplus,
    native_zneg, int_pow2_eq (Int.le_of_lt hw), trV, h]

/-! The operators of the reals, on the fractions. -/

theorem den_ne (q : ℚ) : ((q.den : Int) : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero

theorem ratOf_add (p q : ℚ) : ratOf (p.num * q.den + q.num * p.den) (p.den * q.den) = p + q := by
  have hp := den_ne p
  have hq := den_ne q
  conv_rhs => rw [← Rat.num_div_den p, ← Rat.num_div_den q]
  simp only [ratOf]; push_cast at hp hq ⊢; field_simp

theorem ratOf_sub (p q : ℚ) : ratOf (p.num * q.den - q.num * p.den) (p.den * q.den) = p - q := by
  have hp := den_ne p
  have hq := den_ne q
  conv_rhs => rw [← Rat.num_div_den p, ← Rat.num_div_den q]
  simp only [ratOf]; push_cast at hp hq ⊢; field_simp

theorem ratOf_mul (p q : ℚ) : ratOf (p.num * q.num) (p.den * q.den) = p * q := by
  have hp := den_ne p
  have hq := den_ne q
  conv_rhs => rw [← Rat.num_div_den p, ← Rat.num_div_den q]
  simp only [ratOf]; push_cast at hp hq ⊢; field_simp

theorem ratOf_div (p : ℚ) {q : ℚ} (h : q.num ≠ 0) :
    ratOf (p.num * q.den) (p.den * q.num) = p / q := by
  have hp := den_ne p
  have hq := den_ne q
  have hn : (q.num : ℚ) ≠ 0 := by exact_mod_cast h
  conv_rhs => rw [← Rat.num_div_den p, ← Rat.num_div_den q]
  simp only [ratOf]; push_cast at hp hq ⊢; field_simp

theorem ratOf_neg (p : ℚ) : ratOf (-p.num) p.den = -p := by
  conv_rhs => rw [← Rat.num_div_den p]
  simp only [ratOf]; push_cast; ring

theorem den_mul_ne (p q : ℚ) : (p.den : Int) * q.den ≠ 0 :=
  Int.mul_ne_zero (by exact_mod_cast p.den_ne_zero) (by exact_mod_cast q.den_ne_zero)

set_option maxHeartbeats 1600000 in
/-- The agreement: on the fragment, a value of an expression is of its type, and is the value of
its term in every well-formed model where the calls and the variables agree. -/
theorem ev (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hPD : ProgData D P) {n : Int}
    (hct : CallTy O P D S n)
    {Γ : List (Id × Ty)} {e : Expr} {T : Ty} (h : HasTy D S Γ e T) : Ev O P D S n Γ e T := by
  induction h with
  | var hx hT =>
    intro env v hE he
    rw [eval] at he
    exact ⟨hE _ _ hx v he, fun M _ _ hV => by simp only [tr, hx]; exact hV _ _ hx v he⟩
  | int i => intro env v hE he; rw [eval] at he; cases he; exact ⟨trivial, fun _ _ _ _ => rfl⟩
  | bool b => intro env v hE he; rw [eval] at he; cases he; exact ⟨trivial, fun _ _ _ _ => rfl⟩
  | ite _ _ _ ihc iha ihb =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i b hb
    obtain ⟨_, hcM⟩ := ihc env _ hE (eval_bool_ok hb)
    cases b
    · rw [dite_eq_right_of_eq_false (eq_false Bool.false_ne_true)] at he
      obtain ⟨hv, hbM⟩ := ihb env v hE he
      exact ⟨hv, fun M hw hc hV => by
        simp only [tr, __smtx_model_eval, hcM M hw hc hV, hbM M hw hc hV, trV]; rfl⟩
    · rw [dite_eq_left_of_eq_true (eq_true rfl)] at he
      obtain ⟨hv, haM⟩ := iha env v hE he
      exact ⟨hv, fun M hw hc hV => by
        simp only [tr, __smtx_model_eval, hcM M hw hc hV, haM M hw hc hV, trV]; rfl⟩
  | @and es hes ih =>
    intro env v hE he
    rw [eval] at he
    obtain ⟨hv, hM⟩ := ev_and hty hE es v hes ih hS he
    exact ⟨hv, fun M hw hc hV => by simp only [tr, trs_eq]; exact hM M hw hc hV⟩
  | @or es hes ih =>
    intro env v hE he
    rw [eval] at he
    obtain ⟨hv, hM⟩ := ev_or hty hE es v hes ih hS he
    exact ⟨hv, fun M hw hc hV => by simp only [tr, trs_eq]; exact hM M hw hc hV⟩
  | not _ ih =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i b hb
    cases he
    obtain ⟨_, hM⟩ := ih env _ hE (eval_bool_ok hb)
    exact ⟨trivial, fun M hw hc hV => by
      simp only [tr, __smtx_model_eval, hM M hw hc hV, trV]; rfl⟩
  | @implies a b _ htb iha ihb =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    obtain ⟨_, haM⟩ := iha env _ hE (eval_bool_ok hx)
    cases x
    · rw [dite_eq_right_of_eq_false (eq_false Bool.false_ne_true)] at he
      cases he
      refine ⟨trivial, fun M hw hc hV => ?_⟩
      obtain ⟨y, hy⟩ := Inox.Extend.eval_bool hty hw (tr_typeof hS htb)
      simp only [tr, __smtx_model_eval, haM M hw hc hV, hy, trV]; rfl
    · rw [dite_eq_left_of_eq_true (eq_true rfl)] at he
      ok_split he
      rename_i y hy
      cases he
      obtain ⟨_, hbM⟩ := ihb env _ hE (eval_bool_ok hy)
      exact ⟨trivial, fun M hw hc hV => by
        simp only [tr, __smtx_model_eval, haM M hw hc hV, hbM M hw hc hV, trV]; rfl⟩
  | @equals a b T _ _ iha ihb =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    ok_split he
    rename_i same hsame
    cases he
    obtain ⟨hxT, haM⟩ := iha env _ hE hx
    obtain ⟨hyT, hbM⟩ := ihb env _ hE hy
    refine ⟨trivial, fun M hw hc hV => ?_⟩
    simp only [tr, __smtx_model_eval, haM M hw hc hV, hbM M hw hc hV]
    rw [value_eq_hasV hS.data hO P hPD hxT hyT] at hsame
    cases hsame
    exact eval_eq_trV hS.data hxT
  | plus ha _ iha ihb | minus ha _ iha ihb | times ha _ iha ihb =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    obtain ⟨hxT, haM⟩ := iha env _ hE hx
    obtain ⟨hyT, hbM⟩ := ihb env _ hE hy
    obtain ⟨i, rfl⟩ := hasV_int hxT
    obtain ⟨j, rfl⟩ := hasV_int hyT
    simp only [arith_plus, arith_minus, arith_times] at he
    cases he
    refine ⟨trivial, fun M hw hc hV => ?_⟩
    simp only [tr, isBv_eq ha, Ty.isBv, Bool.false_eq_true, ↓reduceIte, __smtx_model_eval,
      haM M hw hc hV, hbM M hw hc hV, trV,
      __smtx_model_eval_plus, __smtx_model_eval__, __smtx_model_eval_mult, native_zplus,
      native_zneg, native_zmult, Int.sub_eq_add_neg]
  | div ha _ iha ihb | rem ha _ iha ihb | mod ha _ iha ihb =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    obtain ⟨hxT, haM⟩ := iha env _ hE hx
    obtain ⟨hyT, hbM⟩ := ihb env _ hE hy
    obtain ⟨i, rfl⟩ := hasV_int hxT
    obtain ⟨j, rfl⟩ := hasV_int hyT
    simp only [arith_div, arith_rem, arith_mod] at he
    split at he
    · cases he
    rename_i hj
    cases he
    refine ⟨trivial, fun M hw hc hV => ?_⟩
    simp [tr, isBv_eq ha, isReal_eq ha, Ty.isBv, Ty.isReal, __smtx_model_eval, haM M hw hc hV,
      hbM M hw hc hV, trV, __smtx_model_eval_eq, native_veq, hj, __smtx_model_eval_ite,
      __smtx_model_eval_div_total,
      __smtx_model_eval_mod_total, native_div_total, native_mod_total]
  | uminus ha ih =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    obtain ⟨hxT, haM⟩ := ih env _ hE hx
    obtain ⟨i, rfl⟩ := hasV_int hxT
    simp only [arith_neg] at he
    cases he
    refine ⟨trivial, fun M hw hc hV => ?_⟩
    simp only [tr, isBv_eq ha, Ty.isBv, Bool.false_eq_true, ↓reduceIte, __smtx_model_eval,
      haM M hw hc hV, trV, __smtx_model_eval_uneg, native_zneg, Int.zero_sub]
  | lt ha _ iha ihb | gt ha _ iha ihb | le ha _ iha ihb | ge ha _ iha ihb =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    obtain ⟨hxT, haM⟩ := iha env _ hE hx
    obtain ⟨hyT, hbM⟩ := ihb env _ hE hy
    obtain ⟨i, rfl⟩ := hasV_int hxT
    obtain ⟨j, rfl⟩ := hasV_int hyT
    simp only [arith_lt, arith_le] at he
    cases he
    refine ⟨trivial, fun M hw hc hV => ?_⟩
    simp only [tr, isBv_eq ha, Ty.isBv, Bool.false_eq_true, ↓reduceIte, __smtx_model_eval,
      haM M hw hc hV, hbM M hw hc hV, trV, __smtx_model_eval_lt, __smtx_model_eval_leq,
          __smtx_model_eval_gt, __smtx_model_eval_geq,
      native_zlt, native_zleq]
    all_goals (congr 1; rw [← decide_not]; exact decide_eq_decide.mpr Int.not_lt.symm)
  | bvLit hw h0 hx =>
    intro env v hE he; rw [eval] at he; cases he
    exact ⟨hasV_bv_of hw h0 hx, fun _ _ _ _ => rfl⟩
  | bvPlus ha _ iha ihb | bvMinus ha _ iha ihb | bvTimes ha _ iha ihb =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    obtain ⟨hxT, haM⟩ := iha env _ hE hx
    obtain ⟨hyT, hbM⟩ := ihb env _ hE hy
    obtain ⟨i, rfl, hw, hi0, hi⟩ := hasV_bv hxT
    obtain ⟨j, rfl, -, hj0, hj⟩ := hasV_bv hyT
    simp only [arith_plus, arith_minus, arith_times, same_bv, decide_true, Bool.and_self,
      ↓reduceDIte, Result.Ok.injEq] at he
    subst he
    refine ⟨hasV_bvmk hw _, fun M hwf hc hV => ?_⟩
    simp only [tr, isBv_eq ha, Ty.isBv, ↓reduceIte, __smtx_model_eval, haM M hwf hc hV,
      hbM M hwf hc hV, trV]
    first | exact bvadd_eq hw i j | exact bvsub_eq hw i j | exact bvmul_eq hw i j
  | bvDiv ha _ iha ihb =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    obtain ⟨hxT, haM⟩ := iha env _ hE hx
    obtain ⟨hyT, hbM⟩ := ihb env _ hE hy
    obtain ⟨i, rfl, hw, hi0, hi⟩ := hasV_bv hxT
    obtain ⟨j, rfl, -, hj0, hj⟩ := hasV_bv hyT
    by_cases hz : j = 0
    · simp only [arith_div, same_bv, bv_int, decide_true, Bool.and_self, ↓reduceDIte, hz,
        Bool.false_eq_true, Result.Ok.injEq] at he
      subst he
      refine ⟨hasV_bvmk hw _, fun M hwf hc hV => ?_⟩
      simp only [tr, isBv_eq ha, isSigned_eq ha, Ty.isBv, Ty.isSigned, Bool.false_eq_true,
        ↓reduceIte, __smtx_model_eval, haM M hwf hc hV,
        hbM M hwf hc hV, trV]
      rw [bvudiv_eq hw hi0, ite_cond_eq_true _ _ (eq_true hz)]
    · simp only [arith_div, same_bv, bv_int, decide_true, Bool.and_self, ↓reduceDIte, hz,
        Bool.false_eq_true, Result.Ok.injEq] at he
      subst he
      refine ⟨hasV_bvmk hw _, fun M hwf hc hV => ?_⟩
      simp only [tr, isBv_eq ha, isSigned_eq ha, Ty.isBv, Ty.isSigned, Bool.false_eq_true,
        ↓reduceIte, __smtx_model_eval, haM M hwf hc hV,
        hbM M hwf hc hV, trV]
      rw [bvudiv_eq hw hi0, ite_cond_eq_false _ _ (eq_false hz)]
  | bvRem ha _ iha ihb =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    obtain ⟨hxT, haM⟩ := iha env _ hE hx
    obtain ⟨hyT, hbM⟩ := ihb env _ hE hy
    obtain ⟨i, rfl, hw, hi0, hi⟩ := hasV_bv hxT
    obtain ⟨j, rfl, -, hj0, hj⟩ := hasV_bv hyT
    by_cases hz : j = 0
    · simp only [arith_rem, same_bv, bv_int, decide_true, Bool.and_self, ↓reduceDIte, hz,
        Bool.false_eq_true, Result.Ok.injEq] at he
      subst he
      refine ⟨hxT, fun M hwf hc hV => ?_⟩
      simp only [tr, isBv_eq ha, isSigned_eq ha, Ty.isBv, Ty.isSigned, Bool.false_eq_true,
        ↓reduceIte, __smtx_model_eval, haM M hwf hc hV,
        hbM M hwf hc hV, trV]
      rw [bvurem_eq (D := D) hw hi0 hi, ite_cond_eq_true _ _ (eq_true hz)]
      rfl
    · simp only [arith_rem, same_bv, bv_int, decide_true, Bool.and_self, ↓reduceDIte, hz,
        Bool.false_eq_true, Result.Ok.injEq] at he
      subst he
      refine ⟨hasV_bvmk hw _, fun M hwf hc hV => ?_⟩
      simp only [tr, isBv_eq ha, isSigned_eq ha, Ty.isBv, Ty.isSigned, Bool.false_eq_true,
        ↓reduceIte, __smtx_model_eval, haM M hwf hc hV,
        hbM M hwf hc hV, trV]
      rw [bvurem_eq hw hi0 hi, ite_cond_eq_false _ _ (eq_false hz)]
  | bvNeg ha ih =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    obtain ⟨hxT, haM⟩ := ih env _ hE hx
    obtain ⟨i, rfl, hw, hi0, hi⟩ := hasV_bv hxT
    simp only [arith_neg, Result.Ok.injEq] at he
    subst he
    refine ⟨hasV_bvmk hw _, fun M hwf hc hV => ?_⟩
    simp only [tr, isBv_eq ha, Ty.isBv, ↓reduceIte, __smtx_model_eval, haM M hwf hc hV, trV]
    exact bvneg_eq hw i
  | bvNot ha ih =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    obtain ⟨hxT, haM⟩ := ih env _ hE hx
    obtain ⟨i, rfl, hw, hi0, hi⟩ := hasV_bv hxT
    simp only [Result.Ok.injEq] at he
    subst he
    have hp := pow2_eq (Int.le_of_lt hw)
    refine ⟨hasV_bv_of hw (by omega) (by omega), fun M hwf hc hV => ?_⟩
    simp only [tr, __smtx_model_eval, haM M hwf hc hV, trV]
    exact bvnot_eq (D := D) (s := false) hw hi0 hi
  | bvLt ha _ iha ihb | bvGt ha _ iha ihb | bvLe ha _ iha ihb | bvGe ha _ iha ihb =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    obtain ⟨hxT, haM⟩ := iha env _ hE hx
    obtain ⟨hyT, hbM⟩ := ihb env _ hE hy
    obtain ⟨i, rfl, hw, hi0, hi⟩ := hasV_bv hxT
    obtain ⟨j, rfl, -, hj0, hj⟩ := hasV_bv hyT
    simp only [arith_lt, arith_le, same_bv, bv_int, decide_true, Bool.and_self, ↓reduceDIte,
      Bool.false_eq_true] at he
    cases he
    refine ⟨trivial, fun M hwf hc hV => ?_⟩
    simp only [tr, isBv_eq ha, isSigned_eq ha, Ty.isBv, Ty.isSigned, Bool.false_eq_true,
        ↓reduceIte, __smtx_model_eval, haM M hwf hc hV,
      hbM M hwf hc hV, trV]
    simp [__smtx_model_eval_bvult, __smtx_model_eval_bvule, __smtx_model_eval_bvugt,
      __smtx_model_eval_bvuge, __smtx_model_eval_or, __smtx_model_eval_eq, native_veq, native_or,
      native_zlt]
    all_goals
      simp only [← Bool.decide_or, ← decide_not]
      exact decide_eq_decide.mpr
        ⟨fun h => h.elim (fun h => Int.not_lt.mpr (Int.le_of_lt h))
            (fun h => by rw [h]; exact Int.lt_irrefl _),
          fun h => (Int.lt_or_eq_of_le (Int.not_lt.mp h)).imp id Eq.symm⟩
  | bvMod ha _ iha ihb =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    obtain ⟨hxT, haM⟩ := iha env _ hE hx
    obtain ⟨hyT, hbM⟩ := ihb env _ hE hy
    obtain ⟨i, rfl, hw, hi0, hi⟩ := hasV_bv hxT
    obtain ⟨j, rfl, -, hj0, hj⟩ := hasV_bv hyT
    by_cases hz : j = 0
    · simp only [arith_mod, same_bv, bv_int, decide_true, Bool.and_self, ↓reduceDIte, hz,
        Bool.false_eq_true, Result.Ok.injEq] at he
      subst he
      refine ⟨hxT, fun M hwf hc hV => ?_⟩
      simp only [tr, isBv_eq ha, isSigned_eq ha, Ty.isBv, Ty.isSigned, Bool.false_eq_true,
        ↓reduceIte, __smtx_model_eval, haM M hwf hc hV, hbM M hwf hc hV, trV]
      rw [bvurem_eq (D := D) hw hi0 hi, ite_cond_eq_true _ _ (eq_true hz)]
      rfl
    · have hneg : ¬(j < 0 ∧ ¬i % j = 0) := fun h => by omega
      simp only [arith_mod, same_bv, bv_int, decide_true, Bool.and_self, ↓reduceDIte, hz,
        Bool.false_eq_true, hneg, Result.Ok.injEq] at he
      subst he
      refine ⟨hasV_bvmk hw _, fun M hwf hc hV => ?_⟩
      simp only [tr, isBv_eq ha, isSigned_eq ha, Ty.isBv, Ty.isSigned, Bool.false_eq_true,
        ↓reduceIte, __smtx_model_eval, haM M hwf hc hV, hbM M hwf hc hV, trV]
      rw [bvurem_eq (D := D) hw hi0 hi, ite_cond_eq_false _ _ (eq_false hz)]
      simp [trem, tdiv, hi0, Int.emod_def]
  | sDiv ha _ iha ihb | sRem ha _ iha ihb | sMod ha _ iha ihb =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    obtain ⟨hxT, haM⟩ := iha env _ hE hx
    obtain ⟨hyT, hbM⟩ := ihb env _ hE hy
    obtain ⟨i, rfl, hw, hi0, hi⟩ := hasV_bv hxT
    obtain ⟨j, rfl, -, hj0, hj⟩ := hasV_bv hyT
    first
      | (obtain ⟨hv, hm⟩ := bvsdiv_eq (D := D) hw hi0 hi hj0 hj he
         refine ⟨hv, fun M hwf hc hV => ?_⟩
         simp only [tr, isBv_eq ha, isSigned_eq ha, Ty.isBv, Ty.isSigned, Bool.false_eq_true,
           ↓reduceIte, __smtx_model_eval, haM M hwf hc hV, hbM M hwf hc hV, trV]
         exact hm)
      | (obtain ⟨hv, hm⟩ := bvsrem_eq (D := D) hw hi0 hi hj0 hj he
         refine ⟨hv, fun M hwf hc hV => ?_⟩
         simp only [tr, isBv_eq ha, isSigned_eq ha, Ty.isBv, Ty.isSigned, Bool.false_eq_true,
           ↓reduceIte, __smtx_model_eval, haM M hwf hc hV, hbM M hwf hc hV, trV]
         exact hm)
      | (obtain ⟨hv, hm⟩ := bvsmod_eq (D := D) hw hi0 hi hj0 hj he
         refine ⟨hv, fun M hwf hc hV => ?_⟩
         simp only [tr, isBv_eq ha, isSigned_eq ha, Ty.isBv, Ty.isSigned, Bool.false_eq_true,
           ↓reduceIte, __smtx_model_eval, haM M hwf hc hV, hbM M hwf hc hV, trV]
         exact hm)
  | sLt ha _ iha ihb | sGt ha _ iha ihb | sLe ha _ iha ihb | sGe ha _ iha ihb =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    obtain ⟨hxT, haM⟩ := iha env _ hE hx
    obtain ⟨hyT, hbM⟩ := ihb env _ hE hy
    obtain ⟨i, rfl, hw, hi0, hi⟩ := hasV_bv hxT
    obtain ⟨j, rfl, -, hj0, hj⟩ := hasV_bv hyT
    simp only [arith_lt, arith_le, same_bv, bv_int, decide_true, Bool.and_self, ↓reduceDIte]
      at he
    cases he
    refine ⟨trivial, fun M hwf hc hV => ?_⟩
    simp only [tr, isBv_eq ha, isSigned_eq ha, Ty.isBv, Ty.isSigned, ↓reduceIte,
      __smtx_model_eval, haM M hwf hc hV, hbM M hwf hc hV, trV, __smtx_model_eval_bvslt,
      __smtx_model_eval_bvsle, bvsgt_eq hw hi0 hi hj0 hj, bvsgt_eq hw hj0 hj hi0 hi,
      bvsge_eq hw hi0 hi hj0 hj, bvsge_eq hw hj0 hj hi0 hi]
  | u2s _ ih | s2u _ ih =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    obtain ⟨hxT, haM⟩ := ih env _ hE hx
    obtain ⟨i, rfl, hw, hi0, hi⟩ := hasV_bv hxT
    simp only [Result.Ok.injEq] at he
    subst he
    exact ⟨hasV_bv_of hw hi0 hi, fun M hwf hc hV => by simpa only [tr, trV] using haM M hwf hc hV⟩
  | bvAnd ha _ iha ihb | bvOr ha _ iha ihb | bvXor ha _ iha ihb =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    obtain ⟨hxT, haM⟩ := iha env _ hE hx
    obtain ⟨hyT, hbM⟩ := ihb env _ hE hy
    obtain ⟨i, rfl, hw, hi0, hi⟩ := hasV_bv hxT
    obtain ⟨j, rfl, -, hj0, hj⟩ := hasV_bv hyT
    simp only [bv_binary, same_bv, decide_true, Bool.and_self, ↓reduceDIte, Result.Ok.injEq,
      bit_op] at he
    subst he
    first
      | (obtain ⟨h0, h1, hm⟩ := bvand_eq hw hi0 hi hj0 hj
         refine ⟨hasV_bv_of hw h0 h1, fun M hwf hc hV => ?_⟩
         simp only [tr, __smtx_model_eval, haM M hwf hc hV, hbM M hwf hc hV, trV]
         exact hm)
      | (obtain ⟨h0, h1, hm⟩ := bvor_eq hw hi0 hi hj0 hj
         refine ⟨hasV_bv_of hw h0 h1, fun M hwf hc hV => ?_⟩
         simp only [tr, __smtx_model_eval, haM M hwf hc hV, hbM M hwf hc hV, trV]
         exact hm)
      | (obtain ⟨h0, h1, hm⟩ := bvxor_eq hw hi0 hi hj0 hj
         refine ⟨hasV_bv_of hw h0 h1, fun M hwf hc hV => ?_⟩
         simp only [tr, __smtx_model_eval, haM M hwf hc hV, hbM M hwf hc hV, trV]
         exact hm)
  | @bvShl _ _ _ w ha _ iha ihb | @bvAShr _ _ _ w ha _ iha ihb
    | @bvLShr _ _ _ w ha _ iha ihb =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    obtain ⟨hxT, haM⟩ := iha env _ hE hx
    obtain ⟨hyT, hbM⟩ := ihb env _ hE hy
    obtain ⟨i, rfl, hw, hi0, hi⟩ := hasV_bv hxT
    obtain ⟨j, rfl, -, hj0, hj⟩ := hasV_bv hyT
    simp only [bv_binary, same_bv, decide_true, Bool.and_self, ↓reduceDIte, Result.Ok.injEq,
      bit_op] at he
    subst he
    first
      | (refine ⟨hasV_bvmk hw _, fun M hwf hc hV => ?_⟩
         simp only [tr, __smtx_model_eval, haM M hwf hc hV, hbM M hwf hc hV, trV]
         first | exact bvshl_eq hw hj0 | exact bvashr_eq hw hi0 hi hj0)
      | (have hr := lshr_range hi0 hi (pow2_pos (shift_amount w j))
         refine ⟨hasV_bv_of hw hr.1 hr.2, fun M hwf hc hV => ?_⟩
         simp only [tr, __smtx_model_eval, haM M hwf hc hV, hbM M hwf hc hV, trV]
         exact bvlshr_eq hw hi0 hi hj0)
  | narrow _ hv hvw ih =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    obtain ⟨hxT, haM⟩ := ih env _ hE hx
    obtain ⟨i, rfl, hw, hi0, hi⟩ := hasV_bv hxT
    simp only [bv_cast, Result.Ok.injEq] at he
    subst he
    refine ⟨hasV_bvmk hv _, fun M hwf hc hV => ?_⟩
    simp only [tr, __smtx_model_eval, haM M hwf hc hV, trV]
    exact extract_eq hv (Int.le_of_lt hvw)
  | @widen _ s _ _ ha hwv ih =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    obtain ⟨hxT, haM⟩ := ih env _ hE hx
    obtain ⟨i, rfl, hw, hi0, hi⟩ := hasV_bv hxT
    simp only [bv_cast, Result.Ok.injEq] at he
    subst he
    refine ⟨hasV_bvmk (by omega) _, fun M hwf hc hV => ?_⟩
    cases s
    · simp only [tr, isSigned_eq ha, width_eq ha, Ty.isSigned, Ty.width, Bool.false_eq_true,
        ↓reduceIte, __smtx_model_eval, haM M hwf hc hV, trV]
      exact zero_extend_eq hw hi0 hi (Int.le_of_lt hwv)
    · simp only [tr, isSigned_eq ha, width_eq ha, Ty.isSigned, Ty.width, ↓reduceIte,
        __smtx_model_eval, haM M hwf hc hV, trV]
      exact sign_extend_eq hw hi0 hi (Int.le_of_lt hwv)
  | @frac k d hd =>
    intro env v hE he
    rw [eval, real_eq hd] at he
    cases he
    refine ⟨hasV_real_of _, fun M _ _ _ => ?_⟩
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    simp [tr, __smtx_model_eval, lit_eval, trV, ratOf_num_den, __smtx_to_real_coerce,
      __smtx_model_eval_eq, native_veq, __smtx_model_eval_ite, __smtx_model_eval_qdiv_total,
      native_rdiv_total, native_rat_to_real, native_mk_real, native_int_to_real, hd', hd]
    simp [ratOf]
  | rPlus ha _ iha ihb | rMinus ha _ iha ihb | rTimes ha _ iha ihb =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    obtain ⟨hxT, haM⟩ := iha env _ hE hx
    obtain ⟨hyT, hbM⟩ := ihb env _ hE hy
    obtain ⟨p, rfl⟩ := hasV_real hxT
    obtain ⟨q, rfl⟩ := hasV_real hyT
    simp only [arith_plus, arith_minus, arith_times] at he
    rw [real_eq (den_mul_ne p q)] at he
    cases he
    refine ⟨hasV_real_of _, fun M hwf hc hV => ?_⟩
    simp only [tr, isBv_eq ha, Ty.isBv, Bool.false_eq_true, ↓reduceIte, __smtx_model_eval,
      haM M hwf hc hV, hbM M hwf hc hV, trV, ratOf_num_den, __smtx_model_eval_plus,
      __smtx_model_eval__, __smtx_model_eval_mult, native_rplus, native_rneg, native_rmult,
      native_rat_to_real, ratOf_add, ratOf_sub, ratOf_mul]
    congr 1
    push_cast
    ring
  | rDiv ha _ iha ihb =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    obtain ⟨hxT, haM⟩ := iha env _ hE hx
    obtain ⟨hyT, hbM⟩ := ihb env _ hE hy
    obtain ⟨p, rfl⟩ := hasV_real hxT
    obtain ⟨q, rfl⟩ := hasV_real hyT
    by_cases hz : q.num = 0
    · simp [arith_div, hz] at he
    simp only [arith_div, hz, ↓reduceDIte] at he
    have hd : (p.den : Int) * q.num ≠ 0 :=
      Int.mul_ne_zero (by exact_mod_cast p.den_ne_zero) hz
    rw [real_eq hd] at he
    cases he
    refine ⟨hasV_real_of _, fun M hwf hc hV => ?_⟩
    have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (Rat.num_ne_zero.mp hz)
    simp [tr, isBv_eq ha, isReal_eq ha, Ty.isBv, Ty.isReal, __smtx_model_eval, haM M hwf hc hV,
      hbM M hwf hc hV, trV, ratOf_num_den, __smtx_to_real_coerce, ratOf_div p hz,
      __smtx_model_eval_eq, native_veq, __smtx_model_eval_ite, __smtx_model_eval_qdiv_total,
      native_rdiv_total, native_rat_to_real, native_mk_real, hq]
  | rNeg ha ih =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    obtain ⟨hxT, haM⟩ := ih env _ hE hx
    obtain ⟨p, rfl⟩ := hasV_real hxT
    simp only [arith_neg] at he
    cases he
    have hv : Value.RealV (0 - p.num) p.den = .RealV (-p).num (-p).den := by simp
    rw [hv]
    refine ⟨hasV_real_of _, fun M hwf hc hV => ?_⟩
    simp [tr, isBv_eq ha, Ty.isBv, __smtx_model_eval, haM M hwf hc hV, trV, ratOf_num_den,
      __smtx_model_eval_uneg, native_rneg, native_rat_to_real, ratOf_neg]
  | rLt ha _ iha ihb | rGt ha _ iha ihb | rLe ha _ iha ihb | rGe ha _ iha ihb =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i y hy
    obtain ⟨hxT, haM⟩ := iha env _ hE hx
    obtain ⟨hyT, hbM⟩ := ihb env _ hE hy
    obtain ⟨p, rfl⟩ := hasV_real hxT
    obtain ⟨q, rfl⟩ := hasV_real hyT
    simp only [arith_lt, arith_le] at he
    cases he
    refine ⟨trivial, fun M hwf hc hV => ?_⟩
    simp only [tr, isBv_eq ha, Ty.isBv, Bool.false_eq_true, ↓reduceIte, __smtx_model_eval,
      haM M hwf hc hV, hbM M hwf hc hV, trV, ratOf_num_den, __smtx_model_eval_lt,
      __smtx_model_eval_leq, __smtx_model_eval_gt, __smtx_model_eval_geq, native_rlt, native_rleq,
      native_rat_to_real, Rat.cast_lt, Rat.cast_le]
    all_goals
      congr 1
      first
        | exact decide_eq_decide.mpr (Rat.lt_iff _ _)
        | (rw [← decide_not]
           exact decide_eq_decide.mpr (not_lt.symm.trans (not_congr (Rat.lt_iff _ _))))
  | @invoke s args hs hl hargs ih =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i vs hvs
    have hmem := (findSig_spec hs).1
    obtain ⟨hvsT, hvsM⟩ := ev_list hE args (s.params.map Prod.snd) vs (by simpa using hl) ih hvs
    refine ⟨hct s hmem _ vs v hvsT he, fun M hw hc hV => ?_⟩
    simp only [tr, hs, trs_eq]
    rw [eval_spine M _ _ rfl, hvsM M hw hc hV]
    exact hc s hmem _ vs v hvsT he
  | assume _ _ ihp ihb =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i b hb
    cases b
    · rw [dite_eq_right_of_eq_false (eq_false Bool.false_ne_true)] at he
      cases he
    · rw [dite_eq_left_of_eq_true (eq_true rfl)] at he
      obtain ⟨hv, hM⟩ := ihb env v hE he
      exact ⟨hv, fun M hw hc hV => by simp only [tr]; exact hM M hw hc hV⟩
  | @adt c d i fs args hc hl hargs ih =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i vs hvs
    obtain ⟨hvsT, hvsM⟩ := ev_list hE args (fs.map Prod.snd) vs (by simpa using hl) ih hvs
    have hv : v = .ADTV c [] vs := by
      cases P with
      | Program fns cs ss is eq =>
      obtain ⟨hlc, hls⟩ := hPD c d i fs hc
      rw [construct] at he
      simp only [hlc, hls, hO.resolve_all] at he
      cases he; rfl
    subst hv
    refine ⟨hasV_adt hc hvsT, fun M hw hcl hV => ?_⟩
    simp only [tr, hc, trs_eq, trV, trVs_eq]
    rw [eval_spine M _ _ rfl, hvsM M hw hcl hV]
    apply applyAll_ctor M _ _ (by simp [__smtx_model_eval, ctorLike])
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨u, hu, rfl⟩ := ha
    clear hvsM hvs he
    generalize fs.map Prod.snd = Ts at hvsT
    induction hvsT with
    | nil => cases hu
    | cons h _ ihh =>
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact trV_ne hS.data h
      · exact ihh hu'
  | @isCons a c d i fs hc _ ih =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i w hw
    obtain ⟨hwT, hM⟩ := ih env _ hE hw
    obtain ⟨c', vs, d', i', fs', rfl, hc', hname, hvs⟩ := hasV_data hwT
    dsimp only at he
    cases he
    refine ⟨by simp [HasV], fun M hwf hcl hV => ?_⟩
    obtain ⟨hd, hi⟩ := findCtor_spec hc
    obtain ⟨hd', hi'⟩ := findCtor_spec hc'
    have hdd : d' = d := data_eq_of_name hS.data.nodup hd' hd hname
    subst hdd
    simp only [tr, hc, __smtx_model_eval, hM M hwf hcl hV, __smtx_model_eval_dt_tester, trV, hc',
      trVs_eq, head_applyVs, __smtx_apply_head_value, native_veq]
    congr 1
    apply decide_eq_decide.mpr
    constructor
    · intro h
      injection h with _ _ hii
      subst hii
      rw [hi] at hi'
      cases hi'; rfl
    · rintro rfl
      rw [hc] at hc'
      cases hc'; rfl
  | @sel a x d i j T hx _ ih =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i w hw
    obtain ⟨hwT, hM⟩ := ih env _ hE hw
    obtain ⟨c', vs, d', i', fs', rfl, hc', hname, hvs⟩ := hasV_data hwT
    obtain ⟨hd', hi'⟩ := findCtor_spec hc'
    obtain ⟨hd, c, fs, hi, hj⟩ := findSel_spec hx
    have hdd : d' = d := data_eq_of_name hS.data.nodup hd' hd hname
    subst hdd
    have hsel : select_field (fs'.map fun f => Param.Param f.1 f.2) vs x = .Ok v := by
      cases P with
      | Program fns cs ss is eq =>
      obtain ⟨hlc, _⟩ := hPD c' d' i' fs' hc'
      simp only [hlc] at he
      exact he
    obtain ⟨j', T', hj', hvj⟩ := select_field_spec fs' vs hsel
    have hfs := findSel_of hS.data hd' hi' hj'
    rw [hx] at hfs
    cases hfs
    have hv : HasV D v T := forall₂_getElem? hvs hvj (by simp [hj'])
    refine ⟨hv, fun M hwf hcl hV => ?_⟩
    have hlen : vs.length = fs'.length := by simpa using hvs.length_eq
    simp only [tr, hx, __smtx_model_eval, hM M hwf hcl hV, __smtx_model_eval_dt_sel, trV, hc',
      trVs_eq, head_applyVs, __smtx_apply_head_value, native_veq, native_ite, decide_true,
      ↓reduceIte]
    rw [dt_num_sels d'.decl, ctorFields_data hS.data hd', hi']
    simp only [Option.map_some, List.length_map, Option.getD_some, ← hlen]
    have := arg_nth_applyVs (.DtCons (nm d'.name) d'.decl i) (vs.map (trV D)) j (trV D v)
      (by simp [hvj])
    simpa using this

  | @setEmpty A hA =>
    intro env v hE he
    rw [eval, eval_list] at he
    dsimp only [set_insert_all] at he
    cases he
    rw [resolve_fragTy hO _ A hA]
    exact ⟨hasV_set_of hA (fun _ h => nomatch h), fun M _ _ _ => by
      simp only [tr, trs, __smtx_model_eval, trV, trVl, setOf]⟩
  | @setOne a A ha ih =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i vs hvs
    ok_split he
    rename_i zs hzs
    cases he
    obtain ⟨hvT, hvM⟩ := ev_list hE [a] [A] vs rfl (fun p hp => by
      simp at hp
      subst hp
      exact ih) hvs
    obtain ⟨x, rfl, hxT⟩ : ∃ x, vs = [x] ∧ HasV D x A := by
      cases hvT with
      | cons h hs => cases hs; exact ⟨_, rfl, h⟩
    have hA := hasV_fragTy hxT
    have hx1 : ∀ y ∈ [x], HasV D y A := fun y hy => by
      rw [List.mem_singleton.mp hy]; exact hxT
    obtain ⟨hzT, hzm⟩ :=
      set_insert_all_hasV hS.data hO P hPD [x] [] zs (fun _ h => nomatch h) hx1
      hzs
    rw [resolve_fragTy hO _ A hA]
    refine ⟨hasV_set_of hA hzT, fun M hw hc hV => ?_⟩
    have haM := hvM M hw hc hV
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at haM
    simp only [tr, trs, __smtx_model_eval, haM]
    rw [trV_singleton hS.data hxT]
    exact (trV_set_eq hS.data hx1 hzT).mpr fun w => by rw [hzm]; simp
  | @setAdd s a A _ _ ihs iha =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i sv hs'
    ok_split he
    rename_i x hx
    ok_split he
    rename_i zs hzs
    cases he
    obtain ⟨hsT, hsM⟩ := ihs env _ hE (eval_set_ok hs')
    obtain ⟨hxT, hxM⟩ := iha env _ hE hx
    obtain ⟨xs, rfl, hA, hxs⟩ := hasV_set hsT
    simp only [set_elems] at hzs
    obtain ⟨hzT, hzm⟩ := set_insert_hasV hS.data hO P hPD hxs hxT hzs
    have hx1 : ∀ y ∈ [x], HasV D y A := fun y hy => by
      rw [List.mem_singleton.mp hy]; exact hxT
    refine ⟨hasV_set_of hA hzT, fun M hw hc hV => ?_⟩
    simp only [tr, __smtx_model_eval, hsM M hw hc hV, hxM M hw hc hV, set_with]
    rw [trV_singleton hS.data hxT]
    exact trV_union hS.data hx1 hxs hzT fun w => by rw [hzm]; simp
  | @elementOf a s A _ _ iha ihs =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    ok_split he
    rename_i sv hs'
    ok_split he
    rename_i b hb
    cases he
    obtain ⟨hxT, hxM⟩ := iha env _ hE hx
    obtain ⟨hsT, hsM⟩ := ihs env _ hE (eval_set_ok hs')
    obtain ⟨xs, rfl, hA, hxs⟩ := hasV_set hsT
    simp only [set_elems] at hb
    rw [set_contains_hasV hS.data hO P hPD hxs hxT] at hb
    cases hb
    refine ⟨trivial, fun M hw hc hV => ?_⟩
    simp only [tr, __smtx_model_eval, hsM M hw hc hV, hxM M hw hc hV]
    rw [trV_member hS.data x hxs]
    simp only [trV]
  | @subsetOf s u A _ _ ihs ihu =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i sv hs'
    ok_split he
    rename_i uv hu'
    ok_split he
    rename_i b hb
    cases he
    obtain ⟨hsT, hsM⟩ := ihs env _ hE (eval_set_ok hs')
    obtain ⟨huT, huM⟩ := ihu env _ hE (eval_set_ok hu')
    obtain ⟨xs, rfl, hA, hxs⟩ := hasV_set hsT
    obtain ⟨ys, rfl, _, hys⟩ := hasV_set huT
    simp only [set_elems] at hb
    rw [subset_hasV hS.data hO P hPD hxs hys] at hb
    cases hb
    refine ⟨trivial, fun M hw hc hV => ?_⟩
    simp only [tr, __smtx_model_eval, hsM M hw hc hV, huM M hw hc hV]
    rw [trV_subset hS.data hxs hys]
    simp only [trV]
  | @setUnion s u A _ _ ihs ihu =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i sv hs'
    ok_split he
    rename_i uv hu'
    ok_split he
    rename_i zs hzs
    cases he
    obtain ⟨hsT, hsM⟩ := ihs env _ hE (eval_set_ok hs')
    obtain ⟨huT, huM⟩ := ihu env _ hE (eval_set_ok hu')
    obtain ⟨xs, rfl, hA, hxs⟩ := hasV_set hsT
    obtain ⟨ys, rfl, _, hys⟩ := hasV_set huT
    simp only [set_elems] at hzs
    obtain ⟨hzT, hzm⟩ := set_insert_all_hasV hS.data hO P hPD ys xs zs hxs hys hzs
    refine ⟨hasV_set_of hA hzT, fun M hw hc hV => ?_⟩
    simp only [tr, __smtx_model_eval, hsM M hw hc hV, huM M hw hc hV, set_with]
    exact trV_union hS.data hxs hys hzT hzm
  | @setInter s u A _ _ ihs ihu =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i sv hs'
    ok_split he
    rename_i uv hu'
    ok_split he
    rename_i zs hzs
    cases he
    obtain ⟨hsT, hsM⟩ := ihs env _ hE (eval_set_ok hs')
    obtain ⟨huT, huM⟩ := ihu env _ hE (eval_set_ok hu')
    obtain ⟨xs, rfl, hA, hxs⟩ := hasV_set hsT
    obtain ⟨ys, rfl, _, hys⟩ := hasV_set huT
    simp only [set_elems] at hzs
    have hz := set_filter_hasV hS.data hO P hPD ys true hys xs zs hxs hzs
    subst hz
    refine ⟨hasV_set_of hA fun z hz => hxs z (List.mem_filter.mp hz).1, fun M hw hc hV => ?_⟩
    simp only [tr, __smtx_model_eval, hsM M hw hc hV, huM M hw hc hV, set_with]
    exact trV_inter hS.data hxs hys
  | @setDiff s u A _ _ ihs ihu =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i sv hs'
    ok_split he
    rename_i uv hu'
    ok_split he
    rename_i zs hzs
    cases he
    obtain ⟨hsT, hsM⟩ := ihs env _ hE (eval_set_ok hs')
    obtain ⟨huT, huM⟩ := ihu env _ hE (eval_set_ok hu')
    obtain ⟨xs, rfl, hA, hxs⟩ := hasV_set hsT
    obtain ⟨ys, rfl, _, hys⟩ := hasV_set huT
    simp only [set_elems] at hzs
    have hz := set_filter_hasV hS.data hO P hPD ys false hys xs zs hxs hzs
    subst hz
    refine ⟨hasV_set_of hA fun z hz => hxs z (List.mem_filter.mp hz).1, fun M hw hc hV => ?_⟩
    simp only [tr, __smtx_model_eval, hsM M hw hc hV, huM M hw hc hV, set_with]
    exact trV_minus hS.data hxs hys

/-- The bodies of the functions of `S` are typed, so their calls give values of their types, with
any fuel. -/
theorem call_ty (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hP : ProgTy D S P) :
    ∀ (k : Nat) (n : Int), n.toNat = k → CallTy O P D S n
  | 0, n, hn => by
    intro s _ tenv vs v _ hc
    rw [call, dite_eq_left_of_eq_true (eq_true (by omega))] at hc
    cases hc
  | k + 1, n, hn => by
    have ih := call_ty hO hty hS hP k (n - 1) (by omega)
    intro s hs tenv vs v hvs hc
    rw [call, dite_eq_right_of_eq_false (eq_false (by omega))] at hc
    cases P with
    | Program fs _ _ _ _ =>
    obtain ⟨body, hlook, hbody⟩ := hP.1 s hs
    dsimp only at hc
    rw [hlook] at hc
    dsimp only at hc
    ok_split hc
    rename_i bs hbs
    have hE : EnvTy D s.params (Env.Env (bind_types [] [] tenv) bs) := by
      intro x T hx w hw
      obtain ⟨u, hu, huT⟩ := bind_lookup s.params vs bs hbs hvs x T hx
      rw [lookup_var_det hw hu]; exact huT
    exact (ev hO hty hS hP.2 ih hbody _ _ hE hc).1

theorem call_ty' (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hP : ProgTy D S P) (n : Int) :
    CallTy O P D S n :=
  call_ty hO hty hS hP _ n rfl

end Agree

/-! ## The intended model, with the calls as the functions

The model `star (defs D S) (interpOf O P D S) M0 cd N` of `Inox/Model.lean`, where a function of `S`
applied to values is the value of its call, when a call with some fuel gives one. -/

section Star

theorem take_drop_cons {α : Type} : ∀ {l : List α} {k : Nat} {p : α} {rest : List α},
    l.drop k = p :: rest → l.take (k + 1) = l.take k ++ [p] ∧ l.drop (k + 1) = rest
  | [], k, _, _, h => by cases k <;> simp at h
  | a :: l, 0, _, _, h => by simp only [List.drop_zero, List.cons.injEq] at h; simp [h.1, h.2]
  | a :: l, k + 1, _, _, h => by
    simp only [List.drop_succ_cons] at h
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append, List.cons.injEq,
      true_and]
    exact take_drop_cons h

theorem drop_cons_of_lt {α : Type} {l : List α} {k : Nat} (h : k < l.length) :
    ∃ p rest, l.drop k = p :: rest := by
  cases hd : l.drop k with
  | nil => have := congrArg List.length hd; simp at this; omega
  | cons p rest => exact ⟨p, rest, rfl⟩

theorem funVal_eq (cd : Codes) {d : Def} {vs : List SmtValue} {p : native_String × SmtType}
    {rest : List (native_String × SmtType)} (h : d.params.drop vs.length = p :: rest) :
    funVal cd d vs = .Fun (cd.code d.name d.ty vs) p.2 (arrow rest d.ret) := by
  unfold funVal; rw [h]

theorem eval_apply_fun (M : SmtModel) {v : SmtValue} (hv : v ≠ .NotValue) (e : ModelId)
    (A B : SmtType) :
    __smtx_model_eval_apply M (.Fun e A B) v = native_eval_fun_apply M e A B v := by
  cases v <;> first | rfl | exact absurd rfl hv

theorem sig_eq_of_name :
    ∀ {S : List Sig}, (S.map Sig.name).Nodup → ∀ {s s' : Sig}, s ∈ S →
    s' ∈ S → s.name = s'.name → s = s'
  | [], _, _, _, h, _, _ => by simp at h
  | a :: S, hnd, s, s', h1, h2, hn => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h1 with rfl | h1' <;> rcases List.mem_cons.mp h2 with rfl | h2'
    · rfl
    · exact absurd (List.mem_map.mpr ⟨s', h2', hn.symm⟩) hnd.1
    · exact absurd (List.mem_map.mpr ⟨s, h1', hn⟩) hnd.1
    · exact sig_eq_of_name hnd.2 h1' h2' hn

/-- The functions of `S`, as functions of the model. -/
def defs (D : List Data) (S : List Sig) : List Def := S.map (Sig.toDef D)

theorem lookup_toDef : ∀ {S : List Sig}, (S.map Sig.name).Nodup → ∀ {s : Sig}, s ∈ S →
    lookup (defs D S) (s.toDef D).name (s.toDef D).ty = some (s.toDef D)
  | [], _, _, h => by simp at h
  | a :: S, hnd, s, hs => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hs with rfl | hs
    · simp [lookup, defs]
    · have hne : (a.toDef D).name ≠ (s.toDef D).name := fun h =>
        hnd.1 (List.mem_map.mpr ⟨s, hs, (nm_inj h).symm⟩)
      have ih := lookup_toDef (D := D) hnd.2 hs
      simp only [lookup, defs] at ih
      simp [lookup, defs, hne, ih]

theorem toDef_params_ne {S : List Sig} (hS : SigOk D S) {s : Sig} (hs : s ∈ S) :
    ∀ q ∈ (s.toDef D).params, q.2 ≠ .None := by
  intro q hq
  simp only [Sig.toDef, ptys, List.mem_map] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  exact trT_ne hS.data (hS.params s hs p hp)

open Classical in
/-- The interpretation of the functions of `S` by their calls: the value of a call with some fuel
to values of Inox whose SMT values are `ws`, if one gives a value, and otherwise no value. Two
lists of values of Inox are the same SMT values when they differ by the order of the elements of
their sets only, and the calls to them give the same SMT value (`call_congr`). -/
noncomputable def interpOf (O : Oracle) (P : Program) (D : List Data) (S : List Sig) (d : Def)
    (ws : List SmtValue) : SmtValue :=
  if h : ∃ v, ∃ s ∈ S, ∃ n vs, (s.toDef D) = d ∧
      List.Forall₂ (HasV D) vs (s.params.map Prod.snd) ∧ ws = vs.map (trV D) ∧
      call O P n s.name [] [] vs = .Ok v then
    trV D h.choose else .NotValue

open Classical in
/-- The interpretation of the functions of `S` by their calls with `n` fuel. -/
noncomputable def interpAt (O : Oracle) (P : Program) (D : List Data) (S : List Sig) (n : Int)
    (d : Def) (ws : List SmtValue) : SmtValue :=
  if h : ∃ v, ∃ s ∈ S, ∃ vs, (s.toDef D) = d ∧
      List.Forall₂ (HasV D) vs (s.params.map Prod.snd) ∧ ws = vs.map (trV D) ∧
      call O P n s.name [] [] vs = .Ok v then
    trV D h.choose else .NotValue

/-- The calls with `n` fuel to values that are the same SMT values give the same SMT value. -/
def CallCongr (O : Oracle) (P : Program) (D : List Data) (S : List Sig) (n : Int) : Prop :=
  ∀ s ∈ S, ∀ vs vs' v v', List.Forall₂ (HasV D) vs (s.params.map Prod.snd) →
    List.Forall₂ (HasV D) vs' (s.params.map Prod.snd) → vs.map (trV D) = vs'.map (trV D) →
    call O P n s.name [] [] vs = .Ok v → call O P n s.name [] [] vs' = .Ok v' →
    trV D v = trV D v'

theorem interpAt_eq {O : Oracle} {P : Program} {S : List Sig} (hS : SigOk D S) {n : Int}
    (hcg : CallCongr O P D S n) {s : Sig} (hs : s ∈ S) {vs : List Value} {v : Value}
    (hvs : List.Forall₂ (HasV D) vs (s.params.map Prod.snd))
    (hc : call O P n s.name [] [] vs = .Ok v) :
    interpAt O P D S n (s.toDef D) (vs.map (trV D)) = trV D v := by
  have h : ∃ v, ∃ s' ∈ S, ∃ vs', (s'.toDef D) = (s.toDef D) ∧
      List.Forall₂ (HasV D) vs' (s'.params.map Prod.snd) ∧ vs.map (trV D) = vs'.map (trV D) ∧
      call O P n s'.name [] [] vs' = .Ok v :=
    ⟨v, s, hs, vs, rfl, hvs, rfl, hc⟩
  simp only [interpAt, h, ↓reduceDIte]
  obtain ⟨s', hs', vs', hd, hvs', hm, hc'⟩ := h.choose_spec
  have := sig_eq_of_name hS.nodup hs' hs (nm_inj (congrArg Def.name hd))
  subst this
  exact (hcg s' hs' vs vs' v _ hvs hvs' hm hc hc').symm

theorem interpOf_eq {O : Oracle} {P : Program} {S : List Sig} (hP : ProgFrag P) (hS : SigOk D S)
    (hcg : ∀ n, CallCongr O P D S n) {s : Sig} (hs : s ∈ S) {n : Int} {vs : List Value}
    {v : Value} (hvs : List.Forall₂ (HasV D) vs (s.params.map Prod.snd))
    (hc : call O P n s.name [] [] vs = .Ok v) :
    interpOf O P D S (s.toDef D) (vs.map (trV D)) = trV D v := by
  have h : ∃ v, ∃ s' ∈ S, ∃ n vs', (s'.toDef D) = (s.toDef D) ∧
      List.Forall₂ (HasV D) vs' (s'.params.map Prod.snd) ∧ vs.map (trV D) = vs'.map (trV D) ∧
      call O P n s'.name [] [] vs' = .Ok v :=
    ⟨v, s, hs, n, vs, rfl, hvs, rfl, hc⟩
  simp only [interpOf, h, ↓reduceDIte]
  obtain ⟨s', hs', n', vs', hd, hvs', hm, hc'⟩ := h.choose_spec
  have := sig_eq_of_name hS.nodup hs' hs (nm_inj (congrArg Def.name hd))
  subst this
  rcases Int.le_total n n' with hnn | hnn
  · exact (hcg n' s' hs' vs vs' v _ hvs hvs' hm (call_ok_mono hP hnn hc) hc').symm
  · exact (hcg n s' hs' vs vs' v _ hvs hvs' hm hc (call_ok_mono hP hnn hc')).symm

theorem typed_map {D : List Data} (hD : DataOk D) (M : SmtModel) :
    ∀ {ps : List (Id × Ty)} {vs : List Value}, List.Forall₂ (HasV D) vs (ps.map Prod.snd) →
      List.Forall₂ (Typed M) (ptys D ps) (vs.map (trV D))
  | [], [], _ => .nil
  | _ :: _, _ :: _, .cons h hs => .cons (typed_trV hD M _ h) (typed_map hD M hs)

/-- The values of the sorts of the types of the bridge are those of the values of the types, when
no real is among them: a real of a model need not be a fraction. -/
theorem typed_inv {D : List Data} (hD : DataOk D) (hR : RealFree D) {M : SmtModel}
    {ps : List (Id × Ty)} (hf : ∀ p ∈ ps, FragTy D p.2) (hne : ∀ p ∈ ps, NoReal p.2) :
    ∀ {ws : List SmtValue}, List.Forall₂ (Typed M) (ptys D ps) ws →
      ∃ vs, List.Forall₂ (HasV D) vs (ps.map Prod.snd) ∧ ws = vs.map (trV D) := by
  induction ps with
  | nil => intro ws h; simp only [ptys, List.map_nil] at h; cases h; exact ⟨[], .nil, rfl⟩
  | cons p ps ih =>
    intro ws h
    simp only [ptys, List.map_cons] at h
    cases h with
    | cons hw hws =>
      obtain ⟨vs, hvs, rfl⟩ := ih (fun q hq => hf q (.tail _ hq)) (fun q hq => hne q (.tail _ hq))
        hws
      obtain ⟨v, hv, rfl⟩ := typed_inv1 hD hR (hf p (.head _)) (hne p (.head _)) hw.1 hw.2
      exact ⟨v :: vs, .cons hv hvs, rfl⟩

theorem applyAll_setConsts (M : SmtModel) (σ : List (native_String × SmtType × SmtValue)) :
    ∀ fv ws, applyAll (setConsts M σ) fv ws = applyAll M fv ws
  | _, [] => rfl
  | fv, w :: ws => by
    simp only [applyAll]
    rw [model_eval_apply_setConsts]
    exact applyAll_setConsts M σ _ ws

/-- Applying the function value of `d` applied to `ws` to the remaining values `rest` applies `d`
to all of them, when that gives a value of its sort. -/
theorem applyAll_funVal {Q : List Def} {I : Def → List SmtValue → SmtValue} {M0 N : SmtModel}
    {cd : Codes} {d : Def} (hd : lookup Q d.name d.ty = some d)
    (hp : ∀ q ∈ d.params, q.2 ≠ .None) :
    ∀ (rest ws : List SmtValue), ws.length < d.params.length →
      ws.length + rest.length = d.params.length →
      List.Forall₂ (Typed M0) (d.params.drop ws.length) rest →
      Typed M0 (d.name, d.ret) (I d (ws ++ rest)) →
      applyAll (Model.star Q I M0 cd N) (funVal cd d ws) rest = I d (ws ++ rest)
  | [], ws, hlt, hlen, _, _ => by simp at hlen; omega
  | x :: rest, ws, hlt, hlen, hty, hI => by
    obtain ⟨p, r, hdrop⟩ := drop_cons_of_lt hlt
    rw [hdrop] at hty
    cases hty with
    | cons hx hty =>
    have hxne : x ≠ .NotValue := by
      intro h; subst h
      exact hp p (List.mem_of_mem_drop (by rw [hdrop]; exact .head _)) (by rw [← hx.1]; rfl)
    obtain ⟨_, hdrop1⟩ := take_drop_cons hdrop
    simp only [applyAll]
    rw [funVal_eq cd hdrop, eval_apply_fun _ hxne]
    simp only [native_eval_fun_apply, native_default_fun_id, cd.ne, ↓reduceIte, model_fun_lookup,
      Model.star, fns, cd.decode_code, hd]
    by_cases hlen' : ws.length + 1 < d.params.length
    · have hap : applied I cd d ws x = funVal cd d (ws ++ [x]) := by
        simp only [applied, hlen', ↓reduceIte]
      obtain ⟨p', r', hdrop'⟩ :=
        drop_cons_of_lt (l := d.params) (k := (ws ++ [x]).length) (by simp; omega)
      have hfv := funVal_eq cd hdrop'
      have hr : r = p' :: r' := by
        rw [← hdrop1, ← hdrop']; simp
      rw [hap, typedOr_of M0 (by rw [hfv, hr]; exact ⟨rfl, rfl⟩)]
      have := applyAll_funVal (N := N) (cd := cd) hd hp rest (ws ++ [x]) (by simp; omega)
        (by simp at hlen ⊢; omega)
        (by rw [show (ws ++ [x]).length = ws.length + 1 by simp, hdrop1]; exact hty)
        (by simpa using hI)
      rw [List.append_assoc, List.singleton_append] at this
      exact this
    · have hlast : ws.length + 1 = d.params.length := by omega
      have hrest : rest = [] := by
        have : rest.length = 0 := by simp at hlen; omega
        exact List.eq_nil_of_length_eq_zero this
      subst hrest
      have hr : r = [] := by rw [← hdrop1, hlast]; simp
      have hap : applied I cd d ws x = I d (ws ++ [x]) := by
        simp only [applied, hlen', ↓reduceIte]
      rw [hap, typedOr_of M0 (by rw [hr]; exact hI)]
      rfl

variable {O : Oracle} {P : Program} {D : List Data} {S : List Sig}

theorem call_tenv (hP : ProgTy D S P) {s : Sig} (hs : s ∈ S) (n : Int)
    (tenv : List TypeBinding) (vs : List Value) :
    call O P n s.name [] tenv vs = call O P n s.name [] [] vs := by
  cases P with
  | Program fs _ _ _ _ =>
  obtain ⟨body, hlook, _⟩ := hP.1 s hs
  rw [call, call]
  simp only [hlook, bind_types]

/-- The calls with `n` fuel agree with the functions of a model that interprets them by an
interpretation that agrees with these calls. -/
theorem callsOk_of (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hP : ProgTy D S P)
    (I : Def → List SmtValue → SmtValue) (M0 N : SmtModel) (cd : Codes) (n : Int)
    (hIn : ∀ s ∈ S, ∀ vs v, List.Forall₂ (HasV D) vs (s.params.map Prod.snd) →
      call O P n s.name [] [] vs = .Ok v → I (s.toDef D) (vs.map (trV D)) = trV D v) :
    CallsOk O P D S n (Model.star (defs D S) I M0 cd N) := by
  intro s hs tenv vs v hvs hc
  rw [call_tenv hP hs] at hc
  have hv : HasV D v s.ret := call_ty' hO hty hS hP n s hs [] vs v hvs hc
  have hI : I (s.toDef D) (vs.map (trV D)) = trV D v := hIn s hs vs v hvs hc
  have hlook := lookup_toDef (D := D) hS.nodup hs
  have hlen : vs.length = s.params.length := by simpa using hvs.length_eq
  simp only [__smtx_model_eval, native_model_lookup]
  by_cases hnil : s.params = []
  · have hdp : (s.toDef D).params = [] := by simp [Sig.toDef, ptys, hnil]
    have hvs0 : vs = [] := List.eq_nil_of_length_eq_zero (by rw [hlen, hnil]; rfl)
    subst hvs0
    have hdv : defVal I cd (s.toDef D) = trV D v := by
      simp only [defVal, hdp, ↓reduceIte]; exact hI
    rw [star_def (defs D S) I M0 cd N (k := model_key (nm s.name) (s.toDef D).ty)
        rfl
      hlook (by
        rw [hdv]
        simp only [model_key, Sig.toDef, ptys, hnil, List.map_nil, arrow]
        exact typed_trV hS.data M0 (nm s.name) hv)]
    rw [hdv]; rfl
  · have hpos : 0 < (s.toDef D).params.length := by
      simp only [Sig.toDef, ptys, List.length_map]
      exact List.length_pos_iff.mpr hnil
    have hdp : (s.toDef D).params ≠ [] := List.ne_nil_of_length_pos hpos
    obtain ⟨p, rest, hdrop0⟩ := drop_cons_of_lt (k := 0) hpos
    have hfv := funVal_eq cd (vs := []) hdrop0
    have hpar : (s.toDef D).params = p :: rest := by simpa using hdrop0
    have hdv : defVal I cd (s.toDef D) = funVal cd (s.toDef D) [] := by
      simp only [defVal, hdp, ↓reduceIte]
    rw [star_def (defs D S) I M0 cd N (k := model_key (nm s.name) (s.toDef D).ty)
        rfl
      hlook (by
        rw [hdv, hfv]
        show __smtx_typeof_value _ = arrow (s.toDef D).params (s.toDef D).ret ∧ _
        rw [hpar]; exact ⟨rfl, rfl⟩)]
    rw [hdv]
    have := applyAll_funVal (Q := defs D S) (I := I) (M0 := M0) (N := N) (cd := cd)
      hlook (toDef_params_ne hS hs) (vs.map (trV D)) [] (by simpa using hpos)
      (by simp only [List.length_nil, List.length_map, Nat.zero_add, hlen]
          simp [Sig.toDef, ptys])
      (by rw [List.length_nil, List.drop_zero]; exact typed_map hS.data M0 hvs)
      (by rw [List.nil_append, hI]; exact typed_trV hS.data M0 _ hv)
    rw [this, List.nil_append]; exact hI

end Star

/-! ## The defining equations hold in the intended model -/

section Equations

theorem eval_eq_term (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (.eq x y) =
      __smtx_model_eval_eq (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval]

theorem eval_eq_bool (a b : SmtValue) : ∃ c, __smtx_model_eval_eq a b = .Boolean c := by
  unfold __smtx_model_eval_eq; split <;> exact ⟨_, rfl⟩

theorem eval_eq_self {D : List Data} (hD : DataOk D) {v : Value} {T : Ty} (h : HasV D v T) :
    __smtx_model_eval_eq (trV D v) (trV D v) = .Boolean true := by
  rw [eval_eq_trV hD h]; simp [trV]

theorem typed_bindValues {M : SmtModel} : ∀ {qs : List (native_String × SmtType)}
    {ws : List SmtValue}, List.Forall₂ (Typed M) qs ws → ∀ e ∈ bindValues qs ws,
      __smtx_typeof_value e.2.2 = e.2.1 ∧ __smtx_value_canonical M.usortDom e.2.2 = true
  | [], [], .nil, e, h => by simp [bindValues] at h
  | _ :: _, _ :: _, .cons hw hws, e, h => by
    simp only [bindValues, List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact hw
    · exact typed_bindValues hws e h

theorem mem_bindValues : ∀ {qs : List (native_String × SmtType)} {ws : List SmtValue}
    {e : native_String × SmtType × SmtValue}, e ∈ bindValues qs ws → (e.1, e.2.1) ∈ qs
  | [], _, _, h => by simp [bindValues] at h
  | _ :: _, [], _, h => by simp [bindValues] at h
  | _ :: _, _ :: _, e, h => by
    simp only [bindValues, List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact .head _
    · exact .tail _ (mem_bindValues h)

theorem wf_setConsts {M : SmtModel} {σ : List (native_String × SmtType × SmtValue)}
    (hw : model_wf M)
    (hσ : ∀ e ∈ σ, __smtx_typeof_value e.2.2 = e.2.1 ∧
      __smtx_value_canonical M.usortDom e.2.2 = true) :
    model_wf (setConsts M σ) := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  refine ⟨?_, ?_, h3, h4⟩
  · intro isVar s T hT
    simp only [setConsts]
    split
    · exact h1 _ _ _ hT
    · split
      · rename_i e he
        unfold bindingOf at he
        have hp := List.find?_some he
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        rw [← hp.2]; exact (hσ e (List.mem_of_find?_eq_some he)).1
      · exact h1 _ _ _ hT
  · intro isVar s T hT
    simp only [setConsts]
    split
    · exact h2 _ _ _ hT
    · split
      · rename_i e he
        unfold bindingOf at he
        exact (hσ e (List.mem_of_find?_eq_some he)).2
      · exact h2 _ _ _ hT

/-- The constants of distinct names `qs`, bound to `ws` after bindings of other names, have the
values `ws`. -/
theorem eval_consts (M : SmtModel) : ∀ (qs : List (native_String × SmtType)) (ws : List SmtValue)
    (pre : List (native_String × SmtType × SmtValue)),
    (qs.map Prod.fst).Nodup → ws.length = qs.length →
    (∀ e ∈ pre, e.1 ∉ qs.map Prod.fst) →
    (qs.map fun q => SmtTerm.UConst q.1 q.2).map
      (__smtx_model_eval (setConsts M (pre ++ bindValues qs ws))) = ws
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | q :: qs, w :: ws, pre, hnd, hlen, hpre => by
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [List.map_cons, List.cons.injEq]
    constructor
    · have hnone : pre.find? (fun e => e.1 == q.1 && e.2.1 == q.2) = none := by
        apply List.find?_eq_none.mpr
        intro e he h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        exact hpre e he (by rw [h.1]; simp)
      have hb : bindingOf (pre ++ bindValues (q :: qs) (w :: ws)) q.1 q.2 = some (q.1, q.2, w) := by
        unfold bindingOf; rw [List.find?_append, hnone]; simp [bindValues]
      show native_model_lookup _ q.1 q.2 = w
      rw [lookup_setConsts, hb]
    · have := eval_consts M qs ws (pre ++ [(q.1, q.2, w)]) hnd.2 (by simpa using hlen) (by
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact fun h => hpre e he (by simp [h])
        · simp only [List.mem_singleton] at he; subst he; exact hnd.1)
      rw [List.append_assoc, List.singleton_append] at this
      exact this

/-- The constant of a variable bound by a call is bound to its value. -/
theorem bindingOf_var : ∀ (ps : List (Id × Ty)) (vs : List Value) (bs : List Binding),
    bind_all (ps.map Prod.fst) vs = .Ok bs → ∀ x T, ps.lookup x = some T → ∀ w,
      lookup_var bs x = .Ok w →
      bindingOf (bindValues (ptys D ps) (vs.map (trV D))) (nm x) (trT D T) = some (nm x, trT D T,
          trV D w)
  | [], _, _, _, x, T, hx, _, _ => by simp at hx
  | _ :: _, [], _, h, _, _, _, _, _ => by simp [bind_all] at h
  | (y, U) :: ps, v :: vs, bs, h, x, T, hx, w, hw => by
    simp only [List.map_cons] at h
    rw [bind_all] at h
    ok_split h
    rename_i bs' hbs'
    cases h
    by_cases hxy : x = y
    · subst hxy
      simp only [List.lookup_cons_self, Option.some.injEq] at hx
      subst hx
      rw [lookup_var, dite_eq_left_of_eq_true (eq_true rfl)] at hw
      cases hw
      simp [bindingOf, bindValues, ptys]
    · have hx' : ps.lookup x = some T := by
        have hb : (x == y) = false := beq_false_of_ne hxy
        simp only [List.lookup, hb] at hx
        exact hx
      rw [lookup_var, dite_eq_right_of_eq_false (eq_false hxy)] at hw
      have ih := bindingOf_var (D := D) ps vs bs' hbs' x T hx' w hw
      have hne : nm y ≠ nm x := fun h => hxy (nm_inj h).symm
      simp only [bindingOf, bindValues, ptys] at ih ⊢
      simp only [List.zipWith_map] at ih
      simp [hne, ih]

/-- The body of `s` in `P` is `body`. -/
def HasBody (P : Program) (s : Sig) (body : Expr) : Prop :=
  match P with
  | .Program fs _ _ _ _ =>
    lookup_fun fs s.name = .Ok (.FunDef s.name [] (s.params.map Prod.fst) body)

/-- `e` is the defining equation of the function `s` of `P`: its parameters are the constants of
those of `s`, and its term equates the constant of `s` applied to them with the translation of
the body of `s`. -/
def EqFor (P : Program) (D : List Data) (S : List Sig) (s : Sig) (e : Equation) : Prop :=
  ∃ body, HasBody P s body ∧ HasTy D S s.params body s.ret ∧ e.params = ptys D s.params ∧
    __eo_to_smt e.term = .eq
      (spine (.UConst (nm s.name) (s.toDef D).ty) ((ptys D s.params).map fun q => .UConst q.1 q.2))
      (tr D S s.params body)

/-- The arguments `ws` of a defining equation are accepted when the calls of its function to them
give a value with some fuel. -/
def okCall (O : Oracle) (P : Program) (D : List Data) (S : List Sig) (e : Equation) (ws : List
    SmtValue) :
    Prop :=
  ∀ s ∈ S, EqFor P D S s e → ∀ vs, List.Forall₂ (HasV D) vs (s.params.map Prod.snd) →
    ws = vs.map (trV D) → ∃ n v, call O P n s.name [] [] vs = .Ok v

/-- The arguments `ws` of a defining equation are accepted when they are values of Inox to which
the call of its function gives a value with some fuel. Unlike `okCall`, it refuses the arguments
that are not values of Inox: the reals that are not fractions. -/
def okCallV (O : Oracle) (P : Program) (D : List Data) (S : List Sig) (e : Equation) (ws : List
    SmtValue) :
    Prop :=
  ∀ s ∈ S, EqFor P D S s e → ∃ vs, List.Forall₂ (HasV D) vs (s.params.map Prod.snd) ∧
    ws = vs.map (trV D) ∧ ∃ n v, call O P n s.name [] [] vs = .Ok v

/-- No real is among the parameters of the functions and the fields of the datatypes: then every
value of a model at their sorts is a value of Inox. -/
structure Discrete (D : List Data) (S : List Sig) : Prop where
  data : RealFree D
  params : ∀ s ∈ S, ∀ p ∈ s.params, NoReal p.2

variable {O : Oracle} {P : Program} {D : List Data} {S : List Sig}

/-- A model where the calls agree, with the constants of the parameters of a function set to
values of their types: it is well-formed, the calls agree in it, and the variables of the function
have the values. -/
theorem bound_model (hS : SigOk D S) {s : Sig} (hs : s ∈ S) {M : SmtModel} (hw : model_wf M)
    {vs : List Value} (hvs : List.Forall₂ (HasV D) vs (s.params.map Prod.snd)) :
    model_wf (setConsts M (bindValues (ptys D s.params) (vs.map (trV D)))) ∧
      (∀ m, CallsOk O P D S m M →
        CallsOk O P D S m (setConsts M (bindValues (ptys D s.params) (vs.map (trV D))))) ∧
      ∀ bs, bind_all (s.params.map Prod.fst) vs = .Ok bs →
        VarsOk D s.params (Env.Env (bind_types [] [] []) bs)
          (setConsts M (bindValues (ptys D s.params) (vs.map (trV D)))) := by
  have hσ : ∀ s' ∈ S, bindingOf (bindValues (ptys D s.params) (vs.map (trV D))) (nm s'.name)
      (s'.toDef D).ty = none := by
    intro s' hs'
    unfold bindingOf
    apply List.find?_eq_none.mpr
    intro e he h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have hm := mem_bindValues he
    simp only [ptys, List.mem_map] at hm
    obtain ⟨p, hp, hpe⟩ := hm
    have h1 : nm p.1 = e.1 := congrArg Prod.fst hpe
    exact hS.fresh s hs p hp s' hs' (nm_inj (h1.trans h.1))
  refine ⟨wf_setConsts hw (typed_bindValues (typed_map hS.data _ hvs)), ?_, ?_⟩
  · intro m hcalls s' hs' tenv us u hus hu
    have := hcalls s' hs' tenv us u hus hu
    simp only [__smtx_model_eval] at this ⊢
    rw [applyAll_setConsts, lookup_setConsts, hσ s' hs']
    exact this
  · intro bs hbs x T hx w hw
    show native_model_lookup _ (nm x) (trT D T) = trV D w
    rw [lookup_setConsts, bindingOf_var s.params vs bs hbs x T hx w hw]

/-- The value of a call is that of the term of the body of the function, in a well-formed model
where the calls with less fuel agree and where the constants of the parameters are set to the
arguments. -/
theorem call_eval (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hP : ProgTy D S P)
    {s : Sig} (hs : s ∈ S) {body : Expr} (hbody : HasBody P s body)
    (hbty : HasTy D S s.params body s.ret) {M : SmtModel} (hw : model_wf M) {n : Int}
    (hcalls0 : CallsOk O P D S (n - 1) M) {vs : List Value} {v : Value}
    (hvs : List.Forall₂ (HasV D) vs (s.params.map Prod.snd))
    (hc : call O P n s.name [] [] vs = .Ok v) :
    HasV D v s.ret ∧
      __smtx_model_eval (setConsts M (bindValues (ptys D s.params) (vs.map (trV D))))
        (tr D S s.params body) = trV D v := by
  obtain ⟨hwf', hcallsT, hVgen⟩ := bound_model (O := O) (P := P) hS hs hw hvs
  have hcalls := hcallsT (n - 1) hcalls0
  generalize setConsts M (bindValues (ptys D s.params) (vs.map (trV D))) = M' at hwf' hcalls hVgen
  by_cases hn : n ≤ 0
  · rw [call, dite_eq_left_of_eq_true (eq_true hn)] at hc; cases hc
  rw [call, dite_eq_right_of_eq_false (eq_false hn)] at hc
  cases P with
  | Program fs _ _ _ _ =>
  simp only [HasBody] at hbody
  dsimp only at hc
  rw [hbody] at hc
  dsimp only at hc
  ok_split hc
  rename_i bs hbs
  have hE : EnvTy D s.params (Env.Env (bind_types [] [] []) bs) := by
    intro x T hx w hw
    obtain ⟨u, hu, huT⟩ := bind_lookup s.params vs bs hbs hvs x T hx
    rw [lookup_var_det hw hu]; exact huT
  have hV := hVgen bs hbs
  obtain ⟨hvT, hvM⟩ := ev hO hty hS hP.2 (call_ty' hO hty hS hP (n - 1)) hbty _ _ hE hc
  exact ⟨hvT, hvM _ hwf' hcalls hV⟩

/-- The calls to values that are the same SMT values give the same SMT value: the value of a
call is that of a term in a model that depends on the SMT values of the arguments only. -/
theorem call_congr (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hP : ProgTy D S P)
    {M0 N : SmtModel} (cd : Codes) (hM0 : model_wf M0) (hN : model_wf N)
    (hu : N.usortDom = M0.usortDom) : ∀ (k : Nat) (n : Int), n.toNat = k → CallCongr O P D S n
  | 0, n, hn => fun s _ vs vs' v v' _ _ _ hc _ => by
    rw [call, dite_eq_left_of_eq_true (eq_true (by omega))] at hc
    cases hc
  | k + 1, n, hn => by
    have ih := call_congr hO hty hS hP cd hM0 hN hu k (n - 1) (by omega)
    intro s hs vs vs' v v' hvs hvs' hm hc hc'
    have hw : model_wf (Model.star (defs D S) (interpAt O P D S (n - 1)) M0 cd N) :=
      wf_star (defs D S) _ M0 cd hM0 hN hu
    have hcalls : CallsOk O P D S (n - 1)
        (Model.star (defs D S) (interpAt O P D S (n - 1)) M0 cd N) :=
      callsOk_of hO hty hS hP _ M0 N cd (n - 1) fun s hs vs v hvs hc => interpAt_eq hS ih hs hvs hc
    have hP' := hP
    cases P with
    | Program fs cs ss is eq =>
    obtain ⟨body, hlook, hbty⟩ := hP'.1 s hs
    have h1 := (call_eval hO hty hS hP hs (body := body) hlook hbty hw hcalls hvs hc).2
    have h2 := (call_eval hO hty hS hP hs (body := body) hlook hbty hw hcalls hvs' hc').2
    rw [hm] at h1
    exact h1.symm.trans h2

/-- The calls agree with the functions of the intended model. -/
theorem callsOk_star (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hPF : ProgFrag P)
    (hP : ProgTy D S P) {M0 N : SmtModel} (cd : Codes) (hM0 : model_wf M0) (hN : model_wf N)
    (hu : N.usortDom = M0.usortDom) (n : Int) :
    CallsOk O P D S n (Model.star (defs D S) (interpOf O P D S) M0 cd N) :=
  callsOk_of hO hty hS hP _ M0 N cd n fun _ hs _ _ hvs hc =>
    interpOf_eq hPF hS (fun m => call_congr hO hty hS hP cd hM0 hN hu _ m rfl) hs hvs hc

/-- A well-formed model where the calls agree satisfies the defining equations of the program on
the values of Inox where the calls give values. -/
theorem goodOn_callsV (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hP : ProgTy D S P)
    {eqs : List Equation} (hE : ∀ e ∈ eqs, ∃ s ∈ S, EqFor P D S s e) {M : SmtModel}
    (hw : model_wf M) (hcalls0 : ∀ m, CallsOk O P D S m M) : GoodOn (okCallV O P D S) eqs M := by
  intro e he ws hws
  obtain ⟨s, hs, hfor⟩ := hE e he
  obtain ⟨body, hbody, hbty, hpe, hterm⟩ := hfor
  rw [hterm, eval_eq_term]
  refine ⟨eval_eq_bool _ _, fun hok => ?_⟩
  rw [hpe] at hws ⊢
  obtain ⟨vs, hvs, rfl, n, v, hc⟩ := hok s hs ⟨body, hbody, hbty, hpe, hterm⟩
  obtain ⟨hwf', hcallsT, hVgen⟩ := bound_model (O := O) (P := P) hS hs hw hvs
  have hnd : ((ptys D s.params).map Prod.fst).Nodup := by
    have : (ptys D s.params).map Prod.fst = (s.params.map Prod.fst).map nm := by
      simp [ptys, List.map_map, Function.comp_def]
    rw [this]
    exact (hS.pnodup s hs).map (fun _ _ h => nm_inj h)
  have hlen : (vs.map (trV D)).length = (ptys D s.params).length := by
    simpa [ptys] using hvs.length_eq
  have hl := eval_consts M (ptys D s.params) (vs.map (trV D)) [] hnd hlen (by simp)
  rw [List.nil_append] at hl
  rw [eval_spine _ _ _ rfl, hl, hcallsT n (hcalls0 n) s hs [] vs v hvs hc]
  obtain ⟨hvT, hvM⟩ := call_eval hO hty hS hP hs hbody hbty hw (hcalls0 (n - 1)) hvs hc
  rw [hvM]
  exact eval_eq_self hS.data hvT

/-- A well-formed model where the calls agree satisfies the defining equations of the program on
the arguments where the calls give values, when no real is among the parameters. -/
theorem goodOn_calls (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hP : ProgTy D S P)
    (hdis : Discrete D S)
    {eqs : List Equation} (hE : ∀ e ∈ eqs, ∃ s ∈ S, EqFor P D S s e) {M : SmtModel}
    (hw : model_wf M) (hcalls0 : ∀ m, CallsOk O P D S m M) : GoodOn (okCall O P D S) eqs M := by
  intro e he ws hws
  have hg := goodOn_callsV hO hty hS hP hE hw hcalls0 e he ws hws
  refine ⟨hg.1, fun hok => hg.2 fun s hs hfor => ?_⟩
  have hfor' := hfor
  obtain ⟨_, _, _, hpe, _⟩ := hfor'
  rw [hpe] at hws
  obtain ⟨vs, hvs, rfl⟩ := typed_inv hS.data hdis.data (hS.params s hs) (hdis.params s hs) hws
  exact ⟨vs, hvs, rfl, hok s hs hfor vs hvs rfl⟩

/-- The intended model satisfies the defining equations of the program on the arguments where
the calls give values. -/
theorem goodOn_star (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hPF : ProgFrag P)
    (hP : ProgTy D S P) (hdis : Discrete D S) {eqs : List Equation}
    (hE : ∀ e ∈ eqs, ∃ s ∈ S, EqFor P D S s e)
    {M0 N : SmtModel} (cd : Codes) (hM0 : model_wf M0) (hN : model_wf N)
    (hu : N.usortDom = M0.usortDom) :
    GoodOn (okCall O P D S) eqs (Model.star (defs D S) (interpOf O P D S) M0 cd N) :=
  goodOn_calls hO hty hS hP hdis hE (wf_star (defs D S) (interpOf O P D S) M0 cd hM0 hN hu)
    fun m => callsOk_star hO hty hS hPF hP cd hM0 hN hu m

/-- When the calls of the functions of `S` to values of their types give values, every guard is
fine: `GuardOk` holds for every clause. -/
theorem guardOk_total
    (htot : ∀ s ∈ S, ∀ vs, List.Forall₂ (HasV D) vs (s.params.map Prod.snd) →
      ∃ n v, call O P n s.name [] [] vs = .Ok v)
    (eqs : List Equation) (assums : List Term) (c : Term) :
    GuardOk (okCall O P D S) eqs assums c :=
  fun _ _ _ _ _ _ _ _ _ _ _ s hs _ vs hvs _ => htot s hs vs hvs

/-- What an accepted certificate says of the intended model: if the checker accepts a certificate
whose defining equations are those of the functions of `S` in `P`, then the intended model, whose
functions are the calls of `P`, does not satisfy the base clauses of the query, given that the
facts hold in the models where the equations hold on the arguments where the calls give values
(except the unfoldings whose guards imply that the calls give values). The hypothesis on the
facts stays: only the guarded unfoldings are discharged. -/
theorem no_star_model (sound : LogosSound) (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S)
    (hPF : ProgFrag P) (hP : ProgTy D S P) (hdis : Discrete D S)
    {certificate : Logos.Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked) (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hkeeps : r.keeps = true)
    (hE : ∀ e ∈ r.equations, ∃ s ∈ S, EqFor P D S s e)
    (hfacts : FactsHoldBy (GoodOn (okCall O P D S) r.equations)
      (GuardedUnfold (okCall O P D S) r.equations) (extend r.base r.fresh) r.facts)
    {M0 N : SmtModel} (cd : Codes) (hM0 : model_wf M0) (hN : model_wf N)
    (hu : N.usortDom = M0.usortDom) :
    ¬ Satisfies (Model.star (defs D S) (interpOf O P D S) M0 cd N) r.base := by
  have hw := wf_star (defs D S) (interpOf O P D S) M0 cd hM0 hN hu
  exact no_good_model_of_unfold_on sound hty (okCall O P D S) hAccept hr hcheck hkeeps hfacts _
    (goodOn_star hO hty hS hPF hP hdis hE cd hM0 hN hu)

end Equations

end Inox.Bridge
