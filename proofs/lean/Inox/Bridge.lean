/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Data
import Inox.Relative
import Cpc.Proofs.TypePreservation.Helpers

/-!
# From the generated semantics to the intended model, on integers and Booleans

The semantics of Inox is `eval` and `call` of `proofs/semantics/Inox/Semantics.lean`, generated
from `semantics.md`. This module ties it to the models that the certificate checker is about, for
the first-order expressions over integers and Booleans (`HasTy`):

- `tr D S Γ e` is the term of Logos of an expression, and `trV` the value of a value;
- `ev`, the agreement theorem: where `eval` gives a value, the term evaluates to it in each model
  whose function constants agree with `call` (`CallsOk`) and whose variable constants agree with
  the environment (`VarsOk`);
- the intended model is `Model.star` with the calls as the interpretation of the functions
  (`interpOf`, well defined by fuel monotonicity, `Inox/Mono.lean`). It agrees with `call` at
  every fuel (`callsOk_star`), and satisfies the defining equations on the arguments where the
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
  | .Plus a b => .plus (tr D S Γ a) (tr D S Γ b)
  | .Minus a b => .neg (tr D S Γ a) (tr D S Γ b)
  | .Times a b => .mult (tr D S Γ a) (tr D S Γ b)
  | .Division a b => .div (tr D S Γ a) (tr D S Γ b)
  | .Remainder a b | .Modulo a b => .mod (tr D S Γ a) (tr D S Γ b)
  | .UMinus a => .uneg (tr D S Γ a)
  | .LessThan a b => .lt (tr D S Γ a) (tr D S Γ b)
  | .GreaterThan a b => .gt (tr D S Γ a) (tr D S Γ b)
  | .LessEquals a b => .leq (tr D S Γ a) (tr D S Γ b)
  | .GreaterEquals a b => .geq (tr D S Γ a) (tr D S Γ b)
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
  | plus _ _ iha ihb | minus _ _ iha ihb | times _ _ iha ihb | div _ _ iha ihb
    | rem _ _ iha ihb | mod _ _ iha ihb =>
    simp only [tr, __smtx_typeof, iha, ihb, trT]; rfl
  | uminus _ ih => simp only [tr, __smtx_typeof, ih, trT]; rfl
  | lt _ _ iha ihb | gt _ _ iha ihb | le _ _ iha ihb | ge _ _ iha ihb =>
    simp only [tr, __smtx_typeof, iha, ihb, trT]; rfl
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
/-- The equality of the models on the values of a type is that of the values. -/
theorem eval_eq_trV {D : List Data} (hD : DataOk D) {x y : Value} {T : Ty} (hx : HasV D x T)
    (hy : HasV D y T) :
    __smtx_model_eval_eq (trV D x) (trV D y) = trV D (.BoolV (decide (x = y))) := by
  have hne : __smtx_typeof_value (trV D x) ≠ .RegLan := by
    rw [(agrees_trV hD default x T hx).1]
    rcases fragTy_cases (hasV_fragTy hx) with rfl | rfl | ⟨d, hd, rfl⟩
    · simp [trT]
    · simp [trT]
    · rw [trT_data hD hd]; simp
  rw [eval_eq_veq hne]
  simp only [native_veq, trV]
  congr 1
  apply decide_eq_decide.mpr
  exact ⟨fun h => trV_inj hD hx hy h, fun h => by rw [h]⟩

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
    rw [value_eq_hasV hO P x T y hxT hyT] at hsame
    cases hsame
    exact eval_eq_trV hS.data hxT hyT
  | plus _ _ iha ihb | minus _ _ iha ihb | times _ _ iha ihb =>
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
    simp only [tr, __smtx_model_eval, haM M hw hc hV, hbM M hw hc hV, trV,
      __smtx_model_eval_plus, __smtx_model_eval__, __smtx_model_eval_mult, native_zplus,
      native_zneg, native_zmult, Int.sub_eq_add_neg]
  | div _ _ iha ihb | rem _ _ iha ihb | mod _ _ iha ihb =>
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
    simp [tr, __smtx_model_eval, haM M hw hc hV, hbM M hw hc hV, trV, __smtx_model_eval_eq,
      native_veq, hj, __smtx_model_eval_ite, __smtx_model_eval_div_total,
      __smtx_model_eval_mod_total, native_div_total, native_mod_total]
  | uminus _ ih =>
    intro env v hE he
    rw [eval] at he
    ok_split he
    rename_i x hx
    obtain ⟨hxT, haM⟩ := ih env _ hE hx
    obtain ⟨i, rfl⟩ := hasV_int hxT
    simp only [arith_neg] at he
    cases he
    refine ⟨trivial, fun M hw hc hV => ?_⟩
    simp only [tr, __smtx_model_eval, haM M hw hc hV, trV, __smtx_model_eval_uneg, native_zneg,
      Int.zero_sub]
  | lt _ _ iha ihb | gt _ _ iha ihb | le _ _ iha ihb | ge _ _ iha ihb =>
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
    simp only [tr, __smtx_model_eval, haM M hw hc hV, hbM M hw hc hV, trV,
      __smtx_model_eval_lt, __smtx_model_eval_leq, __smtx_model_eval_gt, __smtx_model_eval_geq,
      native_zlt, native_zleq]
    all_goals (congr 1; rw [← decide_not]; exact decide_eq_decide.mpr Int.not_lt.symm)
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
    have hv : v = .ADTV c vs := by
      cases P with
      | Program fns cs ss is eq =>
      obtain ⟨hlc, hls⟩ := hPD c d i fs hc
      rw [construct] at he
      simp only [hlc, hls] at he
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
to the values `ws`, if one gives a value, and otherwise no value. -/
noncomputable def interpOf (O : Oracle) (P : Program) (D : List Data) (S : List Sig) (d : Def)
    (ws : List SmtValue) : SmtValue :=
  if h : ∃ v, ∃ s ∈ S, ∃ n,
      (s.toDef D) = d ∧ call O P n s.name [] [] (ws.map (ofSmt D)) = .Ok v then
    trV D h.choose else .NotValue

theorem interpOf_eq {O : Oracle} {P : Program} {S : List Sig} (hP : ProgFrag P) (hS : SigOk D S)
    {s : Sig} (hs : s ∈ S) {n : Int} {ws : List SmtValue} {v : Value}
    (hc : call O P n s.name [] [] (ws.map (ofSmt D)) = .Ok v) : interpOf O P D S (s.toDef D) ws =
        trV D v := by
  have h : ∃ v, ∃ s' ∈ S, ∃ n, (s'.toDef D) = (s.toDef D) ∧
      call O P n s'.name [] [] (ws.map (ofSmt D)) = .Ok v := ⟨v, s, hs, n, rfl, hc⟩
  simp only [interpOf, h, ↓reduceDIte]
  obtain ⟨s', hs', n', hd, hc'⟩ := h.choose_spec
  have := sig_eq_of_name hS.nodup hs' hs (nm_inj (congrArg Def.name hd))
  subst this
  rw [call_ok_unique hP hc' hc]

theorem typed_map {D : List Data} (hD : DataOk D) (M : SmtModel) :
    ∀ {ps : List (Id × Ty)} {vs : List Value}, List.Forall₂ (HasV D) vs (ps.map Prod.snd) →
      List.Forall₂ (Typed M) (ptys D ps) (vs.map (trV D))
  | [], [], _ => .nil
  | _ :: _, _ :: _, .cons h hs => .cons (typed_trV hD M _ h) (typed_map hD M hs)

theorem ofSmt_map {D : List Data} (hD : DataOk D) : ∀ {vs : List Value} {Ts : List Ty},
    List.Forall₂ (HasV D) vs Ts → (vs.map (trV D)).map (ofSmt D) = vs
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    simp only [List.map_cons, ofSmt_trV hD h, ofSmt_map hD hs]

/-- The values of the sorts of the types of the bridge are those of the values of the types. -/
theorem typed_inv {D : List Data} (hD : DataOk D) {M : SmtModel} {ps : List (Id × Ty)}
    (hf : ∀ p ∈ ps, FragTy D p.2) :
    ∀ {ws : List SmtValue}, List.Forall₂ (Typed M) (ptys D ps) ws →
      ∃ vs, List.Forall₂ (HasV D) vs (ps.map Prod.snd) ∧ ws = vs.map (trV D) := by
  induction ps with
  | nil => intro ws h; simp only [ptys, List.map_nil] at h; cases h; exact ⟨[], .nil, rfl⟩
  | cons p ps ih =>
    intro ws h
    simp only [ptys, List.map_cons] at h
    cases h with
    | cons hw hws =>
      obtain ⟨vs, hvs, rfl⟩ := ih (fun q hq => hf q (.tail _ hq)) hws
      obtain ⟨v, hv, rfl⟩ := typed_inv1 hD (hf p (.head _)) hw.1
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

/-- The calls agree with the functions of the intended model. -/
theorem callsOk_star (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hPF : ProgFrag P)
    (hP : ProgTy D S P) (M0 N : SmtModel) (cd : Codes) (n : Int) :
    CallsOk O P D S n (Model.star (defs D S) (interpOf O P D S) M0 cd N) := by
  intro s hs tenv vs v hvs hc
  rw [call_tenv hP hs] at hc
  have hv : HasV D v s.ret := call_ty' hO hty hS hP n s hs [] vs v hvs hc
  have hI : interpOf O P D S (s.toDef D) (vs.map (trV D)) = trV D v :=
    interpOf_eq hPF hS hs (by rw [ofSmt_map hS.data hvs]; exact hc)
  have hlook := lookup_toDef (D := D) hS.nodup hs
  have hlen : vs.length = s.params.length := by simpa using hvs.length_eq
  simp only [__smtx_model_eval, native_model_lookup]
  by_cases hnil : s.params = []
  · have hdp : (s.toDef D).params = [] := by simp [Sig.toDef, ptys, hnil]
    have hvs0 : vs = [] := List.eq_nil_of_length_eq_zero (by rw [hlen, hnil]; rfl)
    subst hvs0
    have hdv : defVal (interpOf O P D S) cd (s.toDef D) = trV D v := by
      simp only [defVal, hdp, ↓reduceIte]; exact hI
    rw [star_def (defs D S) (interpOf O P D S) M0 cd N (k := model_key (nm s.name) (s.toDef D).ty)
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
    have hdv : defVal (interpOf O P D S) cd (s.toDef D) = funVal cd (s.toDef D) [] := by
      simp only [defVal, hdp, ↓reduceIte]
    rw [star_def (defs D S) (interpOf O P D S) M0 cd N (k := model_key (nm s.name) (s.toDef D).ty)
        rfl
      hlook (by
        rw [hdv, hfv]
        show __smtx_typeof_value _ = arrow (s.toDef D).params (s.toDef D).ret ∧ _
        rw [hpar]; exact ⟨rfl, rfl⟩)]
    rw [hdv]
    have := applyAll_funVal (Q := defs D S) (I := interpOf O P D S) (M0 := M0) (N := N) (cd := cd)
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
  rw [eval_eq_trV hD h h]; simp [trV]

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

variable {O : Oracle} {P : Program} {D : List Data} {S : List Sig}

/-- A model where the calls agree, with the constants of the parameters of a function set to
values of their types: it is well-formed, the calls agree in it, and the variables of the function
have the values. -/
theorem bound_model (hS : SigOk D S) {s : Sig} (hs : s ∈ S) {M : SmtModel} (hw : model_wf M)
    (hcalls : ∀ m, CallsOk O P D S m M) {vs : List Value}
    (hvs : List.Forall₂ (HasV D) vs (s.params.map Prod.snd)) :
    model_wf (setConsts M (bindValues (ptys D s.params) (vs.map (trV D)))) ∧
      (∀ m, CallsOk O P D S m (setConsts M (bindValues (ptys D s.params) (vs.map (trV D))))) ∧
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
  · intro m s' hs' tenv us u hus hu
    have := hcalls m s' hs' tenv us u hus hu
    simp only [__smtx_model_eval] at this ⊢
    rw [applyAll_setConsts, lookup_setConsts, hσ s' hs']
    exact this
  · intro bs hbs x T hx w hw
    show native_model_lookup _ (nm x) (trT D T) = trV D w
    rw [lookup_setConsts, bindingOf_var s.params vs bs hbs x T hx w hw]

/-- A well-formed model where the calls agree satisfies the defining equations of the program on
the arguments where the calls give values. -/
theorem goodOn_calls (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hP : ProgTy D S P)
    {eqs : List Equation} (hE : ∀ e ∈ eqs, ∃ s ∈ S, EqFor P D S s e) {M : SmtModel}
    (hw : model_wf M) (hcalls0 : ∀ m, CallsOk O P D S m M) : GoodOn (okCall O P D S) eqs M := by
  intro e he ws hws
  obtain ⟨s, hs, hfor⟩ := hE e he
  obtain ⟨body, hbody, hbty, hpe, hterm⟩ := hfor
  rw [hterm, eval_eq_term]
  refine ⟨eval_eq_bool _ _, fun hok => ?_⟩
  rw [hpe] at hws ⊢
  obtain ⟨vs, hvs, rfl⟩ := typed_inv hS.data (hS.params s hs) hws
  obtain ⟨n, v, hc⟩ := hok s hs ⟨body, hbody, hbty, hpe, hterm⟩ vs hvs rfl
  obtain ⟨hwf', hcalls, hVgen⟩ := bound_model hS hs hw hcalls0 hvs
  have hnd : ((ptys D s.params).map Prod.fst).Nodup := by
    have : (ptys D s.params).map Prod.fst = (s.params.map Prod.fst).map nm := by
      simp [ptys, List.map_map, Function.comp_def]
    rw [this]
    exact (hS.pnodup s hs).map (fun _ _ h => nm_inj h)
  have hlen : (vs.map (trV D)).length = (ptys D s.params).length := by
    simpa [ptys] using hvs.length_eq
  have hl := eval_consts M (ptys D s.params) (vs.map (trV D)) [] hnd hlen (by simp)
  rw [List.nil_append] at hl
  rw [eval_spine _ _ _ rfl, hl, hcalls n s hs [] vs v hvs hc]
  generalize setConsts M (bindValues (ptys D s.params) (vs.map (trV D))) = M' at hwf' hcalls hVgen
  -- the body
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
  rw [hvM _ hwf' (hcalls (n - 1)) hV]
  exact eval_eq_self hS.data hvT

/-- The intended model satisfies the defining equations of the program on the arguments where
the calls give values. -/
theorem goodOn_star (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hPF : ProgFrag P)
    (hP : ProgTy D S P) {eqs : List Equation} (hE : ∀ e ∈ eqs, ∃ s ∈ S, EqFor P D S s e)
    (M0 N : SmtModel) (cd : Codes)
    (hw : model_wf (Model.star (defs D S) (interpOf O P D S) M0 cd N)) :
    GoodOn (okCall O P D S) eqs (Model.star (defs D S) (interpOf O P D S) M0 cd N) :=
  goodOn_calls hO hty hS hP hE hw fun m => callsOk_star hO hty hS hPF hP M0 N cd m

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
    (hPF : ProgFrag P) (hP : ProgTy D S P)
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
    (goodOn_star hO hty hS hPF hP hE M0 N cd hw)

end Equations

end Inox.Bridge
