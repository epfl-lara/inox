/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Instances

/-!
# The intended model of a program, over an abstract interpretation of its functions

The model in which the definitions of a program hold, built from:

* a signature `P`, the functions of the program: the constant each defines, with its sort, its
  parameters and the sort of its result;
* `interp d vs`, the result of the function `d` on the values `vs` of its parameters, an arbitrary
  function: the README's bridge instantiates it with the result of the generated evaluator, `v`
  when `call … = Ok v`;
* a model `M0`, for the sorts and the function values that the program doesn't define, and a model
  `N`, for the constants that it doesn't define (the free variables of the query);
* `Codes`, identifiers of the model's function values for the partial applications of the
  functions of the program.

A constant that a function of the program defines is interpreted by that function: by `interp`
when it has no parameters, and by the function value that codes its application to no values
otherwise. Applying the function value that codes `d` applied to `vs` to one more value applies
`d` to it: another such function value while some parameters remain, and `interp` once none do.
Where `interp` doesn't give a canonical value of the expected sort (the evaluation is stuck, out
of fuel, or ill-typed), the model falls back to `N` or `M0`, so that it is a model for any
`interp` (`wf_star`): which calls `interp` gives a value for is what `GoodOn` (Relative.lean)
relativizes the equations of a program to.
-/

namespace Inox.Model

open Eo
open SmtEval
open Smtm

/-- A function of the program: the constant `name` of sort `ty`, which it defines, its parameters,
and the sort of its result. -/
structure Def where
  name : native_String
  ty : SmtType
  params : List (native_String × SmtType)
  ret : SmtType

/-- The function of `P` that the constant `s` of sort `T` names, if it names one: the first. -/
def lookup (P : List Def) (s : native_String) (T : SmtType) : Option Def :=
  P.find? fun d => d.name == s && d.ty == T

theorem lookup_spec {P : List Def} {s : native_String} {T : SmtType} {d : Def}
    (h : lookup P s T = some d) : d ∈ P ∧ d.name = s ∧ d.ty = T := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨hm, hp.1, hp.2⟩

/-- The function type from the types of `ps` to `R`. -/
def arrow : List (native_String × SmtType) → SmtType → SmtType
  | [], R => R
  | p :: ps, R => .FunType p.2 (arrow ps R)

/-- Identifiers for the partial applications of the functions of the program, as function values
of the model: an injection into the non-zero identifiers. One exists, since there are as many
identifiers (reals) as constants, sorts and lists of values, but that is not proved here: the
theorems below take it as a hypothesis. -/
structure Codes where
  code : native_String → SmtType → List SmtValue → ModelId
  inj : ∀ {s T vs s' T' vs'}, code s T vs = code s' T' vs' → s = s' ∧ T = T' ∧ vs = vs'
  ne : ∀ s T vs, code s T vs ≠ 0

open Classical in
/-- The partial application that an identifier codes, if it codes one. -/
noncomputable def Codes.decode (cd : Codes) (fid : ModelId) :
    Option (native_String × SmtType × List SmtValue) :=
  if h : ∃ p : native_String × SmtType × List SmtValue, cd.code p.1 p.2.1 p.2.2 = fid then
    some h.choose else none

theorem Codes.decode_code (cd : Codes) (s : native_String) (T : SmtType) (vs : List SmtValue) :
    cd.decode (cd.code s T vs) = some (s, T, vs) := by
  have h : ∃ p : native_String × SmtType × List SmtValue,
      cd.code p.1 p.2.1 p.2.2 = cd.code s T vs := ⟨(s, T, vs), rfl⟩
  simp only [Codes.decode, h, reduceDIte]
  obtain ⟨h1, h2, h3⟩ := cd.inj h.choose_spec
  exact congrArg some (Prod.ext h1 (Prod.ext h2 h3))

section Model

variable (P : List Def) (interp : Def → List SmtValue → SmtValue) (M0 : SmtModel) (cd : Codes)

/-- The function value of `d` applied to `vs`, fewer values than it has parameters. -/
def funVal (d : Def) (vs : List SmtValue) : SmtValue :=
  match d.params.drop vs.length with
  | p :: rest => .Fun (cd.code d.name d.ty vs) p.2 (arrow rest d.ret)
  | [] => .NotValue

open Classical in
/-- `v` if it is a canonical value of sort `T`, and otherwise `fb`. -/
noncomputable def typedOr (T : SmtType) (v fb : SmtValue) : SmtValue :=
  if __smtx_typeof_value v = T ∧ __smtx_value_canonical M0.usortDom v = true then v else fb

/-- The application of `d`, applied to `vs`, to one more value `i`. -/
def applied (d : Def) (vs : List SmtValue) (i : SmtValue) : SmtValue :=
  if vs.length + 1 < d.params.length then funVal cd d (vs ++ [i]) else interp d (vs ++ [i])

/-- The function values of the intended model: those that code a partial application of a function
of the program apply it, as `applied` does; the others are those of `M0`. -/
noncomputable def fns (fid : ModelId) (A B : SmtType) (i : SmtValue) : SmtValue :=
  match cd.decode fid with
  | some (s, T, vs) =>
    match lookup P s T with
    | some d => typedOr M0 B (applied interp cd d vs i) (M0.nativeFuns fid A B i)
    | none => M0.nativeFuns fid A B i
  | none => M0.nativeFuns fid A B i

/-- The value of the constant that `d` defines. -/
def defVal (d : Def) : SmtValue :=
  if d.params = [] then interp d [] else funVal cd d []

/-- The intended model, over the values of `N` for the constants that the program doesn't define:
the constants and the functions of the program are interpreted by `interp`. -/
noncomputable def star (N : SmtModel) : SmtModel where
  values := fun k =>
    if k.isVar then N.values k else
    match lookup P k.name k.ty with
    | some d => typedOr M0 k.ty (defVal interp cd d) (N.values k)
    | none => N.values k
  nativeFuns := fns P interp M0 cd
  usortDom := M0.usortDom

theorem typedOr_typed {T : SmtType} {v fb : SmtValue}
    (hfb : __smtx_typeof_value fb = T ∧ __smtx_value_canonical M0.usortDom fb = true) :
    __smtx_typeof_value (typedOr M0 T v fb) = T ∧
      __smtx_value_canonical M0.usortDom (typedOr M0 T v fb) = true := by
  unfold typedOr; split
  · assumption
  · exact hfb

theorem typedOr_of {T : SmtType} {v fb : SmtValue}
    (h : __smtx_typeof_value v = T ∧ __smtx_value_canonical M0.usortDom v = true) :
    typedOr M0 T v fb = v := by
  unfold typedOr; simp only [h, and_self, ↓reduceIte]

/-- The intended model is a model, whatever `interp` is. -/
theorem wf_star (hwf : model_wf M0) {N : SmtModel} (hN : model_wf N)
    (hu : N.usortDom = M0.usortDom) : model_wf (star P interp M0 cd N) := by
  obtain ⟨h1, h2, h3, h4⟩ := hwf
  obtain ⟨n1, n2, _, _⟩ := hN
  rw [hu] at n2
  refine ⟨?_, ?_, ?_, h4⟩
  · intro isVar s T hT
    simp only [star]
    split
    · exact n1 _ _ _ hT
    · split
      · exact (typedOr_typed M0 ⟨n1 _ _ _ hT, n2 _ _ _ hT⟩).1
      · exact n1 _ _ _ hT
  · intro isVar s T hT
    simp only [star]
    split
    · exact n2 _ _ _ hT
    · split
      · exact (typedOr_typed M0 ⟨n1 _ _ _ hT, n2 _ _ _ hT⟩).2
      · exact n2 _ _ _ hT
  · intro fid A B i hT hi
    have hM := h3 fid A B i hT hi
    simp only [native_eval_fun_apply, model_fun_lookup] at hM ⊢
    by_cases h : fid = native_default_fun_id
    · simp only [h, ↓reduceIte] at hM ⊢; exact hM
    · simp only [h, ↓reduceIte] at hM ⊢
      simp only [star, fns]
      split
      · split
        · exact typedOr_typed M0 hM
        · exact hM
      · exact hM

/-- The function value that codes `d` applied to `vs` applies `d`, when that gives a canonical
value of the expected sort. -/
theorem fns_code {d : Def} (hd : lookup P d.name d.ty = some d) (vs : List SmtValue)
    (A B : SmtType) (i : SmtValue)
    (h : __smtx_typeof_value (applied interp cd d vs i) = B ∧
      __smtx_value_canonical M0.usortDom (applied interp cd d vs i) = true) :
    fns P interp M0 cd (cd.code d.name d.ty vs) A B i = applied interp cd d vs i := by
  simp only [fns, Codes.decode_code, hd]
  exact typedOr_of M0 h

/-- A constant that `d` defines is interpreted by `d`, when that gives a canonical value of its
sort. -/
theorem star_def (N : SmtModel) {k : SmtModelKey} (hk : k.isVar = false) {d : Def}
    (hd : lookup P k.name k.ty = some d)
    (h : __smtx_typeof_value (defVal interp cd d) = k.ty ∧
      __smtx_value_canonical M0.usortDom (defVal interp cd d) = true) :
    (star P interp M0 cd N).values k = defVal interp cd d := by
  simp only [star, hk, hd, Bool.false_eq_true, ↓reduceIte]
  exact typedOr_of M0 h

/-- The constants that the program doesn't define keep their values in `N`. -/
theorem star_undef (N : SmtModel) {k : SmtModelKey} (hd : lookup P k.name k.ty = none) :
    (star P interp M0 cd N).values k = N.values k := by
  simp only [star, hd]; split <;> rfl

end Model

end Inox.Model
