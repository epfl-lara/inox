/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.RuleSteps

/-!
# Unfoldings of the defining equations of the functions

The facts of a certificate include the clauses of the `Unfold` rules: the clause of a function
call is an instance of the function's definition, guarded by the call's activation literal. This
module proves that such a clause holds in every model of the program's defining equations, and
states what that gives: no well-formed model of the defining equations satisfies the query, given
that the other facts hold in those models.

The defining equations are those of the templates whose source is a function, `(= (f x1 … xn)
body)`, as Logos reads them (`equations` in `Inox/Terms.lean`). A model is `Good` when it
satisfies each of them for all the values of the parameters `x1 … xn` of their sorts:
interpreting the parameters as those values makes the equation true. These models are the
program's: whether a model of the defining equations exists, and that it agrees with Inox's
evaluation, which follows from the functions' termination, is a separate layer that this module
does not cover.

A clause `(=> g s)` is an unfolding (`unfoldB`) when `s` is the defining equation of a function with
terms `u1 … un` for its parameters, `g` is a Boolean, and the equation has no binder. Substituting
terms for the parameters then commutes with evaluation (`eval_subst`): the value of `s` is that of
the equation where each parameter is interpreted as the value of its term, which `Good` makes true.
Only the equality of `s` with the substituted equation matters for soundness; the terms `u1 … un`
are found by matching, which nothing relies on.

Reinterpreting a fresh symbol keeps the `Good` models when the defining equations don't mention it
and it is none of their parameters (`keeps_of_keepsB`), by coincidence.
-/

namespace Inox.Fresh

open SmtEval
open Smtm

/-! ## Interpreting several constants -/

/-- The first binding of the constant `s` of sort `T` in `σ`, if it has one. -/
def bindingOf {α : Type} (σ : List (native_String × SmtType × α)) (s : native_String)
    (T : SmtType) : Option (native_String × SmtType × α) :=
  σ.find? (fun e => e.1 == s && e.2.1 == T)

/-- The model `M` with each constant that `σ` binds interpreted as the value of its first
binding. -/
def setConsts (M : SmtModel) (σ : List (native_String × SmtType × SmtValue)) : SmtModel :=
  { M with values := fun k =>
      if k.isVar then M.values k else
      match bindingOf σ k.name k.ty with
      | some e => e.2.2
      | none => M.values k }

section SetConsts

variable (M : SmtModel) (σ : List (native_String × SmtType × SmtValue))

@[simp] theorem setConsts_usortDom : (setConsts M σ).usortDom = M.usortDom := rfl

@[simp] theorem setConsts_var (s' : native_String) (T' : SmtType) :
    (setConsts M σ).values { isVar := true, name := s', ty := T' } =
      M.values { isVar := true, name := s', ty := T' } := by
  simp [setConsts]

theorem lookup_setConsts (s : native_String) (T : SmtType) :
    native_model_lookup (setConsts M σ) s T =
      match bindingOf σ s T with
      | some e => e.2.2
      | none => native_model_lookup M s T := by
  simp [native_model_lookup, setConsts, model_key]

theorem model_eval_apply_setConsts :
    __smtx_model_eval_apply (setConsts M σ) = __smtx_model_eval_apply M := rfl

theorem map_diff_setConsts : __smtx_map_diff (setConsts M σ) = __smtx_map_diff M := rfl

variable {M σ}

theorem bindingOf_reserved {α : Type} {σ : List (native_String × SmtType × α)}
    (hσ : ∀ e ∈ σ, Unreserved e.1) {r : native_String} (hr : r.take 2 ∈ reservedPrefixes)
    (U : SmtType) : bindingOf σ r U = none := by
  simp only [bindingOf, List.find?_eq_none, Bool.and_eq_true, beq_iff_eq, not_and]
  intro e he h1
  exact absurd (h1 ▸ hr) (hσ e he)

theorem lookup_setConsts_reserved (hσ : ∀ e ∈ σ, Unreserved e.1) {r : native_String}
    (hr : r.take 2 ∈ reservedPrefixes) (U : SmtType) :
    native_model_lookup (setConsts M σ) r U = native_model_lookup M r U := by
  rw [lookup_setConsts, bindingOf_reserved hσ hr]

theorem seq_nth_setConsts (hσ : ∀ e ∈ σ, Unreserved e.1) :
    __smtx_seq_nth (setConsts M σ) = __smtx_seq_nth M := by
  funext a b
  unfold __smtx_seq_nth __smtx_seq_nth_wrong
  simp only [lookup_setConsts_reserved hσ head_oob]

theorem dt_sel_setConsts (hσ : ∀ e ∈ σ, Unreserved e.1) :
    __smtx_model_eval_dt_sel (setConsts M σ) = __smtx_model_eval_dt_sel M := by
  funext c dd n m a
  simp only [__smtx_model_eval_dt_sel, lookup_setConsts_reserved hσ (head_wrong_sel n m),
    model_eval_apply_setConsts]

/-- Interpreting a constant that `σ` doesn't bind commutes with interpreting those it binds. -/
theorem setConsts_setConst {s : native_String} {T : SmtType} (h : bindingOf σ s T = none)
    (v : SmtValue) : setConsts (setConst s T M v) σ = setConst s T (setConsts M σ) v := by
  simp only [setConsts, setConst]
  congr 1
  funext k
  by_cases hk : k = model_key s T
  · subst hk
    simp [model_key, h]
  · by_cases hv : k.isVar <;> simp [hv, hk]

end SetConsts

/-! ## Substitution commutes with evaluation -/

/-- The bindings of `σ` with each term replaced by its value in `M`. -/
noncomputable def bindingValues (M : SmtModel) (σ : List (native_String × SmtType × SmtTerm)) :
    List (native_String × SmtType × SmtValue) :=
  σ.map fun e => (e.1, e.2.1, __smtx_model_eval M e.2.2)

theorem bindingOf_bindingValues (M : SmtModel) (σ : List (native_String × SmtType × SmtTerm))
    (s : native_String) (T : SmtType) :
    bindingOf (bindingValues M σ) s T =
      (bindingOf σ s T).map fun e => (e.1, e.2.1, __smtx_model_eval M e.2.2) := by
  simp only [bindingOf, bindingValues, List.find?_map]
  rfl

theorem eval_apply_plain (M : SmtModel) {f : SmtTerm} (h : plainHead f = true) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.Apply f x) =
      __smtx_model_eval_apply M (__smtx_model_eval M f) (__smtx_model_eval M x) := by
  cases f <;> first | (simp [plainHead] at h; done) | simp only [__smtx_model_eval]

theorem plainHead_substConst {σ : List (native_String × SmtType × SmtTerm)}
    (hσ : ∀ e ∈ σ, plainHead e.2.2 = true) (s : native_String) (T : SmtType) :
    plainHead (substConst σ s T) = true := by
  unfold substConst
  split
  · next e he => exact hσ e (List.mem_of_find?_eq_some he)
  · rfl

/-- Substituting terms for constants, in a term without binders, gives the value of the term where
those constants are interpreted as the values of their terms, provided their names are not
reserved by Logos and no term is a selector or a tester, which Logos evaluates apart when they are
applied. -/
theorem eval_subst {σ : List (native_String × SmtType × SmtTerm)}
    (hσ : ∀ e ∈ σ, Unreserved e.1 ∧ plainHead e.2.2 = true) (M : SmtModel) (t : SmtTerm)
    (hb : noBinder t = true) :
    __smtx_model_eval M (substSmt σ t) =
      __smtx_model_eval (setConsts M (bindingValues M σ)) t := by
  have hu : ∀ e ∈ bindingValues M σ, Unreserved e.1 := by
    intro e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact (hσ e' he').1
  cases t
  case UConst s T =>
    simp only [substSmt, __smtx_model_eval, lookup_setConsts, bindingOf_bindingValues]
    simp only [substConst, bindingOf]
    cases h : List.find? (fun e => e.1 == s && e.2.1 == T) σ <;>
      simp [__smtx_model_eval, native_model_lookup]
  case Apply f x =>
    simp only [noBinder, Bool.and_eq_true] at hb
    have ihf := eval_subst hσ M f hb.1
    have ihx := eval_subst hσ M x hb.2
    cases f
    case UConst s T =>
      simp only [substSmt] at ihf ⊢
      rw [eval_apply_plain M (plainHead_substConst (fun e he => (hσ e he).2) s T), ihf, ihx]
      simp only [__smtx_model_eval, model_eval_apply_setConsts]
    all_goals
      simp only [substSmt] at ihf ⊢
      (try simp only [__smtx_model_eval, model_eval_apply_setConsts] at ihf)
      simp only [__smtx_model_eval, ihf, ihx, model_eval_apply_setConsts, dt_sel_setConsts hu]
  case «forall» => simp [noBinder] at hb
  case «exists» => simp [noBinder] at hb
  case choice => simp [noBinder] at hb
  case bind => simp [noBinder] at hb
  all_goals
    simp only [noBinder, Bool.and_eq_true] at hb
    simp only [substSmt, __smtx_model_eval, native_model_var_lookup, setConsts_var,
      model_eval_apply_setConsts, map_diff_setConsts, seq_nth_setConsts hu,
      lookup_setConsts_reserved hu head_div,
      lookup_setConsts_reserved hu head_mod, lookup_setConsts_reserved hu head_qdiv,
      eval_subst hσ M, hb]
termination_by structural t

end Inox.Fresh

namespace Inox

open Logos (Sexp)
open Eo
open SmtEval
open Smtm
open Inox.Fresh
open Inox.Extend

/-! ## The models of the defining equations -/

/-- The value `v` can be that of the parameter `p` in `M`: a canonical value of its sort. -/
def Typed (M : SmtModel) (p : native_String × SmtType) (v : SmtValue) : Prop :=
  __smtx_typeof_value v = p.2 ∧ __smtx_value_canonical M.usortDom v = true

/-- The bindings of the parameters `ps` to the values `vs`. -/
def bindValues (ps : List (native_String × SmtType)) (vs : List SmtValue) :
    List (native_String × SmtType × SmtValue) :=
  List.zipWith (fun p v => (p.1, p.2, v)) ps vs

/-- `M` satisfies each of the defining equations `eqs` for all the values of its parameters. -/
def Good (eqs : List Equation) (M : SmtModel) : Prop :=
  ∀ e ∈ eqs, ∀ vs, List.Forall₂ (Typed M) e.params vs →
    __smtx_model_eval (setConsts M (bindValues e.params vs)) (__eo_to_smt e.term) =
      SmtValue.Boolean true

/-! ## Fresh symbols keep them -/

theorem bindingOf_bindValues {ps : List (native_String × SmtType)} {s : native_String}
    {T : SmtType} (h : ps.contains (s, T) = false) (vs : List SmtValue) :
    bindingOf (bindValues ps vs) s T = none := by
  induction ps generalizing vs with
  | nil => rfl
  | cons p ps ih =>
    cases vs with
    | nil => rfl
    | cons v vs =>
      simp only [List.contains_cons, Bool.or_eq_false_iff] at h
      simp only [bindValues, List.zipWith_cons_cons, bindingOf, List.find?_cons] at ih ⊢
      have hp : (p.1 == s && p.2 == T) = false := by
        obtain ⟨p1, p2⟩ := p
        simp only [beq_eq_false_iff_ne, ne_eq, Prod.mk.injEq, not_and] at h
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
        by_cases h1 : p1 = s
        · exact Or.inr (h.1 h1.symm ∘ Eq.symm)
        · exact Or.inl h1
      rw [hp]
      exact ih h.2 vs

/-- Reinterpreting a constant that `keepsB` accepts keeps the models of the defining equations. -/
theorem keeps_of_keepsB {eqs : List Equation} {s : native_String} {T : SmtType}
    (h : keepsB eqs s T = true) : Keeps (Good eqs) s T := by
  simp only [keepsB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
    Bool.and_eq_true] at h
  obtain ⟨hs, he⟩ := h
  intro M v hM e hmem vs hvs
  obtain ⟨hm, hp⟩ := he e hmem
  rw [setConsts_setConst (bindingOf_bindValues (by simpa using hp) vs),
    eval_setConst hs _ v _ (by simpa using hm)]
  exact hM e hmem vs hvs

/-! ## Unfoldings hold in them -/

theorem bindingValues_bindParams (M : SmtModel) :
    ∀ (ps : List (native_String × SmtType)) (us : List SmtTerm),
      bindingValues M (bindParams ps us) = bindValues ps (us.map (__smtx_model_eval M))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: ps, _ :: us => by
    have ih := bindingValues_bindParams M ps us
    simp only [bindParams, bindValues, bindingValues] at ih ⊢
    simp only [List.zipWith_cons_cons, List.map_cons, ih]

/-- What `paramsB` gives: the terms can replace the parameters, and their values in a
well-formed model are typed. -/
theorem params_of_paramsB (hty : LogosTyping) {M : SmtModel} (hwf : model_wf M) :
    ∀ {ps : List (native_String × SmtType)} {us : List SmtTerm}, paramsB ps us = true →
      (∀ e ∈ bindParams ps us, Unreserved e.1 ∧ plainHead e.2.2 = true) ∧
        List.Forall₂ (Typed M) ps (us.map (__smtx_model_eval M))
  | [], [], _ => ⟨by simp [bindParams], List.Forall₂.nil⟩
  | _ :: _, [], h => by simp [paramsB] at h
  | [], _ :: _, h => by simp [paramsB] at h
  | p :: ps, u :: us, h => by
    simp only [paramsB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hs, hT⟩, hu⟩, hplain⟩, hrest⟩ := h
    obtain ⟨ih1, ih2⟩ := params_of_paramsB hty hwf hrest
    refine ⟨?_, ?_⟩
    · intro e he
      simp only [bindParams, List.zipWith_cons_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨hs, hplain⟩
      · exact ih1 e he
    · refine List.Forall₂.cons ?_ ih2
      have := hty.1 M u hwf (by rw [hu]; exact hT)
      exact ⟨this.1.trans hu, this.2⟩

theorem eval_imp_true (hty : LogosTyping) {M : SmtModel} (hwf : model_wf M) {g : SmtTerm}
    (hg : __smtx_typeof g = SmtType.Bool) :
    __smtx_model_eval_imp (__smtx_model_eval M g) (SmtValue.Boolean true) =
      SmtValue.Boolean true := by
  obtain ⟨b, hb⟩ := eval_bool hty hwf hg
  rw [hb]
  cases b <;> simp [__smtx_model_eval_imp, __smtx_model_eval_or, __smtx_model_eval_not,
    SmtEval.native_not, SmtEval.native_or]

/-- An instance of a defining equation, guarded by a Boolean, holds in the models of the
equations, whatever the clauses before it. -/
theorem holds_unfold (hty : LogosTyping) {eqs : List Equation} {c : Term}
    (h : unfoldB eqs c = true) (assums : List Term) : Holds (Good eqs) assums c := by
  intro M hM hsat
  unfold unfoldB at h
  split at h
  · next g s heq =>
    obtain ⟨e, he, hinst⟩ := List.any_eq_true.mp h
    split at hinst
    · next us _ =>
      simp only [instB, Bool.and_eq_true, decide_eq_true_eq] at hinst
      obtain ⟨⟨⟨hparams, hb⟩, hg⟩, hsubst⟩ := hinst
      obtain ⟨hσ, htyped⟩ := params_of_paramsB hty hsat.1 hparams
      rw [heq]
      simp only [__smtx_model_eval]
      rw [← hsubst, eval_subst hσ M _ hb, bindingValues_bindParams,
        hM e he _ htyped]
      exact eval_imp_true hty hsat.1 hg
    · simp at hinst
  · simp at h

/-! ## What the check gives -/

/-- Each fact holds, in the models that `Good` selects, given the clauses before it, unless
`covered` accepts it. -/
def FactsHoldExcept (Good : SmtModel → Prop) (covered : Term → Bool) :
    List Term → List Term → Prop
  | _, [] => True
  | assums, t :: ts =>
    (covered t = true ∨ Holds Good assums t) ∧ FactsHoldExcept Good covered (assums ++ [t]) ts

theorem factsHold_of_except {Good : SmtModel → Prop} {covered : Term → Bool}
    (hcov : ∀ t, covered t = true → ∀ assums, Holds Good assums t) :
    ∀ {assums ts : List Term}, FactsHoldExcept Good covered assums ts → FactsHold Good assums ts
  | _, [], _ => trivial
  | assums, t :: _, ⟨h1, h2⟩ =>
    ⟨h1.elim (fun h => hcov t h assums) id, factsHold_of_except hcov h2⟩

theorem factsHoldExcept_of_all {Good : SmtModel → Prop} {covered : Term → Bool} :
    ∀ {assums ts : List Term}, ts.all covered = true → FactsHoldExcept Good covered assums ts
  | _, [], _ => trivial
  | _, _ :: _, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact ⟨Or.inl h.1, factsHoldExcept_of_all h.2⟩

theorem keepsConst_of_keeps {r : TermSteps} (h : r.keeps = true) :
    ∀ st ∈ r.fresh, KeepsConst (Good r.equations) st.const := by
  intro st hst s T hc
  have := List.all_eq_true.mp h st hst
  simp only [hc, asConst] at this
  exact keeps_of_keepsB this

/-- If the checker accepts a certificate, the check on terms holds, and no fresh symbol is
mentioned by the defining equations or is one of their parameters (`r.keeps`), then no
well-formed model of the defining equations of the program's functions satisfies the assumptions
of the query, as Logos reads them, given that each fact holds in those models (given the clauses
before it), except the unfoldings of the equations, which `holds_unfold` proves. -/
theorem no_good_model_of_unfold (sound : LogosSound) (hty : LogosTyping)
    {certificate : Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked) (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hkeeps : r.keeps = true)
    (hfacts : FactsHoldExcept (Good r.equations) (unfoldB r.equations) (extend r.base r.fresh)
      r.facts) :
    ∀ M, Good r.equations M → ¬ Satisfies M r.base :=
  no_good_model_of_accept sound hty (Good r.equations) hAccept hr hcheck
    (keepsConst_of_keeps hkeeps)
    (factsHold_of_except (fun _ h => holds_unfold hty h) hfacts)

/-- When every fact is an unfolding, nothing is left to assume of the facts. -/
theorem no_good_model_of_unfoldings (sound : LogosSound) (hty : LogosTyping)
    {certificate : Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked) (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hkeeps : r.keeps = true)
    (hall : r.facts.all (unfoldB r.equations) = true) :
    ∀ M, Good r.equations M → ¬ Satisfies M r.base :=
  no_good_model_of_unfold sound hty hAccept hr hcheck hkeeps (factsHoldExcept_of_all hall)

end Inox
