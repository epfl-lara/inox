/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.NoModel
import Inox.Fresh

/-!
# Fresh-symbol rules on the assumptions of a proof

The lemmas of `Inox/Fresh.lean` are about the terms of SMT-LIB that Logos evaluates. This module
lifts them to the terms that Logos reads from a proof, and to `Satisfies` of `Inox/NoModel.lean`:
a model of a list of assumptions extends to a model of the list with the clauses that introduce a
fresh symbol (`Define`, plain and guarded, the root literal, a hypothesis literal, and the clauses
of an activation literal, `Enables`) appended, and so a model of the assumptions of a script
extends to one of the script with all its fresh-symbol clauses.

The lemmas of `Inox/Fresh.lean` need that the operands of these clauses evaluate to Booleans and
that a definition evaluates to a canonical value of the sort of its symbol. Logos proves both, from
the static types of terms, as `type_preservation`, `model_eval_canonical` and
`bool_value_canonical`, but in its proofs, which take hours to build. They are a hypothesis here,
`LogosTyping`, as the soundness of Logos is in `Inox/Correct.lean`; `Inox/Closed.lean` discharges
it. What a step requires of its clauses is then a static condition, which a check on terms decides:
each clause has the SMT-LIB type `Bool`, as Logos requires of the assumptions of a proof.
-/

namespace Inox.Extend

open Eo
open SmtEval
open Smtm
open Inox.Fresh

/-- Evaluation preserves static types, and gives canonical values, and the values of type `Bool`
are the Booleans: `type_preservation` and `model_eval_canonical` of `Cpc/Proofs`, and
`bool_value_canonical`. -/
def LogosTyping : Prop :=
  (∀ (M : SmtModel) (t : SmtTerm), model_wf M → __smtx_typeof t ≠ SmtType.None →
      __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t ∧
        __smtx_value_canonical M.usortDom (__smtx_model_eval M t) = true) ∧
    ∀ v : SmtValue, __smtx_typeof_value v = SmtType.Bool → ∃ b, v = SmtValue.Boolean b

/-! ## The clauses, as Logos reads them -/

@[simp] theorem eo_to_smt_mkEq (a b : Term) :
    __eo_to_smt (mkEq a b) = SmtTerm.eq (__eo_to_smt a) (__eo_to_smt b) := rfl
@[simp] theorem eo_to_smt_mkImp (a b : Term) :
    __eo_to_smt (mkImp a b) = SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b) := rfl
@[simp] theorem eo_to_smt_mkAnd (a b : Term) :
    __eo_to_smt (mkAnd a b) = SmtTerm.and (__eo_to_smt a) (__eo_to_smt b) := rfl

/-! ## Static types -/

theorem typeof_eq_bool {x y : SmtTerm} (h : __smtx_typeof (SmtTerm.eq x y) = SmtType.Bool) :
    __smtx_typeof y = __smtx_typeof x ∧ __smtx_typeof x ≠ SmtType.None := by
  simp only [__smtx_typeof, __smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq] at h
  by_cases h1 : __smtx_typeof x = SmtType.None
  · simp [h1] at h
  · by_cases h2 : __smtx_typeof x = __smtx_typeof y
    · exact ⟨h2.symm, h1⟩
    · simp [h1, h2] at h

theorem typeof_imp_bool {x y : SmtTerm} (h : __smtx_typeof (SmtTerm.imp x y) = SmtType.Bool) :
    __smtx_typeof x = SmtType.Bool ∧ __smtx_typeof y = SmtType.Bool := by
  simp only [__smtx_typeof, native_ite, native_Teq] at h
  by_cases h1 : __smtx_typeof x = SmtType.Bool <;> by_cases h2 : __smtx_typeof y = SmtType.Bool <;>
    simp_all

theorem typeof_and_bool {x y : SmtTerm} (h : __smtx_typeof (SmtTerm.and x y) = SmtType.Bool) :
    __smtx_typeof x = SmtType.Bool ∧ __smtx_typeof y = SmtType.Bool := by
  simp only [__smtx_typeof, native_ite, native_Teq] at h
  by_cases h1 : __smtx_typeof x = SmtType.Bool <;> by_cases h2 : __smtx_typeof y = SmtType.Bool <;>
    simp_all

/-- A constant has the sort it is declared with, if it has a type at all. -/
theorem typeof_uconst {s : native_String} {T : SmtType}
    (h : __smtx_typeof (SmtTerm.UConst s T) ≠ SmtType.None) :
    __smtx_typeof (SmtTerm.UConst s T) = T := by
  simp only [__smtx_typeof, __smtx_typeof_guard_wf, native_ite] at h ⊢
  split <;> simp_all

theorem uconst_bool {s : native_String} {T : SmtType}
    (h : __smtx_typeof (SmtTerm.UConst s T) = SmtType.Bool) : T = SmtType.Bool := by
  rw [← h]
  exact (typeof_uconst (by rw [h]; simp)).symm

theorem eval_bool (hty : LogosTyping) {M : SmtModel} (hwf : model_wf M) {t : SmtTerm}
    (h : __smtx_typeof t = SmtType.Bool) : ∃ b, __smtx_model_eval M t = SmtValue.Boolean b := by
  apply hty.2
  rw [(hty.1 M t hwf (by rw [h]; simp)).1, h]

/-! ## Extending a model -/

/-- A model of `assums` in which a constant they do not mention is reinterpreted, by a canonical
value of its sort, is a model of `assums` and of the clauses `new` that hold in it. -/
theorem satisfies_setConst {M : SmtModel} {assums : List Term} (hsat : Satisfies M assums)
    {s : native_String} {T : SmtType} (hs : Unreserved s)
    (hfresh : ∀ a ∈ assums, mentions s T (__eo_to_smt a) = false) {v : SmtValue}
    (hty : __smtx_typeof_value v = T) (hcan : __smtx_value_canonical M.usortDom v = true)
    {new : List Term}
    (hnew : ∀ t ∈ new,
      __smtx_model_eval (setConst s T M v) (__eo_to_smt t) = SmtValue.Boolean true) :
    Satisfies (setConst s T M v) (assums ++ new) := by
  refine ⟨wf_setConst hsat.1 hty hcan, fun t ht => ?_⟩
  rcases List.mem_append.mp ht with ht | ht
  · rw [eval_setConst hs M v _ (hfresh t ht)]
    exact hsat.2 t ht
  · exact hnew t ht

/-- `M'` is `M`, or `M` with the constant that `c` translates to reinterpreted. -/
def Reinterprets (c : Term) (M M' : SmtModel) : Prop :=
  M' = M ∨ ∃ s T v, __eo_to_smt c = SmtTerm.UConst s T ∧ M' = setConst s T M v

section Rules

variable (hty : LogosTyping) {M : SmtModel} {assums : List Term} (hsat : Satisfies M assums)
  {c : Term} {s : native_String} {T : SmtType} (hc : __eo_to_smt c = SmtTerm.UConst s T)
  (hs : Unreserved s) (hfresh : ∀ a ∈ assums, mentions s T (__eo_to_smt a) = false)
include hty hsat hc hs hfresh

/-- `Define`: `(= c rhs)`, for a fresh constant `c` that `rhs` does not mention. -/
theorem define_extends {rhs : Term} (hrhs : mentions s T (__eo_to_smt rhs) = false)
    (hbool : __smtx_typeof (__eo_to_smt (mkEq c rhs)) = SmtType.Bool) :
    ∃ M', Satisfies M' (assums ++ [mkEq c rhs]) ∧ Reinterprets c M M' := by
  rw [eo_to_smt_mkEq, hc] at hbool
  obtain ⟨hr, hne⟩ := typeof_eq_bool hbool
  rw [typeof_uconst hne] at hr hne
  obtain ⟨hv, hcan⟩ := hty.1 M _ hsat.1 (by rw [hr]; exact hne)
  rw [hr] at hv
  refine ⟨_, satisfies_setConst hsat hs hfresh hv hcan ?_, Or.inr ⟨_, _, _, hc, rfl⟩⟩
  intro t ht
  rw [List.mem_singleton.mp ht, eo_to_smt_mkEq, hc]
  exact (define_sat (cs := []) hs hsat.1 (by simp) hrhs hv hcan).2.2

/-- Guarded `Define`: `(=> g (= c rhs))`, for a fresh constant `c` that `g` and `rhs` do not
mention. -/
theorem define_guarded_extends {g rhs : Term} (hg : mentions s T (__eo_to_smt g) = false)
    (hrhs : mentions s T (__eo_to_smt rhs) = false)
    (hbool : __smtx_typeof (__eo_to_smt (mkImp g (mkEq c rhs))) = SmtType.Bool) :
    ∃ M', Satisfies M' (assums ++ [mkImp g (mkEq c rhs)]) ∧ Reinterprets c M M' := by
  rw [eo_to_smt_mkImp, eo_to_smt_mkEq, hc] at hbool
  obtain ⟨hgb, heqb⟩ := typeof_imp_bool hbool
  obtain ⟨hr, hne⟩ := typeof_eq_bool heqb
  rw [typeof_uconst hne] at hr hne
  obtain ⟨hv, hcan⟩ := hty.1 M _ hsat.1 (by rw [hr]; exact hne)
  rw [hr] at hv
  refine ⟨_, satisfies_setConst hsat hs hfresh hv hcan ?_, Or.inr ⟨_, _, _, hc, rfl⟩⟩
  intro t ht
  rw [List.mem_singleton.mp ht, eo_to_smt_mkImp, eo_to_smt_mkEq, hc]
  exact (define_guarded_sat (cs := []) hs hsat.1 (by simp) hrhs hv hcan hg
    (eval_bool hty hsat.1 hgb)).2.2

omit hty in
/-- The root literal: `c`, for a fresh constant `c`. -/
theorem root_extends (hbool : __smtx_typeof (__eo_to_smt c) = SmtType.Bool) :
    ∃ M', Satisfies M' (assums ++ [c]) ∧ Reinterprets c M M' := by
  rw [hc] at hbool
  have hT := uconst_bool hbool
  subst hT
  refine ⟨_, satisfies_setConst hsat hs hfresh (v := SmtValue.Boolean true)
    (by simp [__smtx_typeof_value]) (by simp [__smtx_value_canonical]) ?_,
    Or.inr ⟨_, _, _, hc, rfl⟩⟩
  intro t ht
  rw [List.mem_singleton.mp ht, hc]
  exact eval_setConst_self M _

/-- A hypothesis literal: `(=> (and c a) f)`, for a fresh constant `c` that `a` and `f` do not
mention. -/
theorem hypothesis_extends {a f : Term} (ha : mentions s T (__eo_to_smt a) = false)
    (hf : mentions s T (__eo_to_smt f) = false)
    (hbool : __smtx_typeof (__eo_to_smt (mkImp (mkAnd c a) f)) = SmtType.Bool) :
    ∃ M', Satisfies M' (assums ++ [mkImp (mkAnd c a) f]) ∧ Reinterprets c M M' := by
  rw [eo_to_smt_mkImp, eo_to_smt_mkAnd, hc] at hbool
  obtain ⟨hand, hfb⟩ := typeof_imp_bool hbool
  obtain ⟨hcb, hab⟩ := typeof_and_bool hand
  have hT := uconst_bool hcb
  subst hT
  refine ⟨_, satisfies_setConst hsat hs hfresh (v := SmtValue.Boolean false)
    (by simp [__smtx_typeof_value]) (by simp [__smtx_value_canonical]) ?_,
    Or.inr ⟨_, _, _, hc, rfl⟩⟩
  intro t ht
  rw [List.mem_singleton.mp ht, eo_to_smt_mkImp, eo_to_smt_mkAnd, hc]
  exact (hypothesis_sat (cs := []) hs hsat.1 (by simp) ha hf (eval_bool hty hsat.1 hab)
    (eval_bool hty hsat.1 hfb)).2.2

/-- `Enables`: `(=> b c)` for each blocker `b` of `bs`, for a fresh constant `c` that the blockers
do not mention. The model makes `c` their disjunction, so there `c` holds only if one of them
does. -/
theorem enables_extends {bs : List Term}
    (hbs : ∀ b ∈ bs, mentions s T (__eo_to_smt b) = false)
    (hbool : ∀ b ∈ bs, __smtx_typeof (__eo_to_smt (mkImp b c)) = SmtType.Bool) :
    ∃ M', Satisfies M' (assums ++ bs.map fun b => mkImp b c) ∧ Reinterprets c M M' ∧
      (bs ≠ [] → __smtx_model_eval M' (__eo_to_smt c) = SmtValue.Boolean true →
        ∃ b ∈ bs, __smtx_model_eval M' (__eo_to_smt b) = SmtValue.Boolean true) := by
  cases bs with
  | nil => exact ⟨M, by simpa using hsat, Or.inl rfl, fun h => absurd rfl h⟩
  | cons b0 bs0 =>
    have h0 := hbool b0 List.mem_cons_self
    rw [eo_to_smt_mkImp, hc] at h0
    have hT := uconst_bool (typeof_imp_bool h0).2
    subst hT
    have hall := enables_sat (cs := []) (bs := (b0 :: bs0).map __eo_to_smt) hs hsat.1 (by simp)
      (by
        intro b hb
        obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
        refine ⟨hbs b' hb', eval_bool hty hsat.1 ?_⟩
        have h := hbool b' hb'
        rw [eo_to_smt_mkImp, hc] at h
        exact (typeof_imp_bool h).1)
    refine ⟨_, satisfies_setConst hsat hs hfresh
      (v := SmtValue.Boolean
        (((b0 :: bs0).map __eo_to_smt).any fun b => __smtx_model_eval M b == SmtValue.Boolean true))
      (by simp [__smtx_typeof_value]) (by simp [__smtx_value_canonical]) ?_,
      Or.inr ⟨_, _, _, hc, rfl⟩, ?_⟩
    · intro t ht
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
      rw [eo_to_smt_mkImp, hc]
      exact hall.2.2 _ (List.mem_map_of_mem hb)
    · intro _ hcv
      rw [hc, eval_setConst_self] at hcv
      obtain ⟨t, ht, hte⟩ := List.any_eq_true.mp (SmtValue.Boolean.inj hcv)
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
      refine ⟨b, hb, ?_⟩
      rw [eval_setConst hs M _ _ (hbs b hb)]
      simpa using hte

end Rules

/-! ## Sequences of steps -/

namespace Step

/-- The step introduces a fresh constant and can follow `assums`: its constant translates to a
constant whose name Logos does not reserve, that neither `assums` nor the other terms of the step
mention, and its clauses have type `Bool`. The name and the sort are those of the translation of
the constant, so the condition is decided by computing that translation. -/
def Fresh (st : Step) (assums : List Term) : Prop :=
  st.isFact = false ∧ ∃ s T, __eo_to_smt st.const = SmtTerm.UConst s T ∧ Unreserved s ∧
    (∀ a ∈ assums, mentions s T (__eo_to_smt a) = false) ∧
    (∀ t ∈ st.parts, mentions s T (__eo_to_smt t) = false) ∧
    ∀ t ∈ st.clauses, __smtx_typeof (__eo_to_smt t) = SmtType.Bool

/-- What the model of a step's clauses also has: the constant of an `Enables` step holds only if
one of its blockers does, when it has blockers. The clauses `(=> b c)` don't say so, but the model
that makes `c` the disjunction of the blockers does, and the later steps keep it. -/
def Only (st : Step) (M : SmtModel) : Prop :=
  match st with
  | enables c bs => bs ≠ [] → __smtx_model_eval M (__eo_to_smt c) = SmtValue.Boolean true →
      ∃ b ∈ bs, __smtx_model_eval M (__eo_to_smt b) = SmtValue.Boolean true
  | _ => True

/-- Reinterpreting a constant that the clauses of a step don't mention keeps `Only` of it. -/
theorem only_setConst {st : Step} {assums : List Term} (hsub : ∀ t ∈ st.clauses, t ∈ assums)
    {s : native_String} {T : SmtType} (hs : Unreserved s)
    (hfresh : ∀ a ∈ assums, mentions s T (__eo_to_smt a) = false) {M : SmtModel} (v : SmtValue)
    (h : st.Only M) : st.Only (setConst s T M v) := by
  cases st
  case enables c bs =>
    intro hne hcv
    have hm : ∀ b ∈ bs, mentions s T (__eo_to_smt b) = false ∧
        mentions s T (__eo_to_smt c) = false := by
      intro b hb
      have := hfresh _ (hsub (mkImp b c) (List.mem_map_of_mem hb))
      simpa [mentions] using this
    obtain ⟨b0, hb0⟩ := List.exists_mem_of_ne_nil bs hne
    rw [eval_setConst hs M v _ (hm b0 hb0).2] at hcv
    obtain ⟨b, hb, hbv⟩ := h hne hcv
    exact ⟨b, hb, by rw [eval_setConst hs M v _ (hm b hb).1]; exact hbv⟩
  all_goals trivial

/-- A model of `assums` extends to a model of `assums` and the clauses of a step that can follow
them, by reinterpreting the step's constant, in which the step's constant holds only as `Only`
says. -/
theorem extends_reinterprets (hty : LogosTyping) {st : Step} {assums : List Term}
    (hst : st.Fresh assums) {M : SmtModel} (hsat : Satisfies M assums) :
    ∃ M', Satisfies M' (assums ++ st.clauses) ∧ Reinterprets st.const M M' ∧ st.Only M' := by
  obtain ⟨hnf, s, T, hc, hs, hfresh, hparts, hbool⟩ := hst
  cases st <;> simp only [isFact, const, parts, clauses, Only] at hnf hc hparts hbool ⊢
  case define c rhs =>
    simpa using define_extends hty hsat hc hs hfresh (hparts rhs (by simp)) (hbool _ (by simp))
  case defineGuarded c g rhs =>
    simpa using define_guarded_extends hty hsat hc hs hfresh (hparts g (by simp))
      (hparts rhs (by simp)) (hbool _ (by simp))
  case root c => simpa using root_extends hsat hc hs hfresh (hbool _ (by simp))
  case hypothesis c a f =>
    simpa using hypothesis_extends hty hsat hc hs hfresh (hparts a (by simp))
      (hparts f (by simp)) (hbool _ (by simp))
  case enables c bs =>
    exact enables_extends hty hsat hc hs hfresh hparts
      (fun b hb => hbool _ (List.mem_map_of_mem hb))
  case fact => exact absurd hnf (by simp)

/-- A model of `assums` extends to a model of `assums` and the clauses of a step that can follow
them. -/
theorem extends_ (hty : LogosTyping) {st : Step} {assums : List Term} (hst : st.Fresh assums)
    {M : SmtModel} (hsat : Satisfies M assums) : ∃ M', Satisfies M' (assums ++ st.clauses) :=
  let ⟨M', h, _⟩ := extends_reinterprets hty hst hsat
  ⟨M', h⟩

end Step

/-- Each step of `sts` can follow `assums` and the clauses of the steps before it. -/
def StepsFresh : List Term → List Step → Prop
  | _, [] => True
  | assums, st :: sts => st.Fresh assums ∧ StepsFresh (assums ++ st.clauses) sts

/-! ## Facts, and the models a program selects

Some rules are facts about the semantics rather than definitions: they hold in the models that
interpret the program as it defines its functions, and the free variables as a solution of the
query. A predicate `Good` stands for these models. A fact can follow clauses when it holds in
every model of them that `Good` selects, and a fresh constant when reinterpreting it keeps the
models that `Good` selects, as it does when `Good` only depends on the program's symbols and the
constant is not one of them. -/

/-- Reinterpreting the constant `s` of sort `T` keeps the models that `Good` selects. -/
def Keeps (Good : SmtModel → Prop) (s : native_String) (T : SmtType) : Prop :=
  ∀ M v, Good M → Good (setConst s T M v)

/-- Reinterpreting the constant that `c` translates to keeps the models that `Good` selects. -/
def KeepsConst (Good : SmtModel → Prop) (c : Term) : Prop :=
  ∀ s T, __eo_to_smt c = SmtTerm.UConst s T → Keeps Good s T

/-- Every model that `Good` selects and that satisfies `assums` makes `t` true: the side
condition of a fact. -/
def Holds (Good : SmtModel → Prop) (assums : List Term) (t : Term) : Prop :=
  ∀ M, Good M → Satisfies M assums →
    __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean true

theorem good_of_reinterprets {Good : SmtModel → Prop} {c : Term} (hk : KeepsConst Good c)
    {M M' : SmtModel} (hM : Good M) (hr : Reinterprets c M M') : Good M' := by
  rcases hr with rfl | ⟨s, T, v, hc, rfl⟩
  · exact hM
  · exact hk s T hc M v hM

namespace Step

/-- The step can follow `assums` among the models that `Good` selects: a fact holds in each of
them that satisfies `assums`, and a fresh constant is fresh and its reinterpretation keeps them. -/
def Ok (Good : SmtModel → Prop) (st : Step) (assums : List Term) : Prop :=
  match st with
  | fact t => Holds Good assums t
  | _ => st.Fresh assums ∧ KeepsConst Good st.const

/-- A model of `assums` that `Good` selects extends to one of `assums` and the clauses of a step
that can follow them. -/
theorem extends_good (hty : LogosTyping) {Good : SmtModel → Prop} {st : Step}
    {assums : List Term} (hst : st.Ok Good assums) {M : SmtModel} (hgood : Good M)
    (hsat : Satisfies M assums) : ∃ M', Good M' ∧ Satisfies M' (assums ++ st.clauses) := by
  cases st
  case fact t =>
    refine ⟨M, hgood, hsat.1, fun u hu => ?_⟩
    rcases List.mem_append.mp hu with hu | hu
    · exact hsat.2 u hu
    · rw [List.mem_singleton.mp hu]
      exact hst M hgood hsat
  all_goals
    obtain ⟨hf, hk⟩ := hst
    obtain ⟨M', hM', hr, _⟩ := extends_reinterprets hty hf hsat
    exact ⟨M', good_of_reinterprets hk hgood hr, hM'⟩

/-- `extends_good`, with what the extended model also has: `Only` of the step, and of each step
before it, whose clauses are among `assums`, that the model had it of. -/
theorem extends_good_only (hty : LogosTyping) {Good : SmtModel → Prop} {st : Step}
    {assums : List Term} (hst : st.Ok Good assums) {M : SmtModel} (hgood : Good M)
    (hsat : Satisfies M assums) :
    ∃ M', Good M' ∧ Satisfies M' (assums ++ st.clauses) ∧ st.Only M' ∧
      ∀ st0 : Step, (∀ t ∈ st0.clauses, t ∈ assums) → st0.Only M → st0.Only M' := by
  by_cases hfact : st.isFact = true
  · cases st <;> simp only [isFact, Bool.false_eq_true] at hfact
    case fact t =>
      refine ⟨M, hgood, ⟨hsat.1, fun u hu => ?_⟩, trivial, fun _ _ h => h⟩
      rcases List.mem_append.mp hu with hu | hu
      · exact hsat.2 u hu
      · rw [List.mem_singleton.mp hu]
        exact hst M hgood hsat
  · have hst' : st.Fresh assums ∧ KeepsConst Good st.const := by
      cases st <;> first | exact hst | exact absurd rfl hfact
    obtain ⟨hf, hk⟩ := hst'
    obtain ⟨M', hM', hr, ho⟩ := extends_reinterprets hty hf hsat
    refine ⟨M', good_of_reinterprets hk hgood hr, hM', ho, fun st0 hsub h0 => ?_⟩
    obtain ⟨_, s, T, hc, hs, hfresh, _⟩ := hf
    rcases hr with rfl | ⟨s', T', v, hc', rfl⟩
    · exact h0
    · rw [hc] at hc'
      cases hc'
      exact only_setConst hsub hs hfresh v h0

end Step

/-- Each step of `sts` can follow `assums` and the clauses of the steps before it, among the
models that `Good` selects. -/
def StepsOk (Good : SmtModel → Prop) : List Term → List Step → Prop
  | _, [] => True
  | assums, st :: sts => st.Ok Good assums ∧ StepsOk Good (assums ++ st.clauses) sts

/-- A model of the base assumptions that `Good` selects extends to one of them and of the
clauses of steps that can follow them. -/
theorem extend_sat_good (hty : LogosTyping) (Good : SmtModel → Prop) :
    ∀ (sts : List Step) (assums : List Term), StepsOk Good assums sts →
      ∀ M, Good M → Satisfies M assums → ∃ M', Good M' ∧ Satisfies M' (extend assums sts)
  | [], _, _, M, hgood, hsat => ⟨M, hgood, hsat⟩
  | st :: sts, assums, ⟨hst, hsts⟩, M, hgood, hsat => by
    obtain ⟨M', hgood', hM'⟩ := st.extends_good hty hst hgood hsat
    exact extend_sat_good hty Good sts (assums ++ st.clauses) hsts M' hgood' hM'

/-- `extend_sat_good`, with `Only` of each step in the extended model. -/
theorem extend_sat_only (hty : LogosTyping) (Good : SmtModel → Prop) :
    ∀ (sts : List Step) (assums : List Term) (done : List Step), StepsOk Good assums sts →
      ∀ M, Good M → Satisfies M assums →
        (∀ st ∈ done, (∀ t ∈ st.clauses, t ∈ assums) ∧ st.Only M) →
        ∃ M', Good M' ∧ Satisfies M' (extend assums sts) ∧ ∀ st ∈ done ++ sts, st.Only M'
  | [], _, _, _, M, hgood, hsat, hdone =>
    ⟨M, hgood, hsat, fun st h => (hdone st (by simpa using h)).2⟩
  | st :: sts, assums, done, ⟨hst, hsts⟩, M, hgood, hsat, hdone => by
    obtain ⟨M', hgood', hM', ho, hkeep⟩ := st.extends_good_only hty hst hgood hsat
    obtain ⟨M'', hg, hs, hall⟩ := extend_sat_only hty Good sts (assums ++ st.clauses)
      (done ++ [st]) hsts M' hgood' hM' (by
        intro st0 h0
        rcases List.mem_append.mp h0 with h0 | h0
        · exact ⟨fun t ht => List.mem_append_left _ ((hdone st0 h0).1 t ht),
            hkeep st0 (hdone st0 h0).1 (hdone st0 h0).2⟩
        · rw [List.mem_singleton.mp h0]
          exact ⟨fun t ht => List.mem_append_right _ ht, ho⟩)
    exact ⟨M'', hg, hs, fun st0 h0 => hall st0 (by simpa using h0)⟩

/-- So if no model that `Good` selects satisfies the assumptions with the clauses of the steps,
none satisfies the assumptions alone. -/
theorem no_model_of_extend_good (hty : LogosTyping) {Good : SmtModel → Prop}
    {assums : List Term} {sts : List Step} (hsts : StepsOk Good assums sts)
    (hno : ∀ M, Good M → ¬ Satisfies M (extend assums sts)) :
    ∀ M, Good M → ¬ Satisfies M assums := by
  intro M hgood hsat
  obtain ⟨M', hgood', hM'⟩ := extend_sat_good hty Good sts assums hsts M hgood hsat
  exact hno M' hgood' hM'

/-- Fresh steps are steps that can follow among all models. -/
theorem stepsOk_true_of_stepsFresh :
    ∀ {assums : List Term} {sts : List Step}, StepsFresh assums sts →
      StepsOk (fun _ => True) assums sts
  | _, [], _ => trivial
  | _, st :: _, ⟨hst, hsts⟩ => by
    refine ⟨?_, stepsOk_true_of_stepsFresh hsts⟩
    cases st
    case fact => exact absurd hst.1 (by simp [Step.isFact])
    all_goals exact ⟨hst, fun _ _ _ _ _ _ => trivial⟩

/-- Any model of the base assumptions extends to a model of them and of the clauses of steps that
can follow them, each introducing a fresh symbol: `extend_sat_good` where every model is good. -/
theorem extend_sat (hty : LogosTyping) (sts : List Step) (assums : List Term)
    (hsts : StepsFresh assums sts) (M : SmtModel) (hsat : Satisfies M assums) :
    ∃ M', Satisfies M' (extend assums sts) :=
  let ⟨M', _, h⟩ := extend_sat_good hty (fun _ => True) sts assums
    (stepsOk_true_of_stepsFresh hsts) M trivial hsat
  ⟨M', h⟩

/-- So if the assumptions with the clauses of fresh-symbol steps have no model, the assumptions
alone have none. -/
theorem no_model_of_extend (hty : LogosTyping) {assums : List Term} {sts : List Step}
    (hsts : StepsFresh assums sts) (hno : ∀ M, ¬ Satisfies M (extend assums sts)) :
    ∀ M, ¬ Satisfies M assums := by
  intro M hsat
  obtain ⟨M', hM'⟩ := extend_sat hty sts assums hsts M hsat
  exact hno M' hM'

end Inox.Extend
