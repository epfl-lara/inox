/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Unfold
import Inox.Sets

/-!
# The clauses of the instances of templates

An instance of a template, the clauses of an `Unfold` or `Instance` rule taken together, names
local symbols: the conditions of its branches, their blockers, the results of its expressions, the
values of its nested calls and constructors. Each has a meaning, a term over the instance's
arguments (`Inox/Meanings.lean`), and the certificate's terms state it as a definition `(= v D)`:
one more fresh-symbol step for each, which the check (`stepsFreshB`) accepts as any other, so that
a model of the clauses before is extended, simultaneously, to the symbols of the instance.

`TermSteps.instanceFacts` substitutes the definitions that are steps in each clause of the instance
and decides that the result holds in each well-formed model of the defining equations (`verify`),
under the literals that the base clauses and the root steps make known: an implication holds when
its conclusion holds under the literals that its premise makes known, as it is and reduced under the
known literals, a term holds when it reduces to `true` under the known literals (`red`), an instance
of a defining equation holds in their models, as does the conclusion of one whose premise reduces to
`true` (`mpInst`), and an equality holds by congruence (`congB`). The facts that `verify` accepts as
they are hold too (`holds_verified`). This module proves that the clauses that it accepts hold in
the models of the defining equations where the definitions hold (`holds_instanceFact`), which every
model of the clauses before them is, since the definitions are clauses of the fresh-symbol steps:
what the check needs of the facts that it doesn't decide (`no_good_model_of_instances`).
-/

namespace Inox

open Logos (Sexp)
open Eo
open SmtEval
open Smtm
open Inox.Fresh
open Inox.Extend

/-! ## Reducing under known literals -/

/-- The literals `K` have their values in `M`. -/
def KSound (M : SmtModel) (K : List (SmtTerm × Bool)) : Prop :=
  ∀ p ∈ K, __smtx_model_eval M p.1 = SmtValue.Boolean p.2

theorem known_mem : ∀ {K : List (SmtTerm × Bool)} {t : SmtTerm} {b : Bool},
    known K t = some b → (t, b) ∈ K
  | [], _, _, h => by simp [known] at h
  | p :: K, t, b, h => by
    unfold known at h
    split at h
    · next hp => cases h; exact List.mem_cons.mpr (Or.inl (by rw [← hp]))
    · exact List.mem_cons_of_mem _ (known_mem h)

theorem eval_lookupOr {M : SmtModel} {K : List (SmtTerm × Bool)} (hK : KSound M K) {t r : SmtTerm}
    (hr : __smtx_model_eval M r = __smtx_model_eval M t) :
    __smtx_model_eval M (lookupOr K t r) = __smtx_model_eval M t := by
  unfold lookupOr
  split
  · next b hb => rw [hK _ (known_mem hb)]; rfl
  · exact hr

theorem eval_orR (hty : LogosTyping) {M : SmtModel} (hwf : model_wf M) (x y : SmtTerm) :
    __smtx_model_eval M (orR x y) =
      __smtx_model_eval_or (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  unfold orR
  split
  · next h =>
    obtain ⟨b, hb⟩ := eval_bool hty hwf h.2
    rw [h.1, hb]; cases b <;> rfl
  split
  · next h =>
    obtain ⟨b, hb⟩ := eval_bool hty hwf h.2
    rw [h.1, hb]; cases b <;> rfl
  split
  · next h =>
    obtain ⟨b, hb⟩ := eval_bool hty hwf h.2
    rw [h.1, hb]; cases b <;> rfl
  split
  · next h =>
    obtain ⟨b, hb⟩ := eval_bool hty hwf h.2
    rw [h.1, hb]; cases b <;> rfl
  rfl

theorem eval_andR (hty : LogosTyping) {M : SmtModel} (hwf : model_wf M) (x y : SmtTerm) :
    __smtx_model_eval M (andR x y) =
      __smtx_model_eval_and (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  unfold andR
  split
  · next h =>
    obtain ⟨b, hb⟩ := eval_bool hty hwf h.2
    rw [h.1, hb]; cases b <;> rfl
  split
  · next h =>
    obtain ⟨b, hb⟩ := eval_bool hty hwf h.2
    rw [h.1, hb]; cases b <;> rfl
  split
  · next h =>
    obtain ⟨b, hb⟩ := eval_bool hty hwf h.2
    rw [h.1, hb]; cases b <;> rfl
  split
  · next h =>
    obtain ⟨b, hb⟩ := eval_bool hty hwf h.2
    rw [h.1, hb]; cases b <;> rfl
  rfl

/-- Reducing a term under literals that have their values keeps its value. -/
theorem eval_red (hty : LogosTyping) {M : SmtModel} (hwf : model_wf M) {K : List (SmtTerm × Bool)}
    (hK : KSound M K) (t : SmtTerm) : __smtx_model_eval M (red K t) = __smtx_model_eval M t := by
  cases t
  case ite c a b =>
    simp only [red]
    apply eval_lookupOr hK
    have hc := eval_red hty hwf hK c
    split
    · next h => rw [h] at hc; simp only [__smtx_model_eval, ← hc, eval_red hty hwf hK a]; rfl
    · next h => rw [h] at hc; simp only [__smtx_model_eval, ← hc, eval_red hty hwf hK b]; rfl
    · simp only [__smtx_model_eval, hc, eval_red hty hwf hK a, eval_red hty hwf hK b]
  case not x =>
    simp only [red]
    apply eval_lookupOr hK
    have hx := eval_red hty hwf hK x
    split
    · next b h => rw [h] at hx; simp only [__smtx_model_eval, ← hx]; rfl
    · simp only [__smtx_model_eval, hx]
  case or x y =>
    simp only [red]
    apply eval_lookupOr hK
    rw [eval_orR hty hwf, eval_red hty hwf hK x, eval_red hty hwf hK y]; rfl
  case and x y =>
    simp only [red]
    apply eval_lookupOr hK
    rw [eval_andR hty hwf, eval_red hty hwf hK x, eval_red hty hwf hK y]; rfl
  case eq x y =>
    simp only [red]
    apply eval_lookupOr hK
    split
    · next h =>
      have hx := eval_red hty hwf hK x
      have hy := eval_red hty hwf hK y
      rw [h] at hx
      simp only [__smtx_model_eval, ← hx, ← hy, eval_eq_self]
    · simp only [__smtx_model_eval, eval_red hty hwf hK x, eval_red hty hwf hK y]
  all_goals
    simp only [red]
    exact eval_lookupOr hK rfl
termination_by structural t

theorem or_eq_true {x y : SmtValue} (h : __smtx_model_eval_or x y = SmtValue.Boolean true) :
    x = SmtValue.Boolean true ∨ y = SmtValue.Boolean true := by
  unfold __smtx_model_eval_or at h
  split at h <;> simp_all [SmtEval.native_or]

theorem or_eq_false {x y : SmtValue} (h : __smtx_model_eval_or x y = SmtValue.Boolean false) :
    x = SmtValue.Boolean false ∧ y = SmtValue.Boolean false := by
  unfold __smtx_model_eval_or at h
  split at h <;> simp_all [SmtEval.native_or]

theorem and_eq_true' {x y : SmtValue} (h : __smtx_model_eval_and x y = SmtValue.Boolean true) :
    x = SmtValue.Boolean true ∧ y = SmtValue.Boolean true := by
  unfold __smtx_model_eval_and at h
  split at h <;> simp_all [SmtEval.native_and]

theorem not_eq {x : SmtValue} {b : Bool} (h : __smtx_model_eval_not x = SmtValue.Boolean b) :
    x = SmtValue.Boolean (!b) := by
  unfold __smtx_model_eval_not at h
  split at h <;> simp_all [SmtEval.native_not]

/-- A comparison has a value exactly when its opposite has the other one. -/
theorem lt_geq {x y : SmtValue} {b : Bool} (h : __smtx_model_eval_lt x y = SmtValue.Boolean b) :
    __smtx_model_eval_geq x y = SmtValue.Boolean (!b) := by
  unfold __smtx_model_eval_geq __smtx_model_eval_leq
  unfold __smtx_model_eval_lt at h
  split at h <;> simp_all [native_zlt, native_zleq, native_rlt, native_rleq]
  all_goals subst h; simp only [← decide_not, not_lt]

theorem geq_lt {x y : SmtValue} {b : Bool} (h : __smtx_model_eval_geq x y = SmtValue.Boolean b) :
    __smtx_model_eval_lt x y = SmtValue.Boolean (!b) := by
  unfold __smtx_model_eval_lt
  unfold __smtx_model_eval_geq __smtx_model_eval_leq at h
  split at h <;> simp_all [native_zlt, native_zleq, native_rlt, native_rleq]
  all_goals subst h; simp only [← decide_not, not_le]

theorem leq_gt {x y : SmtValue} {b : Bool} (h : __smtx_model_eval_leq x y = SmtValue.Boolean b) :
    __smtx_model_eval_gt x y = SmtValue.Boolean (!b) := by
  unfold __smtx_model_eval_gt __smtx_model_eval_lt
  unfold __smtx_model_eval_leq at h
  split at h <;> simp_all [native_zlt, native_zleq, native_rlt, native_rleq]
  all_goals subst h; simp only [← decide_not, not_le]

theorem gt_leq {x y : SmtValue} {b : Bool} (h : __smtx_model_eval_gt x y = SmtValue.Boolean b) :
    __smtx_model_eval_leq x y = SmtValue.Boolean (!b) := by
  unfold __smtx_model_eval_leq
  unfold __smtx_model_eval_gt __smtx_model_eval_lt at h
  split at h <;> simp_all [native_zlt, native_zleq, native_rlt, native_rleq]
  all_goals subst h; simp only [← decide_not, not_lt]

/-- The literals that a term having a value makes known have their values. -/
theorem lits_sound {M : SmtModel} (t : SmtTerm) (b : Bool)
    (h : __smtx_model_eval M t = SmtValue.Boolean b) : KSound M (lits t b) := by
  intro p hp
  cases t
  case and x y =>
    cases b
    · simp only [lits, List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; exact h
    · simp only [lits, List.mem_cons, List.mem_append] at hp
      simp only [__smtx_model_eval] at h
      have hb := and_eq_true' h
      rcases hp with rfl | hp | hp
      · exact h
      · exact lits_sound x true hb.1 p hp
      · exact lits_sound y true hb.2 p hp
  case or x y =>
    cases b
    · simp only [lits, List.mem_cons, List.mem_append] at hp
      simp only [__smtx_model_eval] at h
      have hb := or_eq_false h
      rcases hp with rfl | hp | hp
      · exact h
      · exact lits_sound x false hb.1 p hp
      · exact lits_sound y false hb.2 p hp
    · simp only [lits, List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; exact h
  case not x =>
    simp only [lits, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h
    · simp only [__smtx_model_eval] at h
      exact lits_sound x (!b) (not_eq h) p hp
  case lt x y =>
    simp only [lits, List.mem_cons, List.not_mem_nil, or_false] at hp
    simp only [__smtx_model_eval] at h
    rcases hp with rfl | rfl
    · simpa [__smtx_model_eval] using h
    · simpa [__smtx_model_eval] using lt_geq h
  case geq x y =>
    simp only [lits, List.mem_cons, List.not_mem_nil, or_false] at hp
    simp only [__smtx_model_eval] at h
    rcases hp with rfl | rfl
    · simpa [__smtx_model_eval] using h
    · simpa [__smtx_model_eval] using geq_lt h
  case leq x y =>
    simp only [lits, List.mem_cons, List.not_mem_nil, or_false] at hp
    simp only [__smtx_model_eval] at h
    rcases hp with rfl | rfl
    · simpa [__smtx_model_eval] using h
    · simpa [__smtx_model_eval] using leq_gt h
  case gt x y =>
    simp only [lits, List.mem_cons, List.not_mem_nil, or_false] at hp
    simp only [__smtx_model_eval] at h
    rcases hp with rfl | rfl
    · simpa [__smtx_model_eval] using h
    · simpa [__smtx_model_eval] using gt_leq h
  all_goals
    simp only [lits, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; exact h
termination_by structural t

theorem kSound_append {M : SmtModel} {K K' : List (SmtTerm × Bool)} (h : KSound M K)
    (h' : KSound M K') : KSound M (K ++ K') := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact h p hp
  · exact h' p hp

/-- The literals that the true disjunctions of `K` make known have their values where those of
`K` do. -/
theorem kSound_unitLits (hty : LogosTyping) {M : SmtModel} (hwf : model_wf M)
    {K : List (SmtTerm × Bool)} (hK : KSound M K) : KSound M (unitLits K) := by
  intro q hq
  simp only [unitLits, List.mem_flatMap] at hq
  obtain ⟨⟨t, b⟩, hp, hq⟩ := hq
  split at hq
  · rename_i x y heq
    cases heq
    have hor := hK _ hp
    simp only [__smtx_model_eval] at hor
    rcases List.mem_append.mp hq with hq | hq
    · split at hq
      · rename_i hx
        have hxv : __smtx_model_eval M x = SmtValue.Boolean false := by
          rw [← eval_red hty hwf hK x, hx]; simp [__smtx_model_eval]
        have hy : __smtx_model_eval M y = SmtValue.Boolean true := by
          rcases or_eq_true hor with h | h
          · rw [hxv] at h; cases h
          · exact h
        rcases List.mem_append.mp hq with hq | hq
        · exact lits_sound _ true (by rw [eval_red hty hwf hK y]; exact hy) q hq
        · exact lits_sound _ true hy q hq
      · cases hq
    · split at hq
      · rename_i hyf
        have hyv : __smtx_model_eval M y = SmtValue.Boolean false := by
          rw [← eval_red hty hwf hK y, hyf]; simp [__smtx_model_eval]
        have hx : __smtx_model_eval M x = SmtValue.Boolean true := by
          rcases or_eq_true hor with h | h
          · exact h
          · rw [hyv] at h; cases h
        rcases List.mem_append.mp hq with hq | hq
        · exact lits_sound _ true (by rw [eval_red hty hwf hK x]; exact hx) q hq
        · exact lits_sound _ true hx q hq
      · cases hq
  · cases hq

theorem kSound_withUnits (hty : LogosTyping) {M : SmtModel} (hwf : model_wf M)
    {K : List (SmtTerm × Bool)} (hK : KSound M K) : KSound M (withUnits K) :=
  kSound_append (kSound_unitLits hty hwf hK) hK

theorem verifyUnder_base (hty : LogosTyping) {M : SmtModel} (hwf : model_wf M)
    {k : List (SmtTerm × Bool) → Bool} {K : List (SmtTerm × Bool)} (hK : KSound M K)
    (p : SmtTerm)
    (hv : (decide (red K p = SmtTerm.Boolean false) ||
      k (withUnits (lits (red K p) true ++ lits p true ++ K))) = true)
    (hp : __smtx_model_eval M p = SmtValue.Boolean true) : ∃ K', KSound M K' ∧ k K' = true := by
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hv
  have hr := eval_red hty hwf hK p
  rcases hv with hv | hv
  · rw [hv, hp] at hr
    simp [__smtx_model_eval] at hr
  · rw [hp] at hr
    exact ⟨_, kSound_withUnits hty hwf
      (kSound_append (kSound_append (lits_sound _ true hr) (lits_sound _ true hp)) hK), hv⟩

/-- When `p` is true, the literals that `verifyUnder` passes to `k`, for one of the disjuncts of
`p`, have their values. -/
theorem verifyUnder_sound (hty : LogosTyping) {M : SmtModel} (hwf : model_wf M)
    {k : List (SmtTerm × Bool) → Bool} {K : List (SmtTerm × Bool)} (hK : KSound M K) :
    ∀ p, verifyUnder k K p = true → __smtx_model_eval M p = SmtValue.Boolean true →
      ∃ K', KSound M K' ∧ k K' = true := by
  intro p hv hp
  cases p
  case or p1 p2 =>
    simp only [verifyUnder, Bool.and_eq_true] at hv
    simp only [__smtx_model_eval] at hp
    rcases or_eq_true hp with h | h
    · exact verifyUnder_sound hty hwf hK p1 hv.1 h
    · exact verifyUnder_sound hty hwf hK p2 hv.2 h
  all_goals
    simp only [verifyUnder] at hv
    exact verifyUnder_base hty hwf hK _ hv hp

/-! ## Congruence, and modus ponens on the defining equations -/

theorem typeof_value_reglan (r : SmtRegLan) :
    __smtx_typeof_value (SmtValue.RegLan r) = SmtType.RegLan := by
  simp [__smtx_typeof_value]

/-- An equality that the literals `K` make known, of terms of a sort other than that of regular
languages, gives them the same value. -/
theorem eval_of_eqKnown (hty : LogosTyping) {M : SmtModel} (hwf : model_wf M)
    {K : List (SmtTerm × Bool)} (hK : KSound M K) {x y : SmtTerm} (h : eqKnown K x y = true) :
    __smtx_model_eval M x = __smtx_model_eval M y := by
  simp only [eqKnown, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hk, hnone⟩, hreg⟩ := h
  have htv := (hty.1 M x hwf hnone).1
  have hnr : ∀ r, __smtx_model_eval M x ≠ SmtValue.RegLan r := by
    intro r hr
    rw [hr, typeof_value_reglan] at htv
    exact hreg htv.symm
  rcases hk with hk | hk
  · have := hK _ (known_mem hk)
    simp only [__smtx_model_eval] at this
    unfold __smtx_model_eval_eq at this
    split at this
    · next r1 r2 h1 _ => exact absurd h1 (hnr r1)
    · simp only [native_veq, SmtValue.Boolean.injEq, decide_eq_true_eq] at this
      exact this
  · have := hK _ (known_mem hk)
    simp only [__smtx_model_eval] at this
    unfold __smtx_model_eval_eq at this
    split at this
    · next r1 r2 _ h2 => exact absurd h2 (hnr r2)
    · simp only [native_veq, SmtValue.Boolean.injEq, decide_eq_true_eq] at this
      exact this.symm

/-- What `congB` accepts has the same value in each well-formed model where the literals `K` have
their values: congruence, which holds in every model, given the equalities of `K`. -/
theorem congB_sound (hty : LogosTyping) {M : SmtModel} (hwf : model_wf M)
    {K : List (SmtTerm × Bool)} (hK : KSound M K) (x : SmtTerm) :
    ∀ y, congB K x y = true → __smtx_model_eval M x = __smtx_model_eval M y := by
  intro y h
  cases x
  case Apply f a =>
    simp only [congB, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with (h | h) | h
    · rw [h]
    · exact eval_of_eqKnown hty hwf hK h
    · split at h
      · next g b =>
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
        obtain ⟨hfg, hab⟩ := h
        have hab' := congB_sound hty hwf hK a b hab
        rcases hfg with hfg | ⟨⟨hf, hg⟩, hfg⟩
        · subst hfg
          cases f <;> simp only [__smtx_model_eval, hab']
        · rw [eval_apply_plain M hf, eval_apply_plain M hg, congB_sound hty hwf hK f g hfg, hab']
      · simp at h
  all_goals
    simp only [congB, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · rw [h]
    · exact eval_of_eqKnown hty hwf hK h
termination_by structural x

/-- The conclusion of an instance of a defining equation `(=> A q)` whose premise reduces to true
under the literals `K` holds in their models where `K` have their values. -/
theorem mpInst_sound (hty : LogosTyping) {eqs : List Equation} {M : SmtModel} (hM : Good eqs M)
    (hwf : model_wf M) {K : List (SmtTerm × Bool)} (hK : KSound M K) {φ : SmtTerm}
    (h : mpInst eqs K φ = true) : __smtx_model_eval M φ = SmtValue.Boolean true := by
  obtain ⟨e, he, h⟩ := List.any_eq_true.mp h
  simp only [mpInstB, Bool.and_eq_true] at h
  obtain ⟨⟨hparams, hb⟩, hm⟩ := h
  obtain ⟨hσ, htyped⟩ := params_of_paramsB hty hwf hparams
  split at hm
  · next a q hs =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
    obtain ⟨hq, ha⟩ := hm
    have heq : __smtx_model_eval M (SmtTerm.imp a q) = SmtValue.Boolean true := by
      rw [← hs, eval_subst hσ M _ hb, bindingValues_bindParams]
      exact hM e he _ htyped
    have ha' : __smtx_model_eval M a = SmtValue.Boolean true := by
      rw [← eval_red hty hwf hK, ha]; rfl
    simp only [__smtx_model_eval, __smtx_model_eval_imp, ha'] at heq
    rcases or_eq_true heq with h | h
    · simp [__smtx_model_eval_not, native_not] at h
    · rw [← hq]; exact h
  · simp at hm

/-! ## Instances of the defining equations -/

/-- An instance of a defining equation holds in their models. -/
theorem eqInst_sound (hty : LogosTyping) {eqs : List Equation} {M : SmtModel} (hM : Good eqs M)
    (hwf : model_wf M) {φ : SmtTerm} (h : eqInst eqs φ = true) :
    __smtx_model_eval M φ = SmtValue.Boolean true := by
  unfold eqInst at h
  split at h
  · next lhs _ =>
    obtain ⟨e, he, hinst⟩ := List.any_eq_true.mp h
    simp only [eqInstB, Bool.and_eq_true, decide_eq_true_eq] at hinst
    obtain ⟨⟨hparams, hb⟩, hsubst⟩ := hinst
    obtain ⟨hσ, htyped⟩ := params_of_paramsB hty hwf hparams
    rw [← hsubst, eval_subst hσ M _ hb, bindingValues_bindParams]
    exact hM e he _ htyped
  · simp at h

/-- The split of a set that the literals `K` make known not to be empty holds where they have
their values. -/
theorem setSplit_sound (hty : LogosTyping) {M : SmtModel} (hwf : model_wf M)
    {K : List (SmtTerm × Bool)} (hK : KSound M K) {φ : SmtTerm} (hv : setSplit K φ = true) :
    __smtx_model_eval M φ = SmtValue.Boolean true := by
  unfold setSplit at hv
  split at hv
  · next _ s c T s' c' =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
    obtain ⟨⟨⟨⟨hs', hc'⟩, hc⟩, hs⟩, hk⟩ := hv
    subst s' c'
    have hne := hK _ (known_mem hk)
    obtain ⟨hvt, hvc⟩ := hty.1 M s hwf (by rw [hs]; simp)
    rw [hs] at hvt
    obtain ⟨m, hm⟩ := set_value_canonical hvt
    rw [hm] at hvt hvc
    have hE : __smtx_model_eval M (SmtTerm.set_empty T) =
        SmtValue.Set (SmtMap.default T (SmtValue.Boolean false)) := by
      rw [__smtx_model_eval.eq_def]
    have hne' : m ≠ SmtMap.default T (SmtValue.Boolean false) := by
      intro h
      simp [__smtx_model_eval, hm, hE, h, __smtx_model_eval_eq, native_veq] at hne
    have hmem := Bridge.choose_mem hwf.2.2.2 hvt hvc hne'
    have hcv : __smtx_model_eval M c =
        native_eval_map_diff M m (SmtMap.default T (SmtValue.Boolean false)) := by
      rw [hc, __smtx_model_eval.eq_def]
      simp only [hm, hE, __smtx_map_diff]
      rfl
    obtain ⟨d, hd, hmem⟩ : ∃ d, __smtx_model_eval M c = d ∧
        __smtx_map_lookup m d = SmtValue.Boolean true := ⟨_, hcv, hmem⟩
    simp only [__smtx_model_eval, hm, hE, hd]
    rw [Bridge.split_eq M.usortDom hvt hvc hmem]
    exact eval_eq_self _
  · simp at hv

theorem verify_base (hty : LogosTyping) {eqs : List Equation} {M : SmtModel} (hM : Good eqs M)
    (hwf : model_wf M) {K : List (SmtTerm × Bool)} (hK : KSound M K) (φ : SmtTerm)
    (hv : (decide (red K φ = SmtTerm.Boolean true) || eqInst eqs φ || mpInst eqs K φ ||
      congEq K φ || setSplit K φ) = true) :
    __smtx_model_eval M φ = SmtValue.Boolean true := by
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hv
  rcases hv with (((hv | hv) | hv) | hv) | hv
  rotate_right
  · exact setSplit_sound hty hwf hK hv
  · rw [← eval_red hty hwf hK, hv]; rfl
  · exact eqInst_sound hty hM hwf hv
  · exact mpInst_sound hty hM hwf hK hv
  · unfold congEq at hv
    split at hv
    · next x y =>
      simp only [__smtx_model_eval]
      rw [congB_sound hty hwf hK x y hv]
      exact eval_eq_self _
    · simp at hv

/-- What `verify` accepts holds in the models of the defining equations where the literals `K`
have their values. -/
theorem verify_sound (hty : LogosTyping) {eqs : List Equation} {M : SmtModel} (hM : Good eqs M)
    (hwf : model_wf M) : ∀ (φ : SmtTerm) {K : List (SmtTerm × Bool)}, KSound M K →
      verify eqs K φ = true → __smtx_model_eval M φ = SmtValue.Boolean true := by
  intro φ K hK hv
  cases φ
  case imp p q =>
    simp only [verify, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨hp, hq⟩, hv⟩ := hv
    simp only [__smtx_model_eval]
    obtain ⟨bp, hbp⟩ := eval_bool hty hwf hp
    obtain ⟨bq, hbq⟩ := eval_bool hty hwf hq
    cases bp
    · rw [hbp, hbq]; cases bq <;> rfl
    · obtain ⟨K', hK', hk⟩ := verifyUnder_sound hty hwf hK p hv hbp
      rw [hbp, verify_sound hty hM hwf q hK' hk]; rfl
  all_goals
    simp only [verify] at hv
    exact verify_base hty hM hwf hK _ hv

/-! ## The definitions of the local symbols -/

/-- A definition that holds gives the constant the value of its term. -/
theorem defBinding_sound (hty : LogosTyping) {M : SmtModel} (hwf : model_wf M) {d : Term}
    {e : native_String × SmtType × SmtTerm} (h : defBinding d = some e)
    (hd : __smtx_model_eval M (__eo_to_smt d) = SmtValue.Boolean true) :
    (Unreserved e.1 ∧ plainHead e.2.2 = true) ∧
      M.values (model_key e.1 e.2.1) = __smtx_model_eval M e.2.2 := by
  unfold defBinding at h
  split at h
  · next v D =>
    split at h
    · next s T hv =>
      split at h
      · next hc =>
        cases h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨hs, hnone⟩, hreg⟩, hplain⟩ := hc
        refine ⟨⟨hs, hplain⟩, ?_⟩
        have hd' : __smtx_model_eval_eq (native_model_lookup M s T)
            (__smtx_model_eval M (__eo_to_smt D)) = SmtValue.Boolean true := by
          have : __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) v) D) =
              SmtTerm.eq (__eo_to_smt v) (__eo_to_smt D) := rfl
          rw [this] at hd
          simp only [__smtx_model_eval, hv] at hd
          exact hd
        have htv := (hty.1 M (SmtTerm.UConst s T) hwf hnone).1
        simp only [__smtx_model_eval] at htv
        unfold __smtx_model_eval_eq at hd'
        split at hd'
        · next r1 r2 h1 _ =>
          rw [h1, typeof_value_reglan] at htv
          exact absurd htv.symm hreg
        · simp only [native_veq, SmtValue.Boolean.injEq, decide_eq_true_eq] at hd'
          exact hd'
      · cases h
    · cases h
  · cases h

/-- A model is unchanged by interpreting constants as the values they have in it. -/
theorem setConsts_self {M : SmtModel} {σ : List (native_String × SmtType × SmtValue)}
    (h : ∀ e ∈ σ, M.values (model_key e.1 e.2.1) = e.2.2) : setConsts M σ = M := by
  simp only [setConsts]
  congr 1
  funext k
  split
  · rfl
  · next hk =>
    split
    · next e he =>
      have hmem := List.mem_of_find?_eq_some he
      have hmatch := List.find?_some he
      simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
      rw [← h e hmem, hmatch.1, hmatch.2]
      cases k
      simp_all [model_key]
    · rfl

/-! ## The clauses of the instances -/

/-- A clause of an instance that `instClauseB` accepts holds in each model of the defining
equations where the definitions that `σ` binds hold. -/
theorem instClause_sound (hty : LogosTyping) {eqs : List Equation} {M : SmtModel}
    (hM : Good eqs M) (hwf : model_wf M) {σ : List (native_String × SmtType × SmtTerm)}
    (hσ : ∀ e ∈ σ, (Unreserved e.1 ∧ plainHead e.2.2 = true) ∧
      M.values (model_key e.1 e.2.1) = __smtx_model_eval M e.2.2)
    {K : List (SmtTerm × Bool)} (hK : KSound M K)
    {c : Term} (h : instClauseB eqs K σ c = true) :
    __smtx_model_eval M (__eo_to_smt c) = SmtValue.Boolean true := by
  simp only [instClauseB, Bool.and_eq_true] at h
  have hself : setConsts M (bindingValues M σ) = M := by
    apply setConsts_self
    intro e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact (hσ e' he').2
  have := eval_subst (fun e he => (hσ e he).1) M _ h.1
  rw [hself] at this
  rw [← this]
  exact verify_sound hty hM hwf _ hK h.2

theorem subset_foldl_append : ∀ (sts : List Step) (acc : List Term),
    acc ⊆ sts.foldl (fun acc st => acc ++ st.clauses) acc
  | [], _ => List.Subset.refl _
  | st :: sts, acc => fun _ hx =>
    subset_foldl_append sts (acc ++ st.clauses) (List.mem_append_left _ hx)

theorem base_subset_extend (base : List Term) (sts : List Step) : base ⊆ extend base sts :=
  subset_foldl_append sts base

/-- The clauses of the steps are among the assumptions that they extend. -/
theorem clause_mem_extend {t : Term} : ∀ {assums : List Term} {sts : List Step} {st : Step},
    st ∈ sts → t ∈ st.clauses → t ∈ extend assums sts
  | _, [], _, h, _ => by cases h
  | assums, st' :: sts, st, h, ht => by
    show t ∈ extend (assums ++ st'.clauses) sts
    rcases List.mem_cons.mp h with rfl | h
    · exact mem_extend (List.mem_append_right _ ht)
    · exact clause_mem_extend h ht

/-- The constants of the root steps are clauses of the fresh-symbol steps. -/
theorem roots_subset_extend (r : TermSteps) : r.roots ⊆ extend r.base r.fresh := by
  intro t ht
  simp only [TermSteps.roots, List.mem_filterMap] at ht
  obtain ⟨st, hst, h⟩ := ht
  cases st <;> simp at h
  subst h
  exact clause_mem_extend hst (by simp [Step.clauses])

/-- The literals that the base clauses and the root steps make known have their values in the
models of the base clauses and of the clauses of the fresh-symbol steps. -/
theorem kSound_baseLits (hty : LogosTyping) {r : TermSteps} {M : SmtModel} (hwf : model_wf M)
    (h : ∀ t ∈ extend r.base r.fresh,
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean true) :
    KSound M r.baseLits := by
  refine kSound_withUnits hty hwf fun p hp => ?_
  simp only [List.mem_flatMap, List.mem_append] at hp
  obtain ⟨t, ht, hp⟩ := hp
  refine lits_sound _ true (h t ?_) p hp
  rcases ht with ht | ht
  · exact base_subset_extend _ _ ht
  · exact roots_subset_extend r ht

/-- The clauses of the instances that the check accepts hold, in the models of the defining
equations, given the base clauses and the clauses of the fresh-symbol steps. -/
theorem holds_instanceFact (hty : LogosTyping) {r : TermSteps} {t : Term}
    (ht : t ∈ r.instanceFacts) {assums : List Term} (hsub : extend r.base r.fresh ⊆ assums) :
    Holds (Good r.equations) assums t := by
  intro M hM hsat
  simp only [TermSteps.instanceFacts, List.mem_flatMap, List.mem_filter] at ht
  obtain ⟨⟨defs, cs⟩, _, _, hc⟩ := ht
  have hK : KSound M r.baseLits :=
    kSound_baseLits hty hsat.1 fun t ht => hsat.2 t (hsub ht)
  refine instClause_sound hty hM hsat.1 ?_ hK hc
  intro e he
  obtain ⟨d, hd, hb⟩ := List.mem_filterMap.mp he
  simp only [List.mem_filter, Std.HashSet.contains_ofList, List.contains_iff_mem] at hd
  exact defBinding_sound hty hsat.1 hb (hsat.2 d (hsub hd.2))

/-- The facts that `verify` accepts as they are hold, in the models of the defining equations,
given the base clauses. -/
theorem holds_verified (hty : LogosTyping) {r : TermSteps} {t : Term} (h : r.verified t = true)
    {assums : List Term} (hsub : extend r.base r.fresh ⊆ assums) :
    Holds (Good r.equations) assums t := by
  intro M hM hsat
  simp only [TermSteps.verified, Bool.and_eq_true] at h
  have hK : KSound M r.baseLits :=
    kSound_baseLits hty hsat.1 fun t ht => hsat.2 t (hsub ht)
  exact verify_sound hty hM hsat.1 _ hK h.2

theorem holds_covered (hty : LogosTyping) {r : TermSteps} {t : Term} (h : r.covered t = true)
    {assums : List Term} (hsub : extend r.base r.fresh ⊆ assums) :
    Holds (Good r.equations) assums t := by
  simp only [TermSteps.covered, Bool.or_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem] at h
  rcases h with (h | h) | h
  · exact holds_unfold hty h assums
  · exact holds_instanceFact hty h hsub
  · exact holds_verified hty h hsub

/-! ## What the check gives -/

theorem factsHold_of_except_sub {Good : SmtModel → Prop} {covered : Term → Bool}
    {ctx : List Term}
    (hcov : ∀ t, covered t = true → ∀ assums, ctx ⊆ assums → Holds Good assums t) :
    ∀ {assums ts : List Term}, ctx ⊆ assums → FactsHoldExcept Good covered assums ts →
      FactsHold Good assums ts
  | _, [], _, _ => trivial
  | assums, t :: _, hsub, ⟨h1, h2⟩ =>
    ⟨h1.elim (fun h => hcov t h assums hsub) id,
      factsHold_of_except_sub hcov (fun _ h => List.mem_append_left _ (hsub h)) h2⟩

/-- If the checker accepts a certificate, the check on terms holds, and the defining equations
don't mention the fresh symbols (`r.keeps`), then no well-formed model of the defining equations
satisfies the assumptions of the query, as Logos reads them, given that each fact holds in those
models (given the clauses before it), except the unfoldings of the equations and the clauses of
the instances of templates that the check accepts (`r.covered`).

The assumptions of the query, `r.base`, are its `check-sat` assumptions, its completeness
assumptions and the source expressions of its assertions, those that mention no fresh symbol. A
source expression is there as `Lowering.Tables.statement` states it: lowered to the syntax of the
session, with the meanings that its `where` gives to its markers in place of the markers, without
its assumptions (`(assume c b)` as `b`) and without the conjuncts that have markers left (and left
out if a marker is left elsewhere). Each is implied by the source expression, given the meanings
of its markers, so that the hypotheses are weaker than the query's assertions. The meanings of the
markers are only checked by the Scala checker (`Sources.scala`), against the clauses of the
templates. -/
theorem no_good_model_of_instances (sound : LogosSound) (hty : LogosTyping)
    {certificate : Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked) (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hkeeps : r.keeps = true)
    (hfacts : FactsHoldExcept (Good r.equations) r.covered (extend r.base r.fresh) r.facts) :
    ∀ M, Good r.equations M → ¬ Satisfies M r.base :=
  no_good_model_of_accept sound hty (Good r.equations) hAccept hr hcheck
    (keepsConst_of_keeps hkeeps)
    (factsHold_of_except_sub (fun _ h _ hsub => holds_covered hty h hsub) (fun _ h => h) hfacts)

/-- When every fact is covered, nothing is left to assume of the facts. -/
theorem no_good_model_of_covered (sound : LogosSound) (hty : LogosTyping)
    {certificate : Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked) (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hkeeps : r.keeps = true)
    (hall : r.facts.all r.covered = true) :
    ∀ M, Good r.equations M → ¬ Satisfies M r.base :=
  no_good_model_of_instances sound hty hAccept hr hcheck hkeeps (factsHoldExcept_of_all hall)

end Inox
