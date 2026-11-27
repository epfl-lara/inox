/- Copyright 2009-2026 EPFL, Lausanne -/
import Cpc.SmtModel
import Inox.Terms

/-!
# Fresh symbols preserve satisfiability

Inox introduces fresh constants in its certificates: a defined symbol (`Define`), the activation
literal of a function unfolding (`Enables`), and the literals of the root and of the hypotheses.
This module shows, in the model theory of Logos, that adding the constraints that introduce such a
symbol to a satisfiable set of constraints that do not mention it keeps the set satisfiable.

The key fact is coincidence: the value of a term only depends on the interpretation of the
constants it mentions. Besides the constants written in a term, its value depends on a few
reserved constants that Logos uses to interpret partial operators (division by zero,
out-of-bounds `seq.nth`, selectors applied to the wrong constructor), named `@div_by_zero`,
`@mod_by_zero`, `@qdiv_by_zero`, `@oob_seq_nth` and `@wrong_apply_sel_n_m`. A fresh symbol is
therefore required not to start like one of them. The names Logos gives the constants of a proof,
`@u.i` and `@c.i`, never do.
-/

namespace Inox.Fresh

open SmtEval
open Smtm

/-- The constants of a proof, `Term.UConst i T`, are named `@u.i` by Logos. -/
theorem unreserved_uconst_id (i : native_Nat) : Unreserved (native_uconst_id i) := by
  simp [Unreserved, native_uconst_id, native_string_lit, reservedPrefixes]

/-- The constants `@const`, named `@c.i` by Logos. -/
theorem unreserved_const_id (i : native_Nat) : Unreserved (native_const_id i) := by
  simp [Unreserved, native_const_id, native_string_lit, reservedPrefixes]

/-- The model `M` with the constant `s` of sort `T` interpreted as `v`. -/
def setConst (s : native_String) (T : SmtType) (M : SmtModel) (v : SmtValue) : SmtModel :=
  { M with values := fun k => if k = model_key s T then v else M.values k }

section Coincidence

variable {s : native_String} {T : SmtType}

@[simp] theorem setConst_usortDom (M : SmtModel) (v : SmtValue) :
    (setConst s T M v).usortDom = M.usortDom := rfl

theorem push_setConst (M : SmtModel) (v : SmtValue) (s' : native_String) (T' : SmtType)
    (w : SmtValue) :
    native_model_push (setConst s T M v) s' T' w = setConst s T (native_model_push M s' T' w) v := by
  simp only [native_model_push, setConst]
  congr 1
  funext k
  by_cases h1 : k = { isVar := true, name := s', ty := T' }
  · subst h1
    simp [model_key]
  · simp [h1]

@[simp] theorem setConst_var (M : SmtModel) (v : SmtValue) (s' : native_String) (T' : SmtType) :
    (setConst s T M v).values { isVar := true, name := s', ty := T' } =
      M.values { isVar := true, name := s', ty := T' } := by
  simp [setConst, model_key]

theorem model_eval_apply_setConst (M : SmtModel) (v : SmtValue) :
    __smtx_model_eval_apply (setConst s T M v) = __smtx_model_eval_apply M := rfl

theorem map_diff_setConst (M : SmtModel) (v : SmtValue) :
    __smtx_map_diff (setConst s T M v) = __smtx_map_diff M := rfl

theorem lookup_setConst_reserved (hs : Unreserved s) {r : native_String}
    (hr : r.take 2 ∈ reservedPrefixes) (M : SmtModel) (v : SmtValue) (U : SmtType) :
    native_model_lookup (setConst s T M v) r U = native_model_lookup M r U := by
  have hne : model_key r U ≠ model_key s T := by
    intro h
    cases h
    exact hs hr
  simp [native_model_lookup, setConst, hne]

theorem head_div : native_div_by_zero_id.take 2 ∈ reservedPrefixes := by decide
theorem head_mod : native_mod_by_zero_id.take 2 ∈ reservedPrefixes := by decide
theorem head_qdiv : native_qdiv_by_zero_id.take 2 ∈ reservedPrefixes := by decide
theorem head_oob : native_oob_seq_nth_id.take 2 ∈ reservedPrefixes := by decide
theorem head_wrong_sel (n m : native_Nat) :
    (native_wrong_apply_sel_id n m).take 2 ∈ reservedPrefixes := by
  simp [native_wrong_apply_sel_id, native_string_lit, reservedPrefixes]

theorem seq_nth_setConst (hs : Unreserved s) (M : SmtModel) (v : SmtValue) :
    __smtx_seq_nth (setConst s T M v) = __smtx_seq_nth M := by
  funext a b
  unfold __smtx_seq_nth __smtx_seq_nth_wrong
  simp only [lookup_setConst_reserved hs head_oob]

theorem dt_sel_setConst (hs : Unreserved s) (M : SmtModel) (v : SmtValue) :
    __smtx_model_eval_dt_sel (setConst s T M v) = __smtx_model_eval_dt_sel M := by
  funext c dd n m a
  simp only [__smtx_model_eval_dt_sel, lookup_setConst_reserved hs (head_wrong_sel n m),
    model_eval_apply_setConst]

/-- Coincidence: the value of a term does not depend on the interpretation of a constant it does
not mention, unless the name of that constant is reserved by Logos. -/
theorem eval_setConst (hs : Unreserved s) (M : SmtModel) (v : SmtValue) (t : SmtTerm)
    (hm : mentions s T t = false) :
    __smtx_model_eval (setConst s T M v) t = __smtx_model_eval M t := by
  cases t
  case Apply f x =>
    simp only [mentions, Bool.or_eq_false_iff] at hm
    have ihf := eval_setConst hs M v f hm.1
    have ihx := eval_setConst hs M v x hm.2
    cases f <;> (try simp only [__smtx_model_eval, model_eval_apply_setConst] at ihf) <;>
      simp only [__smtx_model_eval, ihf, ihx, model_eval_apply_setConst, dt_sel_setConst hs]
  case UConst s' T' =>
    simp only [mentions, Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hm
    simp only [__smtx_model_eval, native_model_lookup, setConst, model_key,
      SmtModelKey.mk.injEq, true_and]
    rcases hm with h | h <;> simp [h]
  case «forall» s' T' b =>
    simp only [mentions] at hm
    simp only [__smtx_model_eval]
    split_ifs with h1 h2 h2 <;>
      simp only [setConst_usortDom, push_setConst, eval_setConst hs _ _ _ hm] at h1 <;>
      first | rfl | exact absurd h1 h2 | exact absurd h2 h1
  all_goals
    classical
    simp only [mentions, Bool.or_eq_false_iff] at hm
    simp only [__smtx_model_eval, native_model_var_lookup, setConst_var, push_setConst,
      model_eval_apply_setConst, map_diff_setConst, seq_nth_setConst hs,
      lookup_setConst_reserved hs head_div,
      lookup_setConst_reserved hs head_mod, lookup_setConst_reserved hs head_qdiv,
      eval_setConst hs, hm, setConst_usortDom]
  -- `choice`: the two sides only differ in their decidability instances.
  all_goals congr
termination_by structural t

/-- Coincidence, for two models that agree everywhere except on the constant `s` of sort `T`. -/
theorem eval_agree (hs : Unreserved s) {M M' : SmtModel}
    (hfuns : M'.nativeFuns = M.nativeFuns) (hdom : M'.usortDom = M.usortDom)
    (hvalues : ∀ k, k ≠ model_key s T → M'.values k = M.values k)
    {t : SmtTerm} (ht : mentions s T t = false) :
    __smtx_model_eval M' t = __smtx_model_eval M t := by
  have hM' : M' = setConst s T M (M'.values (model_key s T)) := by
    cases M'
    simp only [setConst] at *
    subst hfuns hdom
    congr 1
    funext k
    by_cases hk : k = model_key s T
    · simp [hk]
    · simp [hk, hvalues k hk]
  rw [hM']
  exact eval_setConst hs M _ t ht

end Coincidence

/-! ## Adding the constraints of a fresh symbol -/

section Fresh

variable {s : native_String} {T : SmtType}

theorem eval_eq_self (v : SmtValue) : __smtx_model_eval_eq v v = SmtValue.Boolean true := by
  cases v <;> simp [__smtx_model_eval_eq, native_veq]

@[simp] theorem eval_setConst_self (M : SmtModel) (v : SmtValue) :
    __smtx_model_eval (setConst s T M v) (SmtTerm.UConst s T) = v := by
  simp [__smtx_model_eval, native_model_lookup, setConst]

/-- Interpreting a constant by a canonical value of its sort keeps a model well-formed. -/
theorem wf_setConst {M : SmtModel} (hwf : model_wf M) {v : SmtValue}
    (hty : __smtx_typeof_value v = T) (hcan : __smtx_value_canonical M.usortDom v = true) :
    model_wf (setConst s T M v) := by
  obtain ⟨h1, h2, h3, h4⟩ := hwf
  refine ⟨?_, ?_, h3, h4⟩
  · intro isVar s' T' hT
    simp only [setConst]
    split
    · next h =>
      simp only [model_key, SmtModelKey.mk.injEq] at h
      rw [h.2.2]
      exact hty
    · exact h1 _ _ _ hT
  · intro isVar s' T' hT
    simp only [setConst]
    split
    · exact hcan
    · exact h2 _ _ _ hT

theorem wf_setConst_bool {M : SmtModel} (hwf : model_wf M) (b : Bool) :
    model_wf (setConst s SmtType.Bool M (SmtValue.Boolean b)) :=
  wf_setConst hwf (by simp [__smtx_typeof_value]) (by simp [__smtx_value_canonical])

/-- The constraints that hold in a model and do not mention a constant keep holding when the
constant is reinterpreted. -/
theorem holds_setConst (hs : Unreserved s) {M : SmtModel} {cs : List SmtTerm}
    (hcs : ∀ c ∈ cs, mentions s T c = false ∧ __smtx_model_eval M c = SmtValue.Boolean true)
    (v : SmtValue) :
    ∀ c ∈ cs, __smtx_model_eval (setConst s T M v) c = SmtValue.Boolean true := by
  intro c hc
  rw [eval_setConst hs M v c (hcs c hc).1]
  exact (hcs c hc).2

/-- `Define`: a fresh constant `s` of sort `T` can be given the value of its definition `rhs`. -/
theorem define_sat (hs : Unreserved s) {M : SmtModel} (hwf : model_wf M)
    {cs : List SmtTerm}
    (hcs : ∀ c ∈ cs, mentions s T c = false ∧ __smtx_model_eval M c = SmtValue.Boolean true)
    {rhs : SmtTerm} (hrhs : mentions s T rhs = false)
    (hty : __smtx_typeof_value (__smtx_model_eval M rhs) = T)
    (hcan : __smtx_value_canonical M.usortDom (__smtx_model_eval M rhs) = true) :
    model_wf (setConst s T M (__smtx_model_eval M rhs)) ∧
      (∀ c ∈ cs,
        __smtx_model_eval (setConst s T M (__smtx_model_eval M rhs)) c = SmtValue.Boolean true) ∧
      __smtx_model_eval (setConst s T M (__smtx_model_eval M rhs))
          (SmtTerm.eq (SmtTerm.UConst s T) rhs) = SmtValue.Boolean true := by
  refine ⟨wf_setConst hwf hty hcan, holds_setConst hs hcs _, ?_⟩
  have hr := eval_setConst hs M (__smtx_model_eval M rhs) rhs hrhs
  have hl := eval_setConst_self (s := s) (T := T) M (__smtx_model_eval M rhs)
  simp only [__smtx_model_eval] at hl ⊢
  rw [hl, hr]
  exact eval_eq_self _

/-- `Define` under a guard `g`: the definition only needs to hold where `g` does, and `g` needs to
evaluate to a Boolean, as implication is strict in Logos. -/
theorem define_guarded_sat (hs : Unreserved s) {M : SmtModel} (hwf : model_wf M)
    {cs : List SmtTerm}
    (hcs : ∀ c ∈ cs, mentions s T c = false ∧ __smtx_model_eval M c = SmtValue.Boolean true)
    {rhs : SmtTerm} (hrhs : mentions s T rhs = false)
    (hty : __smtx_typeof_value (__smtx_model_eval M rhs) = T)
    (hcan : __smtx_value_canonical M.usortDom (__smtx_model_eval M rhs) = true)
    {g : SmtTerm} (hg : mentions s T g = false) (hgb : ∃ b, __smtx_model_eval M g = SmtValue.Boolean b) :
    model_wf (setConst s T M (__smtx_model_eval M rhs)) ∧
      (∀ c ∈ cs,
        __smtx_model_eval (setConst s T M (__smtx_model_eval M rhs)) c = SmtValue.Boolean true) ∧
      __smtx_model_eval (setConst s T M (__smtx_model_eval M rhs))
          (SmtTerm.imp g (SmtTerm.eq (SmtTerm.UConst s T) rhs)) = SmtValue.Boolean true := by
  obtain ⟨hwf', hcs', heq⟩ := define_sat hs hwf hcs hrhs hty hcan
  refine ⟨hwf', hcs', ?_⟩
  obtain ⟨b, hb⟩ := hgb
  have hg' := eval_setConst hs M (__smtx_model_eval M rhs) g hg
  simp only [__smtx_model_eval] at heq ⊢
  rw [heq, hg', hb]
  cases b <;> rfl

/-- The root literal: a fresh Boolean constant can be made true. -/
theorem root_sat (hs : Unreserved s) {M : SmtModel} (hwf : model_wf M) {cs : List SmtTerm}
    (hcs : ∀ c ∈ cs,
      mentions s SmtType.Bool c = false ∧ __smtx_model_eval M c = SmtValue.Boolean true) :
    model_wf (setConst s SmtType.Bool M (SmtValue.Boolean true)) ∧
      (∀ c ∈ cs,
        __smtx_model_eval (setConst s SmtType.Bool M (SmtValue.Boolean true)) c =
          SmtValue.Boolean true) ∧
      __smtx_model_eval (setConst s SmtType.Bool M (SmtValue.Boolean true))
          (SmtTerm.UConst s SmtType.Bool) = SmtValue.Boolean true :=
  ⟨wf_setConst_bool hwf true, holds_setConst hs hcs _, eval_setConst_self M _⟩

/-- A hypothesis literal `l`: a fresh Boolean constant can be made false, which makes the clause
`(l ∧ c) ⇒ f` hold, provided that `c` and `f` evaluate to Booleans. -/
theorem hypothesis_sat (hs : Unreserved s) {M : SmtModel} (hwf : model_wf M) {cs : List SmtTerm}
    (hcs : ∀ c ∈ cs,
      mentions s SmtType.Bool c = false ∧ __smtx_model_eval M c = SmtValue.Boolean true)
    {c f : SmtTerm} (hc : mentions s SmtType.Bool c = false)
    (hf : mentions s SmtType.Bool f = false)
    (hcb : ∃ b, __smtx_model_eval M c = SmtValue.Boolean b)
    (hfb : ∃ b, __smtx_model_eval M f = SmtValue.Boolean b) :
    model_wf (setConst s SmtType.Bool M (SmtValue.Boolean false)) ∧
      (∀ c ∈ cs,
        __smtx_model_eval (setConst s SmtType.Bool M (SmtValue.Boolean false)) c =
          SmtValue.Boolean true) ∧
      __smtx_model_eval (setConst s SmtType.Bool M (SmtValue.Boolean false))
          (SmtTerm.imp (SmtTerm.and (SmtTerm.UConst s SmtType.Bool) c) f) =
        SmtValue.Boolean true := by
  refine ⟨wf_setConst_bool hwf false, holds_setConst hs hcs _, ?_⟩
  obtain ⟨bc, hbc⟩ := hcb
  obtain ⟨bf, hbf⟩ := hfb
  have hc' := eval_setConst hs M (SmtValue.Boolean false) c hc
  have hf' := eval_setConst hs M (SmtValue.Boolean false) f hf
  have hl := eval_setConst_self (s := s) (T := SmtType.Bool) M (SmtValue.Boolean false)
  simp only [__smtx_model_eval] at hl ⊢
  rw [hl, hc', hf', hbc, hbf]
  cases bc <;> cases bf <;> rfl

/-- The activation literal `t` of an unfolding: a fresh Boolean constant can be made the
disjunction of its blockers `bs`, which makes every clause `b ⇒ t` hold, provided that the
blockers evaluate to Booleans. -/
theorem enables_sat (hs : Unreserved s) {M : SmtModel} (hwf : model_wf M) {cs : List SmtTerm}
    (hcs : ∀ c ∈ cs,
      mentions s SmtType.Bool c = false ∧ __smtx_model_eval M c = SmtValue.Boolean true)
    {bs : List SmtTerm}
    (hbs : ∀ b ∈ bs,
      mentions s SmtType.Bool b = false ∧ ∃ x, __smtx_model_eval M b = SmtValue.Boolean x) :
    let v := SmtValue.Boolean (bs.any fun b => __smtx_model_eval M b == SmtValue.Boolean true)
    model_wf (setConst s SmtType.Bool M v) ∧
      (∀ c ∈ cs, __smtx_model_eval (setConst s SmtType.Bool M v) c = SmtValue.Boolean true) ∧
      ∀ b ∈ bs,
        __smtx_model_eval (setConst s SmtType.Bool M v) (SmtTerm.imp b (SmtTerm.UConst s SmtType.Bool)) =
          SmtValue.Boolean true := by
  intro v
  refine ⟨wf_setConst_bool hwf _, holds_setConst hs hcs _, ?_⟩
  intro b hb
  obtain ⟨hmb, x, hx⟩ := hbs b hb
  have hb' := eval_setConst hs M v b hmb
  have hl := eval_setConst_self (s := s) (T := SmtType.Bool) M v
  simp only [__smtx_model_eval] at hl ⊢
  rw [hl, hb', hx]
  cases x
  · rfl
  · have hany : (bs.any fun b => __smtx_model_eval M b == SmtValue.Boolean true) = true :=
      List.any_eq_true.mpr ⟨b, hb, by simp [hx]⟩
    simp only [v, hany]
    rfl

end Fresh

end Inox.Fresh
