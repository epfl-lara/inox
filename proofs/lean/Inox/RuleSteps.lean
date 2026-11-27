/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Extend

/-!
# The rules of a certificate, on the terms that Logos reads

`Inox.check` compares the clauses of the rules with the asserts of the script as text. This module
reads them as Logos does, as the `Term`s that `Inox/Extend.lean` is about: it writes the proof's
declarations followed by one `assume` per clause (those of the query's assumptions, then those of
each rule in the order of the rules, of the completeness assumptions, of the definitions of local
symbols, and of the source expressions of the assertions), parses that text with `parseProof`, and
makes a step of `Inox.Extend` of each rule:
- a `Define`, a `Hypothesis` and a `Root` introduce their literal, and the `Enables` rules of a
  target together introduce it, as a step whose clauses are one implication per blocker;
- the other rules are facts about the semantics;
- the base clauses, which the models considered satisfy, are the query's assumptions, the source
  expressions and the completeness assumptions, those of the latter two that mention no fresh
  symbol of a rule (the other completeness assumptions are facts, the other source expressions
  are left out);
- an `Enables` clause `(=> b m)` whose blocker has a definition `(= b rhs)` of which `m` is a
  conjunct is no blocker of `m`'s step: it is derived from that definition, after the steps.

The fresh-symbol steps are ordered so that each comes before the clauses that mention its symbol,
and the facts follow them, in the order of the rules: a fact then holds given every definition.
`TermSteps.check` decides that each fresh-symbol step is `Fresh`, given the names of the constants
that the clauses before it mention, that the definition of each derived clause is a clause, and that
every assumption of the real proof, as Logos reads it, is one of the clauses.
`no_good_model_of_accept` states what that gives: no model that `Good` selects satisfies the
assumptions of the query, given that the facts hold in the models that `Good` selects, which is what
the rules state about the semantics, and that `Good` does not depend on the fresh symbols.

The two parses number the constants they declare in the order of the declarations, so the
constants of the proof get the same numbers in both: the text starts with the proof's
declarations, as they are, followed by those of the script that declare names the proof doesn't.
Nothing depends on this for soundness, since the theorem is about the terms of the second parse,
whatever they are; a different numbering would only make the check fail.

The definitions are in `Inox/Terms.lean`, which `inox-check --terms` runs; the theorems are here.
-/

namespace Inox

open Logos (Sexp)
open Eo
open Smtm
open Inox.Fresh
open Inox.Extend

/-! ## The check, on terms -/

theorem termSteps_parse {checked : Checked} {r : TermSteps} (h : termSteps checked = .ok r) :
    ∃ cmds, parseProof checked.proof = .ok (r.assums, cmds) := by
  unfold termSteps at h
  cases hp : parseProof checked.proof with
  | error e => rw [hp] at h; cases h
  | ok p =>
    obtain ⟨assums, cmds⟩ := p
    rw [hp] at h
    refine ⟨cmds, ?_⟩
    dsimp only at h
    split at h
    · cases h
    · revert h
      generalize termStepsOf _ _ = x
      intro h
      cases x with
      | error e => simp [Except.map] at h
      | ok r' =>
        simp only [Except.map, Except.ok.injEq] at h
        subst h; rfl

theorem eq_of_asConst {t : SmtTerm} {s : SmtEval.native_String} {T : SmtType}
    (h : asConst t = some (s, T)) : t = SmtTerm.UConst s T := by
  unfold asConst at h
  split at h
  · cases h; rfl
  · cases h

/-! ### The names of the constants that clauses mention -/

set_option linter.internalConstructors false in
/-- Whether a constant named `x`, of any sort, occurs in a term. -/
def mentionsName (x : SmtEval.native_String) : SmtTerm → Bool
  | .None => false
  | .Boolean _ => false
  | .Numeral _ => false
  | .Rational _ => false
  | .String _ => false
  | .Binary _ _ => false
  | .Apply x1 x2 => mentionsName x x1 || mentionsName x x2
  | .Var _ _ => false
  | .DtCons _ _ _ => false
  | .DtSel _ _ _ _ => false
  | .DtTester _ _ _ => false
  | .UConst s' _ => s' == x
  | .ite x1 x2 x3 => mentionsName x x1 || mentionsName x x2 || mentionsName x x3
  | .not x1 => mentionsName x x1
  | .or x1 x2 => mentionsName x x1 || mentionsName x x2
  | .and x1 x2 => mentionsName x x1 || mentionsName x x2
  | .imp x1 x2 => mentionsName x x1 || mentionsName x x2
  | .xor x1 x2 => mentionsName x x1 || mentionsName x x2
  | .eq x1 x2 => mentionsName x x1 || mentionsName x x2
  | ._at_purify x1 => mentionsName x x1
  | .plus x1 x2 => mentionsName x x1 || mentionsName x x2
  | .neg x1 x2 => mentionsName x x1 || mentionsName x x2
  | .mult x1 x2 => mentionsName x x1 || mentionsName x x2
  | .lt x1 x2 => mentionsName x x1 || mentionsName x x2
  | .leq x1 x2 => mentionsName x x1 || mentionsName x x2
  | .gt x1 x2 => mentionsName x x1 || mentionsName x x2
  | .geq x1 x2 => mentionsName x x1 || mentionsName x x2
  | .to_real x1 => mentionsName x x1
  | .to_int x1 => mentionsName x x1
  | .is_int x1 => mentionsName x x1
  | .abs x1 => mentionsName x x1
  | .uneg x1 => mentionsName x x1
  | .div x1 x2 => mentionsName x x1 || mentionsName x x2
  | .mod x1 x2 => mentionsName x x1 || mentionsName x x2
  | .divisible x1 x2 => mentionsName x x1 || mentionsName x x2
  | .int_pow2 x1 => mentionsName x x1
  | .int_log2 x1 => mentionsName x x1
  | .div_total x1 x2 => mentionsName x x1 || mentionsName x x2
  | .mod_total x1 x2 => mentionsName x x1 || mentionsName x x2
  | .select x1 x2 => mentionsName x x1 || mentionsName x x2
  | .store x1 x2 x3 => mentionsName x x1 || mentionsName x x2 || mentionsName x x3
  | .map_diff x1 x2 => mentionsName x x1 || mentionsName x x2
  | .concat x1 x2 => mentionsName x x1 || mentionsName x x2
  | .extract x1 x2 x3 => mentionsName x x1 || mentionsName x x2 || mentionsName x x3
  | .repeat x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvnot x1 => mentionsName x x1
  | .bvand x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvor x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvnand x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvnor x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvxor x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvxnor x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvcomp x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvneg x1 => mentionsName x x1
  | .bvadd x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvmul x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvudiv x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvurem x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvsub x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvsdiv x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvsrem x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvsmod x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvult x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvule x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvugt x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvuge x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvslt x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvsle x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvsgt x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvsge x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvshl x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvlshr x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvashr x1 x2 => mentionsName x x1 || mentionsName x x2
  | .zero_extend x1 x2 => mentionsName x x1 || mentionsName x x2
  | .sign_extend x1 x2 => mentionsName x x1 || mentionsName x x2
  | .rotate_left x1 x2 => mentionsName x x1 || mentionsName x x2
  | .rotate_right x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvuaddo x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvnego x1 => mentionsName x x1
  | .bvsaddo x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvumulo x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvsmulo x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvusubo x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvssubo x1 x2 => mentionsName x x1 || mentionsName x x2
  | .bvsdivo x1 x2 => mentionsName x x1 || mentionsName x x2
  | .seq_empty _ => false
  | .str_len x1 => mentionsName x x1
  | .str_concat x1 x2 => mentionsName x x1 || mentionsName x x2
  | .str_substr x1 x2 x3 => mentionsName x x1 || mentionsName x x2 || mentionsName x x3
  | .str_contains x1 x2 => mentionsName x x1 || mentionsName x x2
  | .str_replace x1 x2 x3 => mentionsName x x1 || mentionsName x x2 || mentionsName x x3
  | .str_indexof x1 x2 x3 => mentionsName x x1 || mentionsName x x2 || mentionsName x x3
  | .str_at x1 x2 => mentionsName x x1 || mentionsName x x2
  | .str_prefixof x1 x2 => mentionsName x x1 || mentionsName x x2
  | .str_suffixof x1 x2 => mentionsName x x1 || mentionsName x x2
  | .str_rev x1 => mentionsName x x1
  | .str_update x1 x2 x3 => mentionsName x x1 || mentionsName x x2 || mentionsName x x3
  | .str_to_lower x1 => mentionsName x x1
  | .str_to_upper x1 => mentionsName x x1
  | .str_to_code x1 => mentionsName x x1
  | .str_from_code x1 => mentionsName x x1
  | .str_is_digit x1 => mentionsName x x1
  | .str_to_int x1 => mentionsName x x1
  | .str_from_int x1 => mentionsName x x1
  | .str_lt x1 x2 => mentionsName x x1 || mentionsName x x2
  | .str_leq x1 x2 => mentionsName x x1 || mentionsName x x2
  | .str_replace_all x1 x2 x3 => mentionsName x x1 || mentionsName x x2 || mentionsName x x3
  | .str_replace_re x1 x2 x3 => mentionsName x x1 || mentionsName x x2 || mentionsName x x3
  | .str_replace_re_all x1 x2 x3 => mentionsName x x1 || mentionsName x x2 || mentionsName x x3
  | .str_indexof_re x1 x2 x3 => mentionsName x x1 || mentionsName x x2 || mentionsName x x3
  | .re_allchar => false
  | .re_none => false
  | .re_all => false
  | .str_to_re x1 => mentionsName x x1
  | .re_mult x1 => mentionsName x x1
  | .re_plus x1 => mentionsName x x1
  | .re_exp x1 x2 => mentionsName x x1 || mentionsName x x2
  | .re_opt x1 => mentionsName x x1
  | .re_comp x1 => mentionsName x x1
  | .re_range x1 x2 => mentionsName x x1 || mentionsName x x2
  | .re_concat x1 x2 => mentionsName x x1 || mentionsName x x2
  | .re_inter x1 x2 => mentionsName x x1 || mentionsName x x2
  | .re_union x1 x2 => mentionsName x x1 || mentionsName x x2
  | .re_diff x1 x2 => mentionsName x x1 || mentionsName x x2
  | .re_loop x1 x2 x3 => mentionsName x x1 || mentionsName x x2 || mentionsName x x3
  | .str_in_re x1 x2 => mentionsName x x1 || mentionsName x x2
  | .seq_unit x1 => mentionsName x x1
  | .seq_nth x1 x2 => mentionsName x x1 || mentionsName x x2
  | .str_indexof_re_split x1 x2 x3 => mentionsName x x1 || mentionsName x x2 || mentionsName x x3
  | .seq_diff x1 x2 => mentionsName x x1 || mentionsName x x2
  | ._at_strings_occur_index x1 x2 x3 => mentionsName x x1 || mentionsName x x2 || mentionsName x x3
  | ._at_strings_occur_index_re x1 x2 x3 =>
    mentionsName x x1 || mentionsName x x2 || mentionsName x x3
  | .choice _ _ x3 => mentionsName x x3
  | .set_empty _ => false
  | .set_singleton x1 => mentionsName x x1
  | .set_union x1 x2 => mentionsName x x1 || mentionsName x x2
  | .set_inter x1 x2 => mentionsName x x1 || mentionsName x x2
  | .set_minus x1 x2 => mentionsName x x1 || mentionsName x x2
  | .set_member x1 x2 => mentionsName x x1 || mentionsName x x2
  | .set_subset x1 x2 => mentionsName x x1 || mentionsName x x2
  | .qdiv x1 x2 => mentionsName x x1 || mentionsName x x2
  | .qdiv_total x1 x2 => mentionsName x x1 || mentionsName x x2
  | .forall _ _ x3 => mentionsName x x3
  | .exists _ _ x3 => mentionsName x x3
  | .bind _ _ x3 x4 => mentionsName x x3 || mentionsName x x4
  | .int_to_bv x1 x2 => mentionsName x x1 || mentionsName x x2
  | .ubv_to_int x1 => mentionsName x x1
  | .sbv_to_int x1 => mentionsName x x1

theorem contains_addNames (acc : Std.HashSet SmtEval.native_String) (x : SmtEval.native_String)
    (t : SmtTerm) : (addNames acc t).contains x = (acc.contains x || mentionsName x t) := by
  cases t
  case UConst s' _ => simp only [addNames, mentionsName, Std.HashSet.contains_insert, Bool.or_comm]
  all_goals simp only [addNames, mentionsName, Bool.or_false, Bool.or_assoc, contains_addNames]
termination_by structural t

theorem mentions_of_mentionsName {s : SmtEval.native_String} {T : SmtType} (t : SmtTerm)
    (h : mentionsName s t = false) : mentions s T t = false := by
  cases t
  case UConst s' _ =>
    simp only [mentionsName] at h
    simp only [mentions, h, Bool.false_and]
  all_goals
    simp only [mentions, mentionsName, Bool.or_eq_false_iff] at h ⊢
    try simp_all only [mentions_of_mentionsName, and_self]
termination_by structural t

theorem mentionsName_of_mentions {s : SmtEval.native_String} {T : SmtType} {t : SmtTerm}
    (h : mentions s T t = true) : mentionsName s t = true := by
  cases hn : mentionsName s t
  · rw [mentions_of_mentionsName t hn] at h; cases h
  · rfl

theorem contains_addClauseNames (x : SmtEval.native_String) :
    ∀ (acc : Std.HashSet SmtEval.native_String) (ts : List Term),
      (addClauseNames acc ts).contains x =
        (acc.contains x || ts.any fun t => mentionsName x (__eo_to_smt t))
  | acc, [] => by simp [addClauseNames]
  | acc, t :: ts => by
    show (addClauseNames (addNames acc (__eo_to_smt t)) ts).contains x = _
    rw [contains_addClauseNames x _ ts, contains_addNames, List.any_cons, Bool.or_assoc]

/-- `names` contains the name of each constant that a clause of `assums` mentions. -/
def NamesCover (names : Std.HashSet SmtEval.native_String) (assums : List Term) : Prop :=
  ∀ a ∈ assums, ∀ s T, mentions s T (__eo_to_smt a) = true → names.contains s = true

theorem namesCover_append {names : Std.HashSet SmtEval.native_String} {assums : List Term}
    (h : NamesCover names assums) (ts : List Term) :
    NamesCover (addClauseNames names ts) (assums ++ ts) := by
  intro a ha s T hm
  rw [contains_addClauseNames, Bool.or_eq_true, List.any_eq_true]
  rcases List.mem_append.mp ha with ha | ha
  · exact Or.inl (h a ha s T hm)
  · exact Or.inr ⟨a, ha, mentionsName_of_mentions hm⟩

theorem namesCover_base (base : List Term) : NamesCover (addClauseNames {} base) base := by
  have h : NamesCover {} [] := fun _ ha => absurd ha List.not_mem_nil
  simpa using namesCover_append h base

theorem fresh_of_freshB {st : Step} {names : Std.HashSet SmtEval.native_String}
    {assums : List Term} (hcov : NamesCover names assums) (h : freshB st names = true) :
    st.Fresh assums := by
  unfold freshB at h
  split at h
  · rename_i s T hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true] at h
    obtain ⟨⟨⟨⟨hf, hs⟩, hn⟩, hp⟩, hb⟩ := h
    refine ⟨hf, s, T, eq_of_asConst hc, hs, fun a ha => ?_, hp, hb⟩
    cases hm : mentions s T (__eo_to_smt a)
    · rfl
    · rw [hcov a ha s T hm] at hn
      cases hn
  · cases h

theorem stepsFresh_of_stepsFreshB :
    ∀ {names : Std.HashSet SmtEval.native_String} {assums : List Term} {sts : List Step},
      NamesCover names assums → stepsFreshB names sts = true → StepsFresh assums sts
  | _, _, [], _, _ => trivial
  | _, _, st :: _, hcov, h => by
    simp only [stepsFreshB, Bool.and_eq_true] at h
    exact ⟨fresh_of_freshB hcov h.1,
      stepsFresh_of_stepsFreshB (namesCover_append hcov st.clauses) h.2⟩

/-! ## What the check gives -/

/-- Each fact holds, in the models that `Good` selects, given the clauses before it. -/
def FactsHold (Good : SmtModel → Prop) : List Term → List Term → Prop
  | _, [] => True
  | assums, t :: ts => Holds Good assums t ∧ FactsHold Good (assums ++ [t]) ts

theorem extend_append (assums : List Term) (xs ys : List Step) :
    extend assums (xs ++ ys) = extend (extend assums xs) ys := by
  simp [extend, List.foldl_append]

theorem stepsOk_append {Good : SmtModel → Prop} :
    ∀ {assums : List Term} {xs ys : List Step}, StepsOk Good assums xs →
      StepsOk Good (extend assums xs) ys → StepsOk Good assums (xs ++ ys)
  | _, [], _, _, h => h
  | _, _ :: _, _, ⟨h1, h2⟩, h => ⟨h1, stepsOk_append h2 h⟩

theorem stepsOk_fresh {Good : SmtModel → Prop} :
    ∀ {assums : List Term} {sts : List Step}, StepsFresh assums sts →
      (∀ st ∈ sts, KeepsConst Good st.const) → StepsOk Good assums sts
  | _, [], _, _ => trivial
  | _, st :: _, ⟨hst, hsts⟩, hk => by
    refine ⟨?_, stepsOk_fresh hsts fun st' h => hk st' (List.mem_cons_of_mem _ h)⟩
    cases st
    case fact => exact absurd hst.1 (by simp [Step.isFact])
    all_goals exact ⟨hst, hk _ List.mem_cons_self⟩

theorem stepsOk_facts {Good : SmtModel → Prop} :
    ∀ {assums ts : List Term}, FactsHold Good assums ts → StepsOk Good assums (ts.map Step.fact)
  | _, [], _ => trivial
  | _, _ :: _, ⟨h1, h2⟩ => ⟨h1, stepsOk_facts h2⟩

/-! ### Derived clauses -/

theorem and_eq_true {x y : SmtValue} (h : __smtx_model_eval_and x y = SmtValue.Boolean true) :
    x = SmtValue.Boolean true ∧ y = SmtValue.Boolean true := by
  unfold __smtx_model_eval_and at h
  split at h <;> simp_all [SmtEval.native_and]

theorem eq_eq_true {b : Bool} {y : SmtValue}
    (h : __smtx_model_eval_eq (SmtValue.Boolean b) y = SmtValue.Boolean true) :
    y = SmtValue.Boolean b := by
  unfold __smtx_model_eval_eq at h
  split at h <;> simp_all [native_veq]

/-- A conjunct of a true conjunction is true. -/
theorem eval_of_inConj {M : SmtModel} {m t : Term} (hin : inConj m t = true)
    (h : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean true) :
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Boolean true := by
  fun_induction inConj m t with
  | case1 a rest ih =>
    rw [show Term.Apply (Term.Apply (Term.UOp UserOp.and) a) rest = Extend.mkAnd a rest from rfl,
      eo_to_smt_mkAnd] at h
    simp only [__smtx_model_eval] at h
    have hb := and_eq_true h
    rcases Bool.or_eq_true_iff.mp hin with hm | hm
    · rw [← beq_iff_eq.mp hm]; exact hb.1
    · exact ih hm hb.2
  | case2 t _ => rw [← beq_iff_eq.mp hin]; exact h

/-- `(=> b m)` holds in every model of a definition `(= b rhs)` of which `m` is a conjunct. -/
theorem holds_derived (hty : LogosTyping) (Good : SmtModel → Prop) {assums : List Term}
    {d : Derived} (hdef : Extend.mkEq d.blocker d.rhs ∈ assums)
    (hin : inConj d.target d.rhs = true)
    (hbool : __smtx_typeof (__eo_to_smt d.clause) = SmtType.Bool) :
    Holds Good assums d.clause := by
  intro M _ hsat
  rw [Derived.clause, eo_to_smt_mkImp] at hbool ⊢
  obtain ⟨hb, _⟩ := typeof_imp_bool hbool
  obtain ⟨vb, hvb⟩ := eval_bool hty hsat.1 hb
  have heq := hsat.2 _ hdef
  rw [eo_to_smt_mkEq] at heq
  simp only [__smtx_model_eval] at heq ⊢
  rw [hvb] at heq ⊢
  cases vb
  · obtain ⟨vm, hvm⟩ := eval_bool hty hsat.1 (typeof_imp_bool hbool).2
    rw [hvm]
    simp [__smtx_model_eval_imp, __smtx_model_eval_or, __smtx_model_eval_not,
      SmtEval.native_not, SmtEval.native_or]
  · rw [eval_of_inConj hin (eq_eq_true heq)]
    simp [__smtx_model_eval_imp, __smtx_model_eval_or, __smtx_model_eval_not,
      SmtEval.native_not, SmtEval.native_or]

theorem mem_extend {t : Term} : ∀ {assums : List Term} {sts : List Step}, t ∈ assums →
    t ∈ extend assums sts
  | _, [], h => h
  | assums, st :: sts, h => by
    show t ∈ extend (assums ++ st.clauses) sts
    exact mem_extend (List.mem_append_left _ h)

theorem stepsOk_derived (hty : LogosTyping) (Good : SmtModel → Prop) {defs : List Term} :
    ∀ {assums : List Term} {ds : List Derived}, (∀ t ∈ defs, t ∈ assums) →
      (∀ d ∈ ds, Extend.mkEq d.blocker d.rhs ∈ defs ∧ inConj d.target d.rhs = true ∧
        __smtx_typeof (__eo_to_smt d.clause) = SmtType.Bool) →
      StepsOk Good assums (ds.map (Step.fact ∘ Derived.clause))
  | _, [], _, _ => trivial
  | _, d :: _, hsub, hds => by
    obtain ⟨hdef, hin, hbool⟩ := hds d List.mem_cons_self
    exact ⟨holds_derived hty Good (hsub _ hdef) hin hbool,
      stepsOk_derived hty Good (fun t ht => List.mem_append_left _ (hsub t ht))
        fun d' h => hds d' (List.mem_cons_of_mem _ h)⟩

/-- No model satisfies a list that contains every formula of a list that has no model. -/
theorem no_model_of_mem {assums all : List Term} (hno : ∀ M, ¬ Satisfies M assums)
    (hmem : ∀ a ∈ assums, a ∈ all) : ∀ M, ¬ Satisfies M all :=
  fun M ⟨hwf, h⟩ => hno M ⟨hwf, fun a ha => h a (hmem a ha)⟩

/-- A fact that holds in the models that `Good` selects holds in those among them that `Good'`
selects. -/
theorem factsHold_mono {Good Good' : SmtModel → Prop} (h : ∀ M, Good' M → Good M) :
    ∀ {assums ts : List Term}, FactsHold Good assums ts → FactsHold Good' assums ts
  | _, [], _ => trivial
  | _, _ :: _, ⟨h1, h2⟩ => ⟨fun M hM hsat => h1 M (h M hM) hsat, factsHold_mono h h2⟩

/-- `no_good_model_of_accept`, where the facts only have to hold in the models in which the
constant of each `Enables` step holds only if one of its blockers does (`Step.Only`): the model
that the fresh-symbol steps build is one. -/
theorem no_good_model_of_accept_only (sound : LogosSound) (hty : LogosTyping)
    (Good : SmtModel → Prop) {certificate : Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked) (hr : termSteps checked = .ok r)
    (hcheck : r.check = true)
    (hkeep : ∀ st ∈ r.fresh, KeepsConst Good st.const)
    (hfacts : FactsHold (fun M => Good M ∧ ∀ st ∈ r.fresh, st.Only M) (extend r.base r.fresh)
      r.facts) :
    ∀ M, Good M → ¬ Satisfies M r.base := by
  obtain ⟨cmds, hParse⟩ := termSteps_parse hr
  simp only [TermSteps.check, Bool.and_eq_true, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, derivedB, decide_eq_true_eq] at hcheck
  obtain ⟨⟨hfresh, hderived⟩, hmem⟩ := hcheck
  have hno := no_model_of_mem (no_model_of_accept sound certificate checked r.assums cmds hAccept
    hParse) hmem
  intro M hgood hsat
  obtain ⟨M', hgood', hsat', honly⟩ := extend_sat_only hty Good r.fresh r.base []
    (stepsOk_fresh (stepsFresh_of_stepsFreshB (namesCover_base r.base) hfresh) hkeep) M hgood
    hsat (by simp)
  have hrest : StepsOk (fun M => Good M ∧ ∀ st ∈ r.fresh, st.Only M) (extend r.base r.fresh)
      (r.facts.map Step.fact ++ r.derived.map (Step.fact ∘ Derived.clause)) :=
    stepsOk_append (stepsOk_facts hfacts)
      (stepsOk_derived hty _ (fun t ht => mem_extend ht) fun d hd =>
        ⟨(hderived d hd).1.1, (hderived d hd).1.2, (hderived d hd).2⟩)
  obtain ⟨M'', _, hsat''⟩ := extend_sat_good hty _ _ _ hrest M'
    ⟨hgood', fun st h => honly st (by simpa using h)⟩ hsat'
  rw [← extend_append] at hsat''
  exact hno M'' (by simpa [TermSteps.steps, List.append_assoc] using hsat'')

/-- If the checker accepts a certificate and the check on terms holds, then no model that `Good`
selects satisfies the assumptions of the query, as Logos reads them, given:
- `hkeep`: reinterpreting a fresh symbol keeps the models that `Good` selects;
- `hfacts`: each fact holds in the models that `Good` selects, given the clauses of the fresh
  symbols and of the facts before it. These are the side conditions of the rules that are facts
  about the semantics, and of the completeness assumptions. -/
theorem no_good_model_of_accept (sound : LogosSound) (hty : LogosTyping)
    (Good : SmtModel → Prop) {certificate : Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked) (hr : termSteps checked = .ok r)
    (hcheck : r.check = true)
    (hkeep : ∀ st ∈ r.fresh, KeepsConst Good st.const)
    (hfacts : FactsHold Good (extend r.base r.fresh) r.facts) :
    ∀ M, Good M → ¬ Satisfies M r.base :=
  no_good_model_of_accept_only sound hty Good hAccept hr hcheck hkeep
    (factsHold_mono (fun _ h => h.1) hfacts)

end Inox
