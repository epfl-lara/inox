/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Reach
import Inox.Source

/-!
# An accepted certificate: the query has no solution, whatever the calls of the program

`no_solution_of_covered` of `Inox/Source.lean` assumes `Total`: every call of the program gives a
value. The models of a solution only satisfy the defining equation of a function on the arguments
where its call gives a value (`goodOn_calls`), so a certificate has to use the equations on such
calls only. It does: an instance of an equation is guarded by the activation literal of its call,
which holds only if a blocker of a path to the call does (`Step.Only` of `Inox/Extend.lean`), and
a blocker holds only where evaluation takes its path. This module checks it, and proves the
theorem without `Total`, `no_solution_of_reached`.

The check, `reachedCheck`:

- `guardedCalls` collects the pairs of an activation literal and a call that it guards
  (`Paths.guards`): the literal has blockers, and for each of them, evaluation goes through the
  call (`reachedBy`) under the literals that the blocker makes known, with the definitions of the
  constants they mention (`closeK`) and what the base makes known. Evaluation goes through a call
  when a base clause reaches it (`reaches` of `Inox/Reach.lean`), or when the body of a call
  already guarded, whose guard is known, reaches it with the arguments of that call for its
  parameters (`reachesBody`);
- `reachedCovered` accepts a fact that holds without the defining equations (`TermSteps.covered`
  with no equation), or that is an instance of a defining equation guarded by the literal that
  guards its call (`guardedEq`), or that states an assumption that the body of a guarded call
  goes through, such as its precondition, under literals that make the guard of the call true
  (`Paths.assumed`, with the bodies read with their assumptions, `bodyOf`), as it is or once the
  definitions of the local symbols of its instance are in place;
- `apart`: no fresh symbol is a function of the program or a variable of the query, so that
  reinterpreting one keeps the models where the calls and the variables agree.

The models are those of `Agrees`: the calls of the program and the variables of the query have
their values. The intended model of a solution is one, the steps keep them, and each fact that
the check accepts holds in those that satisfy the clauses of the steps (`holds_reachedCovered`):
by induction along `guardedCalls`, a guard that holds implies that its call gives a value
(`inv_calls`), by `called_of_reaches` and `called_of_call`, and the assumptions that the call
goes through hold (`assumed_of_call`).

`inox-check` doesn't run this check: like `sourceCheck`, it is defined over the semantics, in the
verification package.
-/

namespace Inox.Bridge

open Eo
open SmtEval
open Smtm
open Inox.Fresh
open Inox.Extend
open Inox.Model
open Inox.Semantics

/-! ## The check -/

/-- The function of an application. -/
def smtHead : SmtTerm → SmtTerm
  | .Apply f _ => smtHead f
  | t => t

/-- The literals that those of `K` make known, given the definitions `defs` of constants: those
of the definition of each constant that is true, and so on, `n` times. -/
def closeK (defs : List (SmtTerm × SmtTerm)) : Nat → List (SmtTerm × Bool) →
    List (SmtTerm × Bool)
  | 0, K => K
  | n + 1, K =>
    K ++ closeK defs n (K.flatMap fun p =>
      if p.2 then (defs.filter fun d => decide (d.1 = p.1)).flatMap fun d => lits d.2 true
      else [])

/-- Evaluating the call `c'` goes through the call `c`, under the literals `K`: the body of the
equation of the function of `c'`, with the arguments of `c'` for its parameters, reaches `c`. -/
def reachesBody (eqs : List Equation) (K : List (SmtTerm × Bool)) (c c' : SmtTerm) : Bool :=
  eqs.any fun e => match __eo_to_smt e.term with
    | .eq lhs rhs =>
      decide (smtHead lhs = smtHead c') && paramsB e.params (smtArgs c') &&
        reachesW (substSmt (bindParams e.params (smtArgs c'))) K c true rhs
    | _ => false

/-- Evaluation goes through the call `c`, under the literals `K`: a base clause reaches it, or a
call of `J` whose guard `K` makes true does. -/
def reachedBy (eqs : List Equation) (base : List Term) (J : List (SmtTerm × SmtTerm))
    (K : List (SmtTerm × Bool)) (c : SmtTerm) : Bool :=
  base.any (fun t => reaches K c true (__eo_to_smt t)) ||
    J.any fun p => decide (known K p.1 = some true) && reachesBody eqs K c p.2

/-- What the check reads from the steps: the base clauses, the definitions of constants, the
activation literals with their blockers, and the literals that the base makes known. -/
structure Paths where
  eqs : List Equation
  base : List Term
  defs : List (SmtTerm × SmtTerm)
  enab : List (SmtTerm × List SmtTerm)
  K0 : List (SmtTerm × Bool)

/-- The activation literal `d` guards the call `c`: it has blockers, and under each, with the
literals that its definition makes known, evaluation goes through `c`. -/
def Paths.guards (p : Paths) (J : List (SmtTerm × SmtTerm)) (d c : SmtTerm) : Bool :=
  p.enab.any fun q => decide (q.1 = d) && !q.2.isEmpty && q.2.all fun b =>
    reachedBy p.eqs p.base J (closeK p.defs p.defs.length (lits b true) ++ p.K0) c

/-- The pairs of `cands` of an activation literal and a call that it guards, each given those
before it. -/
def Paths.calls (p : Paths) (cands : List (SmtTerm × SmtTerm)) : List (SmtTerm × SmtTerm) :=
  cands.foldl (fun J q => if p.guards J q.1 q.2 then q :: J else J) []

/-- The left side of an equation. -/
def lhsOf (e : Equation) : SmtTerm :=
  match __eo_to_smt e.term with
  | .eq lhs _ => lhs
  | t => t

/-- `φ` is `(=> g (= lhs rhs))`, an instance of a defining equation of `eqs` guarded by a Boolean
that guards its call in `J`. -/
def guardedEq (eqs : List Equation) (J : List (SmtTerm × SmtTerm)) : SmtTerm → Bool
  | .imp g (.eq lhs rhs) =>
    decide (__smtx_typeof g = .Bool) && J.contains (g, lhs) &&
      eqs.any fun e => eqInstB e (.eq lhs rhs) (smtArgs lhs) &&
        decide (smtHead (lhsOf e) = smtHead lhs)
  | _ => false

/-- The guard and the call of a guarded equality. -/
def candOf : SmtTerm → Option (SmtTerm × SmtTerm)
  | .imp g (.eq lhs _) => some (g, lhs)
  | _ => none

/-- The clauses of the instances, with the definitions of their local symbols that are clauses of
the fresh-symbol steps in place of the symbols, paired with the clauses. -/
def substituted (r : TermSteps) : List (Term × SmtTerm) :=
  let ctx := Std.HashSet.ofList (extend r.base r.fresh)
  r.instances.flatMap fun (defs, cs) =>
    let σ := (defs.filter ctx.contains).filterMap defBinding
    (cs.filter fun c => noBinder (__eo_to_smt c)).map fun c => (c, substSmt σ (__eo_to_smt c))

/-- What `Paths` reads from the steps of `r`. -/
def pathsOf (r : TermSteps) : Paths where
  eqs := r.equations
  base := r.base
  defs := r.fresh.filterMap fun st => match st with
    | .define c rhs => some (__eo_to_smt c, __eo_to_smt rhs)
    | _ => none
  enab := r.fresh.filterMap fun st => match st with
    | .enables c bs => some (__eo_to_smt c, bs.map __eo_to_smt)
    | _ => none
  K0 := r.baseLits

/-- The calls that the activation literals of `r` guard, among those of its facts and of the
clauses of its instances. -/
def guardedCalls (r : TermSteps) : List (SmtTerm × SmtTerm) :=
  (pathsOf r).calls
    (r.facts.filterMap (fun t => candOf (__eo_to_smt t)) ++
      (substituted r).filterMap fun q => candOf q.2)

/-- Evaluating the call `c'` goes through an assumption whose term is `ψ`, under the literals
`K`: the body read from the equation of the function of `c'` assumes it, with the arguments of
`c'` for its parameters. -/
def assumesBody (S : List Sig) (eqs : List Equation) (K : List (SmtTerm × Bool))
    (ψ c' : SmtTerm) : Bool :=
  eqs.any fun e => decide (smtHead (lhsOf e) = smtHead c') && paramsB e.params (smtArgs c') &&
    assumesW S (sigOf e).params (substSmt (bindParams e.params (smtArgs c'))) K ψ (bodyOf e)

/-- `φ` is `(=> g ψ)`, where `ψ` is an assumption that the evaluation of a call of `J` goes
through, under the literals that `g` makes known, which make the guard of the call true: a
precondition of the call, or another assumption of its body. -/
def Paths.assumed (p : Paths) (S : List Sig) (J : List (SmtTerm × SmtTerm)) : SmtTerm → Bool
  | .imp g ψ =>
    decide (__smtx_typeof g = .Bool) && decide (__smtx_typeof ψ = .Bool) &&
      J.any fun q =>
        decide (known (closeK p.defs p.defs.length (lits g true) ++ p.K0) q.1 = some true) &&
          assumesBody S p.eqs (closeK p.defs p.defs.length (lits g true) ++ p.K0) ψ q.2
  | _ => false

/-- The fact `t` holds where the calls that evaluation goes through have values: it holds without
the defining equations, or it is, as it is or as the clause of an instance of a template, an
instance of a defining equation whose guard guards its call, or an assumption of a call whose
guard holds. -/
def reachedCovered (r : TermSteps) : Term → Bool :=
  let J := guardedCalls r
  let p := pathsOf r
  let S := sigsOf r.equations
  let ok := fun φ => guardedEq r.equations J φ || p.assumed S J φ
  let sub := (substituted r).filter fun q => ok q.2
  let inst := Std.HashSet.ofList (sub.map Prod.fst)
  fun t => ({ r with equations := [] } : TermSteps).covered t || ok (__eo_to_smt t) ||
    inst.contains t

/-- No fresh symbol is a function of `S` or a variable of `Γ`. -/
def apart (S : List Sig) (Γ : List (Id × Ty)) (r : TermSteps) : Bool :=
  r.fresh.all fun st => match asConst (__eo_to_smt st.const) with
    | some (s, T) =>
      (S.all fun g => !decide (nm g.name = s ∧ g.toDef.ty = T)) &&
        Γ.all fun p => !decide (nm p.1 = s ∧ trT p.2 = T)
    | none => true

/-- The check: the fresh symbols are apart from the program and the query, and every fact is
covered where the calls that evaluation goes through have values. -/
def reachedCheck (r : TermSteps) : Bool :=
  apart (sigsOf r.equations) (varsOf (sigsOf r.equations) r.base) r &&
    r.facts.all (reachedCovered r)

/-! ## Applications and substitutions -/

theorem smtHead_spine : ∀ (us : List SmtTerm) (f : SmtTerm), smtHead (spine f us) = smtHead f
  | [], _ => rfl
  | a :: as, f => by rw [spine, smtHead_spine as]; rfl

theorem smtArgs_spine : ∀ (us : List SmtTerm) (f : SmtTerm),
    smtArgs (spine f us) = smtArgs f ++ us
  | [], f => by simp [spine]
  | a :: as, f => by rw [spine, smtArgs_spine as]; simp [smtArgs]

theorem substSmt_spine (σ : List (native_String × SmtType × SmtTerm)) :
    ∀ (us : List SmtTerm) (f : SmtTerm),
      substSmt σ (spine f us) = spine (substSmt σ f) (us.map (substSmt σ))
  | [], _ => rfl
  | a :: as, f => by
    simp only [spine, List.map_cons]
    rw [substSmt_spine σ as]
    rfl

theorem mem_bindParams : ∀ {ps : List (native_String × SmtType)} {us : List SmtTerm}
    {e : native_String × SmtType × SmtTerm}, e ∈ bindParams ps us → (e.1, e.2.1) ∈ ps
  | [], _, _, h => by simp [bindParams] at h
  | _ :: _, [], _, h => by simp [bindParams] at h
  | _ :: _, _ :: _, e, h => by
    simp only [bindParams, List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact .head _
    · exact .tail _ (mem_bindParams h)

theorem noBinder_andT : ∀ ts : List SmtTerm, (∀ t ∈ ts, noBinder t = true) →
    noBinder (andT ts) = true
  | [], _ => rfl
  | t :: ts, h => by
    simp only [andT, noBinder, Bool.and_eq_true]
    exact ⟨h t (.head _), noBinder_andT ts fun u hu => h u (.tail _ hu)⟩

theorem noBinder_orT : ∀ ts : List SmtTerm, (∀ t ∈ ts, noBinder t = true) →
    noBinder (orT ts) = true
  | [], _ => rfl
  | t :: ts, h => by
    simp only [orT, noBinder, Bool.and_eq_true]
    exact ⟨h t (.head _), noBinder_orT ts fun u hu => h u (.tail _ hu)⟩

theorem noBinder_spine : ∀ (us : List SmtTerm) (f : SmtTerm), noBinder f = true →
    (∀ u ∈ us, noBinder u = true) → noBinder (spine f us) = true
  | [], _, hf, _ => hf
  | a :: as, f, hf, h =>
    noBinder_spine as (.Apply f a) (by simp [noBinder, hf, h a (.head _)])
      fun u hu => h u (.tail _ hu)

theorem all_of_zip {α β : Type} {Q : α → Prop} : ∀ {l : List α} {m : List β},
    l.length = m.length → (∀ p ∈ l.zip m, Q p.1) → ∀ a ∈ l, Q a
  | [], _, _, _, _, ha => by cases ha
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | a :: l, b :: m, hl, h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h (x, b) (.head _)
    · exact all_of_zip (by simpa using hl) (fun p hp => h p (.tail _ hp)) x hx

/-- The term of an expression of the fragment has no binder. -/
theorem noBinder_tr {S : List Sig} {Γ : List (Id × Ty)} {e : Expr} {T : Ty}
    (h : HasTy S Γ e T) : noBinder (tr S Γ e) = true := by
  induction h with
  | var hx hT => simp [tr, hx, noBinder]
  | int i => rfl
  | bool b => rfl
  | @and es _ ih =>
    simp only [tr, trs_eq]
    exact noBinder_andT _ fun t ht => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
      exact ih e he
  | @or es _ ih =>
    simp only [tr, trs_eq]
    exact noBinder_orT _ fun t ht => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
      exact ih e he
  | @invoke s args hs hl _ ih =>
    simp only [tr, hs, trs_eq]
    refine noBinder_spine _ _ rfl fun t ht => ?_
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
    exact all_of_zip (Q := fun a => noBinder (tr S Γ a) = true) (by simpa using hl) ih e he
  | assume _ _ _ ihb => simpa [tr] using ihb
  | _ => simp_all [tr, noBinder]

/-! ## The literals of definitions -/

theorem kSound_closeK {M : SmtModel} {defs : List (SmtTerm × SmtTerm)}
    (hd : ∀ d ∈ defs, __smtx_model_eval M (.eq d.1 d.2) = SmtValue.Boolean true) :
    ∀ (n : Nat) {K : List (SmtTerm × Bool)}, KSound M K → KSound M (closeK defs n K)
  | 0, _, hK => hK
  | n + 1, K, hK => by
    refine kSound_append hK (kSound_closeK hd n fun q hq => ?_)
    simp only [List.mem_flatMap] at hq
    obtain ⟨p, hp, hq⟩ := hq
    split at hq
    · next hp2 =>
      simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hq
      obtain ⟨d, ⟨hdm, hd1⟩, hq⟩ := hq
      have h1 := hK p hp
      rw [hp2, ← hd1] at h1
      have h2 := hd d hdm
      simp only [__smtx_model_eval, h1] at h2
      exact lits_sound _ true (Inox.eq_eq_true h2) q hq
    · simp at hq

/-! ## The models of a solution -/

section Sound
variable {O : Oracle} {P : Program} {S : List Sig}

/-- What the check is about: a well-formed model where the calls and the variables of the query
agree, the base clauses are expressions of the query that have values, the definitions and the
known literals hold, and an activation literal holds only if one of its blockers does. -/
structure Ctx (O : Oracle) (P : Program) (S : List Sig) (Γ : List (Id × Ty)) (env : Env)
    (p : Paths) (M : SmtModel) : Prop where
  wf : model_wf M
  calls : ∀ m, CallsOk O P S m M
  vars : VarsOk Γ env M
  base : ∀ t ∈ p.base, ∃ q, HasTy S Γ q .BooleanType ∧ __eo_to_smt t = tr S Γ q ∧
    ∃ n v, eval O P n env q = .Ok v
  defs : ∀ d ∈ p.defs, __smtx_model_eval M (.eq d.1 d.2) = SmtValue.Boolean true
  enab : ∀ q ∈ p.enab, q.2 ≠ [] → __smtx_model_eval M q.1 = SmtValue.Boolean true →
    ∃ b ∈ q.2, __smtx_model_eval M b = SmtValue.Boolean true
  known : KSound M p.K0
  eqs : ∀ e ∈ p.eqs, ∃ s ∈ S, EqFor P S s e

/-- The guards of `J` imply that their calls give values. -/
def Inv (O : Oracle) (P : Program) (S : List Sig) (M : SmtModel)
    (J : List (SmtTerm × SmtTerm)) : Prop :=
  ∀ q ∈ J, __smtx_model_eval M q.1 = SmtValue.Boolean true → Called O P S M q.2

theorem uconst_inj {a b : native_String} {A B : SmtType}
    (h : SmtTerm.UConst a A = SmtTerm.UConst b B) : a = b := by
  cases h; rfl

/-- A call that the body of a call that gives a value reaches gives a value. -/
theorem called_of_reachesBody (hO : O.Sound) (hty : LogosTyping) (hS : SigOk S)
    (hP : ProgTy S P) {eqs : List Equation} (hE : ∀ e ∈ eqs, ∃ s ∈ S, EqFor P S s e)
    {M : SmtModel} (hw : model_wf M) (hcalls : ∀ m, CallsOk O P S m M)
    {K : List (SmtTerm × Bool)} (hK : KSound M K) {c c' : SmtTerm}
    (hpar : Called O P S M c') (h : reachesBody eqs K c c' = true) : Called O P S M c := by
  obtain ⟨e, he, h⟩ := List.any_eq_true.mp h
  obtain ⟨s, hs, body, hbody, hbty, hpe, hterm⟩ := hE e he
  obtain ⟨s', hs', us, vs, rfl, hus, hvs, n, v, hcall⟩ := hpar
  rw [hterm] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, smtHead_spine, smtArgs_spine, smtHead,
    smtArgs, List.nil_append] at h
  obtain ⟨⟨hhead, hparams⟩, hr⟩ := h
  have hss : s = s' := sig_eq_of_name hS.nodup hs hs' (nm_inj (uconst_inj hhead))
  subst hss
  obtain ⟨hσ, _⟩ := params_of_paramsB hty hw hparams
  obtain ⟨hw', hc', hV'⟩ := bound_model hS hs hw hcalls hvs
  have hM' : setConsts M (bindingValues M (bindParams e.params us)) =
      setConsts M (bindValues (ptys s.params) (vs.map trV)) := by
    rw [bindingValues_bindParams, hpe, hus]
  have hT : Through S s.params (substSmt (bindParams e.params us)) M
      (setConsts M (bindValues (ptys s.params) (vs.map trV))) := by
    intro e' T' h'
    rw [← hM']
    exact eval_subst hσ M _ (noBinder_tr h')
  obtain ⟨s2, hs2, us0, vs0, rfl, hus0, hvs0, hcall0⟩ :=
    called_of_call hO hty hS hP hbody hbty hvs hcall hw' hc' hV' hw hT hK hr
  refine ⟨s2, hs2, us0.map (substSmt (bindParams e.params us)), vs0, ?_, ?_, hvs0, hcall0⟩
  · rw [substSmt_spine]
    congr 1
    simp only [substSmt, substConst]
    rw [List.find?_eq_none.mpr]
    intro b hb hbe
    simp only [Bool.and_eq_true, beq_iff_eq] at hbe
    have hm := mem_bindParams hb
    rw [hpe] at hm
    simp only [ptys, List.mem_map] at hm
    obtain ⟨q, hq, hqe⟩ := hm
    have h1 : nm q.1 = b.1 := congrArg Prod.fst hqe
    exact hS.fresh s hs q hq s2 hs2 (nm_inj (h1.trans hbe.1))
  · rw [List.map_map]
    exact hus0

/-- A call that evaluation goes through, from the query or from a call that gives a value, gives
a value. -/
theorem called_of_reachedBy (hO : O.Sound) (hty : LogosTyping) (hS : SigOk S)
    (hP : ProgTy S P) {Γ : List (Id × Ty)} {env : Env} (hE : EnvTy Γ env) {p : Paths}
    {M : SmtModel} (hM : Ctx O P S Γ env p M) {J : List (SmtTerm × SmtTerm)}
    (hJ : Inv O P S M J) {K : List (SmtTerm × Bool)} (hK : KSound M K) {c : SmtTerm}
    (h : reachedBy p.eqs p.base J K c = true) : Called O P S M c := by
  simp only [reachedBy, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  rcases h with ⟨t, ht, h⟩ | ⟨q, hq, hk, h⟩
  · obtain ⟨e, he, htr, n, v, hv⟩ := hM.base t ht
    rw [htr] at h
    exact called_of_reaches hO hty hS hP (call_ty' hO hty hS hP n) he hE hv hM.wf (hM.calls n)
      hM.vars hK h
  · exact called_of_reachesBody hO hty hS hP hM.eqs hM.wf hM.calls hK
      (hJ q hq (hK _ (known_mem hk))) h

/-- An activation literal that guards a call implies that the call gives a value. -/
theorem inv_guards (hO : O.Sound) (hty : LogosTyping) (hS : SigOk S) (hP : ProgTy S P)
    {Γ : List (Id × Ty)} {env : Env} (hE : EnvTy Γ env) {p : Paths} {M : SmtModel}
    (hM : Ctx O P S Γ env p M) {J : List (SmtTerm × SmtTerm)} (hJ : Inv O P S M J)
    {d c : SmtTerm} (h : p.guards J d c = true) : Inv O P S M ((d, c) :: J) := by
  intro q hq hd
  rcases List.mem_cons.mp hq with rfl | hq
  · simp only [Paths.guards, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', List.all_eq_true] at h
    obtain ⟨x, hx, ⟨hxd, hne⟩, hall⟩ := h
    subst hxd
    obtain ⟨b, hb, hbv⟩ := hM.enab x hx (by intro h0; simp [h0] at hne) hd
    exact called_of_reachedBy hO hty hS hP hE hM hJ
      (kSound_append (kSound_closeK hM.defs _ (lits_sound b true hbv)) hM.known) (hall b hb)
  · exact hJ q hq hd

theorem inv_calls (hO : O.Sound) (hty : LogosTyping) (hS : SigOk S) (hP : ProgTy S P)
    {Γ : List (Id × Ty)} {env : Env} (hE : EnvTy Γ env) {p : Paths} {M : SmtModel}
    (hM : Ctx O P S Γ env p M) (cands : List (SmtTerm × SmtTerm)) :
    Inv O P S M (p.calls cands) := by
  have : ∀ (cands : List (SmtTerm × SmtTerm)) (J : List (SmtTerm × SmtTerm)), Inv O P S M J →
      Inv O P S M (cands.foldl (fun J q => if p.guards J q.1 q.2 then q :: J else J) J) := by
    intro cands
    induction cands with
    | nil => exact fun _ h => h
    | cons q cands ih =>
      intro J hJ
      simp only [List.foldl_cons]
      split
      · next hg => exact ih _ (inv_guards hO hty hS hP hE hM hJ hg)
      · exact ih _ hJ
  exact this cands [] (fun _ h => by cases h)

/-- An instance of a defining equation whose guard guards its call holds. -/
theorem guardedEq_sound (hO : O.Sound) (hty : LogosTyping) (hS : SigOk S) (hP : ProgTy S P)
    {Γ : List (Id × Ty)} {env : Env} {p : Paths} {M : SmtModel} (hM : Ctx O P S Γ env p M)
    {J : List (SmtTerm × SmtTerm)} (hJ : Inv O P S M J) {φ : SmtTerm}
    (h : guardedEq p.eqs J φ = true) : __smtx_model_eval M φ = SmtValue.Boolean true := by
  unfold guardedEq at h
  split at h
  · next g lhs rhs =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, List.any_eq_true] at h
    obtain ⟨⟨hg, hmem⟩, e, he, hinst, hhead⟩ := h
    simp only [eqInstB, Bool.and_eq_true, decide_eq_true_eq] at hinst
    obtain ⟨⟨hparams, hb⟩, hsubst⟩ := hinst
    obtain ⟨hσ, htyped⟩ := params_of_paramsB hty hM.wf hparams
    have hgood := goodOn_calls hO hty hS hP hM.eqs hM.wf hM.calls e he _ htyped
    have hs : __smtx_model_eval M (.eq lhs rhs) = __smtx_model_eval
        (setConsts M (bindValues e.params ((smtArgs lhs).map (__smtx_model_eval M))))
        (__eo_to_smt e.term) := by
      rw [← hsubst, eval_subst hσ M _ hb, bindingValues_bindParams]
    show __smtx_model_eval_imp (__smtx_model_eval M g) (__smtx_model_eval M (.eq lhs rhs)) = _
    obtain ⟨bg, hbg⟩ := eval_bool hty hM.wf hg
    cases bg
    · obtain ⟨b, hb'⟩ := hgood.1
      rw [hbg, hs, hb']
      cases b <;> rfl
    · rw [hs, hgood.2 ?_]
      · exact eval_imp_true hty hM.wf hg
      · intro s hs hfor vs0 hvs0 hws
        obtain ⟨s', hs', us, vs, hl, hus, hvs, n, v, hcall⟩ := hJ _ hmem hbg
        obtain ⟨body, _, _, _, hterm⟩ := hfor
        replace hl : lhs = _ := hl
        rw [hl] at hhead hws
        simp only [lhsOf, hterm, smtHead_spine, smtHead, smtArgs_spine, smtArgs,
          List.nil_append] at hhead hws
        have hss : s = s' := sig_eq_of_name hS.nodup hs hs' (nm_inj (uconst_inj hhead))
        subst hss
        have hvv : vs0 = vs := by
          rw [← ofSmt_map hvs0, ← ofSmt_map hvs, ← hws, hus]
        subst hvv
        exact ⟨n, v, hcall⟩
  · simp at h

/-- The equation `e` is that of the function read from it, with the body read from it. -/
def EqBody (P : Program) (S : List Sig) (e : Equation) : Prop :=
  sigOf e ∈ S ∧ HasBody P (sigOf e) (bodyOf e) ∧
    HasTy S (sigOf e).params (bodyOf e) (sigOf e).ret ∧ e.params = ptys (sigOf e).params ∧
    __eo_to_smt e.term = .eq
      (spine (.UConst (nm (sigOf e).name) (sigOf e).toDef.ty)
        ((ptys (sigOf e).params).map fun q => .UConst q.1 q.2))
      (tr S (sigOf e).params (bodyOf e))

/-- An assumption that the body of a call that gives a value goes through holds. -/
theorem assumesBody_sound (hO : O.Sound) (hty : LogosTyping) (hS : SigOk S) (hP : ProgTy S P)
    {eqs : List Equation} (hE : ∀ e ∈ eqs, EqBody P S e) {M : SmtModel} (hw : model_wf M)
    (hcalls : ∀ m, CallsOk O P S m M) {K : List (SmtTerm × Bool)} (hK : KSound M K)
    {ψ c' : SmtTerm} (hpar : Called O P S M c') (h : assumesBody S eqs K ψ c' = true) :
    __smtx_model_eval M ψ = SmtValue.Boolean true := by
  obtain ⟨e, he, h⟩ := List.any_eq_true.mp h
  obtain ⟨hs, hbody, hbty, hpe, hterm⟩ := hE e he
  obtain ⟨s', hs', us, vs, rfl, hus, hvs, n, v, hcall⟩ := hpar
  simp only [lhsOf, hterm, Bool.and_eq_true, decide_eq_true_eq, smtHead_spine, smtArgs_spine,
    smtHead, smtArgs, List.nil_append] at h
  obtain ⟨⟨hhead, hparams⟩, hr⟩ := h
  have hss : sigOf e = s' := sig_eq_of_name hS.nodup hs hs' (nm_inj (uconst_inj hhead))
  subst hss
  obtain ⟨hσ, _⟩ := params_of_paramsB hty hw hparams
  obtain ⟨hw', hc', hV'⟩ := bound_model hS hs hw hcalls hvs
  have hM' : setConsts M (bindingValues M (bindParams e.params us)) =
      setConsts M (bindValues (ptys (sigOf e).params) (vs.map trV)) := by
    rw [bindingValues_bindParams, hpe, hus]
  have hT : Through S (sigOf e).params (substSmt (bindParams e.params us)) M
      (setConsts M (bindValues (ptys (sigOf e).params) (vs.map trV))) := by
    intro e' T' h'
    rw [← hM']
    exact eval_subst hσ M _ (noBinder_tr h')
  exact assumed_of_call hO hty hS hP hbody hbty hvs hcall hw' hc' hV' hw hT hK hr

/-- A clause that states an assumption of a call whose guard holds is true. -/
theorem assumed_sound (hO : O.Sound) (hty : LogosTyping) (hS : SigOk S) (hP : ProgTy S P)
    {Γ : List (Id × Ty)} {env : Env} {p : Paths} {M : SmtModel} (hM : Ctx O P S Γ env p M)
    (hE : ∀ e ∈ p.eqs, EqBody P S e) {J : List (SmtTerm × SmtTerm)} (hJ : Inv O P S M J)
    {φ : SmtTerm} (h : p.assumed S J φ = true) :
    __smtx_model_eval M φ = SmtValue.Boolean true := by
  unfold Paths.assumed at h
  split at h
  · next g ψ =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
    obtain ⟨⟨hg, hψ⟩, q, hq, hk, ha⟩ := h
    show __smtx_model_eval_imp (__smtx_model_eval M g) (__smtx_model_eval M ψ) = _
    obtain ⟨bg, hbg⟩ := eval_bool hty hM.wf hg
    cases bg
    · obtain ⟨b, hb⟩ := eval_bool hty hM.wf hψ
      rw [hbg, hb]
      cases b <;> rfl
    · have hK := kSound_append (kSound_closeK hM.defs p.defs.length (lits_sound g true hbg))
        hM.known
      rw [assumesBody_sound hO hty hS hP hE hM.wf hM.calls hK
        (hJ q hq (hK _ (known_mem hk))) ha]
      exact eval_imp_true hty hM.wf hg
  · simp at h

end Sound

/-! ## The steps of a certificate -/

section Steps
variable {O : Oracle} {P : Program} {S : List Sig}

/-- The models that the check is about: those where the calls and the variables of the query
agree. -/
def Agrees (O : Oracle) (P : Program) (S : List Sig) (Γ : List (Id × Ty)) (env : Env)
    (M : SmtModel) : Prop :=
  (∀ m, CallsOk O P S m M) ∧ VarsOk Γ env M

theorem applyAll_setConst (s : native_String) (T : SmtType) (M : SmtModel) (v : SmtValue) :
    ∀ fv ws, applyAll (setConst s T M v) fv ws = applyAll M fv ws
  | _, [] => rfl
  | fv, w :: ws => by
    simp only [applyAll]
    rw [model_eval_apply_setConst]
    exact applyAll_setConst s T M v _ ws

theorem eval_uconst_setConst {s a : native_String} {T A : SmtType} (M : SmtModel) (v : SmtValue)
    (h : ¬ (a = s ∧ A = T)) :
    __smtx_model_eval (setConst s T M v) (.UConst a A) = __smtx_model_eval M (.UConst a A) := by
  simp only [__smtx_model_eval, native_model_lookup, setConst]
  split
  · next hk =>
    simp only [model_key, SmtModelKey.mk.injEq, true_and] at hk
    exact absurd hk h
  · rfl

/-- Reinterpreting a fresh symbol keeps the models where the calls and the variables agree, when
the fresh symbols are apart from them. -/
theorem keeps_of_apart {Γ : List (Id × Ty)} {env : Env} {r : TermSteps}
    (h : apart S Γ r = true) : ∀ st ∈ r.fresh, KeepsConst (Agrees O P S Γ env) st.const := by
  intro st hst s T hc M v ⟨hcalls, hvars⟩
  have h := List.all_eq_true.mp h st hst
  simp only [hc, asConst, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  refine ⟨fun m s' hs' tenv vs v' hvs hcall => ?_, fun x T' hx w hw => ?_⟩
  · rw [applyAll_setConst, eval_uconst_setConst M v (h.1 s' hs')]
    exact hcalls m s' hs' tenv vs v' hvs hcall
  · have hmem : (x, T') ∈ Γ := by
      obtain ⟨l₁, l₂, rfl, _⟩ := List.lookup_eq_some_iff.mp hx
      simp
    rw [eval_uconst_setConst M v (h.2 (x, T') hmem)]
    exact hvars x T' hx w hw

/-- A model of the clauses of the steps where the calls and the variables agree, and where the
activation literals hold only as their blockers do, is one that the check is about. -/
theorem ctx_of {Γ : List (Id × Ty)} {env : Env} (hty : LogosTyping) {r : TermSteps}
    {M : SmtModel} (hA : Agrees O P S Γ env M) (honly : ∀ st ∈ r.fresh, st.Only M)
    {assums : List Term} (hsub : extend r.base r.fresh ⊆ assums) (hsat : Satisfies M assums)
    (hbase : ∀ t ∈ r.base, ∃ q, HasTy S Γ q .BooleanType ∧ __eo_to_smt t = tr S Γ q ∧
      ∃ n v, eval O P n env q = .Ok v)
    (hE : ∀ e ∈ r.equations, ∃ s ∈ S, EqFor P S s e) : Ctx O P S Γ env (pathsOf r) M where
  wf := hsat.1
  calls := hA.1
  vars := hA.2
  base := hbase
  defs := by
    intro d hd
    simp only [pathsOf, List.mem_filterMap] at hd
    obtain ⟨st, hst, hd⟩ := hd
    cases st <;> simp only [Option.some.injEq, reduceCtorEq] at hd
    case define c rhs =>
      subst hd
      exact hsat.2 (Extend.mkEq c rhs) (hsub (clause_mem_extend hst (by simp [Step.clauses])))
  enab := by
    intro q hq hne hv
    simp only [pathsOf, List.mem_filterMap] at hq
    obtain ⟨st, hst, hq⟩ := hq
    cases st <;> simp only [Option.some.injEq, reduceCtorEq] at hq
    case enables c bs =>
      subst hq
      obtain ⟨b, hb, hbv⟩ := honly _ hst (by intro h0; simp [h0] at hne) hv
      exact ⟨_, List.mem_map_of_mem hb, hbv⟩
  known := kSound_baseLits hty hsat.1 fun t ht => hsat.2 t (hsub ht)
  eqs := hE

/-- A clause of an instance has the value of the clause with the definitions of the local symbols
in place, in the models of the definitions. -/
theorem eval_of_substituted (hty : LogosTyping) {r : TermSteps} {M : SmtModel}
    {assums : List Term} (hsub : extend r.base r.fresh ⊆ assums) (hsat : Satisfies M assums)
    {q : Term × SmtTerm} (hq : q ∈ substituted r) :
    __smtx_model_eval M (__eo_to_smt q.1) = __smtx_model_eval M q.2 := by
  simp only [substituted, List.mem_flatMap, List.mem_map, List.mem_filter] at hq
  obtain ⟨⟨defs, cs⟩, _, c', ⟨_, hnb⟩, rfl⟩ := hq
  have hσ : ∀ e ∈
      (defs.filter (Std.HashSet.ofList (extend r.base r.fresh)).contains).filterMap defBinding,
      (Unreserved e.1 ∧ plainHead e.2.2 = true) ∧
        M.values (model_key e.1 e.2.1) = __smtx_model_eval M e.2.2 := by
    intro e he
    obtain ⟨d, hd, hb⟩ := List.mem_filterMap.mp he
    simp only [List.mem_filter, Std.HashSet.contains_ofList, List.contains_iff_mem] at hd
    exact defBinding_sound hty hsat.1 hb (hsat.2 d (hsub hd.2))
  have hself : setConsts M (bindingValues M
      ((defs.filter (Std.HashSet.ofList (extend r.base r.fresh)).contains).filterMap
        defBinding)) = M := by
    apply setConsts_self
    intro e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact (hσ e' he').2
  have := eval_subst (fun e he => (hσ e he).1) M _ hnb
  rw [hself] at this
  exact this.symm

/-- A fact that `reachedCovered` accepts holds in the models that the check is about. -/
theorem holds_reachedCovered (hO : O.Sound) (hty : LogosTyping) (hS : SigOk S)
    (hP : ProgTy S P) {Γ : List (Id × Ty)} {env : Env} (hEnv : EnvTy Γ env) {r : TermSteps}
    (hbase : ∀ t ∈ r.base, ∃ q, HasTy S Γ q .BooleanType ∧ __eo_to_smt t = tr S Γ q ∧
      ∃ n v, eval O P n env q = .Ok v)
    (hSr : S = sigsOf r.equations) (hE : ∀ e ∈ r.equations, EqBody P S e) {t : Term}
    (h : reachedCovered r t = true) {assums : List Term}
    (hsub : extend r.base r.fresh ⊆ assums) :
    Holds (fun M => Agrees O P S Γ env M ∧ ∀ st ∈ r.fresh, st.Only M) assums t := by
  intro M ⟨hA, honly⟩ hsat
  have hM := ctx_of hty hA honly hsub hsat hbase
    (fun e he => ⟨sigOf e, (hE e he).1, bodyOf e, (hE e he).2⟩)
  have hJ := inv_calls hO hty hS hP hEnv hM
    (r.facts.filterMap (fun t => candOf (__eo_to_smt t)) ++
      (substituted r).filterMap fun q => candOf q.2)
  have hok : ∀ φ, (guardedEq r.equations (guardedCalls r) φ ||
      (pathsOf r).assumed (sigsOf r.equations) (guardedCalls r) φ) = true →
      __smtx_model_eval M φ = SmtValue.Boolean true := by
    intro φ hφ
    rcases Bool.or_eq_true_iff.mp hφ with hφ | hφ
    · exact guardedEq_sound hO hty hS hP hM hJ hφ
    · exact assumed_sound hO hty hS hP hM hE hJ (hSr ▸ hφ)
  simp only [reachedCovered, Bool.or_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem] at h
  rcases h with (h | h) | h
  · exact holds_covered hty (r := { r with equations := [] }) h hsub M
      (fun e he => by cases he) hsat
  · exact hok _ (by simpa using h)
  · simp only [List.mem_map, List.mem_filter] at h
    obtain ⟨q, ⟨hmem, hg⟩, rfl⟩ := h
    rw [eval_of_substituted hty hsub hsat hmem]
    exact hok _ (by simpa using hg)

end Steps

/-! ## The theorem -/

/-- What the check of `Inox/Source.lean` gives for a function of the equations, with its body. -/
theorem eqBody_of_check {eqs : List Equation} (hS : sigCheck (sigsOf eqs) = true)
    {e : Equation} (he : e ∈ eqs) (h : eqCheck (sigsOf eqs) e = true) :
    EqBody (programOf eqs) (sigsOf eqs) e := by
  simp only [eqCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hp, ht⟩, hk⟩, hi⟩ := h
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hk
  refine ⟨List.mem_map_of_mem he, lookup_funOf (sigOk_of_check hS).nodup e he, ?_, hp, ht⟩
  rw [kind_spec hk]
  exact infer_sound _ _ _ k (hi.trans hk)

/-- The query of an accepted certificate has no solution in the program of the certificate, when
the checks of `Inox/Source.lean` and of this file hold. Nothing is assumed of the calls of the
program: those that the evaluation of a solution goes through give values, and the checker has
checked that the certificate only uses the defining equations of such calls. -/
theorem no_solution_of_reached {O : Oracle} (sound : LogosSound) (hO : O.Sound)
    (hty : LogosTyping) {certificate : Logos.Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked) (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hsrc : sourceCheck r = true)
    (hreached : reachedCheck r = true) :
    ∀ vs, ¬ Solution O (programOf r.equations) (varsOf (sigsOf r.equations) r.base)
      (queryOf r.base) vs := by
  simp only [sourceCheck, Bool.and_eq_true] at hsrc
  obtain ⟨⟨⟨hS', hE'⟩, hΓ'⟩, hB'⟩ := hsrc
  simp only [reachedCheck, Bool.and_eq_true] at hreached
  obtain ⟨hapart, hall⟩ := hreached
  have hS := sigOk_of_check hS'
  have hPF := progFrag_of_check hS' hE'
  have hP := progTy_of_check hS' hE'
  have hE : ∀ e ∈ r.equations, EqBody (programOf r.equations) (sigsOf r.equations) e :=
    fun e he => eqBody_of_check hS' he (List.all_eq_true.mp hE' e he)
  have hΓ := varsFresh_of_check hΓ'
  have hB := baseFor_of_check hB'
  intro vs ⟨hvs, bs, hbs, hsol⟩
  obtain ⟨cd⟩ := Codes.nonempty
  obtain ⟨M0, hM0⟩ := Smtm.model_wf_nonvacuous
  have hEnv : EnvTy (varsOf (sigsOf r.equations) r.base) (Env.Env [] bs) := by
    intro x T hx w hw'
    obtain ⟨u, hu, huT⟩ := bind_lookup _ vs bs hbs hvs x T hx
    rw [lookup_var_det hw' hu]; exact huT
  have hbase : ∀ t ∈ r.base, ∃ q, HasTy (sigsOf r.equations)
      (varsOf (sigsOf r.equations) r.base) q .BooleanType ∧
      __eo_to_smt t = tr (sigsOf r.equations) (varsOf (sigsOf r.equations) r.base) q ∧
      ∃ n v, eval O (programOf r.equations) n (Env.Env [] bs) q = .Ok v := by
    intro t ht
    obtain ⟨q, hq, hqt, htr⟩ := hB t ht
    obtain ⟨n, hn⟩ := hsol q hq
    exact ⟨q, hqt, htr, n, _, hn⟩
  refine no_good_model_of_accept_only sound hty
    (Agrees O (programOf r.equations) (sigsOf r.equations) (varsOf (sigsOf r.equations) r.base)
      (Env.Env [] bs)) hAccept hr hcheck (keeps_of_apart hapart)
    (factsHold_of_except_sub
      (fun _ h _ hsub => holds_reachedCovered hO hty hS hP hEnv hbase rfl hE h hsub) (fun _ h => h)
      (factsHoldExcept_of_all hall)) _
    ⟨fun m => callsOk_star hO hty hS hPF hP M0 _ cd m, varsOk_star hΓ M0 cd hbs []⟩
    (satisfies_star hO hty hS hPF hP hΓ hM0 cd hvs hbs [] ?_)
  intro t ht
  obtain ⟨q, hq, hty', htr⟩ := hB t ht
  exact ⟨q, hty', htr, hsol q hq⟩

end Inox.Bridge
