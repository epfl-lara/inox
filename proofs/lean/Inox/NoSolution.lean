/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Bridge
import Inox.Codes
import Cpc.Proofs.TypePreservation.Nonvacuity

/-!
# An accepted certificate: the query has no solution, on a first-order fragment

The theorem of an UNSAT answer, for the first-order programs of the fragment of
`Inox/Bridge.lean` whose calls all give values (`Total`), given what the certificate doesn't yet
prove. `Total` leaves out the functions that don't terminate and those with a precondition that
can fail.

A solution of a query is an assignment of values to its free variables under which each of its
expressions evaluates to `true` with some fuel. From one, `Inox/Bridge.lean` gives a model: the
intended model `Model.star`, whose functions are the calls of the program, over the model that
gives the free variables their values. It satisfies:

- the defining equations, for all the values of their parameters (`good_star`), since every call
  gives a value: `goodOn_star` with a predicate that accepts every argument;
- the base clauses of the certificate, when each is the translation of an expression of the
  query (`satisfies_star`), by the agreement theorem `ev`.

`no_good_model_of_instances` says that an accepted certificate has no such model, so the query
has no solution (`no_solution`). What stays a hypothesis is listed with the theorem.
-/

namespace Inox.Bridge

open Eo
open SmtEval
open Smtm
open Inox.Fresh
open Inox.Extend
open Inox.Model
open Inox.Semantics

variable {O : Oracle} {P : Program} {D : List Data} {S : List Sig}

/-- The calls of the functions of `S` to values of the types of their parameters give values,
with some fuel: the functions terminate and are never stuck. A function whose `Assume` fails on
some values of its parameters, as one with a precondition does, is stuck on them, so it is not
`Total`. No real is among the parameters and the fields of the datatypes (`Discrete`): a real of
a model need not be a value of the semantics, which has the fractions. -/
def Total (O : Oracle) (P : Program) (D : List Data) (S : List Sig) : Prop :=
  Discrete D S ∧ ∀ s ∈ S, ∀ vs, List.Forall₂ (HasV D) vs (s.params.map Prod.snd) →
    ∃ n v, call O P n s.name [] [] vs = .Ok v

/-- When every call gives a value, the intended model satisfies the defining equations of the
program for all the values of their parameters. -/
theorem good_star (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hPF : ProgFrag P)
    (hP : ProgTy D S P) (htot : Total O P D S) {eqs : List Equation}
    (hE : ∀ e ∈ eqs, ∃ s ∈ S, EqFor P D S s e) (M0 N : SmtModel) (cd : Codes)
    (hw : model_wf (Model.star (defs D S) (interpOf O P D S) M0 cd N)) :
    Good eqs (Model.star (defs D S) (interpOf O P D S) M0 cd N) :=
  fun e he vs hvs =>
    (goodOn_star hO hty hS hPF hP htot.1 hE M0 N cd hw e he vs hvs).2
      (fun s hs _ us hus _ => htot.2 s hs us hus)

/-- The free variables `Γ` of a query: of types of the fragment, and named after no function. -/
structure VarsFresh (D : List Data) (S : List Sig) (Γ : List (Id × Ty)) : Prop where
  types : ∀ p ∈ Γ, FragTy D p.2
  fresh : ∀ p ∈ Γ, ∀ s ∈ S, p.1 ≠ s.name

/-- The model of the free variables `Γ` with the values `vs`: `M0`, with the constants of the
variables set to the values. -/
noncomputable def varsModel (D : List Data) (M0 : SmtModel) (Γ : List (Id × Ty)) (vs : List Value) :
    SmtModel :=
  setConsts M0 (bindValues (ptys D Γ) (vs.map (trV D)))

theorem wf_varsModel (hD : DataOk D) {M0 : SmtModel} (hM0 : model_wf M0) {Γ : List (Id × Ty)}
    {vs : List Value} (hvs : List.Forall₂ (HasV D) vs (Γ.map Prod.snd)) :
    model_wf (varsModel D M0 Γ vs) :=
  wf_setConsts hM0 (typed_bindValues (typed_map hD _ hvs))

/-- A variable of `Γ` is not the name of a function of `S`. -/
theorem lookup_defs_none {Γ : List (Id × Ty)} (hΓ : VarsFresh D S Γ) {x : Id} {T : Ty}
    (hx : Γ.lookup x = some T) (U : SmtType) : Model.lookup (defs D S) (nm x) U = none := by
  unfold Model.lookup
  apply List.find?_eq_none.mpr
  intro d hd h
  simp only [defs, List.mem_map] at hd
  obtain ⟨s, hs, rfl⟩ := hd
  simp only [Sig.toDef, Bool.and_eq_true, beq_iff_eq] at h
  have hmem : (x, T) ∈ Γ := by
    have := List.lookup_eq_some_iff.mp hx
    obtain ⟨l₁, l₂, rfl, _⟩ := this
    simp
  exact hΓ.fresh (x, T) hmem s hs (nm_inj h.1).symm

/-- The intended model over the model of the free variables gives the constants of the variables
their values. -/
theorem varsOk_star {Γ : List (Id × Ty)} (hΓ : VarsFresh D S Γ) (M0 : SmtModel) (cd : Codes)
    {vs : List Value} {bs : List Binding} (hbs : bind_all (Γ.map Prod.fst) vs = .Ok bs)
    (tenv : List TypeBinding) :
    VarsOk D Γ (Env.Env tenv bs)
      (Model.star (defs D S) (interpOf O P D S) M0 cd (varsModel D M0 Γ vs)) := by
  intro x T hx w hw
  show (Model.star (defs D S) (interpOf O P D S) M0 cd (varsModel D M0 Γ vs)).values
    (model_key (nm x) (trT D T)) = trV D w
  rw [star_undef (defs D S) (interpOf O P D S) M0 cd (varsModel D M0 Γ vs)
    (k := model_key (nm x) (trT D T)) (lookup_defs_none hΓ hx _)]
  show native_model_lookup (varsModel D M0 Γ vs) (nm x) (trT D T) = trV D w
  rw [varsModel, lookup_setConsts, bindingOf_var Γ vs bs hbs x T hx w hw]

/-- The intended model of a solution satisfies the clauses that are translations of the
expressions of the query: those that evaluate to `true`, with some fuel, under the values `vs` of
the free variables. -/
theorem satisfies_star (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S) (hPF : ProgFrag P)
    (hP : ProgTy D S P) {Γ : List (Id × Ty)} (hΓ : VarsFresh D S Γ) {M0 : SmtModel}
    (hM0 : model_wf M0) (cd : Codes) {vs : List Value} {bs : List Binding}
    (hvs : List.Forall₂ (HasV D) vs (Γ.map Prod.snd))
    (hbs : bind_all (Γ.map Prod.fst) vs = .Ok bs) (tenv : List TypeBinding)
    {base : List Term}
    (hbase : ∀ t ∈ base, ∃ q, HasTy D S Γ q .BooleanType ∧ __eo_to_smt t = tr D S Γ q ∧
      ∃ n, eval O P n (Env.Env tenv bs) q = .Ok (.BoolV true)) :
    Satisfies (Model.star (defs D S) (interpOf O P D S) M0 cd (varsModel D M0 Γ vs)) base := by
  have hw := wf_star (defs D S) (interpOf O P D S) M0 cd hM0 (wf_varsModel hS.data hM0 hvs) rfl
  refine ⟨hw, fun t ht => ?_⟩
  obtain ⟨q, hq, htr, n, hn⟩ := hbase t ht
  have hE : EnvTy D Γ (Env.Env tenv bs) := by
    intro x T hx w hw'
    obtain ⟨u, hu, huT⟩ := bind_lookup Γ vs bs hbs hvs x T hx
    rw [lookup_var_det hw' hu]; exact huT
  obtain ⟨_, hM⟩ := ev hO hty hS hP.2 (call_ty' hO hty hS hP n) hq _ _ hE hn
  rw [htr, hM _ hw (callsOk_star hO hty hS hPF hP M0 _ cd n) (varsOk_star hΓ M0 cd hbs tenv)]
  rfl

/-- The base clauses `base` are the translations of the expressions `qs` of a query over the
free variables `Γ`. -/
def BaseFor (D : List Data) (S : List Sig) (Γ : List (Id × Ty)) (qs : List Expr)
    (base : List Term) : Prop :=
  ∀ t ∈ base, ∃ q ∈ qs, HasTy D S Γ q .BooleanType ∧ __eo_to_smt t = tr D S Γ q

/-- The values `vs` of the free variables `Γ` are a solution of the query `qs`: each of its
expressions evaluates to `true`, with some fuel. -/
def Solution (O : Oracle) (P : Program) (D : List Data) (Γ : List (Id × Ty)) (qs : List Expr)
    (vs : List Value) : Prop :=
  List.Forall₂ (HasV D) vs (Γ.map Prod.snd) ∧
    ∃ bs, bind_all (Γ.map Prod.fst) vs = .Ok bs ∧
      ∀ q ∈ qs, ∃ n, eval O P n (Env.Env [] bs) q = .Ok (.BoolV true)

/-- The query has no solution: if the checker accepts a certificate whose defining equations are
those of the functions of `S` in `P` (`hE`) and whose base clauses are the translations of the
expressions `qs` of the query (`hbase`), for a program of the fragment whose calls all give
values (`htot`), then no values of the free variables make every expression of the query evaluate
to `true`, given that the facts that the check doesn't cover hold in the models of the defining
equations (`hfacts`). The model of a solution is over a well-formed model, which exists by the
theorem of Logos, with an injection of codes, which exists too (`Codes.nonempty`). -/
theorem no_solution (sound : LogosSound) (hO : O.Sound) (hty : LogosTyping) (hS : SigOk D S)
    (hPF : ProgFrag P) (hP : ProgTy D S P) (htot : Total O P D S)
    {certificate : Logos.Sexp} {checked : Checked} {r : TermSteps}
    (hAccept : accept certificate = .ok checked) (hr : termSteps checked = .ok r)
    (hcheck : r.check = true) (hkeeps : r.keeps = true)
    (hE : ∀ e ∈ r.equations, ∃ s ∈ S, EqFor P D S s e)
    {Γ : List (Id × Ty)} (hΓ : VarsFresh D S Γ) {qs : List Expr} (hbase : BaseFor D S Γ qs r.base)
    (hfacts : FactsHoldExcept (Good r.equations) r.covered (extend r.base r.fresh) r.facts) :
    ∀ vs, ¬ Solution O P D Γ qs vs := by
  intro vs ⟨hvs, bs, hbs, hsol⟩
  obtain ⟨cd⟩ := Codes.nonempty
  obtain ⟨M0, hM0⟩ := Smtm.model_wf_nonvacuous
  have hw := wf_star (defs D S) (interpOf O P D S) M0 cd hM0 (wf_varsModel hS.data hM0 hvs) rfl
  refine no_good_model_of_instances sound hty hAccept hr hcheck hkeeps hfacts _
    (good_star hO hty hS hPF hP htot hE M0 _ cd hw)
    (satisfies_star hO hty hS hPF hP hΓ hM0 cd hvs hbs [] ?_)
  intro t ht
  obtain ⟨q, hq, hty', htr⟩ := hbase t ht
  exact ⟨q, hty', htr, hsol q hq⟩

end Inox.Bridge
