/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Mono
import Inox.Model
import Inox.Sets
import Cpc.Proofs.TypePreservation.Helpers

/-!
# The types and the values of the bridge: integers, Booleans, reals, bit-vectors, datatypes, sets

`Inox/Bridge.lean` ties the semantics of Inox to the models of Logos on the expressions of some
types. This module gives the types (`FragTy`), their sorts (`trT`), their values (`HasV`) and
the values of the models that those are (`trV`), and proves what the bridge uses of them:

- a value of a type is a canonical value of its sort (`typed_trV`), and a canonical value of the
  sort of a type is that of a value of the type (`typed_inv1`);
- two values of a type are equal for the semantics when they are the same value of Logos
  (`value_eq_hasV`). A set of the semantics is the list of its elements, so two lists with the
  same elements are two values, that are equal for the semantics and are the same set of Logos
  (`trV_set_eq`, with `Inox/Sets.lean`);
- the operators of the sets of Logos, on the values (`trV_union` and the like).

A datatype of Inox is a datatype of SMT-LIB. `Data` gives the names of its constructors and of
their fields, which a datatype of Logos doesn't have: a constructor of Logos is the datatype
and an index. `DataOk` is what the datatypes `D` are asked: distinct names, fields of the types
of the bridge, and a declaration whose constructors have the sorts of these fields.
-/

namespace Inox.Bridge

open Eo
open SmtEval
open Smtm
open Inox.Fresh
open Inox.Extend
open Inox.Model
open Inox.Semantics

/-- The name of a constant: the codes of the characters of an identifier. -/
def nm (s : Id) : native_String := s.toList.map Char.toNat

theorem nm_inj {a b : Id} (h : nm a = nm b) : a = b :=
  String.toList_inj.mp (List.map_injective_iff.mpr (fun _ _ h => Char.toNat_inj.mp h) h)

/-! ## Datatypes -/

/-- A datatype: its name, the declaration of Logos that it is a datatype of, and its
constructors in the order of the declaration, each with the names and the types of its fields. -/
structure Data where
  name : Id
  decl : SmtDatatypeDecl
  ctors : List (Id × List (Id × Ty))

/-- The datatype named `s`. -/
def findData (D : List Data) (s : Id) : Option Data := D.find? (·.name == s)

theorem findData_spec {D : List Data} {s : Id} {d : Data} (h : findData D s = some d) :
    d ∈ D ∧ d.name = s := by
  have hp := List.find?_some h
  simp only [beq_iff_eq] at hp
  exact ⟨List.mem_of_find?_eq_some h, hp⟩

/-- The rational of a fraction. -/
def ratOf (n d : Int) : ℚ := (n : ℚ) / (d : ℚ)

/-- The sorts of the types of the bridge. -/
def trT (D : List Data) : Ty → SmtType
  | .IntegerType => .Int
  | .BooleanType => .Bool
  | .RealType => .Real
  | .BVType _ w => .BitVec w.toNat
  | .SetType A => .Set (trT D A)
  | .ADTType s [] =>
    match findData D s with
    | some d => .Datatype (nm s) d.decl
    | none => .None
  | _ => .None

/-- The types of the bridge. -/
def FragTy (D : List Data) : Ty → Prop
  | .IntegerType => True
  | .BooleanType => True
  | .RealType => True
  | .BVType _ w => 0 < w
  | .SetType A => FragTy D A
  | .ADTType s [] => (findData D s).isSome
  | _ => False

/-- The fields `fs` of a constructor, as Logos has them once the references to the datatypes of
its declaration are resolved. -/
def consT (D : List Data) : List (Id × Ty) → SmtDatatypeCons
  | [] => .unit
  | f :: fs => .cons (trT D f.2) (consT D fs)

/-- The constructors `cs` of a datatype, as Logos has them once resolved. -/
def sumT (D : List Data) : List (Id × List (Id × Ty)) → SmtDatatype
  | [] => .null
  | c :: cs => .sum (consT D c.2) (sumT D cs)

/-- What is asked of the datatypes `D`. -/
structure DataOk (D : List Data) : Prop where
  /-- The datatypes have distinct names. -/
  nodup : (D.map (·.name)).Nodup
  /-- The constructors have distinct names, over all the datatypes. -/
  ctors : (D.flatMap fun d => d.ctors.map (·.1)).Nodup
  /-- The fields have distinct names, over all the constructors. -/
  sels : (D.flatMap fun d => d.ctors.flatMap fun c => c.2.map (·.1)).Nodup
  /-- The fields are of types of the bridge. -/
  fields : ∀ d ∈ D, ∀ c ∈ d.ctors, ∀ f ∈ c.2, FragTy D f.2
  /-- The declaration of a datatype gives it the constructors of `ctors`. -/
  resolved : ∀ d ∈ D,
    __smtx_dt_resolve (__smtx_dd_lookup (nm d.name) d.decl) d.decl = sumT D d.ctors
  /-- The sort of a datatype is well formed. -/
  wf : ∀ d ∈ D, __smtx_type_wf (.Datatype (nm d.name) d.decl) = true

theorem findData_of_mem {D : List Data} (hD : (D.map (·.name)).Nodup) {d : Data} (hd : d ∈ D) :
    findData D d.name = some d := by
  induction D with
  | nil => cases hd
  | cons a D ih =>
    rw [List.map_cons, List.nodup_cons] at hD
    rcases List.mem_cons.mp hd with rfl | hd'
    · simp [findData]
    · have hne : a.name ≠ d.name := fun h => hD.1 (List.mem_map.mpr ⟨d, hd', h.symm⟩)
      have := ih hD.2 hd'
      simp only [findData] at this ⊢
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact this

theorem trT_data {D : List Data} (hD : DataOk D) {d : Data} (hd : d ∈ D) :
    trT D (.ADTType d.name []) = .Datatype (nm d.name) d.decl := by
  simp only [trT, findData_of_mem hD.nodup hd]

theorem fragTy_data {D : List Data} (hD : DataOk D) {d : Data} (hd : d ∈ D) :
    FragTy D (.ADTType d.name []) := by
  simp only [FragTy, findData_of_mem hD.nodup hd, Option.isSome_some]

/-- A type of the bridge is of integers, of Booleans, of reals, of bit-vectors, a datatype of
`D`, or of sets of a type of the bridge. -/
theorem fragTy_cases {D : List Data} {T : Ty} (h : FragTy D T) :
    T = .IntegerType ∨ T = .BooleanType ∨ T = .RealType ∨ (∃ s w, 0 < w ∧ T = .BVType s w) ∨
      (∃ d ∈ D, T = .ADTType d.name []) ∨ ∃ A, FragTy D A ∧ T = .SetType A := by
  cases T
  case IntegerType => exact .inl rfl
  case BooleanType => exact .inr (.inl rfl)
  case RealType => exact .inr (.inr (.inl rfl))
  case BVType s w => exact .inr (.inr (.inr (.inl ⟨s, w, h, rfl⟩)))
  case SetType A => exact .inr (.inr (.inr (.inr (.inr ⟨A, h, rfl⟩))))
  case ADTType s args =>
    cases args with
    | nil =>
      simp only [FragTy] at h
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨hm, rfl⟩ := findData_spec hd
      exact .inr (.inr (.inr (.inr (.inl ⟨d, hm, rfl⟩))))
    | cons _ _ => exact absurd h id
  all_goals exact absurd h id

/-- The types of the bridge, by induction: a property of the base types that holds of the sets
of a type where it holds, holds of all. -/
theorem fragTy_induct {D : List Data} {motive : Ty → Prop} (int : motive .IntegerType)
    (bool : motive .BooleanType) (real : motive .RealType)
    (bv : ∀ s w, 0 < w → motive (.BVType s w)) (data : ∀ d ∈ D, motive (.ADTType d.name []))
    (set : ∀ A, FragTy D A → motive A → motive (.SetType A)) : ∀ T, FragTy D T → motive T
  | .IntegerType, _ => int
  | .BooleanType, _ => bool
  | .RealType, _ => real
  | .BVType s w, h => bv s w h
  | .SetType A, h => set A h (fragTy_induct int bool real bv data set A h)
  | .ADTType s [], h => by
    simp only [FragTy] at h
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨hm, rfl⟩ := findData_spec hd
    exact data d hm
  | .ADTType _ (_ :: _), h | .UnitType, h | .CharType, h | .StringType, h | .FPType _ _, h
  | .RoundingModeType, h | .TypeParameter _, h | .TupleType _, h | .BagType _, h
  | .MapType _ _, h | .FunctionType _ _, h | .RefinementType _ _ _, h | .PropType, h
  | .PiType _ _, h | .SigmaType _ _, h => absurd h id

theorem trT_component {D : List Data} (hD : DataOk D) {T : Ty} (h : FragTy D T) :
    __smtx_type_wf_component (trT D T) = true := by
  refine fragTy_induct (motive := fun T => __smtx_type_wf_component (trT D T) = true)
    ?_ ?_ ?_ ?_ ?_ ?_ T h
  · simp [trT, __smtx_type_wf_component, __smtx_type_wf_rec, native_and]
  · simp [trT, __smtx_type_wf_component, __smtx_type_wf_rec, native_and]
  · simp [trT, __smtx_type_wf_component, __smtx_type_wf_rec, native_and, __smtx_inhabited_type]
  · intro s w _
    simp [trT, __smtx_type_wf_component, __smtx_type_wf_rec, native_and, __smtx_inhabited_type]
  · intro d hd
    rw [trT_data hD hd]
    have := hD.wf d hd
    simpa only [__smtx_type_wf] using this
  · intro A _ ih
    simp only [__smtx_type_wf_component, native_and, Bool.and_eq_true] at ih
    simp [trT, __smtx_type_wf_component, __smtx_type_wf_rec, native_and, ih.1, ih.2,
      __smtx_inhabited_type]

theorem trT_wf {D : List Data} (hD : DataOk D) {T : Ty} (h : FragTy D T) :
    __smtx_type_wf (trT D T) = true := by
  rcases fragTy_cases h with
    rfl | rfl | rfl | ⟨sg, w, _, rfl⟩ | ⟨d, hd, rfl⟩ | ⟨A, _, rfl⟩
  · simp only [trT, __smtx_type_wf]; exact trT_component (T := .IntegerType) hD h
  · simp only [trT, __smtx_type_wf]; exact trT_component (T := .BooleanType) hD h
  · simp only [trT, __smtx_type_wf]; exact trT_component (T := .RealType) hD h
  · simp only [trT, __smtx_type_wf]; exact trT_component (T := .BVType sg w) hD h
  · rw [trT_data hD hd]; exact hD.wf d hd
  · simp only [trT, __smtx_type_wf]; exact trT_component (T := .SetType A) hD h

theorem trT_ne {D : List Data} (hD : DataOk D) {T : Ty} (h : FragTy D T) : trT D T ≠ .None := by
  rcases fragTy_cases h with
    rfl | rfl | rfl | ⟨sg, w, _, rfl⟩ | ⟨d, hd, rfl⟩ | ⟨A, _, rfl⟩
  · simp [trT]
  · simp [trT]
  · simp [trT]
  · simp [trT]
  · rw [trT_data hD hd]; simp
  · simp [trT]

/-! ## Constructors -/

/-- The index and the value of the first entry of `cs` named `c`. -/
def lookupIdx {α : Type} (c : Id) : List (Id × α) → Option (Nat × α)
  | [] => none
  | k :: cs => if k.1 = c then some (0, k.2) else (lookupIdx c cs).map fun r => (r.1 + 1, r.2)

theorem lookupIdx_spec {α : Type} {c : Id} : ∀ {cs : List (Id × α)} {i : Nat} {a : α},
    lookupIdx c cs = some (i, a) → cs[i]? = some (c, a)
  | [], _, _, h => by cases h
  | k :: cs, i, a, h => by
    simp only [lookupIdx] at h
    split at h
    · rename_i hk
      cases h
      obtain ⟨k1, k2⟩ := k
      cases hk
      rfl
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨r, hr, rfl, rfl⟩ := h
      simpa using lookupIdx_spec (cs := cs) hr

theorem lookupIdx_of {α : Type} {c : Id} : ∀ {cs : List (Id × α)}, (cs.map (·.1)).Nodup →
    ∀ {i : Nat} {a : α}, cs[i]? = some (c, a) → lookupIdx c cs = some (i, a)
  | [], _, _, _, h => by simp at h
  | k :: cs, hn, i, a, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [lookupIdx]
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      have hne : k.1 ≠ c := fun e =>
        hn.1 (List.mem_map.mpr ⟨(c, a), List.mem_of_getElem? h, e.symm⟩)
      simp only [lookupIdx, hne, ↓reduceIte, lookupIdx_of hn.2 h, Option.map_some]

/-- The index and the fields of the constructor `c` in the datatype `d`. -/
def ctorIn (d : Data) (c : Id) : Option (Nat × List (Id × Ty)) := lookupIdx c d.ctors

/-- The datatype, the index and the fields of the constructor `c`. -/
def findCtor (D : List Data) (c : Id) : Option (Data × Nat × List (Id × Ty)) :=
  D.findSome? fun d => (ctorIn d c).map fun k => (d, k)

theorem findCtor_spec {D : List Data} {c : Id} {d : Data} {i : Nat} {fs : List (Id × Ty)}
    (h : findCtor D c = some (d, i, fs)) : d ∈ D ∧ d.ctors[i]? = some (c, fs) := by
  obtain ⟨d', hd', hk⟩ := List.exists_of_findSome?_eq_some h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hk
  obtain ⟨k, hk, rfl, rfl⟩ := hk
  exact ⟨hd', lookupIdx_spec hk⟩

theorem ctorIn_of {d : Data} (hn : (d.ctors.map (·.1)).Nodup) {c : Id} {i : Nat}
    {fs : List (Id × Ty)} (h : d.ctors[i]? = some (c, fs)) : ctorIn d c = some (i, fs) :=
  lookupIdx_of hn h

theorem ctors_nodup {D : List Data} (hD : DataOk D) {d : Data} (hd : d ∈ D) :
    (d.ctors.map (·.1)).Nodup := by
  have := hD.ctors
  rw [List.nodup_flatMap] at this
  exact this.1 d hd

/-- The constructor of index `i` of a datatype of `D` is found by its name. -/
theorem findCtor_of {D : List Data} (hD : DataOk D) {d : Data} (hd : d ∈ D) {c : Id} {i : Nat}
    {fs : List (Id × Ty)} (h : d.ctors[i]? = some (c, fs)) : findCtor D c = some (d, i, fs) := by
  have hcm : c ∈ d.ctors.map (·.1) :=
    List.mem_map.mpr ⟨(c, fs), List.mem_of_getElem? h, rfl⟩
  cases hf : findCtor D c with
  | none =>
    rw [findCtor, List.findSome?_eq_none_iff] at hf
    have := hf d hd
    rw [ctorIn_of (ctors_nodup hD hd) h] at this
    cases this
  | some r =>
    obtain ⟨d', i', fs'⟩ := r
    obtain ⟨hd', h'⟩ := findCtor_spec hf
    have hcm' : c ∈ d'.ctors.map (·.1) :=
      List.mem_map.mpr ⟨(c, fs'), List.mem_of_getElem? h', rfl⟩
    have hdd : d' = d := by
      by_contra hne
      have hdis := (List.nodup_flatMap.mp hD.ctors).2
      rcases List.mem_iff_getElem.mp hd with ⟨a, ha, rfl⟩
      rcases List.mem_iff_getElem.mp hd' with ⟨b, hb, hbe⟩
      have hab : a ≠ b := fun e => hne (by subst e; exact hbe.symm)
      rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
      · have := List.pairwise_iff_getElem.mp hdis a b ha hb hlt
        exact this hcm (hbe ▸ hcm')
      · have := List.pairwise_iff_getElem.mp hdis b a hb ha hlt
        exact this (hbe ▸ hcm') hcm
    subst hdd
    have := ctorIn_of (ctors_nodup hD hd) h
    have h2 := ctorIn_of (ctors_nodup hD hd) h'
    rw [this] at h2
    cases h2
    rfl

/-! ## Values -/

mutual
/-- The values of the bridge, as SMT values: a value of a datatype is its constructor applied to
the values of its fields, one at a time, and a set is the set of Logos of the list of its
elements. -/
noncomputable def trV (D : List Data) : Value → SmtValue
  | .IntV i => .Numeral i
  | .BoolV b => .Boolean b
  | .RealV n d => .Real (native_rat_to_real (ratOf n d))
  | .BVV _ w x => .Binary w x
  | .SetV A xs => .Set (setOf (trT D A) (trVl D xs))
  | .ADTV c vs =>
    match findCtor D c with
    | some (d, i, _) => trVs D (.DtCons (nm d.name) d.decl i) vs
    | none => .NotValue
  | _ => .NotValue

/-- The value `f` applied to the values `vs`, one at a time. -/
noncomputable def trVs (D : List Data) (f : SmtValue) : List Value → SmtValue
  | [] => f
  | v :: vs => trVs D (.Apply f (trV D v)) vs

/-- The values `vs`, as SMT values. -/
noncomputable def trVl (D : List Data) : List Value → List SmtValue
  | [] => []
  | v :: vs => trV D v :: trVl D vs
end

theorem trVl_eq (D : List Data) : ∀ vs : List Value, trVl D vs = vs.map (trV D)
  | [] => rfl
  | v :: vs => by rw [trVl, trVl_eq D vs]; rfl

mutual
/-- `v` is a value of type `T`, a type of the bridge. -/
def HasV (D : List Data) : Value → Ty → Prop
  | .IntV _, .IntegerType => True
  | .BoolV _, .BooleanType => True
  | .RealV n d, .RealType => ∃ q : ℚ, n = q.num ∧ d = q.den
  | .BVV s' w' x, .BVType s w => s' = s ∧ w' = w ∧ 0 < w ∧ 0 ≤ x ∧ x < 2 ^ w.toNat
  | .ADTV c vs, .ADTType s [] =>
    ∃ d i fs, findCtor D c = some (d, i, fs) ∧ d.name = s ∧ HasVs D vs (fs.map Prod.snd)
  | .SetV B xs, .SetType A => B = A ∧ FragTy D A ∧ HasVall D xs A
  | _, _ => False

/-- The values `vs` are of the types `Ts`. -/
def HasVs (D : List Data) : List Value → List Ty → Prop
  | [], [] => True
  | v :: vs, T :: Ts => HasV D v T ∧ HasVs D vs Ts
  | _, _ => False

/-- The values `vs` are all of the type `T`. -/
def HasVall (D : List Data) : List Value → Ty → Prop
  | [], _ => True
  | v :: vs, T => HasV D v T ∧ HasVall D vs T
end

theorem hasVall_iff {D : List Data} {T : Ty} : ∀ {vs : List Value},
    HasVall D vs T ↔ ∀ v ∈ vs, HasV D v T
  | [] => by simp [HasVall]
  | v :: vs => by simp [HasVall, hasVall_iff (vs := vs)]

theorem hasVs_iff {D : List Data} : ∀ {vs : List Value} {Ts : List Ty},
    HasVs D vs Ts ↔ List.Forall₂ (HasV D) vs Ts
  | [], [] => by simp [HasVs]
  | [], _ :: _ => by simp [HasVs]
  | _ :: _, [] => by simp [HasVs]
  | v :: vs, T :: Ts => by simp [HasVs, hasVs_iff (vs := vs) (Ts := Ts)]

/-- A value of a type of bit-vectors is of the sign and of the width of the type, and in its
range. -/
theorem hasV_bv_inv {D : List Data} {s : Bool} {w' x : Int} {T : Ty}
    (h : HasV D (.BVV s w' x) T) :
    T = .BVType s w' ∧ 0 < w' ∧ 0 ≤ x ∧ x < 2 ^ w'.toNat := by
  cases T <;> try (simp [HasV] at h; done)
  case BVType t w =>
    simp only [HasV] at h
    obtain ⟨rfl, rfl, h⟩ := h
    exact ⟨rfl, h⟩

/-- Closes a goal with a value `h` of a type that has no such value. -/
macro "no_hasV " h:ident : tactic =>
  `(tactic| first
    | (have h' := (hasV_bv_inv $h).1; cases h'; done)
    | (simp [HasV] at $h:ident; done))

theorem hasV_bv {D : List Data} {v : Value} {s : Bool} {w : Int} (h : HasV D v (.BVType s w)) :
    ∃ x, v = .BVV s w x ∧ 0 < w ∧ 0 ≤ x ∧ x < 2 ^ w.toNat := by
  cases v <;> try (simp [HasV] at h; done)
  case BVV t w' x =>
    obtain ⟨hT, hr⟩ := hasV_bv_inv h
    cases hT
    exact ⟨x, rfl, hr⟩

theorem hasV_bv_of {D : List Data} {s : Bool} {w x : Int} (hw : 0 < w) (h0 : 0 ≤ x)
    (hx : x < 2 ^ w.toNat) : HasV D (.BVV s w x) (.BVType s w) := by
  simp only [HasV]; exact ⟨trivial, trivial, hw, h0, hx⟩

/-- A value of the reals is a fraction in lowest terms with a positive denominator. -/
theorem hasV_real {D : List Data} {v : Value} (h : HasV D v .RealType) :
    ∃ q : ℚ, v = .RealV q.num q.den := by
  cases v <;> try no_hasV h
  case RealV n d =>
    simp only [HasV] at h
    obtain ⟨q, rfl, rfl⟩ := h
    exact ⟨q, rfl⟩

theorem hasV_real_of {D : List Data} (q : ℚ) : HasV D (.RealV q.num q.den) .RealType := by
  simp only [HasV]; exact ⟨q, rfl, rfl⟩

theorem ratOf_num_den (q : ℚ) : ratOf q.num q.den = q := by
  simp [ratOf, Rat.num_div_den]

theorem hasV_int {D : List Data} {v : Value} (h : HasV D v .IntegerType) : ∃ i, v = .IntV i := by
  cases v <;> first | exact ⟨_, rfl⟩ | no_hasV h

theorem hasV_bool {D : List Data} {v : Value} (h : HasV D v .BooleanType) :
    ∃ b, v = .BoolV b := by
  cases v <;> first | exact ⟨_, rfl⟩ | no_hasV h

/-- A value of a datatype is a constructor of it with values of the types of its fields. -/
theorem hasV_data {D : List Data} {v : Value} {s : Id} (h : HasV D v (.ADTType s [])) :
    ∃ c vs d i fs, v = .ADTV c vs ∧ findCtor D c = some (d, i, fs) ∧ d.name = s ∧
      List.Forall₂ (HasV D) vs (fs.map Prod.snd) := by
  cases v <;> try no_hasV h
  case ADTV c vs =>
    simp only [HasV] at h
    obtain ⟨d, i, fs, hc, hs, hvs⟩ := h
    exact ⟨c, vs, d, i, fs, rfl, hc, hs, hasVs_iff.mp hvs⟩

theorem hasV_adt {D : List Data} {c : Id} {vs : List Value} {d : Data} {i : Nat}
    {fs : List (Id × Ty)} (hc : findCtor D c = some (d, i, fs))
    (hvs : List.Forall₂ (HasV D) vs (fs.map Prod.snd)) :
    HasV D (.ADTV c vs) (.ADTType d.name []) := by
  simp only [HasV]
  exact ⟨d, i, fs, hc, rfl, hasVs_iff.mpr hvs⟩

/-- A value of a type of sets is a set of that type, of elements of the type of its elements. -/
theorem hasV_set {D : List Data} {v : Value} {A : Ty} (h : HasV D v (.SetType A)) :
    ∃ xs, v = .SetV A xs ∧ FragTy D A ∧ ∀ x ∈ xs, HasV D x A := by
  cases v <;> try no_hasV h
  case SetV B xs =>
    simp only [HasV] at h
    obtain ⟨rfl, hA, hxs⟩ := h
    exact ⟨xs, rfl, hA, hasVall_iff.mp hxs⟩

theorem hasV_set_of {D : List Data} {A : Ty} {xs : List Value} (hA : FragTy D A)
    (h : ∀ x ∈ xs, HasV D x A) : HasV D (.SetV A xs) (.SetType A) := by
  simp only [HasV]
  exact ⟨by trivial, hA, hasVall_iff.mpr h⟩

theorem hasV_fragTy {D : List Data} {v : Value} {T : Ty} (h : HasV D v T) : FragTy D T := by
  cases T <;> try (cases v <;> no_hasV h; done)
  case IntegerType => trivial
  case BooleanType => trivial
  case RealType => trivial
  case BVType s w =>
    obtain ⟨x, rfl, hw, _⟩ := hasV_bv h
    exact hw
  case ADTType s args =>
    cases args with
    | nil =>
      obtain ⟨c, vs, d, i, fs, _, hc, rfl, _⟩ := hasV_data h
      simp only [FragTy, findData]
      exact List.find?_isSome.mpr ⟨d, (findCtor_spec hc).1, by simp⟩
    | cons _ _ =>
      cases v <;> no_hasV h
  case SetType A =>
    obtain ⟨xs, rfl, hA, _⟩ := hasV_set h
    exact hA

/-! ## The sorts of the constructors -/

/-- The sorts of the fields of a constructor. -/
def consFields : SmtDatatypeCons → List SmtType
  | .unit => []
  | .cons U c => U :: consFields c

/-- The sorts of the fields of the constructor of index `i`. -/
def ctorFields : SmtDatatype → Nat → Option (List SmtType)
  | .null, _ => none
  | .sum c _, 0 => some (consFields c)
  | .sum _ d, i + 1 => ctorFields d i

/-- The sort of a constructor of the sort `T` that still takes fields of the sorts `Us`. -/
def chainT (T : SmtType) : List SmtType → SmtType
  | [] => T
  | U :: Us => .DtcAppType U (chainT T Us)

theorem chainT_ne {T : SmtType} (h : T ≠ .None) : ∀ Us : List SmtType, chainT T Us ≠ .None
  | [] => h
  | _ :: _ => by simp [chainT]

theorem cons_value_rec_zero (T : SmtType) (d : SmtDatatype) : ∀ c : SmtDatatypeCons,
    __smtx_typeof_dt_cons_value_rec T (.sum c d) 0 = chainT T (consFields c)
  | .unit => by simp [__smtx_typeof_dt_cons_value_rec, consFields, chainT]
  | .cons U c => by
    simp [__smtx_typeof_dt_cons_value_rec, consFields, chainT, cons_value_rec_zero T d c]

theorem cons_value_rec (T : SmtType) : ∀ (d : SmtDatatype) (i : Nat),
    __smtx_typeof_dt_cons_value_rec T d i = ((ctorFields d i).map (chainT T)).getD .None
  | .null, i => by cases i <;> simp [__smtx_typeof_dt_cons_value_rec, ctorFields]
  | .sum c d, 0 => by simp [ctorFields, cons_value_rec_zero]
  | .sum c d, i + 1 => by
    simp [__smtx_typeof_dt_cons_value_rec, ctorFields, cons_value_rec T d i]

theorem cons_rec_zero (T : SmtType) (d : SmtDatatype) : ∀ c : SmtDatatypeCons,
    __smtx_typeof_dt_cons_rec T (.sum c d) 0 = chainT T (consFields c)
  | .unit => by simp [__smtx_typeof_dt_cons_rec, consFields, chainT]
  | .cons U c => by
    simp [__smtx_typeof_dt_cons_rec, consFields, chainT, cons_rec_zero T d c]

theorem cons_rec (T : SmtType) : ∀ (d : SmtDatatype) (i : Nat),
    __smtx_typeof_dt_cons_rec T d i = ((ctorFields d i).map (chainT T)).getD .None
  | .null, i => by cases i <;> simp [__smtx_typeof_dt_cons_rec, ctorFields]
  | .sum c d, 0 => by simp [ctorFields, cons_rec_zero]
  | .sum c d, i + 1 => by
    simp [__smtx_typeof_dt_cons_rec, ctorFields, cons_rec T d i]

theorem consFields_consT (D : List Data) : ∀ fs : List (Id × Ty),
    consFields (consT D fs) = fs.map fun f => trT D f.2
  | [] => rfl
  | f :: fs => by simp [consT, consFields, consFields_consT D fs]

theorem ctorFields_sumT (D : List Data) : ∀ (cs : List (Id × List (Id × Ty))) (i : Nat),
    ctorFields (sumT D cs) i = (cs[i]?).map fun k => k.2.map fun f => trT D f.2
  | [], i => by simp [sumT, ctorFields]
  | c :: cs, 0 => by simp [sumT, ctorFields, consFields_consT]
  | c :: cs, i + 1 => by simp [sumT, ctorFields, ctorFields_sumT D cs i]

/-- The sorts of the fields of the constructor of index `i` of a datatype of `D`. -/
theorem ctorFields_data {D : List Data} (hD : DataOk D) {d : Data} (hd : d ∈ D) (i : Nat) :
    ctorFields (__smtx_dt_resolve (__smtx_dd_lookup (nm d.name) d.decl) d.decl) i =
      (d.ctors[i]?).map fun k => k.2.map fun f => trT D f.2 := by
  rw [hD.resolved d hd, ctorFields_sumT]

/-! ## Applications of constructors -/

/-- The value `f` applied to the values `as`, one at a time. -/
def applyVs (f : SmtValue) (as : List SmtValue) : SmtValue := as.foldl .Apply f

theorem trVs_eq (D : List Data) : ∀ (vs : List Value) (f : SmtValue),
    trVs D f vs = applyVs f (vs.map (trV D))
  | [], f => by simp [trVs, applyVs]
  | v :: vs, f => by
    rw [trVs, trVs_eq D vs]
    simp [applyVs]

theorem applyVs_snoc (f : SmtValue) (as : List SmtValue) (a : SmtValue) :
    applyVs f (as ++ [a]) = .Apply (applyVs f as) a := by
  simp [applyVs]

theorem typeof_applyVs {T0 : SmtType} : ∀ (as : List SmtValue) (Us : List SmtType)
    (f : SmtValue), __smtx_typeof_value f = chainT T0 Us →
    List.Forall₂ (fun a U => __smtx_typeof_value a = U ∧ U ≠ .None) as Us →
    __smtx_typeof_value (applyVs f as) = T0
  | [], [], f, hf, _ => hf
  | a :: as, U :: Us, f, hf, .cons ⟨ha, hU⟩ hs => by
    apply typeof_applyVs as Us (.Apply f a) _ hs
    simp [__smtx_typeof_value, __smtx_typeof_apply_value, __smtx_typeof_guard, native_ite,
      native_Teq, hf, ha, hU, chainT]

theorem canonical_applyVs (uc : SmtUSortDom) : ∀ (as : List SmtValue) (f : SmtValue),
    __smtx_value_canonical uc f = true → (∀ a ∈ as, __smtx_value_canonical uc a = true) →
    __smtx_value_canonical uc (applyVs f as) = true
  | [], f, hf, _ => hf
  | a :: as, f, hf, h => by
    apply canonical_applyVs uc as (.Apply f a) _ (fun b hb => h b (.tail _ hb))
    simp [__smtx_value_canonical, native_and, hf, h a (.head _)]

theorem head_applyVs : ∀ (as : List SmtValue) (f : SmtValue),
    __smtx_apply_head_value (applyVs f as) = __smtx_apply_head_value f
  | [], _ => rfl
  | a :: as, f => by
    have := head_applyVs as (.Apply f a)
    simpa [applyVs, __smtx_apply_head_value] using this

theorem data_eq_of_name {D : List Data} (hD : (D.map (·.name)).Nodup) {d d' : Data}
    (hd : d ∈ D) (hd' : d' ∈ D) (h : d.name = d'.name) : d = d' := by
  have h1 := findData_of_mem hD hd
  have h2 := findData_of_mem hD hd'
  rw [h, h2] at h1
  exact (Option.some.inj h1).symm

/-! ## The values of the types are values of their sorts -/

/-- What the SMT value of a value `v` of type `T` is: a canonical value of the sort of `T`. -/
def ValueOk (D : List Data) (uc : SmtUSortDom) (v : Value) (T : Ty) : Prop :=
  __smtx_typeof_value (trV D v) = trT D T ∧ __smtx_value_canonical uc (trV D v) = true

theorem agrees_adt {D : List Data} (hD : DataOk D) (uc : SmtUSortDom) {c : Id}
    {vs : List Value} {d : Data} {i : Nat} {fs : List (Id × Ty)}
    (hc : findCtor D c = some (d, i, fs))
    (ih : List.Forall₂ (ValueOk D uc) vs (fs.map Prod.snd)) :
    ValueOk D uc (.ADTV c vs) (.ADTType d.name []) := by
  obtain ⟨hd, hi⟩ := findCtor_spec hc
  have hfs : ∀ f ∈ fs, FragTy D f.2 := hD.fields d hd (c, fs) (List.mem_of_getElem? hi)
  simp only [ValueOk, trV, hc, trVs_eq, trT_data hD hd]
  refine ⟨?_, ?_⟩
  · apply typeof_applyVs (Us := fs.map fun f => trT D f.2)
    · simp only [__smtx_typeof_value, cons_value_rec, ctorFields_data hD hd, hi, Option.map_some,
        Option.getD_some]
    · clear hi hc
      induction fs generalizing vs with
      | nil => cases ih; exact .nil
      | cons f fs ihf =>
        cases ih with
        | cons h hs =>
          exact .cons ⟨h.1, trT_ne hD (hfs f (.head _))⟩
            (ihf hs fun g hg => hfs g (.tail _ hg))
  · apply canonical_applyVs uc _ _ (by simp [__smtx_value_canonical])
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨v, hv, rfl⟩ := ha
    clear hi hc hfs
    generalize fs.map Prod.snd = Ts at ih
    induction ih with
    | nil => cases hv
    | cons h _ ihf =>
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact h.2
      · exact ihf hv'

theorem forall₂_imp_mem {α β : Type} {R Q : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → (∀ a ∈ l, ∀ b, R a b → Q a b) → List.Forall₂ Q l m
  | [], [], _, _ => .nil
  | _ :: _, _ :: _, .cons h hs, f =>
    .cons (f _ (.head _) _ h) (forall₂_imp_mem hs fun a ha => f a (.tail _ ha))

theorem agrees_k {D : List Data} (hD : DataOk D) (uc : SmtUSortDom) :
    ∀ (k : Nat) (v : Value) (T : Ty), sizeOf v < k → HasV D v T → ValueOk D uc v T
  | 0, _, _, h, _ => by omega
  | k + 1, v, T, hk, h => by
    rcases fragTy_cases (hasV_fragTy h) with
      rfl | rfl | rfl | ⟨s, w, _, rfl⟩ | ⟨d, hd, rfl⟩ | ⟨A, hA, rfl⟩
    · obtain ⟨i, rfl⟩ := hasV_int h
      exact ⟨rfl, rfl⟩
    · obtain ⟨b, rfl⟩ := hasV_bool h
      exact ⟨rfl, rfl⟩
    · obtain ⟨q, rfl⟩ := hasV_real h
      exact ⟨rfl, rfl⟩
    · obtain ⟨x, rfl, hw, h0, hx⟩ := hasV_bv h
      have hp : native_int_pow2 w = 2 ^ w.toNat := by
        simp [native_int_pow2, native_zexp_total, Int.not_lt.mpr (Int.le_of_lt hw)]
      have hm : native_zeq x (native_mod_total x (native_int_pow2 w)) = true := by
        simp [native_zeq, native_mod_total, hp, Int.emod_eq_of_lt h0 hx]
      have hz : native_zleq 0 w = true := by simp [native_zleq, Int.le_of_lt hw]
      refine ⟨?_, ?_⟩
      · simp [trV, trT, __smtx_typeof_value, native_ite, native_and, hz, hm, native_int_to_nat]
      · simp [trV, __smtx_value_canonical, native_ite, hz, hm]
    · obtain ⟨c, vs, d', i, fs, rfl, hc, hs, hvs⟩ := hasV_data h
      rw [← hs]
      exact agrees_adt hD uc hc (forall₂_imp_mem hvs fun a ha b hab => agrees_k hD uc k a b (by
        have := List.sizeOf_lt_of_mem ha
        simp only [Value.ADTV.sizeOf_spec] at hk
        omega) hab)
    · obtain ⟨xs, rfl, _, hxs⟩ := hasV_set h
      have hall : ∀ w ∈ xs.map (trV D), __smtx_typeof_value w = trT D A ∧
          __smtx_value_canonical uc w = true := by
        intro w hw
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
        exact agrees_k hD uc k x A (by
          have := List.sizeOf_lt_of_mem hx
          simp only [Value.SetV.sizeOf_spec] at hk
          omega) (hxs x hx)
      simp only [ValueOk, trV, trT, trVl_eq]
      refine ⟨?_, setOf_value_canonical uc _ _ fun w hw => (hall w hw).2⟩
      simp only [__smtx_typeof_value, setOf_typeof _ _ fun w hw => (hall w hw).1,
        __smtx_map_to_set_type]

theorem agrees_trV {D : List Data} (hD : DataOk D) (uc : SmtUSortDom) (v : Value) (T : Ty)
    (h : HasV D v T) : ValueOk D uc v T :=
  agrees_k hD uc _ v T (Nat.lt_succ_self _) h

theorem typed_trV {D : List Data} (hD : DataOk D) (M : SmtModel) (s : native_String) {v : Value}
    {T : Ty} (h : HasV D v T) : Typed M (s, trT D T) (trV D v) :=
  ⟨(agrees_trV hD M.usortDom v T h).1, (agrees_trV hD M.usortDom v T h).2⟩

theorem trV_ne {D : List Data} (hD : DataOk D) {v : Value} {T : Ty} (h : HasV D v T) :
    trV D v ≠ .NotValue := by
  intro e
  have := (agrees_trV hD default v T h).1
  rw [e] at this
  exact trT_ne hD (hasV_fragTy h) this.symm

theorem applyVs_inj : ∀ (as bs : List SmtValue) (f g : SmtValue), as.length = bs.length →
    applyVs f as = applyVs g bs → f = g ∧ as = bs
  | [], [], _, _, _, h => ⟨h, rfl⟩
  | a :: as, b :: bs, f, g, hl, h => by
    obtain ⟨h1, h2⟩ := applyVs_inj as bs (.Apply f a) (.Apply g b) (by simpa using hl)
      (by simpa [applyVs] using h)
    cases h1
    exact ⟨rfl, by rw [h2]⟩
  | [], _ :: _, _, _, hl, _ | _ :: _, [], _, _, hl, _ => by simp at hl

/-- Two values of datatypes are the same SMT value when they are of the same constructor, with
fields that are the same SMT values. -/
theorem trV_adt_eq {D : List Data} (hD : DataOk D) {c c' : Id} {xs ys : List Value}
    {d d' : Data} {i i' : Nat} {fs fs' : List (Id × Ty)} (hc : findCtor D c = some (d, i, fs))
    (hc' : findCtor D c' = some (d', i', fs')) (hl : xs.length = fs.length)
    (hl' : ys.length = fs'.length) :
    trV D (.ADTV c xs) = trV D (.ADTV c' ys) ↔ c = c' ∧ xs.map (trV D) = ys.map (trV D) := by
  simp only [trV, hc, hc', trVs_eq]
  constructor
  · intro h
    have hh := congrArg __smtx_apply_head_value h
    rw [head_applyVs, head_applyVs] at hh
    simp only [__smtx_apply_head_value, SmtValue.DtCons.injEq] at hh
    obtain ⟨hn, _, rfl⟩ := hh
    have hdd := data_eq_of_name hD.nodup (findCtor_spec hc).1 (findCtor_spec hc').1 (nm_inj hn)
    subst hdd
    have h1 := (findCtor_spec hc).2
    rw [(findCtor_spec hc').2] at h1
    cases h1
    exact ⟨rfl, (applyVs_inj _ _ _ _ (by simp [hl, hl']) h).2⟩
  · rintro ⟨rfl, hm⟩
    rw [hc] at hc'
    cases hc'
    rw [hm]

/-- Two sets of a type are the same SMT value when their elements are the same SMT values. -/
theorem trV_set_eq {D : List Data} (hD : DataOk D) {A : Ty} {xs ys : List Value}
    (hxs : ∀ x ∈ xs, HasV D x A) (hys : ∀ y ∈ ys, HasV D y A) :
    trV D (.SetV A xs) = trV D (.SetV A ys) ↔
      ∀ w, w ∈ xs.map (trV D) ↔ w ∈ ys.map (trV D) := by
  have hcx : ∀ w ∈ xs.map (trV D), __smtx_value_canonical default w = true := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
    exact (agrees_trV hD default x A (hxs x hx)).2
  have hcy : ∀ w ∈ ys.map (trV D), __smtx_value_canonical default w = true := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
    exact (agrees_trV hD default y A (hys y hy)).2
  simp only [trV, trVl_eq, SmtValue.Set.injEq]
  exact ⟨fun h => setOf_inj default _ hcx hcy h, fun h => setOf_ext default _ hcx hcy h⟩

/-! ## The values of the sorts are values of the types -/

/-- The sort of a constructor, applied to some of its fields or to all. -/
def IsChain : SmtType → Prop
  | .DtcAppType _ _ => True
  | .Datatype _ _ => True
  | _ => False

theorem forall₂_snoc {α β : Type} {R : α → β → Prop} : ∀ {as : List α} {bs : List β} {a : α}
    {b : β}, List.Forall₂ R as bs → R a b → List.Forall₂ R (as ++ [a]) (bs ++ [b])
  | [], [], _, _, _, h => .cons h .nil
  | _ :: _, _ :: _, _, _, .cons h hs, h' => .cons h (forall₂_snoc hs h')

/-- A value of the sort of a constructor is a constructor applied to values of the sorts of its
first fields. -/
theorem spine_inv : ∀ w : SmtValue, IsChain (__smtx_typeof_value w) →
    ∃ s dd i as fs, w = applyVs (.DtCons s dd i) as ∧
      ctorFields (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) i = some fs ∧
      __smtx_typeof_value w = chainT (.Datatype s dd) (fs.drop as.length) ∧
      List.Forall₂ (fun a U => __smtx_typeof_value a = U) as (fs.take as.length)
  | .DtCons s dd i, h => by
    simp only [__smtx_typeof_value, cons_value_rec] at h ⊢
    cases hf : ctorFields (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) i with
    | none => simp [hf, IsChain] at h
    | some fs => exact ⟨s, dd, i, [], fs, rfl, hf, by simp, by simp⟩
  | .Apply f a, h => by
    cases hft : __smtx_typeof_value f <;>
      simp only [__smtx_typeof_value, __smtx_typeof_apply_value, hft, IsChain] at h
    rename_i A B
    by_cases hA : A = .None
    · simp [__smtx_typeof_guard, native_ite, native_Teq, hA] at h
    by_cases hAa : A = __smtx_typeof_value a
    · have hty : __smtx_typeof_value (.Apply f a) = B := by
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hft, __smtx_typeof_guard,
          native_ite, native_Teq, hA, ← hAa]
      obtain ⟨s, dd, i, as, fs, rfl, hfs, hch, hall⟩ := spine_inv f (by rw [hft]; trivial)
      rw [hft] at hch
      cases hdrop : fs.drop as.length with
      | nil => rw [hdrop] at hch; cases hch
      | cons U rest =>
        rw [hdrop] at hch
        simp only [chainT, SmtType.DtcAppType.injEq] at hch
        obtain ⟨rfl, rfl⟩ := hch
        have hlt : as.length < fs.length := by
          by_contra hge
          rw [List.drop_eq_nil_of_le (by omega)] at hdrop; cases hdrop
        have hget : fs[as.length]? = some A := by
          have := congrArg List.head? hdrop
          simpa [List.head?_drop] using this
        refine ⟨s, dd, i, as ++ [a], fs, (applyVs_snoc _ _ _).symm, hfs, ?_, ?_⟩
        · rw [hty]
          have : fs.drop (as ++ [a]).length = rest := by
            have := congrArg List.tail hdrop
            simpa [List.tail_drop] using this
          rw [this]
        · have : fs.take (as ++ [a]).length = fs.take as.length ++ [A] := by
            simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
            rw [List.take_add_one, hget]; rfl
          rw [this]
          exact forall₂_snoc hall hAa.symm
    · simp [__smtx_typeof_guard, native_ite, native_Teq, hA, hAa] at h
  | .Map m, h => by
    rcases typeof_map_value_shape m with ⟨T, U, hm⟩ | hm <;>
      simp [__smtx_typeof_value, hm, IsChain] at h
  | .Set m, h => by
    rcases typeof_map_value_shape m with ⟨T, U, hm⟩ | hm
    · simp only [__smtx_typeof_value, hm, __smtx_map_to_set_type] at h
      split at h <;> simp [IsChain] at h
    · simp [__smtx_typeof_value, hm, __smtx_map_to_set_type, IsChain] at h
  | .Seq q, h => by
    rcases typeof_seq_value_shape q with ⟨T, hm⟩ | hm <;>
      simp [__smtx_typeof_value, hm, IsChain] at h
  | .Binary w n, h => by
    simp only [__smtx_typeof_value, native_ite] at h
    split at h <;> simp [IsChain] at h
  | .Char c, h => by
    simp only [__smtx_typeof_value, native_ite] at h
    split at h <;> simp [IsChain] at h
  | .NotValue, h | .Boolean _, h | .Numeral _, h | .Real _, h | .Fun _ _ _, h | .UValue _ _, h
  | .RegLan _, h => by simp [__smtx_typeof_value, IsChain] at h

theorem sizeOf_applyVs_le : ∀ (as : List SmtValue) (f : SmtValue),
    sizeOf f ≤ sizeOf (applyVs f as)
  | [], _ => Nat.le_refl _
  | a :: as, f => by
    have := sizeOf_applyVs_le as (.Apply f a)
    simp only [applyVs, List.foldl_cons, SmtValue.Apply.sizeOf_spec] at this ⊢
    omega

theorem sizeOf_applyVs_lt : ∀ (as : List SmtValue) (f : SmtValue), ∀ a ∈ as,
    sizeOf a < sizeOf (applyVs f as)
  | b :: as, f, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha'
    · have := sizeOf_applyVs_le as (.Apply f a)
      simp only [applyVs, List.foldl_cons, SmtValue.Apply.sizeOf_spec] at this ⊢
      omega
    · exact sizeOf_applyVs_lt as (.Apply f b) a ha'

theorem exists_values {D : List Data} : ∀ {as : List SmtValue} {fs : List (Id × Ty)},
    List.Forall₂ (fun a f => ∃ v, HasV D v f.2 ∧ a = trV D v) as fs →
    ∃ vs, List.Forall₂ (HasV D) vs (fs.map Prod.snd) ∧ as = vs.map (trV D)
  | [], [], _ => ⟨[], .nil, rfl⟩
  | _ :: _, _ :: _, .cons ⟨v, hv, rfl⟩ hs => by
    obtain ⟨vs, hvs, rfl⟩ := exists_values hs
    exact ⟨v :: vs, .cons hv hvs, rfl⟩

theorem exists_all {D : List Data} {A : Ty} : ∀ {ws : List SmtValue},
    (∀ w ∈ ws, ∃ v, HasV D v A ∧ w = trV D v) →
    ∃ xs : List Value, (∀ x ∈ xs, HasV D x A) ∧ ws = xs.map (trV D)
  | [], _ => ⟨[], ⟨fun _ h => (nomatch h), rfl⟩⟩
  | w :: ws, h => by
    obtain ⟨v, hv, rfl⟩ := h w (.head _)
    obtain ⟨xs, hxs, rfl⟩ := exists_all fun x hx => h x (.tail _ hx)
    refine ⟨v :: xs, fun x hx => ?_, rfl⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hv
    · exact hxs x hx'

theorem canonical_applyVs_inv (uc : SmtUSortDom) : ∀ (as : List SmtValue) (f : SmtValue),
    __smtx_value_canonical uc (applyVs f as) = true →
    __smtx_value_canonical uc f = true ∧ ∀ a ∈ as, __smtx_value_canonical uc a = true
  | [], _, h => ⟨h, by simp⟩
  | a :: as, f, h => by
    obtain ⟨h1, h2⟩ := canonical_applyVs_inv uc as (.Apply f a) h
    simp only [__smtx_value_canonical, native_and, Bool.and_eq_true] at h1
    refine ⟨h1.1, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact h1.2
    · exact h2 b hb'

/-- No real is in the type: it is not the reals, nor the sets of such a type. -/
def NoReal : Ty → Prop
  | .RealType => False
  | .SetType A => NoReal A
  | _ => True

/-- No datatype has a field with a real. -/
def RealFree (D : List Data) : Prop := ∀ d ∈ D, ∀ c ∈ d.ctors, ∀ f ∈ c.2, NoReal f.2

theorem typed_inv_k {D : List Data} (hD : DataOk D) (hR : RealFree D)
    (uc : SmtUSortDom) : ∀ (k : Nat) (w : SmtValue),
    sizeOf w < k → ∀ T, FragTy D T → NoReal T → __smtx_typeof_value w = trT D T →
    __smtx_value_canonical uc w = true → ∃ v, HasV D v T ∧ w = trV D v
  | 0, _, h, _, _, _, _, _ => by omega
  | k + 1, w, hk, T, hT, hne, hw, hcw => by
    rcases fragTy_cases hT with
      rfl | rfl | rfl | ⟨sg, u, hu, rfl⟩ | ⟨d, hd, rfl⟩ | ⟨A, hA, rfl⟩
    · obtain ⟨i, rfl⟩ := int_value_canonical hw
      exact ⟨.IntV i, by simp [HasV], rfl⟩
    · obtain ⟨b, rfl⟩ := bool_value_canonical hw
      exact ⟨.BoolV b, by simp [HasV], rfl⟩
    · exact absurd hne id
    · simp only [trT] at hw
      obtain ⟨n, rfl⟩ := bitvec_value_canonical hw
      have hu' : native_nat_to_int u.toNat = u := by
        simp [native_nat_to_int, Int.toNat_of_nonneg (Int.le_of_lt hu)]
      rw [hu'] at hw ⊢
      have hr := bitvec_payload_range_of_canonical (w := u) (n := n)
        (by simp [native_zleq, Int.le_of_lt hu]) (bitvec_payload_canonical hw)
      have hp : native_int_pow2 u = 2 ^ u.toNat := by
        simp [native_int_pow2, native_zexp_total, Int.not_lt.mpr (Int.le_of_lt hu)]
      rw [hp] at hr
      exact ⟨.BVV sg u n, hasV_bv_of hu hr.1 hr.2, rfl⟩
    · rw [trT_data hD hd] at hw
      obtain ⟨s, dd, i, as, fs, rfl, hfs, hch, hall⟩ := spine_inv w (by rw [hw]; trivial)
      rw [hw] at hch
      cases hdrop : fs.drop as.length with
      | cons U rest => rw [hdrop] at hch; cases hch
      | nil =>
        rw [hdrop] at hch
        simp only [chainT, SmtType.Datatype.injEq] at hch
        obtain ⟨rfl, rfl⟩ := hch
        rw [ctorFields_data hD hd] at hfs
        simp only [Option.map_eq_some_iff] at hfs
        obtain ⟨⟨c, flds⟩, hi, rfl⟩ := hfs
        have htake : (flds.map fun f => trT D f.2).take as.length =
            flds.map fun f => trT D f.2 := by
          apply List.take_of_length_le
          have := List.drop_eq_nil_iff.mp hdrop
          exact this
        rw [htake] at hall
        have hflds : ∀ f ∈ flds, FragTy D f.2 := hD.fields d hd (c, flds) (List.mem_of_getElem? hi)
        have hfr : ∀ f ∈ flds, NoReal f.2 := hR d hd (c, flds) (List.mem_of_getElem? hi)
        have hcan := (canonical_applyVs_inv uc as _ hcw).2
        have hex : List.Forall₂ (fun a f => ∃ v, HasV D v f.2 ∧ a = trV D v) as flds := by
          have hsz : ∀ a ∈ as, sizeOf a < k := fun a ha => by
            have := sizeOf_applyVs_lt as (.DtCons (nm d.name) d.decl i) a ha
            omega
          clear hi hdrop htake hw hk hcw
          induction flds generalizing as with
          | nil => cases hall; exact .nil
          | cons f flds ih =>
            cases hall with
            | cons ha has =>
              exact .cons (typed_inv_k hD hR uc k _ (hsz _ (.head _)) f.2 (hflds f (.head _))
                  (hfr f (.head _)) ha (hcan _ (.head _)))
                (ih _ has (fun g hg => hflds g (.tail _ hg)) (fun g hg => hfr g (.tail _ hg))
                  (fun b hb => hcan b (.tail _ hb)) fun b hb => hsz b (.tail _ hb))
        obtain ⟨vs, hvs, rfl⟩ := exists_values hex
        have hc := findCtor_of hD hd hi
        exact ⟨.ADTV c vs, hasV_adt hc hvs, by simp only [trV, hc, trVs_eq]⟩
    · simp only [trT] at hw
      obtain ⟨m, rfl⟩ := set_value_canonical hw
      obtain ⟨hm, hks⟩ := set_inv uc hw hcw
      have hex : ∀ j ∈ keys m, ∃ v, HasV D v A ∧ j = trV D v := fun j hj => by
        obtain ⟨h1, h2, h3⟩ := hks j hj
        exact typed_inv_k hD hR uc k j (by simp only [SmtValue.Set.sizeOf_spec] at hk; omega) A hA
          hne h1 h2
      obtain ⟨xs, hxs, hkeys⟩ := exists_all hex
      refine ⟨.SetV A xs, hasV_set_of hA hxs, ?_⟩
      simp only [trV, trVl_eq]
      rw [← hkeys]
      exact congrArg SmtValue.Set hm

/-- A canonical value of the sort of a type of the bridge is that of a value of the type, where
no real is involved: a real of the models needs not be a fraction. -/
theorem typed_inv1 {D : List Data} (hD : DataOk D) (hR : RealFree D) {uc : SmtUSortDom}
    {w : SmtValue} {T : Ty} (hT : FragTy D T) (hne : NoReal T)
    (hw : __smtx_typeof_value w = trT D T) (hcw : __smtx_value_canonical uc w = true) :
    ∃ v, HasV D v T ∧ w = trV D v :=
  typed_inv_k hD hR uc _ w (Nat.lt_succ_self _) T hT hne hw hcw

/-! ## The operators of the sets, on the values -/

/-- The SMT values of the elements of a set are canonical values of the sort of their type. -/
theorem elems_ok {D : List Data} (hD : DataOk D) (uc : SmtUSortDom) {xs : List Value} {A : Ty}
    (h : ∀ x ∈ xs, HasV D x A) : ∀ w ∈ xs.map (trV D),
      __smtx_value_canonical uc w = true ∧ __smtx_typeof_value w = trT D A := by
  intro w hw
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
  exact ⟨(agrees_trV hD uc x A (h x hx)).2, (agrees_trV hD uc x A (h x hx)).1⟩

theorem trV_singleton {D : List Data} (hD : DataOk D) {A : Ty} {x : Value} (hx : HasV D x A) :
    __smtx_model_eval_set_singleton (trV D x) = trV D (.SetV A [x]) := by
  rw [singleton_eq, (agrees_trV hD default x A hx).1]
  simp only [trV, trVl]

theorem trV_union {D : List Data} (hD : DataOk D) {A : Ty} {xs ys zs : List Value}
    (hxs : ∀ x ∈ xs, HasV D x A) (hys : ∀ y ∈ ys, HasV D y A)
    (hzs : ∀ z ∈ zs, HasV D z A)
    (hm : ∀ w, w ∈ zs.map (trV D) ↔ w ∈ xs.map (trV D) ∨ w ∈ ys.map (trV D)) :
    __smtx_model_eval_set_union (trV D (.SetV A xs)) (trV D (.SetV A ys)) =
      trV D (.SetV A zs) := by
  simp only [trV, trVl_eq]
  rw [union_eq default _ (elems_ok hD default hxs) (elems_ok hD default hys)]
  congr 1
  exact setOf_ext default _
    (fun w hw => (List.mem_append.mp hw).elim (fun h => (elems_ok hD default hxs w h).1)
      fun h => (elems_ok hD default hys w h).1)
    (fun w hw => (elems_ok hD default hzs w hw).1)
    fun w => by rw [List.mem_append]; exact (hm w).symm

theorem trV_inter {D : List Data} (hD : DataOk D) {A : Ty} {xs ys : List Value}
    (hxs : ∀ x ∈ xs, HasV D x A) (hys : ∀ y ∈ ys, HasV D y A) :
    __smtx_model_eval_set_inter (trV D (.SetV A xs)) (trV D (.SetV A ys)) =
      trV D (.SetV A (xs.filter fun x => decide (trV D x ∈ ys.map (trV D)) == true)) := by
  have hf : (xs.filter fun x => decide (trV D x ∈ ys.map (trV D)) == true) =
      xs.filter ((fun w => decide (w ∈ ys.map (trV D))) ∘ trV D) :=
    List.filter_congr fun x _ => by simp
  simp only [trV, trVl_eq]
  rw [inter_eq default _ (elems_ok hD default hxs) (elems_ok hD default hys), hf,
    List.filter_map]

theorem trV_minus {D : List Data} (hD : DataOk D) {A : Ty} {xs ys : List Value}
    (hxs : ∀ x ∈ xs, HasV D x A) (hys : ∀ y ∈ ys, HasV D y A) :
    __smtx_model_eval_set_minus (trV D (.SetV A xs)) (trV D (.SetV A ys)) =
      trV D (.SetV A (xs.filter fun x => decide (trV D x ∈ ys.map (trV D)) == false)) := by
  have hf : (xs.filter fun x => decide (trV D x ∈ ys.map (trV D)) == false) =
      xs.filter ((fun w => !decide (w ∈ ys.map (trV D))) ∘ trV D) :=
    List.filter_congr fun x _ => by simp
  simp only [trV, trVl_eq]
  rw [minus_eq default _ (elems_ok hD default hxs) (elems_ok hD default hys), hf,
    List.filter_map]

theorem trV_member {D : List Data} (hD : DataOk D) {A : Ty} {xs : List Value} (v : Value)
    (hxs : ∀ x ∈ xs, HasV D x A) :
    __smtx_model_eval_set_member (trV D v) (trV D (.SetV A xs)) =
      .Boolean (decide (trV D v ∈ xs.map (trV D))) := by
  simp only [trV, trVl_eq]
  exact member_eq default _ _ _ fun w hw => (elems_ok hD default hxs w hw).1

theorem trV_subset {D : List Data} (hD : DataOk D) {A : Ty} {xs ys : List Value}
    (hxs : ∀ x ∈ xs, HasV D x A) (hys : ∀ y ∈ ys, HasV D y A) :
    __smtx_model_eval_set_subset (trV D (.SetV A xs)) (trV D (.SetV A ys)) =
      .Boolean (decide (∀ w ∈ xs.map (trV D), w ∈ ys.map (trV D))) := by
  simp only [trV, trVl_eq]
  exact subset_eq default _ (elems_ok hD default hxs) (elems_ok hD default hys)

/-! ## Equality -/

section Equality
variable {O : Oracle}

open Classical in
theorem values_eq_of {D : List Data} (hO : O.Sound) (P : Program) :
    ∀ (xs ys : List Value) (Ts : List Ty), List.Forall₂ (HasV D) xs Ts →
      List.Forall₂ (HasV D) ys Ts →
      (∀ x ∈ xs, ∀ y ∈ ys, ∀ T, HasV D x T → HasV D y T →
        O.value_eq P x y = .Ok (decide (trV D x = trV D y))) →
      O.values_eq P xs ys = .Ok (decide (xs.map (trV D) = ys.map (trV D)))
  | [], [], _, _, _, _ => by rw [hO.values_eq]; simp
  | [], _ :: _, _, .nil, h2, _ => nomatch h2
  | _ :: _, [], _, .cons _ _, h2, _ => nomatch h2
  | x :: xs, y :: ys, _, .cons hx hxs, .cons hy hys, h => by
    rw [hO.values_eq]
    dsimp only
    rw [h x (.head _) y (.head _) _ hx hy]
    dsimp only
    have ih := values_eq_of hO P xs ys _ hxs hys fun a ha b hb =>
      h a (.tail _ ha) b (.tail _ hb)
    by_cases hxy : trV D x = trV D y
    · rw [dite_eq_left_of_eq_true (by simp [hxy]), ih]
      simp [hxy]
    · simp [hxy]

open Classical in
theorem set_contains_of {D : List Data} (hO : O.Sound) (P : Program) (v : Value) :
    ∀ xs : List Value, (∀ x ∈ xs, O.value_eq P x v = .Ok (decide (trV D x = trV D v))) →
      O.set_contains P xs v = .Ok (decide (trV D v ∈ xs.map (trV D)))
  | [], _ => by rw [hO.set_contains]; simp
  | x :: xs, h => by
    rw [hO.set_contains]
    dsimp only
    rw [h x (.head _)]
    dsimp only
    have ih := set_contains_of hO P v xs fun a ha => h a (.tail _ ha)
    by_cases hxv : trV D x = trV D v
    · simp [hxv]
    · have hvx : trV D v ≠ trV D x := fun e => hxv e.symm
      rw [dite_eq_right_of_eq_false (by simp [hxv]), ih]
      simp [hvx]

open Classical in
theorem subset_of {D : List Data} (hO : O.Sound) (P : Program) (ys : List Value) :
    ∀ xs : List Value,
      (∀ x ∈ xs, ∀ y ∈ ys, O.value_eq P y x = .Ok (decide (trV D y = trV D x))) →
      O.subset P xs ys = .Ok (decide (∀ w ∈ xs.map (trV D), w ∈ ys.map (trV D)))
  | [], _ => by rw [hO.subset]; simp
  | x :: xs, h => by
    rw [hO.subset]
    dsimp only
    rw [set_contains_of hO P x ys fun y hy => h x (.head _) y hy]
    dsimp only
    have ih := subset_of hO P ys xs fun a ha => h a (.tail _ ha)
    by_cases hin : trV D x ∈ ys.map (trV D)
    · rw [dite_eq_left_of_eq_true (by simp only [decide_eq_true hin]), ih]
      congr 1
      apply decide_eq_decide.mpr
      simp only [List.map_cons, List.forall_mem_cons]
      exact ⟨fun h => ⟨hin, h⟩, fun h => h.2⟩
    · rw [dite_eq_right_of_eq_false (by simp only [decide_eq_false hin]; simp)]
      congr 1
      symm
      apply decide_eq_false
      simp only [List.map_cons, List.forall_mem_cons]
      exact fun h => hin h.1

open Classical in
theorem value_eq_k {D : List Data} (hD : DataOk D) (hO : O.Sound) (P : Program) :
    ∀ (k : Nat) (a b : Value) (T : Ty), sizeOf a + sizeOf b < k → HasV D a T → HasV D b T →
      O.value_eq P a b = .Ok (decide (trV D a = trV D b))
  | 0, _, _, _, h, _, _ => by omega
  | k + 1, a, b, T, hk, ha, hb => by
    rcases fragTy_cases (hasV_fragTy ha) with
      rfl | rfl | rfl | ⟨sg, w, _, rfl⟩ | ⟨d, hd, rfl⟩ | ⟨A, hA, rfl⟩
    · obtain ⟨i, rfl⟩ := hasV_int ha
      obtain ⟨j, rfl⟩ := hasV_int hb
      rw [hO.value_eq]; simp [trV]
    · obtain ⟨i, rfl⟩ := hasV_bool ha
      obtain ⟨j, rfl⟩ := hasV_bool hb
      rw [hO.value_eq]; simp [trV]
    · obtain ⟨p, rfl⟩ := hasV_real ha
      obtain ⟨q, rfl⟩ := hasV_real hb
      rw [hO.value_eq]
      dsimp only
      congr 1
      apply decide_eq_decide.mpr
      constructor
      · intro h; rw [h]
      · intro h
        simp only [trV, SmtValue.Real.injEq] at h
        have := Rat.cast_injective h
        rw [ratOf_num_den, ratOf_num_den] at this
        rw [this]
    · obtain ⟨x, rfl, _⟩ := hasV_bv ha
      obtain ⟨y, rfl, _⟩ := hasV_bv hb
      rw [hO.value_eq]; simp [trV]
    · obtain ⟨c, xs, d1, i, fs, rfl, hc, hs, hxs⟩ := hasV_data ha
      obtain ⟨c', ys, d2, i', fs', rfl, hc', hs', hys⟩ := hasV_data hb
      rw [hO.value_eq]
      dsimp only
      have hiff := trV_adt_eq hD hc hc' (xs := xs) (ys := ys) (by simpa using hxs.length_eq)
        (by simpa using hys.length_eq)
      by_cases hcc : c = c'
      · subst hcc
        rw [hc] at hc'
        cases hc'
        rw [dite_eq_left_of_eq_true (eq_true rfl), values_eq_of hO P xs ys _ hxs hys
          fun x hx y hy U hxU hyU => value_eq_k hD hO P k x y U (by
            have h1 := List.sizeOf_lt_of_mem hx
            have h2 := List.sizeOf_lt_of_mem hy
            simp only [Value.ADTV.sizeOf_spec] at hk
            omega) hxU hyU]
        congr 1
        apply decide_eq_decide.mpr
        rw [hiff]
        exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
      · rw [dite_eq_right_of_eq_false (eq_false hcc)]
        congr 1
        symm
        apply decide_eq_false
        rw [hiff]
        exact fun h => hcc h.1
    · obtain ⟨xs, rfl, _, hxs⟩ := hasV_set ha
      obtain ⟨ys, rfl, _, hys⟩ := hasV_set hb
      have hsz : ∀ x ∈ xs, ∀ y ∈ ys, sizeOf x + sizeOf y < k := fun x hx y hy => by
        have h1 := List.sizeOf_lt_of_mem hx
        have h2 := List.sizeOf_lt_of_mem hy
        simp only [Value.SetV.sizeOf_spec] at hk
        omega
      rw [hO.value_eq]
      dsimp only
      rw [subset_of hO P ys xs fun x hx y hy => value_eq_k hD hO P k y x A
        (by have := hsz x hx y hy; omega) (hys y hy) (hxs x hx)]
      dsimp only
      have hiff := trV_set_eq hD hxs hys
      by_cases h1 : ∀ w ∈ xs.map (trV D), w ∈ ys.map (trV D)
      · rw [dite_eq_left_of_eq_true (by simp only [decide_eq_true h1]),
          subset_of hO P xs ys fun y hy x hx => value_eq_k hD hO P k x y A (hsz x hx y hy)
            (hxs x hx) (hys y hy)]
        congr 1
        apply decide_eq_decide.mpr
        rw [hiff]
        exact ⟨fun h2 w => ⟨h1 w, h2 w⟩, fun h w hw => (h w).mpr hw⟩
      · rw [dite_eq_right_of_eq_false (by simp only [decide_eq_false h1]; simp)]
        congr 1
        symm
        apply decide_eq_false
        rw [hiff]
        exact fun h => h1 fun w hw => (h w).mp hw

open Classical in
/-- The equality of the semantics on the values of a type is that of their SMT values. -/
theorem value_eq_hasV {D : List Data} (hD : DataOk D) (hO : O.Sound) (P : Program) {a b : Value}
    {T : Ty} (ha : HasV D a T) (hb : HasV D b T) :
    O.value_eq P a b = .Ok (decide (trV D a = trV D b)) :=
  value_eq_k hD hO P _ a b T (Nat.lt_succ_self _) ha hb

open Classical in
/-- A value is found in a list of values of its type when its SMT value is among theirs. -/
theorem set_contains_hasV {D : List Data} (hD : DataOk D) (hO : O.Sound) (P : Program)
    {xs : List Value} {v : Value} {A : Ty} (hxs : ∀ x ∈ xs, HasV D x A) (hv : HasV D v A) :
    O.set_contains P xs v = .Ok (decide (trV D v ∈ xs.map (trV D))) :=
  set_contains_of hO P v xs fun x hx => value_eq_hasV hD hO P (hxs x hx) hv

open Classical in
theorem subset_hasV {D : List Data} (hD : DataOk D) (hO : O.Sound) (P : Program)
    {xs ys : List Value} {A : Ty} (hxs : ∀ x ∈ xs, HasV D x A)
    (hys : ∀ y ∈ ys, HasV D y A) :
    O.subset P xs ys = .Ok (decide (∀ w ∈ xs.map (trV D), w ∈ ys.map (trV D))) :=
  subset_of hO P ys xs fun x hx y hy => value_eq_hasV hD hO P (hys y hy) (hxs x hx)

end Equality

/-! ## Fields -/

theorem lookupIdx_none {α : Type} {c : Id} {cs : List (Id × α)} (h : c ∉ cs.map (·.1)) :
    lookupIdx c cs = none := by
  cases hl : lookupIdx c cs with
  | none => rfl
  | some r =>
    obtain ⟨i, a⟩ := r
    exact absurd (List.mem_map.mpr ⟨(c, a), List.mem_of_getElem? (lookupIdx_spec hl), rfl⟩) h

/-- The constructor of `cs` that has the field `x`, with the index and the type of the field. -/
def selIn (x : Id) : List (Id × List (Id × Ty)) → Option (Nat × Nat × Ty)
  | [] => none
  | c :: cs =>
    match lookupIdx x c.2 with
    | some r => some (0, r)
    | none => (selIn x cs).map fun r => (r.1 + 1, r.2)

/-- The datatype and the constructor that have the field `x`, with the index and the type of
the field. -/
def findSel (D : List Data) (x : Id) : Option (Data × Nat × Nat × Ty) :=
  D.findSome? fun d => (selIn x d.ctors).map fun r => (d, r)

theorem selIn_spec {x : Id} : ∀ {cs : List (Id × List (Id × Ty))} {i j : Nat} {T : Ty},
    selIn x cs = some (i, j, T) → ∃ c fs, cs[i]? = some (c, fs) ∧ fs[j]? = some (x, T)
  | [], _, _, _, h => by cases h
  | c :: cs, i, j, T, h => by
    simp only [selIn] at h
    split at h
    · rename_i r hr
      cases h
      exact ⟨c.1, c.2, rfl, lookupIdx_spec hr⟩
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨r, hr, rfl, hjT⟩ := h
      obtain ⟨r1, r2, r3⟩ := r
      cases hjT
      simpa using selIn_spec (cs := cs) hr

theorem findSel_spec {D : List Data} {x : Id} {d : Data} {i j : Nat} {T : Ty}
    (h : findSel D x = some (d, i, j, T)) :
    d ∈ D ∧ ∃ c fs, d.ctors[i]? = some (c, fs) ∧ fs[j]? = some (x, T) := by
  obtain ⟨d', hd', hk⟩ := List.exists_of_findSome?_eq_some h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hk
  obtain ⟨k, hk, rfl, rfl⟩ := hk
  exact ⟨hd', selIn_spec hk⟩

theorem selIn_of {x : Id} : ∀ {cs : List (Id × List (Id × Ty))},
    (cs.flatMap fun c => c.2.map (·.1)).Nodup → ∀ {i j : Nat} {c : Id} {fs : List (Id × Ty)}
    {T : Ty}, cs[i]? = some (c, fs) → fs[j]? = some (x, T) → selIn x cs = some (i, j, T)
  | [], _, _, _, _, _, _, h, _ => by simp at h
  | k :: cs, hn, i, j, c, fs, T, hi, hj => by
    rw [List.flatMap_cons, List.nodup_append] at hn
    obtain ⟨hk, hcs, hdis⟩ := hn
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [selIn, lookupIdx_of hk hj]
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have hx : x ∈ cs.flatMap fun c => c.2.map (·.1) :=
        List.mem_flatMap.mpr ⟨(c, fs), List.mem_of_getElem? hi,
          List.mem_map.mpr ⟨(x, T), List.mem_of_getElem? hj, rfl⟩⟩
      have hnot : x ∉ k.2.map (·.1) := fun hm => hdis x hm x hx rfl
      simp only [selIn, lookupIdx_none hnot, selIn_of hcs hi hj, Option.map_some]

theorem sels_nodup {D : List Data} (hD : DataOk D) {d : Data} (hd : d ∈ D) :
    (d.ctors.flatMap fun c => c.2.map (·.1)).Nodup :=
  (List.nodup_flatMap.mp hD.sels).1 d hd

/-- The field of index `j` of the constructor of index `i` of a datatype of `D` is found by its
name. -/
theorem findSel_of {D : List Data} (hD : DataOk D) {d : Data} (hd : d ∈ D) {c x : Id}
    {i j : Nat} {fs : List (Id × Ty)} {T : Ty} (hi : d.ctors[i]? = some (c, fs))
    (hj : fs[j]? = some (x, T)) : findSel D x = some (d, i, j, T) := by
  have hxm : x ∈ d.ctors.flatMap fun c => c.2.map (·.1) :=
    List.mem_flatMap.mpr ⟨(c, fs), List.mem_of_getElem? hi,
      List.mem_map.mpr ⟨(x, T), List.mem_of_getElem? hj, rfl⟩⟩
  have hin := selIn_of (sels_nodup hD hd) hi hj
  cases hf : findSel D x with
  | none =>
    rw [findSel, List.findSome?_eq_none_iff] at hf
    have := hf d hd
    rw [hin] at this
    cases this
  | some r =>
    obtain ⟨d', i', j', T'⟩ := r
    obtain ⟨hd', c', fs', hi', hj'⟩ := findSel_spec hf
    have hxm' : x ∈ d'.ctors.flatMap fun c => c.2.map (·.1) :=
      List.mem_flatMap.mpr ⟨(c', fs'), List.mem_of_getElem? hi',
        List.mem_map.mpr ⟨(x, T'), List.mem_of_getElem? hj', rfl⟩⟩
    have hdd : d' = d := by
      by_contra hne
      have hdis := (List.nodup_flatMap.mp hD.sels).2
      rcases List.mem_iff_getElem.mp hd with ⟨a, ha, rfl⟩
      rcases List.mem_iff_getElem.mp hd' with ⟨b, hb, hbe⟩
      have hab : a ≠ b := fun e => hne (by subst e; exact hbe.symm)
      rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
      · have := List.pairwise_iff_getElem.mp hdis a b ha hb hlt
        exact this hxm (hbe ▸ hxm')
      · have := List.pairwise_iff_getElem.mp hdis b a hb ha hlt
        exact this (hbe ▸ hxm') hxm
    subst hdd
    have h2 := selIn_of (sels_nodup hD hd) hi' hj'
    rw [hin] at h2
    cases h2
    rfl

theorem select_field_spec : ∀ (fs : List (Id × Ty)) (vs : List Value) {x : Id} {v : Value},
    select_field (fs.map fun f => Param.Param f.1 f.2) vs x = .Ok v →
    ∃ (j : Nat) (T : Ty), fs[j]? = some (x, T) ∧ vs[j]? = some v
  | [], _, _, _, h => by rw [List.map_nil, select_field] at h; cases h
  | f :: fs, [], _, _, h => by rw [List.map_cons, select_field] at h; cases h
  | f :: fs, w :: vs, x, v, h => by
    rw [List.map_cons, select_field] at h
    split at h
    · rename_i hf
      cases h
      obtain ⟨f1, f2⟩ := f
      cases hf
      exact ⟨0, f2, rfl, rfl⟩
    · obtain ⟨j, T, hj, hv⟩ := select_field_spec fs vs h
      exact ⟨j + 1, T, by simpa using hj, by simpa using hv⟩

/-- The argument of index `j` of a constructor applied to the values `as`. -/
theorem arg_nth_applyVs (f : SmtValue) : ∀ (as : List SmtValue) (j : Nat) (a : SmtValue),
    as[j]? = some a → __smtx_apply_arg_nth_value (applyVs f as) j as.length = a := by
  intro as
  induction as using List.reverseRecOn with
  | nil => intro j a h; simp at h
  | append_singleton bs b ih =>
    intro j a h
    rw [applyVs_snoc]
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
      __smtx_apply_arg_nth_value, native_ite, native_nateq]
    by_cases hj : j = bs.length
    · subst hj
      simp at h
      simp [h]
    · have hlt : j < bs.length := by
        have := (List.getElem?_eq_some_iff.mp h).1
        simp at this
        omega
      rw [List.getElem?_append_left hlt] at h
      simp [hj, ih j a h]

theorem dtc_num_sels (dd : SmtDatatypeDecl) : ∀ c : SmtDatatypeCons,
    __smtx_dtc_num_sels c = (consFields (__smtx_dtc_resolve c dd)).length
  | .unit => by simp [__smtx_dtc_num_sels, __smtx_dtc_resolve, consFields]
  | .cons U c => by
    cases U <;>
      simp [__smtx_dtc_num_sels, __smtx_dtc_resolve, consFields, dtc_num_sels dd c]

theorem dt_num_sels (dd : SmtDatatypeDecl) : ∀ (d : SmtDatatype) (i : Nat),
    __smtx_dt_num_sels d i = (((ctorFields (__smtx_dt_resolve d dd) i).map List.length).getD 0)
  | .null, i => by cases i <;> simp [__smtx_dt_num_sels, __smtx_dt_resolve, ctorFields]
  | .sum c d, 0 => by simp [__smtx_dt_num_sels, __smtx_dt_resolve, ctorFields, dtc_num_sels dd c]
  | .sum c d, i + 1 => by
    simp [__smtx_dt_num_sels, __smtx_dt_resolve, ctorFields, dt_num_sels dd d i]

theorem ret_typeof_sel_rec : ∀ (d : SmtDatatype) (i j : Nat),
    __smtx_ret_typeof_sel_rec d i j = (((ctorFields d i).bind (·[j]?)).getD .None)
  | .null, i, j => by cases i <;> cases j <;> simp [__smtx_ret_typeof_sel_rec, ctorFields]
  | .sum .unit d, 0, j => by cases j <;> simp [__smtx_ret_typeof_sel_rec, ctorFields, consFields]
  | .sum (.cons T c) d, 0, 0 => by simp [__smtx_ret_typeof_sel_rec, ctorFields, consFields]
  | .sum (.cons T c) d, 0, j + 1 => by
    have := ret_typeof_sel_rec (.sum c d) 0 j
    simp [__smtx_ret_typeof_sel_rec, ctorFields, consFields] at this ⊢
    exact this
  | .sum c d, i + 1, j => by
    simp [__smtx_ret_typeof_sel_rec, ctorFields, ret_typeof_sel_rec d i j]

/-! ## The datatypes of a program -/

/-! ## Reals -/

/-- The greatest common divisor of the semantics is that of the integers. -/
theorem gcd_nat (m k : Nat) : Inox.Semantics.gcd (m : Int) (k : Int) = (Nat.gcd m k : Int) := by
  induction k using Nat.strong_induction_on generalizing m with
  | _ k ih =>
    rw [Inox.Semantics.gcd]
    split
    · next h =>
      have : k = 0 := by omega
      subst this; simp
    · next h =>
      have hk : 0 < k := by omega
      rw [← Int.natCast_mod, ih (m % k) (Nat.mod_lt _ hk) k]
      congr 1
      rw [Nat.gcd_comm m k, Nat.gcd_rec k m]
      exact Nat.gcd_comm _ _

theorem sign_eq {d : Int} (h : d ≠ 0) :
    (if _h : d < 0 then (0 : Int) - 1 else 1) = d.sign := by
  rcases Int.lt_trichotomy d 0 with h1 | h1 | h1
  · simp [h1, Int.sign_eq_neg_one_of_neg h1]
  · exact absurd h1 h
  · simp [Int.not_lt.mpr (Int.le_of_lt h1), Int.sign_eq_one_of_pos h1]

theorem ratOf_num (n d : Int) : (ratOf n d).num = d.sign * n / (d.gcd n : Int) := by
  rw [ratOf, ← Rat.divInt_eq_div, Rat.num_divInt]

theorem ratOf_den (n d : Int) (h : d ≠ 0) :
    ((ratOf n d).den : Int) = d.sign * d / (d.gcd n : Int) := by
  rw [ratOf, ← Rat.divInt_eq_div, Rat.den_divInt, if_neg h, Int.sign_mul_self_eq_natAbs]; simp

/-- A fraction of the semantics is the rational that it is, in lowest terms. -/
theorem real_eq {n d : Int} (h : d ≠ 0) :
    real n d = .Ok (.RealV (ratOf n d).num (ratOf n d).den) := by
  have hg : Inox.Semantics.gcd (Inox.Semantics.abs n) (Inox.Semantics.abs d) = (d.gcd n : Int) := by
    have ha : ∀ x : Int, Inox.Semantics.abs x = (x.natAbs : Int) := by
      intro x; rw [Inox.Semantics.abs]; split <;> omega
    rw [ha, ha, gcd_nat, Nat.gcd_comm]
    rfl
  have hdn : ((d.gcd n : Nat) : Int) ∣ n := Int.gcd_dvd_right _ _
  have hdd : ((d.gcd n : Nat) : Int) ∣ d := Int.gcd_dvd_left _ _
  simp only [real, dif_neg h, hg, sign_eq h, ratOf_num, ratOf_den n d h,
    Int.mul_ediv_assoc _ hdn, Int.mul_ediv_assoc _ hdd]

/-! ## Bit-vectors -/

theorem pow2_toNat : ∀ (k : Nat) (w : Int), w.toNat = k → 0 ≤ w → pow2 w = 2 ^ k
  | 0, w, hk, hw => by
    have : w = 0 := by omega
    subst this
    rw [pow2]; simp
  | k + 1, w, hk, hw => by
    rw [pow2]
    have hn : ¬ w ≤ 0 := by omega
    rw [dif_neg hn, pow2_toNat k (w - 1) (by omega) (by omega), Int.pow_succ, Int.mul_comm]

/-- The power of two of the semantics is that of the integers. -/
theorem pow2_eq {w : Int} (hw : 0 ≤ w) : pow2 w = 2 ^ w.toNat := pow2_toNat _ w rfl hw

/-- The power of two of Logos is that of the integers. -/
theorem int_pow2_eq {w : Int} (hw : 0 ≤ w) : native_int_pow2 w = 2 ^ w.toNat := by
  simp [native_int_pow2, native_zexp_total, Int.not_lt.mpr hw]

theorem two_pow_pos (k : Nat) : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)

/-- A bit-vector of the semantics is a value of its type. -/
theorem hasV_bvmk {D : List Data} {s : Bool} {w : Int} (hw : 0 < w) (z : Int) :
    HasV D (bv s w z) (.BVType s w) := by
  rw [bv, pow2_eq (Int.le_of_lt hw)]
  exact hasV_bv_of hw (Int.emod_nonneg _ (Int.ne_of_gt (two_pow_pos _)))
    (Int.emod_lt_of_pos _ (two_pow_pos _))

theorem trV_bvmk {D : List Data} {s : Bool} {w : Int} (hw : 0 < w) (z : Int) :
    trV D (bv s w z) = .Binary w (z % 2 ^ w.toNat) := by
  rw [bv, pow2_eq (Int.le_of_lt hw)]; rfl

/-- The program has the constructors of `D`, with their fields, in datatypes without type
parameters and without invariants. -/
def ProgData (D : List Data) : Program → Prop
  | .Program _ cs ss _ _ => ∀ c d i fs, findCtor D c = some (d, i, fs) →
      lookup_ctor cs c = .Ok (.Constructor c d.name (fs.map fun f => .Param f.1 f.2)) ∧
      lookup_sort ss d.name = .Ok (.Sort d.name [] none)

end Inox.Bridge
