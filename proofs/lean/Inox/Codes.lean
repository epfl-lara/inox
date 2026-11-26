/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Model
import Mathlib.Analysis.Real.Cardinality

/-!
# An injection of codes exists

`Codes` (`Inox/Model.lean`) is an injection of the partial applications of the functions of a
program, a name, a sort and a list of values, into the non-zero identifiers of the function values
of a model, which are reals. One exists (`Codes.nonempty`): the sorts are countable, and a value
is written as a list of reals and naturals, injectively (`ser_inj`), so there are no more values,
lists of values and partial applications than reals.
-/

namespace Inox.Model

open SmtEval
open Smtm
open Cardinal


/-! ## The sorts are countable -/

mutual
/-- A sort, written as a list of naturals: the number of its constructor, then its arguments. -/
def tser : SmtType → List ℕ
  | .None => [0]
  | .Bool => [1]
  | .Int => [2]
  | .Real => [3]
  | .RegLan => [4]
  | .BitVec n => [5, n]
  | .Map a b => 6 :: (tser a ++ tser b)
  | .Set a => 7 :: tser a
  | .Seq a => 8 :: tser a
  | .Char => [9]
  | .Datatype s d => 10 :: Encodable.encode s :: dser d
  | .TypeRef s => [11, Encodable.encode s]
  | .USort n => [12, n]
  | .FunType a b => 13 :: (tser a ++ tser b)
  | .DtcAppType a b => 14 :: (tser a ++ tser b)

/-- A datatype, written as a list of naturals. -/
def dtser : SmtDatatype → List ℕ
  | .null => [0]
  | .sum c d => 1 :: (cser c ++ dtser d)

/-- A constructor of a datatype, written as a list of naturals. -/
def cser : SmtDatatypeCons → List ℕ
  | .unit => [0]
  | .cons T c => 1 :: (tser T ++ cser c)

/-- A datatype declaration, written as a list of naturals. -/
def dser : SmtDatatypeDecl → List ℕ
  | .nil => [0]
  | .cons s d r => 1 :: Encodable.encode s :: (dtser d ++ dser r)
end

mutual
/-- What a sort is written as determines it, and what follows it: no sort is written as the
start of what another is written as. -/
theorem tser_inj : ∀ (a b : SmtType) (l l' : List ℕ),
    tser a ++ l = tser b ++ l' → a = b ∧ l = l'
  | .None, b, l, l', h | .Bool, b, l, l', h | .Int, b, l, l', h | .Real, b, l, l', h
  | .RegLan, b, l, l', h => by
    cases b <;> simp [tser] at h
    exact ⟨rfl, h⟩
  | .BitVec x0, b, l, l', h => by
    cases b <;> simp [tser] at h
    rename_i y0
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | .Map x0 x1, b, l, l', h => by
    cases b <;> simp [tser] at h
    rename_i y0 y1
    obtain ⟨rfl, h1⟩ := tser_inj x0 y0 _ _ h
    obtain ⟨rfl, rfl⟩ := tser_inj x1 y1 _ _ h1
    exact ⟨rfl, rfl⟩
  | .Set x0, b, l, l', h => by
    cases b <;> simp [tser] at h
    rename_i y0
    obtain ⟨rfl, rfl⟩ := tser_inj x0 y0 _ _ h
    exact ⟨rfl, rfl⟩
  | .Seq x0, b, l, l', h => by
    cases b <;> simp [tser] at h
    rename_i y0
    obtain ⟨rfl, rfl⟩ := tser_inj x0 y0 _ _ h
    exact ⟨rfl, rfl⟩
  | .Char, b, l, l', h => by
    cases b <;> simp [tser] at h
    exact ⟨rfl, h⟩
  | .Datatype x0 x1, b, l, l', h => by
    cases b <;> simp [tser] at h
    rename_i y0 y1
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := dser_inj x1 y1 _ _ h
    exact ⟨rfl, rfl⟩
  | .TypeRef x0, b, l, l', h => by
    cases b <;> simp [tser] at h
    rename_i y0
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | .USort x0, b, l, l', h => by
    cases b <;> simp [tser] at h
    rename_i y0
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | .FunType x0 x1, b, l, l', h => by
    cases b <;> simp [tser] at h
    rename_i y0 y1
    obtain ⟨rfl, h1⟩ := tser_inj x0 y0 _ _ h
    obtain ⟨rfl, rfl⟩ := tser_inj x1 y1 _ _ h1
    exact ⟨rfl, rfl⟩
  | .DtcAppType x0 x1, b, l, l', h => by
    cases b <;> simp [tser] at h
    rename_i y0 y1
    obtain ⟨rfl, h1⟩ := tser_inj x0 y0 _ _ h
    obtain ⟨rfl, rfl⟩ := tser_inj x1 y1 _ _ h1
    exact ⟨rfl, rfl⟩

theorem dtser_inj : ∀ (a b : SmtDatatype) (l l' : List ℕ),
    dtser a ++ l = dtser b ++ l' → a = b ∧ l = l'
  | .null, b, l, l', h => by
    cases b <;> simp [dtser] at h
    exact ⟨rfl, h⟩
  | .sum x0 x1, b, l, l', h => by
    cases b <;> simp [dtser] at h
    rename_i y0 y1
    obtain ⟨rfl, h1⟩ := cser_inj x0 y0 _ _ h
    obtain ⟨rfl, rfl⟩ := dtser_inj x1 y1 _ _ h1
    exact ⟨rfl, rfl⟩

theorem cser_inj : ∀ (a b : SmtDatatypeCons) (l l' : List ℕ),
    cser a ++ l = cser b ++ l' → a = b ∧ l = l'
  | .unit, b, l, l', h => by
    cases b <;> simp [cser] at h
    exact ⟨rfl, h⟩
  | .cons x0 x1, b, l, l', h => by
    cases b <;> simp [cser] at h
    rename_i y0 y1
    obtain ⟨rfl, h1⟩ := tser_inj x0 y0 _ _ h
    obtain ⟨rfl, rfl⟩ := cser_inj x1 y1 _ _ h1
    exact ⟨rfl, rfl⟩

theorem dser_inj : ∀ (a b : SmtDatatypeDecl) (l l' : List ℕ),
    dser a ++ l = dser b ++ l' → a = b ∧ l = l'
  | .nil, b, l, l', h => by
    cases b <;> simp [dser] at h
    exact ⟨rfl, h⟩
  | .cons x0 x1 x2, b, l, l', h => by
    cases b <;> simp [dser] at h
    rename_i y0 y1 y2
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, h1⟩ := dtser_inj x1 y1 _ _ h
    obtain ⟨rfl, rfl⟩ := dser_inj x2 y2 _ _ h1
    exact ⟨rfl, rfl⟩
end

instance : Countable SmtType :=
  Function.Injective.countable (f := tser) fun a b h => (tser_inj a b [] [] (by simpa using h)).1

instance : Countable SmtDatatypeDecl :=
  Function.Injective.countable (f := dser) fun a b h => (dser_inj a b [] [] (by simpa using h)).1

/-! ## Values as lists of reals and naturals -/

/-- A natural for each element of a countable type, injectively. -/
noncomputable def enc {α : Type} [Countable α] : α → ℕ :=
  (Countable.exists_injective_nat α).choose

theorem enc_inj {α : Type} [Countable α] {a b : α} : enc a = enc b ↔ a = b :=
  (Countable.exists_injective_nat α).choose_spec.eq_iff

/-- What values are written with. -/
abbrev Tok := ℝ ⊕ ℕ

mutual
/-- A value, written as a list of tokens: the number of its constructor, then its arguments. -/
noncomputable def ser : SmtValue → List Tok
  | .NotValue => [.inr 0]
  | .Boolean b => [.inr 1, .inr (enc b)]
  | .Numeral i => [.inr 2, .inr (enc i)]
  | .Real r => [.inr 3, .inl r]
  | .Binary a b => [.inr 4, .inr (enc a), .inr (enc b)]
  | .Map m => .inr 5 :: serMap m
  | .Fun i T U => [.inr 6, .inl i, .inr (enc T), .inr (enc U)]
  | .Set m => .inr 7 :: serMap m
  | .Seq s => .inr 8 :: serSeq s
  | .Char c => [.inr 9, .inr (enc c)]
  | .UValue n i => [.inr 10, .inr (enc n), .inl i]
  | .RegLan r => .inr 11 :: serReg r
  | .DtCons s d n => [.inr 12, .inr (enc s), .inr (enc d), .inr (enc n)]
  | .Apply f a => .inr 13 :: (ser f ++ ser a)

/-- A map, written as a list of tokens. -/
noncomputable def serMap : SmtMap → List Tok
  | .cons k v m => .inr 0 :: (ser k ++ (ser v ++ serMap m))
  | .default T v => .inr 1 :: .inr (enc T) :: ser v

/-- A regular language, written as a list of tokens. -/
noncomputable def serReg : SmtRegLan → List Tok
  | .empty => [.inr 0]
  | .epsilon => [.inr 1]
  | .char v => .inr 2 :: ser v
  | .range a b => .inr 3 :: (ser a ++ ser b)
  | .allchar => [.inr 4]
  | .concat a b => .inr 5 :: (serReg a ++ serReg b)
  | .union a b => .inr 6 :: (serReg a ++ serReg b)
  | .inter a b => .inr 7 :: (serReg a ++ serReg b)
  | .star a => .inr 8 :: serReg a
  | .comp a => .inr 9 :: serReg a

/-- A sequence, written as a list of tokens. -/
noncomputable def serSeq : SmtSeq → List Tok
  | .cons v s => .inr 0 :: (ser v ++ serSeq s)
  | .empty T => [.inr 1, .inr (enc T)]
end

mutual
/-- What a value is written as determines it, and what follows it. -/
theorem ser_inj : ∀ (a b : SmtValue) (l l' : List Tok),
    ser a ++ l = ser b ++ l' → a = b ∧ l = l'
  | .NotValue, b, l, l', h => by
    cases b <;> simp [ser] at h
    exact ⟨rfl, h⟩
  | .Boolean x0, b, l, l', h => by
    cases b <;> simp [ser, enc_inj] at h
    rename_i y0
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | .Numeral x0, b, l, l', h => by
    cases b <;> simp [ser, enc_inj] at h
    rename_i y0
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | .Real x0, b, l, l', h => by
    cases b <;> simp [ser] at h
    rename_i y0
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | .Binary x0 x1, b, l, l', h => by
    cases b <;> simp [ser, enc_inj] at h
    rename_i y0 y1
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | .Map x0, b, l, l', h => by
    cases b <;> simp [ser] at h
    rename_i y0
    obtain ⟨rfl, rfl⟩ := serMap_inj x0 y0 _ _ h
    exact ⟨rfl, rfl⟩
  | .Fun x0 x1 x2, b, l, l', h => by
    cases b <;> simp [ser, enc_inj] at h
    rename_i y0 y1 y2
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | .Set x0, b, l, l', h => by
    cases b <;> simp [ser] at h
    rename_i y0
    obtain ⟨rfl, rfl⟩ := serMap_inj x0 y0 _ _ h
    exact ⟨rfl, rfl⟩
  | .Seq x0, b, l, l', h => by
    cases b <;> simp [ser] at h
    rename_i y0
    obtain ⟨rfl, rfl⟩ := serSeq_inj x0 y0 _ _ h
    exact ⟨rfl, rfl⟩
  | .Char x0, b, l, l', h => by
    cases b <;> simp [ser, enc_inj] at h
    rename_i y0
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | .UValue x0 x1, b, l, l', h => by
    cases b <;> simp [ser, enc_inj] at h
    rename_i y0 y1
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | .RegLan x0, b, l, l', h => by
    cases b <;> simp [ser] at h
    rename_i y0
    obtain ⟨rfl, rfl⟩ := serReg_inj x0 y0 _ _ h
    exact ⟨rfl, rfl⟩
  | .DtCons x0 x1 x2, b, l, l', h => by
    cases b <;> simp [ser, enc_inj] at h
    rename_i y0 y1 y2
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | .Apply x0 x1, b, l, l', h => by
    cases b <;> simp [ser] at h
    rename_i y0 y1
    obtain ⟨rfl, h1⟩ := ser_inj x0 y0 _ _ h
    obtain ⟨rfl, rfl⟩ := ser_inj x1 y1 _ _ h1
    exact ⟨rfl, rfl⟩

theorem serMap_inj : ∀ (a b : SmtMap) (l l' : List Tok),
    serMap a ++ l = serMap b ++ l' → a = b ∧ l = l'
  | .cons x0 x1 x2, b, l, l', h => by
    cases b <;> simp [serMap] at h
    rename_i y0 y1 y2
    obtain ⟨rfl, h1⟩ := ser_inj x0 y0 _ _ h
    obtain ⟨rfl, h2⟩ := ser_inj x1 y1 _ _ h1
    obtain ⟨rfl, rfl⟩ := serMap_inj x2 y2 _ _ h2
    exact ⟨rfl, rfl⟩
  | .default x0 x1, b, l, l', h => by
    cases b <;> simp [serMap, enc_inj] at h
    rename_i y0 y1
    obtain ⟨rfl, h0⟩ := h
    obtain ⟨rfl, rfl⟩ := ser_inj x1 y1 _ _ h0
    exact ⟨rfl, rfl⟩

theorem serReg_inj : ∀ (a b : SmtRegLan) (l l' : List Tok),
    serReg a ++ l = serReg b ++ l' → a = b ∧ l = l'
  | .empty, b, l, l', h | .epsilon, b, l, l', h => by
    cases b <;> simp [serReg] at h
    exact ⟨rfl, h⟩
  | .char x0, b, l, l', h => by
    cases b <;> simp [serReg] at h
    rename_i y0
    obtain ⟨rfl, rfl⟩ := ser_inj x0 y0 _ _ h
    exact ⟨rfl, rfl⟩
  | .range x0 x1, b, l, l', h => by
    cases b <;> simp [serReg] at h
    rename_i y0 y1
    obtain ⟨rfl, h1⟩ := ser_inj x0 y0 _ _ h
    obtain ⟨rfl, rfl⟩ := ser_inj x1 y1 _ _ h1
    exact ⟨rfl, rfl⟩
  | .allchar, b, l, l', h => by
    cases b <;> simp [serReg] at h
    exact ⟨rfl, h⟩
  | .concat x0 x1, b, l, l', h => by
    cases b <;> simp [serReg] at h
    rename_i y0 y1
    obtain ⟨rfl, h1⟩ := serReg_inj x0 y0 _ _ h
    obtain ⟨rfl, rfl⟩ := serReg_inj x1 y1 _ _ h1
    exact ⟨rfl, rfl⟩
  | .union x0 x1, b, l, l', h => by
    cases b <;> simp [serReg] at h
    rename_i y0 y1
    obtain ⟨rfl, h1⟩ := serReg_inj x0 y0 _ _ h
    obtain ⟨rfl, rfl⟩ := serReg_inj x1 y1 _ _ h1
    exact ⟨rfl, rfl⟩
  | .inter x0 x1, b, l, l', h => by
    cases b <;> simp [serReg] at h
    rename_i y0 y1
    obtain ⟨rfl, h1⟩ := serReg_inj x0 y0 _ _ h
    obtain ⟨rfl, rfl⟩ := serReg_inj x1 y1 _ _ h1
    exact ⟨rfl, rfl⟩
  | .star x0, b, l, l', h => by
    cases b <;> simp [serReg] at h
    rename_i y0
    obtain ⟨rfl, rfl⟩ := serReg_inj x0 y0 _ _ h
    exact ⟨rfl, rfl⟩
  | .comp x0, b, l, l', h => by
    cases b <;> simp [serReg] at h
    rename_i y0
    obtain ⟨rfl, rfl⟩ := serReg_inj x0 y0 _ _ h
    exact ⟨rfl, rfl⟩

theorem serSeq_inj : ∀ (a b : SmtSeq) (l l' : List Tok),
    serSeq a ++ l = serSeq b ++ l' → a = b ∧ l = l'
  | .cons x0 x1, b, l, l', h => by
    cases b <;> simp [serSeq] at h
    rename_i y0 y1
    obtain ⟨rfl, h1⟩ := ser_inj x0 y0 _ _ h
    obtain ⟨rfl, rfl⟩ := serSeq_inj x1 y1 _ _ h1
    exact ⟨rfl, rfl⟩
  | .empty x0, b, l, l', h => by
    cases b <;> simp [serSeq, enc_inj] at h
    rename_i y0
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
end

/-- Distinct values are written differently. -/
theorem ser_injective : Function.Injective ser :=
  fun a b h => (ser_inj a b [] [] (by simpa using h)).1

/-! ## An injection of codes -/

/-- There are no more values than reals. -/
theorem mk_value_le : #SmtValue ≤ 𝔠 :=
  calc #SmtValue ≤ #(List Tok) := mk_le_of_injective ser_injective
    _ = #Tok := mk_list_eq_mk Tok
    _ = 𝔠 := by simp [mk_real]

/-- There are no more partial applications than reals. -/
theorem mk_app_le : #(native_String × SmtType × List SmtValue) ≤ #ℝ := by
  have h1 : #(List SmtValue) ≤ 𝔠 :=
    (mk_list_le_max _).trans (max_le aleph0_le_continuum mk_value_le)
  have h2 : #native_String ≤ 𝔠 := mk_le_aleph0.trans aleph0_le_continuum
  have h3 : #SmtType ≤ 𝔠 := mk_le_aleph0.trans aleph0_le_continuum
  rw [mk_real]
  simp only [mk_prod, lift_id]
  exact mul_le_of_le aleph0_le_continuum h2 (mul_le_of_le aleph0_le_continuum h3 h1)

/-- An injection of the reals into the non-zero reals. -/
noncomputable def shift (x : ℝ) : ℝ := if 0 ≤ x then x + 1 else x

theorem shift_ne (x : ℝ) : shift x ≠ 0 := by
  unfold shift; split <;> linarith

theorem shift_inj {x y : ℝ} (h : shift x = shift y) : x = y := by
  unfold shift at h; split at h <;> split at h <;> linarith

/-- An injection of codes exists. -/
theorem Codes.nonempty : Nonempty Codes := by
  obtain ⟨e⟩ := (le_def _ _).mp mk_app_le
  refine ⟨{ code := fun s T vs => shift (e (s, T, vs)), inj := ?_,
            ne := fun _ _ _ => shift_ne _ }⟩
  intro s T vs s' T' vs' h
  have := e.injective (shift_inj h)
  simp only [Prod.mk.injEq] at this
  exact this

end Inox.Model
