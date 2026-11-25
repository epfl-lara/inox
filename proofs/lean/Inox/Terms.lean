/- Copyright 2009-2026 EPFL, Lausanne -/
import Inox.Accept
import Cpc.SmtTranslate

/-!
# The rules of a certificate, as the terms that Logos reads

The definitions that `Inox/Fresh.lean`, `Inox/Extend.lean` and `Inox/RuleSteps.lean` are about,
which `inox-check --terms` computes: whether a term mentions a constant, the steps that extend a
set of clauses, and the steps of the rules of a certificate. `Inox/RuleSteps.lean` explains them.
-/

namespace Inox.Fresh

open SmtEval
open Smtm

/-- Whether the constant `s` of sort `T` occurs in a term. -/
def mentions (s : native_String) (T : SmtType) : SmtTerm → Bool
  | .None => false
  | .Boolean _ => false
  | .Numeral _ => false
  | .Rational _ => false
  | .String _ => false
  | .Binary _ _ => false
  | .Apply x1 x2 => mentions s T x1 || mentions s T x2
  | .Var _ _ => false
  | .DtCons _ _ _ => false
  | .DtSel _ _ _ _ => false
  | .DtTester _ _ _ => false
  | .UConst s' T' => s' == s && T' == T
  | .ite x1 x2 x3 => mentions s T x1 || mentions s T x2 || mentions s T x3
  | .not x1 => mentions s T x1
  | .or x1 x2 => mentions s T x1 || mentions s T x2
  | .and x1 x2 => mentions s T x1 || mentions s T x2
  | .imp x1 x2 => mentions s T x1 || mentions s T x2
  | .xor x1 x2 => mentions s T x1 || mentions s T x2
  | .eq x1 x2 => mentions s T x1 || mentions s T x2
  | ._at_purify x1 => mentions s T x1
  | .plus x1 x2 => mentions s T x1 || mentions s T x2
  | .neg x1 x2 => mentions s T x1 || mentions s T x2
  | .mult x1 x2 => mentions s T x1 || mentions s T x2
  | .lt x1 x2 => mentions s T x1 || mentions s T x2
  | .leq x1 x2 => mentions s T x1 || mentions s T x2
  | .gt x1 x2 => mentions s T x1 || mentions s T x2
  | .geq x1 x2 => mentions s T x1 || mentions s T x2
  | .to_real x1 => mentions s T x1
  | .to_int x1 => mentions s T x1
  | .is_int x1 => mentions s T x1
  | .abs x1 => mentions s T x1
  | .uneg x1 => mentions s T x1
  | .div x1 x2 => mentions s T x1 || mentions s T x2
  | .mod x1 x2 => mentions s T x1 || mentions s T x2
  | .divisible x1 x2 => mentions s T x1 || mentions s T x2
  | .int_pow2 x1 => mentions s T x1
  | .int_log2 x1 => mentions s T x1
  | .div_total x1 x2 => mentions s T x1 || mentions s T x2
  | .mod_total x1 x2 => mentions s T x1 || mentions s T x2
  | .select x1 x2 => mentions s T x1 || mentions s T x2
  | .store x1 x2 x3 => mentions s T x1 || mentions s T x2 || mentions s T x3
  | .map_diff x1 x2 => mentions s T x1 || mentions s T x2
  | .concat x1 x2 => mentions s T x1 || mentions s T x2
  | .extract x1 x2 x3 => mentions s T x1 || mentions s T x2 || mentions s T x3
  | .repeat x1 x2 => mentions s T x1 || mentions s T x2
  | .bvnot x1 => mentions s T x1
  | .bvand x1 x2 => mentions s T x1 || mentions s T x2
  | .bvor x1 x2 => mentions s T x1 || mentions s T x2
  | .bvnand x1 x2 => mentions s T x1 || mentions s T x2
  | .bvnor x1 x2 => mentions s T x1 || mentions s T x2
  | .bvxor x1 x2 => mentions s T x1 || mentions s T x2
  | .bvxnor x1 x2 => mentions s T x1 || mentions s T x2
  | .bvcomp x1 x2 => mentions s T x1 || mentions s T x2
  | .bvneg x1 => mentions s T x1
  | .bvadd x1 x2 => mentions s T x1 || mentions s T x2
  | .bvmul x1 x2 => mentions s T x1 || mentions s T x2
  | .bvudiv x1 x2 => mentions s T x1 || mentions s T x2
  | .bvurem x1 x2 => mentions s T x1 || mentions s T x2
  | .bvsub x1 x2 => mentions s T x1 || mentions s T x2
  | .bvsdiv x1 x2 => mentions s T x1 || mentions s T x2
  | .bvsrem x1 x2 => mentions s T x1 || mentions s T x2
  | .bvsmod x1 x2 => mentions s T x1 || mentions s T x2
  | .bvult x1 x2 => mentions s T x1 || mentions s T x2
  | .bvule x1 x2 => mentions s T x1 || mentions s T x2
  | .bvugt x1 x2 => mentions s T x1 || mentions s T x2
  | .bvuge x1 x2 => mentions s T x1 || mentions s T x2
  | .bvslt x1 x2 => mentions s T x1 || mentions s T x2
  | .bvsle x1 x2 => mentions s T x1 || mentions s T x2
  | .bvsgt x1 x2 => mentions s T x1 || mentions s T x2
  | .bvsge x1 x2 => mentions s T x1 || mentions s T x2
  | .bvshl x1 x2 => mentions s T x1 || mentions s T x2
  | .bvlshr x1 x2 => mentions s T x1 || mentions s T x2
  | .bvashr x1 x2 => mentions s T x1 || mentions s T x2
  | .zero_extend x1 x2 => mentions s T x1 || mentions s T x2
  | .sign_extend x1 x2 => mentions s T x1 || mentions s T x2
  | .rotate_left x1 x2 => mentions s T x1 || mentions s T x2
  | .rotate_right x1 x2 => mentions s T x1 || mentions s T x2
  | .bvuaddo x1 x2 => mentions s T x1 || mentions s T x2
  | .bvnego x1 => mentions s T x1
  | .bvsaddo x1 x2 => mentions s T x1 || mentions s T x2
  | .bvumulo x1 x2 => mentions s T x1 || mentions s T x2
  | .bvsmulo x1 x2 => mentions s T x1 || mentions s T x2
  | .bvusubo x1 x2 => mentions s T x1 || mentions s T x2
  | .bvssubo x1 x2 => mentions s T x1 || mentions s T x2
  | .bvsdivo x1 x2 => mentions s T x1 || mentions s T x2
  | .seq_empty _ => false
  | .str_len x1 => mentions s T x1
  | .str_concat x1 x2 => mentions s T x1 || mentions s T x2
  | .str_substr x1 x2 x3 => mentions s T x1 || mentions s T x2 || mentions s T x3
  | .str_contains x1 x2 => mentions s T x1 || mentions s T x2
  | .str_replace x1 x2 x3 => mentions s T x1 || mentions s T x2 || mentions s T x3
  | .str_indexof x1 x2 x3 => mentions s T x1 || mentions s T x2 || mentions s T x3
  | .str_at x1 x2 => mentions s T x1 || mentions s T x2
  | .str_prefixof x1 x2 => mentions s T x1 || mentions s T x2
  | .str_suffixof x1 x2 => mentions s T x1 || mentions s T x2
  | .str_rev x1 => mentions s T x1
  | .str_update x1 x2 x3 => mentions s T x1 || mentions s T x2 || mentions s T x3
  | .str_to_lower x1 => mentions s T x1
  | .str_to_upper x1 => mentions s T x1
  | .str_to_code x1 => mentions s T x1
  | .str_from_code x1 => mentions s T x1
  | .str_is_digit x1 => mentions s T x1
  | .str_to_int x1 => mentions s T x1
  | .str_from_int x1 => mentions s T x1
  | .str_lt x1 x2 => mentions s T x1 || mentions s T x2
  | .str_leq x1 x2 => mentions s T x1 || mentions s T x2
  | .str_replace_all x1 x2 x3 => mentions s T x1 || mentions s T x2 || mentions s T x3
  | .str_replace_re x1 x2 x3 => mentions s T x1 || mentions s T x2 || mentions s T x3
  | .str_replace_re_all x1 x2 x3 => mentions s T x1 || mentions s T x2 || mentions s T x3
  | .str_indexof_re x1 x2 x3 => mentions s T x1 || mentions s T x2 || mentions s T x3
  | .re_allchar => false
  | .re_none => false
  | .re_all => false
  | .str_to_re x1 => mentions s T x1
  | .re_mult x1 => mentions s T x1
  | .re_plus x1 => mentions s T x1
  | .re_exp x1 x2 => mentions s T x1 || mentions s T x2
  | .re_opt x1 => mentions s T x1
  | .re_comp x1 => mentions s T x1
  | .re_range x1 x2 => mentions s T x1 || mentions s T x2
  | .re_concat x1 x2 => mentions s T x1 || mentions s T x2
  | .re_inter x1 x2 => mentions s T x1 || mentions s T x2
  | .re_union x1 x2 => mentions s T x1 || mentions s T x2
  | .re_diff x1 x2 => mentions s T x1 || mentions s T x2
  | .re_loop x1 x2 x3 => mentions s T x1 || mentions s T x2 || mentions s T x3
  | .str_in_re x1 x2 => mentions s T x1 || mentions s T x2
  | .seq_unit x1 => mentions s T x1
  | .seq_nth x1 x2 => mentions s T x1 || mentions s T x2
  | .str_indexof_re_split x1 x2 x3 => mentions s T x1 || mentions s T x2 || mentions s T x3
  | .seq_diff x1 x2 => mentions s T x1 || mentions s T x2
  | ._at_strings_occur_index x1 x2 x3 => mentions s T x1 || mentions s T x2 || mentions s T x3
  | ._at_strings_occur_index_re x1 x2 x3 => mentions s T x1 || mentions s T x2 || mentions s T x3
  | .choice _ _ x3 => mentions s T x3
  | .set_empty _ => false
  | .set_singleton x1 => mentions s T x1
  | .set_union x1 x2 => mentions s T x1 || mentions s T x2
  | .set_inter x1 x2 => mentions s T x1 || mentions s T x2
  | .set_minus x1 x2 => mentions s T x1 || mentions s T x2
  | .set_member x1 x2 => mentions s T x1 || mentions s T x2
  | .set_subset x1 x2 => mentions s T x1 || mentions s T x2
  | .qdiv x1 x2 => mentions s T x1 || mentions s T x2
  | .qdiv_total x1 x2 => mentions s T x1 || mentions s T x2
  | .forall _ _ x3 => mentions s T x3
  | .exists _ _ x3 => mentions s T x3
  | .bind _ _ x3 x4 => mentions s T x3 || mentions s T x4
  | .int_to_bv x1 x2 => mentions s T x1 || mentions s T x2
  | .ubv_to_int x1 => mentions s T x1
  | .sbv_to_int x1 => mentions s T x1

/-- Adds the names of the constants that a term mentions to `acc`. -/
def addNames (acc : Std.HashSet native_String) : SmtTerm → Std.HashSet native_String
  | .None => acc
  | .Boolean _ => acc
  | .Numeral _ => acc
  | .Rational _ => acc
  | .String _ => acc
  | .Binary _ _ => acc
  | .Apply x1 x2 => addNames (addNames acc x1) x2
  | .Var _ _ => acc
  | .DtCons _ _ _ => acc
  | .DtSel _ _ _ _ => acc
  | .DtTester _ _ _ => acc
  | .UConst s' _ => acc.insert s'
  | .ite x1 x2 x3 => addNames (addNames (addNames acc x1) x2) x3
  | .not x1 => addNames acc x1
  | .or x1 x2 => addNames (addNames acc x1) x2
  | .and x1 x2 => addNames (addNames acc x1) x2
  | .imp x1 x2 => addNames (addNames acc x1) x2
  | .xor x1 x2 => addNames (addNames acc x1) x2
  | .eq x1 x2 => addNames (addNames acc x1) x2
  | ._at_purify x1 => addNames acc x1
  | .plus x1 x2 => addNames (addNames acc x1) x2
  | .neg x1 x2 => addNames (addNames acc x1) x2
  | .mult x1 x2 => addNames (addNames acc x1) x2
  | .lt x1 x2 => addNames (addNames acc x1) x2
  | .leq x1 x2 => addNames (addNames acc x1) x2
  | .gt x1 x2 => addNames (addNames acc x1) x2
  | .geq x1 x2 => addNames (addNames acc x1) x2
  | .to_real x1 => addNames acc x1
  | .to_int x1 => addNames acc x1
  | .is_int x1 => addNames acc x1
  | .abs x1 => addNames acc x1
  | .uneg x1 => addNames acc x1
  | .div x1 x2 => addNames (addNames acc x1) x2
  | .mod x1 x2 => addNames (addNames acc x1) x2
  | .divisible x1 x2 => addNames (addNames acc x1) x2
  | .int_pow2 x1 => addNames acc x1
  | .int_log2 x1 => addNames acc x1
  | .div_total x1 x2 => addNames (addNames acc x1) x2
  | .mod_total x1 x2 => addNames (addNames acc x1) x2
  | .select x1 x2 => addNames (addNames acc x1) x2
  | .store x1 x2 x3 => addNames (addNames (addNames acc x1) x2) x3
  | .map_diff x1 x2 => addNames (addNames acc x1) x2
  | .concat x1 x2 => addNames (addNames acc x1) x2
  | .extract x1 x2 x3 => addNames (addNames (addNames acc x1) x2) x3
  | .repeat x1 x2 => addNames (addNames acc x1) x2
  | .bvnot x1 => addNames acc x1
  | .bvand x1 x2 => addNames (addNames acc x1) x2
  | .bvor x1 x2 => addNames (addNames acc x1) x2
  | .bvnand x1 x2 => addNames (addNames acc x1) x2
  | .bvnor x1 x2 => addNames (addNames acc x1) x2
  | .bvxor x1 x2 => addNames (addNames acc x1) x2
  | .bvxnor x1 x2 => addNames (addNames acc x1) x2
  | .bvcomp x1 x2 => addNames (addNames acc x1) x2
  | .bvneg x1 => addNames acc x1
  | .bvadd x1 x2 => addNames (addNames acc x1) x2
  | .bvmul x1 x2 => addNames (addNames acc x1) x2
  | .bvudiv x1 x2 => addNames (addNames acc x1) x2
  | .bvurem x1 x2 => addNames (addNames acc x1) x2
  | .bvsub x1 x2 => addNames (addNames acc x1) x2
  | .bvsdiv x1 x2 => addNames (addNames acc x1) x2
  | .bvsrem x1 x2 => addNames (addNames acc x1) x2
  | .bvsmod x1 x2 => addNames (addNames acc x1) x2
  | .bvult x1 x2 => addNames (addNames acc x1) x2
  | .bvule x1 x2 => addNames (addNames acc x1) x2
  | .bvugt x1 x2 => addNames (addNames acc x1) x2
  | .bvuge x1 x2 => addNames (addNames acc x1) x2
  | .bvslt x1 x2 => addNames (addNames acc x1) x2
  | .bvsle x1 x2 => addNames (addNames acc x1) x2
  | .bvsgt x1 x2 => addNames (addNames acc x1) x2
  | .bvsge x1 x2 => addNames (addNames acc x1) x2
  | .bvshl x1 x2 => addNames (addNames acc x1) x2
  | .bvlshr x1 x2 => addNames (addNames acc x1) x2
  | .bvashr x1 x2 => addNames (addNames acc x1) x2
  | .zero_extend x1 x2 => addNames (addNames acc x1) x2
  | .sign_extend x1 x2 => addNames (addNames acc x1) x2
  | .rotate_left x1 x2 => addNames (addNames acc x1) x2
  | .rotate_right x1 x2 => addNames (addNames acc x1) x2
  | .bvuaddo x1 x2 => addNames (addNames acc x1) x2
  | .bvnego x1 => addNames acc x1
  | .bvsaddo x1 x2 => addNames (addNames acc x1) x2
  | .bvumulo x1 x2 => addNames (addNames acc x1) x2
  | .bvsmulo x1 x2 => addNames (addNames acc x1) x2
  | .bvusubo x1 x2 => addNames (addNames acc x1) x2
  | .bvssubo x1 x2 => addNames (addNames acc x1) x2
  | .bvsdivo x1 x2 => addNames (addNames acc x1) x2
  | .seq_empty _ => acc
  | .str_len x1 => addNames acc x1
  | .str_concat x1 x2 => addNames (addNames acc x1) x2
  | .str_substr x1 x2 x3 => addNames (addNames (addNames acc x1) x2) x3
  | .str_contains x1 x2 => addNames (addNames acc x1) x2
  | .str_replace x1 x2 x3 => addNames (addNames (addNames acc x1) x2) x3
  | .str_indexof x1 x2 x3 => addNames (addNames (addNames acc x1) x2) x3
  | .str_at x1 x2 => addNames (addNames acc x1) x2
  | .str_prefixof x1 x2 => addNames (addNames acc x1) x2
  | .str_suffixof x1 x2 => addNames (addNames acc x1) x2
  | .str_rev x1 => addNames acc x1
  | .str_update x1 x2 x3 => addNames (addNames (addNames acc x1) x2) x3
  | .str_to_lower x1 => addNames acc x1
  | .str_to_upper x1 => addNames acc x1
  | .str_to_code x1 => addNames acc x1
  | .str_from_code x1 => addNames acc x1
  | .str_is_digit x1 => addNames acc x1
  | .str_to_int x1 => addNames acc x1
  | .str_from_int x1 => addNames acc x1
  | .str_lt x1 x2 => addNames (addNames acc x1) x2
  | .str_leq x1 x2 => addNames (addNames acc x1) x2
  | .str_replace_all x1 x2 x3 => addNames (addNames (addNames acc x1) x2) x3
  | .str_replace_re x1 x2 x3 => addNames (addNames (addNames acc x1) x2) x3
  | .str_replace_re_all x1 x2 x3 => addNames (addNames (addNames acc x1) x2) x3
  | .str_indexof_re x1 x2 x3 => addNames (addNames (addNames acc x1) x2) x3
  | .re_allchar => acc
  | .re_none => acc
  | .re_all => acc
  | .str_to_re x1 => addNames acc x1
  | .re_mult x1 => addNames acc x1
  | .re_plus x1 => addNames acc x1
  | .re_exp x1 x2 => addNames (addNames acc x1) x2
  | .re_opt x1 => addNames acc x1
  | .re_comp x1 => addNames acc x1
  | .re_range x1 x2 => addNames (addNames acc x1) x2
  | .re_concat x1 x2 => addNames (addNames acc x1) x2
  | .re_inter x1 x2 => addNames (addNames acc x1) x2
  | .re_union x1 x2 => addNames (addNames acc x1) x2
  | .re_diff x1 x2 => addNames (addNames acc x1) x2
  | .re_loop x1 x2 x3 => addNames (addNames (addNames acc x1) x2) x3
  | .str_in_re x1 x2 => addNames (addNames acc x1) x2
  | .seq_unit x1 => addNames acc x1
  | .seq_nth x1 x2 => addNames (addNames acc x1) x2
  | .str_indexof_re_split x1 x2 x3 => addNames (addNames (addNames acc x1) x2) x3
  | .seq_diff x1 x2 => addNames (addNames acc x1) x2
  | ._at_strings_occur_index x1 x2 x3 => addNames (addNames (addNames acc x1) x2) x3
  | ._at_strings_occur_index_re x1 x2 x3 => addNames (addNames (addNames acc x1) x2) x3
  | .choice _ _ x3 => addNames acc x3
  | .set_empty _ => acc
  | .set_singleton x1 => addNames acc x1
  | .set_union x1 x2 => addNames (addNames acc x1) x2
  | .set_inter x1 x2 => addNames (addNames acc x1) x2
  | .set_minus x1 x2 => addNames (addNames acc x1) x2
  | .set_member x1 x2 => addNames (addNames acc x1) x2
  | .set_subset x1 x2 => addNames (addNames acc x1) x2
  | .qdiv x1 x2 => addNames (addNames acc x1) x2
  | .qdiv_total x1 x2 => addNames (addNames acc x1) x2
  | .forall _ _ x3 => addNames acc x3
  | .exists _ _ x3 => addNames acc x3
  | .bind _ _ x3 x4 => addNames (addNames acc x3) x4
  | .int_to_bv x1 x2 => addNames (addNames acc x1) x2
  | .ubv_to_int x1 => addNames acc x1
  | .sbv_to_int x1 => addNames acc x1

/-- The first two characters of the names Logos reserves for the interpretation of partial
operators. -/
def reservedPrefixes : List native_String :=
  ["@d", "@m", "@q", "@o", "@w"].map native_string_lit

/-- `s` does not start like a name Logos reserves for the interpretation of partial operators. -/
def Unreserved (s : native_String) : Prop := s.take 2 ∉ reservedPrefixes

instance : DecidablePred Unreserved := fun s =>
  inferInstanceAs (Decidable (s.take 2 ∉ reservedPrefixes))

/-! ## Substituting terms for constants -/

/-- The term that `σ` substitutes for the constant `s` of sort `T`: its first binding of it, if
it has one. -/
def substConst (σ : List (native_String × SmtType × SmtTerm)) (s : native_String) (T : SmtType) :
    SmtTerm :=
  match σ.find? (fun e => e.1 == s && e.2.1 == T) with
  | some e => e.2.2
  | none => .UConst s T

/-- `t` with the constants that `σ` binds replaced by their terms, binders included: the results
of `Inox/Unfold.lean` are about terms without binders, where no capture can happen. -/
def substSmt (σ : List (native_String × SmtType × SmtTerm)) : SmtTerm → SmtTerm
  | .None => .None
  | .Boolean x1 => .Boolean x1
  | .Numeral x1 => .Numeral x1
  | .Rational x1 => .Rational x1
  | .String x1 => .String x1
  | .Binary x1 x2 => .Binary x1 x2
  | .Apply x1 x2 => .Apply (substSmt σ x1) (substSmt σ x2)
  | .Var x1 x2 => .Var x1 x2
  | .DtCons x1 x2 x3 => .DtCons x1 x2 x3
  | .DtSel x1 x2 x3 x4 => .DtSel x1 x2 x3 x4
  | .DtTester x1 x2 x3 => .DtTester x1 x2 x3
  | .UConst s T => substConst σ s T
  | .ite x1 x2 x3 => .ite (substSmt σ x1) (substSmt σ x2) (substSmt σ x3)
  | .not x1 => .not (substSmt σ x1)
  | .or x1 x2 => .or (substSmt σ x1) (substSmt σ x2)
  | .and x1 x2 => .and (substSmt σ x1) (substSmt σ x2)
  | .imp x1 x2 => .imp (substSmt σ x1) (substSmt σ x2)
  | .xor x1 x2 => .xor (substSmt σ x1) (substSmt σ x2)
  | .eq x1 x2 => .eq (substSmt σ x1) (substSmt σ x2)
  | ._at_purify x1 => ._at_purify (substSmt σ x1)
  | .plus x1 x2 => .plus (substSmt σ x1) (substSmt σ x2)
  | .neg x1 x2 => .neg (substSmt σ x1) (substSmt σ x2)
  | .mult x1 x2 => .mult (substSmt σ x1) (substSmt σ x2)
  | .lt x1 x2 => .lt (substSmt σ x1) (substSmt σ x2)
  | .leq x1 x2 => .leq (substSmt σ x1) (substSmt σ x2)
  | .gt x1 x2 => .gt (substSmt σ x1) (substSmt σ x2)
  | .geq x1 x2 => .geq (substSmt σ x1) (substSmt σ x2)
  | .to_real x1 => .to_real (substSmt σ x1)
  | .to_int x1 => .to_int (substSmt σ x1)
  | .is_int x1 => .is_int (substSmt σ x1)
  | .abs x1 => .abs (substSmt σ x1)
  | .uneg x1 => .uneg (substSmt σ x1)
  | .div x1 x2 => .div (substSmt σ x1) (substSmt σ x2)
  | .mod x1 x2 => .mod (substSmt σ x1) (substSmt σ x2)
  | .divisible x1 x2 => .divisible (substSmt σ x1) (substSmt σ x2)
  | .int_pow2 x1 => .int_pow2 (substSmt σ x1)
  | .int_log2 x1 => .int_log2 (substSmt σ x1)
  | .div_total x1 x2 => .div_total (substSmt σ x1) (substSmt σ x2)
  | .mod_total x1 x2 => .mod_total (substSmt σ x1) (substSmt σ x2)
  | .select x1 x2 => .select (substSmt σ x1) (substSmt σ x2)
  | .store x1 x2 x3 => .store (substSmt σ x1) (substSmt σ x2) (substSmt σ x3)
  | .map_diff x1 x2 => .map_diff (substSmt σ x1) (substSmt σ x2)
  | .concat x1 x2 => .concat (substSmt σ x1) (substSmt σ x2)
  | .extract x1 x2 x3 => .extract (substSmt σ x1) (substSmt σ x2) (substSmt σ x3)
  | .repeat x1 x2 => .repeat (substSmt σ x1) (substSmt σ x2)
  | .bvnot x1 => .bvnot (substSmt σ x1)
  | .bvand x1 x2 => .bvand (substSmt σ x1) (substSmt σ x2)
  | .bvor x1 x2 => .bvor (substSmt σ x1) (substSmt σ x2)
  | .bvnand x1 x2 => .bvnand (substSmt σ x1) (substSmt σ x2)
  | .bvnor x1 x2 => .bvnor (substSmt σ x1) (substSmt σ x2)
  | .bvxor x1 x2 => .bvxor (substSmt σ x1) (substSmt σ x2)
  | .bvxnor x1 x2 => .bvxnor (substSmt σ x1) (substSmt σ x2)
  | .bvcomp x1 x2 => .bvcomp (substSmt σ x1) (substSmt σ x2)
  | .bvneg x1 => .bvneg (substSmt σ x1)
  | .bvadd x1 x2 => .bvadd (substSmt σ x1) (substSmt σ x2)
  | .bvmul x1 x2 => .bvmul (substSmt σ x1) (substSmt σ x2)
  | .bvudiv x1 x2 => .bvudiv (substSmt σ x1) (substSmt σ x2)
  | .bvurem x1 x2 => .bvurem (substSmt σ x1) (substSmt σ x2)
  | .bvsub x1 x2 => .bvsub (substSmt σ x1) (substSmt σ x2)
  | .bvsdiv x1 x2 => .bvsdiv (substSmt σ x1) (substSmt σ x2)
  | .bvsrem x1 x2 => .bvsrem (substSmt σ x1) (substSmt σ x2)
  | .bvsmod x1 x2 => .bvsmod (substSmt σ x1) (substSmt σ x2)
  | .bvult x1 x2 => .bvult (substSmt σ x1) (substSmt σ x2)
  | .bvule x1 x2 => .bvule (substSmt σ x1) (substSmt σ x2)
  | .bvugt x1 x2 => .bvugt (substSmt σ x1) (substSmt σ x2)
  | .bvuge x1 x2 => .bvuge (substSmt σ x1) (substSmt σ x2)
  | .bvslt x1 x2 => .bvslt (substSmt σ x1) (substSmt σ x2)
  | .bvsle x1 x2 => .bvsle (substSmt σ x1) (substSmt σ x2)
  | .bvsgt x1 x2 => .bvsgt (substSmt σ x1) (substSmt σ x2)
  | .bvsge x1 x2 => .bvsge (substSmt σ x1) (substSmt σ x2)
  | .bvshl x1 x2 => .bvshl (substSmt σ x1) (substSmt σ x2)
  | .bvlshr x1 x2 => .bvlshr (substSmt σ x1) (substSmt σ x2)
  | .bvashr x1 x2 => .bvashr (substSmt σ x1) (substSmt σ x2)
  | .zero_extend x1 x2 => .zero_extend (substSmt σ x1) (substSmt σ x2)
  | .sign_extend x1 x2 => .sign_extend (substSmt σ x1) (substSmt σ x2)
  | .rotate_left x1 x2 => .rotate_left (substSmt σ x1) (substSmt σ x2)
  | .rotate_right x1 x2 => .rotate_right (substSmt σ x1) (substSmt σ x2)
  | .bvuaddo x1 x2 => .bvuaddo (substSmt σ x1) (substSmt σ x2)
  | .bvnego x1 => .bvnego (substSmt σ x1)
  | .bvsaddo x1 x2 => .bvsaddo (substSmt σ x1) (substSmt σ x2)
  | .bvumulo x1 x2 => .bvumulo (substSmt σ x1) (substSmt σ x2)
  | .bvsmulo x1 x2 => .bvsmulo (substSmt σ x1) (substSmt σ x2)
  | .bvusubo x1 x2 => .bvusubo (substSmt σ x1) (substSmt σ x2)
  | .bvssubo x1 x2 => .bvssubo (substSmt σ x1) (substSmt σ x2)
  | .bvsdivo x1 x2 => .bvsdivo (substSmt σ x1) (substSmt σ x2)
  | .seq_empty x1 => .seq_empty x1
  | .str_len x1 => .str_len (substSmt σ x1)
  | .str_concat x1 x2 => .str_concat (substSmt σ x1) (substSmt σ x2)
  | .str_substr x1 x2 x3 => .str_substr (substSmt σ x1) (substSmt σ x2) (substSmt σ x3)
  | .str_contains x1 x2 => .str_contains (substSmt σ x1) (substSmt σ x2)
  | .str_replace x1 x2 x3 => .str_replace (substSmt σ x1) (substSmt σ x2) (substSmt σ x3)
  | .str_indexof x1 x2 x3 => .str_indexof (substSmt σ x1) (substSmt σ x2) (substSmt σ x3)
  | .str_at x1 x2 => .str_at (substSmt σ x1) (substSmt σ x2)
  | .str_prefixof x1 x2 => .str_prefixof (substSmt σ x1) (substSmt σ x2)
  | .str_suffixof x1 x2 => .str_suffixof (substSmt σ x1) (substSmt σ x2)
  | .str_rev x1 => .str_rev (substSmt σ x1)
  | .str_update x1 x2 x3 => .str_update (substSmt σ x1) (substSmt σ x2) (substSmt σ x3)
  | .str_to_lower x1 => .str_to_lower (substSmt σ x1)
  | .str_to_upper x1 => .str_to_upper (substSmt σ x1)
  | .str_to_code x1 => .str_to_code (substSmt σ x1)
  | .str_from_code x1 => .str_from_code (substSmt σ x1)
  | .str_is_digit x1 => .str_is_digit (substSmt σ x1)
  | .str_to_int x1 => .str_to_int (substSmt σ x1)
  | .str_from_int x1 => .str_from_int (substSmt σ x1)
  | .str_lt x1 x2 => .str_lt (substSmt σ x1) (substSmt σ x2)
  | .str_leq x1 x2 => .str_leq (substSmt σ x1) (substSmt σ x2)
  | .str_replace_all x1 x2 x3 => .str_replace_all (substSmt σ x1) (substSmt σ x2) (substSmt σ x3)
  | .str_replace_re x1 x2 x3 => .str_replace_re (substSmt σ x1) (substSmt σ x2) (substSmt σ x3)
  | .str_replace_re_all x1 x2 x3 =>
    .str_replace_re_all (substSmt σ x1) (substSmt σ x2) (substSmt σ x3)
  | .str_indexof_re x1 x2 x3 => .str_indexof_re (substSmt σ x1) (substSmt σ x2) (substSmt σ x3)
  | .re_allchar => .re_allchar
  | .re_none => .re_none
  | .re_all => .re_all
  | .str_to_re x1 => .str_to_re (substSmt σ x1)
  | .re_mult x1 => .re_mult (substSmt σ x1)
  | .re_plus x1 => .re_plus (substSmt σ x1)
  | .re_exp x1 x2 => .re_exp (substSmt σ x1) (substSmt σ x2)
  | .re_opt x1 => .re_opt (substSmt σ x1)
  | .re_comp x1 => .re_comp (substSmt σ x1)
  | .re_range x1 x2 => .re_range (substSmt σ x1) (substSmt σ x2)
  | .re_concat x1 x2 => .re_concat (substSmt σ x1) (substSmt σ x2)
  | .re_inter x1 x2 => .re_inter (substSmt σ x1) (substSmt σ x2)
  | .re_union x1 x2 => .re_union (substSmt σ x1) (substSmt σ x2)
  | .re_diff x1 x2 => .re_diff (substSmt σ x1) (substSmt σ x2)
  | .re_loop x1 x2 x3 => .re_loop (substSmt σ x1) (substSmt σ x2) (substSmt σ x3)
  | .str_in_re x1 x2 => .str_in_re (substSmt σ x1) (substSmt σ x2)
  | .seq_unit x1 => .seq_unit (substSmt σ x1)
  | .seq_nth x1 x2 => .seq_nth (substSmt σ x1) (substSmt σ x2)
  | .str_indexof_re_split x1 x2 x3 =>
    .str_indexof_re_split (substSmt σ x1) (substSmt σ x2) (substSmt σ x3)
  | .seq_diff x1 x2 => .seq_diff (substSmt σ x1) (substSmt σ x2)
  | ._at_strings_occur_index x1 x2 x3 =>
    ._at_strings_occur_index (substSmt σ x1) (substSmt σ x2) (substSmt σ x3)
  | ._at_strings_occur_index_re x1 x2 x3 =>
    ._at_strings_occur_index_re (substSmt σ x1) (substSmt σ x2) (substSmt σ x3)
  | .choice x1 x2 x3 => .choice x1 x2 (substSmt σ x3)
  | .set_empty x1 => .set_empty x1
  | .set_singleton x1 => .set_singleton (substSmt σ x1)
  | .set_union x1 x2 => .set_union (substSmt σ x1) (substSmt σ x2)
  | .set_inter x1 x2 => .set_inter (substSmt σ x1) (substSmt σ x2)
  | .set_minus x1 x2 => .set_minus (substSmt σ x1) (substSmt σ x2)
  | .set_member x1 x2 => .set_member (substSmt σ x1) (substSmt σ x2)
  | .set_subset x1 x2 => .set_subset (substSmt σ x1) (substSmt σ x2)
  | .qdiv x1 x2 => .qdiv (substSmt σ x1) (substSmt σ x2)
  | .qdiv_total x1 x2 => .qdiv_total (substSmt σ x1) (substSmt σ x2)
  | .«forall» x1 x2 x3 => .«forall» x1 x2 (substSmt σ x3)
  | .«exists» x1 x2 x3 => .«exists» x1 x2 (substSmt σ x3)
  | .bind x1 x2 x3 x4 => .bind x1 x2 (substSmt σ x3) (substSmt σ x4)
  | .int_to_bv x1 x2 => .int_to_bv (substSmt σ x1) (substSmt σ x2)
  | .ubv_to_int x1 => .ubv_to_int (substSmt σ x1)
  | .sbv_to_int x1 => .sbv_to_int (substSmt σ x1)

/-- Whether a term has no binder (`forall`, `exists`, `choice`, `bind`). -/
def noBinder : SmtTerm → Bool
  | .None => true
  | .Boolean _ => true
  | .Numeral _ => true
  | .Rational _ => true
  | .String _ => true
  | .Binary _ _ => true
  | .Apply x1 x2 => noBinder x1 && noBinder x2
  | .Var _ _ => true
  | .DtCons _ _ _ => true
  | .DtSel _ _ _ _ => true
  | .DtTester _ _ _ => true
  | .UConst _ _ => true
  | .ite x1 x2 x3 => noBinder x1 && noBinder x2 && noBinder x3
  | .not x1 => noBinder x1
  | .or x1 x2 => noBinder x1 && noBinder x2
  | .and x1 x2 => noBinder x1 && noBinder x2
  | .imp x1 x2 => noBinder x1 && noBinder x2
  | .xor x1 x2 => noBinder x1 && noBinder x2
  | .eq x1 x2 => noBinder x1 && noBinder x2
  | ._at_purify x1 => noBinder x1
  | .plus x1 x2 => noBinder x1 && noBinder x2
  | .neg x1 x2 => noBinder x1 && noBinder x2
  | .mult x1 x2 => noBinder x1 && noBinder x2
  | .lt x1 x2 => noBinder x1 && noBinder x2
  | .leq x1 x2 => noBinder x1 && noBinder x2
  | .gt x1 x2 => noBinder x1 && noBinder x2
  | .geq x1 x2 => noBinder x1 && noBinder x2
  | .to_real x1 => noBinder x1
  | .to_int x1 => noBinder x1
  | .is_int x1 => noBinder x1
  | .abs x1 => noBinder x1
  | .uneg x1 => noBinder x1
  | .div x1 x2 => noBinder x1 && noBinder x2
  | .mod x1 x2 => noBinder x1 && noBinder x2
  | .divisible x1 x2 => noBinder x1 && noBinder x2
  | .int_pow2 x1 => noBinder x1
  | .int_log2 x1 => noBinder x1
  | .div_total x1 x2 => noBinder x1 && noBinder x2
  | .mod_total x1 x2 => noBinder x1 && noBinder x2
  | .select x1 x2 => noBinder x1 && noBinder x2
  | .store x1 x2 x3 => noBinder x1 && noBinder x2 && noBinder x3
  | .map_diff x1 x2 => noBinder x1 && noBinder x2
  | .concat x1 x2 => noBinder x1 && noBinder x2
  | .extract x1 x2 x3 => noBinder x1 && noBinder x2 && noBinder x3
  | .repeat x1 x2 => noBinder x1 && noBinder x2
  | .bvnot x1 => noBinder x1
  | .bvand x1 x2 => noBinder x1 && noBinder x2
  | .bvor x1 x2 => noBinder x1 && noBinder x2
  | .bvnand x1 x2 => noBinder x1 && noBinder x2
  | .bvnor x1 x2 => noBinder x1 && noBinder x2
  | .bvxor x1 x2 => noBinder x1 && noBinder x2
  | .bvxnor x1 x2 => noBinder x1 && noBinder x2
  | .bvcomp x1 x2 => noBinder x1 && noBinder x2
  | .bvneg x1 => noBinder x1
  | .bvadd x1 x2 => noBinder x1 && noBinder x2
  | .bvmul x1 x2 => noBinder x1 && noBinder x2
  | .bvudiv x1 x2 => noBinder x1 && noBinder x2
  | .bvurem x1 x2 => noBinder x1 && noBinder x2
  | .bvsub x1 x2 => noBinder x1 && noBinder x2
  | .bvsdiv x1 x2 => noBinder x1 && noBinder x2
  | .bvsrem x1 x2 => noBinder x1 && noBinder x2
  | .bvsmod x1 x2 => noBinder x1 && noBinder x2
  | .bvult x1 x2 => noBinder x1 && noBinder x2
  | .bvule x1 x2 => noBinder x1 && noBinder x2
  | .bvugt x1 x2 => noBinder x1 && noBinder x2
  | .bvuge x1 x2 => noBinder x1 && noBinder x2
  | .bvslt x1 x2 => noBinder x1 && noBinder x2
  | .bvsle x1 x2 => noBinder x1 && noBinder x2
  | .bvsgt x1 x2 => noBinder x1 && noBinder x2
  | .bvsge x1 x2 => noBinder x1 && noBinder x2
  | .bvshl x1 x2 => noBinder x1 && noBinder x2
  | .bvlshr x1 x2 => noBinder x1 && noBinder x2
  | .bvashr x1 x2 => noBinder x1 && noBinder x2
  | .zero_extend x1 x2 => noBinder x1 && noBinder x2
  | .sign_extend x1 x2 => noBinder x1 && noBinder x2
  | .rotate_left x1 x2 => noBinder x1 && noBinder x2
  | .rotate_right x1 x2 => noBinder x1 && noBinder x2
  | .bvuaddo x1 x2 => noBinder x1 && noBinder x2
  | .bvnego x1 => noBinder x1
  | .bvsaddo x1 x2 => noBinder x1 && noBinder x2
  | .bvumulo x1 x2 => noBinder x1 && noBinder x2
  | .bvsmulo x1 x2 => noBinder x1 && noBinder x2
  | .bvusubo x1 x2 => noBinder x1 && noBinder x2
  | .bvssubo x1 x2 => noBinder x1 && noBinder x2
  | .bvsdivo x1 x2 => noBinder x1 && noBinder x2
  | .seq_empty _ => true
  | .str_len x1 => noBinder x1
  | .str_concat x1 x2 => noBinder x1 && noBinder x2
  | .str_substr x1 x2 x3 => noBinder x1 && noBinder x2 && noBinder x3
  | .str_contains x1 x2 => noBinder x1 && noBinder x2
  | .str_replace x1 x2 x3 => noBinder x1 && noBinder x2 && noBinder x3
  | .str_indexof x1 x2 x3 => noBinder x1 && noBinder x2 && noBinder x3
  | .str_at x1 x2 => noBinder x1 && noBinder x2
  | .str_prefixof x1 x2 => noBinder x1 && noBinder x2
  | .str_suffixof x1 x2 => noBinder x1 && noBinder x2
  | .str_rev x1 => noBinder x1
  | .str_update x1 x2 x3 => noBinder x1 && noBinder x2 && noBinder x3
  | .str_to_lower x1 => noBinder x1
  | .str_to_upper x1 => noBinder x1
  | .str_to_code x1 => noBinder x1
  | .str_from_code x1 => noBinder x1
  | .str_is_digit x1 => noBinder x1
  | .str_to_int x1 => noBinder x1
  | .str_from_int x1 => noBinder x1
  | .str_lt x1 x2 => noBinder x1 && noBinder x2
  | .str_leq x1 x2 => noBinder x1 && noBinder x2
  | .str_replace_all x1 x2 x3 => noBinder x1 && noBinder x2 && noBinder x3
  | .str_replace_re x1 x2 x3 => noBinder x1 && noBinder x2 && noBinder x3
  | .str_replace_re_all x1 x2 x3 => noBinder x1 && noBinder x2 && noBinder x3
  | .str_indexof_re x1 x2 x3 => noBinder x1 && noBinder x2 && noBinder x3
  | .re_allchar => true
  | .re_none => true
  | .re_all => true
  | .str_to_re x1 => noBinder x1
  | .re_mult x1 => noBinder x1
  | .re_plus x1 => noBinder x1
  | .re_exp x1 x2 => noBinder x1 && noBinder x2
  | .re_opt x1 => noBinder x1
  | .re_comp x1 => noBinder x1
  | .re_range x1 x2 => noBinder x1 && noBinder x2
  | .re_concat x1 x2 => noBinder x1 && noBinder x2
  | .re_inter x1 x2 => noBinder x1 && noBinder x2
  | .re_union x1 x2 => noBinder x1 && noBinder x2
  | .re_diff x1 x2 => noBinder x1 && noBinder x2
  | .re_loop x1 x2 x3 => noBinder x1 && noBinder x2 && noBinder x3
  | .str_in_re x1 x2 => noBinder x1 && noBinder x2
  | .seq_unit x1 => noBinder x1
  | .seq_nth x1 x2 => noBinder x1 && noBinder x2
  | .str_indexof_re_split x1 x2 x3 => noBinder x1 && noBinder x2 && noBinder x3
  | .seq_diff x1 x2 => noBinder x1 && noBinder x2
  | ._at_strings_occur_index x1 x2 x3 => noBinder x1 && noBinder x2 && noBinder x3
  | ._at_strings_occur_index_re x1 x2 x3 => noBinder x1 && noBinder x2 && noBinder x3
  | .choice _ _ _ => false
  | .set_empty _ => true
  | .set_singleton x1 => noBinder x1
  | .set_union x1 x2 => noBinder x1 && noBinder x2
  | .set_inter x1 x2 => noBinder x1 && noBinder x2
  | .set_minus x1 x2 => noBinder x1 && noBinder x2
  | .set_member x1 x2 => noBinder x1 && noBinder x2
  | .set_subset x1 x2 => noBinder x1 && noBinder x2
  | .qdiv x1 x2 => noBinder x1 && noBinder x2
  | .qdiv_total x1 x2 => noBinder x1 && noBinder x2
  | .«forall» _ _ _ => false
  | .«exists» _ _ _ => false
  | .bind _ _ _ _ => false
  | .int_to_bv x1 x2 => noBinder x1 && noBinder x2
  | .ubv_to_int x1 => noBinder x1
  | .sbv_to_int x1 => noBinder x1

/-- Whether a term is not a selector or a tester, which Logos evaluates apart when they are
applied. -/
def plainHead : SmtTerm → Bool
  | .DtSel _ _ _ _ => false
  | .DtTester _ _ _ => false
  | _ => true

end Inox.Fresh

namespace Inox.Extend

open Eo
open SmtEval
open Smtm

/-! ## The clauses, as Logos reads them -/

/-- `(= a b)` -/
def mkEq (a b : Term) : Term := Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b
/-- `(=> a b)` -/
def mkImp (a b : Term) : Term := Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b
/-- `(and a b)` -/
def mkAnd (a b : Term) : Term := Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b

/-! ## Sequences of steps -/

/-- A rule: one that introduces a fresh constant, with the terms its clauses are built from, or a
fact about the semantics. -/
inductive Step where
  /-- `(= c rhs)` -/
  | define (c rhs : Term)
  /-- `(=> g (= c rhs))` -/
  | defineGuarded (c g rhs : Term)
  /-- `c` -/
  | root (c : Term)
  /-- `(=> (and c a) f)` -/
  | hypothesis (c a f : Term)
  /-- `(=> b c)` for each `b` of `bs` -/
  | enables (c : Term) (bs : List Term)
  /-- `t`, a fact about the semantics -/
  | fact (t : Term)

namespace Step

/-- Whether the step is a fact. -/
def isFact : Step → Bool
  | fact _ => true
  | _ => false

/-- The fresh constant (the fact itself, for a fact). -/
def const : Step → Term
  | define c _ | defineGuarded c _ _ | root c | hypothesis c _ _ | enables c _ | fact c => c

/-- The terms besides the fresh constant that the clauses are built from. -/
def parts : Step → List Term
  | define _ rhs => [rhs]
  | defineGuarded _ g rhs => [g, rhs]
  | root _ => []
  | hypothesis _ a f => [a, f]
  | enables _ bs => bs
  | fact _ => []

/-- The clauses of the step. -/
def clauses : Step → List Term
  | define c rhs => [mkEq c rhs]
  | defineGuarded c g rhs => [mkImp g (mkEq c rhs)]
  | root c => [c]
  | hypothesis c a f => [mkImp (mkAnd c a) f]
  | enables c bs => bs.map fun b => mkImp b c
  | fact t => [t]

end Step

/-- The assumptions `assums` followed by the clauses of the steps `sts`. -/
def extend (assums : List Term) (sts : List Step) : List Term :=
  sts.foldl (fun acc st => acc ++ st.clauses) assums

end Inox.Extend

namespace Inox

open Logos (Sexp)
open Eo
open Smtm
open Inox.Fresh
open Inox.Extend

/-! ## The text of the clauses -/

private def declarationHeads : List String :=
  ["declare-const", "declare-fun", "declare-sort", "declare-datatype", "declare-datatypes",
    "define"]

/-- The names that a declaration declares, if it is one. -/
def declaredNames : Sexp → Option (List String)
  | .expr (.atom head :: rest) =>
    if !declarationHeads.contains head then none
    else match head, rest with
      | "declare-datatypes", .expr sorts :: _ =>
        some (sorts.filterMap fun s => match s with
          | .expr (.atom n :: _) => some n
          | _ => none)
      | _, .atom n :: _ => some [n]
      | _, _ => none
  | _ => none

/-- The proof's declarations, followed by the script's that declare names the proof doesn't. -/
def declarations (checked : Checked) : List Sexp :=
  let ofProof := checked.cpc.filter fun c => (declaredNames c).isSome
  let names : Std.HashSet String :=
    Std.HashSet.ofList (ofProof.flatMap fun c => (declaredNames c).getD [])
  let ofScript := checked.script.filter fun c => match declaredNames c with
    | some ns => !ns.isEmpty && ns.all (!names.contains ·)
    | none => false
  ofProof ++ ofScript

/-- The clauses: those of the query's assumptions, of each rule, and of the completeness
assumptions. -/
def allClauses (checked : Checked) : List Sexp :=
  checked.query ++ checked.applied.flatMap (·.2) ++ checked.complete

/-- The declarations and one `assume` per clause. -/
def clauseText (checked : Checked) : String :=
  let assumes := (allClauses checked).zipIdx.map fun (c, i) =>
    Sexp.expr [.atom "assume", .atom s!"inox.clause.{i}", c]
  "\n".intercalate ((declarations checked ++ assumes).map text) ++ "\n"

/-! ## Steps -/

/-- The fresh-symbol step of a clause of a rule of kind `kind`. -/
def freshStep (kind : String) (t : Term) : Except String Step :=
  match kind, t with
  | "Define", .Apply (.Apply (.UOp .imp) g) (.Apply (.Apply (.UOp .eq) c) rhs) =>
    .ok (.defineGuarded c g rhs)
  | "Define", .Apply (.Apply (.UOp .eq) c) rhs => .ok (.define c rhs)
  | "Hypothesis", .Apply (.Apply (.UOp .imp) (.Apply (.Apply (.UOp .and) c) a)) f =>
    .ok (.hypothesis c a f)
  | "Root", c => .ok (.root c)
  | _, _ => .error s!"a clause of a {kind} rule doesn't have the shape of its kind"

/-- The constants that a term mentions, by their number. -/
def uconsts (acc : Std.HashSet Nat) : Term → Std.HashSet Nat
  | .UConst i _ => acc.insert i
  | .UOp1 _ a => uconsts acc a
  | .UOp2 _ a b => uconsts (uconsts acc a) b
  | .UOp3 _ a b c => uconsts (uconsts (uconsts acc a) b) c
  | .Apply f a => uconsts (uconsts acc f) a
  | _ => acc

deriving instance Inhabited for Step

/-- The number of a constant. -/
def constNumber : Term → Option Nat
  | .UConst i _ => some i
  | _ => none

/-- The steps in an order where each step whose constant another step's clauses mention comes
before it, where there is one; the others keep their order. -/
def orderSteps (sts : List Step) : List Step := Id.run do
  let arr := sts.toArray
  let mut byConst : Std.HashMap Nat Nat := {}
  for h : j in [0:arr.size] do
    if let some i := constNumber arr[j].const then byConst := byConst.insert i j
  -- the steps that each step must follow
  let mut indeg : Array Nat := Array.replicate arr.size 0
  let mut dependents : Array (List Nat) := Array.replicate arr.size []
  for h : j in [0:arr.size] do
    let own := constNumber arr[j].const
    let mentioned := arr[j].clauses.foldl uconsts {}
    for i in mentioned do
      if some i != own then
        if let some k := byConst.get? i then
          indeg := indeg.set! j (indeg[j]! + 1)
          dependents := dependents.set! k (j :: dependents[k]!)
  let mut ready : Array Nat := #[]
  for j in [0:arr.size] do
    if indeg[j]! == 0 then ready := ready.push j
  let mut placed : Array Bool := Array.replicate arr.size false
  let mut order : Array Step := #[]
  let mut next := 0
  -- `ready` grows as the steps are placed; each step is placed once, so this terminates
  for _ in [0:arr.size] do
    if h : next < ready.size then
      let j := ready[next]
      next := next + 1
      placed := placed.set! j true
      order := order.push arr[j]!
      for k in (dependents[j]!).reverse do
        indeg := indeg.set! k (indeg[k]! - 1)
        if indeg[k]! == 0 then ready := ready.push k
  -- the steps of a cycle, as they are: the check refuses them
  for j in [0:arr.size] do
    if !placed[j]! then order := order.push arr[j]!
  return order.toList

/-- Whether `m` is a conjunct of a term: an operand of an `and` along its right spine, or the term
itself. -/
def inConj (m : Term) : Term → Bool
  | .Apply (.Apply (.UOp .and) a) rest => a == m || inConj m rest
  | t => t == m

/-- An `Enables` clause `(=> blocker target)` that follows from the definition
`(= blocker rhs)`, where `target` is a conjunct of `rhs`. -/
structure Derived where
  blocker : Term
  rhs : Term
  target : Term

/-- The clause `(=> blocker target)`. -/
def Derived.clause (d : Derived) : Term := Extend.mkImp d.blocker d.target

/-! ## The defining equations of the functions -/

/-- The defining equation `(= (f x1 … xn) body)` of a function, as Logos reads it: the term,
the parameters `x1 … xn` as Logos reads them, and their constants, which the equation holds for
all the values of. -/
structure Equation where
  term : Term
  args : List Term
  params : List (SmtEval.native_String × SmtType)

/-- The arguments of a call, if it is one. -/
def callArgs : Term → Option (List Term)
  | .Apply f a => (callArgs f).map (· ++ [a])
  | .UConst _ _ => some []
  | _ => none

/-- The defining equation that `t` is, if it is `(= (f x1 … xn) body)`, where `f` and each
`xi` are constants. -/
def equationOf (t : Term) : Option Equation :=
  match t with
  | .Apply (.Apply (.UOp .eq) call) _ => do
    let args ← callArgs call
    let params ← args.mapM fun a => match __eo_to_smt a with
      | .UConst s T => some (s, T)
      | _ => none
    some { term := t, args, params }
  | _ => none

/-- Binds the pattern variables `ps` of `p` to the subterms of `t` at their places, extending `σ`,
if `t` is `p` with terms for them. -/
def matchTerm (ps : List Term) (σ : List (Term × Term)) :
    Term → Term → Option (List (Term × Term))
  | p, t =>
    if ps.contains p then
      match σ.lookup p with
      | some u => if u == t then some σ else none
      | none => some ((p, t) :: σ)
    else
      match p, t with
      | .Apply f a, .Apply g b => (matchTerm ps σ f g).bind fun σ => matchTerm ps σ a b
      | .UOp1 o a, .UOp1 o' b => if o == o' then matchTerm ps σ a b else none
      | .UOp2 o a1 a2, .UOp2 o' b1 b2 =>
        if o == o' then (matchTerm ps σ a1 b1).bind fun σ => matchTerm ps σ a2 b2 else none
      | .UOp3 o a1 a2 a3, .UOp3 o' b1 b2 b3 =>
        if o == o' then
          ((matchTerm ps σ a1 b1).bind fun σ => matchTerm ps σ a2 b2).bind fun σ =>
            matchTerm ps σ a3 b3
        else none
      | p, t => if p == t then some σ else none

/-- The terms that `t` has for the parameters of `e`, if `t` is `e` with terms for them. -/
def images (e : Equation) (t : Term) : Option (List SmtTerm) := do
  let σ ← matchTerm e.args [] e.term t
  e.args.mapM fun a => (σ.lookup a).map __eo_to_smt

/-- The bindings of the parameters `ps` to the terms `us`. -/
def bindParams (ps : List (SmtEval.native_String × SmtType)) (us : List SmtTerm) :
    List (SmtEval.native_String × SmtType × SmtTerm) :=
  List.zipWith (fun p u => (p.1, p.2, u)) ps us

/-- The terms `us` can replace the parameters `ps`: as many, of their sorts, none a selector or a
tester, and the names of the parameters are not reserved by Logos. -/
def paramsB : List (SmtEval.native_String × SmtType) → List SmtTerm → Bool
  | [], [] => true
  | p :: ps, u :: us =>
    decide (Unreserved p.1) && decide (p.2 ≠ SmtType.None) && decide (__smtx_typeof u = p.2) &&
      plainHead u && paramsB ps us
  | _, _ => false

/-- `(=> g s)` is an instance of the defining equation `e`: `s` is the equation with the terms
`us` for its parameters, and `g` is a Boolean. -/
def instB (e : Equation) (g s : SmtTerm) (us : List SmtTerm) : Bool :=
  paramsB e.params us && noBinder (__eo_to_smt e.term) &&
    decide (__smtx_typeof g = SmtType.Bool) &&
    decide (substSmt (bindParams e.params us) (__eo_to_smt e.term) = s)

/-- The clause `c` is `(=> g s)`, where `s` is an instance of one of the defining equations `eqs`:
the clause of an `Unfold` rule of a function without branches. -/
def unfoldB (eqs : List Equation) (c : Term) : Bool :=
  match c, __eo_to_smt c with
  | .Apply (.Apply (.UOp .imp) _) s', .imp g s =>
    eqs.any fun e => match images e s' with
      | some us => instB e g s us
      | none => false
  | _, _ => false

/-- Reinterpreting the constant `s` of sort `T` keeps the defining equations `eqs`: they do not
mention it, and it is none of their parameters. -/
def keepsB (eqs : List Equation) (s : SmtEval.native_String) (T : SmtType) : Bool :=
  decide (Unreserved s) &&
    eqs.all fun e => !mentions s T (__eo_to_smt e.term) && !e.params.contains (s, T)

/-- The declarations of the clauses, followed by those of the templates' script that declare names
they don't, and one `assume` per defining equation. -/
def equationText (checked : Checked) : String :=
  let decls := declarations checked
  let names : Std.HashSet String :=
    Std.HashSet.ofList (decls.flatMap fun c => (declaredNames c).getD [])
  let ofTemplates := checked.templateScript.filter fun c => match declaredNames c with
    | some ns => !ns.isEmpty && ns.all (!names.contains ·)
    | none => false
  let assumes := checked.sources.zipIdx.map fun (c, i) =>
    Sexp.expr [.atom "assume", .atom s!"inox.source.{i}", c]
  "\n".intercalate ((decls ++ ofTemplates ++ assumes).map text) ++ "\n"

/-- `e` without its assumptions: each `(assume c b)` is `b`. -/
def dropAssumes : Sexp → Sexp
  | .expr [.atom "assume", _, b] => dropAssumes b
  | .expr es => .expr (es.attach.map fun ⟨e, _⟩ => dropAssumes e)
  | a => a

/-- The defining equations of the functions of a certificate, as Logos reads them, if it can,
without their assumptions, which Logos doesn't read in a term: each `(assume c b)` is `b`. Where
the call has a value, its evaluation went through each assumption it met, which held, so the call
equals the body without them: the equation holds on the calls that have values. -/
def equations (checked : Checked) : List Equation :=
  let checked := { checked with sources := checked.sources.map dropAssumes }
  match parseProof (equationText checked) with
  | .ok (terms, _) => terms.filterMap equationOf
  | .error _ => []

/-- What the second parse gives: the proof's assumptions as Logos reads them, the base clauses
(the query's assumptions), the fresh-symbol steps and the facts. -/
structure TermSteps where
  assums : List Term
  base : List Term
  fresh : List Step
  facts : List Term
  derived : List Derived
  /-- the defining equations of the functions -/
  equations : List Equation := []

/-- The steps of the clauses `terms` of the rules `applied`, the terms of the completeness
assumptions following them, and the `Enables` clauses that follow from a definition: those whose
blocker has a plain `Define` of which the target is a conjunct. -/
def ruleSteps (applied : List (String × Nat)) (terms : List Term) :
    Except String (List Step × List Term × List Derived) := do
  -- the plain definitions, by the number of their constant
  let mut defs : Std.HashMap Nat Term := {}
  let mut rest := terms
  for (kind, n) in applied do
    if kind == "Define" then
      for t in rest.take n do
        if let .Apply (.Apply (.UOp .eq) c) rhs := t then
          if let some i := constNumber c then defs := defs.insert i rhs
    rest := rest.drop n
  let mut terms := terms
  let mut fresh : Array Step := #[]
  let mut facts : Array Term := #[]
  let mut derived : Array Derived := #[]
  let mut targets : Std.HashMap Nat (Term × Array Term) := {}
  let mut targetOrder : Array Nat := #[]
  for (kind, n) in applied do
    let ts := terms.take n
    terms := terms.drop n
    if ts.length != n then throw "the parse has fewer assumptions than there are clauses"
    match kind with
    | "Define" | "Hypothesis" | "Root" =>
      for t in ts do fresh := fresh.push (← freshStep kind t)
    | "Enables" =>
      for t in ts do
        match t with
        | .Apply (.Apply (.UOp .imp) b) c =>
          let some i := constNumber c | throw "the target of an Enables rule is not a constant"
          match (constNumber b).bind defs.get? with
          | some rhs =>
            if inConj c rhs then
              derived := derived.push ⟨b, rhs, c⟩
              continue
          | none => pure ()
          match targets.get? i with
          | some (c', bs) => targets := targets.insert i (c', bs.push b)
          | none =>
            targets := targets.insert i (c, #[b])
            targetOrder := targetOrder.push i
        | _ => throw "a clause of an Enables rule doesn't have the shape of its kind"
    | _ => facts := facts ++ ts.toArray
  for i in targetOrder do
    if let some (c, bs) := targets.get? i then fresh := fresh.push (.enables c bs.toList)
  return (orderSteps fresh.toList, facts.toList ++ terms, derived.toList)

/-- Parses the proof and the clauses, and makes the steps of the rules. -/
def termSteps (checked : Checked) : Except String TermSteps :=
  match parseProof checked.proof with
  | .error e => .error s!"Logos can't read the proof: {e}"
  | .ok (assums, _) =>
    match parseProof (clauseText checked) with
    | .error e => .error s!"Logos can't read the clauses: {e}"
    | .ok (terms, _) =>
      let nq := checked.query.length
      match ruleSteps (checked.applied.map fun (k, cs) => (k, cs.length)) (terms.drop nq) with
      | .error e => .error e
      | .ok (fresh, facts, derived) =>
        .ok { assums, base := terms.take nq, fresh, facts, derived, equations := equations checked }

/-! ## The check -/

/-- The constant a term is, if it is one. -/
def asConst : SmtTerm → Option (SmtEval.native_String × SmtType)
  | .UConst s T => some (s, T)
  | _ => none

/-- Adds the names of the constants that the translation of each term mentions to `acc`. -/
def addClauseNames (acc : Std.HashSet SmtEval.native_String) (ts : List Term) :
    Std.HashSet SmtEval.native_String :=
  ts.foldl (fun acc t => Fresh.addNames acc (__eo_to_smt t)) acc

/-- Decides `Step.Fresh`, given a set that contains the name of each constant that the
assumptions mention. -/
def freshB (st : Step) (names : Std.HashSet SmtEval.native_String) : Bool :=
  match asConst (__eo_to_smt st.const) with
  | some (s, T) =>
    !st.isFact && decide (Unreserved s) && !names.contains s &&
      st.parts.all (fun t => !mentions s T (__eo_to_smt t)) &&
      st.clauses.all (fun t => decide (__smtx_typeof (__eo_to_smt t) = SmtType.Bool))
  | none => false

/-- Decides `StepsFresh`, given a set that contains the name of each constant that the
assumptions mention. -/
def stepsFreshB : Std.HashSet SmtEval.native_String → List Step → Bool
  | _, [] => true
  | names, st :: sts => freshB st names && stepsFreshB (addClauseNames names st.clauses) sts

/-- A hash of a term, for the set of the clauses: equal terms have equal hashes, which is all
`Std.HashSet` needs of it. -/
def termHash : Term → UInt64
  | .UOp op => mixHash 1 (hash op.ctorIdx)
  | .UOp1 op a => mixHash (mixHash 2 (hash op.ctorIdx)) (termHash a)
  | .UOp2 op a b => mixHash (mixHash (mixHash 3 (hash op.ctorIdx)) (termHash a)) (termHash b)
  | .UOp3 op a b c =>
    mixHash (mixHash (mixHash (mixHash 4 (hash op.ctorIdx)) (termHash a)) (termHash b))
      (termHash c)
  | .Boolean b => mixHash 5 (hash b)
  | .Numeral n => mixHash 6 (hash n)
  | .String s => mixHash 7 (hash s)
  | .Apply f a => mixHash (mixHash 8 (termHash f)) (termHash a)
  | .Var a b => mixHash (mixHash 9 (termHash a)) (termHash b)
  | .UConst i T => mixHash (mixHash 10 (hash i)) (termHash T)
  | t => hash t.ctorIdx

instance : Hashable Term := ⟨termHash⟩

/-- Decides that a derived clause follows from a clause of `defs`. -/
def derivedB (defs : Std.HashSet Term) (d : Derived) : Bool :=
  defs.contains (Extend.mkEq d.blocker d.rhs) && inConj d.target d.rhs &&
    decide (__smtx_typeof (__eo_to_smt d.clause) = SmtType.Bool)

/-- All the steps: the fresh-symbol steps, then the facts, then the derived clauses, as facts. -/
def TermSteps.steps (r : TermSteps) : List Step :=
  r.fresh ++ r.facts.map Step.fact ++ r.derived.map (Step.fact ∘ Derived.clause)

/-- Each fresh-symbol step can follow the base clauses and those of the steps before it, each
derived clause follows from a definition among them, and every assumption of the proof is a
clause. -/
def TermSteps.check (r : TermSteps) : Bool :=
  stepsFreshB (addClauseNames {} r.base) r.fresh &&
    (let defs := Std.HashSet.ofList (extend r.base r.fresh)
     r.derived.all (derivedB defs)) &&
    let all := Std.HashSet.ofList (extend r.base r.steps)
    r.assums.all all.contains

/-- Reinterpreting each fresh symbol keeps the defining equations of the functions. -/
def TermSteps.keeps (r : TermSteps) : Bool :=
  r.fresh.all fun st => match asConst (__eo_to_smt st.const) with
    | some (s, T) => keepsB r.equations s T
    | none => true

/-- The facts that are not unfoldings of a defining equation. -/
def TermSteps.otherFacts (r : TermSteps) : List Term :=
  r.facts.filter (!unfoldB r.equations ·)

/-- Why `check` fails. -/
def TermSteps.why (r : TermSteps) : String := Id.run do
  let mut names := addClauseNames {} r.base
  let mut n := 0
  for st in r.fresh do
    if !freshB st names then
      return s!"fresh-symbol step {n} of {r.fresh.length}, {repr st.const}, is not fresh"
    names := addClauseNames names st.clauses
    n := n + 1
  let defs := Std.HashSet.ofList (extend r.base r.fresh)
  if let some d := r.derived.find? (!derivedB defs ·) then
    return s!"the clause {repr d.clause} doesn't follow from the definition of its blocker"
  let all := Std.HashSet.ofList (extend r.base r.steps)
  match r.assums.find? (!all.contains ·) with
  | some a => return s!"the proof assumes {repr a}, which is no clause"
  | none => return "the check holds"

end Inox
