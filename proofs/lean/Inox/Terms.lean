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
assumptions, the definitions of the local symbols of the instances, and the source expressions
of the instances of `expression` kind. -/
def allClauses (checked : Checked) : List Sexp :=
  checked.query ++ checked.applied.flatMap (·.2) ++ checked.complete ++
    checked.defined.flatMap (·.map fun (v, m) => app "=" [v, m]) ++ checked.expressions

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
def orderStepsPlaced (sts : List Step) : List Step × Nat := Id.run do
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
  let n := order.size
  for j in [0:arr.size] do
    if !placed[j]! then order := order.push arr[j]!
  return (order.toList, n)

/-- `orderStepsPlaced`, without the number of the steps that follow their dependencies. -/
def orderSteps (sts : List Step) : List Step := (orderStepsPlaced sts).1

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
  /-- the instances of templates: the definitions of their local symbols, and their clauses -/
  instances : List (List Term × List Term) := []
  /-- how many of the defining equations are the reflexivity of an equality -/
  axioms : Nat := 0
  /-- how many base clauses are source expressions, and completeness assumptions -/
  expressions : Nat := 0
  completeBase : Nat := 0
  /-- the kind of each fact, with its clause as the certificate states it -/
  kinds : List (String × Sexp) := []

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
  return (fresh.toList, facts.toList ++ terms, derived.toList)

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

/-- The definitions of the local symbols of the instances that can be fresh-symbol steps: their
steps are added to `fresh`, and those that can't follow the others, or whose symbol the defining
equations `eqs` mention, are left out, until the others can. Nothing relies on this: the check
decides it. -/
def addDefinitions (eqs : List Equation) (base : List Term) (fresh : List Step) (defs : List Term) :
    List Step := Id.run do
  let defSteps := defs.filterMap fun t => match freshStep "Define" t with
    | .ok st => some st
    | .error _ => none
  let isDef : Std.HashSet Nat := Std.HashSet.ofList (defSteps.filterMap (constNumber ·.const))
  let keeps (st : Step) : Bool := match asConst (__eo_to_smt st.const) with
    | some (s, T) => keepsB eqs s T
    | none => true
  let mut kept := defSteps.filter keeps
  for _ in [0:16] do
    let (order, placed) := orderStepsPlaced (fresh ++ kept)
    -- the definitions in a cycle go first
    let cyclic : Std.HashSet Nat := Std.HashSet.ofList ((order.drop placed).filterMap fun st =>
      (constNumber st.const).filter isDef.contains)
    if !cyclic.isEmpty then
      kept := kept.filter fun st => !(constNumber st.const).any cyclic.contains
      continue
    let mut names := addClauseNames {} base
    let mut bad : Std.HashSet Nat := {}
    let mut before : Std.HashSet Nat := {}
    let mut other := false
    for st in order do
      let n := constNumber st.const
      let mine := n.any isDef.contains
      if !freshB st names then
        if mine then bad := bad.insert n.get!
        else
          other := true
          break
      if mine then before := before.insert n.get!
      names := addClauseNames names st.clauses
    if bad.isEmpty && !other then break
    let drop := if bad.isEmpty then before else bad
    if drop.isEmpty then break
    kept := kept.filter fun st => !(constNumber st.const).any drop.contains
  return orderSteps (fresh ++ kept)

/-- The source expressions and the definitions of the local symbols of the instances, as Logos
reads them, if it can read them with the other clauses; failing that, the definitions alone; and
failing that, neither. -/
def usableDefinitions (checked : Checked) : Checked :=
  match parseProof (clauseText checked) with
  | .ok _ => checked
  | .error _ =>
    let checked := { checked with expressions := [] }
    match parseProof (clauseText checked) with
    | .ok _ => checked
    | .error _ => { checked with defined := [] }

/-- The kind of each fact of the rules, with its clause as the certificate states it: the kinds of
the rules that state facts, in the order of `applied`. -/
def factKinds (checked : Checked) : List (String × Sexp) :=
  let stated := checked.applied.filter fun (k, _) =>
    !["Define", "Hypothesis", "Root", "Enables"].contains k
  stated.flatMap fun (k, cs) => cs.map (k, ·)

/-- The terms `ts`, each with the kind of the rule of `counts` that it is a clause of. -/
def withKinds : List (String × Nat) → List Term → List (String × Term)
  | [], _ => []
  | (k, n) :: cs, ts => (ts.take n).map (k, ·) ++ withKinds cs (ts.drop n)

/-- The term `t` mentions none of the constants of the steps `sts`. -/
def mentionsNone (sts : List Step) (t : Term) : Bool :=
  let names := addClauseNames {} [t]
  sts.all fun st => match asConst (__eo_to_smt st.const) with
    | some (s, _) => !names.contains s
    | none => true

/-- `t` is a constant whose name Logos does not reserve. -/
def unreservedConst (t : Term) : Bool :=
  match asConst (__eo_to_smt t) with
  | some (s, _) => decide (Unreserved s)
  | none => false

/-- `t` is such a constant applied to such constants. -/
def constApp : Term → Bool
  | .Apply f x => constApp f && unreservedConst x
  | t => unreservedConst t

/-- The reflexivity of the equality `h` of the clause `c` of a `Reflexivity` rule of the
certificate, `(=> (= a b) (h a b))`, as a defining equation `(=> (= x y) (h x y))`, for the
constants `x` and `y` numbered `n` and `n + 1`, of the type of `a`, when `h` is made of constants
of the query whose names Logos does not reserve (`constApp`), such as
`(dynLambda!2 |eqBag[BigInt]!0|)`: not the equality of SMT, nor another built-in relation, which
would leave no `Good` model. -/
def reflexivity (n : Nat) (c : Term) : Option Equation :=
  match c with
  | .Apply (.Apply (.UOp .imp) _) (.Apply (.Apply h a) _) =>
    if !constApp h then none else
    let T := __eo_typeof a
    let x := Term.UConst n T
    let y := Term.UConst (n + 1) T
    match __eo_to_smt x, __eo_to_smt y with
    | .UConst s T', .UConst s' T'' =>
      some { term := Extend.mkImp (Extend.mkEq x y) (Term.Apply (Term.Apply h x) y),
             args := [x, y], params := [(s, T'), (s', T'')] }
    | _, _ => none
  | _ => none

/-- The reflexivity of the equalities of the `Reflexivity` rules, once each, as defining
equations, for constants numbered after those of `terms`, when they mention none of the constants
of the steps `fresh`. -/
def reflexivities (terms : List Term) (fresh : List Step) (kinds : List (String × Term)) :
    List Equation :=
  let n := (terms.foldl uconsts {}).fold (fun m i => max m i) 0 + 1
  let all := kinds.filterMap fun (k, t) => if k == "Reflexivity" then reflexivity n t else none
  let terms := (all.map (·.term)).eraseDups
  terms.filterMap fun t => (all.find? (·.term == t)).filter fun e => mentionsNone fresh e.term

/-- The steps of the clauses `terms` of the second parse: the base clauses are the query's
assumptions, the source expressions of the instances of `expression` kind and the completeness
assumptions, those of the latter two that mention none of the constants of the steps of the
rules; the other completeness assumptions are facts, and the other source expressions are left
out. -/
def termStepsOf (checked : Checked) (terms : List Term) : Except String TermSteps :=
  let nq := checked.query.length
  let counts := checked.applied.map fun (k, cs) => (k, cs.length)
  let ndefs := checked.defined.map List.length
  let nrules := (counts.map (·.2)).sum
  let nc := checked.complete.length
  let rest := terms.drop nq
  let ruleTerms := rest.take nrules
  let completeTerms := (rest.drop nrules).take nc
  let defs := (rest.drop (nrules + nc)).take ndefs.sum
  let exprTerms := rest.drop (nrules + nc + ndefs.sum)
  match ruleSteps counts ruleTerms with
  | .error e => .error e
  | .ok (fresh, facts, derived) =>
    let exprs := exprTerms.filter (mentionsNone fresh)
    let (completeBase, completeFacts) :=
      (completeTerms.zip checked.complete).partition fun (t, _) => mentionsNone fresh t
    let base := terms.take nq ++ exprs ++ completeBase.map (·.1)
    let axioms := reflexivities terms fresh (withKinds counts ruleTerms)
    let eqs := equations checked ++ axioms
    -- the definitions and the clauses of each instance
    let instances := (counts.zip ndefs).foldl
      (fun (acc : List (List Term × List Term) × List Term × List Term) ((k, n), nd) =>
        let (out, cs, ds) := acc
        let out :=
          if k == "Unfold" || k == "Instance" then out ++ [(ds.take nd, cs.take n)] else out
        (out, cs.drop n, ds.drop nd)) ([], ruleTerms, defs)
    .ok { assums := [], base, fresh := addDefinitions eqs base fresh defs,
          facts := facts ++ completeFacts.map (·.1), derived, equations := eqs,
          instances := instances.1, axioms := axioms.length, expressions := exprs.length,
          completeBase := completeBase.length,
          kinds := factKinds checked ++ completeFacts.map fun (_, c) => ("complete", c) }

/-- Parses the proof and the clauses, and makes the steps of the rules. -/
def termSteps (checked : Checked) : Except String TermSteps :=
  match parseProof checked.proof with
  | .error e => .error s!"Logos can't read the proof: {e}"
  | .ok (assums, _) =>
    let checked := usableDefinitions checked
    match parseProof (clauseText checked) with
    | .error e => .error s!"Logos can't read the clauses: {e}"
    | .ok (terms, _) => (termStepsOf checked terms).map fun r => { r with assums }

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
      let i := (constNumber st.const).getD 0
      let earlier := (r.fresh.take n).zipIdx.find? fun (st', _) =>
        (st'.clauses.foldl uconsts {}).contains i
      let by_ := match earlier with
        | some (st', j) =>
          s!", which step {j}, {repr st'.const} ({st'.isFact}), " ++
            s!"mentions: {st'.clauses.map repr}"
        | none =>
          if (r.base.foldl uconsts {}).contains i then ", which a base clause mentions" else ""
      return s!"fresh-symbol step {n} of {r.fresh.length}, {repr st.const} ({st.isFact}), " ++
        s!"is not fresh{by_}"
    names := addClauseNames names st.clauses
    n := n + 1
  let defs := Std.HashSet.ofList (extend r.base r.fresh)
  if let some d := r.derived.find? (!derivedB defs ·) then
    return s!"the clause {repr d.clause} doesn't follow from the definition of its blocker"
  let all := Std.HashSet.ofList (extend r.base r.steps)
  match r.assums.find? (!all.contains ·) with
  | some a => return s!"the proof assumes {repr a}, which is no clause"
  | none => return "the check holds"

/-! ## The instances of templates

The clauses of an instance of a template hold once its local symbols are interpreted as their
meanings, which the definitions of the instance state (`Inox/Meanings.lean`). `instanceFacts`
substitutes the meanings for the symbols in each clause and decides that the result holds in each
model of the defining equations: by evaluating it under the literals that its guards make known
(`verify`), or as an instance of a defining equation (`eqInst`). `Inox/Instances.lean` proves it.
-/

/-- The value that `K` gives `t`, if it gives one. -/
def known : List (SmtTerm × Bool) → SmtTerm → Option Bool
  | [], _ => none
  | p :: K, t => if p.1 = t then some p.2 else known K t

/-- The literals that `t` having the value `b` makes known: `t` itself, the operands of a true
conjunction or of a false disjunction, the operand of a negation, and the opposite comparison of a
comparison, which Inox states the negated conditions of branches with. -/
def lits (t : SmtTerm) (b : Bool) : List (SmtTerm × Bool) :=
  (t, b) :: match t, b with
    | .and x y, true => lits x true ++ lits y true
    | .or x y, false => lits x false ++ lits y false
    | .not x, b => lits x (!b)
    | .lt x y, b => [(.geq x y, !b)]
    | .geq x y, b => [(.lt x y, !b)]
    | .leq x y, b => [(.gt x y, !b)]
    | .gt x y, b => [(.leq x y, !b)]
    | _, _ => []

/-- `(or x y)`, where a Boolean operand that is a literal decides it. -/
def orR (x y : SmtTerm) : SmtTerm :=
  if x = .Boolean true ∧ __smtx_typeof y = .Bool then .Boolean true
  else if y = .Boolean true ∧ __smtx_typeof x = .Bool then .Boolean true
  else if x = .Boolean false ∧ __smtx_typeof y = .Bool then y
  else if y = .Boolean false ∧ __smtx_typeof x = .Bool then x
  else .or x y

/-- `(and x y)`, where a Boolean operand that is a literal decides it. -/
def andR (x y : SmtTerm) : SmtTerm :=
  if x = .Boolean false ∧ __smtx_typeof y = .Bool then .Boolean false
  else if y = .Boolean false ∧ __smtx_typeof x = .Bool then .Boolean false
  else if x = .Boolean true ∧ __smtx_typeof y = .Bool then y
  else if y = .Boolean true ∧ __smtx_typeof x = .Bool then x
  else .and x y

/-- `r`, unless `K` gives `t` a value. -/
def lookupOr (K : List (SmtTerm × Bool)) (t r : SmtTerm) : SmtTerm :=
  match known K t with
  | some b => .Boolean b
  | none => r

/-- `t` reduced under the literals `K`: the subterms that `K` gives a value are that value, an
`ite` whose condition reduces to a literal is its branch, Boolean operators of literals are
reduced, and an equality of two terms that reduce to the same term is true. -/
def red (K : List (SmtTerm × Bool)) : SmtTerm → SmtTerm
  | .ite c a b => lookupOr K (.ite c a b) (match red K c with
    | .Boolean true => red K a
    | .Boolean false => red K b
    | c' => .ite c' (red K a) (red K b))
  | .not x => lookupOr K (.not x) (match red K x with
    | .Boolean b => .Boolean (SmtEval.native_not b)
    | x' => .not x')
  | .or x y => lookupOr K (.or x y) (orR (red K x) (red K y))
  | .and x y => lookupOr K (.and x y) (andR (red K x) (red K y))
  | .eq x y =>
    lookupOr K (.eq x y) (if red K x = red K y then .Boolean true else .eq (red K x) (red K y))
  | t => lookupOr K t t

/-- The arguments of an application. -/
def smtArgs : SmtTerm → List SmtTerm
  | .Apply f a => smtArgs f ++ [a]
  | _ => []

/-- `φ` is the defining equation `e` with the terms `us` for its parameters. -/
def eqInstB (e : Equation) (φ : SmtTerm) (us : List SmtTerm) : Bool :=
  paramsB e.params us && noBinder (__eo_to_smt e.term) &&
    decide (substSmt (bindParams e.params us) (__eo_to_smt e.term) = φ)

/-- `φ` is an instance of one of the defining equations `eqs`, with the arguments of its left
side for the parameters. -/
def eqInst (eqs : List Equation) (φ : SmtTerm) : Bool :=
  match φ with
  | .eq lhs _ => eqs.any fun e => eqInstB e φ (smtArgs lhs)
  | _ => false

/-- `φ` is the conclusion `q` of a defining equation `(=> A q)` with the terms `us` for its
parameters, whose premise `A` reduces to true under the literals `K`. -/
def mpInstB (e : Equation) (K : List (SmtTerm × Bool)) (φ : SmtTerm) (us : List SmtTerm) : Bool :=
  paramsB e.params us && noBinder (__eo_to_smt e.term) &&
    match substSmt (bindParams e.params us) (__eo_to_smt e.term) with
    | .imp a q => decide (q = φ) && decide (red K a = .Boolean true)
    | _ => false

/-- `φ` follows by modus ponens from an instance of one of the defining equations `eqs`, with the
last arguments of `φ` for the parameters, under the literals `K`. -/
def mpInst (eqs : List Equation) (K : List (SmtTerm × Bool)) (φ : SmtTerm) : Bool :=
  eqs.any fun e => mpInstB e K φ ((smtArgs φ).drop ((smtArgs φ).length - e.params.length))

/-- `K` makes the equality of `x` and `y` known, and `x` is of a sort that has values and is not
that of regular languages, whose equality is not that of their values. -/
def eqKnown (K : List (SmtTerm × Bool)) (x y : SmtTerm) : Bool :=
  (known K (.eq x y) == some true || known K (.eq y x) == some true) &&
    decide (__smtx_typeof x ≠ .None) && decide (__smtx_typeof x ≠ .RegLan)

/-- `x` and `y` have the same value in each model where the literals `K` have their values: they
are the same term, or `K` makes their equality known, or they are applications of the same
function, or of functions that have the same value and are not selectors or testers, to arguments
that have the same value. -/
def congB (K : List (SmtTerm × Bool)) : SmtTerm → SmtTerm → Bool
  | .Apply f a, y =>
    decide (SmtTerm.Apply f a = y) || eqKnown K (.Apply f a) y ||
      match y with
      | .Apply g b => (decide (f = g) || (plainHead f && plainHead g && congB K f g)) && congB K a b
      | _ => false
  | x, y => decide (x = y) || eqKnown K x y

/-- `φ` is an equality of terms that have the same value under the literals `K`, by congruence. -/
def congEq (K : List (SmtTerm × Bool)) : SmtTerm → Bool
  | .eq x y => congB K x y
  | _ => false

/-- `k` holds of the literals that `p` being true makes known, as it is and reduced under `K`, with
`K`, or `p` is false under `K`: for each operand of `p` if it is a disjunction. -/
def verifyUnder (k : List (SmtTerm × Bool) → Bool) (K : List (SmtTerm × Bool)) :
    SmtTerm → Bool
  | .or p1 p2 => verifyUnder k K p1 && verifyUnder k K p2
  | p => red K p = .Boolean false || k (lits (red K p) true ++ lits p true ++ K)

/-- `φ` holds in the models of the defining equations `eqs` where the literals `K` have their
values: an implication whose premise makes its conclusion hold, or a term that reduces to true, or
an instance of a defining equation, or the conclusion of one whose premise holds, or an equality
by congruence. -/
def verify (eqs : List Equation) (K : List (SmtTerm × Bool)) : SmtTerm → Bool
  | .imp p q => decide (__smtx_typeof p = .Bool) && decide (__smtx_typeof q = .Bool) &&
      verifyUnder (fun K' => verify eqs K' q) K p
  | φ => red K φ = .Boolean true || eqInst eqs φ || mpInst eqs K φ || congEq K φ

/-- The binding of the constant that a definition `(= v D)` defines to `D`, if `v` is a constant
whose name Logos doesn't reserve, of a sort that has values and is not that of regular languages,
and `D` is not a selector or a tester. -/
def defBinding : Term → Option (SmtEval.native_String × SmtType × SmtTerm)
  | .Apply (.Apply (.UOp .eq) v) d =>
    match __eo_to_smt v with
    | .UConst s T =>
      if decide (Unreserved s) && decide (__smtx_typeof (.UConst s T) ≠ .None) &&
          decide (__smtx_typeof (.UConst s T) ≠ .RegLan) && plainHead (__eo_to_smt d) then
        some (s, T, __eo_to_smt d)
      else none
    | _ => none
  | _ => none

/-- The clause `c` holds, under the literals `K`, once the definitions `σ` are substituted in
it. -/
def instClauseB (eqs : List Equation) (K : List (SmtTerm × Bool))
    (σ : List (SmtEval.native_String × SmtType × SmtTerm)) (c : Term) : Bool :=
  noBinder (__eo_to_smt c) && verify eqs K (substSmt σ (__eo_to_smt c))

/-- The literals that the base clauses make known. -/
def TermSteps.baseLits (r : TermSteps) : List (SmtTerm × Bool) :=
  r.base.flatMap fun t => lits (__eo_to_smt t) true

/-- The clauses of the instances that hold, given the base clauses and the definitions of their
local symbols that are clauses of the fresh-symbol steps. -/
def TermSteps.instanceFacts (r : TermSteps) : List Term :=
  let ctx := Std.HashSet.ofList (extend r.base r.fresh)
  let K := r.baseLits
  r.instances.flatMap fun (defs, cs) =>
    let σ := (defs.filter ctx.contains).filterMap defBinding
    cs.filter (instClauseB r.equations K σ)

/-- The fact `t` holds given the base clauses, as it is. -/
def TermSteps.verified (r : TermSteps) (t : Term) : Bool :=
  noBinder (__eo_to_smt t) && verify r.equations r.baseLits (__eo_to_smt t)

/-- The facts that the unfoldings of the equations, the instances of templates, or the base
clauses account for. -/
def TermSteps.covered (r : TermSteps) : Term → Bool :=
  let inst := Std.HashSet.ofList r.instanceFacts
  fun t => unfoldB r.equations t || inst.contains t || r.verified t

/-- The atom `a` is a symbol that `unrolling` names `pre!…`. -/
def namedAs (pre : String) : Sexp → Bool
  | .atom a => a.startsWith (pre ++ "!")
  | _ => false

/-- What a fact that remains states, by the kind of its rule and the shape of its clause: the
completeness of an open conjunction or disjunction, a clause with a binder, a decreases clause, the
typing of a value (`tp`), the definition of a call whose function has no source (`(= (f …) e)`),
a clause of an assertion's template (`Instance`), another clause of a function's template (the
contracts: postconditions of calls, refinements of results, `assume`s, preconditions), or the kind
of another rule. -/
def factCategory (kind : String) (c : Sexp) (t : Term) : String :=
  let concl := match c with
    | .expr [.atom "=>", _, q] => q
    | q => q
  if kind == "complete" then "completeness"
  else if !noBinder (__eo_to_smt t) then "binder"
  else if (Meanings.atoms c).any (·.startsWith "diverges!") then "decreases"
  else if namedAs "tp" concl then "typing"
  else if kind == "Unfold" && (match concl with
      | .expr [.atom "=", .expr _, v] => namedAs "e" v
      | _ => false) then "definition without source"
  else if kind == "Instance" then "assertion"
  else if kind == "Unfold" then "contract"
  else kind

/-- How many facts of `r` each argument discharges and how many remain, by kind. -/
def TermSteps.coverage (r : TermSteps) (checked : Checked) : String := Id.run do
  let inst := Std.HashSet.ofList r.instanceFacts
  let mut unf := 0
  let mut byInst := 0
  let mut direct := 0
  let mut done : Std.HashMap String Nat := {}
  let mut remain : Std.HashMap String Nat := {}
  for (t, (k, c)) in r.facts.zip r.kinds do
    let cat := factCategory k c t
    if unfoldB r.equations t then unf := unf + 1
    else if inst.contains t then byInst := byInst + 1
    else if r.verified t then
      direct := direct + 1
      done := done.insert cat (done.getD cat 0 + 1)
    else remain := remain.insert cat (remain.getD cat 0 + 1)
  let fmt (m : Std.HashMap String Nat) :=
    ", ".intercalate ((m.toList.mergeSort (fun a b => a.1 ≤ b.1)).map fun (k, n) => s!"{k} {n}")
  let ctx := Std.HashSet.ofList (extend r.base r.fresh)
  let ndefs := ((r.instances.flatMap (·.1)).filter ctx.contains).length
  let nprop := (checked.defined.map List.length).sum
  let left := r.facts.length - unf - byInst - direct
  let query := r.base.length - r.expressions - r.completeBase
  return s!"{r.facts.length} facts: {unf} by unfolding, {byInst} by instances, " ++
    s!"{direct} directly [{fmt done}], {left} remain [{fmt remain}]; " ++
    s!"{ndefs} of {nprop} definitions of local symbols kept; " ++
    s!"base: {query} of the query, {r.expressions} of {checked.expressions.length} " ++
    s!"source expressions, {r.completeBase} of {checked.complete.length} completeness " ++
    s!"assumptions; {r.axioms} reflexivity axioms"

/-- The facts of `r` that remain, with their kinds and clauses. -/
def TermSteps.remaining (r : TermSteps) : List (String × Sexp) :=
  let inst := Std.HashSet.ofList r.instanceFacts
  ((r.facts.zip r.kinds).filter fun (t, _) =>
    !unfoldB r.equations t && !inst.contains t && !r.verified t).map (·.2)

end Inox
