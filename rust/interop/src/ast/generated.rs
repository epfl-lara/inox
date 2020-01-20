// AUTO-GENERATED FROM STAINLESS
#![allow(non_snake_case)]
use crate::ser::{MarkerId, Serializable, SerializationResult, Serializer};
use crate::ser::types::*;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

// === Definition ===

/// inox.ast.Definitions.Definition
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Definition<'a> {
  ADTSort(ADTSort<'a>),
  FunDef(FunDef<'a>),
  TypeParameterDef(TypeParameterDef<'a>),
  ValDef(ValDef<'a>)
}

impl<'a> Serializable for Definition<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    match self {
      Definition::ADTSort(v) => v.serialize(s)?,
      Definition::FunDef(v) => v.serialize(s)?,
      Definition::TypeParameterDef(v) => v.serialize(s)?,
      Definition::ValDef(v) => v.serialize(s)?,
    };
    Ok(())
  }
}

/// inox.ast.Definitions.ADTSort
#[derive(Clone, Debug)]
pub struct ADTSort<'a> {
  pub id: &'a Identifier,
  pub tparams: Seq<&'a TypeParameterDef<'a>>,
  pub constructors: Seq<&'a ADTConstructor<'a>>,
  pub flags: Seq<Flag<'a>>
}

impl<'a> PartialEq for ADTSort<'a> {
  fn eq(&self, other: &Self) -> bool { self.id == other.id }
}
impl<'a> Eq for ADTSort<'a> {}
impl<'a> PartialOrd for ADTSort<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}
impl<'a> Ord for ADTSort<'a> {
  fn cmp(&self, other: &Self) -> Ordering { self.id.cmp(&other.id) }
}
impl<'a> Hash for ADTSort<'a> {
  fn hash<H: Hasher>(&self, state: &mut H) { self.id.hash(state); }
}

impl<'a> Serializable for ADTSort<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(96))?;
    self.id.serialize(s)?;
    self.tparams.serialize(s)?;
    self.constructors.serialize(s)?;
    self.flags.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Definitions.FunDef
#[derive(Clone, Debug)]
pub struct FunDef<'a> {
  pub id: &'a Identifier,
  pub tparams: Seq<&'a TypeParameterDef<'a>>,
  pub params: Seq<&'a ValDef<'a>>,
  pub returnType: &'a Type<'a>,
  pub fullBody: &'a Expr<'a>,
  pub flags: Seq<Flag<'a>>
}

impl<'a> PartialEq for FunDef<'a> {
  fn eq(&self, other: &Self) -> bool { self.id == other.id }
}
impl<'a> Eq for FunDef<'a> {}
impl<'a> PartialOrd for FunDef<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}
impl<'a> Ord for FunDef<'a> {
  fn cmp(&self, other: &Self) -> Ordering { self.id.cmp(&other.id) }
}
impl<'a> Hash for FunDef<'a> {
  fn hash<H: Hasher>(&self, state: &mut H) { self.id.hash(state); }
}

impl<'a> Serializable for FunDef<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(98))?;
    self.id.serialize(s)?;
    self.tparams.serialize(s)?;
    self.params.serialize(s)?;
    self.returnType.serialize(s)?;
    self.fullBody.serialize(s)?;
    self.flags.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Definitions.TypeParameterDef
#[derive(Clone, Debug)]
pub struct TypeParameterDef<'a> {
  pub tp: &'a TypeParameter<'a>
}

impl<'a> PartialEq for TypeParameterDef<'a> {
  fn eq(&self, other: &Self) -> bool { self.tp.id == other.tp.id }
}
impl<'a> Eq for TypeParameterDef<'a> {}
impl<'a> PartialOrd for TypeParameterDef<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}
impl<'a> Ord for TypeParameterDef<'a> {
  fn cmp(&self, other: &Self) -> Ordering { self.tp.id.cmp(&other.tp.id) }
}
impl<'a> Hash for TypeParameterDef<'a> {
  fn hash<H: Hasher>(&self, state: &mut H) { self.tp.id.hash(state); }
}

/// inox.ast.Definitions.ValDef
#[derive(Clone, Debug)]
pub struct ValDef<'a> {
  pub v: &'a Variable<'a>
}

impl<'a> PartialEq for ValDef<'a> {
  fn eq(&self, other: &Self) -> bool { self.v.id == other.v.id }
}
impl<'a> Eq for ValDef<'a> {}
impl<'a> PartialOrd for ValDef<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}
impl<'a> Ord for ValDef<'a> {
  fn cmp(&self, other: &Self) -> Ordering { self.v.id.cmp(&other.v.id) }
}
impl<'a> Hash for ValDef<'a> {
  fn hash<H: Hasher>(&self, state: &mut H) { self.v.id.hash(state); }
}


// === Flags ===

/// inox.ast.Definitions.Flag
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Flag<'a> {
  Annotation(Annotation<'a>),
  HasADTEquality(HasADTEquality<'a>),
  HasADTInvariant(HasADTInvariant<'a>)
}

impl<'a> Serializable for Flag<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    match self {
      Flag::Annotation(v) => v.serialize(s)?,
      Flag::HasADTEquality(v) => v.serialize(s)?,
      Flag::HasADTInvariant(v) => v.serialize(s)?,
    };
    Ok(())
  }
}

/// inox.ast.Definitions.Annotation
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Annotation<'a> {
  pub name: String,
  pub args: Seq<&'a Expr<'a>>
}

impl<'a> Serializable for Annotation<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(93))?;
    self.name.serialize(s)?;
    self.args.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Definitions.HasADTEquality
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct HasADTEquality<'a> {
  pub id: &'a Identifier
}

impl<'a> Serializable for HasADTEquality<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(92))?;
    self.id.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Definitions.HasADTInvariant
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct HasADTInvariant<'a> {
  pub id: &'a Identifier
}

impl<'a> Serializable for HasADTInvariant<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(91))?;
    self.id.serialize(s)?;
    Ok(())
  }
}

// === Expressions ===

/// inox.ast.Expressions.Expr
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expr<'a> {
  ADT(ADT<'a>),
  ADTSelector(ADTSelector<'a>),
  And(And<'a>),
  Application(Application<'a>),
  Assume(Assume<'a>),
  BVAShiftRight(BVAShiftRight<'a>),
  BVAnd(BVAnd<'a>),
  BVLShiftRight(BVLShiftRight<'a>),
  BVLiteral(BVLiteral),
  BVNarrowingCast(BVNarrowingCast<'a>),
  BVNot(BVNot<'a>),
  BVOr(BVOr<'a>),
  BVShiftLeft(BVShiftLeft<'a>),
  BVWideningCast(BVWideningCast<'a>),
  BVXor(BVXor<'a>),
  BagAdd(BagAdd<'a>),
  BagDifference(BagDifference<'a>),
  BagIntersection(BagIntersection<'a>),
  BagUnion(BagUnion<'a>),
  BooleanLiteral(BooleanLiteral),
  CharLiteral(CharLiteral),
  Choose(Choose<'a>),
  Division(Division<'a>),
  ElementOfSet(ElementOfSet<'a>),
  Equals(Equals<'a>),
  FiniteBag(FiniteBag<'a>),
  FiniteMap(FiniteMap<'a>),
  FiniteSet(FiniteSet<'a>),
  Forall(Forall<'a>),
  FractionLiteral(FractionLiteral),
  FunctionInvocation(FunctionInvocation<'a>),
  GenericValue(GenericValue<'a>),
  GreaterEquals(GreaterEquals<'a>),
  GreaterThan(GreaterThan<'a>),
  IfExpr(IfExpr<'a>),
  Implies(Implies<'a>),
  IntegerLiteral(IntegerLiteral),
  IsConstructor(IsConstructor<'a>),
  Lambda(Lambda<'a>),
  LessEquals(LessEquals<'a>),
  LessThan(LessThan<'a>),
  Let(Let<'a>),
  MapApply(MapApply<'a>),
  MapUpdated(MapUpdated<'a>),
  Minus(Minus<'a>),
  Modulo(Modulo<'a>),
  MultiplicityInBag(MultiplicityInBag<'a>),
  Not(Not<'a>),
  Or(Or<'a>),
  Plus(Plus<'a>),
  Remainder(Remainder<'a>),
  SetAdd(SetAdd<'a>),
  SetDifference(SetDifference<'a>),
  SetIntersection(SetIntersection<'a>),
  SetUnion(SetUnion<'a>),
  StringConcat(StringConcat<'a>),
  StringLength(StringLength<'a>),
  StringLiteral(StringLiteral),
  SubString(SubString<'a>),
  SubsetOf(SubsetOf<'a>),
  Times(Times<'a>),
  Tuple(Tuple<'a>),
  TupleSelect(TupleSelect<'a>),
  UMinus(UMinus<'a>),
  UnitLiteral(UnitLiteral),
  Variable(Variable<'a>)
}

impl<'a> Serializable for Expr<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    match self {
      Expr::ADT(v) => v.serialize(s)?,
      Expr::ADTSelector(v) => v.serialize(s)?,
      Expr::And(v) => v.serialize(s)?,
      Expr::Application(v) => v.serialize(s)?,
      Expr::Assume(v) => v.serialize(s)?,
      Expr::BVAShiftRight(v) => v.serialize(s)?,
      Expr::BVAnd(v) => v.serialize(s)?,
      Expr::BVLShiftRight(v) => v.serialize(s)?,
      Expr::BVLiteral(v) => v.serialize(s)?,
      Expr::BVNarrowingCast(v) => v.serialize(s)?,
      Expr::BVNot(v) => v.serialize(s)?,
      Expr::BVOr(v) => v.serialize(s)?,
      Expr::BVShiftLeft(v) => v.serialize(s)?,
      Expr::BVWideningCast(v) => v.serialize(s)?,
      Expr::BVXor(v) => v.serialize(s)?,
      Expr::BagAdd(v) => v.serialize(s)?,
      Expr::BagDifference(v) => v.serialize(s)?,
      Expr::BagIntersection(v) => v.serialize(s)?,
      Expr::BagUnion(v) => v.serialize(s)?,
      Expr::BooleanLiteral(v) => v.serialize(s)?,
      Expr::CharLiteral(v) => v.serialize(s)?,
      Expr::Choose(v) => v.serialize(s)?,
      Expr::Division(v) => v.serialize(s)?,
      Expr::ElementOfSet(v) => v.serialize(s)?,
      Expr::Equals(v) => v.serialize(s)?,
      Expr::FiniteBag(v) => v.serialize(s)?,
      Expr::FiniteMap(v) => v.serialize(s)?,
      Expr::FiniteSet(v) => v.serialize(s)?,
      Expr::Forall(v) => v.serialize(s)?,
      Expr::FractionLiteral(v) => v.serialize(s)?,
      Expr::FunctionInvocation(v) => v.serialize(s)?,
      Expr::GenericValue(v) => v.serialize(s)?,
      Expr::GreaterEquals(v) => v.serialize(s)?,
      Expr::GreaterThan(v) => v.serialize(s)?,
      Expr::IfExpr(v) => v.serialize(s)?,
      Expr::Implies(v) => v.serialize(s)?,
      Expr::IntegerLiteral(v) => v.serialize(s)?,
      Expr::IsConstructor(v) => v.serialize(s)?,
      Expr::Lambda(v) => v.serialize(s)?,
      Expr::LessEquals(v) => v.serialize(s)?,
      Expr::LessThan(v) => v.serialize(s)?,
      Expr::Let(v) => v.serialize(s)?,
      Expr::MapApply(v) => v.serialize(s)?,
      Expr::MapUpdated(v) => v.serialize(s)?,
      Expr::Minus(v) => v.serialize(s)?,
      Expr::Modulo(v) => v.serialize(s)?,
      Expr::MultiplicityInBag(v) => v.serialize(s)?,
      Expr::Not(v) => v.serialize(s)?,
      Expr::Or(v) => v.serialize(s)?,
      Expr::Plus(v) => v.serialize(s)?,
      Expr::Remainder(v) => v.serialize(s)?,
      Expr::SetAdd(v) => v.serialize(s)?,
      Expr::SetDifference(v) => v.serialize(s)?,
      Expr::SetIntersection(v) => v.serialize(s)?,
      Expr::SetUnion(v) => v.serialize(s)?,
      Expr::StringConcat(v) => v.serialize(s)?,
      Expr::StringLength(v) => v.serialize(s)?,
      Expr::StringLiteral(v) => v.serialize(s)?,
      Expr::SubString(v) => v.serialize(s)?,
      Expr::SubsetOf(v) => v.serialize(s)?,
      Expr::Times(v) => v.serialize(s)?,
      Expr::Tuple(v) => v.serialize(s)?,
      Expr::TupleSelect(v) => v.serialize(s)?,
      Expr::UMinus(v) => v.serialize(s)?,
      Expr::UnitLiteral(v) => v.serialize(s)?,
      Expr::Variable(v) => v.serialize(s)?,
    };
    Ok(())
  }
}

/// inox.ast.Expressions.ADT
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ADT<'a> {
  pub id: &'a Identifier,
  pub tps: Seq<&'a Type<'a>>,
  pub args: Seq<&'a Expr<'a>>
}

impl<'a> Serializable for ADT<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(27))?;
    self.id.serialize(s)?;
    self.tps.serialize(s)?;
    self.args.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.ADTSelector
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ADTSelector<'a> {
  pub adt: &'a Expr<'a>,
  pub selector: &'a Identifier
}

impl<'a> Serializable for ADTSelector<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(29))?;
    self.adt.serialize(s)?;
    self.selector.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.And
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct And<'a> {
  pub exprs: Seq<&'a Expr<'a>>
}

impl<'a> Serializable for And<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(31))?;
    self.exprs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.Application
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Application<'a> {
  pub callee: &'a Expr<'a>,
  pub args: Seq<&'a Expr<'a>>
}

impl<'a> Serializable for Application<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(13))?;
    self.callee.serialize(s)?;
    self.args.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.Assume
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Assume<'a> {
  pub pred: &'a Expr<'a>,
  pub body: &'a Expr<'a>
}

impl<'a> Serializable for Assume<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(10))?;
    self.pred.serialize(s)?;
    self.body.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.BVAShiftRight
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BVAShiftRight<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for BVAShiftRight<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(53))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.BVAnd
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BVAnd<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for BVAnd<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(49))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.BVLShiftRight
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BVLShiftRight<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for BVLShiftRight<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(54))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.BVLiteral
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BVLiteral {
  pub signed: Boolean,
  pub value: BigInt,
  pub size: Int
}

/// inox.ast.Expressions.BVNarrowingCast
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BVNarrowingCast<'a> {
  pub expr: &'a Expr<'a>,
  pub newType: &'a BVType
}

impl<'a> Serializable for BVNarrowingCast<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(55))?;
    self.expr.serialize(s)?;
    self.newType.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.BVNot
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BVNot<'a> {
  pub e: &'a Expr<'a>
}

impl<'a> Serializable for BVNot<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(48))?;
    self.e.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.BVOr
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BVOr<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for BVOr<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(50))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.BVShiftLeft
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BVShiftLeft<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for BVShiftLeft<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(52))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.BVWideningCast
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BVWideningCast<'a> {
  pub expr: &'a Expr<'a>,
  pub newType: &'a BVType
}

impl<'a> Serializable for BVWideningCast<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(56))?;
    self.expr.serialize(s)?;
    self.newType.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.BVXor
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BVXor<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for BVXor<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(51))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.BagAdd
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BagAdd<'a> {
  pub bag: &'a Expr<'a>,
  pub elem: &'a Expr<'a>
}

impl<'a> Serializable for BagAdd<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(67))?;
    self.bag.serialize(s)?;
    self.elem.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.BagDifference
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BagDifference<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for BagDifference<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(71))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.BagIntersection
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BagIntersection<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for BagIntersection<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(69))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.BagUnion
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BagUnion<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for BagUnion<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(70))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.BooleanLiteral
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BooleanLiteral {
  pub value: Boolean
}

impl Serializable for BooleanLiteral {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(23))?;
    self.value.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.CharLiteral
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CharLiteral {
  pub value: Char
}

impl Serializable for CharLiteral {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(19))?;
    self.value.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.Choose
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Choose<'a> {
  pub res: &'a ValDef<'a>,
  pub pred: &'a Expr<'a>
}

impl<'a> Serializable for Choose<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(16))?;
    self.res.serialize(s)?;
    self.pred.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.Division
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Division<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for Division<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(41))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.ElementOfSet
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ElementOfSet<'a> {
  pub element: &'a Expr<'a>,
  pub set: &'a Expr<'a>
}

impl<'a> Serializable for ElementOfSet<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(61))?;
    self.element.serialize(s)?;
    self.set.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.Equals
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Equals<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for Equals<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(30))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.FiniteBag
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FiniteBag<'a> {
  pub elements: Seq<(&'a Expr<'a>, &'a Expr<'a>)>,
  pub base: &'a Type<'a>
}

impl<'a> Serializable for FiniteBag<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(66))?;
    self.elements.serialize(s)?;
    self.base.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.FiniteMap
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FiniteMap<'a> {
  pub pairs: Seq<(&'a Expr<'a>, &'a Expr<'a>)>,
  pub default: &'a Expr<'a>,
  pub keyType: &'a Type<'a>,
  pub valueType: &'a Type<'a>
}

impl<'a> Serializable for FiniteMap<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(72))?;
    self.pairs.serialize(s)?;
    self.default.serialize(s)?;
    self.keyType.serialize(s)?;
    self.valueType.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.FiniteSet
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FiniteSet<'a> {
  pub elements: Seq<&'a Expr<'a>>,
  pub base: &'a Type<'a>
}

impl<'a> Serializable for FiniteSet<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(59))?;
    self.elements.serialize(s)?;
    self.base.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.Forall
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Forall<'a> {
  pub params: Seq<&'a ValDef<'a>>,
  pub body: &'a Expr<'a>
}

impl<'a> Serializable for Forall<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(15))?;
    self.params.serialize(s)?;
    self.body.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.FractionLiteral
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FractionLiteral {
  pub numerator: BigInt,
  pub denominator: BigInt
}

impl Serializable for FractionLiteral {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(22))?;
    self.numerator.serialize(s)?;
    self.denominator.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.FunctionInvocation
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FunctionInvocation<'a> {
  pub id: &'a Identifier,
  pub tps: Seq<&'a Type<'a>>,
  pub args: Seq<&'a Expr<'a>>
}

impl<'a> Serializable for FunctionInvocation<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(17))?;
    self.id.serialize(s)?;
    self.tps.serialize(s)?;
    self.args.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.GenericValue
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GenericValue<'a> {
  pub tp: &'a TypeParameter<'a>,
  pub id: Int
}

impl<'a> Serializable for GenericValue<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(26))?;
    self.tp.serialize(s)?;
    self.id.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.GreaterEquals
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GreaterEquals<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for GreaterEquals<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(47))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.GreaterThan
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GreaterThan<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for GreaterThan<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(45))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.IfExpr
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IfExpr<'a> {
  pub cond: &'a Expr<'a>,
  pub thenn: &'a Expr<'a>,
  pub elze: &'a Expr<'a>
}

impl<'a> Serializable for IfExpr<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(18))?;
    self.cond.serialize(s)?;
    self.thenn.serialize(s)?;
    self.elze.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.Implies
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Implies<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for Implies<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(99))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.IntegerLiteral
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IntegerLiteral {
  pub value: BigInt
}

impl Serializable for IntegerLiteral {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(21))?;
    self.value.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.IsConstructor
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IsConstructor<'a> {
  pub expr: &'a Expr<'a>,
  pub id: &'a Identifier
}

impl<'a> Serializable for IsConstructor<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(28))?;
    self.expr.serialize(s)?;
    self.id.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.Lambda
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Lambda<'a> {
  pub params: Seq<&'a ValDef<'a>>,
  pub body: &'a Expr<'a>
}

impl<'a> Serializable for Lambda<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(14))?;
    self.params.serialize(s)?;
    self.body.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.LessEquals
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LessEquals<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for LessEquals<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(46))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.LessThan
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LessThan<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for LessThan<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(44))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.Let
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Let<'a> {
  pub vd: &'a ValDef<'a>,
  pub value: &'a Expr<'a>,
  pub body: &'a Expr<'a>
}

impl<'a> Serializable for Let<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(12))?;
    self.vd.serialize(s)?;
    self.value.serialize(s)?;
    self.body.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.MapApply
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MapApply<'a> {
  pub map: &'a Expr<'a>,
  pub key: &'a Expr<'a>
}

impl<'a> Serializable for MapApply<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(73))?;
    self.map.serialize(s)?;
    self.key.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.MapUpdated
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MapUpdated<'a> {
  pub map: &'a Expr<'a>,
  pub key: &'a Expr<'a>,
  pub value: &'a Expr<'a>
}

impl<'a> Serializable for MapUpdated<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(74))?;
    self.map.serialize(s)?;
    self.key.serialize(s)?;
    self.value.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.Minus
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Minus<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for Minus<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(38))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.Modulo
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Modulo<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for Modulo<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(43))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.MultiplicityInBag
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MultiplicityInBag<'a> {
  pub element: &'a Expr<'a>,
  pub bag: &'a Expr<'a>
}

impl<'a> Serializable for MultiplicityInBag<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(68))?;
    self.element.serialize(s)?;
    self.bag.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.Not
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Not<'a> {
  pub expr: &'a Expr<'a>
}

impl<'a> Serializable for Not<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(33))?;
    self.expr.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.Or
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Or<'a> {
  pub exprs: Seq<&'a Expr<'a>>
}

impl<'a> Serializable for Or<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(32))?;
    self.exprs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.Plus
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Plus<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for Plus<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(37))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.Remainder
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Remainder<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for Remainder<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(42))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.SetAdd
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SetAdd<'a> {
  pub set: &'a Expr<'a>,
  pub elem: &'a Expr<'a>
}

impl<'a> Serializable for SetAdd<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(60))?;
    self.set.serialize(s)?;
    self.elem.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.SetDifference
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SetDifference<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for SetDifference<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(65))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.SetIntersection
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SetIntersection<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for SetIntersection<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(63))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.SetUnion
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SetUnion<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for SetUnion<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(64))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.StringConcat
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StringConcat<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for StringConcat<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(34))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.StringLength
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StringLength<'a> {
  pub expr: &'a Expr<'a>
}

impl<'a> Serializable for StringLength<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(36))?;
    self.expr.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.StringLiteral
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StringLiteral {
  pub value: String
}

impl Serializable for StringLiteral {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(24))?;
    self.value.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.SubString
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SubString<'a> {
  pub expr: &'a Expr<'a>,
  pub start: &'a Expr<'a>,
  pub end: &'a Expr<'a>
}

impl<'a> Serializable for SubString<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(35))?;
    self.expr.serialize(s)?;
    self.start.serialize(s)?;
    self.end.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.SubsetOf
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SubsetOf<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for SubsetOf<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(62))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.Times
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Times<'a> {
  pub lhs: &'a Expr<'a>,
  pub rhs: &'a Expr<'a>
}

impl<'a> Serializable for Times<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(40))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.Tuple
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Tuple<'a> {
  pub exprs: Seq<&'a Expr<'a>>
}

impl<'a> Serializable for Tuple<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(57))?;
    self.exprs.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.TupleSelect
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TupleSelect<'a> {
  pub tuple: &'a Expr<'a>,
  pub index: Int
}

impl<'a> Serializable for TupleSelect<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(58))?;
    self.tuple.serialize(s)?;
    self.index.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.UMinus
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct UMinus<'a> {
  pub expr: &'a Expr<'a>
}

impl<'a> Serializable for UMinus<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(39))?;
    self.expr.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Expressions.UnitLiteral
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct UnitLiteral {
  
}

impl Serializable for UnitLiteral {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(25))?;
    Ok(())
  }
}
/// inox.ast.Expressions.Variable
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Variable<'a> {
  pub id: &'a Identifier,
  pub tpe: &'a Type<'a>,
  pub flags: Seq<Flag<'a>>
}

impl<'a> Serializable for Variable<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(11))?;
    self.id.serialize(s)?;
    self.tpe.serialize(s)?;
    self.flags.serialize(s)?;
    Ok(())
  }
}

// === Types ===

/// inox.ast.Types.Type
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type<'a> {
  ADTType(ADTType<'a>),
  BVType(BVType),
  BagType(BagType<'a>),
  BooleanType(BooleanType),
  CharType(CharType),
  FunctionType(FunctionType<'a>),
  IntegerType(IntegerType),
  MapType(MapType<'a>),
  PiType(PiType<'a>),
  RealType(RealType),
  RefinementType(RefinementType<'a>),
  SetType(SetType<'a>),
  SigmaType(SigmaType<'a>),
  StringType(StringType),
  TupleType(TupleType<'a>),
  TypeParameter(TypeParameter<'a>),
  UnitType(UnitType),
  Untyped(Untyped)
}

impl<'a> Serializable for Type<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    match self {
      Type::ADTType(v) => v.serialize(s)?,
      Type::BVType(v) => v.serialize(s)?,
      Type::BagType(v) => v.serialize(s)?,
      Type::BooleanType(v) => v.serialize(s)?,
      Type::CharType(v) => v.serialize(s)?,
      Type::FunctionType(v) => v.serialize(s)?,
      Type::IntegerType(v) => v.serialize(s)?,
      Type::MapType(v) => v.serialize(s)?,
      Type::PiType(v) => v.serialize(s)?,
      Type::RealType(v) => v.serialize(s)?,
      Type::RefinementType(v) => v.serialize(s)?,
      Type::SetType(v) => v.serialize(s)?,
      Type::SigmaType(v) => v.serialize(s)?,
      Type::StringType(v) => v.serialize(s)?,
      Type::TupleType(v) => v.serialize(s)?,
      Type::TypeParameter(v) => v.serialize(s)?,
      Type::UnitType(v) => v.serialize(s)?,
      Type::Untyped(v) => v.serialize(s)?,
    };
    Ok(())
  }
}

/// inox.ast.Types.ADTType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ADTType<'a> {
  pub id: &'a Identifier,
  pub tps: Seq<&'a Type<'a>>
}

impl<'a> Serializable for ADTType<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(89))?;
    self.id.serialize(s)?;
    self.tps.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Types.BVType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BVType {
  pub signed: Boolean,
  pub size: Int
}

impl Serializable for BVType {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(82))?;
    self.signed.serialize(s)?;
    self.size.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Types.BagType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BagType<'a> {
  pub base: &'a Type<'a>
}

impl<'a> Serializable for BagType<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(86))?;
    self.base.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Types.BooleanType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BooleanType {
  
}

impl Serializable for BooleanType {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(76))?;
    Ok(())
  }
}
/// inox.ast.Types.CharType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CharType {
  
}

impl Serializable for CharType {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(78))?;
    Ok(())
  }
}
/// inox.ast.Types.FunctionType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FunctionType<'a> {
  pub from: Seq<&'a Type<'a>>,
  pub to: &'a Type<'a>
}

impl<'a> Serializable for FunctionType<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(88))?;
    self.from.serialize(s)?;
    self.to.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Types.IntegerType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IntegerType {
  
}

impl Serializable for IntegerType {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(79))?;
    Ok(())
  }
}
/// inox.ast.Types.MapType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MapType<'a> {
  pub from: &'a Type<'a>,
  pub to: &'a Type<'a>
}

impl<'a> Serializable for MapType<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(87))?;
    self.from.serialize(s)?;
    self.to.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Types.PiType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PiType<'a> {
  pub params: Seq<&'a ValDef<'a>>,
  pub to: &'a Type<'a>
}

impl<'a> Serializable for PiType<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(101))?;
    self.params.serialize(s)?;
    self.to.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Types.RealType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RealType {
  
}

impl Serializable for RealType {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(80))?;
    Ok(())
  }
}
/// inox.ast.Types.RefinementType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RefinementType<'a> {
  pub vd: &'a ValDef<'a>,
  pub prop: &'a Expr<'a>
}

impl<'a> Serializable for RefinementType<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(100))?;
    self.vd.serialize(s)?;
    self.prop.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Types.SetType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SetType<'a> {
  pub base: &'a Type<'a>
}

impl<'a> Serializable for SetType<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(85))?;
    self.base.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Types.SigmaType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SigmaType<'a> {
  pub params: Seq<&'a ValDef<'a>>,
  pub to: &'a Type<'a>
}

impl<'a> Serializable for SigmaType<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(102))?;
    self.params.serialize(s)?;
    self.to.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Types.StringType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StringType {
  
}

impl Serializable for StringType {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(81))?;
    Ok(())
  }
}
/// inox.ast.Types.TupleType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TupleType<'a> {
  pub bases: Seq<&'a Type<'a>>
}

impl<'a> Serializable for TupleType<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(84))?;
    self.bases.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Types.TypeParameter
#[derive(Clone, Debug)]
pub struct TypeParameter<'a> {
  pub id: &'a Identifier,
  pub flags: Seq<Flag<'a>>
}

impl<'a> PartialEq for TypeParameter<'a> {
  fn eq(&self, other: &Self) -> bool { self.id == other.id }
}
impl<'a> Eq for TypeParameter<'a> {}
impl<'a> PartialOrd for TypeParameter<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}
impl<'a> Ord for TypeParameter<'a> {
  fn cmp(&self, other: &Self) -> Ordering { self.id.cmp(&other.id) }
}
impl<'a> Hash for TypeParameter<'a> {
  fn hash<H: Hasher>(&self, state: &mut H) { self.id.hash(state); }
}

impl<'a> Serializable for TypeParameter<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(83))?;
    self.id.serialize(s)?;
    self.flags.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Types.UnitType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct UnitType {
  
}

impl Serializable for UnitType {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(77))?;
    Ok(())
  }
}
/// inox.ast.Types.Untyped
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Untyped {
  
}

impl Serializable for Untyped {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(75))?;
    Ok(())
  }
}

// === Other ===

/// inox.ast.Definitions.ADTConstructor
#[derive(Clone, Debug)]
pub struct ADTConstructor<'a> {
  pub id: &'a Identifier,
  pub sort: &'a Identifier,
  pub fields: Seq<&'a ValDef<'a>>
}

impl<'a> PartialEq for ADTConstructor<'a> {
  fn eq(&self, other: &Self) -> bool { self.id == other.id }
}
impl<'a> Eq for ADTConstructor<'a> {}
impl<'a> PartialOrd for ADTConstructor<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}
impl<'a> Ord for ADTConstructor<'a> {
  fn cmp(&self, other: &Self) -> Ordering { self.id.cmp(&other.id) }
}
impl<'a> Hash for ADTConstructor<'a> {
  fn hash<H: Hasher>(&self, state: &mut H) { self.id.hash(state); }
}

impl<'a> Serializable for ADTConstructor<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(97))?;
    self.id.serialize(s)?;
    self.sort.serialize(s)?;
    self.fields.serialize(s)?;
    Ok(())
  }
}
/// inox.ast.Identifier
#[derive(Clone, Debug)]
pub struct Identifier {
  pub name: String,
  pub globalId: Int,
  pub id: Int
}

impl PartialEq for Identifier {
  fn eq(&self, other: &Self) -> bool { self.id == other.id }
}
impl Eq for Identifier {}
impl PartialOrd for Identifier {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}
impl Ord for Identifier {
  fn cmp(&self, other: &Self) -> Ordering { self.id.cmp(&other.id) }
}
impl Hash for Identifier {
  fn hash<H: Hasher>(&self, state: &mut H) { self.id.hash(state); }
}
