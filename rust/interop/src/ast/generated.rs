// AUTO-GENERATED FROM STAINLESS
#![allow(non_snake_case)]
use super::Factory;
use crate::ser::types::*;
use crate::ser::{MarkerId, Serializable, SerializationResult, Serializer};
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

// === Definitions ===

/// inox.ast.Definitions.Definition
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Definition<'a> {
  ADTSort(&'a ADTSort<'a>),
  FunDef(&'a FunDef<'a>),
  TypeParameterDef(&'a TypeParameterDef<'a>),
  ValDef(&'a ValDef<'a>),
}

impl Factory {
  pub fn ADTSort<'a>(
    &'a self,
    id: &'a Identifier,
    tparams: Seq<&'a TypeParameterDef<'a>>,
    constructors: Seq<&'a ADTConstructor<'a>>,
    flags: Seq<Flag<'a>>,
  ) -> &'a mut ADTSort<'a> {
    self.bump.alloc(ADTSort {
      id,
      tparams,
      constructors,
      flags,
    })
  }

  pub fn FunDef<'a>(
    &'a self,
    id: &'a Identifier,
    tparams: Seq<&'a TypeParameterDef<'a>>,
    params: Seq<&'a ValDef<'a>>,
    returnType: Type<'a>,
    fullBody: Expr<'a>,
    flags: Seq<Flag<'a>>,
  ) -> &'a mut FunDef<'a> {
    self.bump.alloc(FunDef {
      id,
      tparams,
      params,
      returnType,
      fullBody,
      flags,
    })
  }

  pub fn TypeParameterDef<'a>(&'a self, tp: &'a TypeParameter<'a>) -> &'a mut TypeParameterDef<'a> {
    self.bump.alloc(TypeParameterDef { tp })
  }

  pub fn ValDef<'a>(&'a self, v: &'a Variable<'a>) -> &'a mut ValDef<'a> {
    self.bump.alloc(ValDef { v })
  }
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

derive_conversions_for_ast!(Definition<'a>, ADTSort<'a>);
derive_conversions_for_ast!(Definition<'a>, FunDef<'a>);
derive_conversions_for_ast!(Definition<'a>, TypeParameterDef<'a>);
derive_conversions_for_ast!(Definition<'a>, ValDef<'a>);

/// inox.ast.Definitions.ADTSort
#[derive(Clone, Debug)]
pub struct ADTSort<'a> {
  pub id: &'a Identifier,
  pub tparams: Seq<&'a TypeParameterDef<'a>>,
  pub constructors: Seq<&'a ADTConstructor<'a>>,
  pub flags: Seq<Flag<'a>>,
}

impl<'a> PartialEq for ADTSort<'a> {
  fn eq(&self, other: &Self) -> bool {
    self.id == other.id
  }
}
impl<'a> Eq for ADTSort<'a> {}
impl<'a> PartialOrd for ADTSort<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}
impl<'a> Ord for ADTSort<'a> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.id.cmp(&other.id)
  }
}
impl<'a> Hash for ADTSort<'a> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.id.hash(state);
  }
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
  pub returnType: Type<'a>,
  pub fullBody: Expr<'a>,
  pub flags: Seq<Flag<'a>>,
}

impl<'a> PartialEq for FunDef<'a> {
  fn eq(&self, other: &Self) -> bool {
    self.id == other.id
  }
}
impl<'a> Eq for FunDef<'a> {}
impl<'a> PartialOrd for FunDef<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}
impl<'a> Ord for FunDef<'a> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.id.cmp(&other.id)
  }
}
impl<'a> Hash for FunDef<'a> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.id.hash(state);
  }
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
  pub tp: &'a TypeParameter<'a>,
}

impl<'a> PartialEq for TypeParameterDef<'a> {
  fn eq(&self, other: &Self) -> bool {
    self.tp.id == other.tp.id
  }
}
impl<'a> Eq for TypeParameterDef<'a> {}
impl<'a> PartialOrd for TypeParameterDef<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}
impl<'a> Ord for TypeParameterDef<'a> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.tp.id.cmp(&other.tp.id)
  }
}
impl<'a> Hash for TypeParameterDef<'a> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.tp.id.hash(state);
  }
}

/// inox.ast.Definitions.ValDef
#[derive(Clone, Debug)]
pub struct ValDef<'a> {
  pub v: &'a Variable<'a>,
}

impl<'a> PartialEq for ValDef<'a> {
  fn eq(&self, other: &Self) -> bool {
    self.v.id == other.v.id
  }
}
impl<'a> Eq for ValDef<'a> {}
impl<'a> PartialOrd for ValDef<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}
impl<'a> Ord for ValDef<'a> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.v.id.cmp(&other.v.id)
  }
}
impl<'a> Hash for ValDef<'a> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.v.id.hash(state);
  }
}

// === Flags ===

/// inox.ast.Definitions.Flag
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Flag<'a> {
  Annotation(&'a Annotation<'a>),
  HasADTEquality(&'a HasADTEquality<'a>),
  HasADTInvariant(&'a HasADTInvariant<'a>),
}

impl Factory {
  pub fn Annotation<'a>(&'a self, name: String, args: Seq<Expr<'a>>) -> &'a mut Annotation<'a> {
    self.bump.alloc(Annotation { name, args })
  }

  pub fn HasADTEquality<'a>(&'a self, id: &'a Identifier) -> &'a mut HasADTEquality<'a> {
    self.bump.alloc(HasADTEquality { id })
  }

  pub fn HasADTInvariant<'a>(&'a self, id: &'a Identifier) -> &'a mut HasADTInvariant<'a> {
    self.bump.alloc(HasADTInvariant { id })
  }
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

derive_conversions_for_ast!(Flag<'a>, Annotation<'a>);
derive_conversions_for_ast!(Flag<'a>, HasADTEquality<'a>);
derive_conversions_for_ast!(Flag<'a>, HasADTInvariant<'a>);

/// inox.ast.Definitions.Annotation
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Annotation<'a> {
  pub name: String,
  pub args: Seq<Expr<'a>>,
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
  pub id: &'a Identifier,
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
  pub id: &'a Identifier,
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Expr<'a> {
  ADT(&'a ADT<'a>),
  ADTSelector(&'a ADTSelector<'a>),
  And(&'a And<'a>),
  Application(&'a Application<'a>),
  Assume(&'a Assume<'a>),
  BVAShiftRight(&'a BVAShiftRight<'a>),
  BVAnd(&'a BVAnd<'a>),
  BVLShiftRight(&'a BVLShiftRight<'a>),
  BVLiteral(&'a BVLiteral),
  BVNarrowingCast(&'a BVNarrowingCast<'a>),
  BVNot(&'a BVNot<'a>),
  BVOr(&'a BVOr<'a>),
  BVShiftLeft(&'a BVShiftLeft<'a>),
  BVWideningCast(&'a BVWideningCast<'a>),
  BVXor(&'a BVXor<'a>),
  BagAdd(&'a BagAdd<'a>),
  BagDifference(&'a BagDifference<'a>),
  BagIntersection(&'a BagIntersection<'a>),
  BagUnion(&'a BagUnion<'a>),
  BooleanLiteral(&'a BooleanLiteral),
  CharLiteral(&'a CharLiteral),
  Choose(&'a Choose<'a>),
  Division(&'a Division<'a>),
  ElementOfSet(&'a ElementOfSet<'a>),
  Equals(&'a Equals<'a>),
  FiniteBag(&'a FiniteBag<'a>),
  FiniteMap(&'a FiniteMap<'a>),
  FiniteSet(&'a FiniteSet<'a>),
  Forall(&'a Forall<'a>),
  FractionLiteral(&'a FractionLiteral),
  FunctionInvocation(&'a FunctionInvocation<'a>),
  GenericValue(&'a GenericValue<'a>),
  GreaterEquals(&'a GreaterEquals<'a>),
  GreaterThan(&'a GreaterThan<'a>),
  IfExpr(&'a IfExpr<'a>),
  Implies(&'a Implies<'a>),
  IntegerLiteral(&'a IntegerLiteral),
  IsConstructor(&'a IsConstructor<'a>),
  Lambda(&'a Lambda<'a>),
  LessEquals(&'a LessEquals<'a>),
  LessThan(&'a LessThan<'a>),
  Let(&'a Let<'a>),
  MapApply(&'a MapApply<'a>),
  MapUpdated(&'a MapUpdated<'a>),
  Minus(&'a Minus<'a>),
  Modulo(&'a Modulo<'a>),
  MultiplicityInBag(&'a MultiplicityInBag<'a>),
  Not(&'a Not<'a>),
  Or(&'a Or<'a>),
  Plus(&'a Plus<'a>),
  Remainder(&'a Remainder<'a>),
  SetAdd(&'a SetAdd<'a>),
  SetDifference(&'a SetDifference<'a>),
  SetIntersection(&'a SetIntersection<'a>),
  SetUnion(&'a SetUnion<'a>),
  StringConcat(&'a StringConcat<'a>),
  StringLength(&'a StringLength<'a>),
  StringLiteral(&'a StringLiteral),
  SubString(&'a SubString<'a>),
  SubsetOf(&'a SubsetOf<'a>),
  Times(&'a Times<'a>),
  Tuple(&'a Tuple<'a>),
  TupleSelect(&'a TupleSelect<'a>),
  UMinus(&'a UMinus<'a>),
  UnitLiteral(&'a UnitLiteral),
  Variable(&'a Variable<'a>),
}

impl Factory {
  pub fn ADT<'a>(
    &'a self,
    id: &'a Identifier,
    tps: Seq<Type<'a>>,
    args: Seq<Expr<'a>>,
  ) -> &'a mut ADT<'a> {
    self.bump.alloc(ADT { id, tps, args })
  }

  pub fn ADTSelector<'a>(
    &'a self,
    adt: Expr<'a>,
    selector: &'a Identifier,
  ) -> &'a mut ADTSelector<'a> {
    self.bump.alloc(ADTSelector { adt, selector })
  }

  pub fn And<'a>(&'a self, exprs: Seq<Expr<'a>>) -> &'a mut And<'a> {
    self.bump.alloc(And { exprs })
  }

  pub fn Application<'a>(
    &'a self,
    callee: Expr<'a>,
    args: Seq<Expr<'a>>,
  ) -> &'a mut Application<'a> {
    self.bump.alloc(Application { callee, args })
  }

  pub fn Assume<'a>(&'a self, pred: Expr<'a>, body: Expr<'a>) -> &'a mut Assume<'a> {
    self.bump.alloc(Assume { pred, body })
  }

  pub fn BVAShiftRight<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut BVAShiftRight<'a> {
    self.bump.alloc(BVAShiftRight { lhs, rhs })
  }

  pub fn BVAnd<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut BVAnd<'a> {
    self.bump.alloc(BVAnd { lhs, rhs })
  }

  pub fn BVLShiftRight<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut BVLShiftRight<'a> {
    self.bump.alloc(BVLShiftRight { lhs, rhs })
  }

  pub fn BVLiteral<'a>(&'a self, signed: Boolean, value: BigInt, size: Int) -> &'a mut BVLiteral {
    self.bump.alloc(BVLiteral {
      signed,
      value,
      size,
    })
  }

  pub fn BVNarrowingCast<'a>(
    &'a self,
    expr: Expr<'a>,
    newType: &'a BVType,
  ) -> &'a mut BVNarrowingCast<'a> {
    self.bump.alloc(BVNarrowingCast { expr, newType })
  }

  pub fn BVNot<'a>(&'a self, e: Expr<'a>) -> &'a mut BVNot<'a> {
    self.bump.alloc(BVNot { e })
  }

  pub fn BVOr<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut BVOr<'a> {
    self.bump.alloc(BVOr { lhs, rhs })
  }

  pub fn BVShiftLeft<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut BVShiftLeft<'a> {
    self.bump.alloc(BVShiftLeft { lhs, rhs })
  }

  pub fn BVWideningCast<'a>(
    &'a self,
    expr: Expr<'a>,
    newType: &'a BVType,
  ) -> &'a mut BVWideningCast<'a> {
    self.bump.alloc(BVWideningCast { expr, newType })
  }

  pub fn BVXor<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut BVXor<'a> {
    self.bump.alloc(BVXor { lhs, rhs })
  }

  pub fn BagAdd<'a>(&'a self, bag: Expr<'a>, elem: Expr<'a>) -> &'a mut BagAdd<'a> {
    self.bump.alloc(BagAdd { bag, elem })
  }

  pub fn BagDifference<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut BagDifference<'a> {
    self.bump.alloc(BagDifference { lhs, rhs })
  }

  pub fn BagIntersection<'a>(
    &'a self,
    lhs: Expr<'a>,
    rhs: Expr<'a>,
  ) -> &'a mut BagIntersection<'a> {
    self.bump.alloc(BagIntersection { lhs, rhs })
  }

  pub fn BagUnion<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut BagUnion<'a> {
    self.bump.alloc(BagUnion { lhs, rhs })
  }

  pub fn BooleanLiteral<'a>(&'a self, value: Boolean) -> &'a mut BooleanLiteral {
    self.bump.alloc(BooleanLiteral { value })
  }

  pub fn CharLiteral<'a>(&'a self, value: Char) -> &'a mut CharLiteral {
    self.bump.alloc(CharLiteral { value })
  }

  pub fn Choose<'a>(&'a self, res: &'a ValDef<'a>, pred: Expr<'a>) -> &'a mut Choose<'a> {
    self.bump.alloc(Choose { res, pred })
  }

  pub fn Division<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut Division<'a> {
    self.bump.alloc(Division { lhs, rhs })
  }

  pub fn ElementOfSet<'a>(&'a self, element: Expr<'a>, set: Expr<'a>) -> &'a mut ElementOfSet<'a> {
    self.bump.alloc(ElementOfSet { element, set })
  }

  pub fn Equals<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut Equals<'a> {
    self.bump.alloc(Equals { lhs, rhs })
  }

  pub fn FiniteBag<'a>(
    &'a self,
    elements: Seq<(Expr<'a>, Expr<'a>)>,
    base: Type<'a>,
  ) -> &'a mut FiniteBag<'a> {
    self.bump.alloc(FiniteBag { elements, base })
  }

  pub fn FiniteMap<'a>(
    &'a self,
    pairs: Seq<(Expr<'a>, Expr<'a>)>,
    default: Expr<'a>,
    keyType: Type<'a>,
    valueType: Type<'a>,
  ) -> &'a mut FiniteMap<'a> {
    self.bump.alloc(FiniteMap {
      pairs,
      default,
      keyType,
      valueType,
    })
  }

  pub fn FiniteSet<'a>(&'a self, elements: Seq<Expr<'a>>, base: Type<'a>) -> &'a mut FiniteSet<'a> {
    self.bump.alloc(FiniteSet { elements, base })
  }

  pub fn Forall<'a>(&'a self, params: Seq<&'a ValDef<'a>>, body: Expr<'a>) -> &'a mut Forall<'a> {
    self.bump.alloc(Forall { params, body })
  }

  pub fn FractionLiteral<'a>(
    &'a self,
    numerator: BigInt,
    denominator: BigInt,
  ) -> &'a mut FractionLiteral {
    self.bump.alloc(FractionLiteral {
      numerator,
      denominator,
    })
  }

  pub fn FunctionInvocation<'a>(
    &'a self,
    id: &'a Identifier,
    tps: Seq<Type<'a>>,
    args: Seq<Expr<'a>>,
  ) -> &'a mut FunctionInvocation<'a> {
    self.bump.alloc(FunctionInvocation { id, tps, args })
  }

  pub fn GenericValue<'a>(
    &'a self,
    tp: &'a TypeParameter<'a>,
    id: Int,
  ) -> &'a mut GenericValue<'a> {
    self.bump.alloc(GenericValue { tp, id })
  }

  pub fn GreaterEquals<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut GreaterEquals<'a> {
    self.bump.alloc(GreaterEquals { lhs, rhs })
  }

  pub fn GreaterThan<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut GreaterThan<'a> {
    self.bump.alloc(GreaterThan { lhs, rhs })
  }

  pub fn IfExpr<'a>(
    &'a self,
    cond: Expr<'a>,
    thenn: Expr<'a>,
    elze: Expr<'a>,
  ) -> &'a mut IfExpr<'a> {
    self.bump.alloc(IfExpr { cond, thenn, elze })
  }

  pub fn Implies<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut Implies<'a> {
    self.bump.alloc(Implies { lhs, rhs })
  }

  pub fn IntegerLiteral<'a>(&'a self, value: BigInt) -> &'a mut IntegerLiteral {
    self.bump.alloc(IntegerLiteral { value })
  }

  pub fn IsConstructor<'a>(
    &'a self,
    expr: Expr<'a>,
    id: &'a Identifier,
  ) -> &'a mut IsConstructor<'a> {
    self.bump.alloc(IsConstructor { expr, id })
  }

  pub fn Lambda<'a>(&'a self, params: Seq<&'a ValDef<'a>>, body: Expr<'a>) -> &'a mut Lambda<'a> {
    self.bump.alloc(Lambda { params, body })
  }

  pub fn LessEquals<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut LessEquals<'a> {
    self.bump.alloc(LessEquals { lhs, rhs })
  }

  pub fn LessThan<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut LessThan<'a> {
    self.bump.alloc(LessThan { lhs, rhs })
  }

  pub fn Let<'a>(&'a self, vd: &'a ValDef<'a>, value: Expr<'a>, body: Expr<'a>) -> &'a mut Let<'a> {
    self.bump.alloc(Let { vd, value, body })
  }

  pub fn MapApply<'a>(&'a self, map: Expr<'a>, key: Expr<'a>) -> &'a mut MapApply<'a> {
    self.bump.alloc(MapApply { map, key })
  }

  pub fn MapUpdated<'a>(
    &'a self,
    map: Expr<'a>,
    key: Expr<'a>,
    value: Expr<'a>,
  ) -> &'a mut MapUpdated<'a> {
    self.bump.alloc(MapUpdated { map, key, value })
  }

  pub fn Minus<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut Minus<'a> {
    self.bump.alloc(Minus { lhs, rhs })
  }

  pub fn Modulo<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut Modulo<'a> {
    self.bump.alloc(Modulo { lhs, rhs })
  }

  pub fn MultiplicityInBag<'a>(
    &'a self,
    element: Expr<'a>,
    bag: Expr<'a>,
  ) -> &'a mut MultiplicityInBag<'a> {
    self.bump.alloc(MultiplicityInBag { element, bag })
  }

  pub fn Not<'a>(&'a self, expr: Expr<'a>) -> &'a mut Not<'a> {
    self.bump.alloc(Not { expr })
  }

  pub fn Or<'a>(&'a self, exprs: Seq<Expr<'a>>) -> &'a mut Or<'a> {
    self.bump.alloc(Or { exprs })
  }

  pub fn Plus<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut Plus<'a> {
    self.bump.alloc(Plus { lhs, rhs })
  }

  pub fn Remainder<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut Remainder<'a> {
    self.bump.alloc(Remainder { lhs, rhs })
  }

  pub fn SetAdd<'a>(&'a self, set: Expr<'a>, elem: Expr<'a>) -> &'a mut SetAdd<'a> {
    self.bump.alloc(SetAdd { set, elem })
  }

  pub fn SetDifference<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut SetDifference<'a> {
    self.bump.alloc(SetDifference { lhs, rhs })
  }

  pub fn SetIntersection<'a>(
    &'a self,
    lhs: Expr<'a>,
    rhs: Expr<'a>,
  ) -> &'a mut SetIntersection<'a> {
    self.bump.alloc(SetIntersection { lhs, rhs })
  }

  pub fn SetUnion<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut SetUnion<'a> {
    self.bump.alloc(SetUnion { lhs, rhs })
  }

  pub fn StringConcat<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut StringConcat<'a> {
    self.bump.alloc(StringConcat { lhs, rhs })
  }

  pub fn StringLength<'a>(&'a self, expr: Expr<'a>) -> &'a mut StringLength<'a> {
    self.bump.alloc(StringLength { expr })
  }

  pub fn StringLiteral<'a>(&'a self, value: String) -> &'a mut StringLiteral {
    self.bump.alloc(StringLiteral { value })
  }

  pub fn SubString<'a>(
    &'a self,
    expr: Expr<'a>,
    start: Expr<'a>,
    end: Expr<'a>,
  ) -> &'a mut SubString<'a> {
    self.bump.alloc(SubString { expr, start, end })
  }

  pub fn SubsetOf<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut SubsetOf<'a> {
    self.bump.alloc(SubsetOf { lhs, rhs })
  }

  pub fn Times<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut Times<'a> {
    self.bump.alloc(Times { lhs, rhs })
  }

  pub fn Tuple<'a>(&'a self, exprs: Seq<Expr<'a>>) -> &'a mut Tuple<'a> {
    self.bump.alloc(Tuple { exprs })
  }

  pub fn TupleSelect<'a>(&'a self, tuple: Expr<'a>, index: Int) -> &'a mut TupleSelect<'a> {
    self.bump.alloc(TupleSelect { tuple, index })
  }

  pub fn UMinus<'a>(&'a self, expr: Expr<'a>) -> &'a mut UMinus<'a> {
    self.bump.alloc(UMinus { expr })
  }

  pub fn UnitLiteral<'a>(&'a self) -> &'a mut UnitLiteral {
    self.bump.alloc(UnitLiteral {})
  }

  pub fn Variable<'a>(
    &'a self,
    id: &'a Identifier,
    tpe: Type<'a>,
    flags: Seq<Flag<'a>>,
  ) -> &'a mut Variable<'a> {
    self.bump.alloc(Variable { id, tpe, flags })
  }
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

derive_conversions_for_ast!(Expr<'a>, ADT<'a>);
derive_conversions_for_ast!(Expr<'a>, ADTSelector<'a>);
derive_conversions_for_ast!(Expr<'a>, And<'a>);
derive_conversions_for_ast!(Expr<'a>, Application<'a>);
derive_conversions_for_ast!(Expr<'a>, Assume<'a>);
derive_conversions_for_ast!(Expr<'a>, BVAShiftRight<'a>);
derive_conversions_for_ast!(Expr<'a>, BVAnd<'a>);
derive_conversions_for_ast!(Expr<'a>, BVLShiftRight<'a>);
derive_conversions_for_ast!(Expr<'a>, BVLiteral);
derive_conversions_for_ast!(Expr<'a>, BVNarrowingCast<'a>);
derive_conversions_for_ast!(Expr<'a>, BVNot<'a>);
derive_conversions_for_ast!(Expr<'a>, BVOr<'a>);
derive_conversions_for_ast!(Expr<'a>, BVShiftLeft<'a>);
derive_conversions_for_ast!(Expr<'a>, BVWideningCast<'a>);
derive_conversions_for_ast!(Expr<'a>, BVXor<'a>);
derive_conversions_for_ast!(Expr<'a>, BagAdd<'a>);
derive_conversions_for_ast!(Expr<'a>, BagDifference<'a>);
derive_conversions_for_ast!(Expr<'a>, BagIntersection<'a>);
derive_conversions_for_ast!(Expr<'a>, BagUnion<'a>);
derive_conversions_for_ast!(Expr<'a>, BooleanLiteral);
derive_conversions_for_ast!(Expr<'a>, CharLiteral);
derive_conversions_for_ast!(Expr<'a>, Choose<'a>);
derive_conversions_for_ast!(Expr<'a>, Division<'a>);
derive_conversions_for_ast!(Expr<'a>, ElementOfSet<'a>);
derive_conversions_for_ast!(Expr<'a>, Equals<'a>);
derive_conversions_for_ast!(Expr<'a>, FiniteBag<'a>);
derive_conversions_for_ast!(Expr<'a>, FiniteMap<'a>);
derive_conversions_for_ast!(Expr<'a>, FiniteSet<'a>);
derive_conversions_for_ast!(Expr<'a>, Forall<'a>);
derive_conversions_for_ast!(Expr<'a>, FractionLiteral);
derive_conversions_for_ast!(Expr<'a>, FunctionInvocation<'a>);
derive_conversions_for_ast!(Expr<'a>, GenericValue<'a>);
derive_conversions_for_ast!(Expr<'a>, GreaterEquals<'a>);
derive_conversions_for_ast!(Expr<'a>, GreaterThan<'a>);
derive_conversions_for_ast!(Expr<'a>, IfExpr<'a>);
derive_conversions_for_ast!(Expr<'a>, Implies<'a>);
derive_conversions_for_ast!(Expr<'a>, IntegerLiteral);
derive_conversions_for_ast!(Expr<'a>, IsConstructor<'a>);
derive_conversions_for_ast!(Expr<'a>, Lambda<'a>);
derive_conversions_for_ast!(Expr<'a>, LessEquals<'a>);
derive_conversions_for_ast!(Expr<'a>, LessThan<'a>);
derive_conversions_for_ast!(Expr<'a>, Let<'a>);
derive_conversions_for_ast!(Expr<'a>, MapApply<'a>);
derive_conversions_for_ast!(Expr<'a>, MapUpdated<'a>);
derive_conversions_for_ast!(Expr<'a>, Minus<'a>);
derive_conversions_for_ast!(Expr<'a>, Modulo<'a>);
derive_conversions_for_ast!(Expr<'a>, MultiplicityInBag<'a>);
derive_conversions_for_ast!(Expr<'a>, Not<'a>);
derive_conversions_for_ast!(Expr<'a>, Or<'a>);
derive_conversions_for_ast!(Expr<'a>, Plus<'a>);
derive_conversions_for_ast!(Expr<'a>, Remainder<'a>);
derive_conversions_for_ast!(Expr<'a>, SetAdd<'a>);
derive_conversions_for_ast!(Expr<'a>, SetDifference<'a>);
derive_conversions_for_ast!(Expr<'a>, SetIntersection<'a>);
derive_conversions_for_ast!(Expr<'a>, SetUnion<'a>);
derive_conversions_for_ast!(Expr<'a>, StringConcat<'a>);
derive_conversions_for_ast!(Expr<'a>, StringLength<'a>);
derive_conversions_for_ast!(Expr<'a>, StringLiteral);
derive_conversions_for_ast!(Expr<'a>, SubString<'a>);
derive_conversions_for_ast!(Expr<'a>, SubsetOf<'a>);
derive_conversions_for_ast!(Expr<'a>, Times<'a>);
derive_conversions_for_ast!(Expr<'a>, Tuple<'a>);
derive_conversions_for_ast!(Expr<'a>, TupleSelect<'a>);
derive_conversions_for_ast!(Expr<'a>, UMinus<'a>);
derive_conversions_for_ast!(Expr<'a>, UnitLiteral);
derive_conversions_for_ast!(Expr<'a>, Variable<'a>);

/// inox.ast.Expressions.ADT
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ADT<'a> {
  pub id: &'a Identifier,
  pub tps: Seq<Type<'a>>,
  pub args: Seq<Expr<'a>>,
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
  pub adt: Expr<'a>,
  pub selector: &'a Identifier,
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
  pub exprs: Seq<Expr<'a>>,
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
  pub callee: Expr<'a>,
  pub args: Seq<Expr<'a>>,
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
  pub pred: Expr<'a>,
  pub body: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub size: Int,
}

/// inox.ast.Expressions.BVNarrowingCast
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BVNarrowingCast<'a> {
  pub expr: Expr<'a>,
  pub newType: &'a BVType,
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
  pub e: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub expr: Expr<'a>,
  pub newType: &'a BVType,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub bag: Expr<'a>,
  pub elem: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub value: Boolean,
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
  pub value: Char,
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
  pub pred: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub element: Expr<'a>,
  pub set: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub elements: Seq<(Expr<'a>, Expr<'a>)>,
  pub base: Type<'a>,
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
  pub pairs: Seq<(Expr<'a>, Expr<'a>)>,
  pub default: Expr<'a>,
  pub keyType: Type<'a>,
  pub valueType: Type<'a>,
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
  pub elements: Seq<Expr<'a>>,
  pub base: Type<'a>,
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
  pub body: Expr<'a>,
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
  pub denominator: BigInt,
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
  pub tps: Seq<Type<'a>>,
  pub args: Seq<Expr<'a>>,
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
  pub id: Int,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub cond: Expr<'a>,
  pub thenn: Expr<'a>,
  pub elze: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub value: BigInt,
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
  pub expr: Expr<'a>,
  pub id: &'a Identifier,
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
  pub body: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub value: Expr<'a>,
  pub body: Expr<'a>,
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
  pub map: Expr<'a>,
  pub key: Expr<'a>,
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
  pub map: Expr<'a>,
  pub key: Expr<'a>,
  pub value: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub element: Expr<'a>,
  pub bag: Expr<'a>,
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
  pub expr: Expr<'a>,
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
  pub exprs: Seq<Expr<'a>>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub set: Expr<'a>,
  pub elem: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub expr: Expr<'a>,
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
  pub value: String,
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
  pub expr: Expr<'a>,
  pub start: Expr<'a>,
  pub end: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
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
  pub exprs: Seq<Expr<'a>>,
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
  pub tuple: Expr<'a>,
  pub index: Int,
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
  pub expr: Expr<'a>,
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
pub struct UnitLiteral {}

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
  pub tpe: Type<'a>,
  pub flags: Seq<Flag<'a>>,
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Type<'a> {
  ADTType(&'a ADTType<'a>),
  BVType(&'a BVType),
  BagType(&'a BagType<'a>),
  BooleanType(&'a BooleanType),
  CharType(&'a CharType),
  FunctionType(&'a FunctionType<'a>),
  IntegerType(&'a IntegerType),
  MapType(&'a MapType<'a>),
  PiType(&'a PiType<'a>),
  RealType(&'a RealType),
  RefinementType(&'a RefinementType<'a>),
  SetType(&'a SetType<'a>),
  SigmaType(&'a SigmaType<'a>),
  StringType(&'a StringType),
  TupleType(&'a TupleType<'a>),
  TypeParameter(&'a TypeParameter<'a>),
  UnitType(&'a UnitType),
  Untyped(&'a Untyped),
}

impl Factory {
  pub fn ADTType<'a>(&'a self, id: &'a Identifier, tps: Seq<Type<'a>>) -> &'a mut ADTType<'a> {
    self.bump.alloc(ADTType { id, tps })
  }

  pub fn BVType<'a>(&'a self, signed: Boolean, size: Int) -> &'a mut BVType {
    self.bump.alloc(BVType { signed, size })
  }

  pub fn BagType<'a>(&'a self, base: Type<'a>) -> &'a mut BagType<'a> {
    self.bump.alloc(BagType { base })
  }

  pub fn BooleanType<'a>(&'a self) -> &'a mut BooleanType {
    self.bump.alloc(BooleanType {})
  }

  pub fn CharType<'a>(&'a self) -> &'a mut CharType {
    self.bump.alloc(CharType {})
  }

  pub fn FunctionType<'a>(&'a self, from: Seq<Type<'a>>, to: Type<'a>) -> &'a mut FunctionType<'a> {
    self.bump.alloc(FunctionType { from, to })
  }

  pub fn IntegerType<'a>(&'a self) -> &'a mut IntegerType {
    self.bump.alloc(IntegerType {})
  }

  pub fn MapType<'a>(&'a self, from: Type<'a>, to: Type<'a>) -> &'a mut MapType<'a> {
    self.bump.alloc(MapType { from, to })
  }

  pub fn PiType<'a>(&'a self, params: Seq<&'a ValDef<'a>>, to: Type<'a>) -> &'a mut PiType<'a> {
    self.bump.alloc(PiType { params, to })
  }

  pub fn RealType<'a>(&'a self) -> &'a mut RealType {
    self.bump.alloc(RealType {})
  }

  pub fn RefinementType<'a>(
    &'a self,
    vd: &'a ValDef<'a>,
    prop: Expr<'a>,
  ) -> &'a mut RefinementType<'a> {
    self.bump.alloc(RefinementType { vd, prop })
  }

  pub fn SetType<'a>(&'a self, base: Type<'a>) -> &'a mut SetType<'a> {
    self.bump.alloc(SetType { base })
  }

  pub fn SigmaType<'a>(
    &'a self,
    params: Seq<&'a ValDef<'a>>,
    to: Type<'a>,
  ) -> &'a mut SigmaType<'a> {
    self.bump.alloc(SigmaType { params, to })
  }

  pub fn StringType<'a>(&'a self) -> &'a mut StringType {
    self.bump.alloc(StringType {})
  }

  pub fn TupleType<'a>(&'a self, bases: Seq<Type<'a>>) -> &'a mut TupleType<'a> {
    self.bump.alloc(TupleType { bases })
  }

  pub fn TypeParameter<'a>(
    &'a self,
    id: &'a Identifier,
    flags: Seq<Flag<'a>>,
  ) -> &'a mut TypeParameter<'a> {
    self.bump.alloc(TypeParameter { id, flags })
  }

  pub fn UnitType<'a>(&'a self) -> &'a mut UnitType {
    self.bump.alloc(UnitType {})
  }

  pub fn Untyped<'a>(&'a self) -> &'a mut Untyped {
    self.bump.alloc(Untyped {})
  }
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

derive_conversions_for_ast!(Type<'a>, ADTType<'a>);
derive_conversions_for_ast!(Type<'a>, BVType);
derive_conversions_for_ast!(Type<'a>, BagType<'a>);
derive_conversions_for_ast!(Type<'a>, BooleanType);
derive_conversions_for_ast!(Type<'a>, CharType);
derive_conversions_for_ast!(Type<'a>, FunctionType<'a>);
derive_conversions_for_ast!(Type<'a>, IntegerType);
derive_conversions_for_ast!(Type<'a>, MapType<'a>);
derive_conversions_for_ast!(Type<'a>, PiType<'a>);
derive_conversions_for_ast!(Type<'a>, RealType);
derive_conversions_for_ast!(Type<'a>, RefinementType<'a>);
derive_conversions_for_ast!(Type<'a>, SetType<'a>);
derive_conversions_for_ast!(Type<'a>, SigmaType<'a>);
derive_conversions_for_ast!(Type<'a>, StringType);
derive_conversions_for_ast!(Type<'a>, TupleType<'a>);
derive_conversions_for_ast!(Type<'a>, TypeParameter<'a>);
derive_conversions_for_ast!(Type<'a>, UnitType);
derive_conversions_for_ast!(Type<'a>, Untyped);

/// inox.ast.Types.ADTType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ADTType<'a> {
  pub id: &'a Identifier,
  pub tps: Seq<Type<'a>>,
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
  pub size: Int,
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
  pub base: Type<'a>,
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
pub struct BooleanType {}

impl Serializable for BooleanType {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(76))?;
    Ok(())
  }
}

/// inox.ast.Types.CharType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CharType {}

impl Serializable for CharType {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(78))?;
    Ok(())
  }
}

/// inox.ast.Types.FunctionType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FunctionType<'a> {
  pub from: Seq<Type<'a>>,
  pub to: Type<'a>,
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
pub struct IntegerType {}

impl Serializable for IntegerType {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(79))?;
    Ok(())
  }
}

/// inox.ast.Types.MapType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MapType<'a> {
  pub from: Type<'a>,
  pub to: Type<'a>,
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
  pub to: Type<'a>,
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
pub struct RealType {}

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
  pub prop: Expr<'a>,
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
  pub base: Type<'a>,
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
  pub to: Type<'a>,
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
pub struct StringType {}

impl Serializable for StringType {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(81))?;
    Ok(())
  }
}

/// inox.ast.Types.TupleType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TupleType<'a> {
  pub bases: Seq<Type<'a>>,
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
  pub flags: Seq<Flag<'a>>,
}

impl<'a> PartialEq for TypeParameter<'a> {
  fn eq(&self, other: &Self) -> bool {
    self.id == other.id
  }
}
impl<'a> Eq for TypeParameter<'a> {}
impl<'a> PartialOrd for TypeParameter<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}
impl<'a> Ord for TypeParameter<'a> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.id.cmp(&other.id)
  }
}
impl<'a> Hash for TypeParameter<'a> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.id.hash(state);
  }
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
pub struct UnitType {}

impl Serializable for UnitType {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(77))?;
    Ok(())
  }
}

/// inox.ast.Types.Untyped
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Untyped {}

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
  pub fields: Seq<&'a ValDef<'a>>,
}

impl<'a> PartialEq for ADTConstructor<'a> {
  fn eq(&self, other: &Self) -> bool {
    self.id == other.id
  }
}
impl<'a> Eq for ADTConstructor<'a> {}
impl<'a> PartialOrd for ADTConstructor<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}
impl<'a> Ord for ADTConstructor<'a> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.id.cmp(&other.id)
  }
}
impl<'a> Hash for ADTConstructor<'a> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.id.hash(state);
  }
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
  pub id: Int,
}

impl PartialEq for Identifier {
  fn eq(&self, other: &Self) -> bool {
    self.id == other.id
  }
}
impl Eq for Identifier {}
impl PartialOrd for Identifier {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}
impl Ord for Identifier {
  fn cmp(&self, other: &Self) -> Ordering {
    self.id.cmp(&other.id)
  }
}
impl Hash for Identifier {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.id.hash(state);
  }
}
