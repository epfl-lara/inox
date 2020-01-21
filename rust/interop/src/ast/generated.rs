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
  ClassDef(&'a ClassDef<'a>),
  FunDef(&'a FunDef<'a>),
  LocalClassDef(&'a LocalClassDef<'a>),
  LocalFunDef(&'a LocalFunDef<'a>),
  LocalMethodDef(&'a LocalMethodDef<'a>),
  LocalTypeDef(&'a LocalTypeDef<'a>),
  TypeDef(&'a TypeDef<'a>),
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

  pub fn ClassDef<'a>(
    &'a self,
    id: &'a Identifier,
    tparams: Seq<&'a TypeParameterDef<'a>>,
    parents: Seq<&'a ClassType<'a>>,
    fields: Seq<&'a ValDef<'a>>,
    flags: Seq<Flag<'a>>,
  ) -> &'a mut ClassDef<'a> {
    self.bump.alloc(ClassDef {
      id,
      tparams,
      parents,
      fields,
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

  pub fn LocalClassDef<'a>(
    &'a self,
    id: &'a Identifier,
    tparams: Seq<&'a TypeParameterDef<'a>>,
    parents: Seq<Type<'a>>,
    fields: Seq<&'a ValDef<'a>>,
    methods: Seq<&'a LocalMethodDef<'a>>,
    typeMembers: Seq<&'a LocalTypeDef<'a>>,
    flags: Seq<Flag<'a>>,
  ) -> &'a mut LocalClassDef<'a> {
    self.bump.alloc(LocalClassDef {
      id,
      tparams,
      parents,
      fields,
      methods,
      typeMembers,
      flags,
    })
  }

  pub fn LocalFunDef<'a>(
    &'a self,
    id: &'a Identifier,
    tparams: Seq<&'a TypeParameterDef<'a>>,
    params: Seq<&'a ValDef<'a>>,
    returnType: Type<'a>,
    fullBody: Expr<'a>,
    flags: Seq<Flag<'a>>,
  ) -> &'a mut LocalFunDef<'a> {
    self.bump.alloc(LocalFunDef {
      id,
      tparams,
      params,
      returnType,
      fullBody,
      flags,
    })
  }

  pub fn LocalMethodDef<'a>(
    &'a self,
    id: &'a Identifier,
    tparams: Seq<&'a TypeParameterDef<'a>>,
    params: Seq<&'a ValDef<'a>>,
    returnType: Type<'a>,
    fullBody: Expr<'a>,
    flags: Seq<Flag<'a>>,
  ) -> &'a mut LocalMethodDef<'a> {
    self.bump.alloc(LocalMethodDef {
      id,
      tparams,
      params,
      returnType,
      fullBody,
      flags,
    })
  }

  pub fn LocalTypeDef<'a>(
    &'a self,
    id: &'a Identifier,
    tparams: Seq<&'a TypeParameterDef<'a>>,
    rhs: Type<'a>,
    flags: Seq<Flag<'a>>,
  ) -> &'a mut LocalTypeDef<'a> {
    self.bump.alloc(LocalTypeDef {
      id,
      tparams,
      rhs,
      flags,
    })
  }

  pub fn TypeDef<'a>(
    &'a self,
    id: &'a Identifier,
    tparams: Seq<&'a TypeParameterDef<'a>>,
    rhs: Type<'a>,
    flags: Seq<Flag<'a>>,
  ) -> &'a mut TypeDef<'a> {
    self.bump.alloc(TypeDef {
      id,
      tparams,
      rhs,
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
      Definition::ClassDef(v) => v.serialize(s)?,
      Definition::FunDef(v) => v.serialize(s)?,
      Definition::LocalClassDef(v) => v.serialize(s)?,
      Definition::LocalFunDef(v) => v.serialize(s)?,
      Definition::LocalMethodDef(v) => v.serialize(s)?,
      Definition::LocalTypeDef(v) => v.serialize(s)?,
      Definition::TypeDef(v) => v.serialize(s)?,
      Definition::TypeParameterDef(v) => v.serialize(s)?,
      Definition::ValDef(v) => v.serialize(s)?,
    };
    Ok(())
  }
}

derive_conversions_for_ast!(Definition<'a>, ADTSort<'a>);
derive_conversions_for_ast!(Definition<'a>, ClassDef<'a>);
derive_conversions_for_ast!(Definition<'a>, FunDef<'a>);
derive_conversions_for_ast!(Definition<'a>, LocalClassDef<'a>);
derive_conversions_for_ast!(Definition<'a>, LocalFunDef<'a>);
derive_conversions_for_ast!(Definition<'a>, LocalMethodDef<'a>);
derive_conversions_for_ast!(Definition<'a>, LocalTypeDef<'a>);
derive_conversions_for_ast!(Definition<'a>, TypeDef<'a>);
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

/// stainless.extraction.oo.Definitions.ClassDef
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ClassDef<'a> {
  pub id: &'a Identifier,
  pub tparams: Seq<&'a TypeParameterDef<'a>>,
  pub parents: Seq<&'a ClassType<'a>>,
  pub fields: Seq<&'a ValDef<'a>>,
  pub flags: Seq<Flag<'a>>,
}

impl<'a> Serializable for ClassDef<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(222))?;
    self.id.serialize(s)?;
    self.tparams.serialize(s)?;
    self.parents.serialize(s)?;
    self.fields.serialize(s)?;
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

/// stainless.extraction.innerclasses.Definitions.LocalClassDef
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LocalClassDef<'a> {
  pub id: &'a Identifier,
  pub tparams: Seq<&'a TypeParameterDef<'a>>,
  pub parents: Seq<Type<'a>>,
  pub fields: Seq<&'a ValDef<'a>>,
  pub methods: Seq<&'a LocalMethodDef<'a>>,
  pub typeMembers: Seq<&'a LocalTypeDef<'a>>,
  pub flags: Seq<Flag<'a>>,
}

impl<'a> Serializable for LocalClassDef<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(233))?;
    self.id.serialize(s)?;
    self.tparams.serialize(s)?;
    self.parents.serialize(s)?;
    self.fields.serialize(s)?;
    self.methods.serialize(s)?;
    self.typeMembers.serialize(s)?;
    self.flags.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.innerfuns.Definitions.LocalFunDef
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LocalFunDef<'a> {
  pub id: &'a Identifier,
  pub tparams: Seq<&'a TypeParameterDef<'a>>,
  pub params: Seq<&'a ValDef<'a>>,
  pub returnType: Type<'a>,
  pub fullBody: Expr<'a>,
  pub flags: Seq<Flag<'a>>,
}

impl<'a> Serializable for LocalFunDef<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(183))?;
    self.id.serialize(s)?;
    self.tparams.serialize(s)?;
    self.params.serialize(s)?;
    self.returnType.serialize(s)?;
    self.fullBody.serialize(s)?;
    self.flags.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.innerclasses.Definitions.LocalMethodDef
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LocalMethodDef<'a> {
  pub id: &'a Identifier,
  pub tparams: Seq<&'a TypeParameterDef<'a>>,
  pub params: Seq<&'a ValDef<'a>>,
  pub returnType: Type<'a>,
  pub fullBody: Expr<'a>,
  pub flags: Seq<Flag<'a>>,
}

impl<'a> Serializable for LocalMethodDef<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(234))?;
    self.id.serialize(s)?;
    self.tparams.serialize(s)?;
    self.params.serialize(s)?;
    self.returnType.serialize(s)?;
    self.fullBody.serialize(s)?;
    self.flags.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.innerclasses.Definitions.LocalTypeDef
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LocalTypeDef<'a> {
  pub id: &'a Identifier,
  pub tparams: Seq<&'a TypeParameterDef<'a>>,
  pub rhs: Type<'a>,
  pub flags: Seq<Flag<'a>>,
}

impl<'a> Serializable for LocalTypeDef<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(246))?;
    self.id.serialize(s)?;
    self.tparams.serialize(s)?;
    self.rhs.serialize(s)?;
    self.flags.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.oo.Definitions.TypeDef
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeDef<'a> {
  pub id: &'a Identifier,
  pub tparams: Seq<&'a TypeParameterDef<'a>>,
  pub rhs: Type<'a>,
  pub flags: Seq<Flag<'a>>,
}

impl<'a> Serializable for TypeDef<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(244))?;
    self.id.serialize(s)?;
    self.tparams.serialize(s)?;
    self.rhs.serialize(s)?;
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
  Bounds(&'a Bounds<'a>),
  Derived(&'a Derived<'a>),
  Erasable(&'a Erasable),
  Extern(&'a Extern),
  Final(&'a Final),
  Ghost(&'a Ghost),
  HasADTEquality(&'a HasADTEquality<'a>),
  HasADTInvariant(&'a HasADTInvariant<'a>),
  Ignore(&'a Ignore),
  IndexedAt(&'a IndexedAt<'a>),
  Inline(&'a Inline),
  InlineOnce(&'a InlineOnce),
  IsAbstract(&'a IsAbstract),
  IsAccessor(&'a IsAccessor<'a>),
  IsCaseObject(&'a IsCaseObject),
  IsField(&'a IsField),
  IsInvariant(&'a IsInvariant),
  IsMethodOf(&'a IsMethodOf<'a>),
  IsMutable(&'a IsMutable),
  IsPure(&'a IsPure),
  IsSealed(&'a IsSealed),
  IsUnapply(&'a IsUnapply<'a>),
  IsVar(&'a IsVar),
  Law(&'a Law),
  Library(&'a Library),
  Opaque(&'a Opaque),
  PartialEval(&'a PartialEval),
  Private(&'a Private),
  Synthetic(&'a Synthetic),
  Unchecked(&'a Unchecked),
  ValueClass(&'a ValueClass),
  Variance(&'a Variance),
  Wrapping(&'a Wrapping),
}

impl Factory {
  pub fn Annotation<'a>(&'a self, name: String, args: Seq<Expr<'a>>) -> &'a mut Annotation<'a> {
    self.bump.alloc(Annotation { name, args })
  }

  pub fn Bounds<'a>(&'a self, lo: Type<'a>, hi: Type<'a>) -> &'a mut Bounds<'a> {
    self.bump.alloc(Bounds { lo, hi })
  }

  pub fn Derived<'a>(&'a self, id: &'a Identifier) -> &'a mut Derived<'a> {
    self.bump.alloc(Derived { id })
  }

  pub fn Erasable<'a>(&'a self) -> &'a mut Erasable {
    self.bump.alloc(Erasable {})
  }

  pub fn Extern<'a>(&'a self) -> &'a mut Extern {
    self.bump.alloc(Extern {})
  }

  pub fn Final<'a>(&'a self) -> &'a mut Final {
    self.bump.alloc(Final {})
  }

  pub fn Ghost<'a>(&'a self) -> &'a mut Ghost {
    self.bump.alloc(Ghost {})
  }

  pub fn HasADTEquality<'a>(&'a self, id: &'a Identifier) -> &'a mut HasADTEquality<'a> {
    self.bump.alloc(HasADTEquality { id })
  }

  pub fn HasADTInvariant<'a>(&'a self, id: &'a Identifier) -> &'a mut HasADTInvariant<'a> {
    self.bump.alloc(HasADTInvariant { id })
  }

  pub fn Ignore<'a>(&'a self) -> &'a mut Ignore {
    self.bump.alloc(Ignore {})
  }

  pub fn IndexedAt<'a>(&'a self, e: Expr<'a>) -> &'a mut IndexedAt<'a> {
    self.bump.alloc(IndexedAt { e })
  }

  pub fn Inline<'a>(&'a self) -> &'a mut Inline {
    self.bump.alloc(Inline {})
  }

  pub fn InlineOnce<'a>(&'a self) -> &'a mut InlineOnce {
    self.bump.alloc(InlineOnce {})
  }

  pub fn IsAbstract<'a>(&'a self) -> &'a mut IsAbstract {
    self.bump.alloc(IsAbstract {})
  }

  pub fn IsAccessor<'a>(&'a self, id: Option<&'a Identifier>) -> &'a mut IsAccessor<'a> {
    self.bump.alloc(IsAccessor { id })
  }

  pub fn IsCaseObject<'a>(&'a self) -> &'a mut IsCaseObject {
    self.bump.alloc(IsCaseObject {})
  }

  pub fn IsField<'a>(&'a self, isLazy: Boolean) -> &'a mut IsField {
    self.bump.alloc(IsField { isLazy })
  }

  pub fn IsInvariant<'a>(&'a self) -> &'a mut IsInvariant {
    self.bump.alloc(IsInvariant {})
  }

  pub fn IsMethodOf<'a>(&'a self, id: &'a Identifier) -> &'a mut IsMethodOf<'a> {
    self.bump.alloc(IsMethodOf { id })
  }

  pub fn IsMutable<'a>(&'a self) -> &'a mut IsMutable {
    self.bump.alloc(IsMutable {})
  }

  pub fn IsPure<'a>(&'a self) -> &'a mut IsPure {
    self.bump.alloc(IsPure {})
  }

  pub fn IsSealed<'a>(&'a self) -> &'a mut IsSealed {
    self.bump.alloc(IsSealed {})
  }

  pub fn IsUnapply<'a>(
    &'a self,
    isEmpty: &'a Identifier,
    get: &'a Identifier,
  ) -> &'a mut IsUnapply<'a> {
    self.bump.alloc(IsUnapply { isEmpty, get })
  }

  pub fn IsVar<'a>(&'a self) -> &'a mut IsVar {
    self.bump.alloc(IsVar {})
  }

  pub fn Law<'a>(&'a self) -> &'a mut Law {
    self.bump.alloc(Law {})
  }

  pub fn Library<'a>(&'a self) -> &'a mut Library {
    self.bump.alloc(Library {})
  }

  pub fn Opaque<'a>(&'a self) -> &'a mut Opaque {
    self.bump.alloc(Opaque {})
  }

  pub fn PartialEval<'a>(&'a self) -> &'a mut PartialEval {
    self.bump.alloc(PartialEval {})
  }

  pub fn Private<'a>(&'a self) -> &'a mut Private {
    self.bump.alloc(Private {})
  }

  pub fn Synthetic<'a>(&'a self) -> &'a mut Synthetic {
    self.bump.alloc(Synthetic {})
  }

  pub fn Unchecked<'a>(&'a self) -> &'a mut Unchecked {
    self.bump.alloc(Unchecked {})
  }

  pub fn ValueClass<'a>(&'a self) -> &'a mut ValueClass {
    self.bump.alloc(ValueClass {})
  }

  pub fn Variance<'a>(&'a self, variance: Boolean) -> &'a mut Variance {
    self.bump.alloc(Variance { variance })
  }

  pub fn Wrapping<'a>(&'a self) -> &'a mut Wrapping {
    self.bump.alloc(Wrapping {})
  }
}

impl<'a> Serializable for Flag<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    match self {
      Flag::Annotation(v) => v.serialize(s)?,
      Flag::Bounds(v) => v.serialize(s)?,
      Flag::Derived(v) => v.serialize(s)?,
      Flag::Erasable(v) => v.serialize(s)?,
      Flag::Extern(v) => v.serialize(s)?,
      Flag::Final(v) => v.serialize(s)?,
      Flag::Ghost(v) => v.serialize(s)?,
      Flag::HasADTEquality(v) => v.serialize(s)?,
      Flag::HasADTInvariant(v) => v.serialize(s)?,
      Flag::Ignore(v) => v.serialize(s)?,
      Flag::IndexedAt(v) => v.serialize(s)?,
      Flag::Inline(v) => v.serialize(s)?,
      Flag::InlineOnce(v) => v.serialize(s)?,
      Flag::IsAbstract(v) => v.serialize(s)?,
      Flag::IsAccessor(v) => v.serialize(s)?,
      Flag::IsCaseObject(v) => v.serialize(s)?,
      Flag::IsField(v) => v.serialize(s)?,
      Flag::IsInvariant(v) => v.serialize(s)?,
      Flag::IsMethodOf(v) => v.serialize(s)?,
      Flag::IsMutable(v) => v.serialize(s)?,
      Flag::IsPure(v) => v.serialize(s)?,
      Flag::IsSealed(v) => v.serialize(s)?,
      Flag::IsUnapply(v) => v.serialize(s)?,
      Flag::IsVar(v) => v.serialize(s)?,
      Flag::Law(v) => v.serialize(s)?,
      Flag::Library(v) => v.serialize(s)?,
      Flag::Opaque(v) => v.serialize(s)?,
      Flag::PartialEval(v) => v.serialize(s)?,
      Flag::Private(v) => v.serialize(s)?,
      Flag::Synthetic(v) => v.serialize(s)?,
      Flag::Unchecked(v) => v.serialize(s)?,
      Flag::ValueClass(v) => v.serialize(s)?,
      Flag::Variance(v) => v.serialize(s)?,
      Flag::Wrapping(v) => v.serialize(s)?,
    };
    Ok(())
  }
}

derive_conversions_for_ast!(Flag<'a>, Annotation<'a>);
derive_conversions_for_ast!(Flag<'a>, Bounds<'a>);
derive_conversions_for_ast!(Flag<'a>, Derived<'a>);
derive_conversions_for_ast!(Flag<'a>, Erasable);
derive_conversions_for_ast!(Flag<'a>, Extern);
derive_conversions_for_ast!(Flag<'a>, Final);
derive_conversions_for_ast!(Flag<'a>, Ghost);
derive_conversions_for_ast!(Flag<'a>, HasADTEquality<'a>);
derive_conversions_for_ast!(Flag<'a>, HasADTInvariant<'a>);
derive_conversions_for_ast!(Flag<'a>, Ignore);
derive_conversions_for_ast!(Flag<'a>, IndexedAt<'a>);
derive_conversions_for_ast!(Flag<'a>, Inline);
derive_conversions_for_ast!(Flag<'a>, InlineOnce);
derive_conversions_for_ast!(Flag<'a>, IsAbstract);
derive_conversions_for_ast!(Flag<'a>, IsAccessor<'a>);
derive_conversions_for_ast!(Flag<'a>, IsCaseObject);
derive_conversions_for_ast!(Flag<'a>, IsField);
derive_conversions_for_ast!(Flag<'a>, IsInvariant);
derive_conversions_for_ast!(Flag<'a>, IsMethodOf<'a>);
derive_conversions_for_ast!(Flag<'a>, IsMutable);
derive_conversions_for_ast!(Flag<'a>, IsPure);
derive_conversions_for_ast!(Flag<'a>, IsSealed);
derive_conversions_for_ast!(Flag<'a>, IsUnapply<'a>);
derive_conversions_for_ast!(Flag<'a>, IsVar);
derive_conversions_for_ast!(Flag<'a>, Law);
derive_conversions_for_ast!(Flag<'a>, Library);
derive_conversions_for_ast!(Flag<'a>, Opaque);
derive_conversions_for_ast!(Flag<'a>, PartialEval);
derive_conversions_for_ast!(Flag<'a>, Private);
derive_conversions_for_ast!(Flag<'a>, Synthetic);
derive_conversions_for_ast!(Flag<'a>, Unchecked);
derive_conversions_for_ast!(Flag<'a>, ValueClass);
derive_conversions_for_ast!(Flag<'a>, Variance);
derive_conversions_for_ast!(Flag<'a>, Wrapping);

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

/// stainless.extraction.oo.Definitions.Bounds
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Bounds<'a> {
  pub lo: Type<'a>,
  pub hi: Type<'a>,
}

impl<'a> Serializable for Bounds<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(226))?;
    self.lo.serialize(s)?;
    self.hi.serialize(s)?;
    Ok(())
  }
}

/// stainless.ast.Definitions.Derived
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Derived<'a> {
  pub id: &'a Identifier,
}

impl<'a> Serializable for Derived<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(142))?;
    self.id.serialize(s)?;
    Ok(())
  }
}

/// stainless.ast.Definitions.Erasable
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Erasable {}

impl Serializable for Erasable {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(155))?;
    Ok(())
  }
}

/// stainless.ast.Definitions.Extern
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Extern {}

impl Serializable for Extern {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(139))?;
    Ok(())
  }
}

/// stainless.ast.Definitions.Final
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Final {}

impl Serializable for Final {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(149))?;
    Ok(())
  }
}

/// stainless.ast.Definitions.Ghost
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Ghost {}

impl Serializable for Ghost {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(147))?;
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

/// stainless.extraction.xlang.Trees.Ignore
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Ignore {}

impl Serializable for Ignore {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(218))?;
    Ok(())
  }
}

/// stainless.ast.Definitions.IndexedAt
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IndexedAt<'a> {
  pub e: Expr<'a>,
}

impl<'a> Serializable for IndexedAt<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(156))?;
    self.e.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.inlining.Trees.Inline
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Inline {}

impl Serializable for Inline {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(181))?;
    Ok(())
  }
}

/// stainless.extraction.inlining.Trees.InlineOnce
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct InlineOnce {}

impl Serializable for InlineOnce {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(228))?;
    Ok(())
  }
}

/// stainless.extraction.oo.Definitions.IsAbstract
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IsAbstract {}

impl Serializable for IsAbstract {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(224))?;
    Ok(())
  }
}

/// stainless.extraction.methods.Trees.IsAccessor
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IsAccessor<'a> {
  pub id: Option<&'a Identifier>,
}

impl<'a> Serializable for IsAccessor<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(231))?;
    self.id.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.oo.Definitions.IsCaseObject
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IsCaseObject {}

impl Serializable for IsCaseObject {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(229))?;
    Ok(())
  }
}

/// stainless.ast.Definitions.IsField
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IsField {
  pub isLazy: Boolean,
}

impl Serializable for IsField {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(143))?;
    self.isLazy.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.oo.Definitions.IsInvariant
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IsInvariant {}

impl Serializable for IsInvariant {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(223))?;
    Ok(())
  }
}

/// stainless.extraction.methods.Trees.IsMethodOf
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IsMethodOf<'a> {
  pub id: &'a Identifier,
}

impl<'a> Serializable for IsMethodOf<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(217))?;
    self.id.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.imperative.Trees.IsMutable
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IsMutable {}

impl Serializable for IsMutable {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(199))?;
    Ok(())
  }
}

/// stainless.extraction.imperative.Trees.IsPure
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IsPure {}

impl Serializable for IsPure {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(230))?;
    Ok(())
  }
}

/// stainless.extraction.oo.Definitions.IsSealed
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IsSealed {}

impl Serializable for IsSealed {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(225))?;
    Ok(())
  }
}

/// stainless.ast.Definitions.IsUnapply
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IsUnapply<'a> {
  pub isEmpty: &'a Identifier,
  pub get: &'a Identifier,
}

impl<'a> Serializable for IsUnapply<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(144))?;
    self.isEmpty.serialize(s)?;
    self.get.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.imperative.Trees.IsVar
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IsVar {}

impl Serializable for IsVar {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(198))?;
    Ok(())
  }
}

/// stainless.ast.Definitions.Law
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Law {}

impl Serializable for Law {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(150))?;
    Ok(())
  }
}

/// stainless.ast.Definitions.Library
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Library {}

impl Serializable for Library {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(158))?;
    Ok(())
  }
}

/// stainless.ast.Definitions.Opaque
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Opaque {}

impl Serializable for Opaque {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(140))?;
    Ok(())
  }
}

/// stainless.ast.Definitions.PartialEval
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PartialEval {}

impl Serializable for PartialEval {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(146))?;
    Ok(())
  }
}

/// stainless.ast.Definitions.Private
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Private {}

impl Serializable for Private {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(148))?;
    Ok(())
  }
}

/// stainless.ast.Definitions.Synthetic
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Synthetic {}

impl Serializable for Synthetic {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(182))?;
    Ok(())
  }
}

/// stainless.ast.Definitions.Unchecked
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Unchecked {}

impl Serializable for Unchecked {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(141))?;
    Ok(())
  }
}

/// stainless.extraction.methods.Trees.ValueClass
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ValueClass {}

impl Serializable for ValueClass {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(243))?;
    Ok(())
  }
}

/// stainless.extraction.oo.Definitions.Variance
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Variance {
  pub variance: Boolean,
}

impl Serializable for Variance {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(227))?;
    self.variance.serialize(s)?;
    Ok(())
  }
}

/// stainless.ast.Definitions.Wrapping
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Wrapping {}

impl Serializable for Wrapping {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(159))?;
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
  Annotated(&'a Annotated<'a>),
  Application(&'a Application<'a>),
  ApplyLetRec(&'a ApplyLetRec<'a>),
  ArrayLength(&'a ArrayLength<'a>),
  ArraySelect(&'a ArraySelect<'a>),
  ArrayUpdate(&'a ArrayUpdate<'a>),
  ArrayUpdated(&'a ArrayUpdated<'a>),
  AsInstanceOf(&'a AsInstanceOf<'a>),
  Assert(&'a Assert<'a>),
  Assignment(&'a Assignment<'a>),
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
  Block(&'a Block<'a>),
  BoolBitwiseAnd(&'a BoolBitwiseAnd<'a>),
  BoolBitwiseOr(&'a BoolBitwiseOr<'a>),
  BoolBitwiseXor(&'a BoolBitwiseXor<'a>),
  BooleanLiteral(&'a BooleanLiteral),
  CharLiteral(&'a CharLiteral),
  Choose(&'a Choose<'a>),
  ClassConstructor(&'a ClassConstructor<'a>),
  ClassSelector(&'a ClassSelector<'a>),
  Decreases(&'a Decreases<'a>),
  Division(&'a Division<'a>),
  ElementOfSet(&'a ElementOfSet<'a>),
  Ensuring(&'a Ensuring<'a>),
  Equals(&'a Equals<'a>),
  Error(&'a Error<'a>),
  FieldAssignment(&'a FieldAssignment<'a>),
  FiniteArray(&'a FiniteArray<'a>),
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
  IsInstanceOf(&'a IsInstanceOf<'a>),
  Lambda(&'a Lambda<'a>),
  LargeArray(&'a LargeArray<'a>),
  LessEquals(&'a LessEquals<'a>),
  LessThan(&'a LessThan<'a>),
  Let(&'a Let<'a>),
  LetClass(&'a LetClass<'a>),
  LetRec(&'a LetRec<'a>),
  LetVar(&'a LetVar<'a>),
  LocalClassConstructor(&'a LocalClassConstructor<'a>),
  LocalClassSelector(&'a LocalClassSelector<'a>),
  LocalMethodInvocation(&'a LocalMethodInvocation<'a>),
  LocalThis(&'a LocalThis<'a>),
  MapApply(&'a MapApply<'a>),
  MapUpdated(&'a MapUpdated<'a>),
  MatchExpr(&'a MatchExpr<'a>),
  MethodInvocation(&'a MethodInvocation<'a>),
  Minus(&'a Minus<'a>),
  Modulo(&'a Modulo<'a>),
  MultiplicityInBag(&'a MultiplicityInBag<'a>),
  MutableMapApply(&'a MutableMapApply<'a>),
  MutableMapDuplicate(&'a MutableMapDuplicate<'a>),
  MutableMapUpdate(&'a MutableMapUpdate<'a>),
  MutableMapUpdated(&'a MutableMapUpdated<'a>),
  MutableMapWithDefault(&'a MutableMapWithDefault<'a>),
  NoTree(&'a NoTree<'a>),
  Not(&'a Not<'a>),
  Old(&'a Old<'a>),
  Or(&'a Or<'a>),
  Passes(&'a Passes<'a>),
  Plus(&'a Plus<'a>),
  Remainder(&'a Remainder<'a>),
  Require(&'a Require<'a>),
  SetAdd(&'a SetAdd<'a>),
  SetDifference(&'a SetDifference<'a>),
  SetIntersection(&'a SetIntersection<'a>),
  SetUnion(&'a SetUnion<'a>),
  SizedADT(&'a SizedADT<'a>),
  Snapshot(&'a Snapshot<'a>),
  StringConcat(&'a StringConcat<'a>),
  StringLength(&'a StringLength<'a>),
  StringLiteral(&'a StringLiteral),
  SubString(&'a SubString<'a>),
  SubsetOf(&'a SubsetOf<'a>),
  Super(&'a Super<'a>),
  This(&'a This<'a>),
  Throw(&'a Throw<'a>),
  Throwing(&'a Throwing<'a>),
  Times(&'a Times<'a>),
  Try(&'a Try<'a>),
  Tuple(&'a Tuple<'a>),
  TupleSelect(&'a TupleSelect<'a>),
  UMinus(&'a UMinus<'a>),
  UnitLiteral(&'a UnitLiteral),
  Variable(&'a Variable<'a>),
  While(&'a While<'a>),
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

  pub fn Annotated<'a>(&'a self, body: Expr<'a>, flags: Seq<Flag<'a>>) -> &'a mut Annotated<'a> {
    self.bump.alloc(Annotated { body, flags })
  }

  pub fn Application<'a>(
    &'a self,
    callee: Expr<'a>,
    args: Seq<Expr<'a>>,
  ) -> &'a mut Application<'a> {
    self.bump.alloc(Application { callee, args })
  }

  pub fn ApplyLetRec<'a>(
    &'a self,
    id: &'a Identifier,
    tparams: Seq<&'a TypeParameter<'a>>,
    tpe: &'a FunctionType<'a>,
    tps: Seq<Type<'a>>,
    args: Seq<Expr<'a>>,
  ) -> &'a mut ApplyLetRec<'a> {
    self.bump.alloc(ApplyLetRec {
      id,
      tparams,
      tpe,
      tps,
      args,
    })
  }

  pub fn ArrayLength<'a>(&'a self, array: Expr<'a>) -> &'a mut ArrayLength<'a> {
    self.bump.alloc(ArrayLength { array })
  }

  pub fn ArraySelect<'a>(&'a self, array: Expr<'a>, index: Expr<'a>) -> &'a mut ArraySelect<'a> {
    self.bump.alloc(ArraySelect { array, index })
  }

  pub fn ArrayUpdate<'a>(
    &'a self,
    array: Expr<'a>,
    index: Expr<'a>,
    value: Expr<'a>,
  ) -> &'a mut ArrayUpdate<'a> {
    self.bump.alloc(ArrayUpdate {
      array,
      index,
      value,
    })
  }

  pub fn ArrayUpdated<'a>(
    &'a self,
    array: Expr<'a>,
    index: Expr<'a>,
    value: Expr<'a>,
  ) -> &'a mut ArrayUpdated<'a> {
    self.bump.alloc(ArrayUpdated {
      array,
      index,
      value,
    })
  }

  pub fn AsInstanceOf<'a>(&'a self, expr: Expr<'a>, tpe: Type<'a>) -> &'a mut AsInstanceOf<'a> {
    self.bump.alloc(AsInstanceOf { expr, tpe })
  }

  pub fn Assert<'a>(
    &'a self,
    pred: Expr<'a>,
    error: Option<String>,
    body: Expr<'a>,
  ) -> &'a mut Assert<'a> {
    self.bump.alloc(Assert { pred, error, body })
  }

  pub fn Assignment<'a>(&'a self, v: &'a Variable<'a>, value: Expr<'a>) -> &'a mut Assignment<'a> {
    self.bump.alloc(Assignment { v, value })
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

  pub fn Block<'a>(&'a self, exprs: Seq<Expr<'a>>, last: Expr<'a>) -> &'a mut Block<'a> {
    self.bump.alloc(Block { exprs, last })
  }

  pub fn BoolBitwiseAnd<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut BoolBitwiseAnd<'a> {
    self.bump.alloc(BoolBitwiseAnd { lhs, rhs })
  }

  pub fn BoolBitwiseOr<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut BoolBitwiseOr<'a> {
    self.bump.alloc(BoolBitwiseOr { lhs, rhs })
  }

  pub fn BoolBitwiseXor<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut BoolBitwiseXor<'a> {
    self.bump.alloc(BoolBitwiseXor { lhs, rhs })
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

  pub fn ClassConstructor<'a>(
    &'a self,
    ct: &'a ClassType<'a>,
    args: Seq<Expr<'a>>,
  ) -> &'a mut ClassConstructor<'a> {
    self.bump.alloc(ClassConstructor { ct, args })
  }

  pub fn ClassSelector<'a>(
    &'a self,
    expr: Expr<'a>,
    selector: &'a Identifier,
  ) -> &'a mut ClassSelector<'a> {
    self.bump.alloc(ClassSelector { expr, selector })
  }

  pub fn Decreases<'a>(&'a self, measure: Expr<'a>, body: Expr<'a>) -> &'a mut Decreases<'a> {
    self.bump.alloc(Decreases { measure, body })
  }

  pub fn Division<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut Division<'a> {
    self.bump.alloc(Division { lhs, rhs })
  }

  pub fn ElementOfSet<'a>(&'a self, element: Expr<'a>, set: Expr<'a>) -> &'a mut ElementOfSet<'a> {
    self.bump.alloc(ElementOfSet { element, set })
  }

  pub fn Ensuring<'a>(&'a self, body: Expr<'a>, pred: &'a Lambda<'a>) -> &'a mut Ensuring<'a> {
    self.bump.alloc(Ensuring { body, pred })
  }

  pub fn Equals<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut Equals<'a> {
    self.bump.alloc(Equals { lhs, rhs })
  }

  pub fn Error<'a>(&'a self, tpe: Type<'a>, description: String) -> &'a mut Error<'a> {
    self.bump.alloc(Error { tpe, description })
  }

  pub fn FieldAssignment<'a>(
    &'a self,
    obj: Expr<'a>,
    selector: &'a Identifier,
    value: Expr<'a>,
  ) -> &'a mut FieldAssignment<'a> {
    self.bump.alloc(FieldAssignment {
      obj,
      selector,
      value,
    })
  }

  pub fn FiniteArray<'a>(
    &'a self,
    elems: Seq<Expr<'a>>,
    base: Type<'a>,
  ) -> &'a mut FiniteArray<'a> {
    self.bump.alloc(FiniteArray { elems, base })
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

  pub fn IsInstanceOf<'a>(&'a self, expr: Expr<'a>, tpe: Type<'a>) -> &'a mut IsInstanceOf<'a> {
    self.bump.alloc(IsInstanceOf { expr, tpe })
  }

  pub fn Lambda<'a>(&'a self, params: Seq<&'a ValDef<'a>>, body: Expr<'a>) -> &'a mut Lambda<'a> {
    self.bump.alloc(Lambda { params, body })
  }

  pub fn LargeArray<'a>(
    &'a self,
    elems: Map<Int, Expr<'a>>,
    default: Expr<'a>,
    size: Expr<'a>,
    base: Type<'a>,
  ) -> &'a mut LargeArray<'a> {
    self.bump.alloc(LargeArray {
      elems,
      default,
      size,
      base,
    })
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

  pub fn LetClass<'a>(
    &'a self,
    classes: Seq<&'a LocalClassDef<'a>>,
    body: Expr<'a>,
  ) -> &'a mut LetClass<'a> {
    self.bump.alloc(LetClass { classes, body })
  }

  pub fn LetRec<'a>(&'a self, fds: Seq<&'a LocalFunDef<'a>>, body: Expr<'a>) -> &'a mut LetRec<'a> {
    self.bump.alloc(LetRec { fds, body })
  }

  pub fn LetVar<'a>(
    &'a self,
    vd: &'a ValDef<'a>,
    value: Expr<'a>,
    body: Expr<'a>,
  ) -> &'a mut LetVar<'a> {
    self.bump.alloc(LetVar { vd, value, body })
  }

  pub fn LocalClassConstructor<'a>(
    &'a self,
    lct: &'a LocalClassType<'a>,
    args: Seq<Expr<'a>>,
  ) -> &'a mut LocalClassConstructor<'a> {
    self.bump.alloc(LocalClassConstructor { lct, args })
  }

  pub fn LocalClassSelector<'a>(
    &'a self,
    expr: Expr<'a>,
    selector: &'a Identifier,
    tpe: Type<'a>,
  ) -> &'a mut LocalClassSelector<'a> {
    self.bump.alloc(LocalClassSelector {
      expr,
      selector,
      tpe,
    })
  }

  pub fn LocalMethodInvocation<'a>(
    &'a self,
    receiver: Expr<'a>,
    method: &'a Variable<'a>,
    tparams: Seq<&'a TypeParameter<'a>>,
    tps: Seq<Type<'a>>,
    args: Seq<Expr<'a>>,
  ) -> &'a mut LocalMethodInvocation<'a> {
    self.bump.alloc(LocalMethodInvocation {
      receiver,
      method,
      tparams,
      tps,
      args,
    })
  }

  pub fn LocalThis<'a>(&'a self, lct: &'a LocalClassType<'a>) -> &'a mut LocalThis<'a> {
    self.bump.alloc(LocalThis { lct })
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

  pub fn MatchExpr<'a>(
    &'a self,
    scrutinee: Expr<'a>,
    cases: Seq<&'a MatchCase<'a>>,
  ) -> &'a mut MatchExpr<'a> {
    self.bump.alloc(MatchExpr { scrutinee, cases })
  }

  pub fn MethodInvocation<'a>(
    &'a self,
    receiver: Expr<'a>,
    id: &'a Identifier,
    tps: Seq<Type<'a>>,
    args: Seq<Expr<'a>>,
  ) -> &'a mut MethodInvocation<'a> {
    self.bump.alloc(MethodInvocation {
      receiver,
      id,
      tps,
      args,
    })
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

  pub fn MutableMapApply<'a>(
    &'a self,
    map: Expr<'a>,
    key: Expr<'a>,
  ) -> &'a mut MutableMapApply<'a> {
    self.bump.alloc(MutableMapApply { map, key })
  }

  pub fn MutableMapDuplicate<'a>(&'a self, map: Expr<'a>) -> &'a mut MutableMapDuplicate<'a> {
    self.bump.alloc(MutableMapDuplicate { map })
  }

  pub fn MutableMapUpdate<'a>(
    &'a self,
    map: Expr<'a>,
    key: Expr<'a>,
    value: Expr<'a>,
  ) -> &'a mut MutableMapUpdate<'a> {
    self.bump.alloc(MutableMapUpdate { map, key, value })
  }

  pub fn MutableMapUpdated<'a>(
    &'a self,
    map: Expr<'a>,
    key: Expr<'a>,
    value: Expr<'a>,
  ) -> &'a mut MutableMapUpdated<'a> {
    self.bump.alloc(MutableMapUpdated { map, key, value })
  }

  pub fn MutableMapWithDefault<'a>(
    &'a self,
    from: Type<'a>,
    to: Type<'a>,
    default: Expr<'a>,
  ) -> &'a mut MutableMapWithDefault<'a> {
    self.bump.alloc(MutableMapWithDefault { from, to, default })
  }

  pub fn NoTree<'a>(&'a self, tpe: Type<'a>) -> &'a mut NoTree<'a> {
    self.bump.alloc(NoTree { tpe })
  }

  pub fn Not<'a>(&'a self, expr: Expr<'a>) -> &'a mut Not<'a> {
    self.bump.alloc(Not { expr })
  }

  pub fn Old<'a>(&'a self, e: Expr<'a>) -> &'a mut Old<'a> {
    self.bump.alloc(Old { e })
  }

  pub fn Or<'a>(&'a self, exprs: Seq<Expr<'a>>) -> &'a mut Or<'a> {
    self.bump.alloc(Or { exprs })
  }

  pub fn Passes<'a>(
    &'a self,
    in_: Expr<'a>,
    out: Expr<'a>,
    cases: Seq<&'a MatchCase<'a>>,
  ) -> &'a mut Passes<'a> {
    self.bump.alloc(Passes { in_, out, cases })
  }

  pub fn Plus<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut Plus<'a> {
    self.bump.alloc(Plus { lhs, rhs })
  }

  pub fn Remainder<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut Remainder<'a> {
    self.bump.alloc(Remainder { lhs, rhs })
  }

  pub fn Require<'a>(&'a self, pred: Expr<'a>, body: Expr<'a>) -> &'a mut Require<'a> {
    self.bump.alloc(Require { pred, body })
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

  pub fn SizedADT<'a>(
    &'a self,
    id: &'a Identifier,
    tps: Seq<Type<'a>>,
    args: Seq<Expr<'a>>,
    size: Expr<'a>,
  ) -> &'a mut SizedADT<'a> {
    self.bump.alloc(SizedADT {
      id,
      tps,
      args,
      size,
    })
  }

  pub fn Snapshot<'a>(&'a self, e: Expr<'a>) -> &'a mut Snapshot<'a> {
    self.bump.alloc(Snapshot { e })
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

  pub fn Super<'a>(&'a self, ct: &'a ClassType<'a>) -> &'a mut Super<'a> {
    self.bump.alloc(Super { ct })
  }

  pub fn This<'a>(&'a self, ct: &'a ClassType<'a>) -> &'a mut This<'a> {
    self.bump.alloc(This { ct })
  }

  pub fn Throw<'a>(&'a self, ex: Expr<'a>) -> &'a mut Throw<'a> {
    self.bump.alloc(Throw { ex })
  }

  pub fn Throwing<'a>(&'a self, body: Expr<'a>, pred: &'a Lambda<'a>) -> &'a mut Throwing<'a> {
    self.bump.alloc(Throwing { body, pred })
  }

  pub fn Times<'a>(&'a self, lhs: Expr<'a>, rhs: Expr<'a>) -> &'a mut Times<'a> {
    self.bump.alloc(Times { lhs, rhs })
  }

  pub fn Try<'a>(
    &'a self,
    body: Expr<'a>,
    cases: Seq<&'a MatchCase<'a>>,
    finallizer: Option<Expr<'a>>,
  ) -> &'a mut Try<'a> {
    self.bump.alloc(Try {
      body,
      cases,
      finallizer,
    })
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

  pub fn While<'a>(
    &'a self,
    cond: Expr<'a>,
    body: Expr<'a>,
    pred: Option<Expr<'a>>,
  ) -> &'a mut While<'a> {
    self.bump.alloc(While { cond, body, pred })
  }
}

impl<'a> Serializable for Expr<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    match self {
      Expr::ADT(v) => v.serialize(s)?,
      Expr::ADTSelector(v) => v.serialize(s)?,
      Expr::And(v) => v.serialize(s)?,
      Expr::Annotated(v) => v.serialize(s)?,
      Expr::Application(v) => v.serialize(s)?,
      Expr::ApplyLetRec(v) => v.serialize(s)?,
      Expr::ArrayLength(v) => v.serialize(s)?,
      Expr::ArraySelect(v) => v.serialize(s)?,
      Expr::ArrayUpdate(v) => v.serialize(s)?,
      Expr::ArrayUpdated(v) => v.serialize(s)?,
      Expr::AsInstanceOf(v) => v.serialize(s)?,
      Expr::Assert(v) => v.serialize(s)?,
      Expr::Assignment(v) => v.serialize(s)?,
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
      Expr::Block(v) => v.serialize(s)?,
      Expr::BoolBitwiseAnd(v) => v.serialize(s)?,
      Expr::BoolBitwiseOr(v) => v.serialize(s)?,
      Expr::BoolBitwiseXor(v) => v.serialize(s)?,
      Expr::BooleanLiteral(v) => v.serialize(s)?,
      Expr::CharLiteral(v) => v.serialize(s)?,
      Expr::Choose(v) => v.serialize(s)?,
      Expr::ClassConstructor(v) => v.serialize(s)?,
      Expr::ClassSelector(v) => v.serialize(s)?,
      Expr::Decreases(v) => v.serialize(s)?,
      Expr::Division(v) => v.serialize(s)?,
      Expr::ElementOfSet(v) => v.serialize(s)?,
      Expr::Ensuring(v) => v.serialize(s)?,
      Expr::Equals(v) => v.serialize(s)?,
      Expr::Error(v) => v.serialize(s)?,
      Expr::FieldAssignment(v) => v.serialize(s)?,
      Expr::FiniteArray(v) => v.serialize(s)?,
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
      Expr::IsInstanceOf(v) => v.serialize(s)?,
      Expr::Lambda(v) => v.serialize(s)?,
      Expr::LargeArray(v) => v.serialize(s)?,
      Expr::LessEquals(v) => v.serialize(s)?,
      Expr::LessThan(v) => v.serialize(s)?,
      Expr::Let(v) => v.serialize(s)?,
      Expr::LetClass(v) => v.serialize(s)?,
      Expr::LetRec(v) => v.serialize(s)?,
      Expr::LetVar(v) => v.serialize(s)?,
      Expr::LocalClassConstructor(v) => v.serialize(s)?,
      Expr::LocalClassSelector(v) => v.serialize(s)?,
      Expr::LocalMethodInvocation(v) => v.serialize(s)?,
      Expr::LocalThis(v) => v.serialize(s)?,
      Expr::MapApply(v) => v.serialize(s)?,
      Expr::MapUpdated(v) => v.serialize(s)?,
      Expr::MatchExpr(v) => v.serialize(s)?,
      Expr::MethodInvocation(v) => v.serialize(s)?,
      Expr::Minus(v) => v.serialize(s)?,
      Expr::Modulo(v) => v.serialize(s)?,
      Expr::MultiplicityInBag(v) => v.serialize(s)?,
      Expr::MutableMapApply(v) => v.serialize(s)?,
      Expr::MutableMapDuplicate(v) => v.serialize(s)?,
      Expr::MutableMapUpdate(v) => v.serialize(s)?,
      Expr::MutableMapUpdated(v) => v.serialize(s)?,
      Expr::MutableMapWithDefault(v) => v.serialize(s)?,
      Expr::NoTree(v) => v.serialize(s)?,
      Expr::Not(v) => v.serialize(s)?,
      Expr::Old(v) => v.serialize(s)?,
      Expr::Or(v) => v.serialize(s)?,
      Expr::Passes(v) => v.serialize(s)?,
      Expr::Plus(v) => v.serialize(s)?,
      Expr::Remainder(v) => v.serialize(s)?,
      Expr::Require(v) => v.serialize(s)?,
      Expr::SetAdd(v) => v.serialize(s)?,
      Expr::SetDifference(v) => v.serialize(s)?,
      Expr::SetIntersection(v) => v.serialize(s)?,
      Expr::SetUnion(v) => v.serialize(s)?,
      Expr::SizedADT(v) => v.serialize(s)?,
      Expr::Snapshot(v) => v.serialize(s)?,
      Expr::StringConcat(v) => v.serialize(s)?,
      Expr::StringLength(v) => v.serialize(s)?,
      Expr::StringLiteral(v) => v.serialize(s)?,
      Expr::SubString(v) => v.serialize(s)?,
      Expr::SubsetOf(v) => v.serialize(s)?,
      Expr::Super(v) => v.serialize(s)?,
      Expr::This(v) => v.serialize(s)?,
      Expr::Throw(v) => v.serialize(s)?,
      Expr::Throwing(v) => v.serialize(s)?,
      Expr::Times(v) => v.serialize(s)?,
      Expr::Try(v) => v.serialize(s)?,
      Expr::Tuple(v) => v.serialize(s)?,
      Expr::TupleSelect(v) => v.serialize(s)?,
      Expr::UMinus(v) => v.serialize(s)?,
      Expr::UnitLiteral(v) => v.serialize(s)?,
      Expr::Variable(v) => v.serialize(s)?,
      Expr::While(v) => v.serialize(s)?,
    };
    Ok(())
  }
}

derive_conversions_for_ast!(Expr<'a>, ADT<'a>);
derive_conversions_for_ast!(Expr<'a>, ADTSelector<'a>);
derive_conversions_for_ast!(Expr<'a>, And<'a>);
derive_conversions_for_ast!(Expr<'a>, Annotated<'a>);
derive_conversions_for_ast!(Expr<'a>, Application<'a>);
derive_conversions_for_ast!(Expr<'a>, ApplyLetRec<'a>);
derive_conversions_for_ast!(Expr<'a>, ArrayLength<'a>);
derive_conversions_for_ast!(Expr<'a>, ArraySelect<'a>);
derive_conversions_for_ast!(Expr<'a>, ArrayUpdate<'a>);
derive_conversions_for_ast!(Expr<'a>, ArrayUpdated<'a>);
derive_conversions_for_ast!(Expr<'a>, AsInstanceOf<'a>);
derive_conversions_for_ast!(Expr<'a>, Assert<'a>);
derive_conversions_for_ast!(Expr<'a>, Assignment<'a>);
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
derive_conversions_for_ast!(Expr<'a>, Block<'a>);
derive_conversions_for_ast!(Expr<'a>, BoolBitwiseAnd<'a>);
derive_conversions_for_ast!(Expr<'a>, BoolBitwiseOr<'a>);
derive_conversions_for_ast!(Expr<'a>, BoolBitwiseXor<'a>);
derive_conversions_for_ast!(Expr<'a>, BooleanLiteral);
derive_conversions_for_ast!(Expr<'a>, CharLiteral);
derive_conversions_for_ast!(Expr<'a>, Choose<'a>);
derive_conversions_for_ast!(Expr<'a>, ClassConstructor<'a>);
derive_conversions_for_ast!(Expr<'a>, ClassSelector<'a>);
derive_conversions_for_ast!(Expr<'a>, Decreases<'a>);
derive_conversions_for_ast!(Expr<'a>, Division<'a>);
derive_conversions_for_ast!(Expr<'a>, ElementOfSet<'a>);
derive_conversions_for_ast!(Expr<'a>, Ensuring<'a>);
derive_conversions_for_ast!(Expr<'a>, Equals<'a>);
derive_conversions_for_ast!(Expr<'a>, Error<'a>);
derive_conversions_for_ast!(Expr<'a>, FieldAssignment<'a>);
derive_conversions_for_ast!(Expr<'a>, FiniteArray<'a>);
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
derive_conversions_for_ast!(Expr<'a>, IsInstanceOf<'a>);
derive_conversions_for_ast!(Expr<'a>, Lambda<'a>);
derive_conversions_for_ast!(Expr<'a>, LargeArray<'a>);
derive_conversions_for_ast!(Expr<'a>, LessEquals<'a>);
derive_conversions_for_ast!(Expr<'a>, LessThan<'a>);
derive_conversions_for_ast!(Expr<'a>, Let<'a>);
derive_conversions_for_ast!(Expr<'a>, LetClass<'a>);
derive_conversions_for_ast!(Expr<'a>, LetRec<'a>);
derive_conversions_for_ast!(Expr<'a>, LetVar<'a>);
derive_conversions_for_ast!(Expr<'a>, LocalClassConstructor<'a>);
derive_conversions_for_ast!(Expr<'a>, LocalClassSelector<'a>);
derive_conversions_for_ast!(Expr<'a>, LocalMethodInvocation<'a>);
derive_conversions_for_ast!(Expr<'a>, LocalThis<'a>);
derive_conversions_for_ast!(Expr<'a>, MapApply<'a>);
derive_conversions_for_ast!(Expr<'a>, MapUpdated<'a>);
derive_conversions_for_ast!(Expr<'a>, MatchExpr<'a>);
derive_conversions_for_ast!(Expr<'a>, MethodInvocation<'a>);
derive_conversions_for_ast!(Expr<'a>, Minus<'a>);
derive_conversions_for_ast!(Expr<'a>, Modulo<'a>);
derive_conversions_for_ast!(Expr<'a>, MultiplicityInBag<'a>);
derive_conversions_for_ast!(Expr<'a>, MutableMapApply<'a>);
derive_conversions_for_ast!(Expr<'a>, MutableMapDuplicate<'a>);
derive_conversions_for_ast!(Expr<'a>, MutableMapUpdate<'a>);
derive_conversions_for_ast!(Expr<'a>, MutableMapUpdated<'a>);
derive_conversions_for_ast!(Expr<'a>, MutableMapWithDefault<'a>);
derive_conversions_for_ast!(Expr<'a>, NoTree<'a>);
derive_conversions_for_ast!(Expr<'a>, Not<'a>);
derive_conversions_for_ast!(Expr<'a>, Old<'a>);
derive_conversions_for_ast!(Expr<'a>, Or<'a>);
derive_conversions_for_ast!(Expr<'a>, Passes<'a>);
derive_conversions_for_ast!(Expr<'a>, Plus<'a>);
derive_conversions_for_ast!(Expr<'a>, Remainder<'a>);
derive_conversions_for_ast!(Expr<'a>, Require<'a>);
derive_conversions_for_ast!(Expr<'a>, SetAdd<'a>);
derive_conversions_for_ast!(Expr<'a>, SetDifference<'a>);
derive_conversions_for_ast!(Expr<'a>, SetIntersection<'a>);
derive_conversions_for_ast!(Expr<'a>, SetUnion<'a>);
derive_conversions_for_ast!(Expr<'a>, SizedADT<'a>);
derive_conversions_for_ast!(Expr<'a>, Snapshot<'a>);
derive_conversions_for_ast!(Expr<'a>, StringConcat<'a>);
derive_conversions_for_ast!(Expr<'a>, StringLength<'a>);
derive_conversions_for_ast!(Expr<'a>, StringLiteral);
derive_conversions_for_ast!(Expr<'a>, SubString<'a>);
derive_conversions_for_ast!(Expr<'a>, SubsetOf<'a>);
derive_conversions_for_ast!(Expr<'a>, Super<'a>);
derive_conversions_for_ast!(Expr<'a>, This<'a>);
derive_conversions_for_ast!(Expr<'a>, Throw<'a>);
derive_conversions_for_ast!(Expr<'a>, Throwing<'a>);
derive_conversions_for_ast!(Expr<'a>, Times<'a>);
derive_conversions_for_ast!(Expr<'a>, Try<'a>);
derive_conversions_for_ast!(Expr<'a>, Tuple<'a>);
derive_conversions_for_ast!(Expr<'a>, TupleSelect<'a>);
derive_conversions_for_ast!(Expr<'a>, UMinus<'a>);
derive_conversions_for_ast!(Expr<'a>, UnitLiteral);
derive_conversions_for_ast!(Expr<'a>, Variable<'a>);
derive_conversions_for_ast!(Expr<'a>, While<'a>);

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

/// stainless.ast.Expressions.Annotated
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Annotated<'a> {
  pub body: Expr<'a>,
  pub flags: Seq<Flag<'a>>,
}

impl<'a> Serializable for Annotated<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(123))?;
    self.body.serialize(s)?;
    self.flags.serialize(s)?;
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

/// stainless.extraction.innerfuns.Trees.ApplyLetRec
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ApplyLetRec<'a> {
  pub id: &'a Identifier,
  pub tparams: Seq<&'a TypeParameter<'a>>,
  pub tpe: &'a FunctionType<'a>,
  pub tps: Seq<Type<'a>>,
  pub args: Seq<Expr<'a>>,
}

impl<'a> Serializable for ApplyLetRec<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(185))?;
    self.id.serialize(s)?;
    self.tparams.serialize(s)?;
    self.tpe.serialize(s)?;
    self.tps.serialize(s)?;
    self.args.serialize(s)?;
    Ok(())
  }
}

/// stainless.ast.Expressions.ArrayLength
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ArrayLength<'a> {
  pub array: Expr<'a>,
}

impl<'a> Serializable for ArrayLength<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(137))?;
    self.array.serialize(s)?;
    Ok(())
  }
}

/// stainless.ast.Expressions.ArraySelect
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ArraySelect<'a> {
  pub array: Expr<'a>,
  pub index: Expr<'a>,
}

impl<'a> Serializable for ArraySelect<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(135))?;
    self.array.serialize(s)?;
    self.index.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.imperative.Trees.ArrayUpdate
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ArrayUpdate<'a> {
  pub array: Expr<'a>,
  pub index: Expr<'a>,
  pub value: Expr<'a>,
}

impl<'a> Serializable for ArrayUpdate<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(193))?;
    self.array.serialize(s)?;
    self.index.serialize(s)?;
    self.value.serialize(s)?;
    Ok(())
  }
}

/// stainless.ast.Expressions.ArrayUpdated
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ArrayUpdated<'a> {
  pub array: Expr<'a>,
  pub index: Expr<'a>,
  pub value: Expr<'a>,
}

impl<'a> Serializable for ArrayUpdated<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(136))?;
    self.array.serialize(s)?;
    self.index.serialize(s)?;
    self.value.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.oo.Trees.AsInstanceOf
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AsInstanceOf<'a> {
  pub expr: Expr<'a>,
  pub tpe: Type<'a>,
}

impl<'a> Serializable for AsInstanceOf<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(203))?;
    self.expr.serialize(s)?;
    self.tpe.serialize(s)?;
    Ok(())
  }
}

/// stainless.ast.Expressions.Assert
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Assert<'a> {
  pub pred: Expr<'a>,
  pub error: Option<String>,
  pub body: Expr<'a>,
}

impl<'a> Serializable for Assert<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(125))?;
    self.pred.serialize(s)?;
    self.error.serialize(s)?;
    self.body.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.imperative.Trees.Assignment
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Assignment<'a> {
  pub v: &'a Variable<'a>,
  pub value: Expr<'a>,
}

impl<'a> Serializable for Assignment<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(190))?;
    self.v.serialize(s)?;
    self.value.serialize(s)?;
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

/// stainless.extraction.imperative.Trees.Block
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Block<'a> {
  pub exprs: Seq<Expr<'a>>,
  pub last: Expr<'a>,
}

impl<'a> Serializable for Block<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(188))?;
    self.exprs.serialize(s)?;
    self.last.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.imperative.Trees.BoolBitwiseAnd
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BoolBitwiseAnd<'a> {
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
}

impl<'a> Serializable for BoolBitwiseAnd<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(195))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.imperative.Trees.BoolBitwiseOr
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BoolBitwiseOr<'a> {
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
}

impl<'a> Serializable for BoolBitwiseOr<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(196))?;
    self.lhs.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.imperative.Trees.BoolBitwiseXor
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BoolBitwiseXor<'a> {
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
}

impl<'a> Serializable for BoolBitwiseXor<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(197))?;
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

/// stainless.extraction.oo.Trees.ClassConstructor
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ClassConstructor<'a> {
  pub ct: &'a ClassType<'a>,
  pub args: Seq<Expr<'a>>,
}

impl<'a> Serializable for ClassConstructor<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(200))?;
    self.ct.serialize(s)?;
    self.args.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.oo.Trees.ClassSelector
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ClassSelector<'a> {
  pub expr: Expr<'a>,
  pub selector: &'a Identifier,
}

impl<'a> Serializable for ClassSelector<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(201))?;
    self.expr.serialize(s)?;
    self.selector.serialize(s)?;
    Ok(())
  }
}

/// stainless.ast.Expressions.Decreases
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Decreases<'a> {
  pub measure: Expr<'a>,
  pub body: Expr<'a>,
}

impl<'a> Serializable for Decreases<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(180))?;
    self.measure.serialize(s)?;
    self.body.serialize(s)?;
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

/// stainless.ast.Expressions.Ensuring
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Ensuring<'a> {
  pub body: Expr<'a>,
  pub pred: &'a Lambda<'a>,
}

impl<'a> Serializable for Ensuring<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(124))?;
    self.body.serialize(s)?;
    self.pred.serialize(s)?;
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

/// stainless.ast.Expressions.Error
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Error<'a> {
  pub tpe: Type<'a>,
  pub description: String,
}

impl<'a> Serializable for Error<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(121))?;
    self.tpe.serialize(s)?;
    self.description.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.imperative.Trees.FieldAssignment
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FieldAssignment<'a> {
  pub obj: Expr<'a>,
  pub selector: &'a Identifier,
  pub value: Expr<'a>,
}

impl<'a> Serializable for FieldAssignment<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(191))?;
    self.obj.serialize(s)?;
    self.selector.serialize(s)?;
    self.value.serialize(s)?;
    Ok(())
  }
}

/// stainless.ast.Expressions.FiniteArray
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FiniteArray<'a> {
  pub elems: Seq<Expr<'a>>,
  pub base: Type<'a>,
}

impl<'a> Serializable for FiniteArray<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(133))?;
    self.elems.serialize(s)?;
    self.base.serialize(s)?;
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

/// stainless.extraction.oo.Trees.IsInstanceOf
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IsInstanceOf<'a> {
  pub expr: Expr<'a>,
  pub tpe: Type<'a>,
}

impl<'a> Serializable for IsInstanceOf<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(202))?;
    self.expr.serialize(s)?;
    self.tpe.serialize(s)?;
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

/// stainless.ast.Expressions.LargeArray
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LargeArray<'a> {
  pub elems: Map<Int, Expr<'a>>,
  pub default: Expr<'a>,
  pub size: Expr<'a>,
  pub base: Type<'a>,
}

impl<'a> Serializable for LargeArray<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(134))?;
    self.elems.serialize(s)?;
    self.default.serialize(s)?;
    self.size.serialize(s)?;
    self.base.serialize(s)?;
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

/// stainless.extraction.innerclasses.Trees.LetClass
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LetClass<'a> {
  pub classes: Seq<&'a LocalClassDef<'a>>,
  pub body: Expr<'a>,
}

impl<'a> Serializable for LetClass<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(232))?;
    self.classes.serialize(s)?;
    self.body.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.innerfuns.Trees.LetRec
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LetRec<'a> {
  pub fds: Seq<&'a LocalFunDef<'a>>,
  pub body: Expr<'a>,
}

impl<'a> Serializable for LetRec<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(184))?;
    self.fds.serialize(s)?;
    self.body.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.imperative.Trees.LetVar
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LetVar<'a> {
  pub vd: &'a ValDef<'a>,
  pub value: Expr<'a>,
  pub body: Expr<'a>,
}

impl<'a> Serializable for LetVar<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(189))?;
    self.vd.serialize(s)?;
    self.value.serialize(s)?;
    self.body.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.innerclasses.Trees.LocalClassConstructor
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LocalClassConstructor<'a> {
  pub lct: &'a LocalClassType<'a>,
  pub args: Seq<Expr<'a>>,
}

impl<'a> Serializable for LocalClassConstructor<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(235))?;
    self.lct.serialize(s)?;
    self.args.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.innerclasses.Trees.LocalClassSelector
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LocalClassSelector<'a> {
  pub expr: Expr<'a>,
  pub selector: &'a Identifier,
  pub tpe: Type<'a>,
}

impl<'a> Serializable for LocalClassSelector<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(241))?;
    self.expr.serialize(s)?;
    self.selector.serialize(s)?;
    self.tpe.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.innerclasses.Trees.LocalMethodInvocation
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LocalMethodInvocation<'a> {
  pub receiver: Expr<'a>,
  pub method: &'a Variable<'a>,
  pub tparams: Seq<&'a TypeParameter<'a>>,
  pub tps: Seq<Type<'a>>,
  pub args: Seq<Expr<'a>>,
}

impl<'a> Serializable for LocalMethodInvocation<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(240))?;
    self.receiver.serialize(s)?;
    self.method.serialize(s)?;
    self.tparams.serialize(s)?;
    self.tps.serialize(s)?;
    self.args.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.innerclasses.Trees.LocalThis
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LocalThis<'a> {
  pub lct: &'a LocalClassType<'a>,
}

impl<'a> Serializable for LocalThis<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(242))?;
    self.lct.serialize(s)?;
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

/// stainless.ast.Expressions.MatchExpr
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MatchExpr<'a> {
  pub scrutinee: Expr<'a>,
  pub cases: Seq<&'a MatchCase<'a>>,
}

impl<'a> Serializable for MatchExpr<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(126))?;
    self.scrutinee.serialize(s)?;
    self.cases.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.methods.Trees.MethodInvocation
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MethodInvocation<'a> {
  pub receiver: Expr<'a>,
  pub id: &'a Identifier,
  pub tps: Seq<Type<'a>>,
  pub args: Seq<Expr<'a>>,
}

impl<'a> Serializable for MethodInvocation<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(216))?;
    self.receiver.serialize(s)?;
    self.id.serialize(s)?;
    self.tps.serialize(s)?;
    self.args.serialize(s)?;
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

/// stainless.extraction.imperative.Trees.MutableMapApply
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MutableMapApply<'a> {
  pub map: Expr<'a>,
  pub key: Expr<'a>,
}

impl<'a> Serializable for MutableMapApply<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(234))?;
    self.map.serialize(s)?;
    self.key.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.imperative.Trees.MutableMapDuplicate
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MutableMapDuplicate<'a> {
  pub map: Expr<'a>,
}

impl<'a> Serializable for MutableMapDuplicate<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(237))?;
    self.map.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.imperative.Trees.MutableMapUpdate
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MutableMapUpdate<'a> {
  pub map: Expr<'a>,
  pub key: Expr<'a>,
  pub value: Expr<'a>,
}

impl<'a> Serializable for MutableMapUpdate<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(235))?;
    self.map.serialize(s)?;
    self.key.serialize(s)?;
    self.value.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.imperative.Trees.MutableMapUpdated
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MutableMapUpdated<'a> {
  pub map: Expr<'a>,
  pub key: Expr<'a>,
  pub value: Expr<'a>,
}

impl<'a> Serializable for MutableMapUpdated<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(236))?;
    self.map.serialize(s)?;
    self.key.serialize(s)?;
    self.value.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.imperative.Trees.MutableMapWithDefault
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MutableMapWithDefault<'a> {
  pub from: Type<'a>,
  pub to: Type<'a>,
  pub default: Expr<'a>,
}

impl<'a> Serializable for MutableMapWithDefault<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(233))?;
    self.from.serialize(s)?;
    self.to.serialize(s)?;
    self.default.serialize(s)?;
    Ok(())
  }
}

/// stainless.ast.Expressions.NoTree
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NoTree<'a> {
  pub tpe: Type<'a>,
}

impl<'a> Serializable for NoTree<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(120))?;
    self.tpe.serialize(s)?;
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

/// stainless.extraction.imperative.Trees.Old
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Old<'a> {
  pub e: Expr<'a>,
}

impl<'a> Serializable for Old<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(194))?;
    self.e.serialize(s)?;
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

/// stainless.ast.Expressions.Passes
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Passes<'a> {
  pub in_: Expr<'a>,
  pub out: Expr<'a>,
  pub cases: Seq<&'a MatchCase<'a>>,
}

impl<'a> Serializable for Passes<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(158))?;
    self.in_.serialize(s)?;
    self.out.serialize(s)?;
    self.cases.serialize(s)?;
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

/// stainless.ast.Expressions.Require
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Require<'a> {
  pub pred: Expr<'a>,
  pub body: Expr<'a>,
}

impl<'a> Serializable for Require<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(122))?;
    self.pred.serialize(s)?;
    self.body.serialize(s)?;
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

/// stainless.ast.Expressions.SizedADT
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SizedADT<'a> {
  pub id: &'a Identifier,
  pub tps: Seq<Type<'a>>,
  pub args: Seq<Expr<'a>>,
  pub size: Expr<'a>,
}

impl<'a> Serializable for SizedADT<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(154))?;
    self.id.serialize(s)?;
    self.tps.serialize(s)?;
    self.args.serialize(s)?;
    self.size.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.imperative.Trees.Snapshot
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Snapshot<'a> {
  pub e: Expr<'a>,
}

impl<'a> Serializable for Snapshot<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(239))?;
    self.e.serialize(s)?;
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

/// stainless.extraction.methods.Trees.Super
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Super<'a> {
  pub ct: &'a ClassType<'a>,
}

impl<'a> Serializable for Super<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(215))?;
    self.ct.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.methods.Trees.This
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct This<'a> {
  pub ct: &'a ClassType<'a>,
}

impl<'a> Serializable for This<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(214))?;
    self.ct.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.throwing.Trees.Throw
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Throw<'a> {
  pub ex: Expr<'a>,
}

impl<'a> Serializable for Throw<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(212))?;
    self.ex.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.throwing.Trees.Throwing
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Throwing<'a> {
  pub body: Expr<'a>,
  pub pred: &'a Lambda<'a>,
}

impl<'a> Serializable for Throwing<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(211))?;
    self.body.serialize(s)?;
    self.pred.serialize(s)?;
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

/// stainless.extraction.throwing.Trees.Try
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Try<'a> {
  pub body: Expr<'a>,
  pub cases: Seq<&'a MatchCase<'a>>,
  pub finallizer: Option<Expr<'a>>,
}

impl<'a> Serializable for Try<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(213))?;
    self.body.serialize(s)?;
    self.cases.serialize(s)?;
    self.finallizer.serialize(s)?;
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

/// stainless.extraction.imperative.Trees.While
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct While<'a> {
  pub cond: Expr<'a>,
  pub body: Expr<'a>,
  pub pred: Option<Expr<'a>>,
}

impl<'a> Serializable for While<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(192))?;
    self.cond.serialize(s)?;
    self.body.serialize(s)?;
    self.pred.serialize(s)?;
    Ok(())
  }
}

// === Types ===

/// inox.ast.Types.Type
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Type<'a> {
  ADTType(&'a ADTType<'a>),
  AnnotatedType(&'a AnnotatedType<'a>),
  AnyType(&'a AnyType),
  ArrayType(&'a ArrayType<'a>),
  BVType(&'a BVType),
  BagType(&'a BagType<'a>),
  BooleanType(&'a BooleanType),
  CharType(&'a CharType),
  ClassType(&'a ClassType<'a>),
  FunctionType(&'a FunctionType<'a>),
  IntegerType(&'a IntegerType),
  LocalClassType(&'a LocalClassType<'a>),
  MapType(&'a MapType<'a>),
  MutableMapType(&'a MutableMapType<'a>),
  NothingType(&'a NothingType),
  PiType(&'a PiType<'a>),
  RealType(&'a RealType),
  RecursiveType(&'a RecursiveType<'a>),
  RefinementType(&'a RefinementType<'a>),
  SetType(&'a SetType<'a>),
  SigmaType(&'a SigmaType<'a>),
  StringType(&'a StringType),
  TupleType(&'a TupleType<'a>),
  TypeApply(&'a TypeApply<'a>),
  TypeBounds(&'a TypeBounds<'a>),
  TypeParameter(&'a TypeParameter<'a>),
  TypeSelect(&'a TypeSelect<'a>),
  UnitType(&'a UnitType),
  UnknownType(&'a UnknownType),
  Untyped(&'a Untyped),
  ValueType(&'a ValueType<'a>),
}

impl Factory {
  pub fn ADTType<'a>(&'a self, id: &'a Identifier, tps: Seq<Type<'a>>) -> &'a mut ADTType<'a> {
    self.bump.alloc(ADTType { id, tps })
  }

  pub fn AnnotatedType<'a>(
    &'a self,
    tpe: Type<'a>,
    flags: Seq<Flag<'a>>,
  ) -> &'a mut AnnotatedType<'a> {
    self.bump.alloc(AnnotatedType { tpe, flags })
  }

  pub fn AnyType<'a>(&'a self) -> &'a mut AnyType {
    self.bump.alloc(AnyType {})
  }

  pub fn ArrayType<'a>(&'a self, base: Type<'a>) -> &'a mut ArrayType<'a> {
    self.bump.alloc(ArrayType { base })
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

  pub fn ClassType<'a>(&'a self, id: &'a Identifier, tps: Seq<Type<'a>>) -> &'a mut ClassType<'a> {
    self.bump.alloc(ClassType { id, tps })
  }

  pub fn FunctionType<'a>(&'a self, from: Seq<Type<'a>>, to: Type<'a>) -> &'a mut FunctionType<'a> {
    self.bump.alloc(FunctionType { from, to })
  }

  pub fn IntegerType<'a>(&'a self) -> &'a mut IntegerType {
    self.bump.alloc(IntegerType {})
  }

  pub fn LocalClassType<'a>(
    &'a self,
    id: &'a Identifier,
    tparams: Seq<&'a TypeParameterDef<'a>>,
    tps: Seq<Type<'a>>,
    ancestors: Seq<Type<'a>>,
  ) -> &'a mut LocalClassType<'a> {
    self.bump.alloc(LocalClassType {
      id,
      tparams,
      tps,
      ancestors,
    })
  }

  pub fn MapType<'a>(&'a self, from: Type<'a>, to: Type<'a>) -> &'a mut MapType<'a> {
    self.bump.alloc(MapType { from, to })
  }

  pub fn MutableMapType<'a>(&'a self, from: Type<'a>, to: Type<'a>) -> &'a mut MutableMapType<'a> {
    self.bump.alloc(MutableMapType { from, to })
  }

  pub fn NothingType<'a>(&'a self) -> &'a mut NothingType {
    self.bump.alloc(NothingType {})
  }

  pub fn PiType<'a>(&'a self, params: Seq<&'a ValDef<'a>>, to: Type<'a>) -> &'a mut PiType<'a> {
    self.bump.alloc(PiType { params, to })
  }

  pub fn RealType<'a>(&'a self) -> &'a mut RealType {
    self.bump.alloc(RealType {})
  }

  pub fn RecursiveType<'a>(
    &'a self,
    id: &'a Identifier,
    tps: Seq<Type<'a>>,
    index: Expr<'a>,
  ) -> &'a mut RecursiveType<'a> {
    self.bump.alloc(RecursiveType { id, tps, index })
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

  pub fn TypeApply<'a>(
    &'a self,
    selector: &'a TypeSelect<'a>,
    tps: Seq<Type<'a>>,
  ) -> &'a mut TypeApply<'a> {
    self.bump.alloc(TypeApply { selector, tps })
  }

  pub fn TypeBounds<'a>(
    &'a self,
    lo: Type<'a>,
    hi: Type<'a>,
    flags: Seq<Flag<'a>>,
  ) -> &'a mut TypeBounds<'a> {
    self.bump.alloc(TypeBounds { lo, hi, flags })
  }

  pub fn TypeParameter<'a>(
    &'a self,
    id: &'a Identifier,
    flags: Seq<Flag<'a>>,
  ) -> &'a mut TypeParameter<'a> {
    self.bump.alloc(TypeParameter { id, flags })
  }

  pub fn TypeSelect<'a>(
    &'a self,
    expr: Option<Expr<'a>>,
    selector: &'a Identifier,
  ) -> &'a mut TypeSelect<'a> {
    self.bump.alloc(TypeSelect { expr, selector })
  }

  pub fn UnitType<'a>(&'a self) -> &'a mut UnitType {
    self.bump.alloc(UnitType {})
  }

  pub fn UnknownType<'a>(&'a self, isPure: Boolean) -> &'a mut UnknownType {
    self.bump.alloc(UnknownType { isPure })
  }

  pub fn Untyped<'a>(&'a self) -> &'a mut Untyped {
    self.bump.alloc(Untyped {})
  }

  pub fn ValueType<'a>(&'a self, tpe: Type<'a>) -> &'a mut ValueType<'a> {
    self.bump.alloc(ValueType { tpe })
  }
}

impl<'a> Serializable for Type<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    match self {
      Type::ADTType(v) => v.serialize(s)?,
      Type::AnnotatedType(v) => v.serialize(s)?,
      Type::AnyType(v) => v.serialize(s)?,
      Type::ArrayType(v) => v.serialize(s)?,
      Type::BVType(v) => v.serialize(s)?,
      Type::BagType(v) => v.serialize(s)?,
      Type::BooleanType(v) => v.serialize(s)?,
      Type::CharType(v) => v.serialize(s)?,
      Type::ClassType(v) => v.serialize(s)?,
      Type::FunctionType(v) => v.serialize(s)?,
      Type::IntegerType(v) => v.serialize(s)?,
      Type::LocalClassType(v) => v.serialize(s)?,
      Type::MapType(v) => v.serialize(s)?,
      Type::MutableMapType(v) => v.serialize(s)?,
      Type::NothingType(v) => v.serialize(s)?,
      Type::PiType(v) => v.serialize(s)?,
      Type::RealType(v) => v.serialize(s)?,
      Type::RecursiveType(v) => v.serialize(s)?,
      Type::RefinementType(v) => v.serialize(s)?,
      Type::SetType(v) => v.serialize(s)?,
      Type::SigmaType(v) => v.serialize(s)?,
      Type::StringType(v) => v.serialize(s)?,
      Type::TupleType(v) => v.serialize(s)?,
      Type::TypeApply(v) => v.serialize(s)?,
      Type::TypeBounds(v) => v.serialize(s)?,
      Type::TypeParameter(v) => v.serialize(s)?,
      Type::TypeSelect(v) => v.serialize(s)?,
      Type::UnitType(v) => v.serialize(s)?,
      Type::UnknownType(v) => v.serialize(s)?,
      Type::Untyped(v) => v.serialize(s)?,
      Type::ValueType(v) => v.serialize(s)?,
    };
    Ok(())
  }
}

derive_conversions_for_ast!(Type<'a>, ADTType<'a>);
derive_conversions_for_ast!(Type<'a>, AnnotatedType<'a>);
derive_conversions_for_ast!(Type<'a>, AnyType);
derive_conversions_for_ast!(Type<'a>, ArrayType<'a>);
derive_conversions_for_ast!(Type<'a>, BVType);
derive_conversions_for_ast!(Type<'a>, BagType<'a>);
derive_conversions_for_ast!(Type<'a>, BooleanType);
derive_conversions_for_ast!(Type<'a>, CharType);
derive_conversions_for_ast!(Type<'a>, ClassType<'a>);
derive_conversions_for_ast!(Type<'a>, FunctionType<'a>);
derive_conversions_for_ast!(Type<'a>, IntegerType);
derive_conversions_for_ast!(Type<'a>, LocalClassType<'a>);
derive_conversions_for_ast!(Type<'a>, MapType<'a>);
derive_conversions_for_ast!(Type<'a>, MutableMapType<'a>);
derive_conversions_for_ast!(Type<'a>, NothingType);
derive_conversions_for_ast!(Type<'a>, PiType<'a>);
derive_conversions_for_ast!(Type<'a>, RealType);
derive_conversions_for_ast!(Type<'a>, RecursiveType<'a>);
derive_conversions_for_ast!(Type<'a>, RefinementType<'a>);
derive_conversions_for_ast!(Type<'a>, SetType<'a>);
derive_conversions_for_ast!(Type<'a>, SigmaType<'a>);
derive_conversions_for_ast!(Type<'a>, StringType);
derive_conversions_for_ast!(Type<'a>, TupleType<'a>);
derive_conversions_for_ast!(Type<'a>, TypeApply<'a>);
derive_conversions_for_ast!(Type<'a>, TypeBounds<'a>);
derive_conversions_for_ast!(Type<'a>, TypeParameter<'a>);
derive_conversions_for_ast!(Type<'a>, TypeSelect<'a>);
derive_conversions_for_ast!(Type<'a>, UnitType);
derive_conversions_for_ast!(Type<'a>, UnknownType);
derive_conversions_for_ast!(Type<'a>, Untyped);
derive_conversions_for_ast!(Type<'a>, ValueType<'a>);

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

/// stainless.ast.Expressions.AnnotatedType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AnnotatedType<'a> {
  pub tpe: Type<'a>,
  pub flags: Seq<Flag<'a>>,
}

impl<'a> Serializable for AnnotatedType<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(157))?;
    self.tpe.serialize(s)?;
    self.flags.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.oo.Trees.AnyType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AnyType {}

impl Serializable for AnyType {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(207))?;
    Ok(())
  }
}

/// stainless.ast.Types.ArrayType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ArrayType<'a> {
  pub base: Type<'a>,
}

impl<'a> Serializable for ArrayType<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(138))?;
    self.base.serialize(s)?;
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

/// stainless.extraction.oo.Trees.ClassType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ClassType<'a> {
  pub id: &'a Identifier,
  pub tps: Seq<Type<'a>>,
}

impl<'a> Serializable for ClassType<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(206))?;
    self.id.serialize(s)?;
    self.tps.serialize(s)?;
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

/// stainless.extraction.innerclasses.Types.LocalClassType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LocalClassType<'a> {
  pub id: &'a Identifier,
  pub tparams: Seq<&'a TypeParameterDef<'a>>,
  pub tps: Seq<Type<'a>>,
  pub ancestors: Seq<Type<'a>>,
}

impl<'a> Serializable for LocalClassType<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(236))?;
    self.id.serialize(s)?;
    self.tparams.serialize(s)?;
    self.tps.serialize(s)?;
    self.ancestors.serialize(s)?;
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

/// stainless.extraction.imperative.Trees.MutableMapType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MutableMapType<'a> {
  pub from: Type<'a>,
  pub to: Type<'a>,
}

impl<'a> Serializable for MutableMapType<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(232))?;
    self.from.serialize(s)?;
    self.to.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.oo.Trees.NothingType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NothingType {}

impl Serializable for NothingType {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(208))?;
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

/// stainless.ast.Expressions.RecursiveType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RecursiveType<'a> {
  pub id: &'a Identifier,
  pub tps: Seq<Type<'a>>,
  pub index: Expr<'a>,
}

impl<'a> Serializable for RecursiveType<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(152))?;
    self.id.serialize(s)?;
    self.tps.serialize(s)?;
    self.index.serialize(s)?;
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

/// stainless.extraction.oo.Trees.TypeApply
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeApply<'a> {
  pub selector: &'a TypeSelect<'a>,
  pub tps: Seq<Type<'a>>,
}

impl<'a> Serializable for TypeApply<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(238))?;
    self.selector.serialize(s)?;
    self.tps.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.oo.Trees.TypeBounds
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeBounds<'a> {
  pub lo: Type<'a>,
  pub hi: Type<'a>,
  pub flags: Seq<Flag<'a>>,
}

impl<'a> Serializable for TypeBounds<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(209))?;
    self.lo.serialize(s)?;
    self.hi.serialize(s)?;
    self.flags.serialize(s)?;
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

/// stainless.extraction.oo.Trees.TypeSelect
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeSelect<'a> {
  pub expr: Option<Expr<'a>>,
  pub selector: &'a Identifier,
}

impl<'a> Serializable for TypeSelect<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(237))?;
    self.expr.serialize(s)?;
    self.selector.serialize(s)?;
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

/// stainless.extraction.oo.Trees.UnknownType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct UnknownType {
  pub isPure: Boolean,
}

impl Serializable for UnknownType {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(245))?;
    self.isPure.serialize(s)?;
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

/// stainless.ast.Expressions.ValueType
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ValueType<'a> {
  pub tpe: Type<'a>,
}

impl<'a> Serializable for ValueType<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(153))?;
    self.tpe.serialize(s)?;
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

/// stainless.ast.Expressions.ADTPattern
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ADTPattern<'a> {
  pub binder: Option<&'a ValDef<'a>>,
  pub id: &'a Identifier,
  pub tps: Seq<Type<'a>>,
  pub subPatterns: Seq<Expr<'a>>,
}

impl<'a> Serializable for ADTPattern<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(129))?;
    self.binder.serialize(s)?;
    self.id.serialize(s)?;
    self.tps.serialize(s)?;
    self.subPatterns.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.oo.Trees.ClassPattern
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ClassPattern<'a> {
  pub binder: Option<&'a ValDef<'a>>,
  pub tpe: &'a ClassType<'a>,
  pub subPatterns: Seq<Expr<'a>>,
}

impl<'a> Serializable for ClassPattern<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(204))?;
    self.binder.serialize(s)?;
    self.tpe.serialize(s)?;
    self.subPatterns.serialize(s)?;
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
    self.globalId == other.globalId
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
    self.globalId.cmp(&other.globalId)
  }
}
impl Hash for Identifier {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.globalId.hash(state);
  }
}

/// stainless.extraction.xlang.Trees.Import
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Import {
  pub path: Seq<String>,
  pub isWildcard: Boolean,
}

impl Serializable for Import {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(219))?;
    self.path.serialize(s)?;
    self.isWildcard.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.innerfuns.Definitions.Inner
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Inner<'a> {
  pub fd: &'a LocalFunDef<'a>,
}

impl<'a> Serializable for Inner<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(187))?;
    self.fd.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.oo.Trees.InstanceOfPattern
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct InstanceOfPattern<'a> {
  pub binder: Option<&'a ValDef<'a>>,
  pub tpe: Type<'a>,
}

impl<'a> Serializable for InstanceOfPattern<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(205))?;
    self.binder.serialize(s)?;
    self.tpe.serialize(s)?;
    Ok(())
  }
}

/// stainless.ast.Expressions.LiteralPattern
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LiteralPattern<'a> {
  pub binder: Option<&'a ValDef<'a>>,
  pub lit: Expr<'a>,
}

impl<'a> Serializable for LiteralPattern<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(131))?;
    self.binder.serialize(s)?;
    self.lit.serialize(s)?;
    Ok(())
  }
}

/// stainless.ast.Expressions.MatchCase
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MatchCase<'a> {
  pub pattern: Expr<'a>,
  pub optGuard: Option<Expr<'a>>,
  pub rhs: Expr<'a>,
}

impl<'a> Serializable for MatchCase<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(127))?;
    self.pattern.serialize(s)?;
    self.optGuard.serialize(s)?;
    self.rhs.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.xlang.Trees.ModuleDef
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ModuleDef<'a> {
  pub id: &'a Identifier,
  pub imports: Seq<&'a Import>,
  pub classes: Seq<&'a Identifier>,
  pub functions: Seq<&'a Identifier>,
  pub typeDefs: Seq<&'a Identifier>,
  pub modules: Seq<&'a ModuleDef<'a>>,
}

impl<'a> Serializable for ModuleDef<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(221))?;
    self.id.serialize(s)?;
    self.imports.serialize(s)?;
    self.classes.serialize(s)?;
    self.functions.serialize(s)?;
    self.typeDefs.serialize(s)?;
    self.modules.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.innerfuns.Definitions.Outer
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Outer<'a> {
  pub fd: &'a FunDef<'a>,
}

impl<'a> Serializable for Outer<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(186))?;
    self.fd.serialize(s)?;
    Ok(())
  }
}

/// stainless.ast.SymbolIdentifier
#[derive(Clone, Debug)]
pub struct SymbolIdentifier<'a> {
  pub id: &'a Identifier,
  pub symbol_path: Seq<String>,
}

impl<'a> PartialEq for SymbolIdentifier<'a> {
  fn eq(&self, other: &Self) -> bool {
    self.id.globalId == other.id.globalId
  }
}
impl<'a> Eq for SymbolIdentifier<'a> {}
impl<'a> PartialOrd for SymbolIdentifier<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}
impl<'a> Ord for SymbolIdentifier<'a> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.id.globalId.cmp(&other.id.globalId)
  }
}
impl<'a> Hash for SymbolIdentifier<'a> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.id.globalId.hash(state);
  }
}

/// stainless.ast.Expressions.TuplePattern
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TuplePattern<'a> {
  pub binder: Option<&'a ValDef<'a>>,
  pub subPatterns: Seq<Expr<'a>>,
}

impl<'a> Serializable for TuplePattern<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(130))?;
    self.binder.serialize(s)?;
    self.subPatterns.serialize(s)?;
    Ok(())
  }
}

/// stainless.ast.Expressions.UnapplyPattern
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct UnapplyPattern<'a> {
  pub binder: Option<&'a ValDef<'a>>,
  pub recs: Seq<Expr<'a>>,
  pub id: &'a Identifier,
  pub tps: Seq<Type<'a>>,
  pub subPatterns: Seq<Expr<'a>>,
}

impl<'a> Serializable for UnapplyPattern<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(132))?;
    self.binder.serialize(s)?;
    self.recs.serialize(s)?;
    self.id.serialize(s)?;
    self.tps.serialize(s)?;
    self.subPatterns.serialize(s)?;
    Ok(())
  }
}

/// stainless.extraction.xlang.Trees.UnitDef
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct UnitDef<'a> {
  pub id: &'a Identifier,
  pub imports: Seq<&'a Import>,
  pub classes: Seq<&'a Identifier>,
  pub modules: Seq<&'a ModuleDef<'a>>,
  pub isMain: Boolean,
}

impl<'a> Serializable for UnitDef<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(220))?;
    self.id.serialize(s)?;
    self.imports.serialize(s)?;
    self.classes.serialize(s)?;
    self.modules.serialize(s)?;
    self.isMain.serialize(s)?;
    Ok(())
  }
}

/// stainless.ast.Expressions.WildcardPattern
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct WildcardPattern<'a> {
  pub binder: Option<&'a ValDef<'a>>,
}

impl<'a> Serializable for WildcardPattern<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(128))?;
    self.binder.serialize(s)?;
    Ok(())
  }
}
