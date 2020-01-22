#![allow(non_snake_case)]

#[macro_use]
mod macros;

mod generated;
pub use generated::*;

use std::hash::{Hash, Hasher};

use crate::ser::types::*;
use crate::ser::{BufferSerializer, MarkerId, Serializable, SerializationResult, Serializer};

use bumpalo::Bump;

/// A factory for easily allocating AST nodes in an arena
#[derive(Debug)]
pub struct Factory {
  bump: Bump,
}

impl Factory {
  pub fn new() -> Self {
    Factory { bump: Bump::new() }
  }

  pub fn alloc<T>(&self, v: T) -> &mut T {
    self.bump.alloc(v)
  }
}

/// inox.trees.Symbols
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Symbols<'a> {
  pub sorts: Map<&'a Identifier, &'a ADTSort<'a>>,
  pub functions: Map<&'a Identifier, &'a FunDef<'a>>,
}

impl<'a> Hash for Symbols<'a> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    let mut sorts: Vec<_> = self.sorts.values().collect();
    sorts.sort();
    sorts.iter().for_each(|sort| sort.hash(state));
    let mut functions: Vec<_> = self.functions.values().collect();
    functions.sort();
    functions.iter().for_each(|function| function.hash(state));
  }
}

impl<'a> Serializable for Symbols<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    let mut sorts: Vec<_> = self.sorts.values().collect();
    sorts.sort();
    let mut functions: Vec<_> = self.functions.values().collect();
    functions.sort();

    let mut inner_s = BufferSerializer::new();
    (functions, sorts).serialize(&mut inner_s)?;
    inner_s.to_buffer().serialize(s)?;
    Ok(())
  }
}

// Various trait implementations that are significantly different from the rest

impl<'a> Serializable for ValDef<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(94))?;
    self.v.serialize(s)?;
    Ok(())
  }
}

impl<'a> Serializable for TypeParameterDef<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(95))?;
    self.tp.serialize(s)?;
    Ok(())
  }
}

impl Serializable for BVLiteral {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(20))?;
    (self.signed, &self.value, self.size).serialize(s)?;
    Ok(())
  }
}

impl Serializable for Identifier {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(90))?;
    (&self.name, self.globalId, self.id).serialize(s)?;
    Ok(())
  }
}

// TODO: Conditional on stainless build
impl<'a> Serializable for SymbolIdentifier<'a> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(MarkerId(145))?;
    // NOTE: We deviate from Stainless here in that we reuse the Identifier's globalId
    // as the Symbol's id.
    (self.id.globalId, self.id.id, &self.symbol_path, self.id.globalId).serialize(s)?;
    Ok(())
  }
}

// TODO: Conditional on stainless build
impl<'a> Hash for LargeArray<'a> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    let mut elems: Vec<(&Int, &Expr<'a>)> = self.elems.iter().collect();
    elems.sort_by(|&(i1, _), &(i2, _)| { i1.cmp(&i2) });
    elems.iter().for_each(|elem| elem.hash(state));
    self.default.hash(state);
    self.size.hash(state);
    self.base.hash(state);
  }
}

// Additional helpers that mirror those in Inox

pub fn Int32Literal(value: Int) -> BVLiteral {
  BVLiteral {
    signed: true,
    value: value.to_bigint().unwrap(),
    size: 32,
  }
}

pub fn Int32Type() -> BVType {
  BVType {
    signed: true,
    size: 32,
  }
}

impl Factory {
  pub fn Int32Literal<'a>(&'a self, value: Int) -> &'a mut BVLiteral {
    self.bump.alloc(Int32Literal(value))
  }

  pub fn Int32Type<'a>(&'a self) -> &'a mut BVType {
    self.bump.alloc(Int32Type())
  }

  pub fn ADTConstructor<'a>(
    &'a self,
    id: &'a Identifier,
    sort: &'a Identifier,
    fields: Seq<&'a ValDef<'a>>,
  ) -> &'a mut ADTConstructor<'a> {
    self.bump.alloc(ADTConstructor { id, sort, fields })
  }

  pub fn Identifier<'a>(&'a self, name: String, globalId: Int, id: Int) -> &'a mut Identifier {
    self.bump.alloc(Identifier { name, globalId, id })
  }
}
