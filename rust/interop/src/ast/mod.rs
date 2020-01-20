#![allow(non_snake_case)]

mod generated;
pub use generated::*;

use std::hash::{Hasher, Hash};
use crate::ser::types::*;
use crate::ser::{MarkerId, SerializationResult, Serializable, Serializer};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Symbols<'a> {
  sorts: Map<&'a Identifier, &'a ADTSort<'a>>,
  functions: Map<&'a Identifier, &'a FunDef<'a>>
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

pub fn Int32Literal(value: Int) -> BVLiteral {
  BVLiteral {
    signed: true,
    value: value.to_bigint().unwrap(),
    size: 32
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

pub fn Int32Type() -> BVType {
  BVType { signed: true, size: 32 }
}