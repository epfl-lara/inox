#![allow(dead_code)]

extern crate num_bigint;

use std::io;
use std::string::String;
use num_bigint::BigInt;

mod serializable;
mod serializable_generated;

/** == Type mapping ==
  * Boolean <-> bool
  * Integer <-> i32
  * String  <-> std::string::String
  * BigInt  <-> num_bigint::BigInt
  *
  * TupleN  <-> (T1, ..., Tn)
  * Seq[T]  <-> std::vec::Vec<T>
  * Set[T]  <-> std::collections::HashSet
  *
  * SerializationResult <-> SerializationResult
  *
  * Stainless AST class ... auto-generated struct
  */


#[derive(PartialEq,Eq,PartialOrd,Debug)]
pub enum Marker {
  Product,
  Option,
  Seq,
  Set,
  Map,
  Primitive,
  Tuple,
  SerializationResult,
  Generated(MarkerId)
}

#[derive(PartialEq,Eq,PartialOrd,Debug)]
pub struct MarkerId(u32);

impl Marker {
  fn to_id(self) -> MarkerId {
    match self {
      Marker::Product => MarkerId(0),
      Marker::Option => MarkerId(1),
      Marker::Seq => MarkerId(2),
      Marker::Set => MarkerId(3),
      Marker::Map => MarkerId(4),
      Marker::Primitive => MarkerId(5),
      Marker::Tuple => MarkerId(6),
      Marker::SerializationResult => MarkerId(7),
      Marker::Generated(marker_id) => marker_id
    }
  }
}

impl MarkerId {
  fn to_marker(marker_id: MarkerId) -> Marker {
    match marker_id.0 {
      0 => Marker::Product,
      1 => Marker::Option,
      2 => Marker::Seq,
      3 => Marker::Set,
      4 => Marker::Map,
      5 => Marker::Primitive,
      6 => Marker::Tuple,
      7 => Marker::SerializationResult,
      _ => Marker::Generated(marker_id)
    }
  }
}


pub struct Serializer<W: io::Write> {
  writer: W
}

type SerializationResult = Result<(), io::Error>;

macro_rules! make_write_raw {
  ($id:ident, $t:ty) => {
    fn $id(&mut self, v: $t) -> SerializationResult {
      self.writer.write(&v.to_be_bytes())?;
      Ok(())
    }
  }
}

impl<W: io::Write> Serializer<W> {
  fn new(writer: W) -> Serializer<W> {
    Serializer {
      writer
    }
  }

  // Raw writing

  make_write_raw!(write_u8, u8);
  make_write_raw!(write_i8, i8);
  make_write_raw!(write_u16, u16);
  make_write_raw!(write_i16, i16);
  make_write_raw!(write_u32, u32);
  make_write_raw!(write_i32, i32);
  make_write_raw!(write_u64, u64);
  make_write_raw!(write_i64, i64);
  make_write_raw!(write_f32, f32);
  make_write_raw!(write_f64, f64);

  fn write_bool(&mut self, v: bool) -> SerializationResult {
    self.writer.write(&[v as u8])?;
    Ok(())
  }

  fn write_marker(&mut self, marker: Marker) -> SerializationResult {
    self.write_u32(marker.to_id().0)?;
    Ok(())
  }

  // Primitives

  fn write_boolean(&mut self, v: bool) -> SerializationResult {
    self.write_marker(Marker::Primitive)?;
    self.write_u8(0)?;
    self.write_bool(v)?;
    Ok(())
  }

  fn write_integer(&mut self, v: i32) -> SerializationResult {
    self.write_marker(Marker::Primitive)?;
    self.write_u8(4)?;
    self.write_i32(v)?;
    Ok(())
  }

  fn write_string(&mut self, v: String) -> SerializationResult {
    self.write_marker(Marker::Primitive)?;
    self.write_u8(8)?;
    self.writer.write(v.as_bytes())?; 
    Ok(())
  }

  fn write_bigint(&mut self, v: BigInt) -> SerializationResult {
    self.write_marker(Marker::Primitive)?;
    self.write_u8(9)?;
    self.writer.write(v.to_signed_bytes_be().as_slice())?; 
    Ok(())
  }
}


pub trait Serializable {
  const MARKER: Marker;

  fn serialize<W: io::Write>(&self, s: Serializer<W>);
}