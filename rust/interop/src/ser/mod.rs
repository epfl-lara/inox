#![allow(dead_code)]

extern crate num_bigint;

use std::io::{self, /*Read,*/ Write};

mod serializable;
// mod deserializable;
mod generated;

pub use serializable::Serializable;
// pub use deserializable::Deserializable;

/** == Type mapping ==
 * Boolean <-> bool
 * Int     <-> i32
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
pub mod types {
  pub type Boolean = bool;
  pub type Int = i32;
  pub type BigInt = num_bigint::BigInt;
  pub type String = std::string::String;
  pub type Option<T> = std::option::Option<T>;
  pub type Seq<T> = std::vec::Vec<T>;
  pub type Set<T> = std::collections::HashSet<T>;
  pub type Map<K, V> = std::collections::HashMap<K, V>;

  pub use num_bigint::ToBigInt;
}

#[derive(PartialEq, Eq, PartialOrd, Debug)]
pub struct MarkerId(u32);

// Some of the common marker ids
mod marker_ids {
  use super::MarkerId;
  pub const PRODUCT: MarkerId = MarkerId(0);
  pub const OPTION: MarkerId = MarkerId(1);
  pub const SEQ: MarkerId = MarkerId(2);
  pub const SET: MarkerId = MarkerId(3);
  pub const MAP: MarkerId = MarkerId(4);
  pub const PRIMITIVE: MarkerId = MarkerId(5);
  pub const TUPLE: MarkerId = MarkerId(6);
  pub const SERIALIZATIONRESULT: MarkerId = MarkerId(7);
}

// Additional ids to differentiate primitive values
mod primitive_ids {
  pub const BOOLEAN: u8 = 0;
  pub const INTEGER: u8 = 4;
  pub const STRING: u8 = 8;
  pub const BIGINT: u8 = 9;
}

// Serializer, a trait that encapsulates raw serialization operations

type SerializationResult = Result<(), io::Error>;

macro_rules! make_write_raw {
  ($id:ident, $t:ty) => {
    fn $id(&mut self, v: $t) -> SerializationResult {
      self.write(&v.to_be_bytes())?;
      Ok(())
    }
  }
}

pub trait Serializer: Sized {
  type Writer: Write;

  fn writer(&mut self) -> &mut Self::Writer;

  // Raw writing

  fn write(&mut self, data: &[u8]) -> SerializationResult {
    self.writer().write(data)?;
    Ok(())
  }

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
    self.write(&[v as u8])?;
    Ok(())
  }

  // Particulars of the stainless serializer

  fn write_marker(&mut self, marker: MarkerId) -> SerializationResult {
    let id: u32 = marker.0;
    assert!(id < 255);
    self.write_u8(id as u8)?;
    Ok(())
  }

  fn write_length(&mut self, len: usize) -> SerializationResult {
    assert!(len <= (std::i32::MAX as usize));
    if len < 255 {
      self.write_u8(len as u8)?;
    } else {
      self.write_u8(255)?;
      (len as types::Int).serialize(self)?;
    }
    Ok(())
  }
}

/*// Deserializer, a trait that encapsulates raw deserialization operations

type DeserializationResult<T> = Result<T, io::Error>;

macro_rules! make_read_raw {
  ($id:ident, $t:ty) => {
    fn $id(&mut self) -> DeserializationResult<$t> {
      let mut buffer = [0; std::mem::size_of::<$t>()];
      self.reader().read_exact(&mut buffer)?;
      let v = <$t>::from_be_bytes(buffer);
      Ok(v)
    }
  }
}

pub trait Deserializer: Sized {
  type Reader: Read;

  fn reader(&mut self) -> &mut Self::Reader;

  // Raw reading

  fn read(&mut self, length: usize) -> DeserializationResult<Vec<u8>> {
    let mut res: Vec<u8> = vec![];
    self.reader().by_ref().take(length as u64).read_to_end(&mut res)?;
    Ok(res)
  }

  make_read_raw!(read_u8, u8);
  make_read_raw!(read_i8, i8);
  make_read_raw!(read_u16, u16);
  make_read_raw!(read_i16, i16);
  make_read_raw!(read_u32, u32);
  make_read_raw!(read_i32, i32);
  make_read_raw!(read_u64, u64);
  make_read_raw!(read_i64, i64);
  make_read_raw!(read_f32, f32);
  make_read_raw!(read_f64, f64);

  fn read_bool(&mut self) -> DeserializationResult<bool> {
    let v = self.read_u8()?;
    Ok(v == 1)
  }

  // Particulars of the stainless serializer

  fn read_marker(&mut self) -> DeserializationResult<MarkerId> {
    let v = self.read_u8()?;
    assert!(v != 255);
    Ok(MarkerId(v as u32))
  }

  fn read_length(&mut self) -> DeserializationResult<usize> {
    let v1 = self.read_u8()?;
    if v1 < 255 {
      Ok(v1 as usize)
    } else {
      let v2 = types::Int::deserialize(self)?;
      Ok(v2 as usize)
    }
  }
}*/

// BufferSerializer, a simple serializer writing to a vector
pub struct BufferSerializer {
  writer: Vec<u8>,
}

impl BufferSerializer {
  pub fn new() -> Self {
    Self { writer: vec![] }
  }

  pub fn as_slice(&self) -> &[u8] {
    self.writer.as_slice()
  }
}

impl Serializer for BufferSerializer {
  type Writer = Vec<u8>;

  fn writer(&mut self) -> &mut Self::Writer {
    &mut self.writer
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_serialize1() {
    let mut s = BufferSerializer::new();
    assert!(true.serialize(&mut s).is_ok());
    assert!(123.serialize(&mut s).is_ok());
    assert!(String::from("foo").serialize(&mut s).is_ok());
    assert_eq!(s.as_slice().len(), (2 + 1) + (2 + 4) + (2 + 4 + 3));
  }
}
