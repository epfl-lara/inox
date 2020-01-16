use std::io;

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


pub struct Serializer<W: io::Write> {
  writer: W
}

impl<W: Write> Serializer<W> {
  fn new(writer: W) -> Serializer<W> {
    Serializer {
      writer
    }
  }

  fn write_boolean()
}