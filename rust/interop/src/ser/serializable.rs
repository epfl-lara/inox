use super::{marker_ids, primitive_ids, SerializationResult, Serializer, types};

// Serializable, a trait for types that can be serialized
pub trait Serializable {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult;
}

impl Serializable for types::Boolean {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(marker_ids::PRIMITIVE)?;
    s.write_u8(primitive_ids::BOOLEAN)?;
    s.write_bool(*self)?;
    Ok(())
  }
}

impl Serializable for types::Int {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(marker_ids::PRIMITIVE)?;
    s.write_u8(primitive_ids::INTEGER)?;
    s.write_i32(*self)?;
    Ok(())
  }
}

impl Serializable for types::String {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(marker_ids::PRIMITIVE)?;
    s.write_u8(primitive_ids::STRING)?;
    let bytes = self.as_bytes();
    s.write_u32(bytes.len() as u32)?;
    s.write(bytes)?;
    Ok(())
  }
}

impl Serializable for types::BigInt {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(marker_ids::PRIMITIVE)?;
    s.write_u8(primitive_ids::BIGINT)?;
    let bytes_vec = self.to_signed_bytes_be();
    let bytes = bytes_vec.as_slice();
    s.write_u32(bytes.len() as u32)?;
    s.write(bytes)?;
    Ok(())
  }
}

impl<T: Serializable> Serializable for types::Option<T> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(marker_ids::OPTION)?;
    match self {
      None => s.write_u8(0)?,
      Some(value) => {
        s.write_u8(1)?;
        value.serialize(s)?
      }
    };
    Ok(())
  }
}

impl<T: Serializable> Serializable for types::Seq<T> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(marker_ids::SEQ)?;
    s.write_length(self.len())?;
    for value in self {
      value.serialize(s)?;
    }
    Ok(())
  }
}

// TODO: Make the order in which the elements are written stable
impl<T: Serializable> Serializable for types::Set<T> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(marker_ids::SET)?;
    s.write_length(self.len())?;
    for value in self {
      value.serialize(s)?;
    }
    Ok(())
  }
}

// TODO: Make the order in which the elements are written stable
impl<K: Serializable, V: Serializable> Serializable for types::Map<K, V> {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(marker_ids::MAP)?;
    s.write_length(self.len())?;
    for (k, v) in self {
      k.serialize(s)?;
      v.serialize(s)?;
    }
    Ok(())
  }
}

impl<T1: Serializable, T2: Serializable> Serializable for (T1, T2) {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(marker_ids::TUPLE)?;
    s.write_u8(2)?;
    self.0.serialize(s)?;
    self.1.serialize(s)?;
    Ok(())
  }
}

impl<T1: Serializable, T2: Serializable, T3: Serializable> Serializable for (T1, T2, T3) {
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(marker_ids::TUPLE)?;
    s.write_u8(3)?;
    self.0.serialize(s)?;
    self.1.serialize(s)?;
    self.2.serialize(s)?;
    Ok(())
  }
}

impl<T1: Serializable, T2: Serializable, T3: Serializable, T4: Serializable> Serializable
  for (T1, T2, T3, T4)
{
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(marker_ids::TUPLE)?;
    s.write_u8(4)?;
    self.0.serialize(s)?;
    self.1.serialize(s)?;
    self.2.serialize(s)?;
    self.3.serialize(s)?;
    Ok(())
  }
}

impl<T1: Serializable, T2: Serializable, T3: Serializable, T4: Serializable, T5: Serializable>
  Serializable for (T1, T2, T3, T4, T5)
{
  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {
    s.write_marker(marker_ids::TUPLE)?;
    s.write_u8(5)?;
    self.0.serialize(s)?;
    self.1.serialize(s)?;
    self.2.serialize(s)?;
    self.3.serialize(s)?;
    self.4.serialize(s)?;
    Ok(())
  }
}