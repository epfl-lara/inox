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
      10..MAX => Marker::Generated(marker_id)
    }
  }
}

pub trait Serializable {
  const MARKER: Marker;

  fn serialize<S: Serializer<_>>(&self, s: S);
}