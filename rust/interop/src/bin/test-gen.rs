use stainless_interop::ser::*;
use std::fs;

// const OUT_FILE: &'static str = "/tmp/foo";
const OUT_FILE: &'static str =
  "/home/gs/epfl/lara/inox/src/it/resources/regression/rust/seq_of_ints.inoxser";

fn main() {
  let mut s = BufferSerializer::new();
  let ints: types::Seq<types::Int> = vec![1, 2, 3];
  assert!(ints.serialize(&mut s).is_ok());
  // assert!(true.serialize(&mut s).is_ok());
  // assert!(123.serialize(&mut s).is_ok());
  // assert!(String::from("foo").serialize(&mut s).is_ok());
  fs::write(OUT_FILE, s.as_slice()).expect("Unable to write file");
}
