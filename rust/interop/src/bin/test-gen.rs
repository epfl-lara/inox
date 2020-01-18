use stainless_interop::ser::*;
use types::*;
use std::fs;

const PATH_PREFIX: &'static str = "/home/gs/epfl/lara/inox/src/it/resources/regression/rust/";
const PATH_SUFFIX: &'static str = ".inoxser";

macro_rules! test_gen {
  ($name:ident, $body:block) => {
    fn $name() {
      let mut s = BufferSerializer::new();
      let data = $body;
      data.serialize(&mut s).unwrap();
      let path = format!("{}{}{}", PATH_PREFIX, stringify!($name), PATH_SUFFIX);
      fs::write(path, s.as_slice()).expect("Unable to write file");
    }
  }
}

macro_rules! S {
  ($s:expr) => { ($s).to_string() }
}

test_gen!(seq_of_ints, {
  vec![1, 2, 3] as Seq<Int>
});

test_gen!(many_seqs, {
  (vec![1, 2, 3], vec![true, false], vec![S!("Hello"), S!("world")])
});

test_gen!(set_of_int_tuples, {
  let mut set: Set<(Int, Int)> = Set::new();
  set.insert((1, 3));
  set.insert((2, 3));
  set.insert((1, 2));
  set.insert((-4, 5));
  set
});

test_gen!(map_of_strings_and_ints, {
  let mut map: Map<String, Int> = Map::new();
  map.insert(S!("alpha"), 123);
  map.insert(S!("bravo"), 456);
  map.insert(S!("charlie"), 789);
  map
});

test_gen!(option_of_bigint, {
  Some(123.to_bigint().unwrap())
});

fn main() {
  seq_of_ints();
  many_seqs();
  set_of_int_tuples();
  map_of_strings_and_ints();
  option_of_bigint();
}
