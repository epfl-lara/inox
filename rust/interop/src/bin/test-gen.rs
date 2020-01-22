extern crate lazy_static;

use lazy_static::lazy_static;
use stainless_interop::ast::*;
use stainless_interop::ser::*;
use types::*;

lazy_static! {
  static ref PATH_PREFIX: String = {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
      eprintln!("Usage: {} path/to/write/tests/", args[0]);
      std::process::exit(1);
    }
    args[1].clone()
  };
}
const PATH_SUFFIX: &'static str = ".inoxser";

macro_rules! test_gen {
  ($name:ident, $s:ident => $body:block) => {
    fn $name() {
      let mut s = BufferSerializer::new();
      let $s = &mut s;
      $body
      let path = format!("{}{}{}", *PATH_PREFIX, stringify!($name), PATH_SUFFIX);
      std::fs::write(path, s.as_slice()).expect("Unable to write file");
    }
  };
}

macro_rules! S {
  ($s:expr) => {
    ($s).to_string()
  };
}

macro_rules! ser {
  ($v:expr, $s:ident) => {
    $v.serialize($s).unwrap()
  };
}

test_gen!(seq_of_ints, s => { ser!(vec![1, 2, 3] as Seq<Int>, s) });

test_gen!(many_seqs, s => {
  ser!((
    vec![1, 2, 3],
    vec![true, false],
    vec![S!("Hello"), S!("world")],
  ), s)
});

test_gen!(set_of_int_tuples, s => {
  let mut set: Set<(Int, Int)> = Set::new();
  set.insert((1, 3));
  set.insert((2, 3));
  set.insert((1, 2));
  set.insert((-4, 5));
  ser!(set, s)
});

test_gen!(map_of_strings_and_ints, s => {
  let mut map: Map<String, Int> = Map::new();
  map.insert(S!("alpha"), 123);
  map.insert(S!("bravo"), 456);
  map.insert(S!("charlie"), 789);
  ser!(map, s)
});

test_gen!(option_of_bigint, s => { ser!(Some(123.to_bigint().unwrap()), s) });

test_gen!(int32_literal, s => { ser!(Int32Literal(123), s) });

test_gen!(arithmetic_expr, s => {
  let f = Factory::new();
  let one: Expr = f.Int32Literal(1).into();
  let e = f.Times(f.Plus(one, one).into(), one);
  ser!(e, s)
});

fn make_identity_fundef<'a>(f: &'a Factory) -> &'a FunDef<'a> {
  let id_x = f.Identifier(S!("x"), 1, 1);
  let id_f = f.Identifier(S!("f"), 2, 1);
  let tpe_int: Type = f.Int32Type().into();
  let v_x: &'a _ = f.Variable(id_x, tpe_int, vec![]);
  let param: &'a _ = f.ValDef(v_x);
  let body: Expr = v_x.into();
  f.FunDef(
    id_f,
    vec![],
    vec![&param],
    tpe_int,
    body,
    vec![]
  )
}

test_gen!(identity_fundef, s => {
  let f = Factory::new();
  let fd = make_identity_fundef(&f);
  ser!(fd, s)
});

test_gen!(identity_symbols, s => {
  let f = Factory::new();
  let fd = make_identity_fundef(&f);
  let mut functions = Map::new();
  functions.insert(fd.id, fd);
  let symbols = Symbols {
    sorts: Map::new(),
    functions: functions
  };
  ser!(symbols, s)
});

fn main() {
  seq_of_ints();
  many_seqs();
  set_of_int_tuples();
  map_of_strings_and_ints();
  option_of_bigint();
  int32_literal();
  arithmetic_expr();
  identity_fundef();
  identity_symbols();
}
