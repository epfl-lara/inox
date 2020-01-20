use stainless_interop::ast::*;
use stainless_interop::ser::*;
use std::fs;
use types::*;

const PATH_PREFIX: &'static str = "/home/gs/epfl/lara/inox/src/it/resources/regression/rust/";
const PATH_SUFFIX: &'static str = ".inoxser";

fn ser<T: Serializable, S: Serializer>(data: T, s: &mut S) {
  data.serialize(s).unwrap();
}

macro_rules! test_gen {
  ($name:ident, $s:ident => $body:block) => {
    fn $name() {
      let mut s = BufferSerializer::new();
      let $s = &mut s;
      $body
      let path = format!("{}{}{}", PATH_PREFIX, stringify!($name), PATH_SUFFIX);
      fs::write(path, s.as_slice()).expect("Unable to write file");
    }
  };
}

macro_rules! S {
  ($s:expr) => {
    ($s).to_string()
  };
}

test_gen!(seq_of_ints, s => { ser(vec![1, 2, 3] as Seq<Int>, s) });

test_gen!(many_seqs, s => {
  ser((
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
  ser(set, s)
});

test_gen!(map_of_strings_and_ints, s => {
  let mut map: Map<String, Int> = Map::new();
  map.insert(S!("alpha"), 123);
  map.insert(S!("bravo"), 456);
  map.insert(S!("charlie"), 789);
  ser(map, s)
});

test_gen!(option_of_bigint, s => { ser(Some(123.to_bigint().unwrap()), s) });

test_gen!(int32_literal, s => { ser(Int32Literal(123), s) });

test_gen!(arithmetic_expr, s => {
  let e_lit = Expr::BVLiteral(Int32Literal(1));
  let e1 = Expr::Plus(Plus { lhs: &e_lit, rhs: &e_lit });
  let e2 = Expr::Times(Times { lhs: &e1, rhs: &e_lit });
  ser(e2, s)
});

test_gen!(identity_fundef, s => {
  let id_x = Identifier { name: S!("x"), globalId: 1, id: 1 };
  let id_f = Identifier { name: S!("f"), globalId: 2, id: 1 };
  let tpe_int = Type::BVType(Int32Type());
  let v_x = Variable {
    id: &id_x,
    tpe: &tpe_int,
    flags: vec![]
  };
  let param = ValDef { v: &v_x };
  let body = Expr::Variable(v_x.clone());
  let fd = Definition::FunDef(FunDef {
    id: &id_f,
    tparams: vec![],
    params: vec![&param],
    returnType: &tpe_int,
    fullBody: &body,
    flags: vec![]
  });
  ser(fd, s)
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
}
