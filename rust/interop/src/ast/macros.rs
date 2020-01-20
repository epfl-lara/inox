/// Derive From<&t_conc> for t_abs and AsRef for t_conc
macro_rules! derive_conversions_for_ast {
  ($t_abs:tt <'a>, $t_conc:tt <'a>) => {
    impl<'a> From<&'a $t_conc<'a>> for $t_abs<'a> {
      fn from(v: &'a $t_conc<'a>) -> Self {
        $t_abs::$t_conc(v)
      }
    }

    impl<'a> From<&'a mut $t_conc<'a>> for $t_abs<'a> {
      fn from(v: &'a mut $t_conc<'a>) -> Self {
        $t_abs::$t_conc(v)
      }
    }

    impl<'a> AsRef<$t_conc<'a>> for $t_conc<'a> {
      fn as_ref(&self) -> &Self { self }
    }
  };

  ($t_abs:tt <'a>, $t_conc:tt) => {
    impl<'a> From<&'a $t_conc> for $t_abs<'a> {
      fn from(v: &'a $t_conc) -> Self {
        $t_abs::$t_conc(v)
      }
    }

    impl<'a> From<&'a mut $t_conc> for $t_abs<'a> {
      fn from(v: &'a mut $t_conc) -> Self {
        $t_abs::$t_conc(v)
      }
    }
  }
}