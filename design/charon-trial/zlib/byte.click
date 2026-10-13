theorem zlib_byte_u64(value: uint8) {
 ensures to_integer(value) <= 255 by {
  have 0 <= (int32)value by { simp(); }
  have (int32)value <= 255 by { simp(); }
  apply(int32_less_equal_to_integer(0, (int32)value));
  apply(int32_less_equal_to_integer((int32)value, 255));
  have (uint8)(int32)value == value by { normalize(); }
  have to_integer((uint8)(int32)value) == to_integer((int32)value) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer((int32)value) => 0 <= to_integer((int32)value);
   premise 1: to_integer((int32)value) <= 255 => to_integer((int32)value) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer((uint8)(int32)value) == to_integer((int32)value); conclusion 0;
  } }
  have to_integer(value) == to_integer((int32)value) by { rewrite(value == (uint8)(int32)value); assumption(); }
  arithmetic() using { to_integer(value) == to_integer((int32)value); to_integer((int32)value) <= 255; }
 }
 ensures (uint64)value <= 255u64 by {
  have 0 <= (int32)value by { simp(); }
  have (int32)value <= 255 by { simp(); }
  apply(int32_less_equal_to_integer(0, (int32)value));
  apply(int32_less_equal_to_integer((int32)value, 255));
  have to_integer((uint64)value) == to_integer((int32)value) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer((int32)value) => 0 <= to_integer((int32)value);
   premise 1: to_integer((int32)value) <= 255 => to_integer((int32)value) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer((uint64)value) == to_integer((int32)value); conclusion 0;
  } }
  have to_integer((uint64)value) <= to_integer(255u64) by { arithmetic() using {
   to_integer((uint64)value) == to_integer((int32)value);
   to_integer((int32)value) <= to_integer(255);
  } }
  apply(uint64_to_integer_less_equal_implies_less_equal((uint64)value, 255u64));
  assumption();
 }
 ensures (uint64)(uint32)value <= 255u64 by {
  have 0 <= (int32)value by { simp(); }
  have (int32)value <= 255 by { simp(); }
  apply(int32_less_equal_to_integer(0, (int32)value));
  apply(int32_less_equal_to_integer((int32)value, 255));
  have to_integer((uint32)value) == to_integer((int32)value) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer((int32)value) => 0 <= to_integer((int32)value);
   premise 1: to_integer((int32)value) <= 255 => to_integer((int32)value) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer((uint32)value) == to_integer((int32)value); conclusion 0;
  } }
  have 0 <= to_integer((uint32)value) by { rewrite(to_integer((uint32)value) == to_integer((int32)value)); assumption(); }
  have to_integer((uint32)value) <= 255 by { rewrite(to_integer((uint32)value) == to_integer((int32)value)); assumption(); }
  have to_integer((uint64)(uint32)value) == to_integer((uint32)value) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer((uint32)value) => 0 <= to_integer((uint32)value);
   premise 1: to_integer((uint32)value) <= 255 => to_integer((uint32)value) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer((uint64)(uint32)value) == to_integer((uint32)value); conclusion 0;
  } }
  have to_integer((uint64)(uint32)value) <= to_integer(255u64) by { arithmetic() using {
   to_integer((uint64)(uint32)value) == to_integer((uint32)value); to_integer((uint32)value) <= 255;
  } }
  apply(uint64_to_integer_less_equal_implies_less_equal((uint64)(uint32)value, 255u64)); assumption();
 }
 ensures to_integer((uint64)(uint32)value) == to_integer((int32)value) by {
  have 0 <= (int32)value by { simp(); }
  have (int32)value <= 255 by { simp(); }
  apply(int32_less_equal_to_integer(0, (int32)value));
  apply(int32_less_equal_to_integer((int32)value, 255));
  have to_integer((uint32)value) == to_integer((int32)value) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer((int32)value) => 0 <= to_integer((int32)value);
   premise 1: to_integer((int32)value) <= 255 => to_integer((int32)value) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer((uint32)value) == to_integer((int32)value); conclusion 0;
  } }
  have 0 <= to_integer((uint32)value) by { rewrite(to_integer((uint32)value) == to_integer((int32)value)); assumption(); }
  have to_integer((uint32)value) <= 255 by { rewrite(to_integer((uint32)value) == to_integer((int32)value)); assumption(); }
  have to_integer((uint64)(uint32)value) == to_integer((uint32)value) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer((uint32)value) => 0 <= to_integer((uint32)value);
   premise 1: to_integer((uint32)value) <= 255 => to_integer((uint32)value) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer((uint64)(uint32)value) == to_integer((uint32)value); conclusion 0;
  } }
  arithmetic() using { to_integer((uint64)(uint32)value) == to_integer((uint32)value); to_integer((uint32)value) == to_integer((int32)value); }
 }

 ensures 0 <= to_integer((int32)value) by {
  have 0 <= (int32)value by { simp(); }
  apply(int32_less_equal_to_integer(0, (int32)value)); assumption();
 }
 ensures to_integer((int32)value) <= 255 by {
  have (int32)value <= 255 by { simp(); }
  apply(int32_less_equal_to_integer((int32)value, 255)); assumption();
 }

}
