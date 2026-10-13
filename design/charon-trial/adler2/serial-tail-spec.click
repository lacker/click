// Checked native serial-tail sums and their connection to the common spec.
theorem adler_serial_byte_observation(value: uint8) {
 ensures to_integer((uint32)value) == to_integer((int32)value)
     and 0 <= to_integer((uint32)value) and to_integer((uint32)value) <= 255 by {
  apply(adler_byte_bounds(value));
  have to_integer((uint32)value) == to_integer((int32)value) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer((int32)value) => 0 <= to_integer((int32)value);
   premise 1: to_integer((int32)value) <= 255 => to_integer((int32)value) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer((uint32)value) == to_integer((int32)value);
   conclusion 0;
  } }
  have 0 <= to_integer((uint32)value) by {
   rewrite(to_integer((uint32)value) == to_integer((int32)value)); assumption();
  }
  have to_integer((uint32)value) <= 255 by {
   rewrite(to_integer((uint32)value) == to_integer((int32)value)); assumption();
  }
  simp();
 }
}

theorem adler_serial_two_native_result(x0: uint8, x1: uint8) {
 ensures to_integer(((1u32 + (uint32)x0) + (uint32)x1) % 65521u32) == truncating_remainder(1 + to_integer((int32)x0) + to_integer((int32)x1), 65521)
     and to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1)) % 65521u32) == truncating_remainder(2 + 2 * to_integer((int32)x0) + to_integer((int32)x1), 65521) by {
  apply(adler_serial_byte_observation(x0));
  apply(adler_byte_bounds(x0));
  apply(adler_serial_byte_observation(x1));
  apply(adler_byte_bounds(x1));
  have to_integer(1u32) + to_integer((uint32)x0) <= 4294967295 by arithmetic() using { to_integer((uint32)x0) <= 255; };
  apply(uint32_add_to_integer(1u32, (uint32)x0));
  have to_integer((1u32 + (uint32)x0)) == 1 + to_integer((int32)x0) by arithmetic() using { to_integer((1u32 + (uint32)x0)) == to_integer(1u32) + to_integer((uint32)x0); to_integer((uint32)x0) == to_integer((int32)x0); };
  have to_integer((1u32 + (uint32)x0)) <= 256 by arithmetic() using { to_integer((1u32 + (uint32)x0)) == to_integer(1u32) + to_integer((uint32)x0); to_integer((uint32)x0) <= 255; };
  have to_integer((1u32 + (uint32)x0)) + to_integer((uint32)x1) <= 4294967295 by arithmetic() using { to_integer((1u32 + (uint32)x0)) <= 256; to_integer((uint32)x1) <= 255; };
  apply(uint32_add_to_integer((1u32 + (uint32)x0), (uint32)x1));
  have to_integer(((1u32 + (uint32)x0) + (uint32)x1)) == 1 + to_integer((int32)x0) + to_integer((int32)x1) by arithmetic() using { to_integer(((1u32 + (uint32)x0) + (uint32)x1)) == to_integer((1u32 + (uint32)x0)) + to_integer((uint32)x1); to_integer((1u32 + (uint32)x0)) == 1 + to_integer((int32)x0); to_integer((uint32)x1) == to_integer((int32)x1); };
  have to_integer(((1u32 + (uint32)x0) + (uint32)x1)) <= 511 by arithmetic() using { to_integer(((1u32 + (uint32)x0) + (uint32)x1)) == to_integer((1u32 + (uint32)x0)) + to_integer((uint32)x1); to_integer((1u32 + (uint32)x0)) <= 256; to_integer((uint32)x1) <= 255; };
  have to_integer(393126u32) + to_integer((1u32 + (uint32)x0)) <= 4294967295 by arithmetic() using { to_integer((1u32 + (uint32)x0)) <= 256; };
  apply(uint32_add_to_integer(393126u32, (1u32 + (uint32)x0)));
  have to_integer((393126u32 + (1u32 + (uint32)x0))) == 393126 + 1 + to_integer((int32)x0) by arithmetic() using { to_integer((393126u32 + (1u32 + (uint32)x0))) == to_integer(393126u32) + to_integer((1u32 + (uint32)x0)); to_integer((1u32 + (uint32)x0)) == 1 + to_integer((int32)x0); };
  have to_integer((393126u32 + (1u32 + (uint32)x0))) <= 393382 by arithmetic() using { to_integer((393126u32 + (1u32 + (uint32)x0))) == to_integer(393126u32) + to_integer((1u32 + (uint32)x0)); to_integer((1u32 + (uint32)x0)) <= 256; };
  have to_integer((393126u32 + (1u32 + (uint32)x0))) + to_integer(((1u32 + (uint32)x0) + (uint32)x1)) <= 4294967295 by arithmetic() using { to_integer((393126u32 + (1u32 + (uint32)x0))) <= 393382; to_integer(((1u32 + (uint32)x0) + (uint32)x1)) <= 511; };
  apply(uint32_add_to_integer((393126u32 + (1u32 + (uint32)x0)), ((1u32 + (uint32)x0) + (uint32)x1)));
  have to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1))) == 393126 + 2 + 2 * to_integer((int32)x0) + to_integer((int32)x1) by arithmetic() using { to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1))) == to_integer((393126u32 + (1u32 + (uint32)x0))) + to_integer(((1u32 + (uint32)x0) + (uint32)x1)); to_integer((393126u32 + (1u32 + (uint32)x0))) == 393126 + 1 + to_integer((int32)x0); to_integer(((1u32 + (uint32)x0) + (uint32)x1)) == 1 + to_integer((int32)x0) + to_integer((int32)x1); };
  have to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1))) <= 393893 by arithmetic() using { to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1))) == to_integer((393126u32 + (1u32 + (uint32)x0))) + to_integer(((1u32 + (uint32)x0) + (uint32)x1)); to_integer((393126u32 + (1u32 + (uint32)x0))) <= 393382; to_integer(((1u32 + (uint32)x0) + (uint32)x1)) <= 511; };
  apply(uint32_remainder_to_integer(((1u32 + (uint32)x0) + (uint32)x1), 65521u32));
  apply(uint32_remainder_to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1)), 65521u32));
  have 0 <= 2 + 2 * to_integer((int32)x0) + to_integer((int32)x1) by { arithmetic_certificate {
   premise 0: 0 <= to_integer((int32)x0) => 0 <= to_integer((int32)x0);
   scale 0 by 2 => 0 <= 2 * to_integer((int32)x0);
   premise 1: 0 <= to_integer((int32)x1) => 0 <= to_integer((int32)x1);
   trivial => 0 <= 2;
   add 3, 1 => 0 <= 2 + 2 * to_integer((int32)x0);
   add 4, 2 => 0 <= 2 + 2 * to_integer((int32)x0) + to_integer((int32)x1);
   conclusion 5;
  } }
  have 0 <= 393126 + 2 + 2 * to_integer((int32)x0) + to_integer((int32)x1) by arithmetic() using { 0 <= 2 + 2 * to_integer((int32)x0) + to_integer((int32)x1); };
  have 393126 + 2 + 2 * to_integer((int32)x0) + to_integer((int32)x1) == (2 + 2 * to_integer((int32)x0) + to_integer((int32)x1)) + 65521 * 6 by arithmetic() using {};
  apply(adler_residue_congruent(393126 + 2 + 2 * to_integer((int32)x0) + to_integer((int32)x1), 2 + 2 * to_integer((int32)x0) + to_integer((int32)x1), 6));
  have to_integer(((1u32 + (uint32)x0) + (uint32)x1) % 65521u32) == truncating_remainder(1 + to_integer((int32)x0) + to_integer((int32)x1), 65521) by {
   rewrite(to_integer(((1u32 + (uint32)x0) + (uint32)x1) % 65521u32) == truncating_remainder(to_integer(((1u32 + (uint32)x0) + (uint32)x1)), to_integer(65521u32)));
   rewrite(to_integer(((1u32 + (uint32)x0) + (uint32)x1)) == 1 + to_integer((int32)x0) + to_integer((int32)x1));
   normalize();
  }
  have to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1)) % 65521u32) == truncating_remainder(2 + 2 * to_integer((int32)x0) + to_integer((int32)x1), 65521) by {
   rewrite(to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1)) % 65521u32) == truncating_remainder(to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1))), to_integer(65521u32)));
   rewrite(to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1))) == 393126 + 2 + 2 * to_integer((int32)x0) + to_integer((int32)x1));
   rewrite(truncating_remainder(393126 + 2 + 2 * to_integer((int32)x0) + to_integer((int32)x1), 65521) == truncating_remainder(2 + 2 * to_integer((int32)x0) + to_integer((int32)x1), 65521));
   normalize();
  }
  simp();
 }
}

theorem adler_serial_two_result_spec(bytes: uint8[]) {
 ensures to_integer(((1u32 + (uint32)bytes[0]) + (uint32)bytes[1]) % 65521u32) == adler_spec_a(bytes, 2, 1) by {
  apply(adler_spec_two(bytes));
  apply(adler_serial_two_native_result(bytes[0], bytes[1]));
  rewrite(adler_spec_a(bytes, 2, 1) == truncating_remainder(1 + to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]), 65521));
  assumption();
 }
 ensures to_integer(((393126u32 + (1u32 + (uint32)bytes[0])) + ((1u32 + (uint32)bytes[0]) + (uint32)bytes[1])) % 65521u32) == adler_spec_b(bytes, 2, 1, 0) by {
  apply(adler_spec_two(bytes));
  apply(adler_serial_two_native_result(bytes[0], bytes[1]));
  rewrite(adler_spec_b(bytes, 2, 1, 0) == truncating_remainder(2 + 2 * to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]), 65521));
  assumption();
 }
}

theorem adler_serial_three_native_result(x0: uint8, x1: uint8, x2: uint8) {
 ensures to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2) % 65521u32) == truncating_remainder(1 + to_integer((int32)x0) + to_integer((int32)x1) + to_integer((int32)x2), 65521)
     and to_integer((((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1)) + (((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) % 65521u32) == truncating_remainder(3 + 3 * to_integer((int32)x0) + 2 * to_integer((int32)x1) + to_integer((int32)x2), 65521) by {
  apply(adler_serial_byte_observation(x0));
  apply(adler_byte_bounds(x0));
  apply(adler_serial_byte_observation(x1));
  apply(adler_byte_bounds(x1));
  apply(adler_serial_byte_observation(x2));
  apply(adler_byte_bounds(x2));
  have to_integer(1u32) + to_integer((uint32)x0) <= 4294967295 by arithmetic() using { to_integer((uint32)x0) <= 255; };
  apply(uint32_add_to_integer(1u32, (uint32)x0));
  have to_integer((1u32 + (uint32)x0)) == 1 + to_integer((int32)x0) by arithmetic() using { to_integer((1u32 + (uint32)x0)) == to_integer(1u32) + to_integer((uint32)x0); to_integer((uint32)x0) == to_integer((int32)x0); };
  have to_integer((1u32 + (uint32)x0)) <= 256 by arithmetic() using { to_integer((1u32 + (uint32)x0)) == to_integer(1u32) + to_integer((uint32)x0); to_integer((uint32)x0) <= 255; };
  have to_integer((1u32 + (uint32)x0)) + to_integer((uint32)x1) <= 4294967295 by arithmetic() using { to_integer((1u32 + (uint32)x0)) <= 256; to_integer((uint32)x1) <= 255; };
  apply(uint32_add_to_integer((1u32 + (uint32)x0), (uint32)x1));
  have to_integer(((1u32 + (uint32)x0) + (uint32)x1)) == 1 + to_integer((int32)x0) + to_integer((int32)x1) by arithmetic() using { to_integer(((1u32 + (uint32)x0) + (uint32)x1)) == to_integer((1u32 + (uint32)x0)) + to_integer((uint32)x1); to_integer((1u32 + (uint32)x0)) == 1 + to_integer((int32)x0); to_integer((uint32)x1) == to_integer((int32)x1); };
  have to_integer(((1u32 + (uint32)x0) + (uint32)x1)) <= 511 by arithmetic() using { to_integer(((1u32 + (uint32)x0) + (uint32)x1)) == to_integer((1u32 + (uint32)x0)) + to_integer((uint32)x1); to_integer((1u32 + (uint32)x0)) <= 256; to_integer((uint32)x1) <= 255; };
  have to_integer(((1u32 + (uint32)x0) + (uint32)x1)) + to_integer((uint32)x2) <= 4294967295 by arithmetic() using { to_integer(((1u32 + (uint32)x0) + (uint32)x1)) <= 511; to_integer((uint32)x2) <= 255; };
  apply(uint32_add_to_integer(((1u32 + (uint32)x0) + (uint32)x1), (uint32)x2));
  have to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) == 1 + to_integer((int32)x0) + to_integer((int32)x1) + to_integer((int32)x2) by arithmetic() using { to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) == to_integer(((1u32 + (uint32)x0) + (uint32)x1)) + to_integer((uint32)x2); to_integer(((1u32 + (uint32)x0) + (uint32)x1)) == 1 + to_integer((int32)x0) + to_integer((int32)x1); to_integer((uint32)x2) == to_integer((int32)x2); };
  have to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) <= 766 by arithmetic() using { to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) == to_integer(((1u32 + (uint32)x0) + (uint32)x1)) + to_integer((uint32)x2); to_integer(((1u32 + (uint32)x0) + (uint32)x1)) <= 511; to_integer((uint32)x2) <= 255; };
  have to_integer(393126u32) + to_integer((1u32 + (uint32)x0)) <= 4294967295 by arithmetic() using { to_integer((1u32 + (uint32)x0)) <= 256; };
  apply(uint32_add_to_integer(393126u32, (1u32 + (uint32)x0)));
  have to_integer((393126u32 + (1u32 + (uint32)x0))) == 393126 + 1 + to_integer((int32)x0) by arithmetic() using { to_integer((393126u32 + (1u32 + (uint32)x0))) == to_integer(393126u32) + to_integer((1u32 + (uint32)x0)); to_integer((1u32 + (uint32)x0)) == 1 + to_integer((int32)x0); };
  have to_integer((393126u32 + (1u32 + (uint32)x0))) <= 393382 by arithmetic() using { to_integer((393126u32 + (1u32 + (uint32)x0))) == to_integer(393126u32) + to_integer((1u32 + (uint32)x0)); to_integer((1u32 + (uint32)x0)) <= 256; };
  have to_integer((393126u32 + (1u32 + (uint32)x0))) + to_integer(((1u32 + (uint32)x0) + (uint32)x1)) <= 4294967295 by arithmetic() using { to_integer((393126u32 + (1u32 + (uint32)x0))) <= 393382; to_integer(((1u32 + (uint32)x0) + (uint32)x1)) <= 511; };
  apply(uint32_add_to_integer((393126u32 + (1u32 + (uint32)x0)), ((1u32 + (uint32)x0) + (uint32)x1)));
  have to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1))) == 393126 + 2 + 2 * to_integer((int32)x0) + to_integer((int32)x1) by arithmetic() using { to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1))) == to_integer((393126u32 + (1u32 + (uint32)x0))) + to_integer(((1u32 + (uint32)x0) + (uint32)x1)); to_integer((393126u32 + (1u32 + (uint32)x0))) == 393126 + 1 + to_integer((int32)x0); to_integer(((1u32 + (uint32)x0) + (uint32)x1)) == 1 + to_integer((int32)x0) + to_integer((int32)x1); };
  have to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1))) <= 393893 by arithmetic() using { to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1))) == to_integer((393126u32 + (1u32 + (uint32)x0))) + to_integer(((1u32 + (uint32)x0) + (uint32)x1)); to_integer((393126u32 + (1u32 + (uint32)x0))) <= 393382; to_integer(((1u32 + (uint32)x0) + (uint32)x1)) <= 511; };
  have to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1))) + to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) <= 4294967295 by arithmetic() using { to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1))) <= 393893; to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) <= 766; };
  apply(uint32_add_to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1)), (((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)));
  have to_integer((((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1)) + (((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2))) == 393126 + 3 + 3 * to_integer((int32)x0) + 2 * to_integer((int32)x1) + to_integer((int32)x2) by {
   rewrite(to_integer((((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1)) + (((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2))) == to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1))) + to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)));
   rewrite(to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1))) == 393126 + 2 + 2 * to_integer((int32)x0) + to_integer((int32)x1));
   rewrite(to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) == 1 + to_integer((int32)x0) + to_integer((int32)x1) + to_integer((int32)x2));
   arithmetic() using {};
  }
  have to_integer((((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1)) + (((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2))) <= 394659 by arithmetic() using { to_integer((((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1)) + (((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2))) == to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1))) + to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)); to_integer(((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1))) <= 393893; to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) <= 766; };
  apply(uint32_remainder_to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2), 65521u32));
  apply(uint32_remainder_to_integer((((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1)) + (((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)), 65521u32));
  have 0 <= 3 + 3 * to_integer((int32)x0) + 2 * to_integer((int32)x1) + to_integer((int32)x2) by { arithmetic_certificate {
   premise 0: 0 <= to_integer((int32)x0) => 0 <= to_integer((int32)x0);
   scale 0 by 3 => 0 <= 3 * to_integer((int32)x0);
   premise 1: 0 <= to_integer((int32)x1) => 0 <= to_integer((int32)x1);
   scale 2 by 2 => 0 <= 2 * to_integer((int32)x1);
   premise 2: 0 <= to_integer((int32)x2) => 0 <= to_integer((int32)x2);
   trivial => 0 <= 3;
   add 5, 1 => 0 <= 3 + 3 * to_integer((int32)x0);
   add 6, 3 => 0 <= 3 + 3 * to_integer((int32)x0) + 2 * to_integer((int32)x1);
   add 7, 4 => 0 <= 3 + 3 * to_integer((int32)x0) + 2 * to_integer((int32)x1) + to_integer((int32)x2);
   conclusion 8;
  } }
  have 0 <= 393126 + 3 + 3 * to_integer((int32)x0) + 2 * to_integer((int32)x1) + to_integer((int32)x2) by arithmetic() using { 0 <= 3 + 3 * to_integer((int32)x0) + 2 * to_integer((int32)x1) + to_integer((int32)x2); };
  have 393126 + 3 + 3 * to_integer((int32)x0) + 2 * to_integer((int32)x1) + to_integer((int32)x2) == (3 + 3 * to_integer((int32)x0) + 2 * to_integer((int32)x1) + to_integer((int32)x2)) + 65521 * 6 by arithmetic() using {};
  apply(adler_residue_congruent(393126 + 3 + 3 * to_integer((int32)x0) + 2 * to_integer((int32)x1) + to_integer((int32)x2), 3 + 3 * to_integer((int32)x0) + 2 * to_integer((int32)x1) + to_integer((int32)x2), 6));
  have to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2) % 65521u32) == truncating_remainder(1 + to_integer((int32)x0) + to_integer((int32)x1) + to_integer((int32)x2), 65521) by {
   rewrite(to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2) % 65521u32) == truncating_remainder(to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)), to_integer(65521u32)));
   rewrite(to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) == 1 + to_integer((int32)x0) + to_integer((int32)x1) + to_integer((int32)x2));
   normalize();
  }
  have to_integer((((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1)) + (((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) % 65521u32) == truncating_remainder(3 + 3 * to_integer((int32)x0) + 2 * to_integer((int32)x1) + to_integer((int32)x2), 65521) by {
   rewrite(to_integer((((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1)) + (((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) % 65521u32) == truncating_remainder(to_integer((((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1)) + (((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2))), to_integer(65521u32)));
   rewrite(to_integer((((393126u32 + (1u32 + (uint32)x0)) + ((1u32 + (uint32)x0) + (uint32)x1)) + (((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2))) == 393126 + 3 + 3 * to_integer((int32)x0) + 2 * to_integer((int32)x1) + to_integer((int32)x2));
   rewrite(truncating_remainder(393126 + 3 + 3 * to_integer((int32)x0) + 2 * to_integer((int32)x1) + to_integer((int32)x2), 65521) == truncating_remainder(3 + 3 * to_integer((int32)x0) + 2 * to_integer((int32)x1) + to_integer((int32)x2), 65521));
   normalize();
  }
  simp();
 }
}

theorem adler_serial_three_result_spec(bytes: uint8[]) {
 ensures to_integer((((1u32 + (uint32)bytes[0]) + (uint32)bytes[1]) + (uint32)bytes[2]) % 65521u32) == adler_spec_a(bytes, 3, 1) by {
  apply(adler_spec_three(bytes));
  apply(adler_serial_three_native_result(bytes[0], bytes[1], bytes[2]));
  rewrite(adler_spec_a(bytes, 3, 1) == truncating_remainder(1 + to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]) + to_integer((int32)bytes[2]), 65521));
  assumption();
 }
 ensures to_integer((((393126u32 + (1u32 + (uint32)bytes[0])) + ((1u32 + (uint32)bytes[0]) + (uint32)bytes[1])) + (((1u32 + (uint32)bytes[0]) + (uint32)bytes[1]) + (uint32)bytes[2])) % 65521u32) == adler_spec_b(bytes, 3, 1, 0) by {
  apply(adler_spec_three(bytes));
  apply(adler_serial_three_native_result(bytes[0], bytes[1], bytes[2]));
  rewrite(adler_spec_b(bytes, 3, 1, 0) == truncating_remainder(3 + 3 * to_integer((int32)bytes[0]) + 2 * to_integer((int32)bytes[1]) + to_integer((int32)bytes[2]), 65521));
  assumption();
 }
}
