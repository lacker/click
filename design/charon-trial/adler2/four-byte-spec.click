// Checked bridge from the original four-byte recombination to the common spec.
// Assemble after design/adler32-spec.click. No computation summary is assumed.

theorem adler_four_byte_native_result(x0: uint8, x1: uint8, x2: uint8, x3: uint8) {
 ensures to_integer(((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2) + (uint32)x3) % 65521u32) == truncating_remainder(1 + to_integer((int32)x0) + to_integer((int32)x1) + to_integer((int32)x2) + to_integer((int32)x3), 65521)
     and to_integer(((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) + (((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))) % 65521u32) == truncating_remainder(4 + 4 * to_integer((int32)x0) + 3 * to_integer((int32)x1) + 2 * to_integer((int32)x2) + to_integer((int32)x3), 65521) by {
 apply(adler_byte_bounds(x0));
 have to_integer((uint32)x0) == to_integer((int32)x0) by { arithmetic_certificate rules {
  premise 0: 0 <= to_integer((int32)x0) => 0 <= to_integer((int32)x0);
  premise 1: to_integer((int32)x0) <= 255 => to_integer((int32)x0) <= 255;
  integer_cast_identity bounds [0, 1] => to_integer((uint32)x0) == to_integer((int32)x0); conclusion 0;
 } }
 have 0 <= to_integer((uint32)x0) by arithmetic() using { to_integer((uint32)x0) == to_integer((int32)x0); 0 <= to_integer((int32)x0); to_integer((int32)x0) <= 255; };
 have to_integer((uint32)x0) <= 255 by arithmetic() using { to_integer((uint32)x0) == to_integer((int32)x0); 0 <= to_integer((int32)x0); to_integer((int32)x0) <= 255; };
 apply(adler_byte_bounds(x1));
 have to_integer((uint32)x1) == to_integer((int32)x1) by { arithmetic_certificate rules {
  premise 0: 0 <= to_integer((int32)x1) => 0 <= to_integer((int32)x1);
  premise 1: to_integer((int32)x1) <= 255 => to_integer((int32)x1) <= 255;
  integer_cast_identity bounds [0, 1] => to_integer((uint32)x1) == to_integer((int32)x1); conclusion 0;
 } }
 have 0 <= to_integer((uint32)x1) by arithmetic() using { to_integer((uint32)x1) == to_integer((int32)x1); 0 <= to_integer((int32)x1); to_integer((int32)x1) <= 255; };
 have to_integer((uint32)x1) <= 255 by arithmetic() using { to_integer((uint32)x1) == to_integer((int32)x1); 0 <= to_integer((int32)x1); to_integer((int32)x1) <= 255; };
 apply(adler_byte_bounds(x2));
 have to_integer((uint32)x2) == to_integer((int32)x2) by { arithmetic_certificate rules {
  premise 0: 0 <= to_integer((int32)x2) => 0 <= to_integer((int32)x2);
  premise 1: to_integer((int32)x2) <= 255 => to_integer((int32)x2) <= 255;
  integer_cast_identity bounds [0, 1] => to_integer((uint32)x2) == to_integer((int32)x2); conclusion 0;
 } }
 have 0 <= to_integer((uint32)x2) by arithmetic() using { to_integer((uint32)x2) == to_integer((int32)x2); 0 <= to_integer((int32)x2); to_integer((int32)x2) <= 255; };
 have to_integer((uint32)x2) <= 255 by arithmetic() using { to_integer((uint32)x2) == to_integer((int32)x2); 0 <= to_integer((int32)x2); to_integer((int32)x2) <= 255; };
 apply(adler_byte_bounds(x3));
 have to_integer((uint32)x3) == to_integer((int32)x3) by { arithmetic_certificate rules {
  premise 0: 0 <= to_integer((int32)x3) => 0 <= to_integer((int32)x3);
  premise 1: to_integer((int32)x3) <= 255 => to_integer((int32)x3) <= 255;
  integer_cast_identity bounds [0, 1] => to_integer((uint32)x3) == to_integer((int32)x3); conclusion 0;
 } }
 have 0 <= to_integer((uint32)x3) by arithmetic() using { to_integer((uint32)x3) == to_integer((int32)x3); 0 <= to_integer((int32)x3); to_integer((int32)x3) <= 255; };
 have to_integer((uint32)x3) <= 255 by arithmetic() using { to_integer((uint32)x3) == to_integer((int32)x3); 0 <= to_integer((int32)x3); to_integer((int32)x3) <= 255; };
 have to_integer(1u32) + to_integer((uint32)x0) <= 4294967295 by arithmetic() using { to_integer((uint32)x0) <= 255; };
 apply(uint32_add_to_integer(1u32, (uint32)x0)) using { to_integer(1u32) + to_integer((uint32)x0) <= 4294967295; }
 have to_integer((1u32 + (uint32)x0)) == (1 + to_integer((int32)x0)) by {
  rewrite(to_integer((1u32 + (uint32)x0)) == to_integer(1u32) + to_integer((uint32)x0));
  rewrite(to_integer((uint32)x0) == to_integer((int32)x0));
  normalize();
 }
 have 1 <= to_integer((1u32 + (uint32)x0)) by arithmetic() using { to_integer((1u32 + (uint32)x0)) == to_integer(1u32) + to_integer((uint32)x0); 0 <= to_integer((uint32)x0); to_integer((uint32)x0) <= 255; };
 have to_integer((1u32 + (uint32)x0)) <= 256 by arithmetic() using { to_integer((1u32 + (uint32)x0)) == to_integer(1u32) + to_integer((uint32)x0); 0 <= to_integer((uint32)x0); to_integer((uint32)x0) <= 255; };
 have to_integer((1u32 + (uint32)x0)) + to_integer((uint32)x1) <= 4294967295 by arithmetic() using { to_integer((1u32 + (uint32)x0)) <= 256; to_integer((uint32)x1) <= 255; };
 apply(uint32_add_to_integer((1u32 + (uint32)x0), (uint32)x1)) using { to_integer((1u32 + (uint32)x0)) + to_integer((uint32)x1) <= 4294967295; }
 have to_integer(((1u32 + (uint32)x0) + (uint32)x1)) == ((1 + to_integer((int32)x0)) + to_integer((int32)x1)) by {
  rewrite(to_integer(((1u32 + (uint32)x0) + (uint32)x1)) == to_integer((1u32 + (uint32)x0)) + to_integer((uint32)x1));
  rewrite(to_integer((1u32 + (uint32)x0)) == (1 + to_integer((int32)x0)));
  rewrite(to_integer((uint32)x1) == to_integer((int32)x1));
  normalize();
 }
 have 1 <= to_integer(((1u32 + (uint32)x0) + (uint32)x1)) by arithmetic() using { to_integer(((1u32 + (uint32)x0) + (uint32)x1)) == to_integer((1u32 + (uint32)x0)) + to_integer((uint32)x1); 1 <= to_integer((1u32 + (uint32)x0)); to_integer((1u32 + (uint32)x0)) <= 256; 0 <= to_integer((uint32)x1); to_integer((uint32)x1) <= 255; };
 have to_integer(((1u32 + (uint32)x0) + (uint32)x1)) <= 511 by arithmetic() using { to_integer(((1u32 + (uint32)x0) + (uint32)x1)) == to_integer((1u32 + (uint32)x0)) + to_integer((uint32)x1); 1 <= to_integer((1u32 + (uint32)x0)); to_integer((1u32 + (uint32)x0)) <= 256; 0 <= to_integer((uint32)x1); to_integer((uint32)x1) <= 255; };
 have to_integer(((1u32 + (uint32)x0) + (uint32)x1)) + to_integer((uint32)x2) <= 4294967295 by arithmetic() using { to_integer(((1u32 + (uint32)x0) + (uint32)x1)) <= 511; to_integer((uint32)x2) <= 255; };
 apply(uint32_add_to_integer(((1u32 + (uint32)x0) + (uint32)x1), (uint32)x2)) using { to_integer(((1u32 + (uint32)x0) + (uint32)x1)) + to_integer((uint32)x2) <= 4294967295; }
 have to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) == (((1 + to_integer((int32)x0)) + to_integer((int32)x1)) + to_integer((int32)x2)) by {
  rewrite(to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) == to_integer(((1u32 + (uint32)x0) + (uint32)x1)) + to_integer((uint32)x2));
  rewrite(to_integer(((1u32 + (uint32)x0) + (uint32)x1)) == ((1 + to_integer((int32)x0)) + to_integer((int32)x1)));
  rewrite(to_integer((uint32)x2) == to_integer((int32)x2));
  normalize();
 }
 have 1 <= to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) by arithmetic() using { to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) == to_integer(((1u32 + (uint32)x0) + (uint32)x1)) + to_integer((uint32)x2); 1 <= to_integer(((1u32 + (uint32)x0) + (uint32)x1)); to_integer(((1u32 + (uint32)x0) + (uint32)x1)) <= 511; 0 <= to_integer((uint32)x2); to_integer((uint32)x2) <= 255; };
 have to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) <= 766 by arithmetic() using { to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) == to_integer(((1u32 + (uint32)x0) + (uint32)x1)) + to_integer((uint32)x2); 1 <= to_integer(((1u32 + (uint32)x0) + (uint32)x1)); to_integer(((1u32 + (uint32)x0) + (uint32)x1)) <= 511; 0 <= to_integer((uint32)x2); to_integer((uint32)x2) <= 255; };
 have to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) + to_integer((uint32)x3) <= 4294967295 by arithmetic() using { to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) <= 766; to_integer((uint32)x3) <= 255; };
 apply(uint32_add_to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2), (uint32)x3)) using { to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) + to_integer((uint32)x3) <= 4294967295; }
 have to_integer(((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2) + (uint32)x3)) == ((((1 + to_integer((int32)x0)) + to_integer((int32)x1)) + to_integer((int32)x2)) + to_integer((int32)x3)) by {
  rewrite(to_integer(((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2) + (uint32)x3)) == to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) + to_integer((uint32)x3));
  rewrite(to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) == (((1 + to_integer((int32)x0)) + to_integer((int32)x1)) + to_integer((int32)x2)));
  rewrite(to_integer((uint32)x3) == to_integer((int32)x3));
  normalize();
 }
 have 1 <= to_integer(((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2) + (uint32)x3)) by arithmetic() using { to_integer(((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2) + (uint32)x3)) == to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) + to_integer((uint32)x3); 1 <= to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)); to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) <= 766; 0 <= to_integer((uint32)x3); to_integer((uint32)x3) <= 255; };
 have to_integer(((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2) + (uint32)x3)) <= 1021 by arithmetic() using { to_integer(((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2) + (uint32)x3)) == to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) + to_integer((uint32)x3); 1 <= to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)); to_integer((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2)) <= 766; 0 <= to_integer((uint32)x3); to_integer((uint32)x3) <= 255; };
 have to_integer((uint32)x0) <= 1073741823 by arithmetic() using { to_integer((uint32)x0) <= 255; };
 apply(uint32_to_integer_less_equal_implies_less_equal((uint32)x0, 1073741823u32));
 have (uint32)x0 <= 4294967295u32 / 4u32 by simp() using { (uint32)x0 <= 1073741823u32; };
 have 4u32 == 0u32 or (uint32)x0 <= 4294967295u32 / 4u32 by assumption();
 apply(uint32_multiply_to_integer((uint32)x0, 4u32)) using { 4u32 == 0u32 or (uint32)x0 <= 4294967295u32 / 4u32; }
 have to_integer(((uint32)x0 * 4u32)) == (to_integer((int32)x0) * 4) by {
  rewrite(to_integer(((uint32)x0 * 4u32)) == to_integer((uint32)x0) * to_integer(4u32));
  rewrite(to_integer((uint32)x0) == to_integer((int32)x0));
  normalize();
 }
 have 0 <= to_integer(((uint32)x0 * 4u32)) by arithmetic() using { to_integer(((uint32)x0 * 4u32)) == to_integer((uint32)x0) * to_integer(4u32); 0 <= to_integer((uint32)x0); to_integer((uint32)x0) <= 255; };
 have to_integer(((uint32)x0 * 4u32)) <= 1020 by arithmetic() using { to_integer(((uint32)x0 * 4u32)) == to_integer((uint32)x0) * to_integer(4u32); 0 <= to_integer((uint32)x0); to_integer((uint32)x0) <= 255; };
 have to_integer(4u32) + to_integer(((uint32)x0 * 4u32)) <= 4294967295 by arithmetic() using { to_integer(((uint32)x0 * 4u32)) <= 1020; };
 apply(uint32_add_to_integer(4u32, ((uint32)x0 * 4u32))) using { to_integer(4u32) + to_integer(((uint32)x0 * 4u32)) <= 4294967295; }
 have to_integer((4u32 + ((uint32)x0 * 4u32))) == (4 + (to_integer((int32)x0) * 4)) by {
  rewrite(to_integer((4u32 + ((uint32)x0 * 4u32))) == to_integer(4u32) + to_integer(((uint32)x0 * 4u32)));
  rewrite(to_integer(((uint32)x0 * 4u32)) == (to_integer((int32)x0) * 4));
  normalize();
 }
 have 4 <= to_integer((4u32 + ((uint32)x0 * 4u32))) by arithmetic() using { to_integer((4u32 + ((uint32)x0 * 4u32))) == to_integer(4u32) + to_integer(((uint32)x0 * 4u32)); 0 <= to_integer(((uint32)x0 * 4u32)); to_integer(((uint32)x0 * 4u32)) <= 1020; };
 have to_integer((4u32 + ((uint32)x0 * 4u32))) <= 1024 by arithmetic() using { to_integer((4u32 + ((uint32)x0 * 4u32))) == to_integer(4u32) + to_integer(((uint32)x0 * 4u32)); 0 <= to_integer(((uint32)x0 * 4u32)); to_integer(((uint32)x0 * 4u32)) <= 1020; };
 have to_integer((uint32)x1) <= 1073741823 by arithmetic() using { to_integer((uint32)x1) <= 255; };
 apply(uint32_to_integer_less_equal_implies_less_equal((uint32)x1, 1073741823u32));
 have (uint32)x1 <= 4294967295u32 / 4u32 by simp() using { (uint32)x1 <= 1073741823u32; };
 have 4u32 == 0u32 or (uint32)x1 <= 4294967295u32 / 4u32 by assumption();
 apply(uint32_multiply_to_integer((uint32)x1, 4u32)) using { 4u32 == 0u32 or (uint32)x1 <= 4294967295u32 / 4u32; }
 have to_integer(((uint32)x1 * 4u32)) == (to_integer((int32)x1) * 4) by {
  rewrite(to_integer(((uint32)x1 * 4u32)) == to_integer((uint32)x1) * to_integer(4u32));
  rewrite(to_integer((uint32)x1) == to_integer((int32)x1));
  normalize();
 }
 have 0 <= to_integer(((uint32)x1 * 4u32)) by arithmetic() using { to_integer(((uint32)x1 * 4u32)) == to_integer((uint32)x1) * to_integer(4u32); 0 <= to_integer((uint32)x1); to_integer((uint32)x1) <= 255; };
 have to_integer(((uint32)x1 * 4u32)) <= 1020 by arithmetic() using { to_integer(((uint32)x1 * 4u32)) == to_integer((uint32)x1) * to_integer(4u32); 0 <= to_integer((uint32)x1); to_integer((uint32)x1) <= 255; };
 have to_integer((uint32)x1) <= 65521 by arithmetic() using { to_integer((uint32)x1) <= 255; };
 apply(uint32_to_integer_less_equal_implies_less_equal((uint32)x1, 65521u32));
 apply(uint32_subtract_to_integer(65521u32, (uint32)x1)) using { (uint32)x1 <= 65521u32; }
 have to_integer((65521u32 - (uint32)x1)) == (65521 - to_integer((int32)x1)) by {
  rewrite(to_integer((65521u32 - (uint32)x1)) == to_integer(65521u32) - to_integer((uint32)x1));
  rewrite(to_integer((uint32)x1) == to_integer((int32)x1));
  normalize();
 }
 have 65266 <= to_integer((65521u32 - (uint32)x1)) by arithmetic() using { to_integer((65521u32 - (uint32)x1)) == to_integer(65521u32) - to_integer((uint32)x1); 0 <= to_integer((uint32)x1); to_integer((uint32)x1) <= 255; };
 have to_integer((65521u32 - (uint32)x1)) <= 65521 by arithmetic() using { to_integer((65521u32 - (uint32)x1)) == to_integer(65521u32) - to_integer((uint32)x1); 0 <= to_integer((uint32)x1); to_integer((uint32)x1) <= 255; };
 have to_integer(((uint32)x1 * 4u32)) + to_integer((65521u32 - (uint32)x1)) <= 4294967295 by arithmetic() using { to_integer(((uint32)x1 * 4u32)) <= 1020; to_integer((65521u32 - (uint32)x1)) <= 65521; };
 apply(uint32_add_to_integer(((uint32)x1 * 4u32), (65521u32 - (uint32)x1))) using { to_integer(((uint32)x1 * 4u32)) + to_integer((65521u32 - (uint32)x1)) <= 4294967295; }
 have to_integer((((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) == ((to_integer((int32)x1) * 4) + (65521 - to_integer((int32)x1))) by {
  rewrite(to_integer((((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) == to_integer(((uint32)x1 * 4u32)) + to_integer((65521u32 - (uint32)x1)));
  rewrite(to_integer(((uint32)x1 * 4u32)) == (to_integer((int32)x1) * 4));
  rewrite(to_integer((65521u32 - (uint32)x1)) == (65521 - to_integer((int32)x1)));
  normalize();
 }
 have 65266 <= to_integer((((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) by arithmetic() using { to_integer((((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) == to_integer(((uint32)x1 * 4u32)) + to_integer((65521u32 - (uint32)x1)); 0 <= to_integer(((uint32)x1 * 4u32)); to_integer(((uint32)x1 * 4u32)) <= 1020; 65266 <= to_integer((65521u32 - (uint32)x1)); to_integer((65521u32 - (uint32)x1)) <= 65521; };
 have to_integer((((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) <= 66541 by arithmetic() using { to_integer((((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) == to_integer(((uint32)x1 * 4u32)) + to_integer((65521u32 - (uint32)x1)); 0 <= to_integer(((uint32)x1 * 4u32)); to_integer(((uint32)x1 * 4u32)) <= 1020; 65266 <= to_integer((65521u32 - (uint32)x1)); to_integer((65521u32 - (uint32)x1)) <= 65521; };
 have to_integer((4u32 + ((uint32)x0 * 4u32))) + to_integer((((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) <= 4294967295 by arithmetic() using { to_integer((4u32 + ((uint32)x0 * 4u32))) <= 1024; to_integer((((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) <= 66541; };
 apply(uint32_add_to_integer((4u32 + ((uint32)x0 * 4u32)), (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1)))) using { to_integer((4u32 + ((uint32)x0 * 4u32))) + to_integer((((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) <= 4294967295; }
 have to_integer(((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1)))) == ((4 + (to_integer((int32)x0) * 4)) + ((to_integer((int32)x1) * 4) + (65521 - to_integer((int32)x1)))) by {
  rewrite(to_integer(((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1)))) == to_integer((4u32 + ((uint32)x0 * 4u32))) + to_integer((((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))));
  rewrite(to_integer((4u32 + ((uint32)x0 * 4u32))) == (4 + (to_integer((int32)x0) * 4)));
  rewrite(to_integer((((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) == ((to_integer((int32)x1) * 4) + (65521 - to_integer((int32)x1))));
  normalize();
 }
 have 65270 <= to_integer(((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1)))) by arithmetic() using { to_integer(((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1)))) == to_integer((4u32 + ((uint32)x0 * 4u32))) + to_integer((((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))); 4 <= to_integer((4u32 + ((uint32)x0 * 4u32))); to_integer((4u32 + ((uint32)x0 * 4u32))) <= 1024; 65266 <= to_integer((((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))); to_integer((((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) <= 66541; };
 have to_integer(((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1)))) <= 67565 by arithmetic() using { to_integer(((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1)))) == to_integer((4u32 + ((uint32)x0 * 4u32))) + to_integer((((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))); 4 <= to_integer((4u32 + ((uint32)x0 * 4u32))); to_integer((4u32 + ((uint32)x0 * 4u32))) <= 1024; 65266 <= to_integer((((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))); to_integer((((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) <= 66541; };
 have to_integer((uint32)x2) <= 1073741823 by arithmetic() using { to_integer((uint32)x2) <= 255; };
 apply(uint32_to_integer_less_equal_implies_less_equal((uint32)x2, 1073741823u32));
 have (uint32)x2 <= 4294967295u32 / 4u32 by simp() using { (uint32)x2 <= 1073741823u32; };
 have 4u32 == 0u32 or (uint32)x2 <= 4294967295u32 / 4u32 by assumption();
 apply(uint32_multiply_to_integer((uint32)x2, 4u32)) using { 4u32 == 0u32 or (uint32)x2 <= 4294967295u32 / 4u32; }
 have to_integer(((uint32)x2 * 4u32)) == (to_integer((int32)x2) * 4) by {
  rewrite(to_integer(((uint32)x2 * 4u32)) == to_integer((uint32)x2) * to_integer(4u32));
  rewrite(to_integer((uint32)x2) == to_integer((int32)x2));
  normalize();
 }
 have 0 <= to_integer(((uint32)x2 * 4u32)) by arithmetic() using { to_integer(((uint32)x2 * 4u32)) == to_integer((uint32)x2) * to_integer(4u32); 0 <= to_integer((uint32)x2); to_integer((uint32)x2) <= 255; };
 have to_integer(((uint32)x2 * 4u32)) <= 1020 by arithmetic() using { to_integer(((uint32)x2 * 4u32)) == to_integer((uint32)x2) * to_integer(4u32); 0 <= to_integer((uint32)x2); to_integer((uint32)x2) <= 255; };
 have to_integer((uint32)x2) <= 65521 by arithmetic() using { to_integer((uint32)x2) <= 255; };
 apply(uint32_to_integer_less_equal_implies_less_equal((uint32)x2, 65521u32));
 apply(uint32_subtract_to_integer(65521u32, (uint32)x2)) using { (uint32)x2 <= 65521u32; }
 have to_integer((65521u32 - (uint32)x2)) == (65521 - to_integer((int32)x2)) by {
  rewrite(to_integer((65521u32 - (uint32)x2)) == to_integer(65521u32) - to_integer((uint32)x2));
  rewrite(to_integer((uint32)x2) == to_integer((int32)x2));
  normalize();
 }
 have 65266 <= to_integer((65521u32 - (uint32)x2)) by arithmetic() using { to_integer((65521u32 - (uint32)x2)) == to_integer(65521u32) - to_integer((uint32)x2); 0 <= to_integer((uint32)x2); to_integer((uint32)x2) <= 255; };
 have to_integer((65521u32 - (uint32)x2)) <= 65521 by arithmetic() using { to_integer((65521u32 - (uint32)x2)) == to_integer(65521u32) - to_integer((uint32)x2); 0 <= to_integer((uint32)x2); to_integer((uint32)x2) <= 255; };
 have to_integer((65521u32 - (uint32)x2)) <= 2147483647 by arithmetic() using { to_integer((65521u32 - (uint32)x2)) <= 65521; };
 apply(uint32_to_integer_less_equal_implies_less_equal((65521u32 - (uint32)x2), 2147483647u32));
 have (65521u32 - (uint32)x2) <= 4294967295u32 / 2u32 by simp() using { (65521u32 - (uint32)x2) <= 2147483647u32; };
 have 2u32 == 0u32 or (65521u32 - (uint32)x2) <= 4294967295u32 / 2u32 by assumption();
 apply(uint32_multiply_to_integer((65521u32 - (uint32)x2), 2u32)) using { 2u32 == 0u32 or (65521u32 - (uint32)x2) <= 4294967295u32 / 2u32; }
 have to_integer(((65521u32 - (uint32)x2) * 2u32)) == ((65521 - to_integer((int32)x2)) * 2) by {
  rewrite(to_integer(((65521u32 - (uint32)x2) * 2u32)) == to_integer((65521u32 - (uint32)x2)) * to_integer(2u32));
  rewrite(to_integer((65521u32 - (uint32)x2)) == (65521 - to_integer((int32)x2)));
  normalize();
 }
 have 130532 <= to_integer(((65521u32 - (uint32)x2) * 2u32)) by arithmetic() using { to_integer(((65521u32 - (uint32)x2) * 2u32)) == to_integer((65521u32 - (uint32)x2)) * to_integer(2u32); 65266 <= to_integer((65521u32 - (uint32)x2)); to_integer((65521u32 - (uint32)x2)) <= 65521; };
 have to_integer(((65521u32 - (uint32)x2) * 2u32)) <= 131042 by arithmetic() using { to_integer(((65521u32 - (uint32)x2) * 2u32)) == to_integer((65521u32 - (uint32)x2)) * to_integer(2u32); 65266 <= to_integer((65521u32 - (uint32)x2)); to_integer((65521u32 - (uint32)x2)) <= 65521; };
 have to_integer(((uint32)x2 * 4u32)) + to_integer(((65521u32 - (uint32)x2) * 2u32)) <= 4294967295 by arithmetic() using { to_integer(((uint32)x2 * 4u32)) <= 1020; to_integer(((65521u32 - (uint32)x2) * 2u32)) <= 131042; };
 apply(uint32_add_to_integer(((uint32)x2 * 4u32), ((65521u32 - (uint32)x2) * 2u32))) using { to_integer(((uint32)x2 * 4u32)) + to_integer(((65521u32 - (uint32)x2) * 2u32)) <= 4294967295; }
 have to_integer((((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) == ((to_integer((int32)x2) * 4) + ((65521 - to_integer((int32)x2)) * 2)) by {
  rewrite(to_integer((((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) == to_integer(((uint32)x2 * 4u32)) + to_integer(((65521u32 - (uint32)x2) * 2u32)));
  rewrite(to_integer(((uint32)x2 * 4u32)) == (to_integer((int32)x2) * 4));
  rewrite(to_integer(((65521u32 - (uint32)x2) * 2u32)) == ((65521 - to_integer((int32)x2)) * 2));
  normalize();
 }
 have 130532 <= to_integer((((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) by arithmetic() using { to_integer((((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) == to_integer(((uint32)x2 * 4u32)) + to_integer(((65521u32 - (uint32)x2) * 2u32)); 0 <= to_integer(((uint32)x2 * 4u32)); to_integer(((uint32)x2 * 4u32)) <= 1020; 130532 <= to_integer(((65521u32 - (uint32)x2) * 2u32)); to_integer(((65521u32 - (uint32)x2) * 2u32)) <= 131042; };
 have to_integer((((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) <= 132062 by arithmetic() using { to_integer((((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) == to_integer(((uint32)x2 * 4u32)) + to_integer(((65521u32 - (uint32)x2) * 2u32)); 0 <= to_integer(((uint32)x2 * 4u32)); to_integer(((uint32)x2 * 4u32)) <= 1020; 130532 <= to_integer(((65521u32 - (uint32)x2) * 2u32)); to_integer(((65521u32 - (uint32)x2) * 2u32)) <= 131042; };
 have to_integer(((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1)))) + to_integer((((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) <= 4294967295 by arithmetic() using { to_integer(((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1)))) <= 67565; to_integer((((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) <= 132062; };
 apply(uint32_add_to_integer(((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))), (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32)))) using { to_integer(((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1)))) + to_integer((((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) <= 4294967295; }
 have to_integer((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32)))) == (((4 + (to_integer((int32)x0) * 4)) + ((to_integer((int32)x1) * 4) + (65521 - to_integer((int32)x1)))) + ((to_integer((int32)x2) * 4) + ((65521 - to_integer((int32)x2)) * 2))) by {
  rewrite(to_integer((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32)))) == to_integer(((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1)))) + to_integer((((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))));
  rewrite(to_integer(((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1)))) == ((4 + (to_integer((int32)x0) * 4)) + ((to_integer((int32)x1) * 4) + (65521 - to_integer((int32)x1)))));
  rewrite(to_integer((((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) == ((to_integer((int32)x2) * 4) + ((65521 - to_integer((int32)x2)) * 2)));
  normalize();
 }
 have 195802 <= to_integer((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32)))) by arithmetic() using { to_integer((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32)))) == to_integer(((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1)))) + to_integer((((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))); 65270 <= to_integer(((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1)))); to_integer(((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1)))) <= 67565; 130532 <= to_integer((((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))); to_integer((((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) <= 132062; };
 have to_integer((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32)))) <= 199627 by arithmetic() using { to_integer((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32)))) == to_integer(((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1)))) + to_integer((((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))); 65270 <= to_integer(((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1)))); to_integer(((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1)))) <= 67565; 130532 <= to_integer((((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))); to_integer((((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) <= 132062; };
 have to_integer((uint32)x3) <= 1073741823 by arithmetic() using { to_integer((uint32)x3) <= 255; };
 apply(uint32_to_integer_less_equal_implies_less_equal((uint32)x3, 1073741823u32));
 have (uint32)x3 <= 4294967295u32 / 4u32 by simp() using { (uint32)x3 <= 1073741823u32; };
 have 4u32 == 0u32 or (uint32)x3 <= 4294967295u32 / 4u32 by assumption();
 apply(uint32_multiply_to_integer((uint32)x3, 4u32)) using { 4u32 == 0u32 or (uint32)x3 <= 4294967295u32 / 4u32; }
 have to_integer(((uint32)x3 * 4u32)) == (to_integer((int32)x3) * 4) by {
  rewrite(to_integer(((uint32)x3 * 4u32)) == to_integer((uint32)x3) * to_integer(4u32));
  rewrite(to_integer((uint32)x3) == to_integer((int32)x3));
  normalize();
 }
 have 0 <= to_integer(((uint32)x3 * 4u32)) by arithmetic() using { to_integer(((uint32)x3 * 4u32)) == to_integer((uint32)x3) * to_integer(4u32); 0 <= to_integer((uint32)x3); to_integer((uint32)x3) <= 255; };
 have to_integer(((uint32)x3 * 4u32)) <= 1020 by arithmetic() using { to_integer(((uint32)x3 * 4u32)) == to_integer((uint32)x3) * to_integer(4u32); 0 <= to_integer((uint32)x3); to_integer((uint32)x3) <= 255; };
 have to_integer((uint32)x3) <= 65521 by arithmetic() using { to_integer((uint32)x3) <= 255; };
 apply(uint32_to_integer_less_equal_implies_less_equal((uint32)x3, 65521u32));
 apply(uint32_subtract_to_integer(65521u32, (uint32)x3)) using { (uint32)x3 <= 65521u32; }
 have to_integer((65521u32 - (uint32)x3)) == (65521 - to_integer((int32)x3)) by {
  rewrite(to_integer((65521u32 - (uint32)x3)) == to_integer(65521u32) - to_integer((uint32)x3));
  rewrite(to_integer((uint32)x3) == to_integer((int32)x3));
  normalize();
 }
 have 65266 <= to_integer((65521u32 - (uint32)x3)) by arithmetic() using { to_integer((65521u32 - (uint32)x3)) == to_integer(65521u32) - to_integer((uint32)x3); 0 <= to_integer((uint32)x3); to_integer((uint32)x3) <= 255; };
 have to_integer((65521u32 - (uint32)x3)) <= 65521 by arithmetic() using { to_integer((65521u32 - (uint32)x3)) == to_integer(65521u32) - to_integer((uint32)x3); 0 <= to_integer((uint32)x3); to_integer((uint32)x3) <= 255; };
 have to_integer((65521u32 - (uint32)x3)) <= 1431655765 by arithmetic() using { to_integer((65521u32 - (uint32)x3)) <= 65521; };
 apply(uint32_to_integer_less_equal_implies_less_equal((65521u32 - (uint32)x3), 1431655765u32));
 have (65521u32 - (uint32)x3) <= 4294967295u32 / 3u32 by simp() using { (65521u32 - (uint32)x3) <= 1431655765u32; };
 have 3u32 == 0u32 or (65521u32 - (uint32)x3) <= 4294967295u32 / 3u32 by assumption();
 apply(uint32_multiply_to_integer((65521u32 - (uint32)x3), 3u32)) using { 3u32 == 0u32 or (65521u32 - (uint32)x3) <= 4294967295u32 / 3u32; }
 have to_integer(((65521u32 - (uint32)x3) * 3u32)) == ((65521 - to_integer((int32)x3)) * 3) by {
  rewrite(to_integer(((65521u32 - (uint32)x3) * 3u32)) == to_integer((65521u32 - (uint32)x3)) * to_integer(3u32));
  rewrite(to_integer((65521u32 - (uint32)x3)) == (65521 - to_integer((int32)x3)));
  normalize();
 }
 have 195798 <= to_integer(((65521u32 - (uint32)x3) * 3u32)) by arithmetic() using { to_integer(((65521u32 - (uint32)x3) * 3u32)) == to_integer((65521u32 - (uint32)x3)) * to_integer(3u32); 65266 <= to_integer((65521u32 - (uint32)x3)); to_integer((65521u32 - (uint32)x3)) <= 65521; };
 have to_integer(((65521u32 - (uint32)x3) * 3u32)) <= 196563 by arithmetic() using { to_integer(((65521u32 - (uint32)x3) * 3u32)) == to_integer((65521u32 - (uint32)x3)) * to_integer(3u32); 65266 <= to_integer((65521u32 - (uint32)x3)); to_integer((65521u32 - (uint32)x3)) <= 65521; };
 have to_integer(((uint32)x3 * 4u32)) + to_integer(((65521u32 - (uint32)x3) * 3u32)) <= 4294967295 by arithmetic() using { to_integer(((uint32)x3 * 4u32)) <= 1020; to_integer(((65521u32 - (uint32)x3) * 3u32)) <= 196563; };
 apply(uint32_add_to_integer(((uint32)x3 * 4u32), ((65521u32 - (uint32)x3) * 3u32))) using { to_integer(((uint32)x3 * 4u32)) + to_integer(((65521u32 - (uint32)x3) * 3u32)) <= 4294967295; }
 have to_integer((((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))) == ((to_integer((int32)x3) * 4) + ((65521 - to_integer((int32)x3)) * 3)) by {
  rewrite(to_integer((((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))) == to_integer(((uint32)x3 * 4u32)) + to_integer(((65521u32 - (uint32)x3) * 3u32)));
  rewrite(to_integer(((uint32)x3 * 4u32)) == (to_integer((int32)x3) * 4));
  rewrite(to_integer(((65521u32 - (uint32)x3) * 3u32)) == ((65521 - to_integer((int32)x3)) * 3));
  normalize();
 }
 have 195798 <= to_integer((((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))) by arithmetic() using { to_integer((((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))) == to_integer(((uint32)x3 * 4u32)) + to_integer(((65521u32 - (uint32)x3) * 3u32)); 0 <= to_integer(((uint32)x3 * 4u32)); to_integer(((uint32)x3 * 4u32)) <= 1020; 195798 <= to_integer(((65521u32 - (uint32)x3) * 3u32)); to_integer(((65521u32 - (uint32)x3) * 3u32)) <= 196563; };
 have to_integer((((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))) <= 197583 by arithmetic() using { to_integer((((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))) == to_integer(((uint32)x3 * 4u32)) + to_integer(((65521u32 - (uint32)x3) * 3u32)); 0 <= to_integer(((uint32)x3 * 4u32)); to_integer(((uint32)x3 * 4u32)) <= 1020; 195798 <= to_integer(((65521u32 - (uint32)x3) * 3u32)); to_integer(((65521u32 - (uint32)x3) * 3u32)) <= 196563; };
 have to_integer((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32)))) + to_integer((((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))) <= 4294967295 by arithmetic() using { to_integer((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32)))) <= 199627; to_integer((((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))) <= 197583; };
 apply(uint32_add_to_integer((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))), (((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32)))) using { to_integer((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32)))) + to_integer((((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))) <= 4294967295; }
 have to_integer(((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) + (((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32)))) == ((((4 + (to_integer((int32)x0) * 4)) + ((to_integer((int32)x1) * 4) + (65521 - to_integer((int32)x1)))) + ((to_integer((int32)x2) * 4) + ((65521 - to_integer((int32)x2)) * 2))) + ((to_integer((int32)x3) * 4) + ((65521 - to_integer((int32)x3)) * 3))) by {
  rewrite(to_integer(((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) + (((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32)))) == to_integer((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32)))) + to_integer((((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))));
  rewrite(to_integer((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32)))) == (((4 + (to_integer((int32)x0) * 4)) + ((to_integer((int32)x1) * 4) + (65521 - to_integer((int32)x1)))) + ((to_integer((int32)x2) * 4) + ((65521 - to_integer((int32)x2)) * 2))));
  rewrite(to_integer((((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))) == ((to_integer((int32)x3) * 4) + ((65521 - to_integer((int32)x3)) * 3)));
  normalize();
 }
 have 391600 <= to_integer(((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) + (((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32)))) by arithmetic() using { to_integer(((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) + (((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32)))) == to_integer((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32)))) + to_integer((((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))); 195802 <= to_integer((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32)))); to_integer((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32)))) <= 199627; 195798 <= to_integer((((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))); to_integer((((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))) <= 197583; };
 have to_integer(((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) + (((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32)))) <= 397210 by arithmetic() using { to_integer(((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) + (((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32)))) == to_integer((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32)))) + to_integer((((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))); 195802 <= to_integer((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32)))); to_integer((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32)))) <= 199627; 195798 <= to_integer((((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))); to_integer((((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))) <= 197583; };
 have to_integer(((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2) + (uint32)x3)) == 1 + to_integer((int32)x0) + to_integer((int32)x1) + to_integer((int32)x2) + to_integer((int32)x3) by arithmetic() using { to_integer(((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2) + (uint32)x3)) == ((((1 + to_integer((int32)x0)) + to_integer((int32)x1)) + to_integer((int32)x2)) + to_integer((int32)x3)); };
 apply(uint32_remainder_to_integer(((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2) + (uint32)x3), 65521u32));
 have to_integer(((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2) + (uint32)x3) % 65521u32) == truncating_remainder(1 + to_integer((int32)x0) + to_integer((int32)x1) + to_integer((int32)x2) + to_integer((int32)x3), 65521) by {
  rewrite(to_integer(((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2) + (uint32)x3) % 65521u32) == truncating_remainder(to_integer(((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2) + (uint32)x3)), 65521));
  rewrite(to_integer(((((1u32 + (uint32)x0) + (uint32)x1) + (uint32)x2) + (uint32)x3)) == 1 + to_integer((int32)x0) + to_integer((int32)x1) + to_integer((int32)x2) + to_integer((int32)x3));
  normalize();
 }
 have to_integer(((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) + (((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32)))) == 4 + 4 * to_integer((int32)x0) + 3 * to_integer((int32)x1) + 2 * to_integer((int32)x2) + to_integer((int32)x3) + 393126 by arithmetic() using { to_integer(((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) + (((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32)))) == ((((4 + (to_integer((int32)x0) * 4)) + ((to_integer((int32)x1) * 4) + (65521 - to_integer((int32)x1)))) + ((to_integer((int32)x2) * 4) + ((65521 - to_integer((int32)x2)) * 2))) + ((to_integer((int32)x3) * 4) + ((65521 - to_integer((int32)x3)) * 3))); };
 apply(uint32_remainder_to_integer(((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) + (((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))), 65521u32));
 have 0 <= 4 * to_integer((int32)x0) by arithmetic() using { 0 <= to_integer((int32)x0); };
 have 0 <= 4 + 4 * to_integer((int32)x0) by arithmetic() using { 0 <= 4 * to_integer((int32)x0); };
 have 0 <= 3 * to_integer((int32)x1) by arithmetic() using { 0 <= to_integer((int32)x1); };
 have 0 <= 4 + 4 * to_integer((int32)x0) + 3 * to_integer((int32)x1) by arithmetic() using { 0 <= 3 * to_integer((int32)x1); 0 <= 4 + 4 * to_integer((int32)x0); };
 have 0 <= 2 * to_integer((int32)x2) by arithmetic() using { 0 <= to_integer((int32)x2); };
 have 0 <= 4 + 4 * to_integer((int32)x0) + 3 * to_integer((int32)x1) + 2 * to_integer((int32)x2) by arithmetic() using { 0 <= 2 * to_integer((int32)x2); 0 <= 4 + 4 * to_integer((int32)x0) + 3 * to_integer((int32)x1); };
 have 0 <= 4 + 4 * to_integer((int32)x0) + 3 * to_integer((int32)x1) + 2 * to_integer((int32)x2) + to_integer((int32)x3) by arithmetic() using { 0 <= to_integer((int32)x3); 0 <= 4 + 4 * to_integer((int32)x0) + 3 * to_integer((int32)x1) + 2 * to_integer((int32)x2); };
 have 0 <= 4 + 4 * to_integer((int32)x0) + 3 * to_integer((int32)x1) + 2 * to_integer((int32)x2) + to_integer((int32)x3) + 393126 by arithmetic() using { 0 <= 4 + 4 * to_integer((int32)x0) + 3 * to_integer((int32)x1) + 2 * to_integer((int32)x2) + to_integer((int32)x3); };
 have 4 + 4 * to_integer((int32)x0) + 3 * to_integer((int32)x1) + 2 * to_integer((int32)x2) + to_integer((int32)x3) + 393126 == (4 + 4 * to_integer((int32)x0) + 3 * to_integer((int32)x1) + 2 * to_integer((int32)x2) + to_integer((int32)x3)) + 65521 * 6 by arithmetic() using {};
 apply(adler_residue_congruent(4 + 4 * to_integer((int32)x0) + 3 * to_integer((int32)x1) + 2 * to_integer((int32)x2) + to_integer((int32)x3) + 393126, 4 + 4 * to_integer((int32)x0) + 3 * to_integer((int32)x1) + 2 * to_integer((int32)x2) + to_integer((int32)x3), 6));
 have to_integer(((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) + (((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))) % 65521u32) == truncating_remainder(4 + 4 * to_integer((int32)x0) + 3 * to_integer((int32)x1) + 2 * to_integer((int32)x2) + to_integer((int32)x3), 65521) by {
  rewrite(to_integer(((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) + (((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32))) % 65521u32) == truncating_remainder(to_integer(((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) + (((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32)))), 65521));
  rewrite(to_integer(((((4u32 + ((uint32)x0 * 4u32)) + (((uint32)x1 * 4u32) + (65521u32 - (uint32)x1))) + (((uint32)x2 * 4u32) + ((65521u32 - (uint32)x2) * 2u32))) + (((uint32)x3 * 4u32) + ((65521u32 - (uint32)x3) * 3u32)))) == 4 + 4 * to_integer((int32)x0) + 3 * to_integer((int32)x1) + 2 * to_integer((int32)x2) + to_integer((int32)x3) + 393126);
  rewrite(truncating_remainder(4 + 4 * to_integer((int32)x0) + 3 * to_integer((int32)x1) + 2 * to_integer((int32)x2) + to_integer((int32)x3) + 393126, 65521) == truncating_remainder(4 + 4 * to_integer((int32)x0) + 3 * to_integer((int32)x1) + 2 * to_integer((int32)x2) + to_integer((int32)x3), 65521));
  normalize();
 }
 assumption();
 }
}

theorem adler_four_byte_result_spec(bytes: uint8[]) {
 ensures to_integer(((((1u32 + (uint32)bytes[0]) + (uint32)bytes[1]) + (uint32)bytes[2]) + (uint32)bytes[3]) % 65521u32) == adler_spec_a(bytes, 4, 1) by {
  apply(adler_spec_four(bytes));
  apply(adler_four_byte_native_result(bytes[0], bytes[1], bytes[2], bytes[3]));
  rewrite(adler_spec_a(bytes, 4, 1) == truncating_remainder(1 + to_integer((int32)bytes[0]) + to_integer((int32)bytes[1]) + to_integer((int32)bytes[2]) + to_integer((int32)bytes[3]), 65521));
  assumption();
 }
 ensures to_integer(((((4u32 + ((uint32)bytes[0] * 4u32)) + (((uint32)bytes[1] * 4u32) + (65521u32 - (uint32)bytes[1]))) + (((uint32)bytes[2] * 4u32) + ((65521u32 - (uint32)bytes[2]) * 2u32))) + (((uint32)bytes[3] * 4u32) + ((65521u32 - (uint32)bytes[3]) * 3u32))) % 65521u32) == adler_spec_b(bytes, 4, 1, 0) by {
  apply(adler_spec_four(bytes));
  apply(adler_four_byte_native_result(bytes[0], bytes[1], bytes[2], bytes[3]));
  rewrite(adler_spec_b(bytes, 4, 1, 0) == truncating_remainder(4 + 4 * to_integer((int32)bytes[0]) + 3 * to_integer((int32)bytes[1]) + 2 * to_integer((int32)bytes[2]) + to_integer((int32)bytes[3]), 65521));
  assumption();
 }
}
