target "x86_64-linux-userspace";
verifying "adler32.c";
import "../../adler32-spec.click";
theorem zlib_pack_order(value: Integer) {
 ensures value + 65536 * value == 65536 * value + value by { arithmetic() using {}; }
}
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
uint64 adler32_z(uint64 adler, const uint8* buf, uint64 len) {
 requires adler == 1u64;
 requires len == 1u64;
 requires buf != 0;
 views buf[0u64..1u64];
 ensures result == (old(1u64 + buf[0]) | (old(1u64 + buf[0]) << 16i64));
 ensures buf[0] == old(buf[0]);
 ensures to_integer(result) == adler_spec_checksum(old(buf), 1, 1, 0);
} by {
 execute_until(assignment(adler, 0)); step();
 have adler == 1u64 by { simp(); }
 have sum2 == 0u64 by { simp(); }
 apply(zlib_byte_u64(buf[0]));
 have adler + (uint64)buf[0] < 65521u64 by { rewrite(adler == 1u64); arithmetic() using { (uint64)buf[0] <= 255u64; } }
 execute_until(assignment(adler, 1)); step();
 have adler == 1u64 + (uint64)(uint32)buf[0] by { simp(); }
 have adler <= 256u64 by { arithmetic() using { (uint64)(uint32)buf[0] <= 255u64; adler == 1u64 + (uint64)(uint32)buf[0]; } }
 have adler < 65521u64 by { arithmetic() using { adler <= 256u64; } }
 apply(uint64_less_than_implies_not_greater_equal(adler, 65521u64));
 execute_until(assignment(sum2, 1)); step();
 have sum2 == adler by { simp(); }
 have sum2 <= 256u64 by { rewrite(sum2 == adler); assumption(); }
 have sum2 < 65521u64 by { arithmetic() using { sum2 <= 256u64; } }
 apply(uint64_less_than_implies_not_greater_equal(sum2, 65521u64));
 have adler <= 65535u64 by { arithmetic() using { adler <= 256u64; } }
 have sum2 <= 65535u64 by { arithmetic() using { sum2 <= 256u64; } }
 apply(uint64_pack_uint16_to_integer(adler, sum2));
 have to_integer(1u64) + to_integer((uint64)(uint32)buf[0]) <= 18446744073709551615 by { arithmetic() using { to_integer((uint64)(uint32)buf[0]) == to_integer((int32)buf[0]); to_integer((int32)buf[0]) <= 255; } }
 apply(uint64_add_to_integer(1u64, (uint64)(uint32)buf[0]));
 have to_integer(adler) == 1 + to_integer((int32)buf[0]) by { rewrite(adler == 1u64 + (uint64)(uint32)buf[0]); rewrite(to_integer(1u64 + (uint64)(uint32)buf[0]) == to_integer(1u64) + to_integer((uint64)(uint32)buf[0])); rewrite(to_integer((uint64)(uint32)buf[0]) == to_integer((int32)buf[0])); simp(); }
 apply(adler_spec_one(buf));
 have 0 <= 1 + to_integer((int32)buf[0]) by { arithmetic() using { 0 <= to_integer((int32)buf[0]); } }
 have 1 + to_integer((int32)buf[0]) < 65521 by { arithmetic() using { to_integer((int32)buf[0]) <= 255; } }
 have 1 + to_integer((int32)buf[0]) <= 65520 by { arithmetic() using { to_integer((int32)buf[0]) <= 255; } }
 have 1 + to_integer((int32)buf[0]) == 0 * 65521 + (1 + to_integer((int32)buf[0])) by { arithmetic() using {}; }
 apply(adler_residue_unique(1 + to_integer((int32)buf[0]), 0, 1 + to_integer((int32)buf[0])));

 apply(zlib_pack_order(1 + to_integer((int32)buf[0])));
 have to_integer(adler | (sum2 << 16)) == adler_spec_checksum(buf, 1, 1, 0) by {
  unfold(adler_spec_checksum(buf, 1, 1, 0));
  rewrite(adler_spec_a(buf, 1, 1) == truncating_remainder(1 + to_integer((int32)buf[0]), 65521));
  rewrite(adler_spec_b(buf, 1, 1, 0) == truncating_remainder(1 + to_integer((int32)buf[0]), 65521));
  rewrite(truncating_remainder(1 + to_integer((int32)buf[0]), 65521) == 1 + to_integer((int32)buf[0]));
  rewrite(to_integer(adler | (sum2 << 16)) == to_integer(adler) + 65536 * to_integer(sum2));
  rewrite(sum2 == adler);
  rewrite(to_integer(adler) == 1 + to_integer((int32)buf[0]));
  assumption();
 }
 execute(); simp();
}
