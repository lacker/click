target "x86_64-linux-userspace";
verifying "adler32.c";
import "byte.click";
import "../../adler32-spec.click";
import "short-prefix.click";
uint64 adler32_z(uint64 adler, const uint8* buf, uint64 len) {
 requires adler == 1u64;
 requires 2u64 <= len;
 requires len <= 15u64;
 requires buf != 0;
 views buf[0u64..len];
 ensures to_integer(result) == adler_spec_checksum(old(buf), old((int32)(uint32)len), 1, 0);
 ensures result <= 4294967295u64;
 ensures forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) };
} by {
 have viewable(buf[0u64..len]) by simp();
 execute_until(loop(0));
 have viewable(buf[0u64..len]) by simp();
 loop {
  decreases to_integer(len);
  views buf[0u64..len];
  invariant to_integer(len) <= 15;
  invariant to_integer(old(len)) <= 15;
  invariant len <= old(len);
  invariant buf == old(buf) + (old(len) - len);
  invariant viewable(buf[0u64..len]);
  invariant old(len) - len <= 15u64;
  invariant to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len));
  invariant to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len));
  invariant 1 <= to_integer(adler);
  invariant to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - to_integer(len));
  invariant to_integer(adler) <= 3826;
  invariant 0 <= to_integer(sum2);
  invariant to_integer(sum2) <= 3826 * (to_integer(old(len)) - to_integer(len));
  invariant to_integer(sum2) <= 57390;
  initialize by {
   apply(uint64_less_equal_to_integer(len, 15u64));
   have adler == 1u64 by simp();
   have sum2 == 0u64 by simp();
   apply(adler_sum_empty(old(buf), 0));
   have old(len) - len == 0u64 by simp();
   have to_integer(adler) == 1 by { simp() using { adler == 1u64; }; }
   have to_integer(sum2) == 0 by { simp() using { sum2 == 0u64; }; }
   have 1 <= to_integer(adler) by arithmetic() using { to_integer(adler) == 1; };
   have to_integer(adler) <= 3826 by arithmetic() using { to_integer(adler) == 1; };
   have 0 <= to_integer(sum2) by arithmetic() using { to_integer(sum2) == 0; };
   have to_integer(sum2) <= 57390 by arithmetic() using { to_integer(sum2) == 0; };
   have to_integer(old(len)) == to_integer(len) by simp();
   have zlib_prefix_count(old(len), len) == 0 by {
    unfold(zlib_prefix_count(old(len), len));
    simp();
   }
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)) by {
    rewrite(zlib_prefix_count(old(len), len) == 0);
    rewrite(adler_byte_sum(old(buf), 0) == 0);
    simp() using { to_integer(adler) == 1; };
   }
   have to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)) by {
    rewrite(zlib_prefix_count(old(len), len) == 0);
    rewrite(adler_weighted_sum(old(buf), 0, 0) == 0);
    simp() using { to_integer(sum2) == 0; };
   }
   have to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - to_integer(len)) by arithmetic() using { to_integer(adler) == 1; to_integer(old(len)) == to_integer(len); };
   have to_integer(sum2) <= 3826 * (to_integer(old(len)) - to_integer(len)) by arithmetic() using { to_integer(sum2) == 0; to_integer(old(len)) == to_integer(len); };
   simp();
  }
  preserve by {
   if len == 0u64 {
    have old(len) - len == old(len) by simp();
    have zlib_prefix_count(old(len), len) == old((int32)(uint32)len) by {
     unfold(zlib_prefix_count(old(len), len));
     simp();
    }
    have to_integer(adler) == 1 + adler_byte_sum(old(buf), old((int32)(uint32)len)) by {
     simp() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)); zlib_prefix_count(old(len), len) == old((int32)(uint32)len); };
    }
    have to_integer(sum2) == to_integer(old((int32)(uint32)len)) + adler_weighted_sum(old(buf), old((int32)(uint32)len), old((int32)(uint32)len)) by {
     simp() using { to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)); zlib_prefix_count(old(len), len) == old((int32)(uint32)len); };
    }
    step(); step(); step(); step();
    have __click_call_result1 == 0u64 by assumption();
    step();
   } else {
    have 0u64 <= len by normalize();
    have 0u64 < len by {
     if 0u64 < len { assumption(); } else {
      apply(uint64_less_equal_and_not_less_than_implies_equal(0u64, len));
      have len == 0u64 by { rewrite(0u64 == len); normalize(); }
      contradiction(len == 0u64);
     }
    }
   apply(uint64_to_integer_bounds(len));
   apply(uint64_less_than_to_integer(0u64, len));
   have to_integer(1u64) <= to_integer(len) by arithmetic() using { to_integer(0u64) < to_integer(len); };
   apply(uint64_to_integer_less_equal_implies_less_equal(1u64, len));
   apply(uint64_subtract_to_integer(len, 1u64));
   step(); step();
   have 0u64 < len by assumption();
   apply(uint64_to_integer_less_equal_implies_less_equal(len, 15u64));
   have 0u64 <= len by normalize();
   have 0u64 <= len - 0u64 by normalize();
   have viewable(buf[0u64..1u64]) by simp();
   have viewable(buf[0u64..len]) by simp();
   mark before_decrement;
   step(); step(); step();
   have to_integer(len) == at(before_decrement, to_integer(len)) - 1 by assumption();
   have to_integer(len) <= 15 by arithmetic() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; at(before_decrement, to_integer(len)) <= 15; };
   have 0 <= to_integer(len) by arithmetic() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; to_integer(1u64) <= at(before_decrement, to_integer(len)); };
   have to_integer(len) < at(before_decrement, to_integer(len)) by arithmetic() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; };
   execute_until(assignment(adler, 3));
   have __click_call_result0 == at(before_decrement, buf) by simp();
   have viewable(__click_call_result0[0u64..1u64]) by {
    simp() using { __click_call_result0 == at(before_decrement, buf); at(before_decrement, viewable(buf[0u64..1u64])); };
   }
   have __click_call_result0 == old(buf) + (old(len) - at(before_decrement, len)) by simp();
   have at(before_decrement, len) <= old(len) by assumption();
   apply(uint64_less_equal_to_integer(at(before_decrement, len), old(len)));
   apply(uint64_subtract_to_integer(old(len), at(before_decrement, len)));
   have to_integer(old(len) - at(before_decrement, len)) < to_integer(old(len)) by arithmetic() using {
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   apply(uint64_to_integer_less_than_implies_less_than(old(len) - at(before_decrement, len), old(len)));
   apply(uint64_to_integer_less_equal_implies_less_equal(old(len), 15u64));
   have to_integer(old(len) - at(before_decrement, len)) <= 14 by arithmetic() using {
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(old(len)) <= 15;
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   apply(uint64_to_integer_less_equal_implies_less_equal(old(len) - at(before_decrement, len), 14u64));
   have old(len) - at(before_decrement, len) <= 22208u64 by arithmetic() using { old(len) - at(before_decrement, len) <= 14u64; };
   have old(len) - at(before_decrement, len) <= 15u64 by arithmetic() using { old(len) - at(before_decrement, len) <= 14u64; };
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_decrement, len)));
   have __click_call_result0 == old(buf) + zlib_prefix_count(old(len), at(before_decrement, len)) by simp() using {
    __click_call_result0 == old(buf) + (old(len) - at(before_decrement, len));
    old(buf) + (old(len) - at(before_decrement, len)) == old(buf) + zlib_prefix_count(old(len), at(before_decrement, len));
   };
   have __click_call_result0[0] == old(buf)[zlib_prefix_count(old(len), at(before_decrement, len))] by simp() using {
    __click_call_result0 == old(buf) + zlib_prefix_count(old(len), at(before_decrement, len));
   };
   apply(zlib_byte_u64(__click_call_result0[0]));
   apply(zlib_byte_integer_identity(__click_call_result0[0]));
   have to_integer(adler) <= 3571 by arithmetic() using {
    to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - at(before_decrement, to_integer(len)));
    to_integer(old(len)) <= 15;
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   have to_integer(adler) + to_integer((uint64)(uint32)__click_call_result0[0]) <= 18446744073709551615 by arithmetic() using {
    to_integer(adler) <= 3571;
    to_integer((uint64)(uint32)__click_call_result0[0]) == to_integer((int32)__click_call_result0[0]);
    to_integer((int32)__click_call_result0[0]) <= 255;
   };
   apply(uint64_add_to_integer(adler, (uint64)(uint32)__click_call_result0[0]));
   mark before_add;
   step();
   have adler == at(before_add, adler + (uint64)(uint32)__click_call_result0[0]) by simp();
   have to_integer(adler) == at(before_add, to_integer(adler + (uint64)(uint32)__click_call_result0[0])) by simp() using { adler == at(before_add, adler + (uint64)(uint32)__click_call_result0[0]); };
   have to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer((int32)__click_call_result0[0])) by arithmetic() using {
    to_integer(adler) == at(before_add, to_integer(adler + (uint64)(uint32)__click_call_result0[0]));
    at(before_add, to_integer(adler + (uint64)(uint32)__click_call_result0[0])) == at(before_add, to_integer(adler)) + at(before_add, to_integer((uint64)(uint32)__click_call_result0[0]));
    at(before_add, to_integer((uint64)(uint32)__click_call_result0[0])) == at(before_add, to_integer((int32)__click_call_result0[0]));
   };
   have 1 <= to_integer(adler) by arithmetic() using {
    1 <= at(before_add, to_integer(adler));
    0 <= at(before_add, to_integer((int32)__click_call_result0[0]));
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer((int32)__click_call_result0[0]));
   };
   have to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - to_integer(len)) by arithmetic() using {
    at(before_add, to_integer(adler)) <= 1 + 255 * (to_integer(old(len)) - at(before_decrement, to_integer(len)));
    at(before_add, to_integer((int32)__click_call_result0[0])) <= 255;
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer((int32)__click_call_result0[0]));
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
   };
   have to_integer(adler) <= 3826 by arithmetic() using {
    at(before_add, to_integer(adler)) <= 3571;
    at(before_add, to_integer((int32)__click_call_result0[0])) <= 255;
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer((int32)__click_call_result0[0]));
   };
   have to_integer(sum2) + to_integer(adler) <= 18446744073709551615 by arithmetic() using {
    to_integer(sum2) <= 57390;
    to_integer(adler) <= 3826;
   };
   apply(uint64_add_to_integer(sum2, adler));
   mark before_sum;
   execute_until(back_edge());
   have to_integer(sum2) == at(before_sum, to_integer(sum2)) + to_integer(adler) by simp();
   have 0 <= to_integer(sum2) by arithmetic() using {
    0 <= at(before_sum, to_integer(sum2));
    1 <= to_integer(adler);
    to_integer(sum2) == at(before_sum, to_integer(sum2)) + to_integer(adler);
   };
   have to_integer(sum2) <= 3826 * (to_integer(old(len)) - to_integer(len)) by arithmetic() using {
    at(before_sum, to_integer(sum2)) <= 3826 * (to_integer(old(len)) - at(before_decrement, to_integer(len)));
    to_integer(adler) <= 3826;
    to_integer(sum2) == at(before_sum, to_integer(sum2)) + to_integer(adler);
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
   };
   have to_integer(sum2) <= 57390 by arithmetic() using {
    to_integer(sum2) <= 3826 * (to_integer(old(len)) - to_integer(len));
    to_integer(old(len)) <= 15;
    0 <= to_integer(len);
   };
   have to_integer(len) <= to_integer(old(len)) by arithmetic() using {
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
    at(before_decrement, to_integer(len)) <= to_integer(old(len));
   };
   apply(uint64_to_integer_less_equal_implies_less_equal(len, old(len)));
   apply(uint64_subtract_to_integer(old(len), len));
   have to_integer(old(len) - at(before_decrement, len)) <= 14 by arithmetic() using {
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(old(len)) <= 15;
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   apply(uint64_to_integer_less_equal_implies_less_equal(old(len) - at(before_decrement, len), 14u64));
   have to_integer(old(len) - at(before_decrement, len)) + to_integer(1u64) <= 18446744073709551615 by arithmetic() using { to_integer(old(len) - at(before_decrement, len)) <= 14; };
   apply(uint64_add_to_integer(old(len) - at(before_decrement, len), 1u64));
   have to_integer(old(len) - len) == to_integer((old(len) - at(before_decrement, len)) + 1u64) by arithmetic() using {
    to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer((old(len) - at(before_decrement, len)) + 1u64) == to_integer(old(len) - at(before_decrement, len)) + to_integer(1u64);
   };
   apply(uint64_to_integer_equal_implies_equal(old(len) - len, (old(len) - at(before_decrement, len)) + 1u64));
   have buf == at(before_decrement, buf) + 1 by simp();
   have buf == old(buf) + (old(len) - len) by {
    rewrite(buf == at(before_decrement, buf) + 1);
    rewrite(old(len) - len == (old(len) - at(before_decrement, len)) + 1u64);
    arithmetic_certificate rules {
     premise 0: at(before_decrement, buf) == old(buf) + (old(len) - at(before_decrement, len)) => at(before_decrement, buf) == old(buf) + (old(len) - at(before_decrement, len));
     premise 1: old(len) - at(before_decrement, len) <= 14u64 => old(len) - at(before_decrement, len) <= 14u64;
     pointer_translation relation 0 bounds [1] => at(before_decrement, buf) + 1 == old(buf) + ((old(len) - at(before_decrement, len)) + 1u64);
     conclusion 0;
    }
   }
   have to_integer(len) == to_integer(at(before_decrement, len) - 1u64) by simp();
   apply(uint64_to_integer_equal_implies_equal(len, at(before_decrement, len) - 1u64));
   have len <= at(before_decrement, len) - 1u64 by simp();
   apply(uint64_to_integer_less_equal_implies_less_equal(len, 15u64));
   apply(uint64_less_equal_transitive(len, 15u64, 9223372036854775807u64));
   have viewable(buf[0u64..len]) by {
    transport(at(before_decrement, viewable(buf[0u64..len])), viewable(buf[0u64..len])) using {
     buf == at(before_decrement, buf) + 1;
     at(before_decrement, viewable(buf[0u64..len]));
     1u64 <= at(before_decrement, len);
     len <= at(before_decrement, len) - 1u64;
     len <= 15u64;
     len <= 9223372036854775807u64;
    };
   }
   have old(len) - len <= 15u64 by {
    have to_integer(old(len) - len) <= 15 by arithmetic() using {
     to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
     to_integer(old(len)) <= 15;
     0 <= to_integer(len);
    };
    apply(uint64_to_integer_less_equal_implies_less_equal(old(len) - len, 15u64));
   }
   have old(len) - len <= 22208u64 by arithmetic() using { old(len) - len <= 15u64; };
   apply(zlib_prefix_observation(old(len), len));
   apply(zlib_prefix_observation(old(len), at(before_decrement, len)));
   have to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + 1 by arithmetic() using {
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(old(len) - len);
    to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) == to_integer(old(len) - at(before_decrement, len));
    to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
   };

   have 0 < to_integer(zlib_prefix_count(old(len), len)) by arithmetic() using {
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + 1;
    to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) == to_integer(old(len) - at(before_decrement, len));
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    at(before_decrement, to_integer(len)) <= to_integer(old(len));
   };
   have to_integer(1) <= to_integer(zlib_prefix_count(old(len), len)) by arithmetic() using { 0 < to_integer(zlib_prefix_count(old(len), len)); };
   apply(int32_to_integer_less_equal_implies_less_equal(1, zlib_prefix_count(old(len), len)));
   apply(zlib_positive_count(zlib_prefix_count(old(len), len)));
   apply(int32_nonnegative_subtract_within_value_is_defined(zlib_prefix_count(old(len), len), 1));
   apply(int32_subtract_to_integer(zlib_prefix_count(old(len), len), 1));
   have to_integer(zlib_prefix_count(old(len), len) - 1) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) by arithmetic() using {
    to_integer(zlib_prefix_count(old(len), len) - 1) == to_integer(zlib_prefix_count(old(len), len)) - to_integer(1);
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + 1;
   };
   apply(int32_to_integer_equal_implies_equal(zlib_prefix_count(old(len), len) - 1, zlib_prefix_count(old(len), at(before_decrement, len))));
   apply(zlib_prefix_append(old(buf), old(len), len));
   apply(adler_weighted_prefix_step(old(buf), zlib_prefix_count(old(len), len)));
   have old(buf)[zlib_prefix_count(old(len), len) - 1] == at(before_add, __click_call_result0[0]) by simp() using {
    zlib_prefix_count(old(len), len) - 1 == zlib_prefix_count(old(len), at(before_decrement, len));
    at(before_add, __click_call_result0[0]) == old(buf)[zlib_prefix_count(old(len), at(before_decrement, len))];
   };
   have adler_byte_sum(old(buf), zlib_prefix_count(old(len), len) - 1) == adler_byte_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len))) by simp() using {
    zlib_prefix_count(old(len), len) - 1 == zlib_prefix_count(old(len), at(before_decrement, len));
   };
   have adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len) - 1, zlib_prefix_count(old(len), len) - 1) == adler_weighted_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)), zlib_prefix_count(old(len), at(before_decrement, len))) by simp() using {
    zlib_prefix_count(old(len), len) - 1 == zlib_prefix_count(old(len), at(before_decrement, len));
   };
   apply(zlib_equal_byte_integers(old(buf)[zlib_prefix_count(old(len), len) - 1], at(before_add, __click_call_result0[0])));
   have zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]) == at(before_add, to_integer((int32)__click_call_result0[0])) by arithmetic() using {
    zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]) == zlib_byte_integer(at(before_add, __click_call_result0[0]));
    at(before_add, zlib_byte_integer(__click_call_result0[0])) == at(before_add, to_integer((int32)__click_call_result0[0]));
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)) by arithmetic() using {
    adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)) == adler_byte_sum(old(buf), zlib_prefix_count(old(len), len) - 1) + zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]);
    adler_byte_sum(old(buf), zlib_prefix_count(old(len), len) - 1) == adler_byte_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)));
    zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]) == at(before_add, to_integer((int32)__click_call_result0[0]));
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer((int32)__click_call_result0[0]));
    at(before_add, to_integer(adler)) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)));
   };
   have to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)) by arithmetic() using {
    adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)) == adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len) - 1, zlib_prefix_count(old(len), len) - 1) + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len));
    adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len) - 1, zlib_prefix_count(old(len), len) - 1) == adler_weighted_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)), zlib_prefix_count(old(len), at(before_decrement, len)));
    to_integer(sum2) == at(before_sum, to_integer(sum2)) + to_integer(adler);
    at(before_sum, to_integer(sum2)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)), zlib_prefix_count(old(len), at(before_decrement, len)));
    to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len));
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + 1;
   };
   close_invariants by { simp(); }
   }
  }
 }
 apply(uint64_to_integer_less_equal_implies_less_equal(adler, 3826u64));
 apply(uint64_to_integer_less_equal_implies_less_equal(sum2, 57390u64));
 have adler < 65521u64 by arithmetic() using { adler <= 3826u64; };
 apply(uint64_less_than_implies_not_greater_equal(adler, 65521u64));
 execute_until(assignment(sum2, 4));
 apply(zlib_short_result(old(buf), old((int32)(uint32)len), adler, sum2));
 apply(uint64_remainder_to_integer(sum2, 65521u64));
 apply(integer_positive_divisor_remainder_upper(to_integer(sum2), 65521));
 mark before_reduction;
 step();
 have sum2 == at(before_reduction, sum2 % 65521u64) by simp();
 have to_integer(sum2) == at(before_reduction, to_integer(sum2 % 65521u64)) by simp() using { sum2 == at(before_reduction, sum2 % 65521u64); };
 have to_integer(sum2) <= 65520 by arithmetic() using {
  to_integer(sum2) == at(before_reduction, to_integer(sum2 % 65521u64));
  at(before_reduction, to_integer(sum2 % 65521u64)) == truncating_remainder(at(before_reduction, to_integer(sum2)), 65521);
  truncating_remainder(at(before_reduction, to_integer(sum2)), 65521) <= 65521 - 1;
 };
 apply(uint64_to_integer_less_equal_implies_less_equal(sum2, 65520u64));
 have adler <= 65535u64 by arithmetic() using { adler <= 3826u64; };
 have sum2 <= 65535u64 by arithmetic() using { sum2 <= 65520u64; };
 apply(uint64_pack_uint16_to_integer(adler, sum2));
 have to_integer(adler | (sum2 << 16)) <= to_integer(4294967295u64) by arithmetic() using {
  to_integer(adler | (sum2 << 16)) == to_integer(adler) + 65536 * to_integer(sum2);
  to_integer(adler) <= 3826;
  to_integer(sum2) <= 65520;
 };
 apply(uint64_to_integer_less_equal_implies_less_equal(adler | (sum2 << 16), 4294967295u64));
 execute(); simp();
}
