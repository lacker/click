target "x86_64-linux-userspace";
verifying "adler32.c";
import "block.click";
uint64 adler32_z(uint64 adler, const uint8* buf, uint64 len) {
 requires adler == 1u64;
 requires len == 16u64;
 requires buf != 0;
 views buf[0u64..len];
 ensures to_integer(result) == adler_spec_checksum(old(buf), 16, 1, 0);
 ensures forall (k: uint64) { k < 16u64 implies old(buf)[k] == old(buf[k]) };
} by {
 have viewable(buf[0u64..len]) by simp();
 execute_until(loop(3));
 have viewable(buf[0u64..len]) by simp();
 loop {
  decreases to_integer(len);
  views buf[0u64..len];
  invariant len == 0u64 or len == 16u64;
  invariant len <= 16u64;
  invariant to_integer(len) <= 16;
  invariant buf == old(buf) + (16u64 - len);
  invariant viewable(buf[0u64..len]);
  invariant to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(16u64, len));
  invariant to_integer(sum2) == to_integer(zlib_prefix_count(16u64, len)) + adler_weighted_sum(old(buf), zlib_prefix_count(16u64, len), zlib_prefix_count(16u64, len));
  invariant to_integer(adler) <= 1 + 255 * to_integer(zlib_prefix_count(16u64, len));
  invariant to_integer(sum2) <= 1415761 * to_integer(zlib_prefix_count(16u64, len));
  initialize by {
   have len <= 16u64 by simp();
   apply(uint64_less_equal_to_integer(len, 16u64));
   have adler == 1u64 by simp();
   have sum2 == 0u64 by simp();
   have to_integer(adler) == 1 by simp() using { adler == 1u64; };
   have to_integer(sum2) == 0 by simp() using { sum2 == 0u64; };
   have zlib_prefix_count(16u64, len) == 0 by { unfold(zlib_prefix_count(16u64, len)); simp(); }
   apply(adler_sum_empty(old(buf), 0));
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 0) by arithmetic() using { to_integer(adler) == 1; adler_byte_sum(old(buf), 0) == 0; };
   have to_integer(sum2) == to_integer(0) + adler_weighted_sum(old(buf), 0, 0) by arithmetic() using { to_integer(sum2) == 0; adler_weighted_sum(old(buf), 0, 0) == 0; };
   have to_integer(adler) <= 1 + 255 * to_integer(0) by arithmetic() using { to_integer(adler) == 1; };
   have to_integer(sum2) <= 1415761 * to_integer(0) by arithmetic() using { to_integer(sum2) == 0; };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(16u64, len)) by { rewrite(zlib_prefix_count(16u64, len) == 0); assumption(); }
   have to_integer(sum2) == to_integer(zlib_prefix_count(16u64, len)) + adler_weighted_sum(old(buf), zlib_prefix_count(16u64, len), zlib_prefix_count(16u64, len)) by { rewrite(zlib_prefix_count(16u64, len) == 0); assumption(); }
   have to_integer(adler) <= 1 + 255 * to_integer(zlib_prefix_count(16u64, len)) by { rewrite(zlib_prefix_count(16u64, len) == 0); assumption(); }
   have to_integer(sum2) <= 1415761 * to_integer(zlib_prefix_count(16u64, len)) by { rewrite(zlib_prefix_count(16u64, len) == 0); assumption(); }
   simp();
  }
  preserve by {
   have len == 16u64 by {
    cases {
     len == 0u64 => {
      have not (len >= 16u64) by { rewrite(len == 0u64); normalize(); }
      contradiction(len >= 16u64);
     }
     len == 16u64 => { assumption(); }
    }
   }
   have zlib_prefix_count(16u64, len) == 0 by { unfold(zlib_prefix_count(16u64, len)); simp(); }
   have buf == old(buf) by simp();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 0) by { rewrite(0 == zlib_prefix_count(16u64, len)); assumption(); }
   have to_integer(zlib_prefix_count(16u64, len)) == 0 by simp() using { zlib_prefix_count(16u64, len) == 0; };
   have adler_weighted_sum(old(buf), zlib_prefix_count(16u64, len), zlib_prefix_count(16u64, len)) == adler_weighted_sum(old(buf), 0, 0) by { rewrite(zlib_prefix_count(16u64, len) == 0); normalize(); }
   have to_integer(sum2) == to_integer(0) + adler_weighted_sum(old(buf), 0, 0) by arithmetic() using {
    to_integer(sum2) == to_integer(zlib_prefix_count(16u64, len)) + adler_weighted_sum(old(buf), zlib_prefix_count(16u64, len), zlib_prefix_count(16u64, len));
    to_integer(zlib_prefix_count(16u64, len)) == 0;
    adler_weighted_sum(old(buf), zlib_prefix_count(16u64, len), zlib_prefix_count(16u64, len)) == adler_weighted_sum(old(buf), 0, 0);
   };
   have to_integer(adler) <= 1 + 255 * to_integer(0) by arithmetic() using {
    to_integer(adler) <= 1 + 255 * to_integer(zlib_prefix_count(16u64, len));
    to_integer(zlib_prefix_count(16u64, len)) == 0;
   };
   have to_integer(sum2) <= 1415761 * to_integer(0) by arithmetic() using {
    to_integer(sum2) <= 1415761 * to_integer(zlib_prefix_count(16u64, len));
    to_integer(zlib_prefix_count(16u64, len)) == 0;
   };
   have viewable(buf[0u64..16u64]) by simp();
   have to_integer(len) == 16 by simp() using { len == 16u64; };
   mark before_block;
   step();
   have len == 0u64 by simp();
   execute_until(assignment(adler, 22));
   have buf[0] == old(buf)[0] by simp() using { buf == old(buf); };
   apply(zlib_native_component_step(old(buf), 0, adler, sum2, buf[0]));
   mark byte_0;
   step();
   execute_until(assignment(sum2, 22));
   step();
   have adler == at(byte_0, adler + (uint64)(uint32)buf[0]) by simp();
   have sum2 == at(byte_0, sum2 + (adler + (uint64)(uint32)buf[0])) by simp();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 1) by simp() using {
    adler == at(byte_0, adler + (uint64)(uint32)buf[0]);
    at(byte_0, to_integer(adler + (uint64)(uint32)buf[0])) == 1 + adler_byte_sum(old(buf), 1);
   };
   have to_integer(sum2) == to_integer(1) + adler_weighted_sum(old(buf), 1, 1) by simp() using {
    sum2 == at(byte_0, sum2 + (adler + (uint64)(uint32)buf[0]));
    at(byte_0, to_integer(sum2 + (adler + (uint64)(uint32)buf[0]))) == to_integer(1) + adler_weighted_sum(old(buf), 1, 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer(1) by simp() using {
    adler == at(byte_0, adler + (uint64)(uint32)buf[0]);
    at(byte_0, to_integer(adler + (uint64)(uint32)buf[0])) <= 1 + 255 * to_integer(1);
   };
   have to_integer(sum2) <= 1415761 * to_integer(1) by simp() using {
    sum2 == at(byte_0, sum2 + (adler + (uint64)(uint32)buf[0]));
    at(byte_0, to_integer(sum2 + (adler + (uint64)(uint32)buf[0]))) <= 1415761 * to_integer(1);
   };
   execute_until(assignment(adler, 23));
   have buf[1] == old(buf)[1] by simp() using { buf == old(buf); };
   apply(zlib_native_component_step(old(buf), 1, adler, sum2, buf[1]));
   mark byte_1;
   step();
   execute_until(assignment(sum2, 23));
   step();
   have adler == at(byte_1, adler + (uint64)(uint32)buf[1]) by simp();
   have sum2 == at(byte_1, sum2 + (adler + (uint64)(uint32)buf[1])) by simp();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 2) by simp() using {
    adler == at(byte_1, adler + (uint64)(uint32)buf[1]);
    at(byte_1, to_integer(adler + (uint64)(uint32)buf[1])) == 1 + adler_byte_sum(old(buf), 2);
   };
   have to_integer(sum2) == to_integer(2) + adler_weighted_sum(old(buf), 2, 2) by simp() using {
    sum2 == at(byte_1, sum2 + (adler + (uint64)(uint32)buf[1]));
    at(byte_1, to_integer(sum2 + (adler + (uint64)(uint32)buf[1]))) == to_integer(2) + adler_weighted_sum(old(buf), 2, 2);
   };
   have to_integer(adler) <= 1 + 255 * to_integer(2) by simp() using {
    adler == at(byte_1, adler + (uint64)(uint32)buf[1]);
    at(byte_1, to_integer(adler + (uint64)(uint32)buf[1])) <= 1 + 255 * to_integer(2);
   };
   have to_integer(sum2) <= 1415761 * to_integer(2) by simp() using {
    sum2 == at(byte_1, sum2 + (adler + (uint64)(uint32)buf[1]));
    at(byte_1, to_integer(sum2 + (adler + (uint64)(uint32)buf[1]))) <= 1415761 * to_integer(2);
   };
   execute_until(assignment(adler, 24));
   have buf[2] == old(buf)[2] by simp() using { buf == old(buf); };
   apply(zlib_native_component_step(old(buf), 2, adler, sum2, buf[2]));
   mark byte_2;
   step();
   execute_until(assignment(sum2, 24));
   step();
   have adler == at(byte_2, adler + (uint64)(uint32)buf[2]) by simp();
   have sum2 == at(byte_2, sum2 + (adler + (uint64)(uint32)buf[2])) by simp();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 3) by simp() using {
    adler == at(byte_2, adler + (uint64)(uint32)buf[2]);
    at(byte_2, to_integer(adler + (uint64)(uint32)buf[2])) == 1 + adler_byte_sum(old(buf), 3);
   };
   have to_integer(sum2) == to_integer(3) + adler_weighted_sum(old(buf), 3, 3) by simp() using {
    sum2 == at(byte_2, sum2 + (adler + (uint64)(uint32)buf[2]));
    at(byte_2, to_integer(sum2 + (adler + (uint64)(uint32)buf[2]))) == to_integer(3) + adler_weighted_sum(old(buf), 3, 3);
   };
   have to_integer(adler) <= 1 + 255 * to_integer(3) by simp() using {
    adler == at(byte_2, adler + (uint64)(uint32)buf[2]);
    at(byte_2, to_integer(adler + (uint64)(uint32)buf[2])) <= 1 + 255 * to_integer(3);
   };
   have to_integer(sum2) <= 1415761 * to_integer(3) by simp() using {
    sum2 == at(byte_2, sum2 + (adler + (uint64)(uint32)buf[2]));
    at(byte_2, to_integer(sum2 + (adler + (uint64)(uint32)buf[2]))) <= 1415761 * to_integer(3);
   };
   execute_until(assignment(adler, 25));
   have buf[3] == old(buf)[3] by simp() using { buf == old(buf); };
   apply(zlib_native_component_step(old(buf), 3, adler, sum2, buf[3]));
   mark byte_3;
   step();
   execute_until(assignment(sum2, 25));
   step();
   have adler == at(byte_3, adler + (uint64)(uint32)buf[3]) by simp();
   have sum2 == at(byte_3, sum2 + (adler + (uint64)(uint32)buf[3])) by simp();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 4) by simp() using {
    adler == at(byte_3, adler + (uint64)(uint32)buf[3]);
    at(byte_3, to_integer(adler + (uint64)(uint32)buf[3])) == 1 + adler_byte_sum(old(buf), 4);
   };
   have to_integer(sum2) == to_integer(4) + adler_weighted_sum(old(buf), 4, 4) by simp() using {
    sum2 == at(byte_3, sum2 + (adler + (uint64)(uint32)buf[3]));
    at(byte_3, to_integer(sum2 + (adler + (uint64)(uint32)buf[3]))) == to_integer(4) + adler_weighted_sum(old(buf), 4, 4);
   };
   have to_integer(adler) <= 1 + 255 * to_integer(4) by simp() using {
    adler == at(byte_3, adler + (uint64)(uint32)buf[3]);
    at(byte_3, to_integer(adler + (uint64)(uint32)buf[3])) <= 1 + 255 * to_integer(4);
   };
   have to_integer(sum2) <= 1415761 * to_integer(4) by simp() using {
    sum2 == at(byte_3, sum2 + (adler + (uint64)(uint32)buf[3]));
    at(byte_3, to_integer(sum2 + (adler + (uint64)(uint32)buf[3]))) <= 1415761 * to_integer(4);
   };
   execute_until(assignment(adler, 26));
   have buf[4] == old(buf)[4] by simp() using { buf == old(buf); };
   apply(zlib_native_component_step(old(buf), 4, adler, sum2, buf[4]));
   mark byte_4;
   step();
   execute_until(assignment(sum2, 26));
   step();
   have adler == at(byte_4, adler + (uint64)(uint32)buf[4]) by simp();
   have sum2 == at(byte_4, sum2 + (adler + (uint64)(uint32)buf[4])) by simp();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 5) by simp() using {
    adler == at(byte_4, adler + (uint64)(uint32)buf[4]);
    at(byte_4, to_integer(adler + (uint64)(uint32)buf[4])) == 1 + adler_byte_sum(old(buf), 5);
   };
   have to_integer(sum2) == to_integer(5) + adler_weighted_sum(old(buf), 5, 5) by simp() using {
    sum2 == at(byte_4, sum2 + (adler + (uint64)(uint32)buf[4]));
    at(byte_4, to_integer(sum2 + (adler + (uint64)(uint32)buf[4]))) == to_integer(5) + adler_weighted_sum(old(buf), 5, 5);
   };
   have to_integer(adler) <= 1 + 255 * to_integer(5) by simp() using {
    adler == at(byte_4, adler + (uint64)(uint32)buf[4]);
    at(byte_4, to_integer(adler + (uint64)(uint32)buf[4])) <= 1 + 255 * to_integer(5);
   };
   have to_integer(sum2) <= 1415761 * to_integer(5) by simp() using {
    sum2 == at(byte_4, sum2 + (adler + (uint64)(uint32)buf[4]));
    at(byte_4, to_integer(sum2 + (adler + (uint64)(uint32)buf[4]))) <= 1415761 * to_integer(5);
   };
   execute_until(assignment(adler, 27));
   have buf[5] == old(buf)[5] by simp() using { buf == old(buf); };
   apply(zlib_native_component_step(old(buf), 5, adler, sum2, buf[5]));
   mark byte_5;
   step();
   execute_until(assignment(sum2, 27));
   step();
   have adler == at(byte_5, adler + (uint64)(uint32)buf[5]) by simp();
   have sum2 == at(byte_5, sum2 + (adler + (uint64)(uint32)buf[5])) by simp();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 6) by simp() using {
    adler == at(byte_5, adler + (uint64)(uint32)buf[5]);
    at(byte_5, to_integer(adler + (uint64)(uint32)buf[5])) == 1 + adler_byte_sum(old(buf), 6);
   };
   have to_integer(sum2) == to_integer(6) + adler_weighted_sum(old(buf), 6, 6) by simp() using {
    sum2 == at(byte_5, sum2 + (adler + (uint64)(uint32)buf[5]));
    at(byte_5, to_integer(sum2 + (adler + (uint64)(uint32)buf[5]))) == to_integer(6) + adler_weighted_sum(old(buf), 6, 6);
   };
   have to_integer(adler) <= 1 + 255 * to_integer(6) by simp() using {
    adler == at(byte_5, adler + (uint64)(uint32)buf[5]);
    at(byte_5, to_integer(adler + (uint64)(uint32)buf[5])) <= 1 + 255 * to_integer(6);
   };
   have to_integer(sum2) <= 1415761 * to_integer(6) by simp() using {
    sum2 == at(byte_5, sum2 + (adler + (uint64)(uint32)buf[5]));
    at(byte_5, to_integer(sum2 + (adler + (uint64)(uint32)buf[5]))) <= 1415761 * to_integer(6);
   };
   execute_until(assignment(adler, 28));
   have buf[6] == old(buf)[6] by simp() using { buf == old(buf); };
   apply(zlib_native_component_step(old(buf), 6, adler, sum2, buf[6]));
   mark byte_6;
   step();
   execute_until(assignment(sum2, 28));
   step();
   have adler == at(byte_6, adler + (uint64)(uint32)buf[6]) by simp();
   have sum2 == at(byte_6, sum2 + (adler + (uint64)(uint32)buf[6])) by simp();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 7) by simp() using {
    adler == at(byte_6, adler + (uint64)(uint32)buf[6]);
    at(byte_6, to_integer(adler + (uint64)(uint32)buf[6])) == 1 + adler_byte_sum(old(buf), 7);
   };
   have to_integer(sum2) == to_integer(7) + adler_weighted_sum(old(buf), 7, 7) by simp() using {
    sum2 == at(byte_6, sum2 + (adler + (uint64)(uint32)buf[6]));
    at(byte_6, to_integer(sum2 + (adler + (uint64)(uint32)buf[6]))) == to_integer(7) + adler_weighted_sum(old(buf), 7, 7);
   };
   have to_integer(adler) <= 1 + 255 * to_integer(7) by simp() using {
    adler == at(byte_6, adler + (uint64)(uint32)buf[6]);
    at(byte_6, to_integer(adler + (uint64)(uint32)buf[6])) <= 1 + 255 * to_integer(7);
   };
   have to_integer(sum2) <= 1415761 * to_integer(7) by simp() using {
    sum2 == at(byte_6, sum2 + (adler + (uint64)(uint32)buf[6]));
    at(byte_6, to_integer(sum2 + (adler + (uint64)(uint32)buf[6]))) <= 1415761 * to_integer(7);
   };
   execute_until(assignment(adler, 29));
   have buf[7] == old(buf)[7] by simp() using { buf == old(buf); };
   apply(zlib_native_component_step(old(buf), 7, adler, sum2, buf[7]));
   mark byte_7;
   step();
   execute_until(assignment(sum2, 29));
   step();
   have adler == at(byte_7, adler + (uint64)(uint32)buf[7]) by simp();
   have sum2 == at(byte_7, sum2 + (adler + (uint64)(uint32)buf[7])) by simp();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 8) by simp() using {
    adler == at(byte_7, adler + (uint64)(uint32)buf[7]);
    at(byte_7, to_integer(adler + (uint64)(uint32)buf[7])) == 1 + adler_byte_sum(old(buf), 8);
   };
   have to_integer(sum2) == to_integer(8) + adler_weighted_sum(old(buf), 8, 8) by simp() using {
    sum2 == at(byte_7, sum2 + (adler + (uint64)(uint32)buf[7]));
    at(byte_7, to_integer(sum2 + (adler + (uint64)(uint32)buf[7]))) == to_integer(8) + adler_weighted_sum(old(buf), 8, 8);
   };
   have to_integer(adler) <= 1 + 255 * to_integer(8) by simp() using {
    adler == at(byte_7, adler + (uint64)(uint32)buf[7]);
    at(byte_7, to_integer(adler + (uint64)(uint32)buf[7])) <= 1 + 255 * to_integer(8);
   };
   have to_integer(sum2) <= 1415761 * to_integer(8) by simp() using {
    sum2 == at(byte_7, sum2 + (adler + (uint64)(uint32)buf[7]));
    at(byte_7, to_integer(sum2 + (adler + (uint64)(uint32)buf[7]))) <= 1415761 * to_integer(8);
   };
   execute_until(assignment(adler, 30));
   have buf[8] == old(buf)[8] by simp() using { buf == old(buf); };
   apply(zlib_native_component_step(old(buf), 8, adler, sum2, buf[8]));
   mark byte_8;
   step();
   execute_until(assignment(sum2, 30));
   step();
   have adler == at(byte_8, adler + (uint64)(uint32)buf[8]) by simp();
   have sum2 == at(byte_8, sum2 + (adler + (uint64)(uint32)buf[8])) by simp();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 9) by simp() using {
    adler == at(byte_8, adler + (uint64)(uint32)buf[8]);
    at(byte_8, to_integer(adler + (uint64)(uint32)buf[8])) == 1 + adler_byte_sum(old(buf), 9);
   };
   have to_integer(sum2) == to_integer(9) + adler_weighted_sum(old(buf), 9, 9) by simp() using {
    sum2 == at(byte_8, sum2 + (adler + (uint64)(uint32)buf[8]));
    at(byte_8, to_integer(sum2 + (adler + (uint64)(uint32)buf[8]))) == to_integer(9) + adler_weighted_sum(old(buf), 9, 9);
   };
   have to_integer(adler) <= 1 + 255 * to_integer(9) by simp() using {
    adler == at(byte_8, adler + (uint64)(uint32)buf[8]);
    at(byte_8, to_integer(adler + (uint64)(uint32)buf[8])) <= 1 + 255 * to_integer(9);
   };
   have to_integer(sum2) <= 1415761 * to_integer(9) by simp() using {
    sum2 == at(byte_8, sum2 + (adler + (uint64)(uint32)buf[8]));
    at(byte_8, to_integer(sum2 + (adler + (uint64)(uint32)buf[8]))) <= 1415761 * to_integer(9);
   };
   execute_until(assignment(adler, 31));
   have buf[9] == old(buf)[9] by simp() using { buf == old(buf); };
   apply(zlib_native_component_step(old(buf), 9, adler, sum2, buf[9]));
   mark byte_9;
   step();
   execute_until(assignment(sum2, 31));
   step();
   have adler == at(byte_9, adler + (uint64)(uint32)buf[9]) by simp();
   have sum2 == at(byte_9, sum2 + (adler + (uint64)(uint32)buf[9])) by simp();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 10) by simp() using {
    adler == at(byte_9, adler + (uint64)(uint32)buf[9]);
    at(byte_9, to_integer(adler + (uint64)(uint32)buf[9])) == 1 + adler_byte_sum(old(buf), 10);
   };
   have to_integer(sum2) == to_integer(10) + adler_weighted_sum(old(buf), 10, 10) by simp() using {
    sum2 == at(byte_9, sum2 + (adler + (uint64)(uint32)buf[9]));
    at(byte_9, to_integer(sum2 + (adler + (uint64)(uint32)buf[9]))) == to_integer(10) + adler_weighted_sum(old(buf), 10, 10);
   };
   have to_integer(adler) <= 1 + 255 * to_integer(10) by simp() using {
    adler == at(byte_9, adler + (uint64)(uint32)buf[9]);
    at(byte_9, to_integer(adler + (uint64)(uint32)buf[9])) <= 1 + 255 * to_integer(10);
   };
   have to_integer(sum2) <= 1415761 * to_integer(10) by simp() using {
    sum2 == at(byte_9, sum2 + (adler + (uint64)(uint32)buf[9]));
    at(byte_9, to_integer(sum2 + (adler + (uint64)(uint32)buf[9]))) <= 1415761 * to_integer(10);
   };
   execute_until(assignment(adler, 32));
   have buf[10] == old(buf)[10] by simp() using { buf == old(buf); };
   apply(zlib_native_component_step(old(buf), 10, adler, sum2, buf[10]));
   mark byte_10;
   step();
   execute_until(assignment(sum2, 32));
   step();
   have adler == at(byte_10, adler + (uint64)(uint32)buf[10]) by simp();
   have sum2 == at(byte_10, sum2 + (adler + (uint64)(uint32)buf[10])) by simp();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 11) by simp() using {
    adler == at(byte_10, adler + (uint64)(uint32)buf[10]);
    at(byte_10, to_integer(adler + (uint64)(uint32)buf[10])) == 1 + adler_byte_sum(old(buf), 11);
   };
   have to_integer(sum2) == to_integer(11) + adler_weighted_sum(old(buf), 11, 11) by simp() using {
    sum2 == at(byte_10, sum2 + (adler + (uint64)(uint32)buf[10]));
    at(byte_10, to_integer(sum2 + (adler + (uint64)(uint32)buf[10]))) == to_integer(11) + adler_weighted_sum(old(buf), 11, 11);
   };
   have to_integer(adler) <= 1 + 255 * to_integer(11) by simp() using {
    adler == at(byte_10, adler + (uint64)(uint32)buf[10]);
    at(byte_10, to_integer(adler + (uint64)(uint32)buf[10])) <= 1 + 255 * to_integer(11);
   };
   have to_integer(sum2) <= 1415761 * to_integer(11) by simp() using {
    sum2 == at(byte_10, sum2 + (adler + (uint64)(uint32)buf[10]));
    at(byte_10, to_integer(sum2 + (adler + (uint64)(uint32)buf[10]))) <= 1415761 * to_integer(11);
   };
   execute_until(assignment(adler, 33));
   have buf[11] == old(buf)[11] by simp() using { buf == old(buf); };
   apply(zlib_native_component_step(old(buf), 11, adler, sum2, buf[11]));
   mark byte_11;
   step();
   execute_until(assignment(sum2, 33));
   step();
   have adler == at(byte_11, adler + (uint64)(uint32)buf[11]) by simp();
   have sum2 == at(byte_11, sum2 + (adler + (uint64)(uint32)buf[11])) by simp();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 12) by simp() using {
    adler == at(byte_11, adler + (uint64)(uint32)buf[11]);
    at(byte_11, to_integer(adler + (uint64)(uint32)buf[11])) == 1 + adler_byte_sum(old(buf), 12);
   };
   have to_integer(sum2) == to_integer(12) + adler_weighted_sum(old(buf), 12, 12) by simp() using {
    sum2 == at(byte_11, sum2 + (adler + (uint64)(uint32)buf[11]));
    at(byte_11, to_integer(sum2 + (adler + (uint64)(uint32)buf[11]))) == to_integer(12) + adler_weighted_sum(old(buf), 12, 12);
   };
   have to_integer(adler) <= 1 + 255 * to_integer(12) by simp() using {
    adler == at(byte_11, adler + (uint64)(uint32)buf[11]);
    at(byte_11, to_integer(adler + (uint64)(uint32)buf[11])) <= 1 + 255 * to_integer(12);
   };
   have to_integer(sum2) <= 1415761 * to_integer(12) by simp() using {
    sum2 == at(byte_11, sum2 + (adler + (uint64)(uint32)buf[11]));
    at(byte_11, to_integer(sum2 + (adler + (uint64)(uint32)buf[11]))) <= 1415761 * to_integer(12);
   };
   execute_until(assignment(adler, 34));
   have buf[12] == old(buf)[12] by simp() using { buf == old(buf); };
   apply(zlib_native_component_step(old(buf), 12, adler, sum2, buf[12]));
   mark byte_12;
   step();
   execute_until(assignment(sum2, 34));
   step();
   have adler == at(byte_12, adler + (uint64)(uint32)buf[12]) by simp();
   have sum2 == at(byte_12, sum2 + (adler + (uint64)(uint32)buf[12])) by simp();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 13) by simp() using {
    adler == at(byte_12, adler + (uint64)(uint32)buf[12]);
    at(byte_12, to_integer(adler + (uint64)(uint32)buf[12])) == 1 + adler_byte_sum(old(buf), 13);
   };
   have to_integer(sum2) == to_integer(13) + adler_weighted_sum(old(buf), 13, 13) by simp() using {
    sum2 == at(byte_12, sum2 + (adler + (uint64)(uint32)buf[12]));
    at(byte_12, to_integer(sum2 + (adler + (uint64)(uint32)buf[12]))) == to_integer(13) + adler_weighted_sum(old(buf), 13, 13);
   };
   have to_integer(adler) <= 1 + 255 * to_integer(13) by simp() using {
    adler == at(byte_12, adler + (uint64)(uint32)buf[12]);
    at(byte_12, to_integer(adler + (uint64)(uint32)buf[12])) <= 1 + 255 * to_integer(13);
   };
   have to_integer(sum2) <= 1415761 * to_integer(13) by simp() using {
    sum2 == at(byte_12, sum2 + (adler + (uint64)(uint32)buf[12]));
    at(byte_12, to_integer(sum2 + (adler + (uint64)(uint32)buf[12]))) <= 1415761 * to_integer(13);
   };
   execute_until(assignment(adler, 35));
   have buf[13] == old(buf)[13] by simp() using { buf == old(buf); };
   apply(zlib_native_component_step(old(buf), 13, adler, sum2, buf[13]));
   mark byte_13;
   step();
   execute_until(assignment(sum2, 35));
   step();
   have adler == at(byte_13, adler + (uint64)(uint32)buf[13]) by simp();
   have sum2 == at(byte_13, sum2 + (adler + (uint64)(uint32)buf[13])) by simp();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 14) by simp() using {
    adler == at(byte_13, adler + (uint64)(uint32)buf[13]);
    at(byte_13, to_integer(adler + (uint64)(uint32)buf[13])) == 1 + adler_byte_sum(old(buf), 14);
   };
   have to_integer(sum2) == to_integer(14) + adler_weighted_sum(old(buf), 14, 14) by simp() using {
    sum2 == at(byte_13, sum2 + (adler + (uint64)(uint32)buf[13]));
    at(byte_13, to_integer(sum2 + (adler + (uint64)(uint32)buf[13]))) == to_integer(14) + adler_weighted_sum(old(buf), 14, 14);
   };
   have to_integer(adler) <= 1 + 255 * to_integer(14) by simp() using {
    adler == at(byte_13, adler + (uint64)(uint32)buf[13]);
    at(byte_13, to_integer(adler + (uint64)(uint32)buf[13])) <= 1 + 255 * to_integer(14);
   };
   have to_integer(sum2) <= 1415761 * to_integer(14) by simp() using {
    sum2 == at(byte_13, sum2 + (adler + (uint64)(uint32)buf[13]));
    at(byte_13, to_integer(sum2 + (adler + (uint64)(uint32)buf[13]))) <= 1415761 * to_integer(14);
   };
   execute_until(assignment(adler, 36));
   have buf[14] == old(buf)[14] by simp() using { buf == old(buf); };
   apply(zlib_native_component_step(old(buf), 14, adler, sum2, buf[14]));
   mark byte_14;
   step();
   execute_until(assignment(sum2, 36));
   step();
   have adler == at(byte_14, adler + (uint64)(uint32)buf[14]) by simp();
   have sum2 == at(byte_14, sum2 + (adler + (uint64)(uint32)buf[14])) by simp();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 15) by simp() using {
    adler == at(byte_14, adler + (uint64)(uint32)buf[14]);
    at(byte_14, to_integer(adler + (uint64)(uint32)buf[14])) == 1 + adler_byte_sum(old(buf), 15);
   };
   have to_integer(sum2) == to_integer(15) + adler_weighted_sum(old(buf), 15, 15) by simp() using {
    sum2 == at(byte_14, sum2 + (adler + (uint64)(uint32)buf[14]));
    at(byte_14, to_integer(sum2 + (adler + (uint64)(uint32)buf[14]))) == to_integer(15) + adler_weighted_sum(old(buf), 15, 15);
   };
   have to_integer(adler) <= 1 + 255 * to_integer(15) by simp() using {
    adler == at(byte_14, adler + (uint64)(uint32)buf[14]);
    at(byte_14, to_integer(adler + (uint64)(uint32)buf[14])) <= 1 + 255 * to_integer(15);
   };
   have to_integer(sum2) <= 1415761 * to_integer(15) by simp() using {
    sum2 == at(byte_14, sum2 + (adler + (uint64)(uint32)buf[14]));
    at(byte_14, to_integer(sum2 + (adler + (uint64)(uint32)buf[14]))) <= 1415761 * to_integer(15);
   };
   execute_until(assignment(adler, 37));
   have buf[15] == old(buf)[15] by simp() using { buf == old(buf); };
   apply(zlib_native_component_step(old(buf), 15, adler, sum2, buf[15]));
   mark byte_15;
   step();
   execute_until(assignment(sum2, 37));
   step();
   have adler == at(byte_15, adler + (uint64)(uint32)buf[15]) by simp();
   have sum2 == at(byte_15, sum2 + (adler + (uint64)(uint32)buf[15])) by simp();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 16) by simp() using {
    adler == at(byte_15, adler + (uint64)(uint32)buf[15]);
    at(byte_15, to_integer(adler + (uint64)(uint32)buf[15])) == 1 + adler_byte_sum(old(buf), 16);
   };
   have to_integer(sum2) == to_integer(16) + adler_weighted_sum(old(buf), 16, 16) by simp() using {
    sum2 == at(byte_15, sum2 + (adler + (uint64)(uint32)buf[15]));
    at(byte_15, to_integer(sum2 + (adler + (uint64)(uint32)buf[15]))) == to_integer(16) + adler_weighted_sum(old(buf), 16, 16);
   };
   have to_integer(adler) <= 1 + 255 * to_integer(16) by simp() using {
    adler == at(byte_15, adler + (uint64)(uint32)buf[15]);
    at(byte_15, to_integer(adler + (uint64)(uint32)buf[15])) <= 1 + 255 * to_integer(16);
   };
   have to_integer(sum2) <= 1415761 * to_integer(16) by simp() using {
    sum2 == at(byte_15, sum2 + (adler + (uint64)(uint32)buf[15]));
    at(byte_15, to_integer(sum2 + (adler + (uint64)(uint32)buf[15]))) <= 1415761 * to_integer(16);
   };
   execute_until(back_edge());
   have buf == at(before_block, buf) + 16 by simp();
   have buf == old(buf) + 16u64 by simp();
   have viewable(buf[0u64..len]) by {
    transport(at(before_block, viewable(buf[0u64..16u64])), viewable(buf[0u64..len])) using {
     buf == at(before_block, buf) + 16;
     at(before_block, viewable(buf[0u64..16u64]));
     len == 0u64;
    };
   }
   have zlib_prefix_count(16u64, len) == 16 by { unfold(zlib_prefix_count(16u64, len)); simp(); }
   have len <= 16u64 by simp() using { len == 0u64; };
   have to_integer(len) == 0 by simp() using { len == 0u64; };
   have to_integer(len) <= 16 by arithmetic() using { to_integer(len) == 0; };
   have buf == old(buf) + (16u64 - len) by simp() using { buf == old(buf) + 16u64; len == 0u64; };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(16u64, len)) by { rewrite(zlib_prefix_count(16u64, len) == 16); assumption(); }
   have to_integer(sum2) == to_integer(zlib_prefix_count(16u64, len)) + adler_weighted_sum(old(buf), zlib_prefix_count(16u64, len), zlib_prefix_count(16u64, len)) by { rewrite(zlib_prefix_count(16u64, len) == 16); assumption(); }
   have to_integer(adler) <= 1 + 255 * to_integer(zlib_prefix_count(16u64, len)) by { rewrite(zlib_prefix_count(16u64, len) == 16); arithmetic() using { to_integer(adler) <= 1 + 255 * to_integer(16); }; }
   have to_integer(sum2) <= 1415761 * to_integer(zlib_prefix_count(16u64, len)) by { rewrite(zlib_prefix_count(16u64, len) == 16); arithmetic() using { to_integer(sum2) <= 1415761 * to_integer(16); }; }
   have len <= 9223372036854775807u64 by simp() using { len == 0u64; };
   have 0 <= to_integer(len) by arithmetic() using { to_integer(len) == 0; };
   have at(before_block, to_integer(len)) == 16 by assumption();
   have to_integer(len) < at(before_block, to_integer(len)) by arithmetic() using { to_integer(len) == 0; at(before_block, to_integer(len)) == 16; };
   close_invariants();
  }
 }
 have len == 0u64 by {
  cases {
   len == 0u64 => { assumption(); }
   len == 16u64 => {
    have len >= 16u64 by { rewrite(len == 16u64); normalize(); }
    contradiction(len >= 16u64);
   }
  }
 }
 have zlib_prefix_count(16u64, len) == 16 by { unfold(zlib_prefix_count(16u64, len)); simp(); }
 have to_integer(adler) == 1 + adler_byte_sum(old(buf), 16) by { rewrite(16 == zlib_prefix_count(16u64, len)); assumption(); }
 # Convert the count separately: the Integer coefficient has already folded.
 have to_integer(zlib_prefix_count(16u64, len)) == 16 by simp() using { zlib_prefix_count(16u64, len) == 16; };
 have adler_weighted_sum(old(buf), zlib_prefix_count(16u64, len), zlib_prefix_count(16u64, len)) == adler_weighted_sum(old(buf), 16, 16) by { rewrite(zlib_prefix_count(16u64, len) == 16); normalize(); }
 have to_integer(sum2) == to_integer(16) + adler_weighted_sum(old(buf), 16, 16) by arithmetic() using {
  to_integer(sum2) == to_integer(zlib_prefix_count(16u64, len)) + adler_weighted_sum(old(buf), zlib_prefix_count(16u64, len), zlib_prefix_count(16u64, len));
  to_integer(zlib_prefix_count(16u64, len)) == 16;
  adler_weighted_sum(old(buf), zlib_prefix_count(16u64, len), zlib_prefix_count(16u64, len)) == adler_weighted_sum(old(buf), 16, 16);
 };
 # This original scalar loop exits immediately, but must retain A and B.
 execute_until(loop(4));
 loop {
  decreases to_integer(len);
  views buf[0u64..len];
  invariant len == 0u64;
  invariant to_integer(adler) == 1 + adler_byte_sum(old(buf), 16);
  invariant to_integer(sum2) == to_integer(16) + adler_weighted_sum(old(buf), 16, 16);
  preserve by { step(); step(); step(); step(); step(); }
 }
 execute_until(assignment(adler, 39));
 apply(zlib_reduced_result(old(buf), 16, adler, sum2));
 execute(); simp();
}
