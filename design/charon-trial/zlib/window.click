import "block.click";

# Mathematical observations of the original remaining count within one batch.
theorem zlib_remaining_step(total: uint64, remaining: uint64, amount: uint64) {
 requires remaining <= total;
 requires total <= 5551u64;
 requires amount <= remaining;
 ensures remaining - amount <= total by arithmetic() using { remaining <= total; total <= 5551u64; amount <= remaining; }
 ensures total - (remaining - amount) <= 5551u64 by arithmetic() using { remaining <= total; total <= 5551u64; amount <= remaining; }
 ensures to_integer(remaining - amount) == to_integer(remaining) - to_integer(amount) by {
  apply(uint64_less_equal_to_integer(amount, remaining));
  apply(uint64_subtract_to_integer(remaining, amount)); assumption();
 }
 ensures to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(zlib_prefix_count(total, remaining)) + to_integer(amount) by {
  have total - remaining <= 22208u64 by arithmetic() using { remaining <= total; total <= 5551u64; };
  have remaining - amount <= total by arithmetic() using { remaining <= total; total <= 5551u64; amount <= remaining; };
  have total - (remaining - amount) <= 22208u64 by arithmetic() using { remaining <= total; total <= 5551u64; amount <= remaining; };
  apply(zlib_prefix_observation(total, remaining));
  apply(zlib_prefix_observation(total, remaining - amount));
  apply(uint64_less_equal_to_integer(remaining, total));
  apply(uint64_less_equal_to_integer(amount, remaining));
  apply(uint64_less_equal_to_integer(remaining - amount, total));
  apply(uint64_subtract_to_integer(total, remaining));
  apply(uint64_subtract_to_integer(total, remaining - amount));
  apply(uint64_subtract_to_integer(remaining, amount));
  arithmetic() using {
   to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(total - (remaining - amount));
   to_integer(zlib_prefix_count(total, remaining)) == to_integer(total - remaining);
   to_integer(total - (remaining - amount)) == to_integer(total) - to_integer(remaining - amount);
   to_integer(total - remaining) == to_integer(total) - to_integer(remaining);
   to_integer(remaining - amount) == to_integer(remaining) - to_integer(amount);
  };
 }
}

theorem zlib_block_lane(bytes: uint8[], total: uint64, remaining: uint64, lane: int32) {
 requires remaining <= total;
 requires total <= 5551u64;
 requires 16u64 <= remaining;
 requires 0 <= lane;
 requires lane <= 15;
 ensures 0 <= zlib_prefix_count(total, remaining) + lane and zlib_prefix_count(total, remaining) + lane < 5552 by {
  have total - remaining <= 5535u64 by arithmetic() using { remaining <= total; total <= 5551u64; 16u64 <= remaining; };
  have total - remaining <= 22208u64 by arithmetic() using { total - remaining <= 5535u64; };
  apply(zlib_prefix_observation(total, remaining));
  apply(uint64_less_equal_to_integer(total - remaining, 5535u64));
  apply(uint64_to_integer_bounds(total - remaining));
  have defined(zlib_prefix_count(total, remaining) + lane) by simp();
  apply(int32_add_to_integer(zlib_prefix_count(total, remaining), lane));
  apply(int32_less_equal_to_integer(0, lane));
  apply(int32_less_equal_to_integer(lane, 15));
  have 0 <= to_integer(zlib_prefix_count(total, remaining) + lane) by arithmetic() using {
   to_integer(zlib_prefix_count(total, remaining) + lane) == to_integer(zlib_prefix_count(total, remaining)) + to_integer(lane);
   to_integer(zlib_prefix_count(total, remaining)) == to_integer(total - remaining);
   0 <= to_integer(lane);
   0 <= to_integer(total - remaining);
  };
  have to_integer(zlib_prefix_count(total, remaining) + lane) <= 5550 by arithmetic() using {
   to_integer(zlib_prefix_count(total, remaining) + lane) == to_integer(zlib_prefix_count(total, remaining)) + to_integer(lane);
   to_integer(zlib_prefix_count(total, remaining)) == to_integer(total - remaining);
   to_integer(total - remaining) <= 5535;
   to_integer(lane) <= 15;
  };
  both { apply(int32_to_integer_less_equal_implies_less_equal(0, zlib_prefix_count(total, remaining) + lane)); }
  and {
   apply(int32_to_integer_less_equal_implies_less_equal(zlib_prefix_count(total, remaining) + lane, 5550));
   have 5550 < 5552 by normalize();
   apply(int32_less_equal_less_than_transitive(zlib_prefix_count(total, remaining) + lane, 5550, 5552));
  }
 }
 ensures (bytes + (total - remaining))[lane] == bytes[zlib_prefix_count(total, remaining) + lane] by {
  have total - remaining <= 22208u64 by arithmetic() using { remaining <= total; total <= 5551u64; };
  apply(zlib_prefix_observation(total, remaining));
  apply(zlib_prefix_pointer(bytes, total, remaining));
  have defined(zlib_prefix_count(total, remaining) + lane) by simp();
  have bytes + (total - remaining) + lane == bytes + (zlib_prefix_count(total, remaining) + lane) by {
   rewrite(bytes + (total - remaining) == bytes + zlib_prefix_count(total, remaining));
   normalize() using { defined(zlib_prefix_count(total, remaining) + lane); };
  }
  simp() using { bytes + (total - remaining) + lane == bytes + (zlib_prefix_count(total, remaining) + lane); };
 }
}

theorem zlib_block_read_bound(total: uint64, remaining: uint64, lane: uint64) {
 requires remaining <= total;
 requires total <= 5551u64;
 requires 16u64 <= remaining;
 requires lane <= 15u64;
 ensures total - remaining <= 5535u64 by arithmetic() using { remaining <= total; total <= 5551u64; 16u64 <= remaining; }
 ensures total - remaining + lane < total by arithmetic() using { remaining <= total; total <= 5551u64; 16u64 <= remaining; lane <= 15u64; }
}
