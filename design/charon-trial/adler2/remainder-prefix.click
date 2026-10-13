// Checked positions in the aligned remainder after any number of full batches.
// Assemble after general-partition.click and the mathematical integer library.

theorem adler_checked_subprefix(base: int32, total: int32, remaining: int32) {
 requires 0 <= base;
 requires 0 <= total;
 requires total <= 22204;
 requires 0 <= remaining;
 requires remaining <= total;
 requires defined(base + total);
 ensures defined(total - remaining) and defined(base + (total - remaining)) and 0 <= base + (total - remaining) and base + (total - remaining) <= base + total by {
  apply(int32_nonnegative_subtract_within_value_is_defined(total, remaining)) using { 0 <= remaining; remaining <= total; }
  apply(int32_subtract_to_integer(total, remaining)) using { defined(total - remaining); }
  apply(int32_add_to_integer(base, total)) using { defined(base + total); }
  have base + total <= 2147483647 by normalize();
  apply(int32_less_equal_to_integer(base + total, 2147483647)) using { base + total <= 2147483647; }
  apply(int32_less_equal_to_integer(0, base)) using { 0 <= base; }
  apply(int32_less_equal_to_integer(0, remaining)) using { 0 <= remaining; }
  apply(int32_less_equal_to_integer(remaining, total)) using { remaining <= total; }
  have 0 <= to_integer(total - remaining) by { rewrite(to_integer(total - remaining) == to_integer(total) - to_integer(remaining)); arithmetic() using { to_integer(remaining) <= to_integer(total); } }
  have to_integer(base) + to_integer(total - remaining) >= -2147483648 by arithmetic() using { 0 <= to_integer(base); 0 <= to_integer(total - remaining); };
  have to_integer(base) + to_integer(total - remaining) <= 2147483647 by {
   rewrite(to_integer(total - remaining) == to_integer(total) - to_integer(remaining));
   arithmetic() using { to_integer(base + total) == to_integer(base) + to_integer(total); to_integer(base + total) <= 2147483647; 0 <= to_integer(remaining); }
  }
  apply(int32_add_defined_by_integer_bounds(base, total - remaining)) using { to_integer(base) + to_integer(total - remaining) >= -2147483648; to_integer(base) + to_integer(total - remaining) <= 2147483647; }
  have defined(base + (total - remaining)) by { both { assumption(); } and { assumption(); } }
  apply(int32_add_to_integer(base, total - remaining)) using { defined(base + (total - remaining)); }
  have 0 <= to_integer(base + (total - remaining)) by { rewrite(to_integer(base + (total - remaining)) == to_integer(base) + to_integer(total - remaining)); arithmetic() using { 0 <= to_integer(base); 0 <= to_integer(total - remaining); } }
  apply(int32_to_integer_less_equal_implies_less_equal(0, base + (total - remaining))) using { 0 <= to_integer(base + (total - remaining)); }
  have to_integer(base + (total - remaining)) <= to_integer(base + total) by {
   rewrite(to_integer(base + (total - remaining)) == to_integer(base) + to_integer(total - remaining));
   rewrite(to_integer(total - remaining) == to_integer(total) - to_integer(remaining));
   rewrite(to_integer(base + total) == to_integer(base) + to_integer(total));
   arithmetic() using { 0 <= to_integer(remaining); }
  }
  apply(int32_to_integer_less_equal_implies_less_equal(base + (total - remaining), base + total)) using { to_integer(base + (total - remaining)) <= to_integer(base + total); }
  both { both { both { assumption(); } and { assumption(); } } and { assumption(); } } and { assumption(); }
 }
}

theorem adler_checked_four_byte_start(n: int32) {
 requires defined(n + 4);
 ensures n <= 2147483643 by {
  apply(int32_add_to_integer(n, 4)) using { defined(n + 4); }
  have n + 4 <= 2147483647 by normalize();
  apply(int32_less_equal_to_integer(n + 4, 2147483647)) using { n + 4 <= 2147483647; }
  have to_integer(n) <= 2147483643 by arithmetic() using { to_integer(n + 4) == to_integer(n) + to_integer(4); to_integer(n + 4) <= 2147483647; };
  apply(int32_to_integer_less_equal_implies_less_equal(n, 2147483643)) using { to_integer(n) <= 2147483643; }
  assumption();
 }
}

theorem adler_checked_chunk_byte_observation(bytes: uint8[], start: int32, pos: int32, lane: int32) {
 requires defined(start + pos);
 requires 0 <= start + pos;
 requires start + pos <= 2147483643;
 requires 0 <= lane;
 requires lane <= 3;
 ensures to_integer((int32)((bytes + start) + pos)[lane]) == to_integer((int32)bytes[(start + pos) + lane]) by {
  apply(int32_less_equal_to_integer(0, start + pos)) using { 0 <= start + pos; }
  apply(int32_less_equal_to_integer(start + pos, 2147483643)) using { start + pos <= 2147483643; }
  apply(int32_less_equal_to_integer(0, lane)) using { 0 <= lane; }
  apply(int32_less_equal_to_integer(lane, 3)) using { lane <= 3; }
  have to_integer(start + pos) + to_integer(lane) >= -2147483648 by arithmetic() using { 0 <= to_integer(start + pos); 0 <= to_integer(lane); };
  have to_integer(start + pos) + to_integer(lane) <= 2147483647 by arithmetic() using { to_integer(start + pos) <= 2147483643; to_integer(lane) <= 3; };
  apply(int32_add_defined_by_integer_bounds(start + pos, lane)) using { to_integer(start + pos) + to_integer(lane) >= -2147483648; to_integer(start + pos) + to_integer(lane) <= 2147483647; }
  have defined((start + pos) + lane) by { both { assumption(); } and { assumption(); } }
  apply(adler_defined_byte_pointer_add(bytes, start, pos)) using { defined(start + pos); }
  apply(adler_defined_byte_pointer_add(bytes, start + pos, lane)) using { defined((start + pos) + lane); }
  have ((bytes + start) + pos) + lane == bytes + ((start + pos) + lane) by {
   rewrite((bytes + start) + pos == bytes + (start + pos));
   assumption();
  }
  have ((bytes + start) + pos)[lane] == bytes[(start + pos) + lane] by simp() using { ((bytes + start) + pos) + lane == bytes + ((start + pos) + lane); };
  rewrite(((bytes + start) + pos)[lane] == bytes[(start + pos) + lane]);
  normalize();
 }
}

// Association uses the checked additions in this window, rather than reserving
// room for an entire full batch after the base.
theorem adler_checked_prefix_advance(base: int32, pos: int32) {
 requires defined(base + pos);
 requires defined((base + pos) + 4);
 requires defined(pos + 4);
 requires defined(base + (pos + 4));
 ensures (base + pos) + 4 == base + (pos + 4) by {
  apply(int32_add_to_integer(base, pos)) using { defined(base + pos); }
  apply(int32_add_to_integer(base + pos, 4)) using { defined((base + pos) + 4); }
  apply(int32_add_to_integer(pos, 4)) using { defined(pos + 4); }
  apply(int32_add_to_integer(base, pos + 4)) using { defined(base + (pos + 4)); }
  have to_integer((base + pos) + 4) == to_integer(base + (pos + 4)) by {
   rewrite(to_integer((base + pos) + 4) == to_integer(base + pos) + to_integer(4));
   rewrite(to_integer(base + pos) == to_integer(base) + to_integer(pos));
   rewrite(to_integer(base + (pos + 4)) == to_integer(base) + to_integer(pos + 4));
   rewrite(to_integer(pos + 4) == to_integer(pos) + to_integer(4));
   arithmetic() using {};
  }
  apply(int32_to_integer_equal_implies_equal((base + pos) + 4, base + (pos + 4))) using { to_integer((base + pos) + 4) == to_integer(base + (pos + 4)); }
  assumption();
 }
}

theorem adler_empty_remainder_position(total: int32, remaining: int32) {
 requires 0 <= total;
 requires remaining == total;
 ensures to_integer(total - remaining) == 0 by {
  have 0 <= remaining by { rewrite(remaining == total); assumption(); }
  have remaining <= total by { rewrite(remaining == total); normalize(); }
  apply(int32_nonnegative_subtract_within_value_is_defined(total, remaining)) using { 0 <= remaining; remaining <= total; }
  have to_integer(remaining) == to_integer(total) by { rewrite(remaining == total); normalize(); }
  apply(int32_subtract_to_integer(total, remaining)) using { defined(total - remaining); }
  arithmetic() using { to_integer(total - remaining) == to_integer(total) - to_integer(remaining); to_integer(remaining) == to_integer(total); }
 }
}

theorem adler_complete_remainder_position(total: int32, remaining: int32) {
 requires 0 <= total;
 requires remaining == 0;
 ensures to_integer(total - remaining) == to_integer(total) by {
  have 0 <= remaining by { rewrite(remaining == 0); normalize(); }
  have remaining <= total by { rewrite(remaining == 0); assumption(); }
  apply(int32_nonnegative_subtract_within_value_is_defined(total, remaining)) using { 0 <= remaining; remaining <= total; }
  have to_integer(remaining) == 0 by { rewrite(remaining == 0); normalize(); }
  apply(int32_subtract_to_integer(total, remaining)) using { defined(total - remaining); }
  arithmetic() using { to_integer(total - remaining) == to_integer(total) - to_integer(remaining); to_integer(remaining) == 0; }
 }
}

// The native deferred product uses uint32; the prefix position uses int32.
theorem adler_remainder_native_count_observation(count: uint64) {
 requires count <= 22204u64;
 ensures to_integer((uint32)count) == to_integer(count) by {
  apply(uint64_to_integer_bounds(count));
  apply(uint64_less_equal_to_integer(count, 22204u64)) using { count <= 22204u64; }
  arithmetic_certificate rules {
   premise 0: 0 <= to_integer(count) => 0 <= to_integer(count);
   premise 1: to_integer(count) <= 22204 => to_integer(count) <= 22204;
   integer_cast_identity bounds [0, 1] => to_integer((uint32)count) == to_integer(count);
   conclusion 0;
  }
 }
}
