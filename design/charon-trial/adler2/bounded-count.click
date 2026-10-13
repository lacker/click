// Checked signed observations of native counts within the explicit signed limit.
// Iterator state and slice metadata retain their full unsigned 64-bit width.
theorem adler_bounded_count(count: uint64) {
 requires count <= 2147483647u64;
 ensures to_integer((int32)(uint32)count) == to_integer(count) by {
  apply(uint64_to_integer_bounds(count));
  apply(uint64_less_equal_to_integer(count, 2147483647u64));
  arithmetic_certificate rules {
   premise 0: 0 <= to_integer(count) => 0 <= to_integer(count);
   premise 1: to_integer(count) <= 2147483647 => to_integer(count) <= 2147483647;
   integer_cast_identity bounds [0, 1] => to_integer((int32)(uint32)count) == to_integer(count);
   conclusion 0;
  }
 }
 ensures 0 <= (int32)(uint32)count by {
  apply(uint64_to_integer_bounds(count));
  apply(uint64_less_equal_to_integer(count, 2147483647u64));
  have to_integer((int32)(uint32)count) == to_integer(count) by {
   arithmetic_certificate rules {
    premise 0: 0 <= to_integer(count) => 0 <= to_integer(count);
    premise 1: to_integer(count) <= 2147483647 => to_integer(count) <= 2147483647;
    integer_cast_identity bounds [0, 1] => to_integer((int32)(uint32)count) == to_integer(count);
    conclusion 0;
   }
  }
  have 0 <= to_integer((int32)(uint32)count) by { rewrite(to_integer((int32)(uint32)count) == to_integer(count)); assumption(); }
  apply(int32_to_integer_less_equal_implies_less_equal(0, (int32)(uint32)count)); assumption();
 }
 ensures (uint64)(int32)(uint32)count == count by {
  apply(uint64_to_integer_bounds(count));
  apply(uint64_less_equal_to_integer(count, 2147483647u64));
  have to_integer((int32)(uint32)count) == to_integer(count) by {
   arithmetic_certificate rules {
    premise 0: 0 <= to_integer(count) => 0 <= to_integer(count);
    premise 1: to_integer(count) <= 2147483647 => to_integer(count) <= 2147483647;
    integer_cast_identity bounds [0, 1] => to_integer((int32)(uint32)count) == to_integer(count);
    conclusion 0;
   }
  }
  have 0 <= to_integer((int32)(uint32)count) by { rewrite(to_integer((int32)(uint32)count) == to_integer(count)); assumption(); }
  have to_integer((int32)(uint32)count) <= 2147483647 by { rewrite(to_integer((int32)(uint32)count) == to_integer(count)); assumption(); }
  have to_integer((uint64)(int32)(uint32)count) == to_integer((int32)(uint32)count) by {
   arithmetic_certificate rules {
    premise 0: 0 <= to_integer((int32)(uint32)count) => 0 <= to_integer((int32)(uint32)count);
    premise 1: to_integer((int32)(uint32)count) <= 2147483647 => to_integer((int32)(uint32)count) <= 2147483647;
    integer_cast_identity bounds [0, 1] => to_integer((uint64)(int32)(uint32)count) == to_integer((int32)(uint32)count);
    conclusion 0;
   }
  }
  have to_integer((uint64)(int32)(uint32)count) == to_integer(count) by { rewrite(to_integer((uint64)(int32)(uint32)count) == to_integer((int32)(uint32)count)); assumption(); }
  apply(uint64_to_integer_equal_implies_equal((uint64)(int32)(uint32)count, count)); assumption();
 }
}


theorem adler_bounded_pointer_index(base: const uint8*, count: uint64) {
 requires count <= 2147483647u64;
 ensures base + count == base + (int32)(uint32)count by {
  apply(adler_bounded_count(count));
  simp() using { to_integer((int32)(uint32)count) == to_integer(count); (uint64)(int32)(uint32)count == count; 0 <= (int32)(uint32)count; count <= 2147483647u64; }
 }
}

theorem adler_bounded_count_lower(count: uint64, low: int32) {
 requires count <= 2147483647u64;
 requires 0 <= low;
 requires (uint64)low <= count;
 ensures low <= (int32)(uint32)count by {
  apply(adler_bounded_count(count));
  apply(int32_less_equal_to_integer(0, low));
  have low <= 2147483647 by normalize();
  apply(int32_less_equal_to_integer(low, 2147483647));
  have to_integer((uint64)low) == to_integer(low) by {
   arithmetic_certificate rules {
    premise 0: 0 <= to_integer(low) => 0 <= to_integer(low);
    premise 1: to_integer(low) <= 2147483647 => to_integer(low) <= 2147483647;
    integer_cast_identity bounds [0, 1] => to_integer((uint64)low) == to_integer(low);
    conclusion 0;
   }
  }
  apply(uint64_less_equal_to_integer((uint64)low, count));
  have to_integer(low) <= to_integer((int32)(uint32)count) by {
   rewrite(to_integer((int32)(uint32)count) == to_integer(count));
   rewrite(to_integer(low) == to_integer((uint64)low));
   assumption();
  }
  apply(int32_to_integer_less_equal_implies_less_equal(low, (int32)(uint32)count)); assumption();
 }
}

theorem adler_bounded_count_upper(count: uint64, high: int32) {
 requires count <= 2147483647u64;
 requires 0 <= high;
 requires count <= (uint64)high;
 ensures (int32)(uint32)count <= high by {
  apply(adler_bounded_count(count));
  apply(int32_less_equal_to_integer(0, high));
  have high <= 2147483647 by normalize();
  apply(int32_less_equal_to_integer(high, 2147483647));
  have to_integer((uint64)high) == to_integer(high) by {
   arithmetic_certificate rules {
    premise 0: 0 <= to_integer(high) => 0 <= to_integer(high);
    premise 1: to_integer(high) <= 2147483647 => to_integer(high) <= 2147483647;
    integer_cast_identity bounds [0, 1] => to_integer((uint64)high) == to_integer(high);
    conclusion 0;
   }
  }
  apply(uint64_less_equal_to_integer(count, (uint64)high));
  have to_integer((int32)(uint32)count) <= to_integer(high) by {
   rewrite(to_integer((int32)(uint32)count) == to_integer(count));
   rewrite(to_integer(high) == to_integer((uint64)high));
   assumption();
  }
  apply(int32_to_integer_less_equal_implies_less_equal((int32)(uint32)count, high)); assumption();
 }
}

theorem adler_bounded_count_native_lower(count: uint64, low: int32) {
 requires count <= 2147483647u64;
 requires 0 <= low;
 requires low <= (int32)(uint32)count;
 ensures (uint64)low <= count by {
  apply(adler_bounded_count(count));
  apply(int32_less_equal_to_integer(0, low));
  have low <= 2147483647 by normalize();
  apply(int32_less_equal_to_integer(low, 2147483647));
  have to_integer((uint64)low) == to_integer(low) by {
   arithmetic_certificate rules {
    premise 0: 0 <= to_integer(low) => 0 <= to_integer(low);
    premise 1: to_integer(low) <= 2147483647 => to_integer(low) <= 2147483647;
    integer_cast_identity bounds [0, 1] => to_integer((uint64)low) == to_integer(low);
    conclusion 0;
   }
  }
  apply(int32_less_equal_to_integer(low, (int32)(uint32)count));
  have to_integer((uint64)low) <= to_integer(count) by {
   rewrite(to_integer((uint64)low) == to_integer(low));
   rewrite(to_integer(count) == to_integer((int32)(uint32)count));
   assumption();
  }
  apply(uint64_to_integer_less_equal_implies_less_equal((uint64)low, count)); assumption();
 }
}

// Absolute tail-byte observation across the whole signed observation range.
theorem adler_bounded_previous_byte_observation(bytes: uint8[], total: uint64, remaining: uint64) {
 requires remaining <= total;
 requires 1u64 <= total - remaining;
 requires total <= 2147483647u64;
 requires 0 <= (int32)(uint32)remaining;
 requires (int32)(uint32)remaining <= (int32)(uint32)total;
 requires defined(((int32)(uint32)total - (int32)(uint32)remaining) - 1);
 ensures to_integer((int32)(bytes + (total - remaining - 1u64))[0]) == to_integer((int32)bytes[((int32)(uint32)total - (int32)(uint32)remaining) - 1]) by {
  have remaining <= 2147483647u64 by arithmetic() using { remaining <= total; total <= 2147483647u64; };
  have total - remaining - 1u64 <= 2147483647u64 by arithmetic() using { remaining <= total; 1u64 <= total - remaining; total <= 2147483647u64; };
  apply(adler_bounded_count(total)) using { total <= 2147483647u64; }
  apply(adler_bounded_count(remaining)) using { remaining <= 2147483647u64; }
  apply(adler_bounded_count(total - remaining - 1u64)) using { total - remaining - 1u64 <= 2147483647u64; }
  apply(uint64_less_equal_to_integer(remaining, total)) using { remaining <= total; }
  apply(uint64_less_equal_to_integer(1u64, total - remaining)) using { 1u64 <= total - remaining; }
  apply(uint64_subtract_to_integer(total, remaining)) using { remaining <= total; to_integer(remaining) <= to_integer(total); }
  apply(uint64_subtract_to_integer(total - remaining, 1u64)) using { 1u64 <= total - remaining; to_integer(1u64) <= to_integer(total - remaining); }
  apply(int32_nonnegative_subtract_within_value_is_defined((int32)(uint32)total, (int32)(uint32)remaining)) using { 0 <= (int32)(uint32)remaining; (int32)(uint32)remaining <= (int32)(uint32)total; }
  apply(int32_subtract_to_integer((int32)(uint32)total, (int32)(uint32)remaining)) using { defined((int32)(uint32)total - (int32)(uint32)remaining); }
  apply(int32_subtract_to_integer((int32)(uint32)total - (int32)(uint32)remaining, 1)) using { defined(((int32)(uint32)total - (int32)(uint32)remaining) - 1); }
  have to_integer((int32)(uint32)(total - remaining - 1u64)) == to_integer(((int32)(uint32)total - (int32)(uint32)remaining) - 1) by arithmetic() using {
   to_integer((int32)(uint32)(total - remaining - 1u64)) == to_integer(total - remaining - 1u64);
   to_integer(total - remaining - 1u64) == to_integer(total - remaining) - to_integer(1u64);
   to_integer(total - remaining) == to_integer(total) - to_integer(remaining);
   to_integer((int32)(uint32)total) == to_integer(total);
   to_integer((int32)(uint32)remaining) == to_integer(remaining);
   to_integer(((int32)(uint32)total - (int32)(uint32)remaining) - 1) == to_integer((int32)(uint32)total - (int32)(uint32)remaining) - to_integer(1);
   to_integer((int32)(uint32)total - (int32)(uint32)remaining) == to_integer((int32)(uint32)total) - to_integer((int32)(uint32)remaining);
  };
  apply(int32_to_integer_equal_implies_equal((int32)(uint32)(total - remaining - 1u64), ((int32)(uint32)total - (int32)(uint32)remaining) - 1)) using { to_integer((int32)(uint32)(total - remaining - 1u64)) == to_integer(((int32)(uint32)total - (int32)(uint32)remaining) - 1); }
  apply(adler_bounded_pointer_index(bytes, total - remaining - 1u64)) using { total - remaining - 1u64 <= 2147483647u64; }
  have bytes + (total - remaining - 1u64) == bytes + (((int32)(uint32)total - (int32)(uint32)remaining) - 1) by {
   rewrite(bytes + (total - remaining - 1u64) == bytes + (int32)(uint32)(total - remaining - 1u64));
   rewrite((int32)(uint32)(total - remaining - 1u64) == ((int32)(uint32)total - (int32)(uint32)remaining) - 1); normalize();
  }
  have (bytes + (total - remaining - 1u64))[0] == bytes[((int32)(uint32)total - (int32)(uint32)remaining) - 1] by simp() using { bytes + (total - remaining - 1u64) == bytes + (((int32)(uint32)total - (int32)(uint32)remaining) - 1); };
  rewrite((bytes + (total - remaining - 1u64))[0] == bytes[((int32)(uint32)total - (int32)(uint32)remaining) - 1]); normalize();
 }
}

// A guarded logical index denotes an actual byte in the native input range.
theorem adler_bounded_signed_index(count: uint64, index: int32) {
 requires count <= 2147483647u64;
 requires 0 <= index;
 requires index < (int32)(uint32)count;
 ensures (uint64)index < count by {
  apply(adler_bounded_count(count));
  apply(int32_to_integer_bounds(index));
  apply(int32_less_equal_to_integer(0, index));
  apply(int32_less_than_to_integer(index, (int32)(uint32)count));
  have 0 <= to_integer(index) by simp();
  have to_integer((uint64)index) == to_integer(index) by {
   arithmetic_certificate rules {
    premise 0: 0 <= to_integer(index) => 0 <= to_integer(index);
    premise 1: to_integer(index) <= 2147483647 => to_integer(index) <= 2147483647;
    integer_cast_identity bounds [0, 1] => to_integer((uint64)index) == to_integer(index);
    conclusion 0;
   }
  }
  have to_integer((uint64)index) < to_integer(count) by {
   arithmetic() using {
    to_integer((uint64)index) == to_integer(index);
    to_integer(index) < to_integer((int32)(uint32)count);
    to_integer((int32)(uint32)count) == to_integer(count);
   }
  }
  apply(uint64_to_integer_less_than_implies_less_than((uint64)index, count));
  assumption();
 }
}
