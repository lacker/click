// Bounds for the unchanged zero-to-three-byte scalar tail.
// Consumption is an observation of the stored iterator, without a runtime counter.

function adler_tail_consumed(total: int32, remaining: int32) -> Integer {
 to_integer(total) - to_integer(remaining)
}
function adler_tail_a_ceiling(consumed: Integer) -> Integer {
 327600 + 255 * consumed
}
function adler_tail_b_ceiling(consumed: Integer) -> Integer {
 1506966 + 328365 * consumed
}
theorem adler_tail_index_before_next(total: int32, remaining: int32) {
 requires 1 <= remaining;
 requires total <= 3;
 ensures adler_tail_consumed(total, remaining) <= 2 by {
  apply(int32_less_equal_to_integer(1, remaining)) using { 1 <= remaining; }
  apply(int32_less_equal_to_integer(total, 3)) using { total <= 3; }
  unfold(adler_tail_consumed(total, remaining));
  arithmetic() using { 1 <= to_integer(remaining); to_integer(total) <= 3; }
 }
}
theorem adler_tail_ceiling_before_next(k: Integer) {
 requires k <= 2;
 ensures adler_tail_a_ceiling(k) <= 328110 by {
  unfold(adler_tail_a_ceiling(k)); arithmetic() using { k <= 2; }
 }
 ensures adler_tail_b_ceiling(k) <= 2163696 by {
  unfold(adler_tail_b_ceiling(k)); arithmetic() using { k <= 2; }
 }
}
theorem adler_tail_ceiling_increments(k: Integer) {
 ensures adler_tail_a_ceiling(k + 1) == adler_tail_a_ceiling(k) + 255 by {
  unfold(adler_tail_a_ceiling(k + 1)); unfold(adler_tail_a_ceiling(k)); arithmetic() using {};
 }
 ensures adler_tail_b_ceiling(k + 1) == adler_tail_b_ceiling(k) + 328365 by {
  unfold(adler_tail_b_ceiling(k + 1)); unfold(adler_tail_b_ceiling(k)); arithmetic() using {};
 }
}
theorem adler_tail_a_next(k: Integer, a: Integer, byte: Integer) {
 requires k <= 2;
 requires a <= adler_tail_a_ceiling(k);
 requires byte <= 255;
 ensures a + byte <= 328365 by {
  apply(adler_tail_ceiling_before_next(k)) using { k <= 2; }
  arithmetic_certificate {
   premise 0: a <= adler_tail_a_ceiling(k) => a <= adler_tail_a_ceiling(k);
   premise 1: adler_tail_a_ceiling(k) <= 328110 => adler_tail_a_ceiling(k) <= 328110;
   premise 2: byte <= 255 => byte <= 255;
   add 0, 1 => a <= 328110;
   add 3, 2 => a + byte <= 328365;
   conclusion 4;
  }
 }
 ensures a + byte <= adler_tail_a_ceiling(k + 1) by {
  apply(adler_tail_ceiling_increments(k));
  rewrite(adler_tail_a_ceiling(k + 1) == adler_tail_a_ceiling(k) + 255);
  arithmetic() using { a <= adler_tail_a_ceiling(k); byte <= 255; }
 }
}
theorem adler_tail_b_next(k: Integer, a: Integer, b: Integer, byte: Integer) {
 requires k <= 2;
 requires a <= adler_tail_a_ceiling(k);
 requires b <= adler_tail_b_ceiling(k);
 requires byte <= 255;
 ensures b + a + byte <= 2492061 by {
  apply(adler_tail_ceiling_before_next(k)) using { k <= 2; }
  apply(adler_tail_a_next(k, a, byte)) using { k <= 2; a <= adler_tail_a_ceiling(k); byte <= 255; }
  arithmetic_certificate {
   premise 0: b <= adler_tail_b_ceiling(k) => b <= adler_tail_b_ceiling(k);
   premise 1: adler_tail_b_ceiling(k) <= 2163696 => adler_tail_b_ceiling(k) <= 2163696;
   premise 2: a + byte <= 328365 => a + byte <= 328365;
   add 0, 1 => b <= 2163696;
   add 3, 2 => b + a + byte <= 2492061;
   conclusion 4;
  }
 }
 ensures b + a + byte <= adler_tail_b_ceiling(k + 1) by {
  apply(adler_tail_a_next(k, a, byte)) using { k <= 2; a <= adler_tail_a_ceiling(k); byte <= 255; }
  apply(adler_tail_ceiling_increments(k));
  rewrite(adler_tail_b_ceiling(k + 1) == adler_tail_b_ceiling(k) + 328365);
  arithmetic() using { b <= adler_tail_b_ceiling(k); a + byte <= 328365; }
 }
}
theorem adler_tail_iterator_step(total: int32, remaining: int32, a: Integer, b: Integer, byte: Integer) {
 requires 1 <= remaining;
 requires total <= 3;
 requires a <= adler_tail_a_ceiling(adler_tail_consumed(total, remaining));
 requires b <= adler_tail_b_ceiling(adler_tail_consumed(total, remaining));
 requires byte <= 255;
 ensures a + byte <= 4294967295 by {
  apply(adler_tail_index_before_next(total, remaining)) using { 1 <= remaining; total <= 3; }
  apply(adler_tail_a_next(adler_tail_consumed(total, remaining), a, byte)) using { adler_tail_consumed(total, remaining) <= 2; a <= adler_tail_a_ceiling(adler_tail_consumed(total, remaining)); byte <= 255; }
  arithmetic() using { a + byte <= 328365; }
 }
 ensures b + a + byte <= 4294967295 by {
  apply(adler_tail_index_before_next(total, remaining)) using { 1 <= remaining; total <= 3; }
  apply(adler_tail_b_next(adler_tail_consumed(total, remaining), a, b, byte)) using { adler_tail_consumed(total, remaining) <= 2; a <= adler_tail_a_ceiling(adler_tail_consumed(total, remaining)); b <= adler_tail_b_ceiling(adler_tail_consumed(total, remaining)); byte <= 255; }
  arithmetic() using { b + a + byte <= 2492061; }
 }
 ensures a + byte <= adler_tail_a_ceiling(adler_tail_consumed(total, remaining) + 1) by {
  apply(adler_tail_index_before_next(total, remaining)) using { 1 <= remaining; total <= 3; }
  apply(adler_tail_a_next(adler_tail_consumed(total, remaining), a, byte)) using { adler_tail_consumed(total, remaining) <= 2; a <= adler_tail_a_ceiling(adler_tail_consumed(total, remaining)); byte <= 255; }
  assumption();
 }
 ensures b + a + byte <= adler_tail_b_ceiling(adler_tail_consumed(total, remaining) + 1) by {
  apply(adler_tail_index_before_next(total, remaining)) using { 1 <= remaining; total <= 3; }
  apply(adler_tail_b_next(adler_tail_consumed(total, remaining), a, b, byte)) using { adler_tail_consumed(total, remaining) <= 2; a <= adler_tail_a_ceiling(adler_tail_consumed(total, remaining)); b <= adler_tail_b_ceiling(adler_tail_consumed(total, remaining)); byte <= 255; }
  assumption();
 }
}
theorem adler_tail_remaining_progress(total: int32, remaining: int32) {
 requires 1 <= remaining;
 requires remaining <= total;
 requires total <= 3;
 ensures adler_tail_consumed(total, remaining - 1) == adler_tail_consumed(total, remaining) + 1 by {
  have defined(remaining - 1) by simp() using { 1 <= remaining; remaining <= total; total <= 3; };
  apply(int32_subtract_to_integer(remaining, 1)) using { defined(remaining - 1); }
  unfold(adler_tail_consumed(total, remaining - 1));
  unfold(adler_tail_consumed(total, remaining));
  arithmetic() using { to_integer(remaining - 1) == to_integer(remaining) - to_integer(1); }
 }
}
