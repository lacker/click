import click::integer;

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
  unfold(adler_tail_consumed(total, remaining));
  close() using { 1 <= to_integer(remaining); to_integer(total) <= 3; };
 }
}
theorem adler_tail_ceiling_before_next(k: Integer) {
 requires k <= 2;
 ensures adler_tail_a_ceiling(k) <= 328110 by {
  unfold(adler_tail_a_ceiling(k)); close() using { k <= 2; };
 }
 ensures adler_tail_b_ceiling(k) <= 2163696 by {
  unfold(adler_tail_b_ceiling(k)); close() using { k <= 2; };
 }
}
theorem adler_tail_ceiling_increments(k: Integer) {
 ensures adler_tail_a_ceiling(k + 1) == adler_tail_a_ceiling(k) + 255 by {
  unfold(adler_tail_a_ceiling(k + 1));
  unfold(adler_tail_a_ceiling(k));
  apply(integer::multiply_add_left(255, k, 1));
  rewrite(255 * (k + 1), 255 * k + 255 * 1);
  close() using {};
 }
 ensures adler_tail_b_ceiling(k + 1) == adler_tail_b_ceiling(k) + 328365 by {
  unfold(adler_tail_b_ceiling(k + 1));
  unfold(adler_tail_b_ceiling(k));
  apply(integer::multiply_add_left(328365, k, 1));
  rewrite(328365 * (k + 1), 328365 * k + 328365 * 1);
  close() using {};
 }
}
theorem adler_tail_a_next(k: Integer, a: Integer, byte: Integer) {
 requires k <= 2;
 requires a <= adler_tail_a_ceiling(k);
 requires byte <= 255;
 ensures a + byte <= 328365 by {
  apply(adler_tail_ceiling_before_next(k));
  close() using { a <= adler_tail_a_ceiling(k); adler_tail_a_ceiling(k) <= 328110; byte <= 255; };
 }
 ensures a + byte <= adler_tail_a_ceiling(k + 1) by {
  apply(adler_tail_ceiling_increments(k));
  rewrite(adler_tail_a_ceiling(k + 1), adler_tail_a_ceiling(k) + 255);
  close() using { a <= adler_tail_a_ceiling(k); byte <= 255; };
 }
}
theorem adler_tail_b_next(k: Integer, a: Integer, b: Integer, byte: Integer) {
 requires k <= 2;
 requires a <= adler_tail_a_ceiling(k);
 requires b <= adler_tail_b_ceiling(k);
 requires byte <= 255;
 ensures b + a + byte <= 2492061 by {
  apply(adler_tail_ceiling_before_next(k));
  apply(adler_tail_a_next(k, a, byte));
  close() using { b <= adler_tail_b_ceiling(k); adler_tail_b_ceiling(k) <= 2163696; a + byte <= 328365; };
 }
 ensures b + a + byte <= adler_tail_b_ceiling(k + 1) by {
  apply(adler_tail_a_next(k, a, byte));
  apply(adler_tail_ceiling_increments(k));
  rewrite(adler_tail_b_ceiling(k + 1), adler_tail_b_ceiling(k) + 328365);
  close() using { b <= adler_tail_b_ceiling(k); a + byte <= 328365; };
 }
}
theorem adler_tail_iterator_step(total: int32, remaining: int32, a: Integer, b: Integer, byte: Integer) {
 requires 1 <= remaining;
 requires total <= 3;
 requires a <= adler_tail_a_ceiling(adler_tail_consumed(total, remaining));
 requires b <= adler_tail_b_ceiling(adler_tail_consumed(total, remaining));
 requires byte <= 255;
 ensures a + byte <= 4294967295 by {
  apply(adler_tail_index_before_next(total, remaining));
  apply(adler_tail_a_next(adler_tail_consumed(total, remaining), a, byte));
  close() using { a + byte <= 328365; };
 }
 ensures b + a + byte <= 4294967295 by {
  apply(adler_tail_index_before_next(total, remaining));
  apply(adler_tail_b_next(adler_tail_consumed(total, remaining), a, b, byte));
  close() using { b + a + byte <= 2492061; };
 }
 ensures a + byte <= adler_tail_a_ceiling(adler_tail_consumed(total, remaining) + 1) by {
  apply(adler_tail_index_before_next(total, remaining));
  apply(adler_tail_a_next(adler_tail_consumed(total, remaining), a, byte));
  close();
 }
 ensures b + a + byte <= adler_tail_b_ceiling(adler_tail_consumed(total, remaining) + 1) by {
  apply(adler_tail_index_before_next(total, remaining));
  apply(adler_tail_b_next(adler_tail_consumed(total, remaining), a, b, byte));
  close();
 }
}
theorem adler_tail_remaining_progress(total: int32, remaining: int32) {
 requires 1 <= remaining;
 requires remaining <= total;
 requires total <= 3;
 ensures adler_tail_consumed(total, remaining - 1) == adler_tail_consumed(total, remaining) + 1 by {
  have defined(remaining - 1) by close() using { 1 <= remaining; remaining <= total; total <= 3; };
  have to_integer(remaining - 1) == to_integer(remaining) - to_integer(1);
  unfold(adler_tail_consumed(total, remaining - 1));
  unfold(adler_tail_consumed(total, remaining));
  close() using { to_integer(remaining - 1) == to_integer(remaining) - to_integer(1); };
 }
}
