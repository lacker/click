abstract resource mutex_guard(mutex: void*);
abstract resource mutex_live(mutex: void*);
abstract resource mutex_use(mutex: void*);
abstract resource publisher(flag: void*);
abstract resource subscriber(flag: void*);
abstract resource authority();
abstract resource allocation(base: int32*, bytes: int32);

spec enum Nat {
    Zero,
    Succ(Nat),
}

theorem nat_integer_zero() {
    ensures to_integer(Nat::Zero) == 0;
}

theorem nat_integer_succ(n: Nat) {
    ensures to_integer(Nat::Succ(n)) == to_integer(n) + 1;
}

theorem nat_integer_nonnegative(n: Nat) {
    ensures to_integer(n) >= 0;
}

theorem nat_integer_round_trip(n: Nat) {
    ensures to_nat(to_integer(n)) == n;
}

theorem integer_nat_round_trip(z: Integer) {
    requires z >= 0;
    ensures to_integer(to_nat(z)) == z;
}

theorem integer_to_nat_zero() {
    ensures to_nat(0) == Nat::Zero;
}


function nat_add(left: Nat, right: Nat) -> Nat
    decreases left
{
    match left {
        Nat::Zero => right,
        Nat::Succ(previous) => Nat::Succ(nat_add(previous, right)),
    }
}

theorem nat_add_left_identity(n: Nat) {
    ensures nat_add(Nat::Zero, n) == n by {
        unfold(nat_add(Nat::Zero, n));
        normalize();
    }
}

theorem nat_add_succ_left(n: Nat, m: Nat) {
    ensures nat_add(Nat::Succ(n), m) == Nat::Succ(nat_add(n, m)) by {
        unfold(nat_add(Nat::Succ(n), m));
        normalize();
    }
}

theorem nat_integer_add(n: Nat, m: Nat) {
    ensures to_integer(nat_add(n, m)) == to_integer(n) + to_integer(m) by {
        induct(n) as ih {
            Nat::Zero => {
                unfold(nat_add(Nat::Zero, m));
                apply(nat_integer_zero());
                arithmetic_certificate {
                    premise 0: to_integer(Nat::Zero) == 0 => to_integer(Nat::Zero) == 0;
                    scale 0 by -1 => to_integer(m) == to_integer(Nat::Zero) + to_integer(m);
                    conclusion 1;
                }
            }
            Nat::Succ(previous) => {
                unfold(nat_add(Nat::Succ(previous), m));
                apply(nat_integer_succ(nat_add(previous, m)));
                apply(ih(previous));
                apply(nat_integer_succ(previous));
                arithmetic_certificate {
                    premise 0: to_integer(Nat::Succ(nat_add(previous, m))) == to_integer(nat_add(previous, m)) + 1 => to_integer(Nat::Succ(nat_add(previous, m))) == to_integer(nat_add(previous, m)) + 1;
                    premise 1: to_integer(nat_add(previous, m)) == to_integer(previous) + to_integer(m) => to_integer(nat_add(previous, m)) == to_integer(previous) + to_integer(m);
                    premise 2: to_integer(Nat::Succ(previous)) == to_integer(previous) + 1 => to_integer(Nat::Succ(previous)) == to_integer(previous) + 1;
                    add 0, 1 => to_integer(Nat::Succ(nat_add(previous, m))) == to_integer(previous) + to_integer(m) + 1;
                    scale 2 by -1 => to_integer(previous) + 1 == to_integer(Nat::Succ(previous));
                    add 3, 4 => to_integer(Nat::Succ(nat_add(previous, m))) == to_integer(Nat::Succ(previous)) + to_integer(m);
                    conclusion 5;
                }
            }
        }
    }
}

theorem nat_add_right_identity(n: Nat) {
    ensures nat_add(n, Nat::Zero) == n by {
        induct(n) as ih {
            Nat::Zero => {
                unfold(nat_add(Nat::Zero, Nat::Zero));
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                unfold(nat_add(Nat::Succ(previous), Nat::Zero));
                rewrite(nat_add(previous, Nat::Zero) == previous);
                normalize();
            }
        }
    }
}

theorem nat_add_succ_right(n: Nat, m: Nat) {
    ensures nat_add(n, Nat::Succ(m)) == Nat::Succ(nat_add(n, m)) by {
        induct(n) as ih {
            Nat::Zero => {
                unfold(nat_add(Nat::Zero, Nat::Succ(m)));
                unfold(nat_add(Nat::Zero, m));
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                unfold(nat_add(Nat::Succ(previous), Nat::Succ(m)));
                unfold(nat_add(Nat::Succ(previous), m));
                rewrite(nat_add(previous, Nat::Succ(m)) == Nat::Succ(nat_add(previous, m)));
                normalize();
            }
        }
    }
}

theorem nat_add_associative(a: Nat, b: Nat, c: Nat) {
    ensures nat_add(nat_add(a, b), c) == nat_add(a, nat_add(b, c)) by {
        induct(a) as ih {
            Nat::Zero => {
                unfold(nat_add(Nat::Zero, b));
                unfold(nat_add(Nat::Zero, nat_add(b, c)));
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                apply(nat_add_succ_left(previous, b));
                rewrite(nat_add(Nat::Succ(previous), b) == Nat::Succ(nat_add(previous, b)));
                apply(nat_add_succ_left(nat_add(previous, b), c));
                rewrite(nat_add(Nat::Succ(nat_add(previous, b)), c)
                    == Nat::Succ(nat_add(nat_add(previous, b), c)));
                apply(nat_add_succ_left(previous, nat_add(b, c)));
                rewrite(nat_add(Nat::Succ(previous), nat_add(b, c))
                    == Nat::Succ(nat_add(previous, nat_add(b, c))));
                rewrite(nat_add(nat_add(previous, b), c) == nat_add(previous, nat_add(b, c)));
                normalize();
            }
        }
    }
}

theorem nat_add_commutative(a: Nat, b: Nat) {
    ensures nat_add(a, b) == nat_add(b, a) by {
        induct(a) as ih {
            Nat::Zero => {
                unfold(nat_add(Nat::Zero, b));
                apply(nat_add_right_identity(b));
                rewrite(nat_add(b, Nat::Zero) == b);
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                unfold(nat_add(Nat::Succ(previous), b));
                apply(nat_add_succ_right(b, previous));
                rewrite(nat_add(b, Nat::Succ(previous)) == Nat::Succ(nat_add(b, previous)));
                rewrite(nat_add(previous, b) == nat_add(b, previous));
                normalize();
            }
        }
    }
}


spec enum List<T> {
    Nil,
    Cons(T, List<T>),
}

function list_append<T>(xs: List<T>, ys: List<T>) -> List<T>
    decreases xs
{
    match xs {
        List::Nil => ys,
        List::Cons(head, tail) => List<T>::Cons(head, list_append(tail, ys)),
    }
}

function list_contains<T>(xs: List<T>, value: T) -> bool
    decreases xs
{
    match xs {
        List::Nil => false,
        List::Cons(head, tail) =>
            if head == value { true } else { list_contains(tail, value) },
    }
}

theorem list_append_left_identity<T>(xs: List<T>) {
    ensures list_append(List<T>::Nil, xs) == xs by {
        unfold(list_append(List<T>::Nil, xs));
        normalize();
    }
}

theorem list_append_right_identity<T>(xs: List<T>) {
    ensures list_append(xs, List<T>::Nil) == xs by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list_append(List<T>::Nil, List<T>::Nil));
                normalize();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                unfold(list_append(List<T>::Cons(head, tail), List<T>::Nil));
                rewrite(list_append(tail, List<T>::Nil) == tail);
                normalize();
            }
        }
    }
}

theorem list_append_cons<T>(head: T, tail: List<T>, ys: List<T>) {
    ensures list_append(List<T>::Cons(head, tail), ys)
        == List<T>::Cons(head, list_append(tail, ys)) by {
        unfold(list_append(List<T>::Cons(head, tail), ys));
        normalize();
    }
}

theorem list_append_associative<T>(xs: List<T>, ys: List<T>, zs: List<T>) {
    ensures list_append(list_append(xs, ys), zs)
        == list_append(xs, list_append(ys, zs)) by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list_append(List<T>::Nil, ys));
                unfold(list_append(List<T>::Nil, list_append(ys, zs)));
                simp();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                apply(list_append_cons(head, tail, ys));
                rewrite(list_append(List<T>::Cons(head, tail), ys)
                    == List<T>::Cons(head, list_append(tail, ys)));
                apply(list_append_cons(head, list_append(tail, ys), zs));
                rewrite(list_append(List<T>::Cons(head, list_append(tail, ys)), zs)
                    == List<T>::Cons(head, list_append(list_append(tail, ys), zs)));
                apply(list_append_cons(head, tail, list_append(ys, zs)));
                rewrite(list_append(List<T>::Cons(head, tail), list_append(ys, zs))
                    == List<T>::Cons(head, list_append(tail, list_append(ys, zs))));
                rewrite(list_append(list_append(tail, ys), zs)
                    == list_append(tail, list_append(ys, zs)));
                simp();
            }
        }
    }
}

theorem list_contains_nil<T>(value: T) {
    ensures list_contains(List<T>::Nil, value) == false by {
        unfold(list_contains(List<T>::Nil, value));
        normalize();
    }
}

theorem list_contains_cons<T>(head: T, tail: List<T>, value: T) {
    ensures list_contains(List<T>::Cons(head, tail), value)
        == if head == value { true } else { list_contains(tail, value) } by {
        unfold(list_contains(List<T>::Cons(head, tail), value));
        normalize();
    }
}

theorem list_contains_append<T>(xs: List<T>, ys: List<T>, value: T) {
    ensures list_contains(list_append(xs, ys), value)
        == if list_contains(xs, value) { true } else { list_contains(ys, value) } by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list_append(List<T>::Nil, ys));
                unfold(list_contains(List<T>::Nil, value));
                simp();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                apply(list_append_cons(head, tail, ys));
                rewrite(list_append(List<T>::Cons(head, tail), ys)
                    == List<T>::Cons(head, list_append(tail, ys)));
                if head == value {
                    apply(list_contains_cons(head, list_append(tail, ys), value));
                    rewrite(list_contains(List<T>::Cons(head, list_append(tail, ys)), value)
                        == if head == value { true } else { list_contains(list_append(tail, ys), value) });
                    apply(list_contains_cons(head, tail, value));
                    rewrite(list_contains(List<T>::Cons(head, tail), value)
                        == if head == value { true } else { list_contains(tail, value) });
                    normalize() using { head == value; }
                } else {
                    apply(list_contains_cons(head, list_append(tail, ys), value));
                    rewrite(list_contains(List<T>::Cons(head, list_append(tail, ys)), value)
                        == if head == value { true } else { list_contains(list_append(tail, ys), value) });
                    apply(list_contains_cons(head, tail, value));
                    rewrite(list_contains(List<T>::Cons(head, tail), value)
                        == if head == value { true } else { list_contains(tail, value) });
                    rewrite(list_contains(list_append(tail, ys), value)
                        == if list_contains(tail, value) { true } else { list_contains(ys, value) });
                    normalize() using { not(head == value); }
                }
            }
        }
    }
}

function list_length<T>(xs: List<T>) -> Nat
    decreases xs
{
    match xs {
        List::Nil => Nat::Zero,
        List::Cons(head, tail) => Nat::Succ(list_length(tail)),
    }
}

theorem list_length_nil<T>(xs: List<T>) {
    requires xs == List<T>::Nil;
    ensures list_length(xs) == Nat::Zero by {
        rewrite(xs == List<T>::Nil);
        unfold(list_length(List<T>::Nil));
        normalize();
    }
}

theorem list_length_cons<T>(head: T, tail: List<T>) {
    ensures list_length(List<T>::Cons(head, tail)) == Nat::Succ(list_length(tail)) by {
        unfold(list_length(List<T>::Cons(head, tail)));
        normalize();
    }
}

theorem list_length_append<T>(xs: List<T>, ys: List<T>) {
    ensures list_length(list_append(xs, ys)) == nat_add(list_length(xs), list_length(ys)) by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list_append(List<T>::Nil, ys));
                unfold(list_length(List<T>::Nil));
                unfold(nat_add(Nat::Zero, list_length(ys)));
                simp();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                apply(list_append_cons(head, tail, ys));
                rewrite(list_append(List<T>::Cons(head, tail), ys)
                    == List<T>::Cons(head, list_append(tail, ys)));
                apply(list_length_cons(head, list_append(tail, ys)));
                rewrite(list_length(List<T>::Cons(head, list_append(tail, ys)))
                    == Nat::Succ(list_length(list_append(tail, ys))));
                apply(list_length_cons(head, tail));
                rewrite(list_length(List<T>::Cons(head, tail)) == Nat::Succ(list_length(tail)));
                apply(nat_add_succ_left(list_length(tail), list_length(ys)));
                rewrite(nat_add(Nat::Succ(list_length(tail)), list_length(ys))
                    == Nat::Succ(nat_add(list_length(tail), list_length(ys))));
                rewrite(list_length(list_append(tail, ys)) == nat_add(list_length(tail), list_length(ys)));
                normalize();
            }
        }
    }
}

theorem int32_increment_upper_bound(value: int32, upper: int32) {
    requires value < upper;

    ensures value + 1 <= upper;
}

theorem int32_increment_strictly_increases(value: int32, upper: int32) {
    requires value < upper;

    ensures value < value + 1;
}

theorem int32_increment_lower_bound(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures lower <= value + 1;
}

theorem int32_increment_greater_equal_lower_bound(value: int32, lower: int32, upper: int32) {
    requires value >= lower;
    requires value < upper;

    ensures value + 1 >= lower;
}

theorem int32_increment_greater_than_lower_bound(value: int32, lower: int32, upper: int32) {
    requires value >= lower;
    requires value < upper;

    ensures value + 1 > lower;
}

theorem int32_increment_preserves_order(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures lower + 1 <= value + 1;
}

theorem int32_increment_less_equal_implies_less_than(lower: int32, value: int32) {
    requires lower < lower + 1;
    requires lower + 1 <= value;

    ensures lower < value;
}

theorem int32_less_than_increment_implies_less_equal(value: int32, upper: int32) {
    requires value < upper + 1;

    ensures value <= upper;
}

theorem int32_positive_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= value;
}

theorem int32_less_than_implies_less_equal(left: int32, right: int32) {
    requires left < right;

    ensures left <= right;
}

theorem int32_less_than_implies_not_equal(left: int32, right: int32) {
    requires left < right;

    ensures left != right;
}

theorem int32_not_less_than_implies_greater_equal(left: int32, right: int32) {
    requires not (left < right);

    ensures left >= right;
}

theorem int32_increment_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(value + 1);
}

theorem int32_increment_left_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(1 + value);
}

theorem int32_increment_left_strictly_increases(value: int32) {
    requires value < 2147483647;

    ensures value < 1 + value;
}

theorem int32_nonnegative_add_within_max_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires value <= 2147483647 - amount;

    ensures defined(value + amount);
}

theorem int32_nonnegative_subtract_within_value_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires amount <= value;

    ensures defined(value - amount);
}

theorem int32_move_one_from_right_to_left_preserves_sum(
    total: int32,
    left: int32,
    right: int32
) {
    requires 0 <= left;
    requires 1 <= right;
    requires total == left + right;

    ensures total == (left + 1) + (right - 1);
}

theorem int32_subtract_equal_sum_right_cancels(value: int32, left: int32, amount: int32) {
    requires defined(left + amount) and value == left + amount;
    requires defined(value - amount);

    ensures value - amount == left by {
        rewrite(value == left + amount);
        simp();
    }
}

theorem int32_add_nonnegative_right_is_at_least_left(left: int32, right: int32) {
    requires 0 <= right;
    requires defined(left + right);

    ensures left <= left + right;
}

theorem int32_add_nonnegative_left_is_at_least_right(left: int32, right: int32) {
    requires 0 <= left;
    requires defined(left + right);

    ensures right <= left + right;
}

theorem int32_positive_predecessor_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= value - 1;
}

theorem int32_above_one_predecessor_is_at_least_one(value: int32) {
    requires 1 < value;

    ensures value - 1 >= 1;
}

theorem int32_positive_predecessor_strictly_decreases(value: int32) {
    requires 0 < value;

    ensures value - 1 < value;
}

theorem uint32_positive_predecessor_strictly_decreases(value: uint32) {
    requires 0u32 < value;

    ensures value - 1u32 < value;
}

theorem uint32_increment_upper_bound(value: uint32, upper: uint32) {
    requires value < upper;

    ensures value + 1u32 <= upper;
}

theorem uint32_increment_strictly_increases(value: uint32, upper: uint32) {
    requires value < upper;

    ensures value < value + 1u32;
}

theorem uint32_less_than_implies_positive_difference(value: uint32, upper: uint32) {
    requires value < upper;

    ensures 0u32 < upper - value;
}

theorem uint32_difference_decreases_after_increment(value: uint32, bound: uint32) {
    requires value < bound;

    ensures (0u32 - value) + (bound - 1u32) < (0u32 - value) + bound;
}

theorem uint32_less_than_less_equal_transitive(first: uint32, middle: uint32, last: uint32) {
    requires first < middle;
    requires middle <= last;

    ensures first < last;
}

theorem uint32_less_equal_less_than_transitive(first: uint32, middle: uint32, last: uint32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last;
}

theorem uint32_less_than_transitive(first: uint32, middle: uint32, last: uint32) {
    requires first < middle;
    requires middle < last;

    ensures first < last;
}

theorem uint32_less_equal_transitive(first: uint32, middle: uint32, last: uint32) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last;
}

theorem uint64_less_than_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first < middle;
    requires middle <= last;

    ensures first < last;
}

theorem uint64_less_equal_less_than_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first <= middle;
    requires middle < last;

    ensures first < last;
}

theorem uint64_less_than_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first < middle;
    requires middle < last;

    ensures first < last;
}

theorem uint64_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last;
}

theorem uint64_less_equal_and_not_less_than_implies_equal(left: uint64, right: uint64) {
    requires left <= right;
    requires not left < right;

    ensures left == right;
}

theorem int64_less_than_less_equal_transitive(first: int64, middle: int64, last: int64) {
    requires first < middle;
    requires middle <= last;

    ensures first < last;
}

theorem int64_less_equal_less_than_transitive(first: int64, middle: int64, last: int64) {
    requires first <= middle;
    requires middle < last;

    ensures first < last;
}

theorem int64_less_than_transitive(first: int64, middle: int64, last: int64) {
    requires first < middle;
    requires middle < last;

    ensures first < last;
}

theorem int64_less_equal_transitive(first: int64, middle: int64, last: int64) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last;
}

theorem uint32_greater_than_implies_reversed_less_than(greater: uint32, lower: uint32) {
    requires greater > lower;

    ensures lower < greater;
}

theorem uint32_less_than_implies_reversed_greater_than(lower: uint32, greater: uint32) {
    requires lower < greater;

    ensures greater > lower;
}

theorem uint32_greater_equal_implies_reversed_less_equal(greater: uint32, lower: uint32) {
    requires greater >= lower;

    ensures lower <= greater;
}

theorem uint32_less_equal_implies_reversed_greater_equal(lower: uint32, greater: uint32) {
    requires lower <= greater;

    ensures greater >= lower;
}

theorem int32_nonnegative_predecessor_upper_bound(value: int32, bound: int32) {
    requires 0 <= value;
    requires value <= bound;

    ensures value - 1 <= bound;
}

theorem int32_less_equal_less_than_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last;
}

theorem int32_less_equal_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last;
}

theorem int32_less_than_transitive(first: int32, middle: int32, last: int32) {
    requires first < middle;
    requires middle < last;

    ensures first < last;
}

theorem int32_less_than_less_equal_transitive(first: int32, middle: int32, last: int32) {
    requires first < middle;
    requires middle <= last;

    ensures first < last;
}

theorem int32_greater_equal_transitive(last: int32, middle: int32, first: int32) {
    requires last >= middle;
    requires middle >= first;

    ensures last >= first;
}

theorem int32_greater_equal_implies_reversed_less_equal(greater: int32, lower: int32) {
    requires greater >= lower;

    ensures lower <= greater;
}

theorem int32_less_equal_implies_reversed_greater_equal(lower: int32, greater: int32) {
    requires lower <= greater;

    ensures greater >= lower;
}

theorem int32_less_equal_and_not_less_than_implies_equal(left: int32, right: int32) {
    requires left <= right;
    requires not (left < right);

    ensures left == right;
}

theorem int32_less_equal_and_not_equal_implies_less_than(left: int32, right: int32) {
    requires left <= right;
    requires left != right;

    ensures left < right;
}

theorem int32_greater_equal_and_not_greater_than_implies_equal(left: int32, right: int32) {
    requires left >= right;
    requires not (left > right);

    ensures left == right;
}

function count(p: int32[], lo: int32, hi: int32, x: int32) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}

predicate permutation(a: int32[], b: int32[], lo: int32, hi: int32) {
    forall (x: int32) {
        count(a, lo, hi, x) == count(b, lo, hi, x)
    }
}

// Byte ranges are measured as C measures them: an index or count is a
// `size_t`. `byte_count` keeps 32-bit bounds: a C-valued fold over `size_t`
// indices is not yet evaluated (bugs/uint64-c-valued-range-fold-drops-every-path.md).
function byte_count(bytes: uint8[], lo: int32, hi: int32, value: uint8) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if bytes[k] == value { 1 } else { 0 }
    })
}

predicate bytes_equal(left: uint8[], left_lo: uint64, right: uint8[], right_lo: uint64, len: uint64) {
    (0u64..len).all(|k| {
        left[left_lo + k] == right[right_lo + k]
    })
}

predicate bytes_equal_range(left: uint8[], right: uint8[], lo: uint64, hi: uint64) {
    (lo..hi).all(|k| {
        left[k] == right[k]
    })
}

predicate bytes_all_equal(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    (lo..hi).all(|k| {
        bytes[k] == value
    })
}

predicate bytes_contains(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    (lo..hi).any(|k| {
        bytes[k] == value
    })
}

predicate bytes_all_not_equal(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    (lo..hi).all(|k| {
        bytes[k] != value
    })
}

// C strings, measured as C measures them: a length is a `size_t`. A string
// of length `len` occupies `len + 1` bytes, so `len` is below `SIZE_MAX`,
// which also keeps `len + 1` exact.
predicate cstr_prefix(bytes: uint8[], len: uint64) {
    forall (k: uint64) { k < len implies bytes[k] != '\0' }
}

predicate cstr_len(bytes: uint8[], len: uint64) {
    len < 18446744073709551615u64 and
        viewable(bytes[0..len + 1u64]) and
        cstr_prefix(bytes, len) and
        bytes[len] == '\0'
}

predicate cstr(bytes: uint8[]) {
    exists (len: uint64) {
        cstr_len(bytes, len)
    }
}

predicate cstr_readable_len(bytes: uint8[], len: uint64) {
    len < 18446744073709551615u64 and
        viewable(bytes[0..len + 1u64]) and
        forall (k: uint64) { k < len implies bytes[k] != '\0' } and
        bytes[len] == '\0' and
        forall (k: uint64) { k < len + 1u64 implies defined(bytes[k]) }
}

theorem cstr_readable_len_unique(bytes: uint8[], left: uint64, right: uint64) {
    requires forall (k: uint64) { k < left implies bytes[k] != '\0' };
    requires bytes[left] == '\0';
    requires forall (k: uint64) { k < right implies bytes[k] != '\0' };
    requires bytes[right] == '\0';

    ensures left == right by {
        have left < right or not (left < right) by {
            if left < right {
                assumption();
            } else {
                assumption();
            }
        }
        cases {
            left < right => {
                instantiate(forall (k: uint64) { k < right implies bytes[k] != '\0' }, left)
                    using { left < right; }
                contradiction(bytes[left] == '\0');
            }
            not (left < right) => {
                have right < left or not (right < left) by {
                    if right < left {
                        assumption();
                    } else {
                        assumption();
                    }
                }
                cases {
                    right < left => {
                        instantiate(forall (k: uint64) { k < left implies bytes[k] != '\0' }, right)
                            using { right < left; }
                        contradiction(bytes[right] == '\0');
                    }
                    not (right < left) => {
                        have left <= right by {
                            simp();
                        }
                        apply(uint64_less_equal_and_not_less_than_implies_equal(left, right)) using {
                            left <= right;
                            not (left < right);
                        }
                    }
                }
            }
        }
    }
}

predicate cstr_readable(bytes: uint8[]) {
    exists (len: uint64) {
        len < 18446744073709551615u64 and
            viewable(bytes[0..len + 1u64]) and
            forall (k: uint64) { k < len implies bytes[k] != '\0' } and
            bytes[len] == '\0' and
            forall (k: uint64) { k < len + 1u64 implies defined(bytes[k]) }
    }
}

predicate cstr_bounded(bytes: uint8[], max: uint64) {
    exists (k: uint64) { k < max and bytes[k] == '\0' }
}

theorem cstr_len_is_viewable(bytes: uint8[], len: uint64) {
    requires cstr_len(bytes, len);

    ensures viewable(bytes[0..len + 1u64]) by {
        unfold(cstr_len);
        simp();
    }
}

theorem cstr_len_has_prefix(bytes: uint8[], len: uint64) {
    requires cstr_len(bytes, len);

    ensures cstr_prefix(bytes, len) by {
        unfold(cstr_len);
        simp();
    }
}

theorem cstr_len_has_terminator(bytes: uint8[], len: uint64) {
    requires cstr_len(bytes, len);

    ensures bytes[len] == '\0' by {
        unfold(cstr_len);
        simp();
    }
}

extern int32 __click_constant_p_unknown() {
    ensures result == 0 or result == 1;
}

// The C library's byte functions, with C's `size_t` counts. C converts
// `memset`'s `int` fill value to `unsigned char`; Click models that narrowing
// only for a representable value, so the value is required to be one.
extern uint8* memcpy(uint8 destination[], const uint8 source[], uint64 bytes) {
    requires viewable(source[0..bytes]);
    owns destination[0..bytes];
    requires separate(memory(destination[0..bytes]), memory(source[0..bytes]));
    ensures result == destination;
    ensures bytes_equal(destination, 0u64, old(source), 0u64, bytes);
}

extern int32 memcmp(const uint8 left[], const uint8 right[], uint64 bytes) {
    requires viewable(left[0..bytes]);
    requires viewable(right[0..bytes]);
    requires forall (k: uint64) { k < bytes implies defined(left[k]) and defined(right[k]) };
    ensures result == 0 implies bytes_equal(left, 0u64, right, 0u64, bytes);
    ensures result != 0 implies not bytes_equal(left, 0u64, right, 0u64, bytes);
}

extern uint8* memset(uint8 destination[], int32 value, uint64 bytes) {
    requires 0 <= value;
    requires value <= 255;
    owns destination[0..bytes];
    ensures result == destination;
    ensures (0u64..bytes).all(|k| {
        defined(destination[k]) and destination[k] == value
    });
}

extern uint64 strlen(const uint8* bytes) {
    requires cstr_readable(bytes);
    ensures result < 18446744073709551615u64;
    ensures viewable(bytes[0..result + 1u64]);
    ensures forall (k: uint64) { k < result implies bytes[k] != '\0' };
    ensures bytes[result] == '\0';
    ensures cstr_readable_len(bytes, result);
    ensures old(bytes[0]) == '\0' implies result == 0u64;
}

theorem uint32_widened_add_guard_by_integer_bound(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures ((int64)left + (int64)right) <= 4294967295i64;
}

theorem uint32_add_to_integer(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right);
}

// Exact unsigned subtraction needs the native no-underflow guard.
theorem uint32_subtract_to_integer(left: uint32, right: uint32) {
    requires right <= left;
    ensures to_integer(left - right) == to_integer(left) - to_integer(right);
}

theorem uint64_add_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) + to_integer(right) <= 18446744073709551615;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right);
}

theorem uint64_multiply_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) * to_integer(right) <= 18446744073709551615;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right);
}

theorem uint64_subtract_to_integer(left: uint64, right: uint64) {
    requires to_integer(right) <= to_integer(left);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right);
}

theorem uint64_divide_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right));
}

theorem uint64_remainder_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}

theorem uint64_less_equal_to_integer(left: uint64, right: uint64) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right);
}

theorem uint64_to_integer_less_equal_implies_less_equal(left: uint64, right: uint64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right;
}

theorem uint64_less_than_to_integer(left: uint64, right: uint64) {
    requires left < right;
    ensures to_integer(left) < to_integer(right);
}

theorem uint64_to_integer_less_than_implies_less_than(left: uint64, right: uint64) {
    requires to_integer(left) < to_integer(right);
    ensures left < right;
}

theorem uint32_pack_uint16_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high);
}

theorem uint32_pack_uint16_high_first_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer((high << 16) | low) == to_integer(low) + 65536 * to_integer(high);
}

// Exact round trips of two bounded fields packed with the high field first.
theorem uint32_unpack_uint16_low(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures (((high << 16) | low) & 65535u32) == low;
}

theorem uint32_unpack_uint16_high(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures ((((high << 16) | low) >> 16) & 65535u32) == high;
}

theorem uint64_pack_uint16_to_integer(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high);
}

theorem uint64_less_than_implies_not_greater_equal(left: uint64, right: uint64) {
    requires left < right;
    ensures not (left >= right);
}

theorem uint64_to_integer_equal_implies_equal(left: uint64, right: uint64) {
    requires to_integer(left) == to_integer(right);
    ensures left == right;
}

// Exact observations of unsigned division require both evaluation domains.
theorem uint32_divide_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right));
}

theorem uint32_remainder_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}

theorem uint32_multiply_to_integer(left: uint32, right: uint32) {
    requires right == 0u32 or left <= 4294967295u32 / right;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right);
}

theorem uint32_multiply_guard_by_integer_bound(left: uint32, right: uint32) {
    requires to_integer(left) * to_integer(right) <= 4294967295;
    ensures right == 0u32 or left <= 4294967295u32 / right;
}

theorem uint32_less_equal_to_integer(left: uint32, right: uint32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right);
}

theorem uint32_to_integer_less_equal_implies_less_equal(left: uint32, right: uint32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right;
}

theorem uint32_to_integer_equal_implies_equal(left: uint32, right: uint32) {
    requires to_integer(left) == to_integer(right);
    ensures left == right;
}

theorem uint32_less_than_to_integer(left: uint32, right: uint32) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by {
        if to_integer(right) <= to_integer(left) {
            apply(uint32_to_integer_less_equal_implies_less_equal(right, left));
            contradiction(left < right);
        } else {
            arithmetic() using { not (to_integer(right) <= to_integer(left)); }
        }
    }
}

theorem uint32_remainder_less_than_divisor(value: uint32, divisor: uint32) {
    requires divisor != 0u32;
    ensures value % divisor < divisor;
}

theorem uint32_less_than_divisor_implies_remainder_is_value(value: uint32, divisor: uint32) {
    requires value < divisor;
    ensures value % divisor == value;
}

theorem uint32_to_integer_bounds(value: uint32) {
    ensures 0 <= to_integer(value) by {
        have 0u32 <= value;
        apply(uint32_less_equal_to_integer(0u32, value)) using { 0u32 <= value; }
    }
    ensures to_integer(value) <= 4294967295 by {
        have value <= 4294967295u32;
        apply(uint32_less_equal_to_integer(value, 4294967295u32)) using { value <= 4294967295u32; }
    }
}

// Unsigned zero is the lower endpoint; excluding it gives a strict native order.
// This proof uses the existing remainder and transitivity laws, not a new axiom.
theorem uint32_nonzero_implies_positive(value: uint32) {
    requires value != 0u32;
    ensures 0u32 < value by {
        have 0u32 % value < value by {
            apply(uint32_remainder_less_than_divisor(0u32, value)) using { value != 0u32; }
        }
        have 0u32 <= 0u32 % value by {
            apply(uint32_to_integer_bounds(0u32 % value));
            apply(uint32_to_integer_less_equal_implies_less_equal(0u32, 0u32 % value)) using {
                0 <= to_integer(0u32 % value);
            }
        }
        apply(uint32_less_equal_less_than_transitive(0u32, 0u32 % value, value)) using {
            0u32 <= 0u32 % value;
            0u32 % value < value;
        }
    }
}

// Checked source proof of the mathematical domain from native nonzero.

theorem uint32_nonzero_to_integer(value: uint32) {
 requires value != 0u32;
 ensures to_integer(value) != 0 by {
  apply(uint32_remainder_less_than_divisor(0u32, value)) using { value != 0u32; }
  apply(uint32_less_than_to_integer(0u32 % value, value)) using { 0u32 % value < value; }
  apply(uint32_to_integer_bounds(0u32 % value));
  have 1 <= to_integer(value) by {
   arithmetic() using { 0 <= to_integer(0u32 % value); to_integer(0u32 % value) < to_integer(value); }
  }
  arithmetic_certificate rules {
   premise 0: 1 <= to_integer(value) => 1 <= to_integer(value);
   integer_bound_exclusion bounds [0] => to_integer(value) != 0;
   conclusion 0;
  }
 }
}

theorem uint64_to_integer_bounds(value: uint64) {
    ensures 0 <= to_integer(value) by {
        have 0u64 <= value;
        apply(uint64_less_equal_to_integer(0u64, value)) using { 0u64 <= value; }
    }
    ensures to_integer(value) <= 18446744073709551615 by {
        have value <= 18446744073709551615u64;
        apply(uint64_less_equal_to_integer(value, 18446744073709551615u64)) using { value <= 18446744073709551615u64; }
    }
}

theorem int32_add_to_integer(left: int32, right: int32) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right);
}

theorem int32_less_equal_to_integer(left: int32, right: int32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right);
}

theorem int32_to_integer_bounds(value: int32) {
    ensures -2147483648 <= to_integer(value) by {
        have -2147483648 <= value;
        apply(int32_less_equal_to_integer(-2147483648, value)) using { -2147483648 <= value; }
    }
    ensures to_integer(value) <= 2147483647 by {
        have value <= 2147483647;
        apply(int32_less_equal_to_integer(value, 2147483647)) using { value <= 2147483647; }
    }
}

theorem int32_to_integer_equal_implies_equal(left: int32, right: int32) {
    requires to_integer(left) == to_integer(right);
    ensures left == right;
}

theorem int32_to_integer_less_equal_implies_less_equal(left: int32, right: int32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right;
}

theorem int32_less_than_to_integer(left: int32, right: int32) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by {
        if to_integer(right) <= to_integer(left) {
            apply(int32_to_integer_less_equal_implies_less_equal(right, left));
            contradiction(left < right);
        } else {
            arithmetic() using { not (to_integer(right) <= to_integer(left)); }
        }
    }
}

theorem int64_less_equal_to_integer(left: int64, right: int64) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right);
}

theorem int64_to_integer_bounds(value: int64) {
    ensures -9223372036854775808 <= to_integer(value) by {
        have -9223372036854775808i64 <= value;
        apply(int64_less_equal_to_integer(-9223372036854775808i64, value)) using { -9223372036854775808i64 <= value; }
    }
    ensures to_integer(value) <= 9223372036854775807 by {
        have value <= 9223372036854775807i64;
        apply(int64_less_equal_to_integer(value, 9223372036854775807i64)) using { value <= 9223372036854775807i64; }
    }
}

theorem int64_less_than_to_integer(left: int64, right: int64) {
    requires left < right;
    ensures to_integer(left) < to_integer(right);
}

theorem int64_greater_equal_to_integer(left: int64, right: int64) {
    requires left >= right;
    ensures to_integer(left) >= to_integer(right);
}

theorem int64_to_integer_less_equal_implies_less_equal(left: int64, right: int64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right;
}

theorem int64_to_integer_equal_implies_equal(left: int64, right: int64) {
    requires to_integer(left) == to_integer(right);
    ensures left == right;
}

theorem int32_subtract_to_integer(left: int32, right: int32) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right);
}

theorem int32_remainder_to_integer(left: int32, right: int32) {
    requires defined(left % right);
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}

theorem int32_add_defined_by_integer_bounds(left: int32, right: int32) {
    requires to_integer(left) + to_integer(right) >= -2147483648;
    requires to_integer(left) + to_integer(right) <= 2147483647;
    ensures defined(left + right);
}

theorem int32_subtract_defined_by_integer_bounds(left: int32, right: int32) {
    requires to_integer(left) - to_integer(right) >= -2147483648;
    requires to_integer(left) - to_integer(right) <= 2147483647;
    ensures defined(left - right);
}

theorem integer_to_int8_round_trip(z: Integer) {
    requires z >= -128;
    requires z <= 127;
    ensures to_integer(to_int8(z)) == z;
}

theorem integer_to_int16_round_trip(z: Integer) {
    requires z >= -32768;
    requires z <= 32767;
    ensures to_integer(to_int16(z)) == z;
}

theorem integer_to_int32_round_trip(z: Integer) {
    requires z >= -2147483648;
    requires z <= 2147483647;
    ensures to_integer(to_int32(z)) == z;
}

theorem integer_to_uint8_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 255;
    ensures to_integer(to_uint8(z)) == z;
}

theorem integer_to_uint16_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 65535;
    ensures to_integer(to_uint16(z)) == z;
}

theorem integer_to_uint32_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 4294967295;
    ensures to_integer(to_uint32(z)) == z;
}

theorem integer_to_int64_round_trip(z: Integer) {
    requires z >= -9223372036854775808;
    requires z <= 9223372036854775807;
    ensures to_integer(to_int64(z)) == z;
}

theorem integer_to_uint64_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 18446744073709551615;
    ensures to_integer(to_uint64(z)) == z;
}

theorem int64_add_defined_by_integer_bounds(left: int64, right: int64) {
    requires to_integer(left) + to_integer(right) >= -9223372036854775808;
    requires to_integer(left) + to_integer(right) <= 9223372036854775807;
    ensures defined(left + right);
}

theorem int64_subtract_defined_by_integer_bounds(left: int64, right: int64) {
    requires to_integer(left) - to_integer(right) >= -9223372036854775808;
    requires to_integer(left) - to_integer(right) <= 9223372036854775807;
    ensures defined(left - right);
}

theorem int64_to_integer_less_than_implies_less_than(left: int64, right: int64) {
    requires to_integer(left) < to_integer(right);
    ensures left < right;
}

theorem int64_add_to_integer(left: int64, right: int64) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right);
}

theorem int64_subtract_to_integer(left: int64, right: int64) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right);
}

theorem integer_truncation_identity(n: Integer, d: Integer) {
    requires d != 0;
    ensures n == truncating_quotient(n, d) * d + truncating_remainder(n, d);
}

theorem integer_positive_divisor_remainder_lower(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures 1 - d <= truncating_remainder(n, d);
}

theorem integer_positive_divisor_remainder_upper(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures truncating_remainder(n, d) <= d - 1;
}

theorem integer_nonnegative_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 <= n;
    ensures 0 <= truncating_remainder(n, d);
}

theorem integer_nonpositive_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires n <= 0;
    ensures truncating_remainder(n, d) <= 0;
}


theorem integer_multiply_add(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c by {
        arithmetic_certificate rules {
            integer_polynomial_identity bounds [] => (a + b) * c == a * c + b * c;
            conclusion 0;
        }
    }
}

theorem integer_floor_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires r < 0 implies value == q + -1;
    requires 0 <= r implies value == q;
    ensures value * d <= n by {
        if r < 0 {
            have value == q + -1;
            apply(integer_multiply_add(q, -1, d));
            rewrite(value == q + -1);
            rewrite((q + -1) * d == q * d + -1 * d);
            arithmetic() using { n == q * d + r; 1 - d <= r; }
        } else {
            have 0 <= r by { arithmetic() using { not (r < 0); } }
            have value == q;
            rewrite(value == q);
            arithmetic() using { n == q * d + r; 0 <= r; }
        }
    }
    ensures n < (value + 1) * d by {
        if r < 0 {
            have value == q + -1;
            have value + 1 == q by { arithmetic() using { value == q + -1; } }
            rewrite(value + 1 == q);
            arithmetic() using { n == q * d + r; r < 0; }
        } else {
            have 0 <= r by { arithmetic() using { not (r < 0); } }
            have value == q;
            apply(integer_multiply_add(q, 1, d));
            rewrite(value == q);
            rewrite((q + 1) * d == q * d + 1 * d);
            arithmetic() using { n == q * d + r; r <= d - 1; }
        }
    }
}

theorem integer_ceiling_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires 0 < r implies value == q + 1;
    requires r <= 0 implies value == q;
    ensures n <= value * d by {
        if 0 < r {
            have value == q + 1;
            apply(integer_multiply_add(q, 1, d));
            rewrite(value == q + 1);
            rewrite((q + 1) * d == q * d + 1 * d);
            arithmetic() using { n == q * d + r; r <= d - 1; }
        } else {
            have r <= 0 by { arithmetic() using { not (0 < r); } }
            have value == q;
            rewrite(value == q);
            arithmetic() using { n == q * d + r; r <= 0; }
        }
    }
    ensures (value + -1) * d < n by {
        if 0 < r {
            have value == q + 1;
            have value + -1 == q by { arithmetic() using { value == q + 1; } }
            rewrite(value + -1 == q);
            arithmetic() using { n == q * d + r; 0 < r; }
        } else {
            have r <= 0 by { arithmetic() using { not (0 < r); } }
            have value == q;
            apply(integer_multiply_add(q, -1, d));
            rewrite(value == q);
            rewrite((q + -1) * d == q * d + -1 * d);
            arithmetic() using { n == q * d + r; 1 - d <= r; }
        }
    }
}

theorem integer_positive_divisor_quotient_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound * d <= n;
    ensures bound <= truncating_quotient(n, d) by {
        arithmetic_certificate rules {
            premise 0: bound * d <= n => bound * d <= n;
            premise 1: 1 <= d => 1 <= d;
            integer_quotient_bound bounds [0, 1] => bound <= truncating_quotient(n, d);
            conclusion 0;
        }
    }
}

theorem integer_positive_divisor_quotient_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= bound * d;
    ensures truncating_quotient(n, d) <= bound by {
        arithmetic_certificate rules {
            premise 0: n <= bound * d => n <= bound * d;
            premise 1: 1 <= d => 1 <= d;
            integer_quotient_bound bounds [0, 1] => truncating_quotient(n, d) <= bound;
            conclusion 0;
        }
    }
}

theorem integer_positive_divisor_quotient_strict_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound < 0;
    requires bound * d < n;
    ensures bound < truncating_quotient(n, d) by {
        have bound * d <= n by { arithmetic() using { bound * d < n; } }
        apply(integer_positive_divisor_quotient_lower(n, d, bound));
        if bound < truncating_quotient(n, d) {
            assumption();
        } else {
            have truncating_quotient(n, d) == bound by { arithmetic() using {
                bound <= truncating_quotient(n, d); not (bound < truncating_quotient(n, d));
            } }
            if n <= 0 {
                have 0 < d by { arithmetic() using { 1 <= d; } }
                apply(integer_nonpositive_dividend_remainder(n, d));
                apply(integer_truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound == truncating_quotient(n, d));
                    assumption();
                }
                have not (bound * d < n) by { arithmetic() using {
                    n == bound * d + truncating_remainder(n, d); truncating_remainder(n, d) <= 0;
                } }
                contradiction(bound * d < n);
            } else {
                have 0 <= n by { arithmetic() using { not (n <= 0); } }
                have 0 * d <= n by { arithmetic() using { 0 <= n; } }
                apply(integer_positive_divisor_quotient_lower(n, d, 0));
                have not (bound < 0) by { arithmetic() using {
                    0 <= truncating_quotient(n, d); truncating_quotient(n, d) == bound;
                } }
                contradiction(bound < 0);
            }
        }
    }
}

theorem integer_positive_divisor_quotient_strict_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 < bound;
    requires n < bound * d;
    ensures truncating_quotient(n, d) < bound by {
        have n <= bound * d by { arithmetic() using { n < bound * d; } }
        apply(integer_positive_divisor_quotient_upper(n, d, bound));
        if truncating_quotient(n, d) < bound {
            assumption();
        } else {
            have truncating_quotient(n, d) == bound by { arithmetic() using {
                truncating_quotient(n, d) <= bound; not (truncating_quotient(n, d) < bound);
            } }
            if 0 <= n {
                have 0 < d by { arithmetic() using { 1 <= d; } }
                apply(integer_nonnegative_dividend_remainder(n, d));
                apply(integer_truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound == truncating_quotient(n, d));
                    assumption();
                }
                have not (n < bound * d) by { arithmetic() using {
                    n == bound * d + truncating_remainder(n, d); 0 <= truncating_remainder(n, d);
                } }
                contradiction(n < bound * d);
            } else {
                have n <= 0 by { arithmetic() using { not (0 <= n); } }
                have n <= 0 * d by { arithmetic() using { n <= 0; } }
                apply(integer_positive_divisor_quotient_upper(n, d, 0));
                have not (0 < bound) by { arithmetic() using {
                    truncating_quotient(n, d) <= 0; truncating_quotient(n, d) == bound;
                } }
                contradiction(0 < bound);
            }
        }
    }
}

theorem integer_lower_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, lower: Integer) {
    requires lower <= q;
    requires lower * d <= n;
    requires n == q * d + r;
    requires r < 0;
    ensures lower + 1 <= q by {
        if lower + 1 <= q {
            assumption();
        } else {
            have q == lower by { arithmetic() using { lower <= q; not (lower + 1 <= q); } }
            have n == lower * d + r by {
                rewrite(lower == q);
                assumption();
            }
            have not (r < 0) by { arithmetic() using { lower * d <= n; n == lower * d + r; } }
            contradiction(r < 0);
        }
    }
}

theorem integer_upper_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, upper: Integer) {
    requires q <= upper;
    requires n <= upper * d;
    requires n == q * d + r;
    requires 0 < r;
    ensures q <= upper + -1 by {
        if q <= upper + -1 {
            assumption();
        } else {
            have q == upper by { arithmetic() using { q <= upper; not (q <= upper + -1); } }
            have n == upper * d + r by {
                rewrite(upper == q);
                assumption();
            }
            have not (0 < r) by { arithmetic() using { n <= upper * d; n == upper * d + r; } }
            contradiction(0 < r);
        }
    }
}
theorem integer_multiply_order_nonnegative(a: Integer, b: Integer, factor: Integer) {
    requires a <= b;
    requires 0 <= factor;
    ensures a * factor <= b * factor by {
        arithmetic_certificate rules {
            premise 0: a <= b => a <= b;
            premise 1: 0 <= factor => 0 <= factor;
            integer_multiply_order bounds [0, 1] => a * factor <= b * factor;
            conclusion 0;
        }
    }
}

theorem integer_multiply_order_nonpositive(a: Integer, b: Integer, factor: Integer) {
    requires a <= b;
    requires factor <= 0;
    ensures b * factor <= a * factor by {
        arithmetic_certificate rules {
            premise 0: a <= b => a <= b;
            premise 1: factor <= 0 => factor <= 0;
            integer_multiply_order bounds [0, 1] => b * factor <= a * factor;
            conclusion 0;
        }
    }
}

theorem integer_scaled_product_bounds(value: Integer, amount: Integer, size: Integer, lower: Integer, upper: Integer) {
    requires lower <= value;
    requires value <= upper;
    requires lower <= 0;
    requires 0 <= upper;
    requires 0 <= amount;
    requires amount <= size;
    ensures lower * size <= value * amount by {
        apply(integer_multiply_order_nonnegative(lower, value, amount));
        have lower * size <= lower * amount by {
            arithmetic_certificate rules {
                premise 0: amount <= size => amount <= size;
                premise 1: lower <= 0 => lower <= 0;
                integer_multiply_order bounds [0, 1] => lower * size <= lower * amount;
                conclusion 0;
            }
        }
        arithmetic() using { lower * size <= lower * amount; lower * amount <= value * amount; }
    }
    ensures value * amount <= upper * size by {
        apply(integer_multiply_order_nonnegative(value, upper, amount));
        have upper * amount <= upper * size by {
            arithmetic_certificate rules {
                premise 0: amount <= size => amount <= size;
                premise 1: 0 <= upper => 0 <= upper;
                integer_multiply_order bounds [0, 1] => upper * amount <= upper * size;
                conclusion 0;
            }
        }
        arithmetic() using { value * amount <= upper * amount; upper * amount <= upper * size; }
    }
}
