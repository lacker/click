verifying "slices.rs";

// A slice of any integer element, shared or mutable, is a pointer and a
// length, as a byte slice is: indexed reads and writes owe Rust's index
// panic check, the length is `xs.len()`, and a slice passes to a callee
// whole. Iteration keeps the shared slice iterator's cursor and remaining
// count, as `examples/rust-iterators` does for bytes.

fn first(xs: &[i32]) -> i32 {
    views *xs;
    ensures xs.len() == 0 implies result == 0;
    ensures xs.len() > 0 implies result == xs[0];
}

fn sum(xs: &[u32]) -> u32 {
    views *xs;
    ensures true;
} by {
    step_until(loop(0).entry);
    loop {
        decreases xs.len() - i;
        invariant i <= xs.len();
    }
}

fn zero(xs: &mut [u64]) {
    owns *xs;
    ensures xs.len() == old(xs.len());
} by {
    step_until(loop(0).entry);
    loop {
        decreases xs.len() - i;
        invariant i <= xs.len();
    }
}

fn set_at(xs: &mut [i64], k: usize, v: i64) {
    owns *xs;
    requires k < xs.len();
    ensures xs[k] == v;
}

fn get(xs: &[u16], k: usize) -> u16 {
    views *xs;
    requires k < xs.len();
    ensures result == xs[k];
}

fn swap_ends(xs: &mut [i8]) {
    owns *xs;
    ensures xs.len() >= 2 implies xs[0] == old(xs[xs.len() - 1]);
} by {
    if xs.len() >= 2 {
        have 0u64 < xs.len() - 1u64 by { close(); }
        have xs.len() - 1u64 < xs.len() by { close(); }
        have ((xs.len() - 1u64) as uint64) != 0u64 by close();
        step_until(function.exit);
        have xs[0] == old(xs[xs.len() - 1]) by {
            close();
        }
        close();
    } else {
        step_until(function.exit);
        close();
    }
}

fn last(xs: &[i64]) -> i64 {
    views xs[0..xs.len()];
    requires xs.len() <= 1000u64;
    ensures true;
} by {
    step_until(loop(0).entry);
    loop {
        decreases iter.len();
        views xs[0..xs.len()];
        invariant xs.len() <= 1000u64;
        invariant iter.len() <= xs.len();
        invariant iter.as_slice().as_ptr() == xs.as_ptr() + (xs.len() - iter.len());
        maintain by {
            if 0u64 < iter.len() {
                mark iteration;
                have to_integer(xs.len() - iter.len()) < 18446744073709551615;
                have to_integer(xs.len() - iter.len()) < to_integer(xs.len());
                have to_integer(xs.len() - iter.len()) + 1 <= to_integer(xs.len());
                have to_integer((xs.len() - iter.len()) + 1u64) <= to_integer(xs.len());
                have to_integer(xs.len() - iter.len()) + 1 <= 18446744073709551615;
                have (xs.as_ptr() + (xs.len() - iter.len())) + 1u64 == xs.as_ptr() + ((xs.len() - iter.len()) + 1u64);
                step_until(loop.back_edge);
                have to_integer(iter.len()) == to_integer(at(iteration, iter.len())) - 1;
                have to_integer(xs.len() - iter.len()) == to_integer(xs.len()) - to_integer(iter.len());
                have to_integer(xs.len() - at(iteration, iter.len())) == to_integer(xs.len()) - to_integer(at(iteration, iter.len()));
                have to_integer((xs.len() - at(iteration, iter.len())) + 1u64) == to_integer(xs.len() - at(iteration, iter.len())) + 1;
                have to_integer(xs.len() - iter.len()) == to_integer((xs.len() - at(iteration, iter.len())) + 1u64);
                have (xs.len() - at(iteration, iter.len())) + 1u64 == xs.len() - iter.len();
                have iter.as_slice().as_ptr() == xs.as_ptr() + (xs.len() - iter.len());
                have iter.len() <= xs.len();
                have iter.len() < at(iteration, iter.len());
            } else {
                step(); step(); step(); step(); step();
            }
        }
    }
}

fn head(xs: &[u64]) -> u64 {
    views *xs;
    ensures xs.len() > 0 implies result == xs[0];
}

fn head_twice(xs: &[u64]) -> u64 {
    views *xs;
    ensures xs.len() > 0 implies result == xs[0];
}

fn clear_first(xs: &mut [i16]) {
    owns *xs;
    ensures xs.len() > 0 implies xs[0] == 0i16;
}

fn clear_twice(xs: &mut [i16]) {
    owns *xs;
    ensures xs.len() > 0 implies xs[0] == 0i16;
}
