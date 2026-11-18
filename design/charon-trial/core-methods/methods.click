import click::rust::option::{unwrap_or};
import click::rust::i8;
import click::rust::i16;
import click::rust::i32;
import click::rust::i64;
import click::rust::u8;
import click::rust::u32;
import click::rust::usize;
verifying "methods.rs";

// A call of a Rust core method calls an external function whose contract
// the library supplies: its result is the library function of the same
// path, `u32::min(a, b)`, which a proof unfolds to use its definition.

fn smaller(a: u32, b: u32) -> u32 {
    ensures result == u32::min(a, b);
    ensures result <= a and result <= b;
} by {
    step_until(function.exit);
    if a <= b {
        have u32::min(a, b) == a by {
            unfold(u32::min(a, b));
            solve();
        }
    } else {
        have u32::min(a, b) == b by {
            unfold(u32::min(a, b));
            solve();
        }
    }
}

fn larger(a: i64, b: i64) -> i64 {
    ensures result == i64::max(a, b);
}

fn clamp_add(a: u32, b: u32) -> u32 {
    requires a <= 1000u32 and b <= 1000u32;
    ensures result == a + b;
} by {
    have u32::checked_add(a, b) == Option<u32>::Some(a + b) by {
        unfold(u32::checked_add(a, b));
        have to_integer(a) + to_integer(b) <= 4294967295;
        solve();
    }
}

fn spend(a: u32, b: u32) -> u32 {
    requires b <= a;
    ensures result == a - b;
} by {
    have u32::checked_sub(a, b) == Option<u32>::Some(a - b) by {
        unfold(u32::checked_sub(a, b));
        solve();
    }
}

fn shortfall(have: u32, need: u32) -> u32 {
    ensures result == u32::saturating_sub(need, have);
}

fn byte_ring(a: u8, b: u8) -> u8 {
    ensures result == u8::wrapping_add(a, b);
}

fn sample_sum(a: i16, b: i16) -> i16 {
    ensures result == i16::saturating_add(a, b);
}

fn distance(a: i32, b: i32) -> u32 {
    ensures result == i32::abs_diff(a, b);
}

fn magnitude(a: i8) -> u8 {
    ensures result == i8::unsigned_abs(a);
}

fn fewer(a: usize, b: usize) -> usize {
    ensures result == usize::min(a, b);
}

fn or_default(o: Option<u32>) -> u32 {
    ensures result == unwrap_or(o, 7u32);
    ensures o == Option<u32>::None implies result == 7u32;
}

// Each definition is Rust's at the edge of its type.

// `<[T]>::swap` owns the slice, requires both indices in bounds (Rust
// panics otherwise), exchanges the two elements and keeps every other.
fn exchange(xs: &mut [u32], a: usize, b: usize) {
    owns *xs;
    requires a < xs.len();
    requires b < xs.len();
    ensures xs[a] == old(xs[b]);
    ensures xs[b] == old(xs[a]);
    ensures forall (k: usize) { k < xs.len() and k != a and k != b implies xs[k] == old(xs[k]) };
}

fn swap_bytes(bytes: &mut [u8]) {
    owns *bytes;
    ensures bytes.len() >= 2 implies bytes[0] == old(bytes[1]);
}

// An element the call keeps is the contract's frame at that index.
fn reverse_three(xs: &mut [i64]) {
    owns *xs;
    requires xs.len() == 3;
    ensures xs[0] == old(xs[2]);
    ensures xs[1] == old(xs[1]);
    ensures xs[2] == old(xs[0]);
} by {
    step_until(function.exit);
    have 1u64 < xs.len() and 1u64 != 0u64 and 1u64 != 2u64 by { solve(); }
    have xs[1] == old(xs[1]) by {
        instantiate(forall (k: usize) { k < xs.len() and k != 0u64 and k != 2u64 implies xs[k] == old(xs[k]) }, 1u64);
        known();
    }
}

theorem i8_wrapping_add_wraps() {
    ensures i8::wrapping_add(127i8, 1i8) == -128i8 by {
        unfold(i8::wrapping_add(127i8, 1i8));
        solve();
    }
}

theorem u8_wrapping_add_wraps() {
    ensures u8::wrapping_add(200u8, 100u8) == 44u8 by {
        unfold(u8::wrapping_add(200u8, 100u8));
        solve();
    }
}

theorem i16_saturating_add_saturates() {
    ensures i16::saturating_add(30000i16, 10000i16) == 32767i16 by {
        unfold(i16::saturating_add(30000i16, 10000i16));
        solve();
    }
}

theorem i8_unsigned_abs_of_min() {
    ensures i8::unsigned_abs(-128i8) == 128u8 by {
        unfold(i8::unsigned_abs(-128i8));
        solve();
    }
}

theorem i32_abs_diff_spans_the_type() {
    ensures i32::abs_diff(-2147483648i32, 2147483647i32) == 4294967295u32 by {
        unfold(i32::abs_diff(-2147483648i32, 2147483647i32));
        solve();
    }
}
