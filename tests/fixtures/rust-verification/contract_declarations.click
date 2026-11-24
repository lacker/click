verifying "callback.rs";

contract fn Doubling(x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}

fn function_pointers::twice(x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}

fn function_pointers::apply(f: fn(i32) -> i32, x: i32) -> i32 {
    requires Doubling(f);
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}

theorem twice_is_doubling() {
    ensures Doubling(function_pointers::twice) by {
        unfold(Doubling(function_pointers::twice));
        close();
    }
}

fn function_pointers::caller(x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
} by { apply(twice_is_doubling()); }
