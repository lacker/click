verifying "at_least_max_money.cpp";

bool at_most_max_money(const int64& value) {
    owns value;
    ensures result == (if old(value) <= 2100000000000000i64 { true } else { false });
} by {
    if value <= 2100000000000000i64 {
        step_until(function.exit);
        close();
    } else {
        step_until(function.exit);
        close();
    }
}
