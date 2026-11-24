verifying "at_least_max_money.cpp";

bool money_range(const int64& value) {
    owns value;
    ensures result == (if old(value) >= 0i64 {
        if old(value) <= 2100000000000000i64 { true } else { false }
    } else { false });
} by {
    if value >= 0i64 {
        if value <= 2100000000000000i64 {
            step_until(function.exit);
            close();
        } else {
            step_until(function.exit);
            close();
        }
    } else {
        step_until(function.exit);
        close();
    }
}
