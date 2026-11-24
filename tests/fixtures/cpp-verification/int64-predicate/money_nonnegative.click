verifying "money_nonnegative.cpp";

bool money_nonnegative(const int64& nValue) {
    owns nValue;
    ensures result == (if old(nValue) >= 0i64 { true } else { false });
} by {
    if nValue >= 0i64 {
        step_until(function.exit);
        close();
    } else {
        step_until(function.exit);
        close();
    }
}
