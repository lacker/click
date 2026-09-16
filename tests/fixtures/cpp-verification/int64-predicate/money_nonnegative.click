verifying "money_nonnegative.cpp";

bool money_nonnegative(const int64* nValue) {
    owns nValue[0..1];
    ensures result == (if old(nValue[0]) >= 0i64 { 1 } else { 0 });
} by {
    if nValue[0] >= 0i64 {
        execute();
        simp();
    } else {
        execute();
        simp();
    }
}
