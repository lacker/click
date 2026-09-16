verifying "at_least_max_money.cpp";

bool money_range(const int64* value) {
    owns value[0..1];
    ensures result == (if old(value[0]) >= 0i64 {
        if old(value[0]) <= 2100000000000000i64 { 1 } else { 0 }
    } else { 0 });
} by {
    if value[0] >= 0i64 {
        if value[0] <= 2100000000000000i64 {
            execute();
            simp();
        } else {
            execute();
            simp();
        }
    } else {
        execute();
        simp();
    }
}
