verifying "at_least_one_coin.cpp";

bool at_least_one_coin(const int64* value) {
    owns value[0..1];
    ensures result == (if old(value[0]) >= 100000000i64 { 1 } else { 0 });
} by {
    if value[0] >= 100000000i64 {
        execute();
        simp();
    } else {
        execute();
        simp();
    }
}
