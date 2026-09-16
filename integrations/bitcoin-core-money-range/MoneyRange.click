verifying "bitcoin-src/src/consensus/amount.h";

bool MoneyRange(const int64* nValue) {
    owns nValue[0..1];
    ensures result == (if old(nValue[0]) >= 0i64 {
        if old(nValue[0]) <= 2100000000000000i64 { 1 } else { 0 }
    } else { 0 });
} by {
    if nValue[0] >= 0i64 {
        if nValue[0] <= 2100000000000000i64 {
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
