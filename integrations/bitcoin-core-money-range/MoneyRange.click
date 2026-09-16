verifying "bitcoin-src/src/consensus/amount.h";

bool MoneyRange(const int64* nValue) {
    owns nValue[0..1];
    ensures nValue[0] == old(nValue[0]);
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

contract bool BelowRange(const int64* nValue) {
    requires nValue[0] == -1i64;
    owns nValue[0..1];
    ensures nValue[0] == old(nValue[0]);
    ensures result == 0;
}

theorem below_range_is_false() executes MoneyRange(const int64* nValue) {
    ensures BelowRange(&MoneyRange) by {
        execute();
        simp();
    }
}

contract bool AtZero(const int64* nValue) {
    requires nValue[0] == 0i64;
    owns nValue[0..1];
    ensures nValue[0] == old(nValue[0]);
    ensures result == 1;
}

theorem zero_is_in_range() executes MoneyRange(const int64* nValue) {
    ensures AtZero(&MoneyRange) by {
        execute();
        simp();
    }
}

contract bool AtMaxMoney(const int64* nValue) {
    requires nValue[0] == 2100000000000000i64;
    owns nValue[0..1];
    ensures nValue[0] == old(nValue[0]);
    ensures result == 1;
}

theorem max_money_is_in_range() executes MoneyRange(const int64* nValue) {
    ensures AtMaxMoney(&MoneyRange) by {
        execute();
        simp();
    }
}

contract bool AboveRange(const int64* nValue) {
    requires nValue[0] == 2100000000000001i64;
    owns nValue[0..1];
    ensures nValue[0] == old(nValue[0]);
    ensures result == 0;
}

theorem above_range_is_false() executes MoneyRange(const int64* nValue) {
    ensures AboveRange(&MoneyRange) by {
        execute();
        simp();
    }
}
