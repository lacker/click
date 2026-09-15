verifying "relay_value.cpp";

int32 read_value(int32* value) {
    owns value[0..1];
    ensures value[0] == old(value[0]);
    ensures result == value[0];
} by {
    execute();
    simp();
}

int32 relay_value(int32* value) {
    requires value[0] < 2147483647;
    owns value[0..1];
    ensures result == value[0] + 1;
} by {
    execute();
    simp();
}
