verifying "increment.cpp";

int32 increment(int32* value) {
    requires value[0] < 2147483647;
    owns value[0..1];
    ensures value[0] == old(value[0]) + 1;
    ensures result == value[0];
} by {
    execute();
    simp();
}
