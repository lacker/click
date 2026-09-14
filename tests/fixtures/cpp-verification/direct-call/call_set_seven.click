verifying "call_set_seven.cpp";

int32 set_seven(int32* value) {
    owns value[0..1];
    ensures value[0] == 7;
    ensures result == value[0];
} by {
    execute();
    simp();
}

int32 call_set_seven(int32* value) {
    owns value[0..1];
    ensures value[0] == 7;
    ensures result == value[0];
} by {
    execute();
    simp();
}
