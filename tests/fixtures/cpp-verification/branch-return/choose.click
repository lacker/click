verifying "choose.cpp";

int32 choose(bool early, int32* value) {
    owns value[0..1];
    ensures result == (if early != 0 { 7 } else { 9 });
    ensures value[0] == result;
} by {
    execute();
    simp();
}
