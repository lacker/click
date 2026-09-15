verifying "stage_restore.cpp";

int32 stage_restore(int32* value) {
    owns value[0..1];
    ensures value[0] == 7;
    ensures result == old(value[0]);
} by {
    execute();
    simp();
}
