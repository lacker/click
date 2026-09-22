verifying "stage_restore.cpp";

int32 stage_restore(struct RestoreState* state, int32* value) {
    owns &state->pointer;
    owns state->saved;
    owns value[0..1];
    ensures state->pointer == value;
    ensures state->saved == old(value[0]);
    ensures value[0] == 7;
    ensures result == old(value[0]);
} by {
    execute();
    simp();
}
