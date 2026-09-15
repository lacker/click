verifying "capture.cpp";

void RestoreState_constructor(struct RestoreState* self, int32* slot) {
    owns self->pointer;
    owns self->saved;
    owns slot[0..1];
    ensures self->pointer == slot;
    ensures self->saved == old(slot[0]);
    ensures slot[0] == 7;
} by {
    execute();
    simp();
}

int32 capture(int32* value) {
    owns value[0..1];
    ensures value[0] == 7;
    ensures result == old(value[0]);
} by {
    execute();
    simp();
}
