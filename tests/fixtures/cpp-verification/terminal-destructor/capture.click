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

void RestoreState_destructor(struct RestoreState* self) {
    requires separate(memory(object(self)), memory(self->pointer[0..1]));
    owns self->pointer;
    owns self->saved;
    owns self->pointer[0..1];
    ensures self->pointer == old(self->pointer);
    ensures self->saved == old(self->saved);
    ensures self->pointer[0] == old(self->saved);
} by {
    execute();
    simp();
}

int32 capture(int32* value) {
    owns value[0..1];
    ensures result == 7;
    ensures value[0] == old(value[0]);
} by {
    execute();
    simp();
}
