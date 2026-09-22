verifying "conditional_restore.cpp";

void Restore_constructor(struct Restore* self, int32* slot) {
    owns &self->p;
    owns self->saved;
    owns slot[0..1];
    ensures self->p == slot;
    ensures self->saved == old(slot[0]);
    ensures slot[0] == 7;
} by {
    execute();
    simp();
}

void Restore_destructor(struct Restore* self) {
    requires self->saved == 41;
    requires separate(memory(object(self)), memory(self->p[0..1]));
    owns &self->p;
    owns self->saved;
    owns self->p[0..1];
    ensures self->p == old(self->p);
    ensures self->saved == old(self->saved);
    ensures self->p[0] == old(self->saved);
} by {
    execute();
    simp();
}

int32 conditional_restore(bool construct, bool early, int32* value) {
    owns value[0..1];
    requires value[0] == 41;
    ensures construct != 0 implies (early != 0 implies result == 7);
    ensures construct != 0 implies (early == 0 implies result == 41);
    ensures construct == 0 implies result == 41;
    ensures value[0] == 41;
} by {
    execute();
    simp();
}
