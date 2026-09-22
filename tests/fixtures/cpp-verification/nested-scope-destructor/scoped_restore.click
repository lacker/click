verifying "scoped_restore.cpp";

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

int32 scoped_restore(bool early, int32* value) {
    owns value[0..1];
    ensures early != 0 implies result == 7;
    ensures early == 0 implies result == old(value[0]);
    ensures value[0] == old(value[0]);
} by {
    execute();
    simp();
}
