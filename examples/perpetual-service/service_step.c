struct service {
    int32 phase;
    int32* cell;
};

int32 service_step(struct service* owner) {
    if (owner->phase == 0) {
        owner->phase = 1;
    } else {
        owner->phase = 0;
    }
    owner->cell[0] = owner->phase;
    return owner->phase;
}
