struct service {
    int32 phase;
    int32* cell;
};

int32 service_init(struct service* owner, int32* cell) {
    owner->phase = 0;
    owner->cell = cell;
    cell[0] = 0;
    return 0;
}
