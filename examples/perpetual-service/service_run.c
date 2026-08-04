struct service {
    int32 phase;
    int32* cell;
};

int32 service_run(struct service* owner) {
    int32 status;
    while (1) {
        status = service_step(owner);
    }
    return status;
}
