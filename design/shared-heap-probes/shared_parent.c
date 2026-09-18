struct child {
    int32 refs;
    int32 payload;
};

struct parent {
    struct child* kid;
};

void child_init(struct child* obj, int32 payload) {
    obj->refs = 1;
    obj->payload = payload;
}

void child_retain(struct child* obj) {
    obj->refs = obj->refs + 1;
}

void child_release(struct child* obj) {
    if (obj->refs == 1) {
        free(obj);
    } else {
        obj->refs = obj->refs - 1;
    }
}

void parent_attach(struct parent* p, struct child* kid) {
    p->kid = kid;
    child_retain(kid);
}

int32 parent_read_payload(struct parent* p) {
    struct child* kid = p->kid;
    return kid->payload;
}

void parent_detach(struct parent* p) {
    struct child* kid = p->kid;
    child_release(kid);
    p->kid = 0;
}

int32 run_first_destroyed(int32 payload) {
    struct child* kid = malloc(sizeof(struct child));
    if (kid == 0) {
        return -1;
    }
    child_init(kid, payload);
    struct parent* first = malloc(sizeof(struct parent));
    if (first == 0) {
        child_release(kid);
        return -1;
    }
    struct parent* second = malloc(sizeof(struct parent));
    if (second == 0) {
        child_release(kid);
        free(first);
        return -1;
    }
    parent_attach(first, kid);
    parent_attach(second, kid);
    child_release(kid);
    parent_detach(first);
    int32 out = parent_read_payload(second);
    parent_detach(second);
    free(first);
    free(second);
    return out;
}

int32 run_second_destroyed(int32 payload) {
    struct child* kid = malloc(sizeof(struct child));
    if (kid == 0) {
        return -1;
    }
    child_init(kid, payload);
    struct parent* first = malloc(sizeof(struct parent));
    if (first == 0) {
        child_release(kid);
        return -1;
    }
    struct parent* second = malloc(sizeof(struct parent));
    if (second == 0) {
        child_release(kid);
        free(first);
        return -1;
    }
    parent_attach(first, kid);
    parent_attach(second, kid);
    child_release(kid);
    parent_detach(second);
    int32 out = parent_read_payload(first);
    parent_detach(first);
    free(first);
    free(second);
    return out;
}
