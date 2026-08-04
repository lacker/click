resource owned_item(item: struct item*) {
    if item != 0 {
        contains allocation(item, sizeof(struct item));
        owns object(item);
    }
}

verifying "item_create.c";
verifying "item_read.c";
verifying "item_destroy.c";
verifying "item_round_trip.c";
verifying "item_pipeline.c";

struct item* item_create(int32 value) {
    produces owned_item(result);
} by {
    execute();
    fold(owned_item(result));
    simp();
}

int32 item_read(struct item* item) {
    requires item != 0;
    views owned_item(item);
    immutable;

    ensures result == item->value;
} by {
    execute();
    frame();
    simp();
}

int32 item_destroy(struct item* item) {
    consumes owned_item(item);

    ensures result == 0;
} by {
    if item != 0 {
        unfold(owned_item(item));
        execute();
        simp();
    } else {
        unfold(owned_item(item));
        execute();
        simp();
    }
}

int32 item_round_trip(int32 value) {
    ensures result == -1 or result == value;
} by {
    execute();
    simp();
}

int32 item_pipeline(int32 value) {
    ensures result == -1 or result == 0;
} by {
    execute();
    simp();
}
