verifying "rb_erase.c";
import "../rbtree-model/rbtree_resources.click";

contract void AugmentRotate(struct rb_node* old, struct rb_node* new) {
    requires new != 0; ensures 1 == 1;
}
contract void ErasePropagate(struct rb_node* node, struct rb_node* stop) {
    ensures 1 == 1;
}

contract void EraseCopy(struct rb_node* node, struct rb_node* successor) {
    requires node != 0;
    requires successor != 0;
    ensures 1 == 1;
}

resource erase_callbacks(augment: const struct rb_augment_callbacks*) {
    views augment->propagate;
    views augment->copy;
    views augment->rotate;
    fact ErasePropagate(augment->propagate);
    fact EraseCopy(augment->copy);
    fact AugmentRotate(augment->rotate);
}

void dummy_propagate(struct rb_node* node, struct rb_node* stop) {
    ensures 1 == 1;
} by { execute(); normalize(); }
void dummy_copy(struct rb_node* old, struct rb_node* new) {
    requires old != 0;
    requires new != 0;
    ensures 1 == 1;
} by { execute(); normalize(); }
void dummy_rotate(struct rb_node* old, struct rb_node* new) {
    requires new != 0;
    ensures 1 == 1;
} by { execute(); normalize(); }

theorem dummy_propagate_contract() {
    ensures ErasePropagate(&dummy_propagate) by { unfold(ErasePropagate); simp(); }
}
theorem dummy_copy_contract() {
    ensures EraseCopy(&dummy_copy) by { unfold(EraseCopy); simp(); }
}
theorem dummy_rotate_contract() {
    ensures AugmentRotate(&dummy_rotate) by { unfold(AugmentRotate); simp(); }
}

