import click::separation;
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_copy.click";
import "size_arithmetic.click";

resource optional_size(node: struct rb_node*) {
    field value: int32;
    if node != 0 {
        owns (node as (uint8 *) as (struct sized_node *))->size;
        fact (node as (uint8 *) as (struct sized_node *))->size == value;
    }
}

int32 compute_size(struct sized_node* node, int32 exit) {
    requires node != 0;
    requires defined(&node->size);
    views node->rb.rb_left;
    views node->rb.rb_right;
    owns parent: size_metadata(node as (uint8 *) as (struct rb_node *));
    owns left: optional_size(node->rb.rb_left);
    owns right: optional_size(node->rb.rb_right);
    requires node->rb.rb_left != 0 or left.value == 0;
    requires node->rb.rb_right != 0 or right.value == 0;
    requires node->rb.rb_left != node as (uint8 *) as (struct rb_node *);
    requires node->rb.rb_right != node as (uint8 *) as (struct rb_node *);
    requires 0 <= left.value;
    requires 0 <= right.value;
    requires right.value <= 2147483646;
    requires left.value <= 2147483646 - right.value;
    ensures parent.value == 1 + old(left.value) + old(right.value);
    ensures left.value == old(left.value);
    ensures right.value == old(right.value);
    ensures result == 0 or result == 1;
    ensures result == 0 or old(parent.value) == 1 + old(left.value) + old(right.value);
} by {
    if node->rb.rb_left != 0 {
        if node->rb.rb_right != 0 {
            unfold(left);
            unfold(right);
            unfold(parent);
            apply(size_sum_defined(old(left.value), old(right.value)));
            if exit == 0 {
                step_until(function.exit);
                fold(left);
                fold(right);
                let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                    value: 1 + old(left.value) + old(right.value)
                });
                solve();
            } else {
                step_until(statement(3).entry);
                if node->size == size {
                    step_until(function.exit);
                    fold(left);
                    fold(right);
                    let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                        value: 1 + old(left.value) + old(right.value)
                    });
                    solve();
                } else {
                    step_until(function.exit);
                    fold(left);
                    fold(right);
                    let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                        value: 1 + old(left.value) + old(right.value)
                    });
                    solve();
                }
            }
        } else {
            have old(right.value) == 0 by {
 cases {
 node->rb.rb_right != 0 => { contradiction(node->rb.rb_right == 0); }
 right.value == 0 => { known(); }
 }
 }
            unfold(left);
            unfold(right);
            unfold(parent);
            apply(size_sum_defined(old(left.value), old(right.value)));
            if exit == 0 {
                step_until(function.exit);
                fold(left);
                fold(right);
                let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                    value: 1 + old(left.value) + old(right.value)
                });
                solve();
            } else {
                step_until(statement(3).entry);
                if node->size == size {
                    step_until(function.exit);
                    fold(left);
                    fold(right);
                    let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                        value: 1 + old(left.value) + old(right.value)
                    });
                    solve();
                } else {
                    step_until(function.exit);
                    fold(left);
                    fold(right);
                    let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                        value: 1 + old(left.value) + old(right.value)
                    });
                    solve();
                }
            }
        }
    } else {
        have old(left.value) == 0 by {
 cases {
 node->rb.rb_left != 0 => { contradiction(node->rb.rb_left == 0); }
 left.value == 0 => { known(); }
 }
 }
        if node->rb.rb_right != 0 {
            unfold(left);
            unfold(right);
            unfold(parent);
            apply(size_sum_defined(old(left.value), old(right.value)));
            if exit == 0 {
                step_until(function.exit);
                fold(left);
                fold(right);
                let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                    value: 1 + old(left.value) + old(right.value)
                });
                solve();
            } else {
                step_until(statement(3).entry);
                if node->size == size {
                    step_until(function.exit);
                    fold(left);
                    fold(right);
                    let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                        value: 1 + old(left.value) + old(right.value)
                    });
                    solve();
                } else {
                    step_until(function.exit);
                    fold(left);
                    fold(right);
                    let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                        value: 1 + old(left.value) + old(right.value)
                    });
                    solve();
                }
            }
        } else {
            have old(right.value) == 0 by {
 cases {
 node->rb.rb_right != 0 => { contradiction(node->rb.rb_right == 0); }
 right.value == 0 => { known(); }
 }
 }
            unfold(left);
            unfold(right);
            unfold(parent);
            apply(size_sum_defined(old(left.value), old(right.value)));
            if exit == 0 {
                step_until(function.exit);
                fold(left);
                fold(right);
                let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                    value: 1 + old(left.value) + old(right.value)
                });
                solve();
            } else {
                step_until(statement(3).entry);
                if node->size == size {
                    step_until(function.exit);
                    fold(left);
                    fold(right);
                    let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                        value: 1 + old(left.value) + old(right.value)
                    });
                    solve();
                } else {
                    step_until(function.exit);
                    fold(left);
                    fold(right);
                    let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), {
                        value: 1 + old(left.value) + old(right.value)
                    });
                    solve();
                }
            }
        }
    }
}

contract int32 ComputeSize(struct sized_node* node, int32 exit) {
    requires node != 0;
    requires defined(&node->size);
    views node->rb.rb_left;
    views node->rb.rb_right;
    owns parent: size_metadata(node as (uint8 *) as (struct rb_node *));
    owns left: optional_size(node->rb.rb_left);
    owns right: optional_size(node->rb.rb_right);
    requires node->rb.rb_left != 0 or left.value == 0;
    requires node->rb.rb_right != 0 or right.value == 0;
    requires node->rb.rb_left != node as (uint8 *) as (struct rb_node *);
    requires node->rb.rb_right != node as (uint8 *) as (struct rb_node *);
    requires node->rb.rb_left == 0 or separate(memory(node->rb.rb_left), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size));
    requires node->rb.rb_left == 0 or separate(memory(node->rb.rb_right), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size));
    requires node->rb.rb_right == 0 or separate(memory(node->rb.rb_left), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size));
    requires node->rb.rb_right == 0 or separate(memory(node->rb.rb_right), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size));
    requires 0 <= left.value;
    requires 0 <= right.value;
    requires right.value <= 2147483646;
    requires left.value <= 2147483646 - right.value;
    ensures parent.value == 1 + old(left.value) + old(right.value);
    ensures left.value == old(left.value);
    ensures right.value == old(right.value);
    ensures result == 0 or result == 1;
    ensures result == 0 or old(parent.value) == 1 + old(left.value) + old(right.value);
}

theorem size_metadata_separate_from_links(base: int32*, metadata: Resource) {
    requires separate(memory(base[2..4]), metadata);
    requires separate(memory(base[4..6]), metadata);
    ensures separate(metadata, memory(base[2..6])) by {
        apply(separation::separate_star(memory(base[2..4]), memory(base[4..6]), metadata));
        apply(separation::contains_joined_ranges(base, 2, 4, 6));
        apply(separation::contains_refl(metadata));
        apply(separation::separate_restrict(memory(base[2..4]) * memory(base[4..6]), metadata,
            memory(base[2..6]), metadata));
        apply(separation::separate_symm(memory(base[2..6]), metadata));
    }
}

theorem compute_size_has_size_contract()
    executes compute_size(struct sized_node* node, int32 exit) {
    ensures ComputeSize(&compute_size) as { parent: p, left: l, right: r } by {
        apply(separation::separate_adjacent_ranges(node as (int32 *), 2, 6, 8));
        apply(separation::separate_symm(memory((node as (int32 *))[2..6]), memory((node as (int32 *))[6..8])));
        apply(size_sum_defined(l.value, r.value));
        if node->rb.rb_left != 0 {
            if node->rb.rb_right != 0 {
                have separate(memory(node->rb.rb_left), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        node->rb.rb_left == 0 => { contradiction(node->rb.rb_left == 0); }
                        separate(memory(node->rb.rb_left), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                have separate(memory(node->rb.rb_right), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        node->rb.rb_left == 0 => { contradiction(node->rb.rb_left == 0); }
                        separate(memory(node->rb.rb_right), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                have separate(memory(node->rb.rb_left), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        node->rb.rb_right == 0 => { contradiction(node->rb.rb_right == 0); }
                        separate(memory(node->rb.rb_left), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                have separate(memory(node->rb.rb_right), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        node->rb.rb_right == 0 => { contradiction(node->rb.rb_right == 0); }
                        separate(memory(node->rb.rb_right), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                apply(size_metadata_separate_from_links(node as (int32 *), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size)));
                apply(size_metadata_separate_from_links(node as (int32 *), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size)));
                step(compute_size, { parent: p, left: l, right: r });
                solve();
            } else {
                have separate(memory(node->rb.rb_left), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        node->rb.rb_left == 0 => { contradiction(node->rb.rb_left == 0); }
                        separate(memory(node->rb.rb_left), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                have separate(memory(node->rb.rb_right), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        node->rb.rb_left == 0 => { contradiction(node->rb.rb_left == 0); }
                        separate(memory(node->rb.rb_right), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                apply(size_metadata_separate_from_links(node as (int32 *), memory((node->rb.rb_left as (uint8 *) as (struct sized_node *))->size)));
                step(compute_size, { parent: p, left: l, right: r });
                solve();
            }
        } else {
            if node->rb.rb_right != 0 {
                have separate(memory(node->rb.rb_left), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        node->rb.rb_right == 0 => { contradiction(node->rb.rb_right == 0); }
                        separate(memory(node->rb.rb_left), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                have separate(memory(node->rb.rb_right), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) by {
                    cases {
                        node->rb.rb_right == 0 => { contradiction(node->rb.rb_right == 0); }
                        separate(memory(node->rb.rb_right), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size)) => { known(); }
                    }
                }
                apply(size_metadata_separate_from_links(node as (int32 *), memory((node->rb.rb_right as (uint8 *) as (struct sized_node *))->size)));
                step(compute_size, { parent: p, left: l, right: r });
                solve();
            } else {
                step(compute_size, { parent: p, left: l, right: r });
                solve();
            }
        }
    }
}


tactic child_size_separation(node: struct sized_node*, child: struct rb_node*) {
    owns node->rb;
    owns metadata: optional_size(child);
    requires child != 0;
    ensures metadata.value == old(metadata.value);
    ensures separate(memory(node->rb.rb_left), memory((child as (uint8 *) as (struct sized_node *))->size));
    ensures separate(memory(node->rb.rb_right), memory((child as (uint8 *) as (struct sized_node *))->size));
} by {
    unfold(metadata);
    have separate(memory(node->rb.rb_left), memory((child as (uint8 *) as (struct sized_node *))->size)) by known();
    have separate(memory(node->rb.rb_right), memory((child as (uint8 *) as (struct sized_node *))->size)) by known();
    fold(metadata);
}
