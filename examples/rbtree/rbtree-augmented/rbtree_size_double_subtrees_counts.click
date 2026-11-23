import click::integer;
// Cache arithmetic when both children of the focused node survive a rotation.
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_double_middle_counts.click";

theorem sized_double_subtrees_bounds(pv: int32, far: SizedTree, middle: SizedTree, other: SizedTree) {
    requires sized_counts_valid(far) == 1;
    requires sized_counts_valid(middle) == 1;
    requires sized_counts_valid(other) == 1;
    requires to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) + to_integer(sized_value(other));
    ensures defined(pv - 1)
        and 0 <= sized_value(far)
        and 0 <= sized_value(middle)
        and 0 <= sized_value(other)
        and sized_value(middle) <= 2147483646
        and sized_value(far) <= 2147483646 - sized_value(middle)
        and sized_value(far) <= 2147483646
        and sized_value(middle) <= 2147483646 - sized_value(far)
        and 1 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) <= 2147483647 by {
        apply(sized_valid_value_nonnegative(far));
        apply(sized_valid_value_nonnegative(middle));
        apply(sized_valid_value_nonnegative(other));
        have -2147483648 <= to_integer(pv);
        have to_integer(pv) <= 2147483647;
        have to_integer(pv) - to_integer(1) >= -2147483648 by {
            solve() using {
                to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) + to_integer(sized_value(other));
                0 <= to_integer(sized_value(far));
                0 <= to_integer(sized_value(middle));
                0 <= to_integer(sized_value(other));
            };
        }
        have to_integer(pv) - to_integer(1) <= 2147483647 by {
            solve() using { to_integer(pv) <= 2147483647; };
        }
        have defined(pv - 1);
        have 1 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) <= 2147483647 by {
            solve() using {
                to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) + to_integer(sized_value(other));
                to_integer(pv) <= 2147483647;
                0 <= to_integer(sized_value(other));
            };
        }
        have 1 + to_integer(sized_value(middle)) + to_integer(sized_value(far)) <= 2147483647 by {
            solve() using { 1 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) <= 2147483647; };
        }
        apply(size_children_fit(sized_value(far), sized_value(middle)));
        apply(size_children_fit(sized_value(middle), sized_value(far)));
        have 0 <= sized_value(other);
        have to_integer(sized_value(far)) <= 2147483646 - to_integer(sized_value(middle)) by {
            solve() using { 1 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) <= 2147483647; };
        }
        have to_integer(sized_value(middle)) <= 2147483646 - to_integer(sized_value(far)) by {
            solve() using { 1 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) <= 2147483647; };
        }
        known();
    }
}

theorem sized_double_subtrees_subtract_other_defined(pv: int32, far: SizedTree, middle: SizedTree, other: SizedTree) {
    requires sized_counts_valid(far) == 1;
    requires sized_counts_valid(middle) == 1;
    requires sized_counts_valid(other) == 1;
    requires to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) + to_integer(sized_value(other));
    requires defined(pv - 1);
    ensures defined(pv - 1 - sized_value(other)) by {
        apply(sized_valid_value_nonnegative(far));
        apply(sized_valid_value_nonnegative(middle));
        apply(sized_valid_value_nonnegative(other));
        have -2147483648 <= to_integer(pv);
        have to_integer(pv) <= 2147483647;
        apply(integer::int32_subtract_to_integer(pv, 1));
        have to_integer(pv - 1) - to_integer(sized_value(other)) >= -2147483648 by {
            solve() using {
                to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) + to_integer(sized_value(other));
                to_integer(pv - 1) == to_integer(pv) - to_integer(1);
                0 <= to_integer(sized_value(far));
                0 <= to_integer(sized_value(middle));
            };
        }
        have to_integer(pv - 1) - to_integer(sized_value(other)) <= 2147483647 by {
            solve() using {
                to_integer(pv - 1) == to_integer(pv) - to_integer(1);
                to_integer(pv) <= 2147483647;
                0 <= to_integer(sized_value(other));
            };
        }
        have defined((pv - 1) - sized_value(other));
        apply(integer::int32_subtract_to_integer(pv - 1, sized_value(other)));
        known();
    }
}

theorem sized_double_subtrees_repaired_count(pv: int32, far: SizedTree, middle: SizedTree, other: SizedTree) {
    requires to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) + to_integer(sized_value(other));
    requires defined(pv - 1);
    requires defined(pv - 1 - sized_value(other));
    ensures to_integer(pv - 1 - sized_value(other)) == 1 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) by {
        apply(integer::int32_subtract_to_integer(pv, 1));
        apply(integer::int32_subtract_to_integer(pv - 1, sized_value(other)));
        solve() using {
            to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) + to_integer(sized_value(other));
            to_integer(pv - 1) == to_integer(pv) - to_integer(1);
            to_integer(pv - 1 - sized_value(other)) == to_integer(pv - 1) - to_integer(sized_value(other));
        };
    }
}

// The first writable callback repairs the demoted parent while retaining both
// focused-node children. Its promoted cache is the original parent's cache.
theorem sized_double_subtrees_inner_valid(p: struct rb_node*, node: struct rb_node*, pv: int32,
                                          far: SizedTree, middle: SizedTree, other: SizedTree) {
    requires sized_counts_valid(far) == 1;
    requires sized_counts_valid(middle) == 1;
    requires sized_counts_valid(other) == 1;
    requires defined(pv - 1);
    requires defined(pv - 1 - sized_value(other));
    requires to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) + to_integer(sized_value(other));
    ensures sized_counts_valid(SizedTree::Node(p, node, Color::Red, pv - 1 - sized_value(other), far,
                sized_recolor(sized_reparent(middle, p), Color::Black))) == 1
        and sized_counts_valid(SizedTree::Node(node, p, Color::Red, pv,
                SizedTree::Node(p, node, Color::Red, pv - 1 - sized_value(other), far,
                    sized_recolor(sized_reparent(middle, p), Color::Black)), other)) == 1 by {
        apply(sized_double_subtrees_repaired_count(pv, far, middle, other));
        apply(sized_reparent_observations(middle, p));
        apply(sized_recolor_observations(sized_reparent(middle, p), Color::Black));
        have sized_counts_valid(sized_recolor(sized_reparent(middle, p), Color::Black)) == 1 by {
            rewrite(sized_counts_valid(sized_recolor(sized_reparent(middle, p), Color::Black)), sized_counts_valid(sized_reparent(middle, p)));
            rewrite(sized_counts_valid(sized_reparent(middle, p)), sized_counts_valid(middle));
            known();
        }
        have to_integer(pv - 1 - sized_value(other)) == 1 + to_integer(sized_value(far))
                + to_integer(sized_value(sized_recolor(sized_reparent(middle, p), Color::Black))) by {
            rewrite(sized_value(sized_recolor(sized_reparent(middle, p), Color::Black)), sized_value(sized_reparent(middle, p)));
            rewrite(sized_value(sized_reparent(middle, p)), sized_value(middle));
            known();
        }
        apply(sized_valid_node(p, node, Color::Red, pv - 1 - sized_value(other), far,
            sized_recolor(sized_reparent(middle, p), Color::Black)));
        unfold(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1 - sized_value(other), far,
            sized_recolor(sized_reparent(middle, p), Color::Black))));
        have to_integer(pv) == 1 + to_integer(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1 - sized_value(other), far,
                    sized_recolor(sized_reparent(middle, p), Color::Black)))) + to_integer(sized_value(other)) by {
            unfold(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1 - sized_value(other), far,
                    sized_recolor(sized_reparent(middle, p), Color::Black))));
            solve() using {
                to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(middle)) + to_integer(sized_value(other));
                to_integer(pv - 1 - sized_value(other)) == 1 + to_integer(sized_value(far)) + to_integer(sized_value(middle));
            };
        }
        apply(sized_valid_node(node, p, Color::Red, pv,
            SizedTree::Node(p, node, Color::Red, pv - 1 - sized_value(other), far,
                sized_recolor(sized_reparent(middle, p), Color::Black)), other));
        known();
    }
}
