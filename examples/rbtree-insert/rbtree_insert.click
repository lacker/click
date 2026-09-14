import "../rbtree-model/rbtree_model.click";

verifying "rb_insert_color.c";

# The complete insert contract and its deliberately unfinished proof live in
# rbtree_insert.frontier. The examples gate loads this entry to check the
# shared model import and unchanged C source without claiming that frontier
# has been discharged.
