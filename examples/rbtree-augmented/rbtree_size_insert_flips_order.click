// Repeated color flips preserve every node and its in-order position.
verifying "rb_insert_augmented.c";
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_insert_flips_model.click";

theorem sized_flip_result_preserves_inorder(chain: SizedFlipChain, sub: SizedTree) {
    ensures rb_inorder(sized_shape(sized_flip_result(chain, sub)))
        == rb_inorder(sized_shape(sized_plug(sized_flip_context(chain), sub))) by {
        induct(chain) as ih {
            SizedFlipChain::Root => {
                apply(sized_recolor_observations(sub, Color::Black));
                apply(rb_recolor_preserves_inorder(sized_shape(sub), Color::Black));
                unfold(sized_flip_result(SizedFlipChain::Root, sub));
                unfold(sized_flip_context(SizedFlipChain::Root));
                unfold(sized_plug(SizedContext::Top, sub));
                assumption();
            },
            SizedFlipChain::Stop(ctx) => {
                unfold(sized_flip_result(SizedFlipChain::Stop(ctx), sub));
                unfold(sized_flip_context(SizedFlipChain::Stop(ctx))); normalize();
            },
            SizedFlipChain::LL(p, g, pv, gv, other, uncle, up) => {
                apply(ih(up, SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, sub, other), sized_recolor(uncle, Color::Black))));
                apply(sized_insert_fix_recolor_observations(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, sub, other), uncle)));
                apply(rb_insert_fix_recolor_preserves_inorder(sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, sub, other), uncle))));
                unfold(sized_insert_fix_recolor(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, sub, other), uncle)));
                unfold(sized_recolor(SizedTree::Node(p, g, Color::Red, pv, sub, other), Color::Black));
                have rb_inorder(sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, sub, other), sized_recolor(uncle, Color::Black)))) == rb_inorder(sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, sub, other), uncle))) by assumption();
                apply(plug_inorder_transport(sized_context_shape(sized_flip_context(up)), sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, sub, other), sized_recolor(uncle, Color::Black))), sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, sub, other), uncle))));
                apply(sized_plug_preserves_shape(sized_flip_context(up), SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, sub, other), sized_recolor(uncle, Color::Black))));
                apply(sized_plug_preserves_shape(sized_flip_context(up), SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, sub, other), uncle)));
                unfold(sized_flip_result(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up), sub));
                unfold(sized_flip_context(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)));
                unfold(sized_plug(SizedContext::Left(p, g, Color::Red, pv, other, SizedContext::Left(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))), sub));
                unfold(sized_plug(SizedContext::Left(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up)), SizedTree::Node(p, g, Color::Red, pv, sub, other)));
                assumption();
            },
            SizedFlipChain::LR(p, g, pv, gv, other, uncle, up) => {
                apply(ih(up, SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, other, sub), sized_recolor(uncle, Color::Black))));
                apply(sized_insert_fix_recolor_observations(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, other, sub), uncle)));
                apply(rb_insert_fix_recolor_preserves_inorder(sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, other, sub), uncle))));
                unfold(sized_insert_fix_recolor(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, other, sub), uncle)));
                unfold(sized_recolor(SizedTree::Node(p, g, Color::Red, pv, other, sub), Color::Black));
                have rb_inorder(sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, other, sub), sized_recolor(uncle, Color::Black)))) == rb_inorder(sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, other, sub), uncle))) by assumption();
                apply(plug_inorder_transport(sized_context_shape(sized_flip_context(up)), sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, other, sub), sized_recolor(uncle, Color::Black))), sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, other, sub), uncle))));
                apply(sized_plug_preserves_shape(sized_flip_context(up), SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, other, sub), sized_recolor(uncle, Color::Black))));
                apply(sized_plug_preserves_shape(sized_flip_context(up), SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, other, sub), uncle)));
                unfold(sized_flip_result(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up), sub));
                unfold(sized_flip_context(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)));
                unfold(sized_plug(SizedContext::Right(p, g, Color::Red, pv, other, SizedContext::Left(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))), sub));
                unfold(sized_plug(SizedContext::Left(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up)), SizedTree::Node(p, g, Color::Red, pv, other, sub)));
                assumption();
            },
            SizedFlipChain::RL(p, g, pv, gv, other, uncle, up) => {
                apply(ih(up, SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, sized_recolor(uncle, Color::Black), SizedTree::Node(p, g, Color::Black, pv, sub, other))));
                apply(sized_insert_fix_recolor_observations(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, uncle, SizedTree::Node(p, g, Color::Red, pv, sub, other))));
                apply(rb_insert_fix_recolor_preserves_inorder(sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, uncle, SizedTree::Node(p, g, Color::Red, pv, sub, other)))));
                unfold(sized_insert_fix_recolor(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, uncle, SizedTree::Node(p, g, Color::Red, pv, sub, other))));
                unfold(sized_recolor(SizedTree::Node(p, g, Color::Red, pv, sub, other), Color::Black));
                have rb_inorder(sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, sized_recolor(uncle, Color::Black), SizedTree::Node(p, g, Color::Black, pv, sub, other)))) == rb_inorder(sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, uncle, SizedTree::Node(p, g, Color::Red, pv, sub, other)))) by assumption();
                apply(plug_inorder_transport(sized_context_shape(sized_flip_context(up)), sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, sized_recolor(uncle, Color::Black), SizedTree::Node(p, g, Color::Black, pv, sub, other))), sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, uncle, SizedTree::Node(p, g, Color::Red, pv, sub, other)))));
                apply(sized_plug_preserves_shape(sized_flip_context(up), SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, sized_recolor(uncle, Color::Black), SizedTree::Node(p, g, Color::Black, pv, sub, other))));
                apply(sized_plug_preserves_shape(sized_flip_context(up), SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, uncle, SizedTree::Node(p, g, Color::Red, pv, sub, other))));
                unfold(sized_flip_result(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up), sub));
                unfold(sized_flip_context(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)));
                unfold(sized_plug(SizedContext::Left(p, g, Color::Red, pv, other, SizedContext::Right(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))), sub));
                unfold(sized_plug(SizedContext::Right(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up)), SizedTree::Node(p, g, Color::Red, pv, sub, other)));
                assumption();
            },
            SizedFlipChain::RR(p, g, pv, gv, other, uncle, up) => {
                apply(ih(up, SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, sized_recolor(uncle, Color::Black), SizedTree::Node(p, g, Color::Black, pv, other, sub))));
                apply(sized_insert_fix_recolor_observations(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, uncle, SizedTree::Node(p, g, Color::Red, pv, other, sub))));
                apply(rb_insert_fix_recolor_preserves_inorder(sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, uncle, SizedTree::Node(p, g, Color::Red, pv, other, sub)))));
                unfold(sized_insert_fix_recolor(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, uncle, SizedTree::Node(p, g, Color::Red, pv, other, sub))));
                unfold(sized_recolor(SizedTree::Node(p, g, Color::Red, pv, other, sub), Color::Black));
                have rb_inorder(sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, sized_recolor(uncle, Color::Black), SizedTree::Node(p, g, Color::Black, pv, other, sub)))) == rb_inorder(sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, uncle, SizedTree::Node(p, g, Color::Red, pv, other, sub)))) by assumption();
                apply(plug_inorder_transport(sized_context_shape(sized_flip_context(up)), sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, sized_recolor(uncle, Color::Black), SizedTree::Node(p, g, Color::Black, pv, other, sub))), sized_shape(SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, uncle, SizedTree::Node(p, g, Color::Red, pv, other, sub)))));
                apply(sized_plug_preserves_shape(sized_flip_context(up), SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, sized_recolor(uncle, Color::Black), SizedTree::Node(p, g, Color::Black, pv, other, sub))));
                apply(sized_plug_preserves_shape(sized_flip_context(up), SizedTree::Node(g, sized_flip_parent(up), Color::Black, gv, uncle, SizedTree::Node(p, g, Color::Red, pv, other, sub))));
                unfold(sized_flip_result(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up), sub));
                unfold(sized_flip_context(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)));
                unfold(sized_plug(SizedContext::Right(p, g, Color::Red, pv, other, SizedContext::Right(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))), sub));
                unfold(sized_plug(SizedContext::Right(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up)), SizedTree::Node(p, g, Color::Red, pv, other, sub)));
                assumption();
            },
        }
    }
}
