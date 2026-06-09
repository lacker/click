; Derived list theorems for the standard prelude.

(theorem member_nil
  (forall value (is-value value)
    (computes-to (member value nil) (quote :false)))
  (by
    (intro value)
    (eval)))

(theorem member_cons_true
  (forall value (is-value value)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (value-eq value head) (quote :true))
          (computes-to
            (member value (cons head tail))
            (quote :true))))))
  (by
    (intro value)
    (intro head)
    (intro tail)
    (intro value_eq_true)
    (simp only value_eq_true)))

(theorem member_cons_false
  (forall value (is-value value)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (value-eq value head) (quote :false))
          (computes-to
            (member value (cons head tail))
            (member value tail))))))
  (by
    (intro value)
    (intro head)
    (intro tail)
    (intro value_eq_false)
    (simp only value_eq_false)))

(theorem map_identity
  (forall list (is-list list)
    (computes-to
      (map (lambda value value) list)
      list))
  (by
    (list-induction list
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (simp only map_cons induction_hypothesis)))))

(theorem concat_map_singleton
  (forall list (is-list list)
    (computes-to
      (concat-map (lambda value (cons value nil)) list)
      list))
  (by
    (list-induction list
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (simp only concat_map_cons induction_hypothesis append_singleton)))))

(theorem fold_right_cons_nil
  (forall list (is-list list)
    (computes-to
      (fold-right
        (lambda value
          (lambda accumulator
            (cons value accumulator)))
        nil
        list)
      list))
  (by
    (list-induction list
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (simp only fold_right_cons induction_hypothesis)))))

(theorem fold_left_reverse_acc
  (forall list (is-list list)
    (forall acc (is-list acc)
      (computes-to
        (fold-left
          (lambda accumulator
            (lambda value
              (cons value accumulator)))
          acc
          list)
        (reverse_acc list acc))))
  (by
    (list-induction list
      (by
        (intro acc)
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (intro acc)
        (specialize tail_reverse_acc induction_hypothesis (cons head acc))
        (have fold_step
          (computes-to
            (fold-left
              (lambda accumulator
                (lambda value
                  (cons value accumulator)))
              acc
              (cons head tail))
            (fold-left
              (lambda accumulator
                (lambda value
                  (cons value accumulator)))
              (cons head acc)
              tail))
          (by
            (specialize
              fold_left_cons_step
              fold_left_cons
              (lambda accumulator
                (lambda value
                  (cons value accumulator)))
              acc
              head
              tail)
            (rewrite
              (symm
                (eval-to
                  ((lambda accumulator
                     (lambda value
                       (cons value accumulator)))
                   acc
                   head)
                  (cons head acc))))
            (exact fold_left_cons_step))
          (by
            (calc
              (fold-left
                (lambda accumulator
                  (lambda value
                    (cons value accumulator)))
                acc
                (cons head tail))
              (==
                (fold-left
                  (lambda accumulator
                    (lambda value
                      (cons value accumulator)))
                  (cons head acc)
                  tail)
                (by
                  (exact fold_step)))
              (==
                (reverse_acc tail (cons head acc))
                (by
                  (exact tail_reverse_acc)))
              (==
                (reverse_acc (cons head tail) acc)
                (by
                  (eval))))))))))

(theorem fold_left_reverse
  (forall list (is-list list)
    (computes-to
      (fold-left
        (lambda accumulator
          (lambda value
            (cons value accumulator)))
        nil
        list)
      (reverse list)))
  (by
    (intro list)
    (calc
      (fold-left
        (lambda accumulator
          (lambda value
            (cons value accumulator)))
        nil
        list)
      (==
        (reverse_acc list nil)
        (by
          (exact fold_left_reverse_acc list nil)))
      (==
        (reverse list)
        (by
          (eval))))))

(theorem append_assoc
  (forall left (is-list left)
    (forall middle (is-list middle)
      (forall right (is-list right)
        (computes-to
          (append (append left middle) right)
          (append left (append middle right))))))
  (by
    (list-induction left
      (by
        (intro middle)
        (intro right)
        (obtain middle_right middle_right_proof
          (append_computes_to_list middle right))
        (calc
          (append (append nil middle) right)
          (==
            (append middle right)
            (by
              (eval)))
          (==
            middle_right
            (by
              (exact middle_right_proof)))
          (==
            (append nil middle_right)
            (by
              (exact (symm (append_nil_returns_right middle_right)))))
          (==
            (append nil (append middle right))
            (by
              (simpa only (symm middle_right_proof))))))
      head
      tail
      induction_hypothesis
      (by
        (intro middle)
        (intro right)
        (obtain tail_middle tail_middle_proof
          (append_computes_to_list tail middle))
        (obtain middle_right middle_right_proof
          (append_computes_to_list middle right))
        (calc
          (append (append (cons head tail) middle) right)
          (==
            (append (cons head (append tail middle)) right)
            (by
              (simpa only (append_cons head tail middle))))
          (==
            (append (cons head tail_middle) right)
            (by
              (simpa only tail_middle_proof)))
          (==
            (cons head (append tail_middle right))
            (by
              (exact append_cons head tail_middle right)))
          (==
            (cons head (append (append tail middle) right))
            (by
              (simpa only (symm tail_middle_proof))))
          (==
            (cons head (append tail (append middle right)))
            (by
              (simpa only (induction_hypothesis middle right))))
          (==
            (cons head (append tail middle_right))
            (by
              (simpa only middle_right_proof)))
          (==
            (append (cons head tail) middle_right)
            (by
              (exact (symm (append_cons head tail middle_right)))))
          (==
            (append (cons head tail) (append middle right))
            (by
              (simpa only (symm middle_right_proof)))))))))

(theorem append_take_drop
  (forall count (is-list count)
    (forall list (is-list list)
      (computes-to
        (append (take count list) (drop count list))
        list)))
  (by
    (list-induction count
      (by
        (intro list)
        (calc
          (append (take nil list) (drop nil list))
          (==
            (append nil (drop nil list))
            (by
              (simpa only (take_zero list))))
          (==
            (append nil list)
            (by
              (simpa only (drop_zero list))))
          (==
            list
            (by
              (exact append_nil_returns_right list)))))
      count_head
      count_tail
      induction_hypothesis
      (by
        (list-induction list
          (by
            (eval))
          head
          tail
          list_induction_hypothesis
          (by
            (obtain taken_tail taken_tail_proof
              (take_computes_to_list count_tail tail))
            (obtain dropped_tail dropped_tail_proof
              (drop_computes_to_list count_tail tail))
            (calc
              (append
                (take (cons count_head count_tail) (cons head tail))
                (drop (cons count_head count_tail) (cons head tail)))
              (==
                (append
                  (cons head (take count_tail tail))
                  (drop count_tail tail))
                (by
                  (simpa only
                    (take_cons count_head count_tail head tail)
                    (drop_cons count_head count_tail head tail))))
              (==
                (append
                  (cons head taken_tail)
                  (drop count_tail tail))
                (by
                  (simpa only taken_tail_proof)))
              (==
                (append (cons head taken_tail) dropped_tail)
                (by
                  (simpa only dropped_tail_proof)))
              (==
                (cons head (append taken_tail dropped_tail))
                (by
                  (exact
                    append_cons
                    head
                    taken_tail
                    dropped_tail)))
              (==
                (cons
                  head
                  (append (take count_tail tail) dropped_tail))
                (by
                  (simpa only (symm taken_tail_proof))))
              (==
                (cons
                  head
                  (append (take count_tail tail) (drop count_tail tail)))
                (by
                  (simpa only (symm dropped_tail_proof))))
              (==
                (cons head tail)
                (by
                  (simpa only (induction_hypothesis tail)))))))))))

(theorem reverse_acc_append
  (forall list (is-list list)
    (forall acc (is-list acc)
      (computes-to
        (reverse_acc list acc)
        (append (reverse list) acc))))
  (by
    (list-induction list
      (by
        (intro acc)
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (intro acc)
        (obtain tail_reversed tail_reversed_proof
          (reverse_computes_to_list tail))
        (have reverse_cons_step
          (computes-to
            (reverse (cons head tail))
            (append tail_reversed (cons head nil)))
          (by
            (calc
              (reverse (cons head tail))
              (==
                (reverse_acc tail (cons head nil))
                (by
                  (eval)))
              (==
                (append (reverse tail) (cons head nil))
                (by
                  (exact induction_hypothesis (cons head nil))))
              (==
                (append tail_reversed (cons head nil))
                (by
                  (simpa only tail_reversed_proof)))))
          (by
            (calc
              (reverse_acc (cons head tail) acc)
              (==
                (reverse_acc tail (cons head acc))
                (by
                  (eval)))
              (==
                (append (reverse tail) (cons head acc))
                (by
                  (exact induction_hypothesis (cons head acc))))
              (==
                (append tail_reversed (cons head acc))
                (by
                  (simpa only tail_reversed_proof)))
              (==
                (append
                  tail_reversed
                  (append (cons head nil) acc))
                (by
                  (rewrite (symm (append_singleton head acc)))
                  (eval)))
              (==
                (append (append tail_reversed (cons head nil)) acc)
                (by
                  (exact
                    (symm
                      (append_assoc tail_reversed (cons head nil) acc)))))
              (==
                (append (reverse (cons head tail)) acc)
                (by
                  (simpa only (symm reverse_cons_step)))))))))))

(theorem reverse_cons
  (forall head (is-value head)
    (forall tail (is-list tail)
      (computes-to
        (reverse (cons head tail))
        (append (reverse tail) (cons head nil)))))
  (by
    (intro head)
    (intro tail)
    (calc
      (reverse (cons head tail))
      (==
        (reverse_acc tail (cons head nil))
        (by
          (eval)))
      (==
        (append (reverse tail) (cons head nil))
        (by
          (exact reverse_acc_append tail (cons head nil)))))))

(theorem reverse_acc_reverse
  (forall list (is-list list)
    (forall acc (is-list acc)
      (computes-to
        (reverse (reverse_acc list acc))
        (append (reverse acc) list))))
  (by
    (list-induction list
      (by
        (intro acc)
        (obtain acc_reversed acc_reversed_proof
          (reverse_computes_to_list acc))
        (calc
          (reverse (reverse_acc nil acc))
          (==
            (reverse acc)
            (by
              (eval)))
          (==
            acc_reversed
            (by
              (exact acc_reversed_proof)))
          (==
            (append acc_reversed nil)
            (by
              (exact (symm (append_right_nil acc_reversed)))))
          (==
            (append (reverse acc) nil)
            (by
              (simpa only (symm acc_reversed_proof))))))
      head
      tail
      induction_hypothesis
      (by
        (intro acc)
        (obtain acc_reversed acc_reversed_proof
          (reverse_computes_to_list acc))
        (calc
          (reverse (reverse_acc (cons head tail) acc))
          (==
            (reverse (reverse_acc tail (cons head acc)))
            (by
              (eval)))
          (==
            (append (reverse (cons head acc)) tail)
            (by
              (exact induction_hypothesis (cons head acc))))
          (==
            (append (append acc_reversed (cons head nil)) tail)
            (by
              (rewrite (reverse_cons head acc))
              (rewrite acc_reversed_proof)
              (eval)))
          (==
            (append acc_reversed (append (cons head nil) tail))
            (by
              (exact append_assoc acc_reversed (cons head nil) tail)))
          (==
            (append acc_reversed (cons head tail))
            (by
              (simpa only (append_singleton head tail))))
          (==
            (append (reverse acc) (cons head tail))
            (by
              (simpa only (symm acc_reversed_proof)))))))))

(theorem reverse_double
  (forall list (is-list list)
    (computes-to
      (reverse (reverse list))
      list))
  (by
    (intro list)
    (calc
      (reverse (reverse list))
      (==
        (reverse (reverse_acc list nil))
        (by
          (rewrite
            (eval-to
              (reverse list)
              (reverse_acc list nil)))
          (eval)))
      (==
        (append (reverse nil) list)
        (by
          (exact reverse_acc_reverse list nil)))
      (==
        (append nil list)
        (by
          (simpa only reverse_nil)))
      (==
        list
        (by
          (exact append_nil_returns_right list))))))

(theorem reverse_acc_of_append
  (forall left (is-list left)
    (forall right (is-list right)
      (forall acc (is-list acc)
        (computes-to
          (reverse_acc (append left right) acc)
          (reverse_acc right (reverse_acc left acc))))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro acc)
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (intro acc)
        (obtain tail_right tail_right_proof
          (append_computes_to_list tail right))
        (calc
          (reverse_acc (append (cons head tail) right) acc)
          (==
            (reverse_acc (cons head (append tail right)) acc)
            (by
              (simpa only (append_cons head tail right))))
          (==
            (reverse_acc (cons head tail_right) acc)
            (by
              (simpa only tail_right_proof)))
          (==
            (reverse_acc tail_right (cons head acc))
            (by
              (eval)))
          (==
            (reverse_acc (append tail right) (cons head acc))
            (by
              (simpa only (symm tail_right_proof))))
          (==
            (reverse_acc right (reverse_acc tail (cons head acc)))
            (by
              (exact induction_hypothesis right (cons head acc))))
          (==
            (reverse_acc right (reverse_acc (cons head tail) acc))
            (by
              (rewrite
                (symm
                  (eval-same
                    (reverse_acc (cons head tail) acc)
                    (reverse_acc tail (cons head acc)))))
              (eval))))))))

(theorem reverse_append
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (reverse (append left right))
        (append (reverse right) (reverse left)))))
  (by
    (intro left)
    (intro right)
    (obtain appended appended_proof
      (append_computes_to_list left right))
    (obtain left_reversed_acc left_reversed_acc_proof
      (reverse_acc_computes_to_list left nil))
    (have reverse_left_step
      (computes-to
        (reverse left)
        left_reversed_acc)
      (by
        (calc
          (reverse left)
          (==
            (reverse_acc left nil)
            (by
              (eval)))
          (==
            left_reversed_acc
            (by
              (exact left_reversed_acc_proof)))))
      (by
        (calc
          (reverse (append left right))
          (==
            (reverse appended)
            (by
              (simpa only appended_proof)))
          (==
            (reverse_acc appended nil)
            (by
              (eval)))
          (==
            (reverse_acc (append left right) nil)
            (by
              (simpa only (symm appended_proof))))
          (==
            (reverse_acc right (reverse_acc left nil))
            (by
              (exact reverse_acc_of_append left right nil)))
          (==
            (reverse_acc right left_reversed_acc)
            (by
              (simpa only left_reversed_acc_proof)))
          (==
            (append (reverse right) left_reversed_acc)
            (by
              (exact reverse_acc_append right left_reversed_acc)))
          (==
            (append (reverse right) (reverse left))
            (by
              (simpa only (symm reverse_left_step)))))))))

(theorem snoc_computes_to_list
  (forall list (is-list list)
    (forall value (is-value value)
      (computes-to-list result (snoc list value))))
  (by
    (list-induction list
      (by
        (intro value)
        (exists (cons value nil)
          (by
            (eval))))
      head
      tail
      induction_hypothesis
      (by
        (intro value)
        (obtain tail_result tail_result_proof
          (induction_hypothesis value))
        (exists (cons head tail_result)
          (by
            (calc
              (snoc (cons head tail) value)
              (==
                (cons head (snoc tail value))
                (by
                  (eval)))
              (==
                (cons head tail_result)
                (by
                  (simpa only tail_result_proof))))))))))

(theorem snoc_nil
  (forall value (is-value value)
    (computes-to
      (snoc nil value)
      (cons value nil)))
  (by
    (intro value)
    (eval)))

(theorem snoc_cons
  (forall head (is-value head)
    (forall tail (is-list tail)
      (forall value (is-value value)
        (computes-to
          (snoc (cons head tail) value)
          (cons head (snoc tail value))))))
  (by
    (intro head)
    (intro tail)
    (intro value)
    (eval)))

(theorem concat_nil
  (computes-to (concat nil) nil)
  (by
    (eval)))

(theorem last_nil_errors
  (errors-with (last nil) 0)
  (by
    (eval)))

(theorem last_singleton
  (forall head (is-value head)
    (computes-to
      (last (cons head nil))
      head))
  (by
    (intro head)
    (eval)))

(theorem last_cons
  (forall head (is-value head)
    (forall next (is-value next)
      (forall tail (is-list tail)
        (computes-to
          (last (cons head (cons next tail)))
          (last (cons next tail))))))
  (by
    (intro head)
    (intro next)
    (intro tail)
    (eval)))

(theorem init_nil_errors
  (errors-with (init nil) 0)
  (by
    (eval)))

(theorem init_singleton
  (forall head (is-value head)
    (computes-to
      (init (cons head nil))
      nil))
  (by
    (intro head)
    (eval)))

(theorem init_cons
  (forall head (is-value head)
    (forall next (is-value next)
      (forall tail (is-list tail)
        (computes-to
          (init (cons head (cons next tail)))
          (cons head (init (cons next tail)))))))
  (by
    (intro head)
    (intro next)
    (intro tail)
    (eval)))

(theorem null_nil
  (computes-to
    (null nil)
    (quote :true))
  (by
    (eval)))

(theorem null_cons
  (forall head (is-value head)
    (forall tail (is-list tail)
      (computes-to
        (null (cons head tail))
        (quote :false))))
  (by
    (intro head)
    (intro tail)
    (eval)))

(theorem is_singleton_nil
  (computes-to
    (is-singleton nil)
    (quote :false))
  (by
    (eval)))

(theorem is_singleton_singleton
  (forall head (is-value head)
    (computes-to
      (is-singleton (cons head nil))
      (quote :true)))
  (by
    (intro head)
    (eval)))

(theorem is_singleton_cons
  (forall head (is-value head)
    (forall next (is-value next)
      (forall tail (is-list tail)
        (computes-to
          (is-singleton (cons head (cons next tail)))
          (quote :false)))))
  (by
    (intro head)
    (intro next)
    (intro tail)
    (eval)))
