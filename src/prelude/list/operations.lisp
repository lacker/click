; List operation theorems for the standard prelude.

(theorem reverse_acc_computes_to_list
  (forall list (is-list list)
    (forall acc (is-list acc)
      (computes-to-list result (reverse_acc list acc))))
  (by
    (list-induction list
      (by
        (intro acc)
        (exists acc
          (by
            (eval))))
      head
      tail
      induction_hypothesis
      (by
        (intro acc)
        (specialize reversed_tail induction_hypothesis (cons head acc))
        (rewrite
          (eval-same
            (reverse_acc (cons head tail) acc)
            (reverse_acc tail (cons head acc))))
        (exact reversed_tail)))))

(theorem reverse_computes_to_list
  (forall list (is-list list)
    (computes-to-list result (reverse list)))
  (by
    (intro list)
    (specialize reversed_acc reverse_acc_computes_to_list list nil)
    (rewrite
      (eval-to
        (reverse list)
        (reverse_acc list nil)))
    (exact reversed_acc)))

(theorem reverse_nil_computes_to_list
  (computes-to-list result (reverse nil))
  (by
    (apply reverse_computes_to_list nil)))

(theorem reverse_nil
  (computes-to (reverse nil) nil)
  (by
    (eval)))

(theorem reverse_singleton
  (forall head (is-value head)
    (computes-to
      (reverse (cons head nil))
      (cons head nil)))
  (by
    (intro head)
    (eval)))

(theorem append_nil_computes_to_list
  (forall right (is-list right)
    (computes-to-list result (append nil right)))
  (by
    (intro right)
    (exists right
      (by
        (eval)))))

(theorem append_computes_to_list
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to-list result (append left right))))
  (by
    (list-induction left
      (by
        (intro right)
        (exists right
          (by
            (eval))))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (specialize tail_result_exists induction_hypothesis right)
        (obtain tail_result tail_result_proof tail_result_exists)
        (exists (cons head tail_result)
          (by
            (calc
              (append (cons head tail) right)
              (==
                (cons head (append tail right))
                (by
                  (eval)))
              (==
                (cons head tail_result)
                (by
                  (simpa only tail_result_proof))))))))))

(theorem append_nil_returns_right
  (forall right (is-list right)
    (computes-to (append nil right) right))
  (by
    (intro right)
    (eval)))

(theorem append_right_nil
  (forall left (is-list left)
    (computes-to (append left nil) left))
  (by
    (list-induction left
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (calc
          (append (cons head tail) nil)
          (==
            (cons head (append tail nil))
            (by
              (eval)))
          (==
            (cons head tail)
            (by
              (simpa only induction_hypothesis))))))))

(theorem append_cons
  (forall head (is-value head)
    (forall tail (is-list tail)
      (forall right (is-list right)
        (computes-to
          (append (cons head tail) right)
          (cons head (append tail right))))))
  (by
    (intro head)
    (intro tail)
    (intro right)
    (eval)))

(theorem append_singleton
  (forall head (is-value head)
    (forall right (is-list right)
      (computes-to
        (append (cons head nil) right)
        (cons head right))))
  (by
    (intro head)
    (intro right)
    (eval)))

(theorem length_nil
  (computes-to (length nil) nil)
  (by
    (eval)))

(theorem length_cons
  (forall head (is-value head)
    (forall tail (is-list tail)
      (computes-to
        (length (cons head tail))
        (cons (quote unit) (length tail)))))
  (by
    (intro head)
    (intro tail)
    (eval)))

(theorem length_singleton
  (forall head (is-value head)
    (computes-to
      (length (cons head nil))
      (cons (quote unit) nil)))
  (by
    (intro head)
    (eval)))

(theorem length_computes_to_list
  (forall list (is-list list)
    (computes-to-list result (length list)))
  (by
    (list-induction list
      (by
        (exists nil
          (by
            (eval))))
      head
      tail
      induction_hypothesis
      (by
        (obtain tail_length tail_length_proof induction_hypothesis)
        (exists (cons (quote unit) tail_length)
          (by
            (calc
              (length (cons head tail))
              (==
                (cons (quote unit) (length tail))
                (by
                  (exact length_cons head tail)))
              (==
                (cons (quote unit) tail_length)
                (by
                  (simpa only tail_length_proof))))))))))

(theorem length_append
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (length (append left right))
        (append (length left) (length right)))))
  (by
    (list-induction left
      (by
        (intro right)
        (obtain right_length right_length_proof
          (length_computes_to_list right))
        (calc
          (length (append nil right))
          (==
            (length right)
            (by
              (eval)))
          (==
            right_length
            (by
              (exact right_length_proof)))
          (==
            (append nil right_length)
            (by
              (exact (symm (append_nil_returns_right right_length)))))
          (==
            (append (length nil) right_length)
            (by
              (rewrite (symm length_nil))
              (eval)))
          (==
            (append (length nil) (length right))
            (by
              (simpa only (symm right_length_proof))))))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (obtain tail_right tail_right_proof
          (append_computes_to_list tail right))
        (obtain tail_length tail_length_proof
          (length_computes_to_list tail))
        (obtain right_length right_length_proof
          (length_computes_to_list right))
        (obtain tail_sum tail_sum_proof
          (append_computes_to_list tail_length right_length))
        (calc
          (length (append (cons head tail) right))
          (==
            (length (cons head (append tail right)))
            (by
              (simpa only (append_cons head tail right))))
          (==
            (length (cons head tail_right))
            (by
              (simpa only tail_right_proof)))
          (==
            (cons (quote unit) (length tail_right))
            (by
              (exact length_cons head tail_right)))
          (==
            (cons (quote unit) (length (append tail right)))
            (by
              (simpa only (symm tail_right_proof))))
          (==
            (cons
              (quote unit)
              (append (length tail) (length right)))
            (by
              (simpa only (induction_hypothesis right))))
          (==
            (cons
              (quote unit)
              (append tail_length right_length))
            (by
              (simpa only tail_length_proof right_length_proof)))
          (==
            (cons (quote unit) tail_sum)
            (by
              (simpa only tail_sum_proof)))
          (==
            (cons
              (quote unit)
              (append tail_length right_length))
            (by
              (simpa only (symm tail_sum_proof))))
          (==
            (append
              (cons (quote unit) tail_length)
              right_length)
            (by
              (exact (symm (append_cons (quote unit) tail_length right_length)))))
          (==
            (append
              (cons (quote unit) (length tail))
              right_length)
            (by
              (simpa only (symm tail_length_proof))))
          (==
            (append
              (cons (quote unit) (length tail))
              (length right))
            (by
              (simpa only (symm right_length_proof))))
          (==
            (append
              (length (cons head tail))
              (length right))
            (by
              (simpa only (symm (length_cons head tail))))))))))

(theorem take_zero
  (forall list (is-list list)
    (computes-to (take nil list) nil))
  (by
    (intro list)
    (eval)))

(theorem take_nil
  (forall count (is-list count)
    (computes-to (take count nil) nil))
  (by
    (list-induction count
      (by
        (eval))
      count_head
      count_tail
      induction_hypothesis
      (by
        (eval)))))

(theorem take_cons
  (forall count_head (is-value count_head)
    (forall count_tail (is-list count_tail)
      (forall head (is-value head)
        (forall tail (is-list tail)
          (computes-to
            (take (cons count_head count_tail) (cons head tail))
            (cons head (take count_tail tail)))))))
  (by
    (intro count_head)
    (intro count_tail)
    (intro head)
    (intro tail)
    (eval)))

(theorem take_computes_to_list
  (forall count (is-list count)
    (forall list (is-list list)
      (computes-to-list result (take count list))))
  (by
    (list-induction count
      (by
        (intro list)
        (exists nil
          (by
            (eval))))
      count_head
      count_tail
      count_induction_hypothesis
      (by
        (list-induction list
          (by
            (exists nil
              (by
                (eval))))
          head
          tail
          list_induction_hypothesis
          (by
            (obtain taken_tail taken_tail_proof
              (count_induction_hypothesis tail))
            (exists (cons head taken_tail)
              (by
                (calc
                  (take (cons count_head count_tail) (cons head tail))
                  (==
                    (cons head (take count_tail tail))
                    (by
                      (exact take_cons count_head count_tail head tail)))
                  (==
                    (cons head taken_tail)
                    (by
                      (simpa only taken_tail_proof))))))))))))

(theorem drop_zero
  (forall list (is-list list)
    (computes-to (drop nil list) list))
  (by
    (intro list)
    (eval)))

(theorem drop_nil
  (forall count (is-list count)
    (computes-to (drop count nil) nil))
  (by
    (list-induction count
      (by
        (eval))
      count_head
      count_tail
      induction_hypothesis
      (by
        (eval)))))

(theorem drop_cons
  (forall count_head (is-value count_head)
    (forall count_tail (is-list count_tail)
      (forall head (is-value head)
        (forall tail (is-list tail)
          (computes-to
            (drop (cons count_head count_tail) (cons head tail))
            (drop count_tail tail))))))
  (by
    (intro count_head)
    (intro count_tail)
    (intro head)
    (intro tail)
    (eval)))

(theorem drop_computes_to_list
  (forall count (is-list count)
    (forall list (is-list list)
      (computes-to-list result (drop count list))))
  (by
    (list-induction count
      (by
        (intro list)
        (exists list
          (by
            (eval))))
      count_head
      count_tail
      count_induction_hypothesis
      (by
        (list-induction list
          (by
            (exists nil
              (by
                (eval))))
          head
          tail
          list_induction_hypothesis
          (by
            (obtain dropped_tail dropped_tail_proof
              (count_induction_hypothesis tail))
            (exists dropped_tail
              (by
                (calc
                  (drop (cons count_head count_tail) (cons head tail))
                  (==
                    (drop count_tail tail)
                    (by
                      (exact drop_cons count_head count_tail head tail)))
                  (==
                    dropped_tail
                    (by
                      (exact dropped_tail_proof))))))))))))

(theorem pair_first
  (forall first (is-value first)
    (forall second (is-value second)
      (computes-to
        (head (cons first (cons second nil)))
        first)))
  (by
    (intro first)
    (intro second)
    (eval)))

(theorem pair_tail
  (forall first (is-value first)
    (forall second (is-value second)
      (computes-to
        (tail (cons first (cons second nil)))
        (cons second nil))))
  (by
    (intro first)
    (intro second)
    (eval)))

(theorem pair_second
  (forall first (is-value first)
    (forall second (is-value second)
      (computes-to
        (head (tail (cons first (cons second nil))))
        second)))
  (by
    (intro first)
    (intro second)
    (eval)))

(theorem list_pair_first_from_computation
  (forall computation
    (forall first (is-list first)
      (forall second (is-list second)
        (implies
          (computes-to computation (cons first (cons second nil)))
          (computes-to (head computation) first)))))
  (by
    (intro computation)
    (intro first)
    (intro second)
    (intro computation_is_pair)
    (calc
      (head computation)
      (==
        (head (cons first (cons second nil)))
        (by
          (simpa only computation_is_pair)))
      (==
        first
        (by
          (eval))))))

(theorem list_pair_second_from_computation
  (forall computation
    (forall first (is-list first)
      (forall second (is-list second)
        (implies
          (computes-to computation (cons first (cons second nil)))
          (computes-to (head (tail computation)) second)))))
  (by
    (intro computation)
    (intro first)
    (intro second)
    (intro computation_is_pair)
    (calc
      (head (tail computation))
      (==
        (head (tail (cons first (cons second nil))))
        (by
          (simpa only computation_is_pair)))
      (==
        second
        (by
          (eval))))))

(theorem split_at_def
  (forall count (is-list count)
    (forall list (is-list list)
      (computes-to
        (split-at count list)
        (cons
          (take count list)
          (cons (drop count list) nil)))))
  (by
    (intro count)
    (intro list)
    (eval)))

(theorem split_at_zero
  (forall list (is-list list)
    (computes-to
      (split-at nil list)
      (cons nil (cons list nil))))
  (by
    (intro list)
    (eval)))

(theorem split_at_nil
  (forall count (is-list count)
    (computes-to
      (split-at count nil)
      (cons nil (cons nil nil))))
  (by
    (intro count)
    (calc
      (split-at count nil)
      (==
        (cons
          (take count nil)
          (cons (drop count nil) nil))
        (by
          (exact split_at_def count nil)))
      (==
        (cons nil (cons nil nil))
        (by
          (simpa only (take_nil count) (drop_nil count)))))))

(theorem split_at_cons
  (forall count_head (is-value count_head)
    (forall count_tail (is-list count_tail)
      (forall head (is-value head)
        (forall tail (is-list tail)
          (computes-to
            (split-at
              (cons count_head count_tail)
              (cons head tail))
            (cons
              (cons head (take count_tail tail))
              (cons (drop count_tail tail) nil)))))))
  (by
    (intro count_head)
    (intro count_tail)
    (intro head)
    (intro tail)
    (calc
      (split-at
        (cons count_head count_tail)
        (cons head tail))
      (==
        (cons
          (take
            (cons count_head count_tail)
            (cons head tail))
          (cons
            (drop
              (cons count_head count_tail)
              (cons head tail))
            nil))
        (by
          (exact
            split_at_def
            (cons count_head count_tail)
            (cons head tail))))
      (==
        (cons
          (cons head (take count_tail tail))
          (cons (drop count_tail tail) nil))
        (by
          (simpa only
            (take_cons count_head count_tail head tail)
            (drop_cons count_head count_tail head tail)))))))

(theorem nth_zero_nil
  (computes-to (nth nil nil) none)
  (by
    (eval)))

(theorem nth_zero_cons
  (forall head (is-value head)
    (forall tail (is-list tail)
      (computes-to
        (nth nil (cons head tail))
        (some head))))
  (by
    (intro head)
    (intro tail)
    (eval)))

(theorem nth_cons_nil
  (forall index_head (is-value index_head)
    (forall index_tail (is-list index_tail)
      (computes-to
        (nth (cons index_head index_tail) nil)
        none)))
  (by
    (intro index_head)
    (intro index_tail)
    (eval)))

(theorem nth_cons_cons
  (forall index_head (is-value index_head)
    (forall index_tail (is-list index_tail)
      (forall head (is-value head)
        (forall tail (is-list tail)
          (computes-to
            (nth
              (cons index_head index_tail)
              (cons head tail))
            (nth index_tail tail))))))
  (by
    (intro index_head)
    (intro index_tail)
    (intro head)
    (intro tail)
    (eval)))

(theorem replicate_zero
  (forall value (is-value value)
    (computes-to (replicate nil value) nil))
  (by
    (intro value)
    (eval)))

(theorem replicate_cons
  (forall count_head (is-value count_head)
    (forall count_tail (is-list count_tail)
      (forall value (is-value value)
        (computes-to
          (replicate (cons count_head count_tail) value)
          (cons value (replicate count_tail value))))))
  (by
    (intro count_head)
    (intro count_tail)
    (intro value)
    (eval)))

(theorem replicate_computes_to_list
  (forall count (is-list count)
    (forall value (is-value value)
      (computes-to-list result (replicate count value))))
  (by
    (list-induction count
      (by
        (intro value)
        (exists nil
          (by
            (eval))))
      count_head
      count_tail
      induction_hypothesis
      (by
        (intro value)
        (obtain replicated_tail replicated_tail_proof
          (induction_hypothesis value))
        (exists (cons value replicated_tail)
          (by
            (calc
              (replicate (cons count_head count_tail) value)
              (==
                (cons value (replicate count_tail value))
                (by
                  (exact replicate_cons count_head count_tail value)))
              (==
                (cons value replicated_tail)
                (by
                  (simpa only replicated_tail_proof))))))))))

(theorem length_replicate
  (forall count (is-list count)
    (forall value (is-value value)
      (computes-to
        (length (replicate count value))
        (length count))))
  (by
    (list-induction count
      (by
        (intro value)
        (eval))
      count_head
      count_tail
      induction_hypothesis
      (by
        (intro value)
        (obtain replicated_tail replicated_tail_proof
          (replicate_computes_to_list count_tail value))
        (calc
          (length (replicate (cons count_head count_tail) value))
          (==
            (length (cons value (replicate count_tail value)))
            (by
              (simpa only (replicate_cons count_head count_tail value))))
          (==
            (length (cons value replicated_tail))
            (by
              (simpa only replicated_tail_proof)))
          (==
            (cons (quote unit) (length replicated_tail))
            (by
              (exact length_cons value replicated_tail)))
          (==
            (cons (quote unit) (length (replicate count_tail value)))
            (by
              (simpa only (symm replicated_tail_proof))))
          (==
            (cons (quote unit) (length count_tail))
            (by
              (simpa only (induction_hypothesis value))))
          (==
            (length (cons count_head count_tail))
            (by
              (exact (symm (length_cons count_head count_tail))))))))))

(theorem intersperse_nil
  (forall separator (is-value separator)
    (computes-to (intersperse separator nil) nil))
  (by
    (intro separator)
    (eval)))

(theorem intersperse_singleton
  (forall separator (is-value separator)
    (forall head (is-value head)
      (computes-to
        (intersperse separator (cons head nil))
        (cons head nil))))
  (by
    (intro separator)
    (intro head)
    (eval)))

(theorem intersperse_cons_cons
  (forall separator (is-value separator)
    (forall head (is-value head)
      (forall next (is-value next)
        (forall tail (is-list tail)
          (computes-to
            (intersperse separator (cons head (cons next tail)))
            (cons
              head
              (cons
                separator
                (intersperse separator (cons next tail)))))))))
  (by
    (intro separator)
    (intro head)
    (intro next)
    (intro tail)
    (eval)))

(theorem intersperse_cons_computes_to_list
  (forall separator (is-value separator)
    (forall tail (is-list tail)
      (forall head (is-value head)
        (computes-to-list result (intersperse separator (cons head tail))))))
  (by
    (intro separator)
    (list-induction tail
      (by
        (intro head)
        (exists (cons head nil)
          (by
            (exact intersperse_singleton separator head))))
      next
      rest
      induction_hypothesis
      (by
        (intro head)
        (obtain interspersed_tail interspersed_tail_proof
          (induction_hypothesis next))
        (exists (cons head (cons separator interspersed_tail))
          (by
            (calc
              (intersperse separator (cons head (cons next rest)))
              (==
                (cons
                  head
                  (cons
                    separator
                    (intersperse separator (cons next rest))))
                (by
                  (exact intersperse_cons_cons separator head next rest)))
              (==
                (cons head (cons separator interspersed_tail))
                (by
                  (simpa only interspersed_tail_proof))))))))))

(theorem intersperse_computes_to_list
  (forall separator (is-value separator)
    (forall list (is-list list)
      (computes-to-list result (intersperse separator list))))
  (by
    (intro separator)
    (list-induction list
      (by
        (exists nil
          (by
            (eval))))
      head
      tail
      induction_hypothesis
      (by
        (exact intersperse_cons_computes_to_list separator tail head)))))

(theorem intercalate_nil
  (forall separator (is-list separator)
    (computes-to (intercalate separator nil) nil))
  (by
    (intro separator)
    (eval)))

(theorem intercalate_singleton
  (forall separator (is-list separator)
    (forall list (is-list list)
      (computes-to
        (intercalate separator (cons list nil))
        list)))
  (by
    (intro separator)
    (intro list)
    (eval)))

(theorem intercalate_cons_cons
  (forall separator (is-list separator)
    (forall head (is-list head)
      (forall next (is-list next)
        (forall tail (is-list tail)
          (computes-to
            (intercalate separator (cons head (cons next tail)))
            (append
              head
              (append
                separator
                (intercalate separator (cons next tail)))))))))
  (by
    (intro separator)
    (intro head)
    (intro next)
    (intro tail)
    (eval)))

(theorem is_list_value_true_implies_is_list
  (forall value (is-value value)
    (implies
      (computes-to (is-list-value value) (quote :true))
      (is-list value)))
  (proof
    (forall-intro value
      (implies-intro value_is_value
        (is-value value)
        (implies-intro value_is_list_value
          (computes-to (is-list-value value) (quote :true))
          (value-non-symbol-non-lambda-is-list
            (assume value_is_value)
            (trans
              (eval-same
                (is-symbol value)
                (symbol-eq (value-kind value) (quote :symbol)))
              (rewrite
                (symm
                  (implies-elim
                    (forall-elim
                      (forall-elim
                        (known symbol_eq_true)
                        (value-kind value))
                      (quote :list))
                    (trans
                      (eval-same
                        (symbol-eq (value-kind value) (quote :list))
                        (is-list-value value))
                      (assume value_is_list_value))))
                (eval-to
                  (symbol-eq (quote :list) (quote :symbol))
                  (quote :false))
                kind
                (computes-to
                  (symbol-eq kind (quote :symbol))
                  (quote :false))))
            (trans
              (eval-same
                (is-lambda value)
                (symbol-eq (value-kind value) (quote :lambda)))
              (rewrite
                (symm
                  (implies-elim
                    (forall-elim
                      (forall-elim
                        (known symbol_eq_true)
                        (value-kind value))
                      (quote :list))
                    (trans
                      (eval-same
                        (symbol-eq (value-kind value) (quote :list))
                        (is-list-value value))
                      (assume value_is_list_value))))
                (eval-to
                  (symbol-eq (quote :list) (quote :lambda))
                  (quote :false))
                kind
                (computes-to
                  (symbol-eq kind (quote :lambda))
                  (quote :false))))))))))

(theorem all_lists_cons_true
  (forall head (is-value head)
    (forall tail (is-list tail)
      (implies
        (computes-to
          (all-lists (cons head tail))
          (quote :true))
        (and
          (is-list head)
          (computes-to
            (all-lists tail)
            (quote :true))))))
  (by
    (intro head)
    (intro tail)
    (intro lists_are_lists)
    (have unfolded_all_lists
      (computes-to
        (if
          (is-list-value head)
          (all-lists (tail (cons head tail)))
          (quote :false))
        (quote :true))
      (by
        (calc
          (if
            (is-list-value head)
            (all-lists (tail (cons head tail)))
            (quote :false))
          (==
            (all-lists (cons head tail))
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact lists_are_lists)))))
      (by
        (specialize all_parts if_true_result_with_false_else
          (is-list-value head)
          (all-lists (tail (cons head tail))))
        (cases all_parts head_is_list_value tail_is_all_lists_through_cons)
        (split
          (by
            (apply is_list_value_true_implies_is_list head))
          (by
            (calc
              (all-lists tail)
              (==
                (all-lists (tail (cons head tail)))
                (by
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact tail_is_all_lists_through_cons))))))))))

(theorem none_is_none
  (computes-to (is-none none) (quote :true))
  (by
    (eval)))

(theorem some_is_none
  (forall value (is-value value)
    (computes-to (is-none (some value)) (quote :false)))
  (by
    (intro value)
    (eval)))

(theorem none_is_some
  (computes-to (is-some none) (quote :false))
  (by
    (eval)))

(theorem some_is_some
  (forall value (is-value value)
    (computes-to (is-some (some value)) (quote :true)))
  (by
    (intro value)
    (eval)))

(theorem some_tag
  (forall value (is-value value)
    (computes-to
      (head (some value))
      (quote :some)))
  (by
    (intro value)
    (eval)))

(theorem some_tail
  (forall value (is-value value)
    (computes-to
      (tail (some value))
      (cons value nil)))
  (by
    (intro value)
    (eval)))

(theorem some_value
  (forall value (is-value value)
    (computes-to
      (head (tail (some value)))
      value))
  (by
    (intro value)
    (eval)))

(theorem some_tag_from_computation
  (forall computation
    (forall value (is-value value)
      (implies
        (computes-to computation (some value))
        (computes-to
          (head computation)
          (quote :some)))))
  (by
    (intro computation)
    (intro value)
    (intro computation_is_some)
    (calc
      (head computation)
      (==
        (head (some value))
        (by
          (simpa only computation_is_some)))
      (==
        (quote :some)
        (by
          (exact some_tag value))))))

(theorem some_value_from_computation
  (forall computation
    (forall value (is-value value)
      (implies
        (computes-to computation (some value))
        (computes-to
          (head (tail computation))
          value))))
  (by
    (intro computation)
    (intro value)
    (intro computation_is_some)
    (calc
      (head (tail computation))
      (==
        (head (tail (some value)))
        (by
          (simpa only computation_is_some)))
      (==
        value
        (by
          (exact some_value value))))))

(theorem some_none_absurd
  (forall value (is-value value)
    (implies
      (computes-to (some value) none)
      (absurd)))
  (by
    (intro value)
    (intro some_is_none_value)
    (have impossible_eq
      (computes-to
        (cons (quote :some) (cons value nil))
        (quote :none))
      (by
        (calc
          (cons (quote :some) (cons value nil))
          (==
            (some value)
            (by
              (exact
                (symm
                  (eval-to
                    (some value)
                    (cons (quote :some) (cons value nil)))))))
          (==
            none
            (by
              (exact some_is_none_value)))
          (==
            (quote :none)
            (by
              (eval)))))
      (by
        (exact
          (distinct-outcomes impossible_eq))))))

(theorem none_some_absurd
  (forall value (is-value value)
    (implies
      (computes-to none (some value))
      (absurd)))
  (by
    (intro value)
    (intro none_is_some_value)
    (have some_is_none_value
      (computes-to (some value) none)
      (by
        (exact (symm none_is_some_value)))
      (by
        (apply some_none_absurd value)))))

(theorem intercalate_cons_computes_to_list
  (forall separator (is-list separator)
    (forall tail (is-list tail)
      (forall head (is-value head)
        (implies
          (computes-to
            (all-lists (cons head tail))
            (quote :true))
          (computes-to-list result (intercalate separator (cons head tail)))))))
  (by
    (intro separator)
    (list-induction tail
      (by
        (intro head)
        (intro lists_are_lists)
        (specialize all_parts all_lists_cons_true head nil)
        (cases all_parts head_is_list tail_is_all_lists)
        (exists head
          (by
            (exact intercalate_singleton separator head))))
      next
      rest
      induction_hypothesis
      (by
        (intro head)
        (intro lists_are_lists)
        (specialize all_parts all_lists_cons_true
          head
          (cons next rest))
        (cases all_parts head_is_list tail_is_all_lists)
        (specialize tail_parts all_lists_cons_true next rest)
        (cases tail_parts next_is_list rest_is_all_lists)
        (specialize intercalated_tail_exists induction_hypothesis next)
        (obtain intercalated_tail intercalated_tail_proof
          intercalated_tail_exists)
        (obtain separator_tail separator_tail_proof
          (append_computes_to_list separator intercalated_tail))
        (obtain result result_proof
          (append_computes_to_list head separator_tail))
        (exists result
          (by
            (calc
              (intercalate separator (cons head (cons next rest)))
              (==
                (append
                  head
                  (append
                    separator
                    (intercalate separator (cons next rest))))
                (by
                  (exact intercalate_cons_cons separator head next rest)))
              (==
                (append head (append separator intercalated_tail))
                (by
                  (simpa only intercalated_tail_proof)))
              (==
                (append head separator_tail)
                (by
                  (simpa only separator_tail_proof)))
              (==
                result
                (by
                  (exact result_proof))))))))))

(theorem intercalate_computes_to_list
  (forall separator (is-list separator)
    (forall lists (is-list lists)
      (implies
        (computes-to (all-lists lists) (quote :true))
        (computes-to-list result (intercalate separator lists)))))
  (by
    (intro separator)
    (list-induction lists
      (by
        (intro lists_are_lists)
        (exists nil
          (by
            (eval))))
      head
      tail
      induction_hypothesis
      (by
        (intro lists_are_lists)
        (exact intercalate_cons_computes_to_list separator tail head)))))

(theorem map_nil
  (forall function (is-value function)
    (computes-to (map function nil) nil))
  (by
    (intro function)
    (eval)))

(theorem map_cons
  (forall function (is-value function)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (computes-to
          (map function (cons head tail))
          (cons (function head) (map function tail))))))
  (by
    (intro function)
    (intro head)
    (intro tail)
    (eval)))

(theorem map_computes_to_list
  (forall function (is-value function)
    (implies
      (forall value (is-value value)
        (exists mapped_value (is-value mapped_value)
          (computes-to (function value) mapped_value)))
      (forall list (is-list list)
        (computes-to-list result (map function list)))))
  (by
    (intro function)
    (intro maps_values)
    (list-induction list
      (by
        (exists nil
          (by
            (eval))))
      head
      tail
      induction_hypothesis
      (by
        (obtain mapped_head mapped_head_proof
          (maps_values head))
        (obtain mapped_tail mapped_tail_proof induction_hypothesis)
        (exists (cons mapped_head mapped_tail)
          (by
            (calc
              (map function (cons head tail))
              (==
                (cons (function head) (map function tail))
                (by
                  (exact map_cons function head tail)))
              (==
                (cons mapped_head (map function tail))
                (by
                  (simpa only mapped_head_proof)))
              (==
                (cons mapped_head mapped_tail)
                (by
                  (simpa only mapped_tail_proof))))))))))

(theorem length_map
  (forall function (is-value function)
    (implies
      (forall value (is-value value)
        (exists mapped_value (is-value mapped_value)
          (computes-to (function value) mapped_value)))
      (forall list (is-list list)
        (computes-to
          (length (map function list))
          (length list)))))
  (by
    (intro function)
    (intro maps_values)
    (list-induction list
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (obtain mapped_head mapped_head_proof
          (maps_values head))
        (obtain mapped_tail mapped_tail_proof
          (map_computes_to_list function tail))
        (calc
          (length (map function (cons head tail)))
          (==
            (length (cons (function head) (map function tail)))
            (by
              (simpa only (map_cons function head tail))))
          (==
            (length (cons mapped_head (map function tail)))
            (by
              (simpa only mapped_head_proof)))
          (==
            (length (cons mapped_head mapped_tail))
            (by
              (simpa only mapped_tail_proof)))
          (==
            (cons (quote unit) (length mapped_tail))
            (by
              (exact length_cons mapped_head mapped_tail)))
          (==
            (cons (quote unit) (length (map function tail)))
            (by
              (simpa only (symm mapped_tail_proof))))
          (==
            (cons (quote unit) (length tail))
            (by
              (simpa only induction_hypothesis)))
          (==
            (length (cons head tail))
            (by
              (exact (symm (length_cons head tail))))))))))

(theorem concat_map_nil
  (forall function (is-value function)
    (computes-to (concat-map function nil) nil))
  (by
    (intro function)
    (eval)))

(theorem concat_map_cons
  (forall function (is-value function)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (computes-to
          (concat-map function (cons head tail))
          (append
            (function head)
            (concat-map function tail))))))
  (by
    (intro function)
    (intro head)
    (intro tail)
    (eval)))

(theorem concat_map_computes_to_list
  (forall function (is-value function)
    (implies
      (forall value (is-value value)
        (computes-to-list mapped_list (function value)))
      (forall list (is-list list)
        (computes-to-list result (concat-map function list)))))
  (by
    (intro function)
    (intro maps_values_to_lists)
    (list-induction list
      (by
        (exists nil
          (by
            (eval))))
      head
      tail
      induction_hypothesis
      (by
        (obtain mapped_head mapped_head_proof
          (maps_values_to_lists head))
        (obtain mapped_tail mapped_tail_proof induction_hypothesis)
        (obtain appended appended_proof
          (append_computes_to_list mapped_head mapped_tail))
        (exists appended
          (by
            (calc
              (concat-map function (cons head tail))
              (==
                (append (function head) (concat-map function tail))
                (by
                  (exact concat_map_cons function head tail)))
              (==
                (append mapped_head (concat-map function tail))
                (by
                  (simpa only mapped_head_proof)))
              (==
                (append mapped_head mapped_tail)
                (by
                  (simpa only mapped_tail_proof)))
              (==
                appended
                (by
                  (exact appended_proof))))))))))

(theorem fold_right_nil
  (forall function (is-value function)
    (forall initial (is-value initial)
      (computes-to (fold-right function initial nil) initial)))
  (by
    (intro function)
    (intro initial)
    (eval)))

(theorem fold_right_cons
  (forall function (is-value function)
    (forall initial (is-value initial)
      (forall head (is-value head)
        (forall tail (is-list tail)
          (computes-to
            (fold-right function initial (cons head tail))
            (function
              head
              (fold-right function initial tail)))))))
  (by
    (intro function)
    (intro initial)
    (intro head)
    (intro tail)
    (eval)))

(theorem fold_right_computes_to_value
  (forall function (is-value function)
    (forall initial (is-value initial)
      (implies
        (forall value (is-value value)
          (forall accumulator (is-value accumulator)
            (exists folded_value (is-value folded_value)
              (computes-to
                (function value accumulator)
                folded_value))))
        (forall list (is-list list)
          (exists result (is-value result)
            (computes-to
              (fold-right function initial list)
              result))))))
  (by
    (intro function)
    (intro initial)
    (intro combines_values)
    (list-induction list
      (by
        (exists initial
          (by
            (eval))))
      head
      tail
      induction_hypothesis
      (by
        (obtain tail_result tail_result_proof induction_hypothesis)
        (obtain folded_result folded_result_proof
          (combines_values head tail_result))
        (exists folded_result
          (by
            (calc
              (fold-right function initial (cons head tail))
              (==
                (function
                  head
                  (fold-right function initial tail))
                (by
                  (exact fold_right_cons function initial head tail)))
              (==
                (function head tail_result)
                (by
                  (simpa only tail_result_proof)))
              (==
                folded_result
                (by
                  (exact folded_result_proof))))))))))

(theorem fold_left_nil
  (forall function (is-value function)
    (forall initial (is-value initial)
      (computes-to (fold-left function initial nil) initial)))
  (by
    (intro function)
    (intro initial)
    (eval)))

(theorem fold_left_cons
  (forall function (is-value function)
    (forall initial (is-value initial)
      (forall head (is-value head)
        (forall tail (is-list tail)
          (computes-to
            (fold-left function initial (cons head tail))
            (fold-left
              function
              (function initial head)
              tail))))))
  (by
    (intro function)
    (intro initial)
    (intro head)
    (intro tail)
    (eval)))

(theorem fold_left_computes_to_value
  (forall function (is-value function)
    (implies
      (forall accumulator (is-value accumulator)
        (forall value (is-value value)
          (exists folded_value (is-value folded_value)
            (computes-to
              (function accumulator value)
              folded_value))))
      (forall list (is-list list)
        (forall initial (is-value initial)
          (exists result (is-value result)
            (computes-to
              (fold-left function initial list)
              result))))))
  (by
    (intro function)
    (intro combines_values)
    (list-induction list
      (by
        (intro initial)
        (exists initial
          (by
            (eval))))
      head
      tail
      induction_hypothesis
      (by
        (intro initial)
        (obtain folded_initial folded_initial_proof
          (combines_values initial head))
        (obtain result result_proof
          (induction_hypothesis folded_initial))
        (exists result
          (by
            (calc
              (fold-left function initial (cons head tail))
              (==
                (fold-left
                  function
                  (function initial head)
                  tail)
                (by
                  (exact fold_left_cons function initial head tail)))
              (==
                (fold-left function folded_initial tail)
                (by
                  (simpa only folded_initial_proof)))
              (==
                result
                (by
                  (exact result_proof))))))))))

(theorem zip_left_nil
  (forall right (is-list right)
    (computes-to (zip nil right) nil))
  (by
    (intro right)
    (eval)))

(theorem zip_right_nil
  (forall left (is-list left)
    (computes-to (zip left nil) nil))
  (by
    (list-induction left
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (eval)))))

(theorem zip_cons
  (forall left_head (is-value left_head)
    (forall left_tail (is-list left_tail)
      (forall right_head (is-value right_head)
        (forall right_tail (is-list right_tail)
          (computes-to
            (zip
              (cons left_head left_tail)
              (cons right_head right_tail))
            (cons
              (cons left_head (cons right_head nil))
              (zip left_tail right_tail)))))))
  (by
    (intro left_head)
    (intro left_tail)
    (intro right_head)
    (intro right_tail)
    (eval)))

(theorem zip_computes_to_list
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to-list result (zip left right))))
  (by
    (list-induction left
      (by
        (intro right)
        (exists nil
          (by
            (eval))))
      left_head
      left_tail
      left_induction_hypothesis
      (by
        (list-induction right
          (by
            (exists nil
              (by
                (eval))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (obtain zipped_tail zipped_tail_proof
              (left_induction_hypothesis right_tail))
            (exists
              (cons
                (cons left_head (cons right_head nil))
                zipped_tail)
              (by
                (calc
                  (zip
                    (cons left_head left_tail)
                    (cons right_head right_tail))
                  (==
                    (cons
                      (cons left_head (cons right_head nil))
                      (zip left_tail right_tail))
                    (by
                      (exact
                        zip_cons
                        left_head
                        left_tail
                        right_head
                        right_tail)))
                  (==
                    (cons
                      (cons left_head (cons right_head nil))
                      zipped_tail)
                    (by
                      (simpa only zipped_tail_proof))))))))))))

(theorem unzip_nil
  (computes-to
    (unzip nil)
    (cons nil (cons nil nil)))
  (by
    (eval)))

(theorem unzip_cons
  (forall left (is-value left)
    (forall right (is-value right)
      (forall tail (is-list tail)
        (computes-to
          (unzip
            (cons
              (cons left (cons right nil))
              tail))
          (cons
            (cons
              left
              (head (unzip tail)))
            (cons
              (cons
                right
                (head (tail (unzip tail))))
              nil))))))
  (by
    (intro left)
    (intro right)
    (intro tail)
    (eval)))

(theorem zip_with_left_nil
  (forall function (is-value function)
    (forall right (is-list right)
      (computes-to (zip-with function nil right) nil)))
  (by
    (intro function)
    (intro right)
    (eval)))

(theorem zip_with_right_nil
  (forall function (is-value function)
    (forall left (is-list left)
      (computes-to (zip-with function left nil) nil)))
  (by
    (intro function)
    (list-induction left
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (eval)))))

(theorem zip_with_cons
  (forall function (is-value function)
    (forall left_head (is-value left_head)
      (forall left_tail (is-list left_tail)
        (forall right_head (is-value right_head)
          (forall right_tail (is-list right_tail)
            (computes-to
              (zip-with
                function
                (cons left_head left_tail)
                (cons right_head right_tail))
              (cons
                (function left_head right_head)
                (zip-with function left_tail right_tail))))))))
  (by
    (intro function)
    (intro left_head)
    (intro left_tail)
    (intro right_head)
    (intro right_tail)
    (eval)))

(theorem zip_with_computes_to_list
  (forall function (is-value function)
    (implies
      (forall left_value (is-value left_value)
        (forall right_value (is-value right_value)
          (exists zipped_value (is-value zipped_value)
            (computes-to
              (function left_value right_value)
              zipped_value))))
      (forall left (is-list left)
        (forall right (is-list right)
          (computes-to-list result (zip-with function left right))))))
  (by
    (intro function)
    (intro combines_values)
    (list-induction left
      (by
        (intro right)
        (exists nil
          (by
            (eval))))
      left_head
      left_tail
      left_induction_hypothesis
      (by
        (list-induction right
          (by
            (exists nil
              (by
                (eval))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (obtain zipped_head zipped_head_proof
              (combines_values left_head right_head))
            (obtain zipped_tail zipped_tail_proof
              (left_induction_hypothesis right_tail))
            (exists (cons zipped_head zipped_tail)
              (by
                (calc
                  (zip-with
                    function
                    (cons left_head left_tail)
                    (cons right_head right_tail))
                  (==
                    (cons
                      (function left_head right_head)
                      (zip-with function left_tail right_tail))
                    (by
                      (exact
                        zip_with_cons
                        function
                        left_head
                        left_tail
                        right_head
                        right_tail)))
                  (==
                    (cons
                      zipped_head
                      (zip-with function left_tail right_tail))
                    (by
                      (simpa only zipped_head_proof)))
                  (==
                    (cons zipped_head zipped_tail)
                    (by
                      (simpa only zipped_tail_proof))))))))))))

(theorem filter_nil
  (forall predicate (is-value predicate)
    (computes-to (filter predicate nil) nil))
  (by
    (intro predicate)
    (eval)))

(theorem filter_cons_true
  (forall predicate (is-value predicate)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (predicate head) (quote :true))
          (computes-to
            (filter predicate (cons head tail))
            (cons head (filter predicate tail)))))))
  (by
    (intro predicate)
    (intro head)
    (intro tail)
    (intro predicate_true)
    (simp only predicate_true)))

(theorem filter_cons_false
  (forall predicate (is-value predicate)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (predicate head) (quote :false))
          (computes-to
            (filter predicate (cons head tail))
            (filter predicate tail))))))
  (by
    (intro predicate)
    (intro head)
    (intro tail)
    (intro predicate_false)
    (simp only predicate_false)))

(theorem reject_nil
  (forall predicate (is-value predicate)
    (computes-to (reject predicate nil) nil))
  (by
    (intro predicate)
    (eval)))

(theorem reject_cons_true
  (forall predicate (is-value predicate)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (predicate head) (quote :true))
          (computes-to
            (reject predicate (cons head tail))
            (reject predicate tail))))))
  (by
    (intro predicate)
    (intro head)
    (intro tail)
    (intro predicate_true)
    (simp only predicate_true)))

(theorem reject_cons_false
  (forall predicate (is-value predicate)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (predicate head) (quote :false))
          (computes-to
            (reject predicate (cons head tail))
            (cons head (reject predicate tail)))))))
  (by
    (intro predicate)
    (intro head)
    (intro tail)
    (intro predicate_false)
    (simp only predicate_false)))

(theorem partition_nil
  (forall predicate (is-value predicate)
    (computes-to
      (partition predicate nil)
      (cons nil (cons nil nil))))
  (by
    (intro predicate)
    (eval)))

(theorem partition_cons_true
  (forall predicate (is-value predicate)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (predicate head) (quote :true))
          (computes-to
            (partition predicate (cons head tail))
            (cons
              (cons
                head
                (head (partition predicate tail)))
              (cons
                (head (tail (partition predicate tail)))
                nil)))))))
  (by
    (intro predicate)
    (intro head)
    (intro tail)
    (intro predicate_true)
    (have predicate_head_true
      (computes-to
        (predicate (head (cons head tail)))
        (quote :true))
      (by
        (calc
          (predicate (head (cons head tail)))
          (==
            (predicate head)
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact predicate_true)))))
      (by
        (calc
          (partition predicate (cons head tail))
          (==
            (if
              (predicate (head (cons head tail)))
              (cons
                (cons
                  (head (cons head tail))
                  (head
                    (partition predicate (tail (cons head tail)))))
                (cons
                  (head
                    (tail
                      (partition
                        predicate
                        (tail (cons head tail)))))
                  nil))
              (cons
                (head
                  (partition predicate (tail (cons head tail))))
                (cons
                  (cons
                    (head (cons head tail))
                    (head
                      (tail
                        (partition
                          predicate
                          (tail (cons head tail))))))
                  nil)))
            (by
              (eval)))
          (==
            (cons
              (cons
                (head (cons head tail))
                (head
                  (partition predicate (tail (cons head tail)))))
              (cons
                (head
                  (tail
                    (partition
                      predicate
                      (tail (cons head tail)))))
                nil))
            (by
              (exact
                if_condition_true
                (predicate (head (cons head tail)))
                (cons
                  (cons
                    (head (cons head tail))
                    (head
                      (partition predicate (tail (cons head tail)))))
                  (cons
                    (head
                      (tail
                        (partition
                          predicate
                          (tail (cons head tail)))))
                    nil))
                (cons
                  (head
                    (partition predicate (tail (cons head tail))))
                  (cons
                    (cons
                      (head (cons head tail))
                      (head
                        (tail
                          (partition
                            predicate
                            (tail (cons head tail))))))
                    nil)))))
          (==
            (cons
              (cons
                head
                (head (partition predicate tail)))
              (cons
                (head (tail (partition predicate tail)))
                nil))
            (by
              (eval))))))))
(theorem partition_cons_false
  (forall predicate (is-value predicate)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (predicate head) (quote :false))
          (computes-to
            (partition predicate (cons head tail))
            (cons
              (head (partition predicate tail))
              (cons
                (cons
                  head
                  (head (tail (partition predicate tail))))
                nil)))))))
  (by
    (intro predicate)
    (intro head)
    (intro tail)
    (intro predicate_false)
    (have predicate_head_false
      (computes-to
        (predicate (head (cons head tail)))
        (quote :false))
      (by
        (calc
          (predicate (head (cons head tail)))
          (==
            (predicate head)
            (by
              (eval)))
          (==
            (quote :false)
            (by
              (exact predicate_false)))))
      (by
        (calc
          (partition predicate (cons head tail))
          (==
            (if
              (predicate (head (cons head tail)))
              (cons
                (cons
                  (head (cons head tail))
                  (head
                    (partition predicate (tail (cons head tail)))))
                (cons
                  (head
                    (tail
                      (partition
                        predicate
                        (tail (cons head tail)))))
                  nil))
              (cons
                (head
                  (partition predicate (tail (cons head tail))))
                (cons
                  (cons
                    (head (cons head tail))
                    (head
                      (tail
                        (partition
                          predicate
                          (tail (cons head tail))))))
                  nil)))
            (by
              (eval)))
          (==
            (cons
              (head
                (partition predicate (tail (cons head tail))))
              (cons
                (cons
                  (head (cons head tail))
                  (head
                    (tail
                      (partition
                        predicate
                        (tail (cons head tail))))))
                nil))
            (by
              (exact
                if_condition_false
                (predicate (head (cons head tail)))
                (cons
                  (cons
                    (head (cons head tail))
                    (head
                      (partition predicate (tail (cons head tail)))))
                  (cons
                    (head
                      (tail
                        (partition
                          predicate
                          (tail (cons head tail)))))
                    nil))
                (cons
                  (head
                    (partition predicate (tail (cons head tail))))
                  (cons
                    (cons
                      (head (cons head tail))
                      (head
                        (tail
                          (partition
                            predicate
                            (tail (cons head tail))))))
                    nil)))))
          (==
            (cons
              (head (partition predicate tail))
              (cons
                (cons
                  head
                  (head (tail (partition predicate tail))))
                nil))
            (by
              (eval))))))))
(theorem any_nil
  (forall predicate (is-value predicate)
    (computes-to (any predicate nil) (quote :false)))
  (by
    (intro predicate)
    (eval)))

(theorem any_cons_true
  (forall predicate (is-value predicate)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (predicate head) (quote :true))
          (computes-to
            (any predicate (cons head tail))
            (quote :true))))))
  (by
    (intro predicate)
    (intro head)
    (intro tail)
    (intro predicate_true)
    (simp only predicate_true)))

(theorem any_cons_false
  (forall predicate (is-value predicate)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (predicate head) (quote :false))
          (computes-to
            (any predicate (cons head tail))
            (any predicate tail))))))
  (by
    (intro predicate)
    (intro head)
    (intro tail)
    (intro predicate_false)
    (simp only predicate_false)))

(theorem all_nil
  (forall predicate (is-value predicate)
    (computes-to (all predicate nil) (quote :true)))
  (by
    (intro predicate)
    (eval)))

(theorem all_cons_true
  (forall predicate (is-value predicate)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (predicate head) (quote :true))
          (computes-to
            (all predicate (cons head tail))
            (all predicate tail))))))
  (by
    (intro predicate)
    (intro head)
    (intro tail)
    (intro predicate_true)
    (simp only predicate_true)))

(theorem all_cons_false
  (forall predicate (is-value predicate)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (predicate head) (quote :false))
          (computes-to
            (all predicate (cons head tail))
            (quote :false))))))
  (by
    (intro predicate)
    (intro head)
    (intro tail)
    (intro predicate_false)
    (simp only predicate_false)))

(theorem any_cons_or
  (forall predicate (is-value predicate)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (is-bool (predicate head))
          (implies
            (is-bool (any predicate tail))
            (computes-to
              (any predicate (cons head tail))
              (or (predicate head) (any predicate tail))))))))
  (by
    (intro predicate)
    (intro head)
    (intro tail)
    (intro predicate_bool)
    (intro tail_bool)
    (or-elim predicate_bool
      predicate_true
      (by
        (have branch_true
          (computes-to
            (or (predicate head) (any predicate tail))
            (quote :true))
          (by
            (apply or_true_left (predicate head) (any predicate tail)))
          (by
            (calc
              (any predicate (cons head tail))
              (==
                (quote :true)
                (by
                  (apply any_cons_true predicate head tail)))
              (==
                (or (predicate head) (any predicate tail))
                (by
                  (exact (symm branch_true))))))))
      predicate_false
      (by
        (have branch_false
          (computes-to
            (or (predicate head) (any predicate tail))
            (any predicate tail))
          (by
            (apply or_false_left (predicate head) (any predicate tail)))
          (by
            (calc
              (any predicate (cons head tail))
              (==
                (any predicate tail)
                (by
                  (apply any_cons_false predicate head tail)))
              (==
                (or (predicate head) (any predicate tail))
                (by
                  (exact (symm branch_false)))))))))))

(theorem all_cons_and
  (forall predicate (is-value predicate)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (is-bool (predicate head))
          (implies
            (is-bool (all predicate tail))
            (computes-to
              (all predicate (cons head tail))
              (and (predicate head) (all predicate tail))))))))
  (by
    (intro predicate)
    (intro head)
    (intro tail)
    (intro predicate_bool)
    (intro tail_bool)
    (or-elim predicate_bool
      predicate_true
      (by
        (have branch_true
          (computes-to
            (and (predicate head) (all predicate tail))
            (all predicate tail))
          (by
            (apply and_true_left (predicate head) (all predicate tail)))
          (by
            (calc
              (all predicate (cons head tail))
              (==
                (all predicate tail)
                (by
                  (apply all_cons_true predicate head tail)))
              (==
                (and (predicate head) (all predicate tail))
                (by
                  (exact (symm branch_true))))))))
      predicate_false
      (by
        (have branch_false
          (computes-to
            (and (predicate head) (all predicate tail))
            (quote :false))
          (by
            (apply and_false_left (predicate head) (all predicate tail)))
          (by
            (calc
              (all predicate (cons head tail))
              (==
                (quote :false)
                (by
                  (apply all_cons_false predicate head tail)))
              (==
                (and (predicate head) (all predicate tail))
                (by
                  (exact (symm branch_false)))))))))))

(theorem filter_computes_to_list
  (forall predicate (is-value predicate)
    (implies
      (forall value (is-value value)
        (is-bool (predicate value)))
      (forall list (is-list list)
        (computes-to-list result (filter predicate list)))))
  (by
    (intro predicate)
    (intro predicate_returns_bool)
    (list-induction list
      (by
        (exists nil
          (by
            (eval))))
      head
      tail
      induction_hypothesis
      (by
        (or-elim
          (predicate_returns_bool head)
          predicate_true
          (by
            (obtain filtered_tail filtered_tail_proof induction_hypothesis)
            (exists (cons head filtered_tail)
              (by
                (calc
                  (filter predicate (cons head tail))
                  (==
                    (cons head (filter predicate tail))
                    (by
                      (apply filter_cons_true predicate head tail)))
                  (==
                    (cons head filtered_tail)
                    (by
                      (simpa only filtered_tail_proof)))))))
          predicate_false
          (by
            (obtain filtered_tail filtered_tail_proof induction_hypothesis)
            (exists filtered_tail
              (by
                (calc
                  (filter predicate (cons head tail))
                  (==
                    (filter predicate tail)
                    (by
                      (apply filter_cons_false predicate head tail)))
                  (==
                    filtered_tail
                    (by
                      (exact filtered_tail_proof))))))))))))

(theorem reject_computes_to_list
  (forall predicate (is-value predicate)
    (implies
      (forall value (is-value value)
        (is-bool (predicate value)))
      (forall list (is-list list)
        (computes-to-list result (reject predicate list)))))
  (by
    (intro predicate)
    (intro predicate_returns_bool)
    (list-induction list
      (by
        (exists nil
          (by
            (eval))))
      head
      tail
      induction_hypothesis
      (by
        (or-elim
          (predicate_returns_bool head)
          predicate_true
          (by
            (obtain rejected_tail rejected_tail_proof induction_hypothesis)
            (exists rejected_tail
              (by
                (calc
                  (reject predicate (cons head tail))
                  (==
                    (reject predicate tail)
                    (by
                      (apply reject_cons_true predicate head tail)))
                  (==
                    rejected_tail
                    (by
                      (exact rejected_tail_proof)))))))
          predicate_false
          (by
            (obtain rejected_tail rejected_tail_proof induction_hypothesis)
            (exists (cons head rejected_tail)
              (by
                (calc
                  (reject predicate (cons head tail))
                  (==
                    (cons head (reject predicate tail))
                    (by
                      (apply reject_cons_false predicate head tail)))
                  (==
                    (cons head rejected_tail)
                    (by
                      (simpa only rejected_tail_proof))))))))))))

(theorem any_computes_to_bool
  (forall predicate (is-value predicate)
    (implies
      (forall value (is-value value)
        (is-bool (predicate value)))
      (forall list (is-list list)
        (is-bool (any predicate list)))))
  (by
    (intro predicate)
    (intro predicate_returns_bool)
    (list-induction list
      (by
        (right
          (by
            (eval))))
      head
      tail
      induction_hypothesis
      (by
        (specialize predicate_bool predicate_returns_bool head)
        (have cons_as_or
          (computes-to
            (any predicate (cons head tail))
            (or (predicate head) (any predicate tail)))
          (by
            (apply any_cons_or predicate head tail))
          (by
            (have branch_bool
              (is-bool (or (predicate head) (any predicate tail)))
              (by
                (apply
                  or_computes_to_bool
                  (predicate head)
                  (any predicate tail)))
              (by
                (or-elim branch_bool
                  branch_true
                  (by
                    (left
                      (by
                        (calc
                          (any predicate (cons head tail))
                          (==
                            (or (predicate head) (any predicate tail))
                            (by
                              (exact cons_as_or)))
                          (==
                            (quote :true)
                            (by
                              (exact branch_true)))))))
                  branch_false
                  (by
                    (right
                      (by
                        (calc
                          (any predicate (cons head tail))
                          (==
                            (or (predicate head) (any predicate tail))
                            (by
                              (exact cons_as_or)))
                          (==
                            (quote :false)
                            (by
                              (exact branch_false))))))))))))))))

(theorem any_cons_false_parts
  (forall predicate (is-value predicate)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to
            (any predicate (cons head tail))
            (quote :false))
          (and
            (computes-to (predicate head) (quote :false))
            (computes-to (any predicate tail) (quote :false)))))))
  (by
    (intro predicate)
    (intro head)
    (intro tail)
    (intro any_false)
    (have any_branch_false
      (computes-to
        (if
          (predicate (head (cons head tail)))
          (quote :true)
          (any predicate (tail (cons head tail))))
        (quote :false))
      (by
        (calc
          (if
            (predicate (head (cons head tail)))
            (quote :true)
            (any predicate (tail (cons head tail))))
          (==
            (any predicate (cons head tail))
            (by
              (eval)))
          (==
            (quote :false)
            (by
              (exact any_false)))))
      (by
        (specialize branch_parts
          if_false_result_with_true_then
          (predicate (head (cons head tail)))
          (any predicate (tail (cons head tail))))
        (cases branch_parts
          predicate_false_through_cons
          tail_any_false_through_cons)
        (split
          (by
            (calc
              (predicate head)
              (==
                (predicate (head (cons head tail)))
                (by
                  (eval)))
              (==
                (quote :false)
                (by
                  (exact predicate_false_through_cons)))))
          (by
            (calc
              (any predicate tail)
              (==
                (any predicate (tail (cons head tail)))
                (by
                  (eval)))
              (==
                (quote :false)
                (by
                  (exact tail_any_false_through_cons))))))))))

(theorem any_cons_true_cases
  (forall predicate (is-value predicate)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to
            (any predicate (cons head tail))
            (quote :true))
          (or
            (computes-to (predicate head) (quote :true))
            (and
              (computes-to (predicate head) (quote :false))
              (computes-to (any predicate tail) (quote :true))))))))
  (by
    (intro predicate)
    (intro head)
    (intro tail)
    (intro any_true)
    (have any_branch_true
      (computes-to
        (if
          (predicate (head (cons head tail)))
          (quote :true)
          (any predicate (tail (cons head tail))))
        (quote :true))
      (by
        (calc
          (if
            (predicate (head (cons head tail)))
            (quote :true)
            (any predicate (tail (cons head tail))))
          (==
            (any predicate (cons head tail))
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact any_true)))))
      (by
        (have predicate_bool
          (is-bool (predicate (head (cons head tail))))
          (proof
            (if-value-condition-bool
              (assume any_branch_true)))
          (by
            (or-elim predicate_bool
              predicate_true_through_cons
              (by
                (left
                  (by
                    (calc
                      (predicate head)
                      (==
                        (predicate (head (cons head tail)))
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact predicate_true_through_cons)))))))
              predicate_false_through_cons
              (by
                (right
                  (by
                    (split
                      (by
                        (calc
                          (predicate head)
                          (==
                            (predicate (head (cons head tail)))
                            (by
                              (eval)))
                          (==
                            (quote :false)
                            (by
                              (exact predicate_false_through_cons)))))
                      (by
                        (calc
                          (any predicate tail)
                          (==
                            (any predicate (tail (cons head tail)))
                            (by
                              (eval)))
                          (==
                            (if
                              (predicate (head (cons head tail)))
                              (quote :true)
                              (any predicate (tail (cons head tail))))
                            (by
                              (simpa only predicate_false_through_cons)))
                          (==
                            (quote :true)
                            (by
                              (exact any_branch_true))))))))))))))))

(theorem all_computes_to_bool
  (forall predicate (is-value predicate)
    (implies
      (forall value (is-value value)
        (is-bool (predicate value)))
      (forall list (is-list list)
        (is-bool (all predicate list)))))
  (by
    (intro predicate)
    (intro predicate_returns_bool)
    (list-induction list
      (by
        (left
          (by
            (eval))))
      head
      tail
      induction_hypothesis
      (by
        (specialize predicate_bool predicate_returns_bool head)
        (have cons_as_and
          (computes-to
            (all predicate (cons head tail))
            (and (predicate head) (all predicate tail)))
          (by
            (apply all_cons_and predicate head tail))
          (by
            (have branch_bool
              (is-bool (and (predicate head) (all predicate tail)))
              (by
                (apply
                  and_computes_to_bool
                  (predicate head)
                  (all predicate tail)))
              (by
                (or-elim branch_bool
                  branch_true
                  (by
                    (left
                      (by
                        (calc
                          (all predicate (cons head tail))
                          (==
                            (and (predicate head) (all predicate tail))
                            (by
                              (exact cons_as_and)))
                          (==
                            (quote :true)
                            (by
                              (exact branch_true)))))))
                  branch_false
                  (by
                    (right
                      (by
                        (calc
                          (all predicate (cons head tail))
                          (==
                            (and (predicate head) (all predicate tail))
                            (by
                              (exact cons_as_and)))
                          (==
                            (quote :false)
                            (by
                              (exact branch_false))))))))))))))))

(theorem find_nil
  (forall predicate (is-value predicate)
    (computes-to (find predicate nil) none))
  (by
    (intro predicate)
    (eval)))

(theorem find_cons_true
  (forall predicate (is-value predicate)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (predicate head) (quote :true))
          (computes-to
            (find predicate (cons head tail))
            (some head))))))
  (by
    (intro predicate)
    (intro head)
    (intro tail)
    (intro predicate_true)
    (simp only predicate_true)))

(theorem find_cons_false
  (forall predicate (is-value predicate)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (predicate head) (quote :false))
          (computes-to
            (find predicate (cons head tail))
            (find predicate tail))))))
  (by
    (intro predicate)
    (intro head)
    (intro tail)
    (intro predicate_false)
    (simp only predicate_false)))

(theorem find_cons_branch
  (forall predicate (is-value predicate)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (computes-to
          (find predicate (cons head tail))
          (if
            (predicate (head (cons head tail)))
            (some (head (cons head tail)))
            (find predicate (tail (cons head tail))))))))
  (by
    (intro predicate)
    (intro head)
    (intro tail)
    (eval)))

(theorem find_cons_none_parts
  (forall predicate (is-value predicate)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (find predicate (cons head tail)) none)
          (and
            (computes-to (predicate head) (quote :false))
            (computes-to (find predicate tail) none))))))
  (by
    (intro predicate)
    (intro head)
    (intro tail)
    (intro find_missing)
    (have find_branch_result
      (computes-to
        (if
          (predicate (head (cons head tail)))
          (some (head (cons head tail)))
          (find predicate (tail (cons head tail))))
        (quote :none))
      (by
        (calc
          (if
            (predicate (head (cons head tail)))
            (some (head (cons head tail)))
            (find predicate (tail (cons head tail))))
          (==
            (find predicate (cons head tail))
            (by
              (exact (symm (find_cons_branch predicate head tail)))))
          (==
            none
            (by
              (exact find_missing)))
          (==
            (quote :none)
            (by
              (eval)))))
      (by
        (have predicate_bool
          (is-bool (predicate (head (cons head tail))))
          (proof
            (if-value-condition-bool
              (assume find_branch_result)))
          (by
            (or-elim predicate_bool
              predicate_true_through_cons
              (by
                (have predicate_true
                  (computes-to (predicate head) (quote :true))
                  (by
                    (calc
                      (predicate head)
                      (==
                        (predicate (head (cons head tail)))
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact predicate_true_through_cons)))))
                  (by
                    (have cons_found
                      (computes-to
                        (find predicate (cons head tail))
                        (some head))
                      (by
                        (apply
                          find_cons_true
                          predicate
                          head
                          tail))
                      (by
                        (have impossible_eq
                          (computes-to (some head) none)
                          (by
                            (calc
                              (some head)
                              (==
                                (find predicate (cons head tail))
                                (by
                                  (exact (symm cons_found))))
                              (==
                                none
                                (by
                                  (exact find_missing)))))
                          (by
                            (have contradiction
                              (absurd)
                              (by
                                (apply some_none_absurd head))
                              (by
                                (exact
                                  (absurd-elim
                                    contradiction
                                    (and
                                      (computes-to
                                        (predicate head)
                                        (quote :false))
                                      (computes-to
                                        (find predicate tail)
                                        none)))))))))))))
              predicate_false_through_cons
              (by
                (split
                  (by
                    (calc
                      (predicate head)
                      (==
                        (predicate (head (cons head tail)))
                        (by
                          (eval)))
                      (==
                        (quote :false)
                        (by
                          (exact predicate_false_through_cons)))))
                  (by
                    (calc
                      (find predicate tail)
                      (==
                        (find predicate (cons head tail))
                        (by
                          (simpa only predicate_false_through_cons)))
                      (==
                        none
                        (by
                          (exact find_missing))))))))))))))

(theorem find_cons_some_cases
  (forall predicate (is-value predicate)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (forall found (is-value found)
          (implies
            (computes-to
              (find predicate (cons head tail))
              (some found))
            (or
              (computes-to (predicate head) (quote :true))
              (and
                (computes-to (predicate head) (quote :false))
                (computes-to
                  (find predicate tail)
                  (some found)))))))))
  (by
    (intro predicate)
    (intro head)
    (intro tail)
    (intro found)
    (intro find_found)
    (have find_branch_result
      (computes-to
        (if
          (predicate (head (cons head tail)))
          (some (head (cons head tail)))
          (find predicate (tail (cons head tail))))
        (cons (quote :some) (cons found nil)))
      (by
        (calc
          (if
            (predicate (head (cons head tail)))
            (some (head (cons head tail)))
            (find predicate (tail (cons head tail))))
          (==
            (find predicate (cons head tail))
            (by
              (exact (symm (find_cons_branch predicate head tail)))))
          (==
            (some found)
            (by
              (exact find_found)))
          (==
            (cons (quote :some) (cons found nil))
            (by
              (eval)))))
      (by
        (have predicate_bool
          (is-bool (predicate (head (cons head tail))))
          (proof
            (if-value-condition-bool
              (assume find_branch_result)))
          (by
            (or-elim predicate_bool
              predicate_true_through_cons
              (by
                (left
                  (by
                    (calc
                      (predicate head)
                      (==
                        (predicate (head (cons head tail)))
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact predicate_true_through_cons)))))))
              predicate_false_through_cons
              (by
                (right
                  (by
                    (split
                      (by
                        (calc
                          (predicate head)
                          (==
                            (predicate (head (cons head tail)))
                            (by
                              (eval)))
                          (==
                            (quote :false)
                            (by
                              (exact predicate_false_through_cons)))))
                      (by
                        (calc
                          (find predicate tail)
                          (==
                            (find predicate (cons head tail))
                            (by
                              (simpa only predicate_false_through_cons)))
                          (==
                            (some found)
                            (by
                              (exact find_found))))))))))))))))

(theorem elem_index_nil
  (forall value (is-value value)
    (computes-to (elem-index value nil) none))
  (by
    (intro value)
    (eval)))

(theorem elem_index_cons_true
  (forall value (is-value value)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (value-eq value head) (quote :true))
          (computes-to
            (elem-index value (cons head tail))
            (some nil))))))
  (by
    (intro value)
    (intro head)
    (intro tail)
    (intro values_equal)
    (simp only values_equal)))

(theorem elem_index_cons_false_none
  (forall value (is-value value)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (value-eq value head) (quote :false))
          (implies
            (computes-to (elem-index value tail) none)
            (computes-to
              (elem-index value (cons head tail))
              none))))))
  (by
    (intro value)
    (intro head)
    (intro tail)
    (intro values_not_equal)
    (intro tail_missing)
    (simp only values_not_equal tail_missing none_is_some)))

(theorem elem_index_cons_false_some
  (forall value (is-value value)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (forall index (is-list index)
          (implies
            (computes-to (value-eq value head) (quote :false))
            (implies
              (computes-to (elem-index value tail) (some index))
              (computes-to
                (elem-index value (cons head tail))
                (some (cons (quote unit) index)))))))))
  (by
    (intro value)
    (intro head)
    (intro tail)
    (intro index)
    (intro values_not_equal)
    (intro tail_found)
    (simp only values_not_equal tail_found (some_is_some index))))

(theorem elem_index_cons_branch
  (forall value (is-value value)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (computes-to
          (elem-index value (cons head tail))
          (if
            (value-eq value (head (cons head tail)))
            (some nil)
            ((lambda tail_result
               (if
                 (is-some tail_result)
                 (some (cons (quote unit) (head (tail tail_result))))
                 none))
             (elem-index value (tail (cons head tail)))))))))
  (by
    (intro value)
    (intro head)
    (intro tail)
    (eval)))

(theorem elem_index_cons_false_branch
  (forall value (is-value value)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (value-eq value head) (quote :false))
          (computes-to
            (elem-index value (cons head tail))
            ((lambda tail_result
               (if
                 (is-some tail_result)
                 (some (cons (quote unit) (head (tail tail_result))))
                 none))
             (elem-index value (tail (cons head tail)))))))))
  (by
    (intro value)
    (intro head)
    (intro tail)
    (intro values_not_equal)
    (simp only values_not_equal)))
