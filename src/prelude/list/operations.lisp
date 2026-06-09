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
        (or-elim
          (predicate_returns_bool head)
          predicate_true
          (by
            (left
              (by
                (apply any_cons_true predicate head tail))))
          predicate_false
          (by
            (or-elim
              induction_hypothesis
              tail_true
              (by
                (left
                  (by
                    (calc
                      (any predicate (cons head tail))
                      (==
                        (any predicate tail)
                        (by
                          (apply any_cons_false predicate head tail)))
                      (==
                        (quote :true)
                        (by
                          (exact tail_true)))))))
              tail_false
              (by
                (right
                  (by
                    (calc
                      (any predicate (cons head tail))
                      (==
                        (any predicate tail)
                        (by
                          (apply any_cons_false predicate head tail)))
                      (==
                        (quote :false)
                        (by
                          (exact tail_false))))))))))))))

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
        (or-elim
          (predicate_returns_bool head)
          predicate_true
          (by
            (or-elim
              induction_hypothesis
              tail_true
              (by
                (left
                  (by
                    (calc
                      (all predicate (cons head tail))
                      (==
                        (all predicate tail)
                        (by
                          (apply all_cons_true predicate head tail)))
                      (==
                        (quote :true)
                        (by
                          (exact tail_true)))))))
              tail_false
              (by
                (right
                  (by
                    (calc
                      (all predicate (cons head tail))
                      (==
                        (all predicate tail)
                        (by
                          (apply all_cons_true predicate head tail)))
                      (==
                        (quote :false)
                        (by
                          (exact tail_false)))))))))
          predicate_false
          (by
            (right
              (by
                (apply all_cons_false predicate head tail)))))))))
