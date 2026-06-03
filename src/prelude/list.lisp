; List definitions for the standard prelude.

(def reverse_acc
  ((lambda fixed_point_function
     ((lambda fixed_point_self
        (fixed_point_function
          (lambda fixed_point_value
            ((fixed_point_self fixed_point_self) fixed_point_value))))
      (lambda fixed_point_self
        (fixed_point_function
          (lambda fixed_point_value
            ((fixed_point_self fixed_point_self) fixed_point_value))))))
   (lambda self
     (lambda list
       (lambda acc
         (list-case list
           acc
           cell
           ((self (tail cell))
            (cons (head cell) acc))))))))

(def reverse
  (lambda list
    ((reverse_acc list) nil)))

(def append
  ((lambda fixed_point_function
     ((lambda fixed_point_self
        (fixed_point_function
          (lambda fixed_point_value
            ((fixed_point_self fixed_point_self) fixed_point_value))))
      (lambda fixed_point_self
        (fixed_point_function
          (lambda fixed_point_value
            ((fixed_point_self fixed_point_self) fixed_point_value))))))
   (lambda self
     (lambda left
       (lambda right
         (list-case left
           right
           cell
           (cons
             (head cell)
             ((self (tail cell)) right))))))))

(def snoc
  ((lambda fixed_point_function
     ((lambda fixed_point_self
        (fixed_point_function
          (lambda fixed_point_value
            ((fixed_point_self fixed_point_self) fixed_point_value))))
      (lambda fixed_point_self
        (fixed_point_function
          (lambda fixed_point_value
            ((fixed_point_self fixed_point_self) fixed_point_value))))))
   (lambda self
     (lambda list
       (lambda value
         (list-case list
           (cons value nil)
           cell
           (cons
             (head cell)
             ((self (tail cell)) value))))))))

(def concat
  ((lambda fixed_point_function
     ((lambda fixed_point_self
        (fixed_point_function
          (lambda fixed_point_value
            ((fixed_point_self fixed_point_self) fixed_point_value))))
      (lambda fixed_point_self
        (fixed_point_function
          (lambda fixed_point_value
            ((fixed_point_self fixed_point_self) fixed_point_value))))))
   (lambda self
     (lambda lists
       (list-case lists
         nil
        cell
        ((append (head cell))
         (self (tail cell))))))))

(def map
  ((lambda fixed_point_function
     ((lambda fixed_point_self
        (fixed_point_function
          (lambda fixed_point_value
            ((fixed_point_self fixed_point_self) fixed_point_value))))
      (lambda fixed_point_self
        (fixed_point_function
          (lambda fixed_point_value
            ((fixed_point_self fixed_point_self) fixed_point_value))))))
   (lambda self
     (lambda function
       (lambda list
         (list-case list
           nil
           cell
           (cons
             (function (head cell))
             ((self function) (tail cell)))))))))

(def concat-map
  (lambda function
    (lambda list
      (list-case list
        nil
        cell
        (append
          (function (head cell))
          (concat-map function (tail cell)))))))

(def fold-right
  (lambda function
    (lambda initial
      (lambda list
        (list-case list
          initial
          cell
          (function
            (head cell)
            (fold-right function initial (tail cell))))))))

(def fold-left
  (lambda function
    (lambda initial
      (lambda list
        (list-case list
          initial
          cell
          (fold-left
            function
            (function initial (head cell))
            (tail cell)))))))

(def zip-with
  (lambda function
    (lambda left
      (lambda right
        (list-case left
          nil
          left_cell
          (list-case right
            nil
            right_cell
            (cons
              (function (head left_cell) (head right_cell))
              (zip-with
                function
                (tail left_cell)
                (tail right_cell)))))))))

(def filter
  (lambda predicate
    (lambda list
      (list-case list
        nil
        cell
        (if
          (predicate (head cell))
          (cons
            (head cell)
            (filter predicate (tail cell)))
          (filter predicate (tail cell)))))))

(def any
  (lambda predicate
    (lambda list
      (list-case list
        (quote :false)
        cell
        (if
          (predicate (head cell))
          (quote :true)
          (any predicate (tail cell)))))))

(def all
  (lambda predicate
    (lambda list
      (list-case list
        (quote :true)
        cell
        (if
          (predicate (head cell))
          (all predicate (tail cell))
          (quote :false))))))

(def is-symbol
  (lambda value
    (symbol-eq (value-kind value) (quote :symbol))))

(def is-lambda
  (lambda value
    (symbol-eq (value-kind value) (quote :lambda))))

(def is-list-value
  (lambda value
    (symbol-eq (value-kind value) (quote :list))))

(def value-eq
  (lambda left
    (lambda right
      (if
        (is-lambda left)
        (error 0)
        (if
          (is-lambda right)
          (error 0)
          (if
            (is-symbol left)
            (symbol-eq left right)
            (if
              (is-symbol right)
              (quote :false)
              (list-case left
                (list-case right
                  (quote :true)
                  right_cell
                  (quote :false))
                left_cell
                (list-case right
                  (quote :false)
                  right_cell
                  (if
                    (value-eq (head left_cell) (head right_cell))
                    (value-eq (tail left_cell) (tail right_cell))
                    (quote :false)))))))))))

(def member
  (lambda value
    (lambda list
      (list-case list
        (quote :false)
        cell
        (if
          (value-eq value (head cell))
          (quote :true)
          (member value (tail cell)))))))

(def last
  ((lambda fixed_point_function
     ((lambda fixed_point_self
        (fixed_point_function
          (lambda fixed_point_value
            ((fixed_point_self fixed_point_self) fixed_point_value))))
      (lambda fixed_point_self
        (fixed_point_function
          (lambda fixed_point_value
            ((fixed_point_self fixed_point_self) fixed_point_value))))))
   (lambda self
     (lambda list
       (list-case list
         (error 0)
         cell
         (list-case (tail cell)
           (head cell)
           rest_cell
           (self (tail cell))))))))

(def init
  ((lambda fixed_point_function
     ((lambda fixed_point_self
        (fixed_point_function
          (lambda fixed_point_value
            ((fixed_point_self fixed_point_self) fixed_point_value))))
      (lambda fixed_point_self
        (fixed_point_function
          (lambda fixed_point_value
            ((fixed_point_self fixed_point_self) fixed_point_value))))))
   (lambda self
     (lambda list
       (list-case list
         (error 0)
         cell
         (list-case (tail cell)
           nil
           rest_cell
           (cons
             (head cell)
             (self (tail cell)))))))))

(def null
  (lambda list
    (list-case list
      (quote :true)
      cell
      (quote :false))))

(def is-singleton
  (lambda list
    (list-case list
      (quote :false)
      cell
      (list-case (tail cell)
        (quote :true)
        rest_cell
        (quote :false)))))

(theorem reverse_acc_computes_to_list
  (forall list (is-list list)
    (forall acc (is-list acc)
      (computes-to-list result (reverse_acc list acc))))
  (proof
    (list-induction list
      (forall acc (is-list acc)
        (computes-to-list result (reverse_acc list acc)))
      (forall-intro acc (is-list acc)
        (exists-intro result (is-list result)
          (computes-to (reverse_acc nil acc) result)
          acc
          (eval-to (reverse_acc nil acc) acc)))
      head
      tail
      induction_hypothesis
      (forall-intro acc (is-list acc)
        (rewrite
          (symm
            (eval-same
              (reverse_acc (cons head tail) acc)
              (reverse_acc tail (cons head acc))))
          (forall-elim
            (assume induction_hypothesis)
            (cons head acc))
          rewrite_target
          (computes-to-list result rewrite_target))))))

(theorem reverse_computes_to_list
  (forall list (is-list list)
    (computes-to-list result (reverse list)))
  (proof
    (forall-intro list (is-list list)
      (rewrite
        (symm
          (eval-to
            (reverse list)
            (reverse_acc list nil)))
        (forall-elim
          (forall-elim
            (known reverse_acc_computes_to_list)
            list)
          nil)
        rewrite_target
        (computes-to-list result rewrite_target)))))

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
  (proof
    (list-induction left
      (forall right (is-list right)
        (computes-to-list result (append left right)))
      (forall-intro right (is-list right)
        (exists-intro result (is-list result)
          (computes-to (append nil right) result)
          right
          (eval-to (append nil right) right)))
      head
      tail
      induction_hypothesis
      (forall-intro right (is-list right)
        (exists-elim
          (forall-elim
            (assume induction_hypothesis)
            right)
          tail_result
          tail_result_proof
          (exists-intro result (is-list result)
            (computes-to (append (cons head tail) right) result)
            (cons head tail_result)
            (rewrite
              (assume tail_result_proof)
              (eval-same
                (append (cons head tail) right)
                (cons head (append tail right)))
              rewrite_target
              (computes-to
                (append (cons head tail) right)
                (cons head rewrite_target)))))))))

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
              (rewrite induction_hypothesis)
              (eval))))))))

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
  (proof
    (forall-intro function (is-value function)
      (implies-intro maps_values
        (forall value (is-value value)
          (exists mapped_value (is-value mapped_value)
            (computes-to (function value) mapped_value)))
        (list-induction list
          (computes-to-list result (map function list))
          (exists-intro result (is-list result)
            (computes-to (map function nil) result)
            nil
            (eval-to (map function nil) nil))
          head
          tail
          induction_hypothesis
          (exists-elim
            (forall-elim
              (assume maps_values)
              head)
            mapped_head
            mapped_head_proof
            (exists-elim
              (assume induction_hypothesis)
              mapped_tail
              mapped_tail_proof
              (exists-intro result (is-list result)
                (computes-to (map function (cons head tail)) result)
                (cons mapped_head mapped_tail)
                (rewrite
                  (assume mapped_tail_proof)
                  (rewrite
                    (assume mapped_head_proof)
                    (forall-elim
                      (forall-elim
                        (forall-elim
                          (known map_cons)
                          function)
                        head)
                      tail)
                    mapped_head_rewrite_target
                    (computes-to
                      (map function (cons head tail))
                      (cons mapped_head_rewrite_target (map function tail))))
                  mapped_tail_rewrite_target
                  (computes-to
                    (map function (cons head tail))
                    (cons mapped_head mapped_tail_rewrite_target)))))))))))

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
  (proof
    (forall-intro function (is-value function)
      (forall-intro head (is-value head)
        (forall-intro tail (is-list tail)
          (trans
            (eval-to
              (concat-map function (cons head tail))
              (append
                (function (head (cons head tail)))
                (concat-map function (tail (cons head tail)))))
            (rewrite
              (eval-to
                (tail (cons head tail))
                tail)
              (rewrite
                (eval-to
                  (head (cons head tail))
                  head)
                (eval-to
                  (append
                    (function (head (cons head tail)))
                    (concat-map function (tail (cons head tail))))
                  (append
                    (function (head (cons head tail)))
                    (concat-map function (tail (cons head tail)))))
                head_rewrite_target
                (computes-to
                  (append
                    (function (head (cons head tail)))
                    (concat-map function (tail (cons head tail))))
                  (append
                    (function head_rewrite_target)
                    (concat-map function (tail (cons head tail))))))
              tail_rewrite_target
              (computes-to
                (append
                  (function (head (cons head tail)))
                  (concat-map function (tail (cons head tail))))
                (append
                  (function head)
                  (concat-map function tail_rewrite_target))))))))))

(theorem concat_map_computes_to_list
  (forall function (is-value function)
    (implies
      (forall value (is-value value)
        (computes-to-list mapped_list (function value)))
      (forall list (is-list list)
        (computes-to-list result (concat-map function list)))))
  (proof
    (forall-intro function (is-value function)
      (implies-intro maps_values_to_lists
        (forall value (is-value value)
          (computes-to-list mapped_list (function value)))
        (list-induction list
          (computes-to-list result (concat-map function list))
          (exists-intro result (is-list result)
            (computes-to (concat-map function nil) result)
            nil
            (eval-to (concat-map function nil) nil))
          head
          tail
          induction_hypothesis
          (exists-elim
            (forall-elim
              (assume maps_values_to_lists)
              head)
            mapped_head
            mapped_head_proof
            (exists-elim
              (assume induction_hypothesis)
              mapped_tail
              mapped_tail_proof
              (exists-elim
                (forall-elim
                  (forall-elim
                    (known append_computes_to_list)
                    mapped_head)
                  mapped_tail)
                appended
                appended_proof
                (exists-intro result (is-list result)
                  (computes-to (concat-map function (cons head tail)) result)
                  appended
                  (trans
                    (rewrite
                      (assume mapped_tail_proof)
                      (rewrite
                        (assume mapped_head_proof)
                        (forall-elim
                          (forall-elim
                            (forall-elim
                              (known concat_map_cons)
                              function)
                            head)
                          tail)
                        mapped_head_rewrite_target
                        (computes-to
                          (concat-map function (cons head tail))
                          (append
                            mapped_head_rewrite_target
                            (concat-map function tail))))
                      mapped_tail_rewrite_target
                      (computes-to
                        (concat-map function (cons head tail))
                        (append
                          mapped_head
                          mapped_tail_rewrite_target)))
                    (assume appended_proof)))))))))))

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
  (proof
    (forall-intro function (is-value function)
      (forall-intro initial (is-value initial)
        (forall-intro head (is-value head)
          (forall-intro tail (is-list tail)
            (trans
              (eval-to
                (fold-right function initial (cons head tail))
                (function
                  (head (cons head tail))
                  (fold-right
                    function
                    initial
                    (tail (cons head tail)))))
              (rewrite
                (eval-to
                  (tail (cons head tail))
                  tail)
                (rewrite
                  (eval-to
                    (head (cons head tail))
                    head)
                  (eval-to
                    (function
                      (head (cons head tail))
                      (fold-right
                        function
                        initial
                        (tail (cons head tail))))
                    (function
                      (head (cons head tail))
                      (fold-right
                        function
                        initial
                        (tail (cons head tail)))))
                  head_rewrite_target
                  (computes-to
                    (function
                      (head (cons head tail))
                      (fold-right
                        function
                        initial
                        (tail (cons head tail))))
                    (function
                      head_rewrite_target
                      (fold-right
                        function
                        initial
                        (tail (cons head tail))))))
                tail_rewrite_target
                (computes-to
                  (function
                    (head (cons head tail))
                    (fold-right
                      function
                      initial
                      (tail (cons head tail))))
                  (function
                    head
                    (fold-right
                      function
                      initial
                      tail_rewrite_target)))))))))))

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
  (proof
    (forall-intro function (is-value function)
      (forall-intro initial (is-value initial)
        (implies-intro combines_values
          (forall value (is-value value)
            (forall accumulator (is-value accumulator)
              (exists folded_value (is-value folded_value)
                (computes-to
                  (function value accumulator)
                  folded_value))))
          (list-induction list
            (exists result (is-value result)
              (computes-to
                (fold-right function initial list)
                result))
            (exists-intro result (is-value result)
              (computes-to (fold-right function initial nil) result)
              initial
              (eval-to (fold-right function initial nil) initial))
            head
            tail
            induction_hypothesis
            (exists-elim
              (assume induction_hypothesis)
              tail_result
              tail_result_proof
              (exists-elim
                (forall-elim
                  (forall-elim
                    (assume combines_values)
                    head)
                  tail_result)
                folded_result
                folded_result_proof
                (exists-intro result (is-value result)
                  (computes-to
                    (fold-right function initial (cons head tail))
                    result)
                  folded_result
                  (trans
                    (forall-elim
                      (forall-elim
                        (forall-elim
                          (forall-elim
                            (known fold_right_cons)
                            function)
                          initial)
                        head)
                      tail)
                    (rewrite
                      (symm
                        (assume tail_result_proof))
                      (assume folded_result_proof)
                      tail_result_rewrite_target
                      (computes-to
                        (function head tail_result_rewrite_target)
                        folded_result))))))))))))

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
  (proof
    (forall-intro function (is-value function)
      (forall-intro initial (is-value initial)
        (forall-intro head (is-value head)
          (forall-intro tail (is-list tail)
            (trans
              (eval-to
                (fold-left function initial (cons head tail))
                (fold-left
                  function
                  (function initial (head (cons head tail)))
                  (tail (cons head tail))))
              (rewrite
                (eval-to
                  (tail (cons head tail))
                  tail)
                (rewrite
                  (eval-to
                    (head (cons head tail))
                    head)
                  (eval-to
                    (fold-left
                      function
                      (function initial (head (cons head tail)))
                      (tail (cons head tail)))
                    (fold-left
                      function
                      (function initial (head (cons head tail)))
                      (tail (cons head tail))))
                  head_rewrite_target
                  (computes-to
                    (fold-left
                      function
                      (function initial (head (cons head tail)))
                      (tail (cons head tail)))
                    (fold-left
                      function
                      (function initial head_rewrite_target)
                      (tail (cons head tail)))))
                tail_rewrite_target
                (computes-to
                  (fold-left
                    function
                    (function initial (head (cons head tail)))
                    (tail (cons head tail)))
                  (fold-left
                    function
                    (function initial head)
                    tail_rewrite_target))))))))))

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
  (proof
    (forall-intro function (is-value function)
      (implies-intro combines_values
        (forall accumulator (is-value accumulator)
          (forall value (is-value value)
            (exists folded_value (is-value folded_value)
              (computes-to
                (function accumulator value)
                folded_value))))
        (list-induction list
          (forall initial (is-value initial)
            (exists result (is-value result)
              (computes-to
                (fold-left function initial list)
                result)))
          (forall-intro initial (is-value initial)
            (exists-intro result (is-value result)
              (computes-to (fold-left function initial nil) result)
              initial
              (eval-to (fold-left function initial nil) initial)))
          head
          tail
          induction_hypothesis
          (forall-intro initial (is-value initial)
            (exists-elim
              (forall-elim
                (forall-elim
                  (assume combines_values)
                  initial)
                head)
              folded_initial
              folded_initial_proof
              (exists-elim
                (forall-elim
                  (assume induction_hypothesis)
                  folded_initial)
                result
                result_proof
                (exists-intro result (is-value result)
                  (computes-to
                    (fold-left function initial (cons head tail))
                    result)
                  result
                  (trans
                    (forall-elim
                      (forall-elim
                        (forall-elim
                          (forall-elim
                            (known fold_left_cons)
                            function)
                          initial)
                        head)
                      tail)
                    (rewrite
                      (symm
                        (assume folded_initial_proof))
                      (assume result_proof)
                      folded_initial_rewrite_target
                      (computes-to
                        (fold-left function folded_initial_rewrite_target tail)
                        result))))))))))))

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
  (proof
    (forall-intro function (is-value function)
      (list-induction left
        (computes-to (zip-with function left nil) nil)
        (eval-to (zip-with function nil nil) nil)
        head
        tail
        induction_hypothesis
        (eval-to (zip-with function (cons head tail) nil) nil)))))

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
  (proof
    (forall-intro function (is-value function)
      (implies-intro combines_values
        (forall left_value (is-value left_value)
          (forall right_value (is-value right_value)
            (exists zipped_value (is-value zipped_value)
              (computes-to
                (function left_value right_value)
                zipped_value))))
        (list-induction left
          (forall right (is-list right)
            (computes-to-list result (zip-with function left right)))
          (forall-intro right (is-list right)
            (exists-intro result (is-list result)
              (computes-to (zip-with function nil right) result)
              nil
              (eval-to (zip-with function nil right) nil)))
          left_head
          left_tail
          left_induction_hypothesis
          (list-induction right
            (computes-to-list
              result
              (zip-with function (cons left_head left_tail) right))
            (exists-intro result (is-list result)
              (computes-to
                (zip-with function (cons left_head left_tail) nil)
                result)
              nil
              (eval-to
                (zip-with function (cons left_head left_tail) nil)
                nil))
            right_head
            right_tail
            right_induction_hypothesis
            (exists-elim
              (forall-elim
                (forall-elim
                  (assume combines_values)
                  left_head)
                right_head)
              zipped_head
              zipped_head_proof
              (exists-elim
                (forall-elim
                  (assume left_induction_hypothesis)
                  right_tail)
                zipped_tail
                zipped_tail_proof
                (exists-intro result (is-list result)
                  (computes-to
                    (zip-with
                      function
                      (cons left_head left_tail)
                      (cons right_head right_tail))
                    result)
                  (cons zipped_head zipped_tail)
                  (rewrite
                    (assume zipped_tail_proof)
                    (rewrite
                      (assume zipped_head_proof)
                      (forall-elim
                        (forall-elim
                          (forall-elim
                            (forall-elim
                              (forall-elim
                                (known zip_with_cons)
                                function)
                              left_head)
                            left_tail)
                          right_head)
                        right_tail)
                      zipped_head_rewrite_target
                      (computes-to
                        (zip-with
                          function
                          (cons left_head left_tail)
                          (cons right_head right_tail))
                        (cons
                          zipped_head_rewrite_target
                          (zip-with function left_tail right_tail))))
                    zipped_tail_rewrite_target
                    (computes-to
                      (zip-with
                        function
                        (cons left_head left_tail)
                        (cons right_head right_tail))
                      (cons
                        zipped_head
                        zipped_tail_rewrite_target))))))))))))

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
    (calc
      (filter predicate (cons head tail))
      (==
        (if
          (predicate head)
          (cons
            (head (cons head tail))
            (filter predicate (tail (cons head tail))))
          (filter predicate (tail (cons head tail))))
        (by
          (eval)))
      (==
        (if
          (quote :true)
          (cons
            (head (cons head tail))
            (filter predicate (tail (cons head tail))))
          (filter predicate (tail (cons head tail))))
        (by
          (rewrite predicate_true)
          (eval)))
      (==
        (cons head (filter predicate tail))
        (by
          (eval))))))

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
    (calc
      (filter predicate (cons head tail))
      (==
        (if
          (predicate head)
          (cons
            (head (cons head tail))
            (filter predicate (tail (cons head tail))))
          (filter predicate (tail (cons head tail))))
        (by
          (eval)))
      (==
        (if
          (quote :false)
          (cons
            (head (cons head tail))
            (filter predicate (tail (cons head tail))))
          (filter predicate (tail (cons head tail))))
        (by
          (rewrite predicate_false)
          (eval)))
      (==
        (filter predicate tail)
        (by
          (eval))))))

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
    (calc
      (any predicate (cons head tail))
      (==
        (if
          (predicate head)
          (quote :true)
          (any predicate (tail (cons head tail))))
        (by
          (eval)))
      (==
        (if
          (quote :true)
          (quote :true)
          (any predicate (tail (cons head tail))))
        (by
          (rewrite predicate_true)
          (eval)))
      (==
        (quote :true)
        (by
          (eval))))))

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
    (calc
      (any predicate (cons head tail))
      (==
        (if
          (predicate head)
          (quote :true)
          (any predicate (tail (cons head tail))))
        (by
          (eval)))
      (==
        (if
          (quote :false)
          (quote :true)
          (any predicate (tail (cons head tail))))
        (by
          (rewrite predicate_false)
          (eval)))
      (==
        (any predicate tail)
        (by
          (eval))))))

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
    (calc
      (all predicate (cons head tail))
      (==
        (if
          (predicate head)
          (all predicate (tail (cons head tail)))
          (quote :false))
        (by
          (eval)))
      (==
        (if
          (quote :true)
          (all predicate (tail (cons head tail)))
          (quote :false))
        (by
          (rewrite predicate_true)
          (eval)))
      (==
        (all predicate tail)
        (by
          (eval))))))

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
    (calc
      (all predicate (cons head tail))
      (==
        (if
          (predicate head)
          (all predicate (tail (cons head tail)))
          (quote :false))
        (by
          (eval)))
      (==
        (if
          (quote :false)
          (all predicate (tail (cons head tail)))
          (quote :false))
        (by
          (rewrite predicate_false)
          (eval)))
      (==
        (quote :false)
        (by
          (eval))))))

(theorem filter_computes_to_list
  (forall predicate (is-value predicate)
    (implies
      (forall value (is-value value)
        (is-bool (predicate value)))
      (forall list (is-list list)
        (computes-to-list result (filter predicate list)))))
  (proof
    (forall-intro predicate (is-value predicate)
      (implies-intro predicate_returns_bool
        (forall value (is-value value)
          (is-bool (predicate value)))
        (list-induction list
          (computes-to-list result (filter predicate list))
          (exists-intro result (is-list result)
            (computes-to (filter predicate nil) result)
            nil
            (eval-to (filter predicate nil) nil))
          head
          tail
          induction_hypothesis
          (or-elim
            (forall-elim
              (assume predicate_returns_bool)
              head)
            predicate_true
            (exists-elim
              (assume induction_hypothesis)
              filtered_tail
              filtered_tail_proof
              (exists-intro result (is-list result)
                (computes-to
                  (filter predicate (cons head tail))
                  result)
                (cons head filtered_tail)
                (rewrite
                  (assume filtered_tail_proof)
                  (implies-elim
                    (forall-elim
                      (forall-elim
                        (forall-elim
                          (known filter_cons_true)
                          predicate)
                        head)
                      tail)
                    (assume predicate_true))
                  filtered_tail_rewrite_target
                  (computes-to
                    (filter predicate (cons head tail))
                    (cons head filtered_tail_rewrite_target)))))
            predicate_false
            (exists-elim
              (assume induction_hypothesis)
              filtered_tail
              filtered_tail_proof
              (exists-intro result (is-list result)
                (computes-to
                  (filter predicate (cons head tail))
                  result)
                filtered_tail
                (trans
                  (implies-elim
                    (forall-elim
                      (forall-elim
                        (forall-elim
                          (known filter_cons_false)
                          predicate)
                        head)
                      tail)
                    (assume predicate_false))
                  (assume filtered_tail_proof))))))))))

(theorem any_computes_to_bool
  (forall predicate (is-value predicate)
    (implies
      (forall value (is-value value)
        (is-bool (predicate value)))
      (forall list (is-list list)
        (is-bool (any predicate list)))))
  (proof
    (forall-intro predicate (is-value predicate)
      (implies-intro predicate_returns_bool
        (forall value (is-value value)
          (is-bool (predicate value)))
        (list-induction list
          (is-bool (any predicate list))
          (or-intro-right
            (computes-to (any predicate nil) (quote :true))
            (eval-to (any predicate nil) (quote :false)))
          head
          tail
          induction_hypothesis
          (or-elim
            (forall-elim
              (assume predicate_returns_bool)
              head)
            predicate_true
            (or-intro-left
              (implies-elim
                (forall-elim
                  (forall-elim
                    (forall-elim
                      (known any_cons_true)
                      predicate)
                    head)
                  tail)
                (assume predicate_true))
              (computes-to
                (any predicate (cons head tail))
                (quote :false)))
            predicate_false
            (or-elim
              (assume induction_hypothesis)
              tail_true
              (or-intro-left
                (trans
                  (implies-elim
                    (forall-elim
                      (forall-elim
                        (forall-elim
                          (known any_cons_false)
                          predicate)
                        head)
                      tail)
                    (assume predicate_false))
                  (assume tail_true))
                (computes-to
                  (any predicate (cons head tail))
                  (quote :false)))
              tail_false
              (or-intro-right
                (computes-to
                  (any predicate (cons head tail))
                  (quote :true))
                (trans
                  (implies-elim
                    (forall-elim
                      (forall-elim
                        (forall-elim
                          (known any_cons_false)
                          predicate)
                        head)
                      tail)
                    (assume predicate_false))
                  (assume tail_false))))))))))

(theorem all_computes_to_bool
  (forall predicate (is-value predicate)
    (implies
      (forall value (is-value value)
        (is-bool (predicate value)))
      (forall list (is-list list)
        (is-bool (all predicate list)))))
  (proof
    (forall-intro predicate (is-value predicate)
      (implies-intro predicate_returns_bool
        (forall value (is-value value)
          (is-bool (predicate value)))
        (list-induction list
          (is-bool (all predicate list))
          (or-intro-left
            (eval-to (all predicate nil) (quote :true))
            (computes-to (all predicate nil) (quote :false)))
          head
          tail
          induction_hypothesis
          (or-elim
            (forall-elim
              (assume predicate_returns_bool)
              head)
            predicate_true
            (or-elim
              (assume induction_hypothesis)
              tail_true
              (or-intro-left
                (trans
                  (implies-elim
                    (forall-elim
                      (forall-elim
                        (forall-elim
                          (known all_cons_true)
                          predicate)
                        head)
                      tail)
                    (assume predicate_true))
                  (assume tail_true))
                (computes-to
                  (all predicate (cons head tail))
                  (quote :false)))
              tail_false
              (or-intro-right
                (computes-to
                  (all predicate (cons head tail))
                  (quote :true))
                (trans
                  (implies-elim
                    (forall-elim
                      (forall-elim
                        (forall-elim
                          (known all_cons_true)
                          predicate)
                        head)
                      tail)
                    (assume predicate_true))
                  (assume tail_false))))
            predicate_false
            (or-intro-right
              (computes-to
                (all predicate (cons head tail))
                (quote :true))
              (implies-elim
                (forall-elim
                  (forall-elim
                    (forall-elim
                      (known all_cons_false)
                      predicate)
                    head)
                  tail)
                (assume predicate_false)))))))))

(theorem value_eq_true_true
  (computes-to
    (value-eq (quote :true) (quote :true))
    (quote :true))
  (by
    (eval)))

(theorem value_eq_true_false
  (computes-to
    (value-eq (quote :true) (quote :false))
    (quote :false))
  (by
    (eval)))

(theorem value_eq_nil
  (computes-to (value-eq nil nil) (quote :true))
  (by
    (eval)))

(theorem value_eq_nil_cons
  (forall head (is-value head)
    (forall tail (is-list tail)
      (computes-to
        (value-eq nil (cons head tail))
        (quote :false))))
  (by
    (intro head)
    (intro tail)
    (eval)))

(theorem value_eq_cons_nil
  (forall head (is-value head)
    (forall tail (is-list tail)
      (computes-to
        (value-eq (cons head tail) nil)
        (quote :false))))
  (by
    (intro head)
    (intro tail)
    (eval)))

(theorem value_eq_cons
  (forall left_head (is-value left_head)
    (forall left_tail (is-list left_tail)
      (forall right_head (is-value right_head)
        (forall right_tail (is-list right_tail)
          (computes-to
            (value-eq
              (cons left_head left_tail)
              (cons right_head right_tail))
            (if
              (value-eq
                (head (cons left_head left_tail))
                (head (cons right_head right_tail)))
              (value-eq
                (tail (cons left_head left_tail))
                (tail (cons right_head right_tail)))
              (quote :false)))))))
  (by
    (intro left_head)
    (intro left_tail)
    (intro right_head)
    (intro right_tail)
    (eval)))

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
    (calc
      (member value (cons head tail))
      (==
        (if
          (value-eq value head)
          (quote :true)
          (member value (tail (cons head tail))))
        (by
          (eval)))
      (==
        (if
          (quote :true)
          (quote :true)
          (member value (tail (cons head tail))))
        (by
          (rewrite value_eq_true)
          (eval)))
      (==
        (quote :true)
        (by
          (eval))))))

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
    (calc
      (member value (cons head tail))
      (==
        (if
          (value-eq value head)
          (quote :true)
          (member value (tail (cons head tail))))
        (by
          (eval)))
      (==
        (if
          (quote :false)
          (quote :true)
          (member value (tail (cons head tail))))
        (by
          (rewrite value_eq_false)
          (eval)))
      (==
        (member value tail)
        (by
          (eval))))))

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
        (calc
          (map (lambda value value) (cons head tail))
          (==
            (cons
              ((lambda value value) head)
              (map (lambda value value) tail))
            (by
              (apply map_cons (lambda value value) head tail)))
          (==
            (cons head (map (lambda value value) tail))
            (by
              (eval)))
          (==
            (cons head tail)
            (by
              (rewrite induction_hypothesis)
              (eval))))))))

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
        (calc
          (concat-map (lambda value (cons value nil)) (cons head tail))
          (==
            (append
              ((lambda value (cons value nil)) head)
              (concat-map (lambda value (cons value nil)) tail))
            (by
              (apply concat_map_cons (lambda value (cons value nil)) head tail)))
          (==
            (append
              (cons head nil)
              (concat-map (lambda value (cons value nil)) tail))
            (by
              (eval)))
          (==
            (append (cons head nil) tail)
            (by
              (rewrite induction_hypothesis)
              (eval)))
          (==
            (cons head tail)
            (by
              (apply append_singleton head tail))))))))

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
        (calc
          (fold-right
            (lambda value
              (lambda accumulator
                (cons value accumulator)))
            nil
            (cons head tail))
          (==
            ((lambda value
               (lambda accumulator
                 (cons value accumulator)))
             head
             (fold-right
               (lambda value
                 (lambda accumulator
                   (cons value accumulator)))
               nil
               tail))
            (by
              (apply
                fold_right_cons
                (lambda value
                  (lambda accumulator
                    (cons value accumulator)))
                nil
                head
                tail)))
          (==
            ((lambda value
               (lambda accumulator
                 (cons value accumulator)))
             head
             tail)
            (by
              (rewrite induction_hypothesis)
              (eval)))
          (==
            (cons head tail)
            (by
              (eval))))))))

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
  (proof
    (list-induction list
      (forall acc (is-list acc)
        (computes-to
          (fold-left
            (lambda accumulator
              (lambda value
                (cons value accumulator)))
            acc
            list)
          (reverse_acc list acc)))
      (forall-intro acc (is-list acc)
        (eval-same
          (fold-left
            (lambda accumulator
              (lambda value
                (cons value accumulator)))
            acc
            nil)
          (reverse_acc nil acc)))
      head
      tail
      induction_hypothesis
      (forall-intro acc (is-list acc)
        (trans
          (rewrite
            (eval-to
              ((lambda accumulator
                 (lambda value
                   (cons value accumulator)))
               acc
               head)
              (cons head acc))
            (forall-elim
              (forall-elim
                (forall-elim
                  (forall-elim
                    (known fold_left_cons)
                    (lambda accumulator
                      (lambda value
                        (cons value accumulator))))
                  acc)
                head)
              tail)
            next_accumulator_rewrite_target
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
                next_accumulator_rewrite_target
                tail)))
          (trans
            (forall-elim
              (assume induction_hypothesis)
              (cons head acc))
            (symm
              (eval-same
                (reverse_acc (cons head tail) acc)
                (reverse_acc tail (cons head acc))))))))))

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
  (proof
    (forall-intro list (is-list list)
      (trans
        (forall-elim
          (forall-elim
            (known fold_left_reverse_acc)
            list)
          nil)
        (symm
          (eval-to
            (reverse list)
            (reverse_acc list nil)))))))

(theorem append_assoc
  (forall left (is-list left)
    (forall middle (is-list middle)
      (forall right (is-list right)
        (computes-to
          (append (append left middle) right)
          (append left (append middle right))))))
  (proof
    (list-induction left
      (forall middle (is-list middle)
        (forall right (is-list right)
          (computes-to
            (append (append left middle) right)
            (append left (append middle right)))))
      (forall-intro middle (is-list middle)
        (forall-intro right (is-list right)
          (trans
            (symm
              (rewrite
                (forall-elim
                  (known append_nil_returns_right)
                  middle)
                (eval-to
                  (append (append nil middle) right)
                  (append (append nil middle) right))
                rewrite_target
                (computes-to
                  (append rewrite_target right)
                  (append (append nil middle) right))))
            (symm
              (exists-elim
                (forall-elim
                  (forall-elim
                    (known append_computes_to_list)
                    middle)
                  right)
                middle_right
                middle_right_proof
                (rewrite
                  (symm
                    (assume middle_right_proof))
                  (forall-elim
                    (known append_nil_returns_right)
                    middle_right)
                  rewrite_target
                  (computes-to
                    (append nil rewrite_target)
                    rewrite_target)))))))
      head
      tail
      induction_hypothesis
      (forall-intro middle (is-list middle)
        (forall-intro right (is-list right)
          (exists-elim
            (forall-elim
              (forall-elim
                (known append_computes_to_list)
                tail)
              middle)
            tail_middle
            tail_middle_proof
            (exists-elim
              (forall-elim
                (forall-elim
                  (known append_computes_to_list)
                  middle)
                right)
              middle_right
              middle_right_proof
              (trans
                (symm
                  (rewrite
                    (forall-elim
                      (forall-elim
                        (forall-elim
                          (known append_cons)
                          head)
                        tail)
                      middle)
                    (eval-to
                      (append (append (cons head tail) middle) right)
                      (append (append (cons head tail) middle) right))
                    rewrite_target
                    (computes-to
                      (append rewrite_target right)
                      (append (append (cons head tail) middle) right))))
                (trans
                  (rewrite
                    (symm
                      (assume tail_middle_proof))
                    (forall-elim
                      (forall-elim
                        (forall-elim
                          (known append_cons)
                          head)
                        tail_middle)
                      right)
                    rewrite_target
                    (computes-to
                      (append (cons head rewrite_target) right)
                      (cons head (append rewrite_target right))))
                  (trans
                    (rewrite
                      (forall-elim
                        (forall-elim
                          (assume induction_hypothesis)
                          middle)
                        right)
                      (eval-to
                        (cons head (append (append tail middle) right))
                        (cons head (append (append tail middle) right)))
                      rewrite_target
                      (computes-to
                        (cons head (append (append tail middle) right))
                        (cons head rewrite_target)))
                    (symm
                      (rewrite
                        (symm
                          (assume middle_right_proof))
                        (forall-elim
                          (forall-elim
                            (forall-elim
                              (known append_cons)
                              head)
                            tail)
                          middle_right)
                        rewrite_target
                        (computes-to
                          (append (cons head tail) rewrite_target)
                          (cons head (append tail rewrite_target)))))))))))))))

(theorem reverse_acc_append
  (forall list (is-list list)
    (forall acc (is-list acc)
      (computes-to
        (reverse_acc list acc)
        (append (reverse list) acc))))
  (proof
    (list-induction list
      (forall acc (is-list acc)
        (computes-to
          (reverse_acc list acc)
          (append (reverse list) acc)))
      (forall-intro acc (is-list acc)
        (eval-same
          (reverse_acc nil acc)
          (append (reverse nil) acc)))
      head
      tail
      induction_hypothesis
      (forall-intro acc (is-list acc)
        (exists-elim
          (forall-elim
            (known reverse_computes_to_list)
            tail)
          tail_reversed
          tail_reversed_proof
          (trans
            (trans
              (eval-same
                (reverse_acc (cons head tail) acc)
                (reverse_acc tail (cons head acc)))
              (rewrite
                (assume tail_reversed_proof)
                (forall-elim
                  (assume induction_hypothesis)
                  (cons head acc))
                rewrite_target
                (computes-to
                  (reverse_acc tail (cons head acc))
                  (append rewrite_target (cons head acc)))))
            (trans
              (symm
                (rewrite
                  (forall-elim
                    (forall-elim
                      (known append_singleton)
                      head)
                    acc)
                  (forall-elim
                    (forall-elim
                      (forall-elim
                        (known append_assoc)
                        tail_reversed)
                      (cons head nil))
                    acc)
                  rewrite_target
                  (computes-to
                    (append (append tail_reversed (cons head nil)) acc)
                    (append tail_reversed rewrite_target))))
              (rewrite
                (symm
                  (trans
                    (trans
                      (eval-to
                        (reverse (cons head tail))
                        (reverse_acc (cons head tail) nil))
                      (eval-same
                        (reverse_acc (cons head tail) nil)
                        (reverse_acc tail (cons head nil))))
                    (rewrite
                      (assume tail_reversed_proof)
                      (forall-elim
                        (assume induction_hypothesis)
                        (cons head nil))
                      rewrite_target
                      (computes-to
                        (reverse_acc tail (cons head nil))
                        (append rewrite_target (cons head nil))))))
                (eval-to
                  (append (append tail_reversed (cons head nil)) acc)
                  (append (append tail_reversed (cons head nil)) acc))
                rewrite_target
                (computes-to
                  (append (append tail_reversed (cons head nil)) acc)
                  (append rewrite_target acc))))))))))

(theorem reverse_cons
  (forall head (is-value head)
    (forall tail (is-list tail)
      (computes-to
        (reverse (cons head tail))
        (append (reverse tail) (cons head nil)))))
  (proof
    (forall-intro head (is-value head)
      (forall-intro tail (is-list tail)
        (trans
          (trans
            (eval-to
              (reverse (cons head tail))
              (reverse_acc (cons head tail) nil))
            (eval-same
              (reverse_acc (cons head tail) nil)
              (reverse_acc tail (cons head nil))))
          (forall-elim
            (forall-elim
              (known reverse_acc_append)
              tail)
            (cons head nil)))))))

(theorem reverse_acc_reverse
  (forall list (is-list list)
    (forall acc (is-list acc)
      (computes-to
        (reverse (reverse_acc list acc))
        (append (reverse acc) list))))
  (proof
    (list-induction list
      (forall acc (is-list acc)
        (computes-to
          (reverse (reverse_acc list acc))
          (append (reverse acc) list)))
      (forall-intro acc (is-list acc)
        (exists-elim
          (forall-elim
            (known reverse_computes_to_list)
            acc)
          acc_reversed
          acc_reversed_proof
          (trans
            (rewrite
              (eval-to
                (reverse_acc nil acc)
                acc)
              (eval-to
                (reverse (reverse_acc nil acc))
                (reverse (reverse_acc nil acc)))
              rewrite_target
              (computes-to
                (reverse (reverse_acc nil acc))
                (reverse rewrite_target)))
            (trans
              (assume acc_reversed_proof)
              (trans
                (symm
                  (forall-elim
                    (known append_right_nil)
                    acc_reversed))
                (rewrite
                  (symm
                    (assume acc_reversed_proof))
                  (eval-to
                    (append acc_reversed nil)
                    (append acc_reversed nil))
                  rewrite_target
                  (computes-to
                    (append acc_reversed nil)
                    (append rewrite_target nil))))))))
      head
      tail
      induction_hypothesis
      (forall-intro acc (is-list acc)
        (exists-elim
          (forall-elim
            (known reverse_computes_to_list)
            acc)
          acc_reversed
          acc_reversed_proof
          (trans
            (trans
              (rewrite
                (eval-same
                  (reverse_acc (cons head tail) acc)
                  (reverse_acc tail (cons head acc)))
                (eval-to
                  (reverse (reverse_acc (cons head tail) acc))
                  (reverse (reverse_acc (cons head tail) acc)))
                rewrite_target
                (computes-to
                  (reverse (reverse_acc (cons head tail) acc))
                  (reverse rewrite_target)))
              (forall-elim
                (assume induction_hypothesis)
                (cons head acc)))
            (trans
              (rewrite
                (rewrite
                  (assume acc_reversed_proof)
                  (forall-elim
                    (forall-elim
                      (known reverse_cons)
                      head)
                    acc)
                  rewrite_target
                  (computes-to
                    (reverse (cons head acc))
                    (append rewrite_target (cons head nil))))
                (eval-to
                  (append (reverse (cons head acc)) tail)
                  (append (reverse (cons head acc)) tail))
                rewrite_target
                (computes-to
                  (append (reverse (cons head acc)) tail)
                  (append rewrite_target tail)))
              (trans
                (rewrite
                  (forall-elim
                    (forall-elim
                      (known append_singleton)
                      head)
                    tail)
                  (forall-elim
                    (forall-elim
                      (forall-elim
                        (known append_assoc)
                        acc_reversed)
                      (cons head nil))
                    tail)
                  rewrite_target
                  (computes-to
                    (append (append acc_reversed (cons head nil)) tail)
                    (append acc_reversed rewrite_target)))
                (rewrite
                  (symm
                    (assume acc_reversed_proof))
                  (eval-to
                    (append acc_reversed (cons head tail))
                    (append acc_reversed (cons head tail)))
                  rewrite_target
                  (computes-to
                    (append acc_reversed (cons head tail))
                    (append rewrite_target (cons head tail))))))))))))

(theorem reverse_double
  (forall list (is-list list)
    (computes-to
      (reverse (reverse list))
      list))
  (proof
    (forall-intro list (is-list list)
      (trans
        (rewrite
          (eval-to
            (reverse list)
            (reverse_acc list nil))
          (eval-to
            (reverse (reverse list))
            (reverse (reverse list)))
          rewrite_target
          (computes-to
            (reverse (reverse list))
            (reverse rewrite_target)))
        (trans
          (forall-elim
            (forall-elim
              (known reverse_acc_reverse)
              list)
            nil)
          (trans
            (rewrite
              (known reverse_nil)
              (eval-to
                (append (reverse nil) list)
                (append (reverse nil) list))
              rewrite_target
              (computes-to
                (append (reverse nil) list)
                (append rewrite_target list)))
            (forall-elim
              (known append_nil_returns_right)
              list)))))))

(theorem reverse_acc_of_append
  (forall left (is-list left)
    (forall right (is-list right)
      (forall acc (is-list acc)
        (computes-to
          (reverse_acc (append left right) acc)
          (reverse_acc right (reverse_acc left acc))))))
  (proof
    (list-induction left
      (forall right (is-list right)
        (forall acc (is-list acc)
          (computes-to
            (reverse_acc (append left right) acc)
            (reverse_acc right (reverse_acc left acc)))))
      (forall-intro right (is-list right)
        (forall-intro acc (is-list acc)
          (eval-same
            (reverse_acc (append nil right) acc)
            (reverse_acc right (reverse_acc nil acc)))))
      head
      tail
      induction_hypothesis
      (forall-intro right (is-list right)
        (forall-intro acc (is-list acc)
          (exists-elim
            (forall-elim
              (forall-elim
                (known append_computes_to_list)
                tail)
              right)
            tail_right
            tail_right_proof
            (trans
              (rewrite
                (forall-elim
                  (forall-elim
                    (forall-elim
                      (known append_cons)
                      head)
                    tail)
                  right)
                (eval-to
                  (reverse_acc (append (cons head tail) right) acc)
                  (reverse_acc (append (cons head tail) right) acc))
                rewrite_target
                (computes-to
                  (reverse_acc (append (cons head tail) right) acc)
                  (reverse_acc rewrite_target acc)))
              (trans
                (rewrite
                  (assume tail_right_proof)
                  (eval-to
                    (reverse_acc (cons head (append tail right)) acc)
                    (reverse_acc (cons head (append tail right)) acc))
                  rewrite_target
                  (computes-to
                    (reverse_acc (cons head (append tail right)) acc)
                    (reverse_acc (cons head rewrite_target) acc)))
                (trans
                  (eval-same
                    (reverse_acc (cons head tail_right) acc)
                    (reverse_acc tail_right (cons head acc)))
                  (trans
                    (rewrite
                      (symm
                        (assume tail_right_proof))
                      (eval-to
                        (reverse_acc tail_right (cons head acc))
                        (reverse_acc tail_right (cons head acc)))
                      rewrite_target
                      (computes-to
                        (reverse_acc tail_right (cons head acc))
                        (reverse_acc rewrite_target (cons head acc))))
                    (trans
                      (forall-elim
                        (forall-elim
                          (assume induction_hypothesis)
                          right)
                        (cons head acc))
                      (rewrite
                        (symm
                          (eval-same
                            (reverse_acc (cons head tail) acc)
                            (reverse_acc tail (cons head acc))))
                        (eval-to
                          (reverse_acc right (reverse_acc tail (cons head acc)))
                          (reverse_acc right (reverse_acc tail (cons head acc))))
                        rewrite_target
                        (computes-to
                          (reverse_acc right (reverse_acc tail (cons head acc)))
                          (reverse_acc right rewrite_target))))))))))))))

(theorem reverse_append
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (reverse (append left right))
        (append (reverse right) (reverse left)))))
  (proof
    (forall-intro left (is-list left)
      (forall-intro right (is-list right)
        (exists-elim
          (forall-elim
            (forall-elim
              (known append_computes_to_list)
              left)
            right)
          appended
          appended_proof
          (exists-elim
            (forall-elim
              (forall-elim
                (known reverse_acc_computes_to_list)
                left)
              nil)
            left_reversed_acc
            left_reversed_acc_proof
            (trans
              (rewrite
                (assume appended_proof)
                (eval-to
                  (reverse (append left right))
                  (reverse (append left right)))
                rewrite_target
                (computes-to
                  (reverse (append left right))
                  (reverse rewrite_target)))
              (trans
                (eval-to
                  (reverse appended)
                  (reverse_acc appended nil))
                (trans
                  (rewrite
                    (symm
                      (assume appended_proof))
                    (eval-to
                      (reverse_acc appended nil)
                      (reverse_acc appended nil))
                    rewrite_target
                    (computes-to
                      (reverse_acc appended nil)
                      (reverse_acc rewrite_target nil)))
                  (trans
                    (forall-elim
                      (forall-elim
                        (forall-elim
                          (known reverse_acc_of_append)
                          left)
                        right)
                      nil)
                    (trans
                      (rewrite
                        (assume left_reversed_acc_proof)
                        (eval-to
                          (reverse_acc right (reverse_acc left nil))
                          (reverse_acc right (reverse_acc left nil)))
                        rewrite_target
                        (computes-to
                          (reverse_acc right (reverse_acc left nil))
                          (reverse_acc right rewrite_target)))
                      (trans
                        (forall-elim
                          (forall-elim
                            (known reverse_acc_append)
                            right)
                          left_reversed_acc)
                        (rewrite
                          (symm
                            (trans
                              (eval-to
                                (reverse left)
                                (reverse_acc left nil))
                              (assume left_reversed_acc_proof)))
                          (eval-to
                            (append (reverse right) left_reversed_acc)
                            (append (reverse right) left_reversed_acc))
                          rewrite_target
                          (computes-to
                            (append (reverse right) left_reversed_acc)
                            (append (reverse right) rewrite_target)))))))))))))))

(theorem snoc_computes_to_list
  (forall list (is-list list)
    (forall value (is-value value)
      (computes-to-list result (snoc list value))))
  (proof
    (list-induction list
      (forall value (is-value value)
        (computes-to-list result (snoc list value)))
      (forall-intro value (is-value value)
        (exists-intro result (is-list result)
          (computes-to (snoc nil value) result)
          (cons value nil)
          (eval-to
            (snoc nil value)
            (cons value nil))))
      head
      tail
      induction_hypothesis
      (forall-intro value (is-value value)
        (exists-elim
          (forall-elim
            (assume induction_hypothesis)
            value)
          tail_result
          tail_result_proof
          (exists-intro result (is-list result)
            (computes-to (snoc (cons head tail) value) result)
            (cons head tail_result)
            (rewrite
              (assume tail_result_proof)
              (eval-same
                (snoc (cons head tail) value)
                (cons head (snoc tail value)))
              rewrite_target
              (computes-to
                (snoc (cons head tail) value)
                (cons head rewrite_target)))))))))

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
