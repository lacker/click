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

(theorem if_true
  (forall then
    (forall else
      (computes-to
        (if (quote :true) then else)
        then)))
  (by
    (intro then)
    (intro else)
    (eval)))

(theorem if_false
  (forall then
    (forall else
      (computes-to
        (if (quote :false) then else)
        else)))
  (by
    (intro then)
    (intro else)
    (eval)))

(theorem if_condition_true
  (forall condition
    (forall then
      (forall else
        (implies
          (computes-to condition (quote :true))
          (computes-to
            (if condition then else)
            then)))))
  (by
    (intro condition)
    (intro then)
    (intro else)
    (rewrite else)
    (eval)))

(theorem if_condition_false
  (forall condition
    (forall then
      (forall else
        (implies
          (computes-to condition (quote :false))
          (computes-to
            (if condition then else)
            else)))))
  (by
    (intro condition)
    (intro then)
    (intro else)
    (rewrite else)
    (eval)))

(theorem if_true_result_with_false_else
  (forall condition
    (forall then_branch
      (implies
        (computes-to
          (if condition then_branch (quote :false))
          (quote :true))
        (and
          (computes-to condition (quote :true))
          (computes-to then_branch (quote :true))))))
  (proof
    (forall-intro condition
      (forall-intro then_branch
        (implies-intro if_is_true
          (computes-to
            (if condition then_branch (quote :false))
            (quote :true))
          (and-intro
            (if-true-condition (assume if_is_true))
            (if-true-then (assume if_is_true))))))))

(theorem if_true_result_with_error_then
  (forall condition
    (forall else_branch
      (implies
        (computes-to
          (if condition (error 0) else_branch)
          (quote :true))
        (and
          (computes-to condition (quote :false))
          (computes-to else_branch (quote :true))))))
  (proof
    (forall-intro condition
      (forall-intro else_branch
        (implies-intro if_is_true
          (computes-to
            (if condition (error 0) else_branch)
            (quote :true))
          (and-intro
            (if-effect-then-condition-false (assume if_is_true))
            (if-effect-then-else (assume if_is_true))))))))

(theorem if_true_result_with_false_then
  (forall condition
    (forall else_branch
      (implies
        (computes-to
          (if condition (quote :false) else_branch)
          (quote :true))
        (and
          (computes-to condition (quote :false))
          (computes-to else_branch (quote :true))))))
  (by
    (intro condition)
    (intro else_branch)
    (have condition_is_bool
      (is-bool condition)
      (proof
        (if-value-condition-bool (assume else_branch))))
    (or-elim condition_is_bool
      condition_true
      (by
        (have impossible_eq
          (computes-to (quote :false) (quote :true))
          (by
            (calc
              (quote :false)
              (==
                (if condition (quote :false) else_branch)
                (by
                  (rewrite condition_true)
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact else_branch)))))
          (by
            (exact
              (absurd-elim
                (distinct-outcomes impossible_eq)
                (and
                  (computes-to condition (quote :false))
                  (computes-to else_branch (quote :true))))))))
      condition_false
      (by
        (split
          (by
            (exact condition_false))
          (by
            (calc
              else_branch
              (==
                (if condition (quote :false) else_branch)
                (by
                  (rewrite condition_false)
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact else_branch))))))))))

(theorem symbol_eq_unit_unit
  (computes-to
    (symbol-eq (quote unit) (quote unit))
    (quote :true))
  (by
    (eval)))

(theorem symbol_eq_true_false
  (computes-to
    (symbol-eq (quote :true) (quote :false))
    (quote :false))
  (by
    (eval)))

(theorem symbol_eq_true
  (forall left
    (forall right
      (implies
        (computes-to
          (symbol-eq left right)
          (quote :true))
        (computes-to left right))))
  (proof
    (forall-intro left
      (forall-intro right
        (implies-intro symbol_eq_is_true
          (computes-to
            (symbol-eq left right)
            (quote :true))
          (symbol-eq-true (assume symbol_eq_is_true)))))))

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
                  (rewrite tail_result_proof)
                  (eval))))))))))

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
                  (rewrite mapped_head_proof)
                  (eval)))
              (==
                (cons mapped_head mapped_tail)
                (by
                  (rewrite mapped_tail_proof)
                  (eval))))))))))

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
                  (rewrite mapped_head_proof)
                  (eval)))
              (==
                (append mapped_head mapped_tail)
                (by
                  (rewrite mapped_tail_proof)
                  (eval)))
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
                  (rewrite tail_result_proof)
                  (eval)))
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
                  (rewrite folded_initial_proof)
                  (eval)))
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
                      (rewrite zipped_head_proof)
                      (eval)))
                  (==
                    (cons zipped_head zipped_tail)
                    (by
                      (rewrite zipped_tail_proof)
                      (eval))))))))))))

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
                      (rewrite filtered_tail_proof)
                      (eval)))))))
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

(theorem is_symbol_true_implies_is_lambda_false
  (forall value
    (implies
      (computes-to (is-symbol value) (quote :true))
      (computes-to (is-lambda value) (quote :false))))
  (proof
    (forall-intro value
      (implies-intro value_is_symbol
        (computes-to (is-symbol value) (quote :true))
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
                  (quote :symbol))
                (trans
                  (eval-same
                    (symbol-eq (value-kind value) (quote :symbol))
                    (is-symbol value))
                  (assume value_is_symbol))))
            (eval-to
              (symbol-eq (quote :symbol) (quote :lambda))
              (quote :false))
            kind
            (computes-to
              (symbol-eq kind (quote :lambda))
              (quote :false))))))))

(theorem value_eq_true_implies_not_lambdas
  (forall left (is-value left)
    (forall right (is-value right)
      (implies
        (computes-to (value-eq left right) (quote :true))
        (and
          (computes-to (is-lambda left) (quote :false))
          (computes-to (is-lambda right) (quote :false))))))
  (by
    (intro left)
    (intro right)
    (intro values_equal)
    (have top_if_true
      (computes-to
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
                      (quote :false))))))))
        (quote :true))
      (by
        (calc
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
                        (quote :false))))))))
          (==
            (value-eq left right)
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact values_equal)))))
      (by
        (specialize left_branch_parts if_true_result_with_error_then
          (is-lambda left)
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
                      (quote :false))))))))
        (cases left_branch_parts left_not_lambda after_left_guard)
        (specialize right_branch_parts if_true_result_with_error_then
          (is-lambda right)
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
                    (quote :false)))))))
        (cases right_branch_parts right_not_lambda after_right_guard)
        (split
          (by
            (exact left_not_lambda))
          (by
            (exact right_not_lambda)))))))

(theorem value_non_symbol_non_lambda_is_list
  (forall value (is-value value)
    (implies
      (computes-to (is-symbol value) (quote :false))
      (implies
        (computes-to (is-lambda value) (quote :false))
        (is-list value))))
  (proof
    (forall-intro value
      (implies-intro value_is_value
        (is-value value)
        (implies-intro value_not_symbol
          (computes-to (is-symbol value) (quote :false))
          (implies-intro value_not_lambda
            (computes-to (is-lambda value) (quote :false))
            (value-non-symbol-non-lambda-is-list
              (assume value_is_value)
              (assume value_not_symbol)
              (assume value_not_lambda))))))))

(theorem value_eq_left_non_symbol_true_implies_lists
  (forall left (is-value left)
    (implies
      (computes-to (is-symbol left) (quote :false))
      (forall right (is-value right)
        (implies
          (computes-to (value-eq left right) (quote :true))
          (and
            (is-list left)
            (is-list right))))))
  (by
    (intro left)
    (intro left_not_symbol)
    (intro right)
    (intro values_equal)
    (specialize not_lambdas value_eq_true_implies_not_lambdas left right)
    (cases not_lambdas left_not_lambda right_not_lambda)
    (specialize left_is_list value_non_symbol_non_lambda_is_list left)
    (have right_symbol_branch_true
      (computes-to
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
                (quote :false)))))
        (quote :true))
      (by
        (calc
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
                  (quote :false)))))
          (==
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
                      (quote :false))))))
            (by
              (rewrite left_not_symbol)
              (eval)))
          (==
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
                        (quote :false)))))))
            (by
              (rewrite right_not_lambda)
              (eval)))
          (==
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
                          (quote :false))))))))
            (by
              (rewrite left_not_lambda)
              (eval)))
          (==
            (value-eq left right)
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact values_equal))))))
    (specialize right_branch_parts if_true_result_with_false_then
      (is-symbol right)
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
            (quote :false)))))
    (cases right_branch_parts right_not_symbol list_branch_true)
    (specialize right_is_list value_non_symbol_non_lambda_is_list right)
    (split
      (by
        (exact left_is_list))
      (by
        (exact right_is_list)))))

(theorem value_eq_left_symbol_true
  (forall left (is-value left)
    (implies
      (computes-to (is-symbol left) (quote :true))
      (forall right (is-value right)
        (implies
          (computes-to (is-lambda right) (quote :false))
          (implies
            (computes-to (value-eq left right) (quote :true))
            (computes-to left right))))))
  (by
    (intro left)
    (intro left_is_symbol)
    (intro right)
    (intro right_is_not_lambda)
    (intro values_equal)
    (specialize left_is_not_lambda is_symbol_true_implies_is_lambda_false left)
    (have symbols_equal
      (computes-to
        (symbol-eq left right)
        (quote :true))
      (by
        (calc
          (symbol-eq left right)
          (==
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
                      (quote :false))))))
            (by
              (rewrite left_is_symbol)
              (eval)))
          (==
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
                        (quote :false)))))))
            (by
              (rewrite right_is_not_lambda)
              (eval)))
          (==
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
                          (quote :false))))))))
            (by
              (rewrite left_is_not_lambda)
              (eval)))
          (==
            (value-eq left right)
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact values_equal)))))
      (by
        (specialize result symbol_eq_true left right)
        (exact result)))))

(theorem value_eq_left_symbol_sound
  (forall left (is-value left)
    (implies
      (computes-to (is-symbol left) (quote :true))
      (forall right (is-value right)
        (implies
          (computes-to (value-eq left right) (quote :true))
          (computes-to left right)))))
  (by
    (intro left)
    (intro left_is_symbol)
    (intro right)
    (intro values_equal)
    (specialize not_lambdas value_eq_true_implies_not_lambdas left right)
    (cases not_lambdas left_not_lambda right_not_lambda)
    (specialize result value_eq_left_symbol_true left right)
    (exact result)))

(theorem value_eq_cons_true_elim
  (forall left_head (is-value left_head)
    (forall left_tail (is-list left_tail)
      (forall right_head (is-value right_head)
        (forall right_tail (is-list right_tail)
          (implies
            (computes-to
              (value-eq
                (cons left_head left_tail)
                (cons right_head right_tail))
              (quote :true))
            (and
              (computes-to
                (value-eq left_head right_head)
                (quote :true))
              (computes-to
                (value-eq left_tail right_tail)
                (quote :true))))))))
  (by
    (intro left_head)
    (intro left_tail)
    (intro right_head)
    (intro right_tail)
    (intro conses_equal)
    (specialize cons_step value_eq_cons left_head left_tail right_head right_tail)
    (have branch_true
      (computes-to
        (if
          (value-eq
            (head (cons left_head left_tail))
            (head (cons right_head right_tail)))
          (value-eq
            (tail (cons left_head left_tail))
            (tail (cons right_head right_tail)))
          (quote :false))
        (quote :true))
      (by
        (calc
          (if
            (value-eq
              (head (cons left_head left_tail))
              (head (cons right_head right_tail)))
            (value-eq
              (tail (cons left_head left_tail))
              (tail (cons right_head right_tail)))
            (quote :false))
          (==
            (value-eq
              (cons left_head left_tail)
              (cons right_head right_tail))
            (by
              (exact (symm cons_step))))
          (==
            (quote :true)
            (by
              (exact conses_equal)))))
      (by
        (specialize branch_parts if_true_result_with_false_else
          (value-eq
            (head (cons left_head left_tail))
            (head (cons right_head right_tail)))
          (value-eq
            (tail (cons left_head left_tail))
            (tail (cons right_head right_tail))))
        (cases branch_parts head_equal tail_equal)
        (split
          (by
            (calc
              (value-eq left_head right_head)
              (==
                (value-eq
                  (head (cons left_head left_tail))
                  (head (cons right_head right_tail)))
                (by
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact head_equal)))))
          (by
            (calc
              (value-eq left_tail right_tail)
              (==
                (value-eq
                  (tail (cons left_head left_tail))
                  (tail (cons right_head right_tail)))
                (by
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact tail_equal))))))))))

(theorem cons_congr
  (forall left_head
    (forall left_tail
      (forall right_head
        (equal left_head right_head)
        (forall right_tail
          (equal left_tail right_tail)
          (equal
            (cons left_head left_tail)
            (cons right_head right_tail))))))
  (by
    (intro left_head)
    (intro left_tail)
    (intro right_head)
    (intro right_tail)
    (rewrite right_head)
    (rewrite right_tail)
    (eval)))

(theorem value_eq_sound
  (forall left (is-value left)
    (forall right (is-value right)
      (implies
        (computes-to (value-eq left right) (quote :true))
        (computes-to left right))))
  (by
    (value-induction left
      left_is_symbol
      (by
        (intro right)
        (intro values_equal)
        (specialize result value_eq_left_symbol_sound left right)
        (exact result))
      left_is_lambda
      (by
        (intro right)
        (intro values_equal)
        (specialize not_lambdas value_eq_true_implies_not_lambdas left right)
        (cases not_lambdas left_not_lambda right_not_lambda)
        (have impossible_eq
          (computes-to (quote :true) (quote :false))
          (by
            (calc
              (quote :true)
              (==
                (is-lambda left)
                (by
                  (exact (symm left_is_lambda))))
              (==
                (quote :false)
                (by
                  (exact left_not_lambda)))))
          (by
            (exact
              (absurd-elim
                (distinct-outcomes impossible_eq)
                (computes-to left right))))))
      (by
        (value-induction right
          right_is_symbol
          (by
            (intro values_equal)
            (have nil_not_symbol
              (computes-to (is-symbol nil) (quote :false))
              (by
                (eval)))
            (specialize lists value_eq_left_non_symbol_true_implies_lists nil right)
            (cases lists nil_is_list right_is_list)
            (have right_not_symbol
              (computes-to (is-symbol right) (quote :false))
              (by
                (eval)))
            (have impossible_eq
              (computes-to (quote :true) (quote :false))
              (by
                (calc
                  (quote :true)
                  (==
                    (is-symbol right)
                    (by
                      (exact (symm right_is_symbol))))
                  (==
                    (quote :false)
                    (by
                      (exact right_not_symbol)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to nil right))))))
          right_is_lambda
          (by
            (intro values_equal)
            (specialize not_lambdas value_eq_true_implies_not_lambdas nil right)
            (cases not_lambdas nil_not_lambda right_not_lambda)
            (have impossible_eq
              (computes-to (quote :true) (quote :false))
              (by
                (calc
                  (quote :true)
                  (==
                    (is-lambda right)
                    (by
                      (exact (symm right_is_lambda))))
                  (==
                    (quote :false)
                    (by
                      (exact right_not_lambda)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to nil right))))))
          (by
            (intro values_equal)
            (eval))
          right_head
          right_tail
          right_head_sound
          right_tail_sound
          (by
            (intro values_equal)
            (specialize nil_cons_false value_eq_nil_cons right_head right_tail)
            (have impossible_eq
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (value-eq nil (cons right_head right_tail))
                    (by
                      (exact (symm nil_cons_false))))
                  (==
                    (quote :true)
                    (by
                      (exact values_equal)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to nil (cons right_head right_tail)))))))))
      left_head
      left_tail
      left_head_sound
      left_tail_sound
      (by
        (value-induction right
          right_is_symbol
          (by
            (intro values_equal)
            (have left_not_symbol
              (computes-to (is-symbol (cons left_head left_tail)) (quote :false))
              (by
                (eval)))
            (specialize lists value_eq_left_non_symbol_true_implies_lists
              (cons left_head left_tail)
              right)
            (cases lists left_is_list right_is_list)
            (have right_not_symbol
              (computes-to (is-symbol right) (quote :false))
              (by
                (eval)))
            (have impossible_eq
              (computes-to (quote :true) (quote :false))
              (by
                (calc
                  (quote :true)
                  (==
                    (is-symbol right)
                    (by
                      (exact (symm right_is_symbol))))
                  (==
                    (quote :false)
                    (by
                      (exact right_not_symbol)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to (cons left_head left_tail) right))))))
          right_is_lambda
          (by
            (intro values_equal)
            (specialize not_lambdas value_eq_true_implies_not_lambdas
              (cons left_head left_tail)
              right)
            (cases not_lambdas left_not_lambda right_not_lambda)
            (have impossible_eq
              (computes-to (quote :true) (quote :false))
              (by
                (calc
                  (quote :true)
                  (==
                    (is-lambda right)
                    (by
                      (exact (symm right_is_lambda))))
                  (==
                    (quote :false)
                    (by
                      (exact right_not_lambda)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to (cons left_head left_tail) right))))))
          (by
            (intro values_equal)
            (specialize cons_nil_false value_eq_cons_nil left_head left_tail)
            (have impossible_eq
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (value-eq (cons left_head left_tail) nil)
                    (by
                      (exact (symm cons_nil_false))))
                  (==
                    (quote :true)
                    (by
                      (exact values_equal)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to (cons left_head left_tail) nil))))))
          right_head
          right_tail
          right_head_sound
          right_tail_sound
          (by
            (intro values_equal)
            (specialize parts value_eq_cons_true_elim
              left_head
              left_tail
              right_head
              right_tail)
            (cases parts heads_equal tails_equal)
            (specialize head_equal left_head_sound right_head)
            (specialize tail_equal left_tail_sound right_tail)
            (specialize result cons_congr left_head left_tail right_head right_tail)
            (exact result)))))))

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
              (rewrite (symm middle_right_proof))
              (eval)))))
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
              (rewrite (append_cons head tail middle))
              (eval)))
          (==
            (append (cons head tail_middle) right)
            (by
              (rewrite tail_middle_proof)
              (eval)))
          (==
            (cons head (append tail_middle right))
            (by
              (exact append_cons head tail_middle right)))
          (==
            (cons head (append (append tail middle) right))
            (by
              (rewrite (symm tail_middle_proof))
              (eval)))
          (==
            (cons head (append tail (append middle right)))
            (by
              (rewrite (induction_hypothesis middle right))
              (eval)))
          (==
            (cons head (append tail middle_right))
            (by
              (rewrite middle_right_proof)
              (eval)))
          (==
            (append (cons head tail) middle_right)
            (by
              (exact (symm (append_cons head tail middle_right)))))
          (==
            (append (cons head tail) (append middle right))
            (by
              (rewrite (symm middle_right_proof))
              (eval))))))))

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
                  (rewrite tail_reversed_proof)
                  (eval)))))
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
                  (rewrite tail_reversed_proof)
                  (eval)))
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
                  (rewrite (symm reverse_cons_step))
                  (eval))))))))))

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
              (rewrite (symm acc_reversed_proof))
              (eval)))))
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
              (rewrite (append_singleton head tail))
              (eval)))
          (==
            (append (reverse acc) (cons head tail))
            (by
              (rewrite (symm acc_reversed_proof))
              (eval))))))))

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
          (rewrite reverse_nil)
          (eval)))
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
              (rewrite (append_cons head tail right))
              (eval)))
          (==
            (reverse_acc (cons head tail_right) acc)
            (by
              (rewrite tail_right_proof)
              (eval)))
          (==
            (reverse_acc tail_right (cons head acc))
            (by
              (eval)))
          (==
            (reverse_acc (append tail right) (cons head acc))
            (by
              (rewrite (symm tail_right_proof))
              (eval)))
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
              (rewrite appended_proof)
              (eval)))
          (==
            (reverse_acc appended nil)
            (by
              (eval)))
          (==
            (reverse_acc (append left right) nil)
            (by
              (rewrite (symm appended_proof))
              (eval)))
          (==
            (reverse_acc right (reverse_acc left nil))
            (by
              (exact reverse_acc_of_append left right nil)))
          (==
            (reverse_acc right left_reversed_acc)
            (by
              (rewrite left_reversed_acc_proof)
              (eval)))
          (==
            (append (reverse right) left_reversed_acc)
            (by
              (exact reverse_acc_append right left_reversed_acc)))
          (==
            (append (reverse right) (reverse left))
            (by
              (rewrite (symm reverse_left_step))
              (eval))))))))

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
                  (rewrite tail_result_proof)
                  (eval))))))))))

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
