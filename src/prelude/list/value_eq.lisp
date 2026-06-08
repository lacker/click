; Value equality theorems for the standard prelude.

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

(theorem value_kind_symbol_implies_is_symbol
  (forall value
    (implies
      (computes-to
        (symbol-eq (value-kind value) (quote :symbol))
        (quote :true))
      (computes-to (is-symbol value) (quote :true))))
  (proof
    (forall-intro value
      (implies-intro value_kind_symbol
        (computes-to
          (symbol-eq (value-kind value) (quote :symbol))
          (quote :true))
        (trans
          (eval-same
            (is-symbol value)
            (symbol-eq (value-kind value) (quote :symbol)))
          (assume value_kind_symbol))))))

(theorem value_kind_lambda_implies_is_lambda
  (forall value
    (implies
      (computes-to
        (symbol-eq (value-kind value) (quote :lambda))
        (quote :true))
      (computes-to (is-lambda value) (quote :true))))
  (proof
    (forall-intro value
      (implies-intro value_kind_lambda
        (computes-to
          (symbol-eq (value-kind value) (quote :lambda))
          (quote :true))
        (trans
          (eval-same
            (is-lambda value)
            (symbol-eq (value-kind value) (quote :lambda)))
          (assume value_kind_lambda))))))

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

(theorem value_eq_comparable_symbol
  (forall value (is-value value)
    (implies
      (computes-to (is-symbol value) (quote :true))
      (computes-to (value-eq-comparable value) (quote :true))))
  (by
    (intro value)
    (intro value_is_symbol)
    (specialize value_not_lambda is_symbol_true_implies_is_lambda_false value)
    (simp only value_not_lambda value_is_symbol)))

(theorem value_eq_comparable_nil
  (computes-to (value-eq-comparable nil) (quote :true))
  (by
    (eval)))

(theorem value_eq_comparable_cons
  (forall head (is-value head)
    (forall tail (is-list tail)
      (implies
        (computes-to (value-eq-comparable head) (quote :true))
        (implies
          (computes-to (value-eq-comparable tail) (quote :true))
          (computes-to
            (value-eq-comparable (cons head tail))
            (quote :true))))))
  (by
    (intro head)
    (intro tail)
    (intro head_comparable)
    (intro tail_comparable)
    (simp only head_comparable tail_comparable)))

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
              (simpa only left_not_symbol)))
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
              (simpa only right_not_lambda)))
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
              (simpa only left_not_lambda)))
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
              (simpa only left_is_symbol)))
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
              (simpa only right_is_not_lambda)))
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
              (simpa only left_is_not_lambda)))
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

(theorem value_eq_refl
  (forall value (is-value value)
    (implies
      (computes-to (value-eq-comparable value) (quote :true))
      (computes-to (value-eq value value) (quote :true))))
  (by
    (value-induction value
      value_is_symbol
      (by
        (intro value_comparable)
        (have value_is_symbol_result
          (computes-to (is-symbol value) (quote :true))
          (by
            (calc
              (is-symbol value)
              (==
                (symbol-eq (value-kind value) (quote :symbol))
                (by
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact value_is_symbol))))))
        (specialize value_not_lambda is_symbol_true_implies_is_lambda_false value)
        (have symbols_equal
          (computes-to (symbol-eq value value) (quote :true))
          (by
            (eval)))
        (calc
          (value-eq value value)
          (==
            (if
              (is-lambda value)
              (error 0)
              (if
                (is-lambda value)
                (error 0)
                (if
                  (is-symbol value)
                  (symbol-eq value value)
                  (if
                    (is-symbol value)
                    (quote :false)
                    (list-case value
                      (list-case value
                        (quote :true)
                        right_cell
                        (quote :false))
                      left_cell
                      (list-case value
                        (quote :false)
                        right_cell
                        (if
                          (value-eq (head left_cell) (head right_cell))
                          (value-eq (tail left_cell) (tail right_cell))
                          (quote :false))))))))
            (by
              (eval)))
          (==
            (if
              (is-lambda value)
              (error 0)
              (if
                (is-symbol value)
                (symbol-eq value value)
                (if
                  (is-symbol value)
                  (quote :false)
                  (list-case value
                    (list-case value
                      (quote :true)
                      right_cell
                      (quote :false))
                    left_cell
                    (list-case value
                      (quote :false)
                      right_cell
                      (if
                        (value-eq (head left_cell) (head right_cell))
                        (value-eq (tail left_cell) (tail right_cell))
                        (quote :false)))))))
            (by
              (simpa only value_not_lambda)))
          (==
            (if
              (is-symbol value)
              (symbol-eq value value)
              (if
                (is-symbol value)
                (quote :false)
                (list-case value
                  (list-case value
                    (quote :true)
                    right_cell
                    (quote :false))
                  left_cell
                  (list-case value
                    (quote :false)
                    right_cell
                    (if
                      (value-eq (head left_cell) (head right_cell))
                      (value-eq (tail left_cell) (tail right_cell))
                      (quote :false))))))
            (by
              (simpa only value_not_lambda)))
          (==
            (symbol-eq value value)
            (by
              (simpa only value_is_symbol_result)))
          (==
            (quote :true)
            (by
              (exact symbols_equal)))))
      value_is_lambda
      (by
        (intro value_comparable)
        (have value_is_lambda_result
          (computes-to (is-lambda value) (quote :true))
          (by
            (calc
              (is-lambda value)
              (==
                (symbol-eq (value-kind value) (quote :lambda))
                (by
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact value_is_lambda))))))
        (have comparable_false
          (computes-to (value-eq-comparable value) (quote :false))
          (by
            (calc
              (value-eq-comparable value)
              (==
                (if
                  (is-lambda value)
                  (quote :false)
                  (if
                    (is-symbol value)
                    (quote :true)
                    (list-case value
                      (quote :true)
                      cell
                      (if
                        (value-eq-comparable (head cell))
                        (value-eq-comparable (tail cell))
                        (quote :false)))))
                (by
                  (eval)))
              (==
                (quote :false)
                (by
                  (simpa only value_is_lambda_result))))))
        (have impossible_eq
          (computes-to (quote :false) (quote :true))
          (by
            (calc
              (quote :false)
              (==
                (value-eq-comparable value)
                (by
                  (exact (symm comparable_false))))
              (==
                (quote :true)
                (by
                  (exact value_comparable)))))
          (by
            (exact
              (absurd-elim
                (distinct-outcomes impossible_eq)
                (computes-to (value-eq value value) (quote :true)))))))
      (by
        (intro value_comparable)
        (eval))
      head
      tail
      head_refl
      tail_refl
      (by
        (intro value_comparable)
        (have branch_true
          (computes-to
            (if
              (value-eq-comparable head)
              (value-eq-comparable (tail (cons head tail)))
              (quote :false))
            (quote :true))
          (by
            (calc
              (if
                (value-eq-comparable head)
                (value-eq-comparable (tail (cons head tail)))
                (quote :false))
              (==
                (value-eq-comparable (cons head tail))
                (by
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact value_comparable)))))
          (by
            (specialize comparable_parts if_true_result_with_false_else
              (value-eq-comparable head)
              (value-eq-comparable (tail (cons head tail))))
            (cases comparable_parts head_comparable tail_comparable_through_cell)
            (have tail_comparable
              (computes-to (value-eq-comparable tail) (quote :true))
              (by
                (calc
                  (value-eq-comparable tail)
                  (==
                    (value-eq-comparable (tail (cons head tail)))
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact tail_comparable_through_cell))))))
            (specialize head_equal head_refl)
            (specialize tail_equal tail_refl)
            (have tail_equal_through_cell
              (computes-to
                (value-eq
                  (tail (cons head tail))
                  (tail (cons head tail)))
                (quote :true))
              (by
                (calc
                  (value-eq
                    (tail (cons head tail))
                    (tail (cons head tail)))
                  (==
                    (value-eq tail tail)
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact tail_equal))))))
            (calc
              (value-eq (cons head tail) (cons head tail))
              (==
                (if
                  (value-eq
                    (head (cons head tail))
                    (head (cons head tail)))
                  (value-eq
                    (tail (cons head tail))
                    (tail (cons head tail)))
                  (quote :false))
                (by
                  (apply value_eq_cons head tail head tail)))
              (==
                (if
                  (value-eq head head)
                  (value-eq
                    (tail (cons head tail))
                    (tail (cons head tail)))
                  (quote :false))
                (by
                  (eval)))
              (==
                (quote :true)
                (by
                  (rewrite head_equal)
                  (rewrite tail_equal_through_cell)
                  (eval))))))))))

(theorem value_eq_true_implies_comparable_left
  (forall left (is-value left)
    (forall right (is-value right)
      (implies
        (computes-to (value-eq left right) (quote :true))
        (computes-to (value-eq-comparable left) (quote :true)))))
  (by
    (value-induction left
      left_is_symbol
      (by
        (intro right)
        (intro values_equal)
        (specialize left_is_symbol_result value_kind_symbol_implies_is_symbol left)
        (specialize result value_eq_comparable_symbol left)
        (exact result))
      left_is_lambda
      (by
        (intro right)
        (intro values_equal)
        (specialize not_lambdas value_eq_true_implies_not_lambdas left right)
        (cases not_lambdas left_not_lambda right_not_lambda)
        (specialize left_is_lambda_result value_kind_lambda_implies_is_lambda left)
        (have impossible_eq
          (computes-to (quote :true) (quote :false))
          (by
            (calc
              (quote :true)
              (==
                (is-lambda left)
                (by
                  (exact (symm left_is_lambda_result))))
              (==
                (quote :false)
                (by
                  (exact left_not_lambda)))))
          (by
            (exact
              (absurd-elim
                (distinct-outcomes impossible_eq)
                (computes-to (value-eq-comparable left) (quote :true)))))))
      (by
        (intro right)
        (intro values_equal)
        (exact value_eq_comparable_nil))
      left_head
      left_tail
      left_head_comparable
      left_tail_comparable
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
            (specialize right_is_symbol_result value_kind_symbol_implies_is_symbol right)
            (have impossible_eq
              (computes-to (quote :true) (quote :false))
              (by
                (calc
                  (quote :true)
                  (==
                    (is-symbol right)
                    (by
                      (exact (symm right_is_symbol_result))))
                  (==
                    (quote :false)
                    (by
                      (exact right_not_symbol)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to
                      (value-eq-comparable (cons left_head left_tail))
                      (quote :true)))))))
          right_is_lambda
          (by
            (intro values_equal)
            (specialize not_lambdas value_eq_true_implies_not_lambdas
              (cons left_head left_tail)
              right)
            (cases not_lambdas left_not_lambda right_not_lambda)
            (specialize right_is_lambda_result value_kind_lambda_implies_is_lambda right)
            (have impossible_eq
              (computes-to (quote :true) (quote :false))
              (by
                (calc
                  (quote :true)
                  (==
                    (is-lambda right)
                    (by
                      (exact (symm right_is_lambda_result))))
                  (==
                    (quote :false)
                    (by
                      (exact right_not_lambda)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to
                      (value-eq-comparable (cons left_head left_tail))
                      (quote :true)))))))
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
                    (computes-to
                      (value-eq-comparable (cons left_head left_tail))
                      (quote :true)))))))
          right_head
          right_tail
          right_head_comparable
          right_tail_comparable
          (by
            (intro values_equal)
            (specialize parts value_eq_cons_true_elim
              left_head
              left_tail
              right_head
              right_tail)
            (cases parts heads_equal tails_equal)
            (specialize head_comparable left_head_comparable right_head)
            (specialize tail_comparable left_tail_comparable right_tail)
            (specialize result value_eq_comparable_cons left_head left_tail)
            (exact result)))))))

(theorem value_eq_true_implies_comparable_right
  (forall left (is-value left)
    (forall right (is-value right)
      (implies
        (computes-to (value-eq left right) (quote :true))
        (computes-to (value-eq-comparable right) (quote :true)))))
  (by
    (intro left)
    (intro right)
    (intro values_equal)
    (specialize left_comparable value_eq_true_implies_comparable_left left right)
    (specialize values_same value_eq_sound left right)
    (simp only (symm values_same) left_comparable)))

(theorem value_eq_symm
  (forall left (is-value left)
    (forall right (is-value right)
      (implies
        (computes-to (value-eq left right) (quote :true))
        (computes-to (value-eq right left) (quote :true)))))
  (by
    (intro left)
    (intro right)
    (intro values_equal)
    (specialize right_comparable value_eq_true_implies_comparable_right left right)
    (specialize values_same value_eq_sound left right)
    (specialize right_refl value_eq_refl right)
    (simp only values_same right_refl)))
