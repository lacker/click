; Nat multiplication theorems for the standard prelude.

(theorem mul_zero_left
  (forall right (is-list right)
    (computes-to (mul zero right) zero))
  (by
    (intro right)
    (eval)))

(theorem is_zero_mul_zero_left
  (forall right (is-list right)
    (computes-to
      (is-zero (mul zero right))
      (quote :true)))
  (by
    (intro right)
    (eval)))

(theorem mul_cons
  (forall head (is-value head)
    (forall tail (is-list tail)
      (forall right (is-list right)
        (computes-to
          (mul (cons head tail) right)
          (add right (mul tail right))))))
  (by
    (intro head)
    (intro tail)
    (intro right)
    (eval)))

(theorem mul_computes_to_list
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to-list result (mul left right))))
  (by
    (list-induction left
      (by
        (intro right)
        (exists nil
          (by
            (eval))))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (specialize tail_product_exists induction_hypothesis right)
        (obtain tail_product tail_product_proof tail_product_exists)
        (obtain product product_proof
          (add_computes_to_list right tail_product))
        (exists product
          (by
            (calc
              (mul (cons head tail) right)
              (==
                (add right (mul tail right))
                (by
                  (exact mul_cons head tail right)))
              (==
                (add right tail_product)
                (by
                  (simpa only tail_product_proof)))
              (==
                product
                (by
                  (exact product_proof))))))))))

(theorem nat_le_mul_right_mono
  (forall left (is-list left)
    (forall right (is-list right)
      (forall factor (is-list factor)
        (implies
          (computes-to (nat-le left right) (quote :true))
          (computes-to
            (nat-le (mul left factor) (mul right factor))
            (quote :true))))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro factor)
        (intro left_le_right)
        (obtain product product_proof
          (mul_computes_to_list right factor))
        (calc
          (nat-le (mul nil factor) (mul right factor))
          (==
            (nat-le nil product)
            (by
              (simpa only product_proof)))
          (==
            (quote :true)
            (by
              (eval)))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro factor)
            (intro left_le_right)
            (have impossible_eq
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (nat-le (cons left_head left_tail) nil)
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact left_le_right)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to
                      (nat-le
                        (mul (cons left_head left_tail) factor)
                        (mul nil factor))
                      (quote :true)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro factor)
            (intro left_le_right)
            (have tail_le_right
              (computes-to (nat-le left_tail right_tail) (quote :true))
              (by
                (calc
                  (nat-le left_tail right_tail)
                  (==
                    (nat-le (cons left_head left_tail) (cons right_head right_tail))
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact left_le_right)))))
              (by
                (obtain left_product left_product_proof
                  (mul_computes_to_list left_tail factor))
                (obtain right_product right_product_proof
                  (mul_computes_to_list right_tail factor))
                (specialize tail_mono induction_hypothesis right_tail factor)
                (have tail_products_le
                  (computes-to (nat-le left_product right_product) (quote :true))
                  (by
                    (calc
                      (nat-le left_product right_product)
                      (==
                        (nat-le (mul left_tail factor) right_product)
                        (by
                          (simpa only (symm left_product_proof))))
                      (==
                        (nat-le (mul left_tail factor) (mul right_tail factor))
                        (by
                          (simpa only (symm right_product_proof))))
                      (==
                        (quote :true)
                        (by
                          (exact tail_mono)))))
                  (by
                    (specialize add_mono nat_le_add_left_mono left_product right_product factor)
                    (calc
                      (nat-le
                        (mul (cons left_head left_tail) factor)
                        (mul (cons right_head right_tail) factor))
                      (==
                        (nat-le
                          (add factor (mul left_tail factor))
                          (mul (cons right_head right_tail) factor))
                        (by
                          (simpa only (mul_cons left_head left_tail factor))))
                      (==
                        (nat-le
                          (add factor left_product)
                          (mul (cons right_head right_tail) factor))
                        (by
                          (simpa only left_product_proof)))
                      (==
                        (nat-le
                          (add factor left_product)
                          (add factor (mul right_tail factor)))
                        (by
                          (simpa only (mul_cons right_head right_tail factor))))
                      (==
                        (nat-le
                          (add factor left_product)
                          (add factor right_product))
                        (by
                          (simpa only right_product_proof)))
                      (==
                        (quote :true)
                        (by
                          (exact add_mono)))))))))))))
)

(theorem nat_lt_mul_right_mono
  (forall left (is-list left)
    (forall right (is-list right)
      (forall factor (is-list factor)
        (implies
          (computes-to (nat-lt left right) (quote :true))
          (implies
            (computes-to (nat-lt zero factor) (quote :true))
            (computes-to
              (nat-lt (mul left factor) (mul right factor))
              (quote :true)))))))
  (by
    (list-induction left
      (by
        (list-induction right
          (by
            (intro factor)
            (intro left_lt_right)
            (intro factor_positive)
            (have impossible_eq
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (nat-lt nil nil)
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact left_lt_right)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to
                      (nat-lt (mul nil factor) (mul nil factor))
                      (quote :true)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro factor)
            (intro left_lt_right)
            (intro factor_positive)
            (obtain right_product right_product_proof
              (mul_computes_to_list right_tail factor))
            (have factor_positive_nil
              (computes-to (nat-lt nil factor) (quote :true))
              (by
                (calc
                  (nat-lt nil factor)
                  (==
                    (nat-lt zero factor)
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact factor_positive)))))
              (by
                (specialize zero_lt_sum nat_lt_nil_left_add factor right_product)
                (calc
                  (nat-lt (mul nil factor) (mul (cons right_head right_tail) factor))
                  (==
                    (nat-lt nil (add factor (mul right_tail factor)))
                    (by
                      (simpa only (mul_cons right_head right_tail factor))))
                  (==
                    (nat-lt nil (add factor right_product))
                    (by
                      (simpa only right_product_proof)))
                  (==
                    (quote :true)
                    (by
                      (exact zero_lt_sum)))))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro factor)
            (intro left_lt_right)
            (intro factor_positive)
            (have impossible_eq
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (nat-lt (cons left_head left_tail) nil)
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact left_lt_right)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to
                      (nat-lt
                        (mul (cons left_head left_tail) factor)
                        (mul nil factor))
                      (quote :true)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro factor)
            (intro left_lt_right)
            (intro factor_positive)
            (have tail_lt_right
              (computes-to (nat-lt left_tail right_tail) (quote :true))
              (by
                (calc
                  (nat-lt left_tail right_tail)
                  (==
                    (nat-lt (cons left_head left_tail) (cons right_head right_tail))
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact left_lt_right)))))
              (by
                (obtain left_product left_product_proof
                  (mul_computes_to_list left_tail factor))
                (obtain right_product right_product_proof
                  (mul_computes_to_list right_tail factor))
                (specialize tail_mono induction_hypothesis right_tail factor)
                (have tail_products_lt
                  (computes-to (nat-lt left_product right_product) (quote :true))
                  (by
                    (calc
                      (nat-lt left_product right_product)
                      (==
                        (nat-lt (mul left_tail factor) right_product)
                        (by
                          (simpa only (symm left_product_proof))))
                      (==
                        (nat-lt (mul left_tail factor) (mul right_tail factor))
                        (by
                          (simpa only (symm right_product_proof))))
                      (==
                        (quote :true)
                        (by
                          (exact tail_mono)))))
                  (by
                    (specialize add_mono nat_lt_add_left_mono left_product right_product factor)
                    (calc
                      (nat-lt
                        (mul (cons left_head left_tail) factor)
                        (mul (cons right_head right_tail) factor))
                      (==
                        (nat-lt
                          (add factor (mul left_tail factor))
                          (mul (cons right_head right_tail) factor))
                        (by
                          (simpa only (mul_cons left_head left_tail factor))))
                      (==
                        (nat-lt
                          (add factor left_product)
                          (mul (cons right_head right_tail) factor))
                        (by
                          (simpa only left_product_proof)))
                      (==
                        (nat-lt
                          (add factor left_product)
                          (add factor (mul right_tail factor)))
                        (by
                          (simpa only (mul_cons right_head right_tail factor))))
                      (==
                        (nat-lt
                          (add factor left_product)
                          (add factor right_product))
                        (by
                          (simpa only right_product_proof)))
                      (==
                        (quote :true)
                        (by
                          (exact add_mono)))))))))))))
)

(theorem nat_le_mul_left_mono
  (forall left (is-list left)
    (forall right (is-list right)
      (forall factor (is-list factor)
        (implies
          (computes-to (nat-le left right) (quote :true))
          (computes-to
            (nat-le (mul factor left) (mul factor right))
            (quote :true))))))
  (by
    (intro left)
    (intro right)
    (list-induction factor
      (by
        (intro left_le_right)
        (eval))
      factor_head
      factor_tail
      induction_hypothesis
      (by
        (intro left_le_right)
        (obtain tail_left_product tail_left_product_proof
          (mul_computes_to_list factor_tail left))
        (obtain tail_right_product tail_right_product_proof
          (mul_computes_to_list factor_tail right))
        (specialize tail_mono induction_hypothesis)
        (have tail_products_le
          (computes-to
            (nat-le tail_left_product tail_right_product)
            (quote :true))
          (by
            (calc
              (nat-le tail_left_product tail_right_product)
              (==
                (nat-le (mul factor_tail left) tail_right_product)
                (by
                  (simpa only (symm tail_left_product_proof))))
              (==
                (nat-le (mul factor_tail left) (mul factor_tail right))
                (by
                  (simpa only (symm tail_right_product_proof))))
              (==
                (quote :true)
                (by
                  (exact tail_mono)))))
          (by
            (obtain left_total left_total_proof
              (add_computes_to_list left tail_left_product))
            (obtain middle_total middle_total_proof
              (add_computes_to_list right tail_left_product))
            (obtain right_total right_total_proof
              (add_computes_to_list right tail_right_product))
            (specialize first_mono nat_le_add_right_mono left right tail_left_product)
            (have left_total_le_middle_total
              (computes-to
                (nat-le left_total middle_total)
                (quote :true))
              (by
                (calc
                  (nat-le left_total middle_total)
                  (==
                    (nat-le (add left tail_left_product) middle_total)
                    (by
                      (simpa only (symm left_total_proof))))
                  (==
                    (nat-le (add left tail_left_product) (add right tail_left_product))
                    (by
                      (simpa only (symm middle_total_proof))))
                  (==
                    (quote :true)
                    (by
                      (exact first_mono)))))
              (by
                (specialize second_mono nat_le_add_left_mono
                  tail_left_product
                  tail_right_product
                  right)
                (have middle_total_le_right_total
                  (computes-to
                    (nat-le middle_total right_total)
                    (quote :true))
                  (by
                    (calc
                      (nat-le middle_total right_total)
                      (==
                        (nat-le (add right tail_left_product) right_total)
                        (by
                          (simpa only (symm middle_total_proof))))
                      (==
                        (nat-le (add right tail_left_product) (add right tail_right_product))
                        (by
                          (simpa only (symm right_total_proof))))
                      (==
                        (quote :true)
                        (by
                          (exact second_mono)))))
                  (by
                    (specialize total_le nat_le_trans left_total middle_total right_total)
                    (calc
                      (nat-le
                        (mul (cons factor_head factor_tail) left)
                        (mul (cons factor_head factor_tail) right))
                      (==
                        (nat-le
                          (add left (mul factor_tail left))
                          (mul (cons factor_head factor_tail) right))
                        (by
                          (simpa only (mul_cons factor_head factor_tail left))))
                      (==
                        (nat-le
                          (add left tail_left_product)
                          (mul (cons factor_head factor_tail) right))
                        (by
                          (simpa only tail_left_product_proof)))
                      (==
                        (nat-le
                          left_total
                          (mul (cons factor_head factor_tail) right))
                        (by
                          (simpa only left_total_proof)))
                      (==
                        (nat-le
                          left_total
                          (add right (mul factor_tail right)))
                        (by
                          (simpa only (mul_cons factor_head factor_tail right))))
                      (==
                        (nat-le
                          left_total
                          (add right tail_right_product))
                        (by
                          (simpa only tail_right_product_proof)))
                      (==
                        (nat-le left_total right_total)
                        (by
                          (simpa only right_total_proof)))
                      (==
                        (quote :true)
                        (by
                          (exact total_le)))))))))))))
)

(theorem nat_lt_mul_left_mono
  (forall left (is-list left)
    (forall right (is-list right)
      (forall factor (is-list factor)
        (implies
          (computes-to (nat-lt left right) (quote :true))
          (implies
            (computes-to (nat-lt zero factor) (quote :true))
            (computes-to
              (nat-lt (mul factor left) (mul factor right))
              (quote :true)))))))
  (by
    (intro left)
    (intro right)
    (list-induction factor
      (by
        (intro left_lt_right)
        (intro factor_positive)
        (have impossible_eq
          (computes-to (quote :false) (quote :true))
          (by
            (calc
              (quote :false)
              (==
                (nat-lt zero nil)
                (by
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact factor_positive)))))
          (by
            (exact
                (absurd-elim
                  (distinct-outcomes impossible_eq)
                (computes-to (nat-lt (mul nil left) (mul nil right)) (quote :true)))))))
      factor_head
      factor_tail
      induction_hypothesis
      (by
        (intro left_lt_right)
        (intro factor_positive)
        (obtain tail_left_product tail_left_product_proof
          (mul_computes_to_list factor_tail left))
        (obtain tail_right_product tail_right_product_proof
          (mul_computes_to_list factor_tail right))
        (have left_le_right
          (computes-to (nat-le left right) (quote :true))
          (by
            (exact nat_lt_implies_nat_le left right))
          (by
            (specialize tail_le_mono nat_le_mul_left_mono left right factor_tail)
            (have tail_products_le
              (computes-to
                (nat-le tail_left_product tail_right_product)
                (quote :true))
              (by
                (calc
                  (nat-le tail_left_product tail_right_product)
                  (==
                    (nat-le (mul factor_tail left) tail_right_product)
                    (by
                      (simpa only (symm tail_left_product_proof))))
                  (==
                    (nat-le (mul factor_tail left) (mul factor_tail right))
                    (by
                      (simpa only (symm tail_right_product_proof))))
                  (==
                    (quote :true)
                    (by
                      (exact tail_le_mono)))))
              (by
                (obtain left_total left_total_proof
                  (add_computes_to_list left tail_left_product))
                (obtain middle_total middle_total_proof
                  (add_computes_to_list right tail_left_product))
                (obtain right_total right_total_proof
                  (add_computes_to_list right tail_right_product))
                (specialize first_mono nat_lt_add_right_mono left right tail_left_product)
                (have left_total_lt_middle_total
                  (computes-to
                    (nat-lt left_total middle_total)
                    (quote :true))
                  (by
                    (calc
                      (nat-lt left_total middle_total)
                      (==
                        (nat-lt (add left tail_left_product) middle_total)
                        (by
                          (simpa only (symm left_total_proof))))
                      (==
                        (nat-lt (add left tail_left_product) (add right tail_left_product))
                        (by
                          (simpa only (symm middle_total_proof))))
                      (==
                        (quote :true)
                        (by
                          (exact first_mono)))))
                  (by
                    (specialize second_mono nat_le_add_left_mono
                      tail_left_product
                      tail_right_product
                      right)
                    (have middle_total_le_right_total
                      (computes-to
                        (nat-le middle_total right_total)
                        (quote :true))
                      (by
                        (calc
                          (nat-le middle_total right_total)
                          (==
                            (nat-le (add right tail_left_product) right_total)
                            (by
                              (simpa only (symm middle_total_proof))))
                          (==
                            (nat-le (add right tail_left_product) (add right tail_right_product))
                            (by
                              (simpa only (symm right_total_proof))))
                          (==
                            (quote :true)
                            (by
                              (exact second_mono)))))
                      (by
                        (specialize total_lt nat_lt_le_trans left_total middle_total right_total)
                        (calc
                          (nat-lt
                            (mul (cons factor_head factor_tail) left)
                            (mul (cons factor_head factor_tail) right))
                          (==
                            (nat-lt
                              (add left (mul factor_tail left))
                              (mul (cons factor_head factor_tail) right))
                            (by
                              (simpa only (mul_cons factor_head factor_tail left))))
                          (==
                            (nat-lt
                              (add left tail_left_product)
                              (mul (cons factor_head factor_tail) right))
                            (by
                              (simpa only tail_left_product_proof)))
                          (==
                            (nat-lt
                              left_total
                              (mul (cons factor_head factor_tail) right))
                            (by
                              (simpa only left_total_proof)))
                          (==
                            (nat-lt
                              left_total
                              (add right (mul factor_tail right)))
                            (by
                              (simpa only (mul_cons factor_head factor_tail right))))
                          (==
                            (nat-lt
                              left_total
                              (add right tail_right_product))
                            (by
                              (simpa only tail_right_product_proof)))
                          (==
                            (nat-lt left_total right_total)
                            (by
                              (simpa only right_total_proof)))
                          (==
                            (quote :true)
                            (by
                              (exact total_lt))))))))))))))
))

(theorem mul_preserves_nat_value
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (implies
          (computes-to (is-nat-value right) (quote :true))
          (computes-to
            (is-nat-value (mul left right))
            (quote :true))))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro left_is_nat)
        (intro right_is_nat)
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (intro cons_is_nat)
        (intro right_is_nat)
        (specialize cons_parts is_nat_value_cons_true_elim head tail)
        (cases cons_parts ignored_head_unit tail_is_nat)
        (specialize tail_product_is_nat induction_hypothesis right)
        (obtain tail_product tail_product_proof
          (mul_computes_to_list tail right))
        (have tail_product_value_is_nat
          (computes-to
            (is-nat-value tail_product)
            (quote :true))
          (by
            (calc
              (is-nat-value tail_product)
              (==
                (is-nat-value (mul tail right))
                (by
                  (simpa only (symm tail_product_proof))))
            (==
                (quote :true)
                (by
                  (exact tail_product_is_nat))))))
        (specialize product_is_nat add_preserves_nat_value right tail_product)
        (calc
          (is-nat-value (mul (cons head tail) right))
          (==
            (is-nat-value (add right (mul tail right)))
            (by
              (simpa only (mul_cons head tail right))))
          (==
            (is-nat-value (add right tail_product))
            (by
              (simpa only tail_product_proof)))
          (==
            (quote :true)
            (by
              (exact product_is_nat))))))))

(theorem mul_succ_left
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (mul (succ left) right)
        (add right (mul left right)))))
  (by
    (intro left)
    (intro right)
    (calc
      (mul (succ left) right)
      (==
        (mul (cons (quote unit) left) right)
        (by
          (eval)))
      (==
        (add right (mul left right))
        (by
          (exact mul_cons (quote unit) left right))))))

(theorem is_zero_mul_succ_succ
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (is-zero (mul (succ left) (succ right)))
        (quote :false))))
  (by
    (intro left)
    (intro right)
    (obtain right_succ right_succ_proof
      (succ_computes_to_list right))
    (obtain tail_product tail_product_proof
      (mul_computes_to_list left right_succ))
    (calc
      (is-zero (mul (succ left) (succ right)))
      (==
        (is-zero (mul (succ left) right_succ))
        (by
          (simpa only right_succ_proof)))
      (==
        (is-zero (add right_succ (mul left right_succ)))
        (by
          (simpa only (mul_succ_left left right_succ))))
      (==
        (is-zero (add right_succ tail_product))
        (by
          (simpa only tail_product_proof)))
      (==
        (is-zero (add (succ right) tail_product))
        (by
          (simpa only (symm right_succ_proof))))
      (==
        (quote :false)
        (by
          (exact is_zero_add_succ_left right tail_product))))))

(theorem nat_lt_zero_mul_succ_left
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-lt zero right) (quote :true))
        (computes-to
          (nat-lt zero (mul (succ left) right))
          (quote :true)))))
  (by
    (intro left)
    (intro right)
    (intro right_positive)
    (have right_positive_nil
      (computes-to (nat-lt nil right) (quote :true))
      (by
        (calc
          (nat-lt nil right)
          (==
            (nat-lt zero right)
            (by
              (fold zero)
              (eval)))
          (==
            (quote :true)
            (by
              (exact right_positive)))))
      (by
        (obtain tail_product tail_product_proof
          (mul_computes_to_list left right))
        (specialize sum_positive nat_lt_nil_left_add right tail_product)
        (calc
          (nat-lt zero (mul (succ left) right))
          (==
            (nat-lt zero (add right (mul left right)))
            (by
              (simpa only (mul_succ_left left right))))
          (==
            (nat-lt zero (add right tail_product))
            (by
              (simpa only tail_product_proof)))
          (==
            (nat-lt nil (add right tail_product))
            (by
              (simpa only zero_eq_nil)))
          (==
            (quote :true)
            (by
              (exact sum_positive)))))))
)

(theorem nat_lt_zero_mul_succ_succ
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (nat-lt zero (mul (succ left) (succ right)))
        (quote :true))))
  (by
    (intro left)
    (intro right)
    (obtain right_succ right_succ_proof
      (succ_computes_to_list right))
    (have right_succ_positive
      (computes-to (nat-lt zero right_succ) (quote :true))
      (by
        (calc
          (nat-lt zero right_succ)
          (==
            (nat-lt zero (succ right))
            (by
              (simpa only (symm right_succ_proof))))
          (==
            (quote :true)
            (by
              (exact nat_lt_zero_succ right)))))
      (by
        (specialize product_positive
          nat_lt_zero_mul_succ_left
          left
          right_succ)
        (calc
          (nat-lt zero (mul (succ left) (succ right)))
          (==
            (nat-lt zero (mul (succ left) right_succ))
            (by
              (simpa only right_succ_proof)))
          (==
            (quote :true)
            (by
              (exact product_positive)))))))
)

(theorem pred_mul_succ_succ
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (pred (mul (succ left) (succ right)))
        (add right (mul left (succ right))))))
  (by
    (intro left)
    (intro right)
    (obtain right_succ right_succ_proof
      (succ_computes_to_list right))
    (obtain tail_product tail_product_proof
      (mul_computes_to_list left right_succ))
    (calc
      (pred (mul (succ left) (succ right)))
      (==
        (pred (mul (succ left) right_succ))
        (by
          (simpa only right_succ_proof)))
      (==
        (pred (add right_succ (mul left right_succ)))
        (by
          (simpa only (mul_succ_left left right_succ))))
      (==
        (pred (add right_succ tail_product))
        (by
          (simpa only tail_product_proof)))
      (==
        (pred (add (succ right) tail_product))
        (by
          (simpa only (symm right_succ_proof))))
      (==
        (add right tail_product)
        (by
          (exact pred_add_succ_left right tail_product)))
      (==
        (add right (mul left right_succ))
        (by
          (simpa only (symm tail_product_proof))))
      (==
        (add right (mul left (succ right)))
        (by
          (simpa only (symm right_succ_proof)))))))

(theorem mul_succ_right
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (implies
          (computes-to (is-nat-value right) (quote :true))
          (computes-to
            (mul left (succ right))
            (add left (mul left right)))))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro left_is_nat)
        (intro right_is_nat)
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (intro cons_is_nat)
        (intro right_is_nat)
        (specialize cons_parts is_nat_value_cons_true_elim head tail)
        (cases cons_parts head_unit tail_is_nat)
        (have cons_unit_right_is_nat
          (computes-to
            (is-nat-value (cons (quote unit) right))
            (quote :true))
          (by
            (calc
              (is-nat-value (cons (quote unit) right))
              (==
                (is-nat-value right)
                (by
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact right_is_nat))))))
        (specialize tail_succ induction_hypothesis right)
        (obtain tail_product tail_product_proof
          (mul_computes_to_list tail right))
        (obtain right_tail_product right_tail_product_proof
          (add_computes_to_list right tail_product))
        (have cons_product
          (computes-to
            (mul (cons head tail) right)
            (add right tail_product))
          (by
            (calc
              (mul (cons head tail) right)
              (==
                (add right (mul tail right))
                (by
                  (exact mul_cons head tail right)))
              (==
                (add right tail_product)
                (by
                  (simpa only tail_product_proof))))))
        (specialize swapped_tail add_swap (cons (quote unit) right) tail tail_product)
        (specialize tail_cons_unit add_cons_unit_right tail right_tail_product)
        (calc
          (mul (cons head tail) (succ right))
          (==
            (mul (cons head tail) (cons (quote unit) right))
            (by
              (eval)))
          (==
            (add
              (cons (quote unit) right)
              (mul tail (cons (quote unit) right)))
            (by
              (exact mul_cons head tail (cons (quote unit) right))))
          (==
            (add
              (cons (quote unit) right)
              (mul tail (succ right)))
            (by
              (eval)))
          (==
            (add
              (cons (quote unit) right)
              (add tail (mul tail right)))
            (by
              (simpa only tail_succ)))
          (==
            (add
              (cons (quote unit) right)
              (add tail tail_product))
            (by
              (simpa only tail_product_proof)))
          (==
            (add tail (add (cons (quote unit) right) tail_product))
            (by
              (exact swapped_tail)))
          (==
            (add tail (cons (quote unit) (add right tail_product)))
            (by
              (simpa only (add_cons (quote unit) right tail_product))))
          (==
            (add tail (cons (quote unit) right_tail_product))
            (by
              (simpa only right_tail_product_proof)))
          (==
            (succ (add tail right_tail_product))
            (by
              (exact tail_cons_unit)))
          (==
            (add (succ tail) right_tail_product)
            (by
              (exact (symm (add_succ_left tail right_tail_product)))))
          (==
            (add (cons (quote unit) tail) right_tail_product)
            (by
              (eval)))
          (==
            (add (cons (quote unit) tail) (add right tail_product))
            (by
              (simpa only (symm right_tail_product_proof))))
          (==
            (add (cons head tail) (add right tail_product))
            (by
              (simpa only (symm head_unit))))
          (==
            (add (cons head tail) (mul (cons head tail) right))
            (by
              (simpa only (symm cons_product)))))))))

(theorem nat_lt_zero_mul_succ_right
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (implies
          (computes-to (is-nat-value right) (quote :true))
          (implies
            (computes-to (nat-lt zero left) (quote :true))
            (computes-to
              (nat-lt zero (mul left (succ right)))
              (quote :true)))))))
  (by
    (intro left)
    (intro right)
    (intro left_is_nat)
    (intro right_is_nat)
    (intro left_positive)
    (have left_positive_nil
      (computes-to (nat-lt nil left) (quote :true))
      (by
        (calc
          (nat-lt nil left)
          (==
            (nat-lt zero left)
            (by
              (fold zero)
              (eval)))
          (==
            (quote :true)
            (by
              (exact left_positive)))))
      (by
        (obtain product product_proof
          (mul_computes_to_list left right))
        (specialize sum_positive nat_lt_nil_left_add left product)
        (calc
          (nat-lt zero (mul left (succ right)))
          (==
            (nat-lt zero (add left (mul left right)))
            (by
              (simpa only (mul_succ_right left right))))
          (==
            (nat-lt zero (add left product))
            (by
              (simpa only product_proof)))
          (==
            (nat-lt nil (add left product))
            (by
              (simpa only zero_eq_nil)))
          (==
            (quote :true)
            (by
              (exact sum_positive)))))))
)

(theorem mul_zero_right
  (forall nat (is-list nat)
    (computes-to (mul nat zero) zero))
  (by
    (list-induction nat
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (obtain tail_product tail_product_proof
          (mul_computes_to_list tail nil))
        (calc
          (mul (cons head tail) zero)
          (==
            (mul (cons head tail) nil)
            (by
              (simpa only (eval-to zero nil))))
          (==
            (add nil (mul tail nil))
            (by
              (exact mul_cons head tail nil)))
          (==
            (add zero tail_product)
            (by
              (simpa only tail_product_proof)))
          (==
            tail_product
            (by
              (exact add_zero_left tail_product)))
          (==
            (mul tail nil)
            (by
              (simpa only (symm tail_product_proof))))
          (==
            (mul tail zero)
            (by
              (fold zero)
              (eval)))
          (==
            zero
            (by
              (exact induction_hypothesis))))))))

(theorem is_zero_mul_zero_right
  (forall nat (is-list nat)
    (computes-to
      (is-zero (mul nat zero))
      (quote :true)))
  (by
    (intro nat)
    (calc
      (is-zero (mul nat zero))
      (==
        (is-zero zero)
        (by
          (simpa only (mul_zero_right nat))))
      (==
        (quote :true)
        (by
          (eval))))))

(theorem mul_one_left
  (forall right (is-list right)
    (computes-to
      (mul (succ zero) right)
      right))
  (by
    (intro right)
    (calc
      (mul (succ zero) right)
      (==
        (mul (succ nil) right)
        (by
          (simpa only (eval-to zero nil))))
      (==
        (add right (mul nil right))
        (by
          (exact mul_succ_left nil right)))
      (==
        (add right (mul zero right))
        (by
          (fold zero)
          (eval)))
      (==
        (add right zero)
        (by
          (simpa only (mul_zero_left right))))
      (==
        right
        (by
          (exact add_zero_right right))))))

(theorem mul_one_right
  (forall left (is-list left)
    (implies
      (computes-to (is-nat-value left) (quote :true))
      (computes-to
        (mul left (succ zero))
        left)))
  (by
    (list-induction left
      (by
        (intro left_is_nat)
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (intro cons_is_nat)
        (specialize cons_parts is_nat_value_cons_true_elim head tail)
        (cases cons_parts head_unit tail_is_nat)
        (specialize tail_product induction_hypothesis)
        (calc
          (mul (cons head tail) (succ zero))
          (==
            (mul (cons head tail) (cons (quote unit) nil))
            (by
              (eval)))
          (==
            (add
              (cons (quote unit) nil)
              (mul tail (cons (quote unit) nil)))
            (by
              (exact mul_cons head tail (cons (quote unit) nil))))
          (==
            (add (succ zero) (mul tail (succ zero)))
            (by
              (eval)))
          (==
            (add (succ zero) tail)
            (by
              (simpa only tail_product)))
          (==
            (cons (quote unit) tail)
            (by
              (eval)))
          (==
            (cons head tail)
            (by
              (simpa only (symm head_unit)))))))))

(theorem mul_comm
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (implies
          (computes-to (is-nat-value right) (quote :true))
          (computes-to
            (mul left right)
            (mul right left))))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro left_is_nat)
        (intro right_is_nat)
        (calc
          (mul nil right)
          (==
            nil
            (by
              (eval)))
          (==
            zero
            (by
              (fold zero)
              (eval)))
          (==
            (mul right zero)
            (by
              (exact (symm (mul_zero_right right)))))
          (==
            (mul right nil)
            (by
              (eval)))))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (intro cons_is_nat)
        (intro right_is_nat)
        (specialize cons_parts is_nat_value_cons_true_elim head tail)
        (cases cons_parts head_unit tail_is_nat)
        (specialize tail_product induction_hypothesis right)
        (specialize right_times_succ mul_succ_right right tail)
        (calc
          (mul (cons head tail) right)
          (==
            (add right (mul tail right))
            (by
              (exact mul_cons head tail right)))
          (==
            (add right (mul right tail))
            (by
              (simpa only tail_product)))
          (==
            (mul right (succ tail))
            (by
              (exact (symm right_times_succ))))
          (==
            (mul right (cons (quote unit) tail))
            (by
              (eval)))
          (==
            (mul right (cons head tail))
            (by
              (simpa only (symm head_unit)))))))))

(theorem mul_add_left_distrib
  (forall left (is-list left)
    (forall middle (is-list middle)
      (forall right (is-list right)
        (computes-to
          (mul (add left middle) right)
          (add (mul left right) (mul middle right))))))
  (by
    (list-induction left
      (by
        (intro middle)
        (intro right)
        (obtain middle_right middle_right_proof
          (mul_computes_to_list middle right))
        (calc
          (mul (add nil middle) right)
          (==
            (mul middle right)
            (by
              (eval)))
          (==
            middle_right
            (by
              (exact middle_right_proof)))
          (==
            (add zero middle_right)
            (by
              (exact (symm (add_zero_left middle_right)))))
          (==
            (add (mul zero right) middle_right)
            (by
              (rewrite (symm (mul_zero_left right)))
              (eval)))
          (==
            (add (mul nil right) middle_right)
            (by
              (simpa only (eval-to zero nil))))
          (==
            (add (mul nil right) (mul middle right))
            (by
              (simpa only (symm middle_right_proof))))))
      head
      tail
      induction_hypothesis
      (by
        (intro middle)
        (intro right)
        (specialize tail_distrib induction_hypothesis middle right)
        (obtain tail_middle tail_middle_proof
          (add_computes_to_list tail middle))
        (obtain tail_right tail_right_proof
          (mul_computes_to_list tail right))
        (obtain middle_right middle_right_proof
          (mul_computes_to_list middle right))
        (calc
          (mul (add (cons head tail) middle) right)
          (==
            (mul (cons head (add tail middle)) right)
            (by
              (simpa only (add_cons head tail middle))))
          (==
            (mul (cons head tail_middle) right)
            (by
              (simpa only tail_middle_proof)))
          (==
            (add right (mul tail_middle right))
            (by
              (exact mul_cons head tail_middle right)))
          (==
            (add right (mul (add tail middle) right))
            (by
              (simpa only (symm tail_middle_proof))))
          (==
            (add right (add (mul tail right) (mul middle right)))
            (by
              (simpa only tail_distrib)))
          (==
            (add right (add tail_right (mul middle right)))
            (by
              (simpa only tail_right_proof)))
          (==
            (add right (add tail_right middle_right))
            (by
              (simpa only middle_right_proof)))
          (==
            (add (add right tail_right) middle_right)
            (by
              (exact (symm (add_assoc right tail_right middle_right)))))
          (==
            (add (add right tail_right) (mul middle right))
            (by
              (simpa only (symm middle_right_proof))))
          (==
            (add (add right (mul tail right)) (mul middle right))
            (by
              (simpa only (symm tail_right_proof))))
          (==
            (add (mul (cons head tail) right) (mul middle right))
            (by
              (rewrite (symm (mul_cons head tail right)))
              (eval))))))))

(theorem mul_assoc
  (forall left (is-list left)
    (forall middle (is-list middle)
      (forall right (is-list right)
        (computes-to
          (mul (mul left middle) right)
          (mul left (mul middle right))))))
  (by
    (list-induction left
      (by
        (intro middle)
        (intro right)
        (obtain middle_right middle_right_proof
          (mul_computes_to_list middle right))
        (calc
          (mul (mul nil middle) right)
          (==
            nil
            (by
              (eval)))
          (==
            zero
            (by
              (fold zero)
              (eval)))
          (==
            (mul zero middle_right)
            (by
              (exact (symm (mul_zero_left middle_right)))))
          (==
            (mul nil middle_right)
            (by
              (simpa only (eval-to zero nil))))
          (==
            (mul nil (mul middle right))
            (by
              (simpa only (symm middle_right_proof))))))
      head
      tail
      induction_hypothesis
      (by
        (intro middle)
        (intro right)
        (specialize tail_assoc induction_hypothesis middle right)
        (obtain tail_middle tail_middle_proof
          (mul_computes_to_list tail middle))
        (obtain middle_right middle_right_proof
          (mul_computes_to_list middle right))
        (calc
          (mul (mul (cons head tail) middle) right)
          (==
            (mul (add middle (mul tail middle)) right)
            (by
              (simpa only (mul_cons head tail middle))))
          (==
            (mul (add middle tail_middle) right)
            (by
              (simpa only tail_middle_proof)))
          (==
            (add (mul middle right) (mul tail_middle right))
            (by
              (exact mul_add_left_distrib middle tail_middle right)))
          (==
            (add (mul middle right) (mul (mul tail middle) right))
            (by
              (simpa only (symm tail_middle_proof))))
          (==
            (add (mul middle right) (mul tail (mul middle right)))
            (by
              (simpa only tail_assoc)))
          (==
            (add middle_right (mul tail (mul middle right)))
            (by
              (simpa only middle_right_proof)))
          (==
            (add middle_right (mul tail middle_right))
            (by
              (simpa only middle_right_proof)))
          (==
            (mul (cons head tail) middle_right)
            (by
              (exact (symm (mul_cons head tail middle_right)))))
          (==
            (mul (cons head tail) (mul middle right))
            (by
              (simpa only (symm middle_right_proof)))))))))

(theorem mul_add_right_distrib
  (forall left (is-list left)
    (forall middle (is-list middle)
      (forall right (is-list right)
        (implies
          (computes-to (is-nat-value left) (quote :true))
          (implies
            (computes-to (is-nat-value middle) (quote :true))
            (implies
              (computes-to (is-nat-value right) (quote :true))
              (computes-to
                (mul left (add middle right))
                (add (mul left middle) (mul left right)))))))))
  (by
    (intro left)
    (intro middle)
    (intro right)
    (intro left_is_nat)
    (intro middle_is_nat)
    (intro right_is_nat)
    (obtain middle_right_sum middle_right_sum_proof
      (add_computes_to_list middle right))
    (specialize sum_is_nat add_preserves_nat_value middle right)
    (have sum_value_is_nat
      (computes-to
        (is-nat-value middle_right_sum)
        (quote :true))
      (by
        (calc
          (is-nat-value middle_right_sum)
          (==
            (is-nat-value (add middle right))
            (by
              (simpa only (symm middle_right_sum_proof))))
          (==
            (quote :true)
            (by
              (exact sum_is_nat))))))
    (specialize left_sum_comm mul_comm left middle_right_sum)
    (specialize middle_left_comm mul_comm middle left)
    (specialize right_left_comm mul_comm right left)
    (calc
      (mul left (add middle right))
      (==
        (mul left middle_right_sum)
        (by
          (simpa only middle_right_sum_proof)))
      (==
        (mul middle_right_sum left)
        (by
          (exact left_sum_comm)))
      (==
        (mul (add middle right) left)
        (by
          (simpa only (symm middle_right_sum_proof))))
      (==
        (add (mul middle left) (mul right left))
        (by
          (exact mul_add_left_distrib middle right left)))
      (==
        (add (mul left middle) (mul right left))
        (by
          (simpa only middle_left_comm)))
      (==
        (add (mul left middle) (mul left right))
        (by
          (simpa only right_left_comm))))))
