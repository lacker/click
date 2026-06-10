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

(theorem partition_computes_to_pair
  (forall predicate (is-value predicate)
    (implies
      (forall value (is-value value)
        (is-bool (predicate value)))
      (forall list (is-list list)
        (exists left (is-list left)
          (exists right (is-list right)
            (computes-to
              (partition predicate list)
              (cons left (cons right nil))))))))
  (by
    (intro predicate)
    (intro predicate_returns_bool)
    (list-induction list
      (by
        (exists nil
          (by
            (exists nil
              (by
                (exact partition_nil predicate))))))
      head
      tail
      induction_hypothesis
      (by
        (obtain tail_left tail_right_exists induction_hypothesis)
        (obtain tail_right tail_partition tail_right_exists)
        (or-elim
          (predicate_returns_bool head)
          predicate_true
          (by
            (exists (cons head tail_left)
              (by
                (exists tail_right
                  (by
                    (calc
                      (partition predicate (cons head tail))
                      (==
                        (cons
                          (cons
                            head
                            (head (partition predicate tail)))
                          (cons
                            (head (tail (partition predicate tail)))
                            nil))
                        (by
                          (apply partition_cons_true predicate head tail)))
                      (==
                        (cons
                          (cons
                            head
                            (head
                              (cons tail_left (cons tail_right nil))))
                          (cons
                            (head
                              (tail
                                (cons tail_left (cons tail_right nil))))
                            nil))
                        (by
                          (simpa only tail_partition)))
                      (==
                        (cons
                          (cons head tail_left)
                          (cons tail_right nil))
                        (by
                          (eval)))))))))
          predicate_false
          (by
            (exists tail_left
              (by
                (exists (cons head tail_right)
                  (by
                    (calc
                      (partition predicate (cons head tail))
                      (==
                        (cons
                          (head (partition predicate tail))
                          (cons
                            (cons
                              head
                              (head
                                (tail (partition predicate tail))))
                            nil))
                        (by
                          (apply partition_cons_false predicate head tail)))
                      (==
                        (cons
                          (head
                            (cons tail_left (cons tail_right nil)))
                          (cons
                            (cons
                              head
                              (head
                                (tail
                                  (cons
                                    tail_left
                                    (cons tail_right nil)))))
                            nil))
                        (by
                          (simpa only tail_partition)))
                      (==
                        (cons
                          tail_left
                          (cons (cons head tail_right) nil))
                        (by
                          (eval)))))))))))))
)

(theorem partition_first_filter
  (forall predicate (is-value predicate)
    (implies
      (forall value (is-value value)
        (is-bool (predicate value)))
      (forall list (is-list list)
        (computes-to
          (head (partition predicate list))
          (filter predicate list)))))
  (by
    (intro predicate)
    (intro predicate_returns_bool)
    (list-induction list
      (by
        (have partition_pair
          (computes-to
            (partition predicate nil)
            (cons nil (cons nil nil)))
          (by
            (exact partition_nil predicate))
          (by
            (calc
              (head (partition predicate nil))
              (==
                nil
                (by
                  (apply
                    list_pair_first_from_computation
                    (partition predicate nil)
                    nil
                    nil)))
              (==
                (filter predicate nil)
                (by
                  (exact (symm (filter_nil predicate)))))))))
      head
      tail
      induction_hypothesis
      (by
        (obtain tail_left tail_right_exists
          (partition_computes_to_pair predicate tail))
        (obtain tail_right tail_partition tail_right_exists)
        (have tail_first
          (computes-to
            (head (partition predicate tail))
            tail_left)
          (by
            (apply
              list_pair_first_from_computation
              (partition predicate tail)
              tail_left
              tail_right))
          (by
            (have tail_left_filter
              (computes-to tail_left (filter predicate tail))
              (by
                (calc
                  tail_left
                  (==
                    (head (partition predicate tail))
                    (by
                      (exact (symm tail_first))))
                  (==
                    (filter predicate tail)
                    (by
                      (exact induction_hypothesis)))))
              (by
                (or-elim
                  (predicate_returns_bool head)
                  predicate_true
                  (by
                    (have current_partition
                      (computes-to
                        (partition predicate (cons head tail))
                        (cons
                          (cons head tail_left)
                          (cons tail_right nil)))
                      (by
                        (calc
                          (partition predicate (cons head tail))
                          (==
                            (cons
                              (cons
                                head
                                (head (partition predicate tail)))
                              (cons
                                (head (tail (partition predicate tail)))
                                nil))
                            (by
                              (apply
                                partition_cons_true
                                predicate
                                head
                                tail)))
                          (==
                            (cons
                              (cons head tail_left)
                              (cons tail_right nil))
                            (by
                              (simpa only tail_first tail_partition)))))
                      (by
                        (calc
                          (head
                            (partition
                              predicate
                              (cons head tail)))
                          (==
                            (cons head tail_left)
                            (by
                              (apply
                                list_pair_first_from_computation
                                (partition
                                  predicate
                                  (cons head tail))
                                (cons head tail_left)
                                tail_right)))
                          (==
                            (cons head (filter predicate tail))
                            (by
                              (simpa only tail_left_filter)))
                          (==
                            (filter
                              predicate
                              (cons head tail))
                            (by
                              (have filter_step
                                (computes-to
                                  (filter predicate (cons head tail))
                                  (cons head (filter predicate tail)))
                                (by
                                  (apply
                                    filter_cons_true
                                    predicate
                                    head
                                    tail))
                                (by
                                  (exact (symm filter_step))))))))))
                  predicate_false
                  (by
                    (have current_partition
                      (computes-to
                        (partition predicate (cons head tail))
                        (cons
                          tail_left
                          (cons (cons head tail_right) nil)))
                      (by
                        (calc
                          (partition predicate (cons head tail))
                          (==
                            (cons
                              (head (partition predicate tail))
                              (cons
                                (cons
                                  head
                                  (head
                                    (tail
                                      (partition predicate tail))))
                                nil))
                            (by
                              (apply
                                partition_cons_false
                                predicate
                                head
                                tail)))
                          (==
                            (cons
                              tail_left
                              (cons (cons head tail_right) nil))
                            (by
                              (simpa only tail_first tail_partition)))))
                      (by
                        (calc
                          (head
                            (partition
                              predicate
                              (cons head tail)))
                          (==
                            tail_left
                            (by
                              (apply
                                list_pair_first_from_computation
                                (partition
                                  predicate
                                  (cons head tail))
                                tail_left
                                (cons head tail_right))))
                          (==
                            (filter predicate tail)
                            (by
                              (exact tail_left_filter)))
                          (==
                            (filter
                              predicate
                              (cons head tail))
                            (by
                              (have filter_step
                                (computes-to
                                  (filter predicate (cons head tail))
                                  (filter predicate tail))
                                (by
                                  (apply
                                    filter_cons_false
                                    predicate
                                    head
                                    tail))
                                (by
                                  (exact (symm filter_step)))))))))))))))
))))

(theorem partition_second_filter_false
  (forall predicate (is-value predicate)
    (implies
      (forall value (is-value value)
        (is-bool (predicate value)))
      (forall list (is-list list)
        (computes-to
          (head (tail (partition predicate list)))
          (reject predicate list)))))
  (by
    (intro predicate)
    (intro predicate_returns_bool)
    (list-induction list
      (by
        (have partition_pair
          (computes-to
            (partition predicate nil)
            (cons nil (cons nil nil)))
          (by
            (exact partition_nil predicate))
          (by
            (calc
              (head (tail (partition predicate nil)))
              (==
                nil
                (by
                  (apply
                    list_pair_second_from_computation
                    (partition predicate nil)
                    nil
                    nil)))
              (==
                (reject predicate nil)
                (by
                  (exact (symm (reject_nil predicate)))))))))
      head
      tail
      induction_hypothesis
      (by
        (obtain tail_left tail_right_exists
          (partition_computes_to_pair predicate tail))
        (obtain tail_right tail_partition tail_right_exists)
        (have tail_first
          (computes-to
            (head (partition predicate tail))
            tail_left)
          (by
            (apply
              list_pair_first_from_computation
              (partition predicate tail)
              tail_left
              tail_right))
          (by
            (have tail_second
              (computes-to
                (head (tail (partition predicate tail)))
                tail_right)
              (by
                (apply
                  list_pair_second_from_computation
                  (partition predicate tail)
                  tail_left
                  tail_right))
              (by
                (have tail_right_reject
                  (computes-to tail_right (reject predicate tail))
                  (by
                    (calc
                      tail_right
                      (==
                        (head (tail (partition predicate tail)))
                        (by
                          (exact (symm tail_second))))
                      (==
                        (reject predicate tail)
                        (by
                          (exact induction_hypothesis)))))
                  (by
                    (or-elim
                      (predicate_returns_bool head)
                      predicate_true
                      (by
                        (have current_partition
                          (computes-to
                            (partition predicate (cons head tail))
                            (cons
                              (cons head tail_left)
                              (cons tail_right nil)))
                          (by
                            (calc
                              (partition predicate (cons head tail))
                              (==
                                (cons
                                  (cons
                                    head
                                    (head (partition predicate tail)))
                                  (cons
                                    (head
                                      (tail
                                        (partition predicate tail)))
                                    nil))
                                (by
                                  (apply
                                    partition_cons_true
                                    predicate
                                    head
                                    tail)))
                              (==
                                (cons
                                  (cons head tail_left)
                                  (cons tail_right nil))
                                (by
                                  (simpa only tail_first tail_partition)))))
                          (by
                            (calc
                              (head
                                (tail
                                  (partition
                                    predicate
                                    (cons head tail))))
                              (==
                                tail_right
                                (by
                                  (apply
                                    list_pair_second_from_computation
                                    (partition
                                      predicate
                                      (cons head tail))
                                    (cons head tail_left)
                                    tail_right)))
                              (==
                                (reject predicate tail)
                                (by
                                  (exact tail_right_reject)))
                              (==
                                (reject
                                  predicate
                                  (cons head tail))
                                (by
                                  (have reject_step
                                    (computes-to
                                      (reject
                                        predicate
                                        (cons head tail))
                                      (reject predicate tail))
                                    (by
                                      (apply
                                        reject_cons_true
                                        predicate
                                        head
                                        tail))
                                    (by
                                      (exact
                                        (symm reject_step))))))))))
                      predicate_false
                      (by
                        (have current_partition
                          (computes-to
                            (partition predicate (cons head tail))
                            (cons
                              tail_left
                              (cons (cons head tail_right) nil)))
                          (by
                            (calc
                              (partition predicate (cons head tail))
                              (==
                                (cons
                                  (head (partition predicate tail))
                                  (cons
                                    (cons
                                      head
                                      (head
                                        (tail
                                          (partition predicate tail))))
                                    nil))
                                (by
                                  (apply
                                    partition_cons_false
                                    predicate
                                    head
                                    tail)))
                              (==
                                (cons
                                  tail_left
                                  (cons (cons head tail_right) nil))
                                (by
                                  (simpa only tail_first tail_partition)))))
                          (by
                            (calc
                              (head
                                (tail
                                  (partition
                                    predicate
                                    (cons head tail))))
                              (==
                                (cons head tail_right)
                                (by
                                  (apply
                                    list_pair_second_from_computation
                                    (partition
                                      predicate
                                      (cons head tail))
                                    tail_left
                                    (cons head tail_right))))
                              (==
                                (cons head (reject predicate tail))
                                (by
                                  (simpa only tail_right_reject)))
                              (==
                                (reject
                                  predicate
                                  (cons head tail))
                                (by
                                  (have reject_step
                                    (computes-to
                                      (reject
                                        predicate
                                        (cons head tail))
                                      (cons
                                        head
                                        (reject predicate tail)))
                                    (by
                                      (apply
                                        reject_cons_false
                                        predicate
                                        head
                                        tail))
                                    (by
                                      (exact
                                        (symm reject_step))))))))))))))))))
)))

(theorem partition_append_filter_reject
  (forall predicate (is-value predicate)
    (implies
      (forall value (is-value value)
        (is-bool (predicate value)))
      (forall list (is-list list)
        (computes-to
          (append
            (head (partition predicate list))
            (head (tail (partition predicate list))))
          (append
            (filter predicate list)
            (reject predicate list))))))
  (by
    (intro predicate)
    (intro predicate_returns_bool)
    (intro list)
    (calc
      (append
        (head (partition predicate list))
        (head (tail (partition predicate list))))
      (==
        (append
          (filter predicate list)
          (head (tail (partition predicate list))))
        (by
          (simpa only (partition_first_filter predicate list))))
      (==
        (append
          (filter predicate list)
          (reject predicate list))
        (by
          (simpa only
            (partition_second_filter_false predicate list)))))))

(theorem partition_all_true
  (forall predicate (is-value predicate)
    (implies
      (forall value (is-value value)
        (computes-to (predicate value) (quote :true)))
      (forall list (is-list list)
        (computes-to
          (partition predicate list)
          (cons list (cons nil nil))))))
  (by
    (intro predicate)
    (intro predicate_true)
    (list-induction list
      (by
        (exact partition_nil predicate))
      head
      tail
      induction_hypothesis
      (by
        (have head_true
          (computes-to (predicate head) (quote :true))
          (by
            (exact predicate_true head))
          (by
            (calc
              (partition predicate (cons head tail))
              (==
                (cons
                  (cons
                    head
                    (head (partition predicate tail)))
                  (cons
                    (head (tail (partition predicate tail)))
                    nil))
                (by
                  (apply
                    partition_cons_true
                    predicate
                    head
                    tail)))
              (==
                (cons (cons head tail) (cons nil nil))
                (by
                  (simpa only induction_hypothesis))))))))
  ))

(theorem partition_all_false
  (forall predicate (is-value predicate)
    (implies
      (forall value (is-value value)
        (computes-to (predicate value) (quote :false)))
      (forall list (is-list list)
        (computes-to
          (partition predicate list)
          (cons nil (cons list nil))))))
  (by
    (intro predicate)
    (intro predicate_false)
    (list-induction list
      (by
        (exact partition_nil predicate))
      head
      tail
      induction_hypothesis
      (by
        (have head_false
          (computes-to (predicate head) (quote :false))
          (by
            (exact predicate_false head))
          (by
            (calc
              (partition predicate (cons head tail))
              (==
                (cons
                  (head (partition predicate tail))
                  (cons
                    (cons
                      head
                      (head (tail (partition predicate tail))))
                    nil))
                (by
                  (apply
                    partition_cons_false
                    predicate
                    head
                    tail)))
              (==
                (cons nil (cons (cons head tail) nil))
                (by
                  (simpa only induction_hypothesis))))))))
  ))

(theorem elem_index_cons_true_member_true
  (forall value (is-value value)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (value-eq value head) (quote :true))
          (and
            (computes-to
              (elem-index value (cons head tail))
              (some nil))
            (computes-to
              (member value (cons head tail))
              (quote :true)))))))
  (by
    (intro value)
    (intro head)
    (intro tail)
    (intro values_equal)
    (split
      (by
        (apply elem_index_cons_true value head tail))
      (by
        (apply member_cons_true value head tail)))))

(theorem elem_index_cons_false_none_member_false
  (forall value (is-value value)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to (value-eq value head) (quote :false))
          (implies
            (computes-to (elem-index value tail) none)
            (implies
              (computes-to
                (member value tail)
                (quote :false))
              (and
                (computes-to
                  (elem-index value (cons head tail))
                  none)
                (computes-to
                  (member value (cons head tail))
                  (quote :false)))))))))
  (by
    (intro value)
    (intro head)
    (intro tail)
    (intro values_not_equal)
    (intro tail_missing)
    (intro tail_member_false)
    (split
      (by
        (apply elem_index_cons_false_none value head tail))
      (by
        (calc
          (member value (cons head tail))
          (==
            (member value tail)
            (by
              (apply member_cons_false value head tail)))
          (==
            (quote :false)
            (by
              (exact tail_member_false)))))))
)

(theorem elem_index_cons_false_some_member_true
  (forall value (is-value value)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (forall index (is-list index)
          (implies
            (computes-to (value-eq value head) (quote :false))
            (implies
              (computes-to (elem-index value tail) (some index))
              (implies
                (computes-to
                  (member value tail)
                  (quote :true))
                (and
                  (computes-to
                    (elem-index value (cons head tail))
                    (some (cons (quote unit) index)))
                  (computes-to
                    (member value (cons head tail))
                    (quote :true))))))))))
  (by
    (intro value)
    (intro head)
    (intro tail)
    (intro index)
    (intro values_not_equal)
    (intro tail_found)
    (intro tail_member_true)
    (split
      (by
        (apply elem_index_cons_false_some value head tail index))
      (by
        (calc
          (member value (cons head tail))
          (==
            (member value tail)
            (by
              (apply member_cons_false value head tail)))
          (==
            (quote :true)
            (by
              (exact tail_member_true)))))))
)

(theorem elem_index_computes_to_option
  (forall value (is-value value)
    (forall list (is-list list)
      (forall result (is-value result)
        (implies
          (computes-to (elem-index value list) result)
          (or
            (computes-to result none)
            (exists index (is-list index)
              (computes-to result (some index))))))))
  (by
    (intro value)
    (list-induction list
      (by
        (intro result)
        (intro elem_result)
        (left
          (by
            (calc
              result
              (==
                (elem-index value nil)
                (by
                  (exact (symm elem_result))))
              (==
                none
                (by
                  (exact elem_index_nil value)))))))
      head
      tail
      induction_hypothesis
      (by
        (intro result)
        (intro elem_result)
        (have elem_branch_result
          (computes-to
            (if
              (value-eq value (head (cons head tail)))
              (some nil)
              ((lambda branch_option
                 (if
                   (is-some branch_option)
                   (some (cons (quote unit) (head (tail branch_option))))
                   none))
               (elem-index value (tail (cons head tail)))))
            result)
          (by
            (calc
              (if
                (value-eq value (head (cons head tail)))
                (some nil)
                ((lambda branch_option
                   (if
                     (is-some branch_option)
                     (some (cons (quote unit) (head (tail branch_option))))
                     none))
                 (elem-index value (tail (cons head tail)))))
              (==
                (elem-index value (cons head tail))
                (by
                  (exact (symm (elem_index_cons_branch value head tail)))))
              (==
                result
                (by
                  (exact elem_result)))))
          (by
            (have value_eq_bool
              (is-bool
                (value-eq value (head (cons head tail))))
              (proof
                (if-value-condition-bool
                  (assume elem_branch_result)))
              (by
                (or-elim value_eq_bool
                  values_equal_through_cons
                  (by
                    (have values_equal
                      (computes-to
                        (value-eq value head)
                        (quote :true))
                      (by
                        (calc
                          (value-eq value head)
                          (==
                            (value-eq
                              value
                              (head (cons head tail)))
                            (by
                              (eval)))
                          (==
                            (quote :true)
                            (by
                              (exact values_equal_through_cons)))))
                      (by
                        (right
                          (by
                            (exists nil
                              (by
                                (calc
                                  result
                                  (==
                                    (elem-index value (cons head tail))
                                    (by
                                      (exact (symm elem_result))))
                                  (==
                                    (some nil)
                                    (by
                                      (apply
                                        elem_index_cons_true
                                        value
                                        head
                                        tail)))))))))))
                  values_not_equal_through_cons
                  (by
                    (have values_not_equal
                      (computes-to
                        (value-eq value head)
                        (quote :false))
                      (by
                        (calc
                          (value-eq value head)
                          (==
                            (value-eq
                              value
                              (head (cons head tail)))
                            (by
                              (eval)))
                          (==
                            (quote :false)
                            (by
                              (exact values_not_equal_through_cons)))))
                      (by
                        (have branch_application
                          (computes-to
                            ((lambda branch_option
                               (if
                                 (is-some branch_option)
                                 (some (cons (quote unit) (head (tail branch_option))))
                                 none))
                             (elem-index value (tail (cons head tail))))
                            result)
                          (by
                            (calc
                              ((lambda branch_option
                                 (if
                                   (is-some branch_option)
                                   (some (cons (quote unit) (head (tail branch_option))))
                                   none))
                               (elem-index value (tail (cons head tail))))
                              (==
                                (elem-index value (cons head tail))
                                (by
                                  (simpa only values_not_equal)))
                              (==
                                result
                                (by
                                  (exact elem_result)))))
                          (by
                            (obtain tail_result tail_result_proof
                              (apply-value-argument
                                tail_result
                                (assume branch_application))
                              (by
                                (have tail_result_from_tail
                                  (computes-to
                                    (elem-index value tail)
                                    tail_result)
                                  (by
                                    (calc
                                      (elem-index value tail)
                                      (==
                                        (elem-index
                                          value
                                          (tail (cons head tail)))
                                        (by
                                          (eval)))
                                      (==
                                        tail_result
                                        (by
                                          (exact tail_result_proof)))))
                                  (by
                                    (specialize tail_option_imp
                                      induction_hypothesis
                                      tail_result)
                                    (have tail_option
                                      (or
                                        (computes-to tail_result none)
                                        (exists index (is-list index)
                                          (computes-to
                                            tail_result
                                            (some index))))
                                      (by
                                        (exact tail_option_imp))
                                      (by
                                        (or-elim tail_option
                                          tail_none
                                          (by
                                            (left
                                              (by
                                                (calc
                                                  result
                                                  (==
                                                    ((lambda branch_option
                                                       (if
                                                         (is-some branch_option)
                                                         (some
                                                           (cons
                                                             (quote unit)
                                                             (head (tail branch_option))))
                                                         none))
                                                     (elem-index
                                                       value
                                                       (tail (cons head tail))))
                                                    (by
                                                      (exact
                                                        (symm
                                                          branch_application))))
                                                  (==
                                                    none
                                                    (by
                                                      (simpa only
                                                        tail_result_proof
                                                        tail_none
                                                        none_is_some)))))))
                                          tail_some_exists
                                          (by
                                            (obtain index tail_some tail_some_exists)
                                            (right
                                              (by
                                                (exists
                                                  (cons (quote unit) index)
                                                  (by
                                                    (calc
                                                      result
                                                      (==
                                                        ((lambda branch_option
                                                           (if
                                                             (is-some branch_option)
                                                             (some
                                                               (cons
                                                                 (quote unit)
                                                                 (head (tail branch_option))))
                                                             none))
                                                         (elem-index
                                                           value
                                                           (tail (cons head tail))))
                                                        (by
                                                          (exact
                                                            (symm
                                                              branch_application))))
                                                      (==
                                                        (some
                                                          (cons (quote unit) index))
                                                        (by
                                                          (simpa only
                                                            tail_result_proof
                                                            tail_some
                                                            (some_is_some index)))))))))))))))))))))))))))))
  ))

(theorem member_false_implies_elem_index_none
  (forall value (is-value value)
    (forall list (is-list list)
      (implies
        (computes-to (member value list) (quote :false))
        (computes-to (elem-index value list) none))))
  (by
    (intro value)
    (list-induction list
      (by
        (intro member_false)
        (exact elem_index_nil value))
      head
      tail
      induction_hypothesis
      (by
        (intro member_false)
        (have member_branch_false
          (computes-to
            (if
              (value-eq value (head (cons head tail)))
              (quote :true)
              (member value (tail (cons head tail))))
            (quote :false))
          (by
            (calc
              (if
                (value-eq value (head (cons head tail)))
                (quote :true)
                (member value (tail (cons head tail))))
              (==
                (member value (cons head tail))
                (by
                  (eval)))
              (==
                (quote :false)
                (by
                  (exact member_false)))))
          (by
            (specialize branch_parts
              if_false_result_with_true_then
              (value-eq value (head (cons head tail)))
              (member value (tail (cons head tail))))
            (cases branch_parts values_not_equal_through_cons tail_member_false_through_cons)
            (have values_not_equal
              (computes-to (value-eq value head) (quote :false))
              (by
                (calc
                  (value-eq value head)
                  (==
                    (value-eq value (head (cons head tail)))
                    (by
                      (eval)))
                  (==
                    (quote :false)
                    (by
                      (exact values_not_equal_through_cons)))))
              (by
                (have tail_member_false
                  (computes-to (member value tail) (quote :false))
                  (by
                    (calc
                      (member value tail)
                      (==
                        (member value (tail (cons head tail)))
                        (by
                          (eval)))
                      (==
                        (quote :false)
                        (by
                          (exact tail_member_false_through_cons)))))
                  (by
                    (specialize tail_missing induction_hypothesis)
                    (apply elem_index_cons_false_none value head tail))))))))))
  )

(theorem member_true_implies_elem_index_some
  (forall value (is-value value)
    (forall list (is-list list)
      (implies
        (computes-to (member value list) (quote :true))
        (exists index (is-list index)
          (computes-to
            (elem-index value list)
            (some index))))))
  (by
    (intro value)
    (list-induction list
      (by
        (intro member_true)
        (have impossible_eq
          (computes-to (quote :false) (quote :true))
          (by
            (calc
              (quote :false)
              (==
                (member value nil)
                (by
                  (exact (symm (member_nil value)))))
              (==
                (quote :true)
                (by
                  (exact member_true)))))
          (by
            (exact
              (absurd-elim
                (distinct-outcomes impossible_eq)
                (exists index (is-list index)
                  (computes-to
                    (elem-index value nil)
                    (some index))))))))
      head
      tail
      induction_hypothesis
      (by
        (intro member_true)
        (have member_branch_true
          (computes-to
            (if
              (value-eq value (head (cons head tail)))
              (quote :true)
              (member value (tail (cons head tail))))
            (quote :true))
          (by
            (calc
              (if
                (value-eq value (head (cons head tail)))
                (quote :true)
                (member value (tail (cons head tail))))
              (==
                (member value (cons head tail))
                (by
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact member_true)))))
          (by
            (have value_eq_bool
              (is-bool
                (value-eq value (head (cons head tail))))
              (proof
                (if-value-condition-bool
                  (assume member_branch_true)))
              (by
                (or-elim value_eq_bool
                  values_equal_through_cons
                  (by
                    (have values_equal
                      (computes-to
                        (value-eq value head)
                        (quote :true))
                      (by
                        (calc
                          (value-eq value head)
                          (==
                            (value-eq
                              value
                              (head (cons head tail)))
                            (by
                              (eval)))
                          (==
                            (quote :true)
                            (by
                              (exact values_equal_through_cons)))))
                      (by
                        (exists nil
                          (by
                            (apply
                              elem_index_cons_true
                              value
                              head
                              tail))))))
                  values_not_equal_through_cons
                  (by
                    (have values_not_equal
                      (computes-to
                        (value-eq value head)
                        (quote :false))
                      (by
                        (calc
                          (value-eq value head)
                          (==
                            (value-eq
                              value
                              (head (cons head tail)))
                            (by
                              (eval)))
                          (==
                            (quote :false)
                            (by
                              (exact values_not_equal_through_cons)))))
                      (by
                        (have tail_member_true
                          (computes-to
                            (member value tail)
                            (quote :true))
                          (by
                            (calc
                              (member value tail)
                              (==
                                (member
                                  value
                                  (tail (cons head tail)))
                                (by
                                  (eval)))
                              (==
                                (if
                                  (value-eq
                                    value
                                    (head (cons head tail)))
                                  (quote :true)
                                  (member
                                    value
                                    (tail (cons head tail))))
                                (by
                                  (simpa only
                                    values_not_equal_through_cons)))
                              (==
                                (quote :true)
                                (by
                                  (exact member_branch_true)))))
                          (by
                            (specialize tail_exists induction_hypothesis)
                            (obtain index tail_found tail_exists)
                            (exists (cons (quote unit) index)
                              (by
                                (apply
                                  elem_index_cons_false_some
                                  value
                                  head
                                  tail
                                  index)))))))))))))))
  ))

(theorem elem_index_none_implies_member_false
  (forall value (is-value value)
    (forall list (is-list list)
      (implies
        (computes-to (elem-index value list) none)
        (computes-to (member value list) (quote :false)))))
  (by
    (intro value)
    (list-induction list
      (by
        (intro elem_missing)
        (exact member_nil value))
      head
      tail
      induction_hypothesis
      (by
        (intro elem_missing)
        (have elem_branch_result
          (computes-to
            (if
              (value-eq value (head (cons head tail)))
              (some nil)
              ((lambda branch_option
                 (if
                   (is-some branch_option)
                   (some (cons (quote unit) (head (tail branch_option))))
                   none))
               (elem-index value (tail (cons head tail)))))
            (quote :none))
          (by
            (calc
              (if
                (value-eq value (head (cons head tail)))
                (some nil)
                ((lambda branch_option
                   (if
                     (is-some branch_option)
                     (some (cons (quote unit) (head (tail branch_option))))
                     none))
                 (elem-index value (tail (cons head tail)))))
              (==
                (elem-index value (cons head tail))
                (by
                  (exact (symm (elem_index_cons_branch value head tail)))))
              (==
                none
                (by
                  (exact elem_missing)))
              (==
                (quote :none)
                (by
                  (eval)))))
          (by
            (have value_eq_bool
              (is-bool
                (value-eq value (head (cons head tail))))
              (proof
                (if-value-condition-bool
                  (assume elem_branch_result)))
              (by
                (or-elim value_eq_bool
                  values_equal_through_cons
                  (by
                    (have values_equal
                      (computes-to
                        (value-eq value head)
                        (quote :true))
                      (by
                        (calc
                          (value-eq value head)
                          (==
                            (value-eq
                              value
                              (head (cons head tail)))
                            (by
                              (eval)))
                          (==
                            (quote :true)
                            (by
                              (exact values_equal_through_cons)))))
                      (by
                        (have impossible_eq
                          (computes-to (some nil) none)
                          (by
                            (calc
                              (some nil)
                              (==
                                (elem-index value (cons head tail))
                                (by
                                  (simpa only values_equal)))
                              (==
                                none
                                (by
                                  (exact elem_missing)))))
                          (by
                            (have contradiction
                              (absurd)
                              (by
                                (apply some_none_absurd nil))
                              (by
                                (exact
                                  (absurd-elim
                                    contradiction
                                    (computes-to
                                      (member value (cons head tail))
                                      (quote :false)))))))))))
                  values_not_equal_through_cons
                  (by
                    (have values_not_equal
                      (computes-to
                        (value-eq value head)
                        (quote :false))
                      (by
                        (calc
                          (value-eq value head)
                          (==
                            (value-eq
                              value
                              (head (cons head tail)))
                            (by
                              (eval)))
                          (==
                            (quote :false)
                            (by
                              (exact values_not_equal_through_cons)))))
                      (by
                        (have branch_application
                          (computes-to
                            ((lambda branch_option
                               (if
                                 (is-some branch_option)
                                 (some (cons (quote unit) (head (tail branch_option))))
                                 none))
                             (elem-index value (tail (cons head tail))))
                            (quote :none))
                          (by
                            (calc
                              ((lambda branch_option
                                 (if
                                   (is-some branch_option)
                                   (some (cons (quote unit) (head (tail branch_option))))
                                   none))
                               (elem-index value (tail (cons head tail))))
                              (==
                                (elem-index value (cons head tail))
                                (by
                                  (simpa only values_not_equal)))
                              (==
                                none
                                (by
                                  (exact elem_missing)))
                              (==
                                (quote :none)
                                (by
                                  (eval)))))
                          (by
                            (obtain tail_result tail_result_proof
                              (apply-value-argument
                                tail_result
                                (assume branch_application))
                              (by
                                (have tail_result_from_tail
                                  (computes-to
                                    (elem-index value tail)
                                    tail_result)
                                  (by
                                    (calc
                                      (elem-index value tail)
                                      (==
                                        (elem-index
                                          value
                                          (tail (cons head tail)))
                                        (by
                                          (eval)))
                                      (==
                                        tail_result
                                        (by
                                          (exact tail_result_proof)))))
                                  (by
                                    (specialize tail_option
                                      elem_index_computes_to_option
                                      value
                                      tail
                                      tail_result)
                                    (or-elim tail_option
                                      tail_none
                                      (by
                                        (have tail_missing
                                          (computes-to
                                            (elem-index value tail)
                                            none)
                                          (by
                                            (calc
                                              (elem-index value tail)
                                              (==
                                                tail_result
                                                (by
                                                  (exact
                                                    tail_result_from_tail)))
                                              (==
                                                none
                                                (by
                                                  (exact tail_none)))))
                                          (by
                                            (specialize tail_member_false
                                              induction_hypothesis)
                                            (calc
                                              (member value (cons head tail))
                                              (==
                                                (member value tail)
                                                (by
                                                  (apply
                                                    member_cons_false
                                                    value
                                                    head
                                                    tail)))
                                              (==
                                                (quote :false)
                                                (by
                                                  (exact
                                                    tail_member_false)))))))
                                      tail_some_exists
                                      (by
                                        (obtain tail_index tail_some tail_some_exists)
                                        (have tail_found
                                          (computes-to
                                            (elem-index value tail)
                                            (some tail_index))
                                          (by
                                            (calc
                                              (elem-index value tail)
                                              (==
                                                tail_result
                                                (by
                                                  (exact
                                                    tail_result_from_tail)))
                                              (==
                                                (some tail_index)
                                                (by
                                                  (exact tail_some)))))
                                          (by
                                            (have cons_found
                                              (computes-to
                                                (elem-index
                                                  value
                                                  (cons head tail))
                                                (some
                                                  (cons
                                                    (quote unit)
                                                    tail_index)))
                                              (by
                                                (apply
                                                  elem_index_cons_false_some
                                                  value
                                                  head
                                                  tail
                                                  tail_index))
                                              (by
                                                (have impossible_eq
                                                  (computes-to
                                                    (some
                                                      (cons
                                                        (quote unit)
                                                        tail_index))
                                                    none)
                                                  (by
                                                    (calc
                                                      (some
                                                        (cons
                                                          (quote unit)
                                                          tail_index))
                                                      (==
                                                        (elem-index
                                                          value
                                                          (cons head tail))
                                                        (by
                                                          (exact
                                                            (symm
                                                              cons_found))))
                                                      (==
                                                        none
                                                        (by
                                                          (exact
                                                            elem_missing)))))
                                                  (by
                                                    (have contradiction
                                                      (absurd)
                                                      (by
                                                        (apply
                                                          some_none_absurd
                                                          (cons
                                                            (quote unit)
                                                            tail_index)))
                                                      (by
                                                        (exact
                                                          (absurd-elim
                                                            contradiction
                                                            (computes-to
                                                              (member
                                                                value
                                                                (cons head tail))
                                                              (quote :false)))))))))))))))))))))))))))))))
  )

(theorem elem_index_some_implies_member_true
  (forall value (is-value value)
    (forall list (is-list list)
      (forall index (is-list index)
        (implies
          (computes-to (elem-index value list) (some index))
          (computes-to (member value list) (quote :true))))))
  (by
    (intro value)
    (list-induction list
      (by
        (intro index)
        (intro elem_found)
        (have impossible_eq
          (computes-to (some index) none)
          (by
            (calc
              (some index)
              (==
                (elem-index value nil)
                (by
                  (exact (symm elem_found))))
              (==
                none
                (by
                  (exact (elem_index_nil value))))))
          (by
            (have contradiction
              (absurd)
              (by
                (apply some_none_absurd index))
              (by
                (exact
                  (absurd-elim
                    contradiction
                    (computes-to (member value nil) (quote :true)))))))))
      head
      tail
      induction_hypothesis
      (by
        (intro index)
        (intro elem_found)
        (have elem_branch_result
          (computes-to
            (if
              (value-eq value (head (cons head tail)))
              (some nil)
              ((lambda branch_option
                 (if
                   (is-some branch_option)
                   (some (cons (quote unit) (head (tail branch_option))))
                   none))
               (elem-index value (tail (cons head tail)))))
            (cons (quote :some) (cons index nil)))
          (by
            (calc
              (if
                (value-eq value (head (cons head tail)))
                (some nil)
                ((lambda branch_option
                   (if
                     (is-some branch_option)
                     (some (cons (quote unit) (head (tail branch_option))))
                     none))
                 (elem-index value (tail (cons head tail)))))
              (==
                (elem-index value (cons head tail))
                (by
                  (exact (symm (elem_index_cons_branch value head tail)))))
              (==
                (some index)
                (by
                  (exact elem_found)))
              (==
                (cons (quote :some) (cons index nil))
                (by
                  (eval)))))
          (by
            (have value_eq_bool
              (is-bool
                (value-eq value (head (cons head tail))))
              (proof
                (if-value-condition-bool
                  (assume elem_branch_result)))
              (by
                (or-elim value_eq_bool
                  values_equal_through_cons
                  (by
                    (have values_equal
                      (computes-to
                        (value-eq value head)
                        (quote :true))
                      (by
                        (calc
                          (value-eq value head)
                          (==
                            (value-eq
                              value
                              (head (cons head tail)))
                            (by
                              (eval)))
                          (==
                            (quote :true)
                            (by
                              (exact values_equal_through_cons)))))
                      (by
                        (apply member_cons_true value head tail))))
                  values_not_equal_through_cons
                  (by
                    (have values_not_equal
                      (computes-to
                        (value-eq value head)
                        (quote :false))
                      (by
                        (calc
                          (value-eq value head)
                          (==
                            (value-eq
                              value
                              (head (cons head tail)))
                            (by
                              (eval)))
                          (==
                            (quote :false)
                            (by
                              (exact values_not_equal_through_cons)))))
                      (by
                        (have branch_application
                          (computes-to
                            ((lambda branch_option
                               (if
                                 (is-some branch_option)
                                 (some (cons (quote unit) (head (tail branch_option))))
                                 none))
                             (elem-index value (tail (cons head tail))))
                            (cons (quote :some) (cons index nil)))
                          (by
                            (calc
                              ((lambda branch_option
                                 (if
                                   (is-some branch_option)
                                   (some (cons (quote unit) (head (tail branch_option))))
                                   none))
                               (elem-index value (tail (cons head tail))))
                              (==
                                (elem-index value (cons head tail))
                                (by
                                  (simpa only values_not_equal)))
                              (==
                                (some index)
                                (by
                                  (exact elem_found)))
                              (==
                                (cons (quote :some) (cons index nil))
                                (by
                                  (eval)))))
                          (by
                            (obtain tail_result tail_result_proof
                              (apply-value-argument
                                tail_result
                                (assume branch_application))
                              (by
                                (have tail_result_from_tail
                                  (computes-to
                                    (elem-index value tail)
                                    tail_result)
                                  (by
                                    (calc
                                      (elem-index value tail)
                                      (==
                                        (elem-index
                                          value
                                          (tail (cons head tail)))
                                        (by
                                          (eval)))
                                      (==
                                        tail_result
                                        (by
                                          (exact tail_result_proof)))))
                                  (by
                                    (specialize tail_option
                                      elem_index_computes_to_option
                                      value
                                      tail
                                      tail_result)
                                    (or-elim tail_option
                                      tail_none
                                      (by
                                        (have tail_missing
                                          (computes-to
                                            (elem-index value tail)
                                            none)
                                          (by
                                            (calc
                                              (elem-index value tail)
                                              (==
                                                tail_result
                                                (by
                                                  (exact
                                                    tail_result_from_tail)))
                                              (==
                                                none
                                                (by
                                                  (exact tail_none)))))
                                          (by
                                            (have cons_missing
                                              (computes-to
                                                (elem-index
                                                  value
                                                  (cons head tail))
                                                none)
                                              (by
                                                (apply
                                                  elem_index_cons_false_none
                                                  value
                                                  head
                                                  tail))
                                              (by
                                                (have impossible_eq
                                                  (computes-to (some index) none)
                                                  (by
                                                    (calc
                                                      (some index)
                                                      (==
                                                        (elem-index
                                                          value
                                                          (cons head tail))
                                                        (by
                                                          (exact
                                                            (symm
                                                              elem_found))))
                                                      (==
                                                        none
                                                        (by
                                                          (exact
                                                            cons_missing)))))
                                                  (by
                                                    (have contradiction
                                                      (absurd)
                                                      (by
                                                        (apply
                                                          some_none_absurd
                                                          index))
                                                      (by
                                                        (exact
                                                          (absurd-elim
                                                            contradiction
                                                            (computes-to
                                                              (member
                                                                value
                                                                (cons head tail))
                                                              (quote :true)))))))))))))
                                      tail_some_exists
                                      (by
                                        (obtain tail_index tail_some tail_some_exists)
                                        (have tail_found
                                          (computes-to
                                            (elem-index value tail)
                                            (some tail_index))
                                          (by
                                            (calc
                                              (elem-index value tail)
                                              (==
                                                tail_result
                                                (by
                                                  (exact
                                                    tail_result_from_tail)))
                                              (==
                                                (some tail_index)
                                                (by
                                                  (exact tail_some)))))
                                          (by
                                            (specialize tail_member_true
                                              induction_hypothesis
                                              tail_index)
                                            (calc
                                              (member value (cons head tail))
                                              (==
                                                (member value tail)
                                                (by
                                                  (apply
                                                    member_cons_false
                                                    value
                                                    head
                                                    tail)))
                                              (==
                                                (quote :true)
                                                (by
                                                  (exact
                                                    tail_member_true))))))))))))))))))))))))
  ))

(theorem find_computes_to_option
  (forall predicate (is-value predicate)
    (forall list (is-list list)
      (forall result (is-value result)
        (implies
          (computes-to (find predicate list) result)
          (or
            (computes-to result none)
            (exists value (is-value value)
              (computes-to result (some value))))))))
  (by
    (intro predicate)
    (list-induction list
      (by
        (intro result)
        (intro find_result)
        (left
          (by
            (calc
              result
              (==
                (find predicate nil)
                (by
                  (exact (symm find_result))))
              (==
                none
                (by
                  (exact (find_nil predicate))))))))
      head
      tail
      induction_hypothesis
      (by
        (intro result)
        (intro find_result)
        (have find_branch_result
          (computes-to
            (if
              (predicate (head (cons head tail)))
              (some (head (cons head tail)))
              (find predicate (tail (cons head tail))))
            result)
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
                result
                (by
                  (exact find_result)))))
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
                        (right
                          (by
                            (exists head
                              (by
                                (calc
                                  result
                                  (==
                                    (find predicate (cons head tail))
                                    (by
                                      (exact (symm find_result))))
                                  (==
                                    (some head)
                                    (by
                                      (apply
                                        find_cons_true
                                        predicate
                                        head
                                        tail)))))))))))
                  predicate_false_through_cons
                  (by
                    (have predicate_false
                      (computes-to (predicate head) (quote :false))
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
                        (have tail_find_result
                          (computes-to (find predicate tail) result)
                          (by
                            (calc
                              (find predicate tail)
                              (==
                                (find predicate (cons head tail))
                                (by
                                  (simpa only predicate_false)))
                              (==
                                result
                                (by
                                  (exact find_result)))))
                          (by
                            (specialize tail_option
                              induction_hypothesis
                              result)
                            (exact tail_option)))))))))))))))

(theorem any_false_implies_find_none
  (forall predicate (is-value predicate)
    (forall list (is-list list)
      (implies
        (computes-to (any predicate list) (quote :false))
        (computes-to (find predicate list) none))))
  (by
    (intro predicate)
    (list-induction list
      (by
        (intro any_false)
        (exact (find_nil predicate)))
      head
      tail
      induction_hypothesis
      (by
        (intro any_false)
        (specialize branch_parts any_cons_false_parts predicate head tail)
        (cases branch_parts predicate_false tail_any_false)
        (specialize tail_find_none induction_hypothesis)
        (calc
          (find predicate (cons head tail))
          (==
            (find predicate tail)
            (by
              (apply find_cons_false predicate head tail)))
          (==
            none
            (by
              (exact tail_find_none))))))))

(theorem any_true_implies_find_some
  (forall predicate (is-value predicate)
    (forall list (is-list list)
      (implies
        (computes-to (any predicate list) (quote :true))
        (exists value (is-value value)
          (computes-to (find predicate list) (some value))))))
  (by
    (intro predicate)
    (list-induction list
      (by
        (intro any_true)
        (have impossible_eq
          (computes-to (quote :false) (quote :true))
          (by
            (calc
              (quote :false)
              (==
                (any predicate nil)
                (by
                  (exact (symm (any_nil predicate)))))
              (==
                (quote :true)
                (by
                  (exact any_true)))))
          (by
            (exact
              (absurd-elim
                (distinct-outcomes impossible_eq)
                (exists value (is-value value)
                  (computes-to
                    (find predicate nil)
                    (some value))))))))
      head
      tail
      induction_hypothesis
      (by
        (intro any_true)
        (specialize branch_cases any_cons_true_cases predicate head tail)
        (or-elim branch_cases
          predicate_true
          (by
            (exists head
              (by
                (apply find_cons_true predicate head tail))))
          predicate_false_and_tail
          (by
            (cases predicate_false_and_tail predicate_false tail_any_true)
            (specialize tail_exists induction_hypothesis)
            (obtain found tail_found tail_exists)
            (exists found
              (by
                (calc
                  (find predicate (cons head tail))
                  (==
                    (find predicate tail)
                    (by
                      (apply find_cons_false predicate head tail)))
                  (==
                    (some found)
                    (by
                      (exact tail_found))))))))))))

(theorem find_none_implies_any_false
  (forall predicate (is-value predicate)
    (forall list (is-list list)
      (implies
        (computes-to (find predicate list) none)
        (computes-to (any predicate list) (quote :false)))))
  (by
    (intro predicate)
    (list-induction list
      (by
        (intro find_missing)
        (exact (any_nil predicate)))
      head
      tail
      induction_hypothesis
      (by
        (intro find_missing)
        (specialize branch_parts find_cons_none_parts predicate head tail)
        (cases branch_parts predicate_false tail_missing)
        (specialize tail_any_false induction_hypothesis)
        (calc
          (any predicate (cons head tail))
          (==
            (any predicate tail)
            (by
              (apply any_cons_false predicate head tail)))
          (==
            (quote :false)
            (by
              (exact tail_any_false))))))))

(theorem find_some_implies_any_true
  (forall predicate (is-value predicate)
    (forall list (is-list list)
      (forall found (is-value found)
        (implies
          (computes-to (find predicate list) (some found))
          (computes-to (any predicate list) (quote :true))))))
  (by
    (intro predicate)
    (list-induction list
      (by
        (intro found)
        (intro find_found)
        (have impossible_eq
          (computes-to none (some found))
          (by
            (calc
              none
              (==
                (find predicate nil)
                (by
                  (exact (symm (find_nil predicate)))))
              (==
                (some found)
                (by
                  (exact find_found)))))
          (by
            (have contradiction
              (absurd)
              (by
                (apply none_some_absurd found))
              (by
                (exact
                  (absurd-elim
                    contradiction
                    (computes-to
                      (any predicate nil)
                      (quote :true)))))))))
      head
      tail
      induction_hypothesis
      (by
        (intro found)
        (intro find_found)
        (specialize branch_cases
          find_cons_some_cases
          predicate
          head
          tail
          found)
        (or-elim branch_cases
          predicate_true
          (by
            (apply any_cons_true predicate head tail))
          predicate_false_and_tail
          (by
            (cases predicate_false_and_tail predicate_false tail_found)
            (specialize tail_any_true
              induction_hypothesis
              found)
            (calc
              (any predicate (cons head tail))
              (==
                (any predicate tail)
                (by
                  (apply any_cons_false predicate head tail)))
              (==
                (quote :true)
                (by
                  (exact tail_any_true))))))))))

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

(theorem split_at_computes_to_pair
  (forall count (is-list count)
    (forall list (is-list list)
      (exists prefix (is-list prefix)
        (exists suffix (is-list suffix)
          (computes-to
            (split-at count list)
            (cons prefix (cons suffix nil)))))))
  (by
    (intro count)
    (intro list)
    (obtain prefix prefix_proof
      (take_computes_to_list count list))
    (obtain suffix suffix_proof
      (drop_computes_to_list count list))
    (exists prefix
      (by
        (exists suffix
          (by
            (calc
              (split-at count list)
              (==
                (cons
                  (take count list)
                  (cons (drop count list) nil))
                (by
                  (exact split_at_def count list)))
              (==
                (cons prefix (cons suffix nil))
                (by
                  (simpa only prefix_proof suffix_proof)))))))))
)

(theorem split_at_first_take
  (forall count (is-list count)
    (forall list (is-list list)
      (computes-to
        (head (split-at count list))
        (take count list))))
  (by
    (intro count)
    (intro list)
    (obtain prefix prefix_proof
      (take_computes_to_list count list))
    (obtain suffix suffix_proof
      (drop_computes_to_list count list))
    (have split_pair
      (computes-to
        (split-at count list)
        (cons prefix (cons suffix nil)))
      (by
        (calc
          (split-at count list)
          (==
            (cons
              (take count list)
              (cons (drop count list) nil))
            (by
              (exact split_at_def count list)))
          (==
            (cons prefix (cons suffix nil))
            (by
              (simpa only prefix_proof suffix_proof)))))
      (by
        (calc
          (head (split-at count list))
          (==
            prefix
            (by
              (apply
                list_pair_first_from_computation
                (split-at count list)
                prefix
                suffix)))
          (==
            (take count list)
            (by
              (exact (symm prefix_proof))))))))
)

(theorem split_at_second_drop
  (forall count (is-list count)
    (forall list (is-list list)
      (computes-to
        (head (tail (split-at count list)))
        (drop count list))))
  (by
    (intro count)
    (intro list)
    (obtain prefix prefix_proof
      (take_computes_to_list count list))
    (obtain suffix suffix_proof
      (drop_computes_to_list count list))
    (have split_pair
      (computes-to
        (split-at count list)
        (cons prefix (cons suffix nil)))
      (by
        (calc
          (split-at count list)
          (==
            (cons
              (take count list)
              (cons (drop count list) nil))
            (by
              (exact split_at_def count list)))
          (==
            (cons prefix (cons suffix nil))
            (by
              (simpa only prefix_proof suffix_proof)))))
      (by
        (calc
          (head (tail (split-at count list)))
          (==
            suffix
            (by
              (apply
                list_pair_second_from_computation
                (split-at count list)
                prefix
                suffix)))
          (==
            (drop count list)
            (by
              (exact (symm suffix_proof))))))))
)

(theorem split_at_append
  (forall count (is-list count)
    (forall list (is-list list)
      (computes-to
        (append
          (head (split-at count list))
          (head (tail (split-at count list))))
        list)))
  (by
    (intro count)
    (intro list)
    (calc
      (append
        (head (split-at count list))
        (head (tail (split-at count list))))
      (==
        (append
          (take count list)
          (head (tail (split-at count list))))
        (by
          (simpa only (split_at_first_take count list))))
      (==
        (append (take count list) (drop count list))
        (by
          (simpa only (split_at_second_drop count list))))
      (==
        list
        (by
          (exact append_take_drop count list))))))

(theorem split_at_pair_eta
  (forall count (is-list count)
    (forall list (is-list list)
      (computes-to
        (split-at count list)
        (cons
          (head (split-at count list))
          (cons
            (head (tail (split-at count list)))
            nil)))))
  (by
    (intro count)
    (intro list)
    (obtain prefix prefix_proof
      (take_computes_to_list count list))
    (obtain suffix suffix_proof
      (drop_computes_to_list count list))
    (have split_pair
      (computes-to
        (split-at count list)
        (cons prefix (cons suffix nil)))
      (by
        (calc
          (split-at count list)
          (==
            (cons
              (take count list)
              (cons (drop count list) nil))
            (by
              (exact split_at_def count list)))
          (==
            (cons prefix (cons suffix nil))
            (by
              (simpa only prefix_proof suffix_proof)))))
      (by
        (have split_first
          (computes-to
            (head (split-at count list))
            prefix)
          (by
            (apply
              list_pair_first_from_computation
              (split-at count list)
              prefix
              suffix))
          (by
            (have split_second
              (computes-to
                (head (tail (split-at count list)))
                suffix)
              (by
                (apply
                  list_pair_second_from_computation
                  (split-at count list)
                  prefix
                  suffix))
              (by
                (calc
                  (split-at count list)
                  (==
                    (cons prefix (cons suffix nil))
                    (by
                      (exact split_pair)))
                  (==
                    (cons
                      (head (split-at count list))
                      (cons suffix nil))
                    (by
                      (simpa only (symm split_first))))
                  (==
                    (cons
                      (head (split-at count list))
                      (cons
                        (head (tail (split-at count list)))
                        nil))
                    (by
                      (simpa only (symm split_second)))))))))))
    ))

(theorem take_length
  (forall list (is-list list)
    (computes-to (take (length list) list) list))
  (by
    (list-induction list
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (obtain tail_length tail_length_proof
          (length_computes_to_list tail))
        (calc
          (take (length (cons head tail)) (cons head tail))
          (==
            (take
              (cons (quote unit) (length tail))
              (cons head tail))
            (by
              (simpa only (length_cons head tail))))
          (==
            (take
              (cons (quote unit) tail_length)
              (cons head tail))
            (by
              (simpa only tail_length_proof)))
          (==
            (cons head (take tail_length tail))
            (by
              (exact
                take_cons
                (quote unit)
                tail_length
                head
                tail)))
          (==
            (cons head (take (length tail) tail))
            (by
              (simpa only (symm tail_length_proof))))
          (==
            (cons head tail)
            (by
              (simpa only induction_hypothesis))))))))

(theorem drop_length
  (forall list (is-list list)
    (computes-to (drop (length list) list) nil))
  (by
    (list-induction list
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (obtain tail_length tail_length_proof
          (length_computes_to_list tail))
        (calc
          (drop (length (cons head tail)) (cons head tail))
          (==
            (drop
              (cons (quote unit) (length tail))
              (cons head tail))
            (by
              (simpa only (length_cons head tail))))
          (==
            (drop
              (cons (quote unit) tail_length)
              (cons head tail))
            (by
              (simpa only tail_length_proof)))
          (==
            (drop tail_length tail)
            (by
              (exact
                drop_cons
                (quote unit)
                tail_length
                head
                tail)))
          (==
            (drop (length tail) tail)
            (by
              (simpa only (symm tail_length_proof))))
          (==
            nil
            (by
              (exact induction_hypothesis))))))))

(theorem nth_zero_after_drop
  (forall count (is-list count)
    (forall list (is-list list)
      (forall head (is-value head)
        (forall tail (is-list tail)
          (implies
            (computes-to (drop count list) (cons head tail))
            (computes-to
              (nth nil (drop count list))
              (some head)))))))
  (by
    (intro count)
    (intro list)
    (intro head)
    (intro tail)
    (intro dropped)
    (calc
      (nth nil (drop count list))
      (==
        (nth nil (cons head tail))
        (by
          (simpa only dropped)))
      (==
        (some head)
        (by
          (exact nth_zero_cons head tail))))))

(theorem nth_after_split_at
  (forall count (is-list count)
    (forall list (is-list list)
      (forall head (is-value head)
        (forall tail (is-list tail)
          (implies
            (computes-to
              (head (tail (split-at count list)))
              (cons head tail))
            (computes-to
              (nth nil (head (tail (split-at count list))))
              (some head)))))))
  (by
    (intro count)
    (intro list)
    (intro head)
    (intro tail)
    (intro suffix)
    (calc
      (nth nil (head (tail (split-at count list))))
      (==
        (nth nil (cons head tail))
        (by
          (simpa only suffix)))
      (==
        (some head)
        (by
          (exact nth_zero_cons head tail))))))

(theorem nth_zero_after_split_at_zero_second
  (forall head (is-value head)
    (forall tail (is-list tail)
      (computes-to
        (nth
          nil
          (head (tail (split-at nil (cons head tail)))))
        (some head))))
  (by
    (intro head)
    (intro tail)
    (calc
      (nth
        nil
        (head (tail (split-at nil (cons head tail)))))
      (==
        (nth
          nil
          (head
            (tail
              (cons nil (cons (cons head tail) nil)))))
        (by
          (simpa only (split_at_zero (cons head tail)))))
      (==
        (nth nil (cons head tail))
        (by
          (eval)))
      (==
        (some head)
        (by
          (exact nth_zero_cons head tail))))))

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
