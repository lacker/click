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

(theorem member_computes_to_bool
  (forall value (is-value value)
    (forall list (is-list list)
      (forall result (is-value result)
        (implies
          (computes-to (member value list) result)
          (is-bool result)))))
  (by
    (intro value)
    (list-induction list
      (by
        (intro result)
        (intro member_result)
        (right
          (by
            (calc
              result
              (==
                (member value nil)
                (by
                  (exact (symm member_result))))
              (==
                (quote :false)
                (by
                  (exact (member_nil value))))))))
      head
      tail
      induction_hypothesis
      (by
        (intro result)
        (intro member_result)
        (have member_branch_result
          (computes-to
            (if
              (value-eq value (head (cons head tail)))
              (quote :true)
              (member value (tail (cons head tail))))
            result)
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
                result
                (by
                  (exact member_result)))))
          (by
            (have value_eq_bool
              (is-bool
                (value-eq value (head (cons head tail))))
              (proof
                (if-value-condition-bool
                  (assume member_branch_result)))
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
                        (left
                          (by
                            (calc
                              result
                              (==
                                (member value (cons head tail))
                                (by
                                  (exact (symm member_result))))
                              (==
                                (quote :true)
                                (by
                                  (apply
                                    member_cons_true
                                    value
                                    head
                                    tail)))))))))
                  values_distinct_through_cons
                  (by
                    (have values_distinct
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
                              (exact values_distinct_through_cons)))))
                      (by
                        (have tail_member_result
                          (computes-to (member value tail) result)
                          (by
                            (calc
                              (member value tail)
                              (==
                                (member value (cons head tail))
                                (by
                                  (simpa only values_distinct)))
                              (==
                                result
                                (by
                                  (exact member_result)))))
                          (by
                            (specialize tail_bool
                              induction_hypothesis
                              result)
                            (exact tail_bool)))))))))))))))

(theorem member_is_bool_for_comparable_value
  (forall value (is-value value)
    (implies
      (forall element (is-value element)
        (is-bool (value-eq value element)))
      (forall list (is-list list)
        (is-bool (member value list)))))
  (by
    (intro value)
    (intro value_eq_returns_bool)
    (list-induction list
      (by
        (right
          (by
            (exact member_nil value))))
      head
      tail
      induction_hypothesis
      (by
        (or-elim
          (value_eq_returns_bool head)
          values_equal
          (by
            (left
              (by
                (apply member_cons_true value head tail))))
          values_not_equal
          (by
            (or-elim
              induction_hypothesis
              tail_member_true
              (by
                (left
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
              tail_member_false
              (by
                (right
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
                          (exact tail_member_false)))))))))))))
  )

(theorem member_cons_or
  (forall value (is-value value)
    (implies
      (forall element (is-value element)
        (is-bool (value-eq value element)))
      (forall head (is-value head)
        (forall tail (is-list tail)
          (computes-to
            (member value (cons head tail))
            (or (value-eq value head) (member value tail)))))))
  (by
    (intro value)
    (intro value_eq_returns_bool)
    (intro head)
    (intro tail)
    (have tail_member_bool
      (is-bool (member value tail))
      (by
        (exact member_is_bool_for_comparable_value value tail))
      (by
        (or-elim
          (value_eq_returns_bool head)
          values_equal
          (by
            (have branch_true
              (computes-to
                (or (value-eq value head) (member value tail))
                (quote :true))
              (by
                (apply
                  or_true_left
                  (value-eq value head)
                  (member value tail)))
              (by
                (calc
                  (member value (cons head tail))
                  (==
                    (quote :true)
                    (by
                      (apply member_cons_true value head tail)))
                  (==
                    (or (value-eq value head) (member value tail))
                    (by
                      (exact (symm branch_true))))))))
          values_not_equal
          (by
            (have branch_false
              (computes-to
                (or (value-eq value head) (member value tail))
                (member value tail))
              (by
                (apply
                  or_false_left
                  (value-eq value head)
                  (member value tail)))
              (by
                (calc
                  (member value (cons head tail))
                  (==
                    (member value tail)
                    (by
                      (apply member_cons_false value head tail)))
                  (==
                    (or (value-eq value head) (member value tail))
                    (by
                      (exact (symm branch_false)))))))))))
  )
  )

(theorem member_append
  (forall value (is-value value)
    (implies
      (forall element (is-value element)
        (is-bool (value-eq value element)))
      (forall left (is-list left)
        (forall right (is-list right)
          (computes-to
            (member value (append left right))
            (or (member value left) (member value right)))))))
  (by
    (intro value)
    (intro value_eq_returns_bool)
    (list-induction left
      (by
        (intro right)
        (have right_member_bool
          (is-bool (member value right))
          (by
            (exact
              member_is_bool_for_comparable_value
              value
              right))
          (by
            (have nil_member_false
              (computes-to (member value nil) (quote :false))
              (by
                (exact member_nil value))
              (by
                (have branch_false
                  (computes-to
                    (or (member value nil) (member value right))
                    (member value right))
                  (by
                    (apply
                      or_false_left
                      (member value nil)
                      (member value right)))
                  (by
                    (calc
                      (member value (append nil right))
                      (==
                        (member value right)
                        (by
                          (simpa only (append_nil_returns_right right))))
                      (==
                        (or (member value nil) (member value right))
                        (by
                          (exact (symm branch_false))))))))))))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (obtain tail_right tail_right_proof
          (append_computes_to_list tail right))
        (have value_eq_bool
          (is-bool (value-eq value head))
          (by
            (exact value_eq_returns_bool head))
          (by
            (have tail_member_bool
              (is-bool (member value tail))
              (by
                (exact
                  member_is_bool_for_comparable_value
                  value
                  tail))
              (by
                (have right_member_bool
                  (is-bool (member value right))
                  (by
                    (exact
                      member_is_bool_for_comparable_value
                      value
                      right))
                  (by
                    (have current_member_step
                      (computes-to
                        (member value (cons head tail))
                        (or (value-eq value head) (member value tail)))
                      (by
                        (exact member_cons_or value head tail))
                      (by
                        (calc
                          (member
                            value
                            (append (cons head tail) right))
                          (==
                            (member
                              value
                              (cons head (append tail right)))
                            (by
                              (simpa only (append_cons head tail right))))
                          (==
                            (member value (cons head tail_right))
                            (by
                              (simpa only tail_right_proof)))
                          (==
                            (or
                              (value-eq value head)
                              (member value tail_right))
                            (by
                              (exact member_cons_or value head tail_right)))
                          (==
                            (or
                              (value-eq value head)
                              (member value (append tail right)))
                            (by
                              (simpa only (symm tail_right_proof))))
                          (==
                            (or
                              (value-eq value head)
                              (or
                                (member value tail)
                                (member value right)))
                            (by
                              (simpa only (induction_hypothesis right))))
                          (==
                            (or
                              (or
                                (value-eq value head)
                                (member value tail))
                              (member value right))
                            (by
                              (simpa
                                only
                                (or_assoc
                                  (value-eq value head)
                                  (member value tail)
                                  (member value right)))))
                          (==
                            (or
                              (member value (cons head tail))
                              (member value right))
                            (by
                              (rewrite (symm current_member_step))
                              (eval)))))))))))))))
  )

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

(theorem partition_second_reject
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
    (intro list)
    (exact partition_second_filter_false predicate list)))

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
            (partition_second_reject predicate list)))))))

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

(theorem elem_index_cons_some_cases
  (forall value (is-value value)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (forall index (is-list index)
          (implies
            (computes-to
              (elem-index value (cons head tail))
              (some index))
            (or
              (computes-to (value-eq value head) (quote :true))
              (exists tail_index (is-list tail_index)
                (and
                  (computes-to (value-eq value head) (quote :false))
                  (computes-to
                    (elem-index value tail)
                    (some tail_index))))))))))
  (by
    (intro value)
    (intro head)
    (intro tail)
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
                (left
                  (by
                    (calc
                      (value-eq value head)
                      (==
                        (value-eq value (head (cons head tail)))
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact values_equal_through_cons)))))))
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
                        (value-eq value (head (cons head tail)))
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
                             (some
                               (cons
                                 (quote unit)
                                 (head (tail branch_option))))
                             none))
                         (elem-index value (tail (cons head tail))))
                        (cons (quote :some) (cons index nil)))
                      (by
                        (calc
                          ((lambda branch_option
                             (if
                               (is-some branch_option)
                               (some
                                 (cons
                                   (quote unit)
                                   (head (tail branch_option))))
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
                                              (exact tail_result_from_tail)))
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
                                                        (symm elem_found))))
                                                  (==
                                                    none
                                                    (by
                                                      (exact cons_missing)))))
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
                                                        (or
                                                          (computes-to
                                                            (value-eq
                                                              value
                                                              head)
                                                            (quote :true))
                                                          (exists tail_index
                                                            (is-list
                                                              tail_index)
                                                            (and
                                                              (computes-to
                                                                (value-eq
                                                                  value
                                                                  head)
                                                                (quote :false))
                                                              (computes-to
                                                                (elem-index
                                                                  value
                                                                  tail)
                                                                (some
                                                                  tail_index))))))))))))))))
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
                                              (exact tail_result_from_tail)))
                                          (==
                                            (some tail_index)
                                            (by
                                              (exact tail_some)))))
                                      (by
                                        (right
                                          (by
                                            (exists tail_index
                                              (by
                                                (split
                                                  (by
                                                    (exact
                                                      values_not_equal))
                                                  (by
                                                    (exact
                                                      tail_found)))))))))))))))))))))))))
  )
  )

(theorem elem_index_append_left
  (forall value (is-value value)
    (forall left (is-list left)
      (forall right (is-list right)
        (forall index (is-list index)
          (implies
            (computes-to
              (elem-index value left)
              (some index))
            (computes-to
              (elem-index value (append left right))
              (some index)))))))
  (by
    (intro value)
    (list-induction left
      (by
        (intro right)
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
                  (exact elem_index_nil value)))))
          (by
            (have contradiction
              (absurd)
              (by
                (apply some_none_absurd index))
              (by
                (exact
                  (absurd-elim
                    contradiction
                    (computes-to
                      (elem-index value (append nil right))
                      (some index)))))))))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (intro index)
        (intro elem_found)
        (obtain tail_right tail_right_proof
          (append_computes_to_list tail right))
        (specialize cons_cases
          elem_index_cons_some_cases
          value
          head
          tail
          index)
        (or-elim cons_cases
          values_equal
          (by
            (have current_found
              (computes-to
                (elem-index value (cons head tail))
                (some nil))
              (by
                (apply elem_index_cons_true value head tail))
              (by
                (calc
                  (elem-index value (append (cons head tail) right))
                  (==
                    (elem-index value (cons head (append tail right)))
                    (by
                      (simpa only (append_cons head tail right))))
                  (==
                    (elem-index value (cons head tail_right))
                    (by
                      (simpa only tail_right_proof)))
                  (==
                    (some nil)
                    (by
                      (apply elem_index_cons_true value head tail_right)))
                  (==
                    (elem-index value (cons head tail))
                    (by
                      (exact (symm current_found))))
                  (==
                    (some index)
                    (by
                      (exact elem_found)))))))
          tail_found_exists
          (by
            (obtain tail_index tail_parts tail_found_exists)
            (cases tail_parts values_not_equal tail_found)
            (specialize tail_appended_found
              induction_hypothesis
              right
              tail_index)
            (have current_found
              (computes-to
                (elem-index value (cons head tail))
                (some (cons (quote unit) tail_index)))
              (by
                (apply
                  elem_index_cons_false_some
                  value
                  head
                  tail
                  tail_index))
              (by
                (calc
                  (elem-index value (append (cons head tail) right))
                  (==
                    (elem-index value (cons head (append tail right)))
                    (by
                      (simpa only (append_cons head tail right))))
                  (==
                    (elem-index value (cons head tail_right))
                    (by
                      (simpa only tail_right_proof)))
                  (==
                    ((lambda tail_result
                       (if
                         (is-some tail_result)
                         (some
                           (cons
                             (quote unit)
                             (head (tail tail_result))))
                         none))
                     (elem-index value tail_right))
                    (by
                      (simpa only
                        (elem_index_cons_false_branch
                          value
                          head
                          tail_right))))
                  (==
                    ((lambda tail_result
                       (if
                         (is-some tail_result)
                         (some
                           (cons
                             (quote unit)
                             (head (tail tail_result))))
                         none))
                     (elem-index value (append tail right)))
                    (by
                      (simpa only (symm tail_right_proof))))
                  (==
                    ((lambda tail_result
                       (if
                         (is-some tail_result)
                         (some
                           (cons
                             (quote unit)
                             (head (tail tail_result))))
                         none))
                     (some tail_index))
                    (by
                      (simpa only tail_appended_found)))
                  (==
                    (some (cons (quote unit) tail_index))
                    (by
                      (eval)))
                  (==
                    (elem-index value (cons head tail))
                    (by
                      (exact (symm current_found))))
                  (==
                    (some index)
                    (by
                      (exact elem_found)))))))))
  )
  )
  )

(theorem elem_index_cons_none_parts
  (forall value (is-value value)
    (forall head (is-value head)
      (forall tail (is-list tail)
        (implies
          (computes-to
            (elem-index value (cons head tail))
            none)
          (and
            (computes-to (value-eq value head) (quote :false))
            (computes-to (elem-index value tail) none))))))
  (by
    (intro value)
    (intro head)
    (intro tail)
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
                        (value-eq value (head (cons head tail)))
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact values_equal_through_cons)))))
                  (by
                    (have cons_found
                      (computes-to
                        (elem-index value (cons head tail))
                        (some nil))
                      (by
                        (apply elem_index_cons_true value head tail))
                      (by
                        (have impossible_eq
                          (computes-to (some nil) none)
                          (by
                            (calc
                              (some nil)
                              (==
                                (elem-index value (cons head tail))
                                (by
                                  (exact (symm cons_found))))
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
                                    (and
                                      (computes-to
                                        (value-eq value head)
                                        (quote :false))
                                      (computes-to
                                        (elem-index value tail)
                                        none)))))))))))))
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
                        (value-eq value (head (cons head tail)))
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
                             (some
                               (cons
                                 (quote unit)
                                 (head (tail branch_option))))
                             none))
                         (elem-index value (tail (cons head tail))))
                        (quote :none))
                      (by
                        (calc
                          ((lambda branch_option
                             (if
                               (is-some branch_option)
                               (some
                                 (cons
                                   (quote unit)
                                   (head (tail branch_option))))
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
                                              (exact tail_result_from_tail)))
                                          (==
                                            none
                                            (by
                                              (exact tail_none)))))
                                      (by
                                        (split
                                          (by
                                            (exact values_not_equal))
                                          (by
                                            (exact tail_missing))))))
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
                                              (exact tail_result_from_tail)))
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
                                                      (exact elem_missing)))))
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
                                                        (and
                                                          (computes-to
                                                            (value-eq
                                                              value
                                                              head)
                                                            (quote :false))
                                                          (computes-to
                                                            (elem-index
                                                              value
                                                              tail)
                                                            none)))))))))))))))))))))))))))))
  )

(theorem elem_index_append_right
  (forall value (is-value value)
    (forall left (is-list left)
      (forall right (is-list right)
        (forall index (is-list index)
          (implies
            (computes-to (elem-index value left) none)
            (implies
              (computes-to (elem-index value right) (some index))
              (computes-to
                (elem-index value (append left right))
                (some (append (length left) index)))))))))
  (by
    (intro value)
    (list-induction left
      (by
        (intro right)
        (intro index)
        (intro left_missing)
        (intro right_found)
        (calc
          (elem-index value (append nil right))
          (==
            (elem-index value right)
            (by
              (simpa only (append_nil_returns_right right))))
          (==
            (some index)
            (by
              (exact right_found)))
          (==
            (some (append nil index))
            (by
              (rewrite (symm (append_nil_returns_right index)))
              (eval)))
          (==
            (some (append (length nil) index))
            (by
              (rewrite (symm length_nil))
              (eval)))))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (intro index)
        (intro left_missing)
        (intro right_found)
        (specialize left_parts
          elem_index_cons_none_parts
          value
          head
          tail)
        (cases left_parts values_not_equal tail_missing)
        (specialize tail_appended_found
          induction_hypothesis
          right
          index)
        (obtain tail_right tail_right_proof
          (append_computes_to_list tail right))
        (obtain tail_length tail_length_proof
          (length_computes_to_list tail))
        (obtain shifted_index shifted_index_proof
          (append_computes_to_list tail_length index))
        (have tail_appended_shifted
          (computes-to
            (elem-index value (append tail right))
            (some shifted_index))
          (by
            (calc
              (elem-index value (append tail right))
              (==
                (some (append (length tail) index))
                (by
                  (exact tail_appended_found)))
              (==
                (some (append tail_length index))
                (by
                  (simpa only tail_length_proof)))
              (==
                (some shifted_index)
                (by
                  (simpa only shifted_index_proof))))))
        (calc
          (elem-index value (append (cons head tail) right))
          (==
            (elem-index value (cons head (append tail right)))
            (by
              (simpa only (append_cons head tail right))))
          (==
            (elem-index value (cons head tail_right))
            (by
              (simpa only tail_right_proof)))
          (==
            ((lambda tail_result
               (if
                 (is-some tail_result)
                 (some
                   (cons
                     (quote unit)
                     (head (tail tail_result))))
                 none))
             (elem-index value tail_right))
            (by
              (simpa only
                (elem_index_cons_false_branch
                  value
                  head
                  tail_right))))
          (==
            ((lambda tail_result
               (if
                 (is-some tail_result)
                 (some
                   (cons
                     (quote unit)
                     (head (tail tail_result))))
                 none))
             (elem-index value (append tail right)))
            (by
              (simpa only (symm tail_right_proof))))
          (==
            ((lambda tail_result
               (if
                 (is-some tail_result)
                 (some
                   (cons
                     (quote unit)
                     (head (tail tail_result))))
                 none))
             (some shifted_index))
            (by
              (simpa only tail_appended_shifted)))
          (==
            (some (cons (quote unit) shifted_index))
            (by
              (eval)))
          (==
            (some (cons (quote unit) (append tail_length index)))
            (by
              (simpa only (symm shifted_index_proof))))
          (==
            (some (append (cons (quote unit) tail_length) index))
            (by
              (simpa only
                (symm
                  (append_cons
                    (quote unit)
                    tail_length
                    index)))))
          (==
            (some
              (append
                (cons (quote unit) (length tail))
                index))
            (by
              (simpa only (symm tail_length_proof))))
          (==
            (some (append (length (cons head tail)) index))
            (by
              (simpa only (symm (length_cons head tail)))))))))
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

(theorem find_append
  (forall predicate (is-value predicate)
    (implies
      (forall value (is-value value)
        (is-bool (predicate value)))
      (forall left (is-list left)
        (forall right (is-list right)
          (computes-to
            (find predicate (append left right))
            (if
              (any predicate left)
              (find predicate left)
              (find predicate right)))))))
  (by
    (intro predicate)
    (intro predicate_returns_bool)
    (list-induction left
      (by
        (intro right)
        (simpa only
          (append_nil_returns_right right)
          (any_nil predicate)
          (if_false
            (find predicate nil)
            (find predicate right))))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (obtain tail_right tail_right_proof
          (append_computes_to_list tail right))
        (have predicate_bool
          (is-bool (predicate head))
          (by
            (exact predicate_returns_bool head))
          (by
            (or-elim predicate_bool
              predicate_true
              (by
                (have right_find_head
                  (computes-to
                    (find predicate (cons head tail_right))
                    (some head))
                  (by
                    (apply find_cons_true predicate head tail_right))
                  (by
                    (have left_find_head
                      (computes-to
                        (find predicate (cons head tail))
                        (some head))
                      (by
                        (apply find_cons_true predicate head tail))
                      (by
                        (have left_any_true
                          (computes-to
                            (any predicate (cons head tail))
                            (quote :true))
                          (by
                            (apply any_cons_true predicate head tail))
                          (by
                            (have if_left_true
                              (computes-to
                                (if
                                  (any predicate (cons head tail))
                                  (find predicate (cons head tail))
                                  (find predicate right))
                                (find predicate (cons head tail)))
                              (by
                                (apply
                                  if_condition_true
                                  (any predicate (cons head tail))
                                  (find predicate (cons head tail))
                                  (find predicate right)))
                              (by
                                (calc
                                  (find
                                    predicate
                                    (append (cons head tail) right))
                                  (==
                                    (find
                                      predicate
                                      (cons head (append tail right)))
                                    (by
                                      (simpa only (append_cons head tail right))))
                                  (==
                                    (find predicate (cons head tail_right))
                                    (by
                                      (simpa only tail_right_proof)))
                                  (==
                                    (some head)
                                    (by
                                      (exact right_find_head)))
                                  (==
                                    (find predicate (cons head tail))
                                    (by
                                      (exact (symm left_find_head))))
                                  (==
                                    (if
                                      (any predicate (cons head tail))
                                      (find predicate (cons head tail))
                                      (find predicate right))
                                    (by
                                      (exact (symm if_left_true))))))))))))))
              predicate_false
              (by
                (have right_find_tail
                  (computes-to
                    (find predicate (cons head tail_right))
                    (find predicate tail_right))
                  (by
                    (apply find_cons_false predicate head tail_right))
                  (by
                    (have left_find_tail
                      (computes-to
                        (find predicate (cons head tail))
                        (find predicate tail))
                      (by
                        (apply find_cons_false predicate head tail))
                      (by
                        (have left_any_tail
                          (computes-to
                            (any predicate (cons head tail))
                            (any predicate tail))
                          (by
                            (apply any_cons_false predicate head tail))
                          (by
                            (calc
                              (find
                                predicate
                                (append (cons head tail) right))
                              (==
                                (find
                                  predicate
                                  (cons head (append tail right)))
                                (by
                                  (simpa only (append_cons head tail right))))
                              (==
                                (find predicate (cons head tail_right))
                                (by
                                  (simpa only tail_right_proof)))
                              (==
                                (find predicate tail_right)
                                (by
                                  (exact right_find_tail)))
                              (==
                                (find predicate (append tail right))
                                (by
                                  (simpa only (symm tail_right_proof))))
                              (==
                                (if
                                  (any predicate tail)
                                  (find predicate tail)
                                  (find predicate right))
                                (by
                                  (simpa only (induction_hypothesis right))))
                              (==
                                (if
                                  (any predicate (cons head tail))
                                  (find predicate tail)
                                  (find predicate right))
                                (by
                                  (rewrite (symm left_any_tail))
                                  (eval)))
                              (==
                                (if
                                  (any predicate (cons head tail))
                                  (find predicate (cons head tail))
                                  (find predicate right))
                                (by
                                  (rewrite (symm left_find_tail))
                                  (eval))))))))))))))))))

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

(theorem map_compose
  (forall outer (is-value outer)
    (forall inner (is-value inner)
      (implies
        (forall input_value (is-value input_value)
          (exists inner_value (is-value inner_value)
            (computes-to (inner input_value) inner_value)))
        (implies
          (forall input_value (is-value input_value)
            (exists outer_value (is-value outer_value)
              (computes-to (outer input_value) outer_value)))
          (forall list (is-list list)
            (computes-to
              (map outer (map inner list))
              (map
                (lambda compose_value
                  (outer (inner compose_value)))
                list)))))))
  (by
    (intro outer)
    (intro inner)
    (intro inner_maps_values)
    (intro outer_maps_values)
    (list-induction list
      (by
        (calc
          (map outer (map inner nil))
          (==
            (map outer nil)
            (by
              (simpa only (map_nil inner))))
          (==
            nil
            (by
              (exact map_nil outer)))
          (==
            (map
              (lambda compose_value
                (outer (inner compose_value)))
              nil)
            (by
              (exact
                (symm
                  (map_nil
                    (lambda compose_value
                      (outer (inner compose_value))))))))))
      head
      tail
      induction_hypothesis
      (by
        (obtain inner_head inner_head_proof
          (inner_maps_values head))
        (obtain outer_head outer_head_proof
          (outer_maps_values inner_head))
        (obtain inner_tail inner_tail_proof
          (map_computes_to_list inner tail))
        (have composed_head
          (computes-to
            ((lambda compose_value
               (outer (inner compose_value)))
             head)
            outer_head)
          (by
            (calc
              ((lambda compose_value
                 (outer (inner compose_value)))
               head)
              (==
                (outer (inner head))
                (by
                  (eval)))
              (==
                (outer inner_head)
                (by
                  (simpa only inner_head_proof)))
              (==
                outer_head
                (by
                  (exact outer_head_proof)))))
          (by
            (calc
              (map outer (map inner (cons head tail)))
              (==
                (map outer (cons (inner head) (map inner tail)))
                (by
                  (simpa only (map_cons inner head tail))))
              (==
                (map outer (cons inner_head (map inner tail)))
                (by
                  (simpa only inner_head_proof)))
              (==
                (map outer (cons inner_head inner_tail))
                (by
                  (simpa only inner_tail_proof)))
              (==
                (cons (outer inner_head) (map outer inner_tail))
                (by
                  (exact map_cons outer inner_head inner_tail)))
              (==
                (cons outer_head (map outer inner_tail))
                (by
                  (simpa only outer_head_proof)))
              (==
                (cons outer_head (map outer (map inner tail)))
                (by
                  (simpa only (symm inner_tail_proof))))
              (==
                (cons
                  outer_head
                  (map
                    (lambda compose_value
                      (outer (inner compose_value)))
                    tail))
                (by
                  (simpa only induction_hypothesis)))
              (==
                (cons
                  ((lambda compose_value
                     (outer (inner compose_value)))
                   head)
                  (map
                    (lambda compose_value
                      (outer (inner compose_value)))
                    tail))
                (by
                  (simpa only (symm composed_head))))
              (==
                (map
                  (lambda compose_value
                    (outer (inner compose_value)))
                  (cons head tail))
                (by
                  (exact
                    (symm
                      (map_cons
                        (lambda compose_value
                          (outer (inner compose_value)))
                        head
                        tail))))))))))))

(theorem map_append
  (forall function (is-value function)
    (implies
      (forall value (is-value value)
        (exists mapped_value (is-value mapped_value)
          (computes-to (function value) mapped_value)))
      (forall left (is-list left)
        (forall right (is-list right)
          (computes-to
            (map function (append left right))
            (append (map function left) (map function right)))))))
  (by
    (intro function)
    (intro maps_values)
    (list-induction left
      (by
        (intro right)
        (obtain mapped_right mapped_right_proof
          (map_computes_to_list function right))
        (simpa only
          (append_nil_returns_right right)
          (map_nil function)
          mapped_right_proof
          (append_nil_returns_right mapped_right)))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (obtain mapped_head mapped_head_proof
          (maps_values head))
        (obtain tail_right tail_right_proof
          (append_computes_to_list tail right))
        (obtain mapped_tail mapped_tail_proof
          (map_computes_to_list function tail))
        (obtain mapped_right mapped_right_proof
          (map_computes_to_list function right))
        (calc
          (map function (append (cons head tail) right))
          (==
            (map function (cons head (append tail right)))
            (by
              (simpa only (append_cons head tail right))))
          (==
            (map function (cons head tail_right))
            (by
              (simpa only tail_right_proof)))
          (==
            (cons (function head) (map function tail_right))
            (by
              (exact map_cons function head tail_right)))
          (==
            (cons (function head) (map function (append tail right)))
            (by
              (simpa only (symm tail_right_proof))))
          (==
            (cons
              (function head)
              (append (map function tail) (map function right)))
            (by
              (simpa only (induction_hypothesis right))))
          (==
            (cons
              mapped_head
              (append (map function tail) (map function right)))
            (by
              (simpa only mapped_head_proof)))
          (==
            (cons mapped_head (append mapped_tail (map function right)))
            (by
              (simpa only mapped_tail_proof)))
          (==
            (cons mapped_head (append mapped_tail mapped_right))
            (by
              (simpa only mapped_right_proof)))
          (==
            (append
              (map function (cons head tail))
              (map function right))
            (by
              (simpa only
                (map_cons function head tail)
                mapped_head_proof
                mapped_tail_proof
                mapped_right_proof
                (append_cons mapped_head mapped_tail mapped_right)))))))))

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

(theorem fold_right_append
  (forall function (is-value function)
    (forall initial (is-value initial)
      (implies
        (forall value (is-value value)
          (forall accumulator (is-value accumulator)
            (exists folded_value (is-value folded_value)
              (computes-to
                (function value accumulator)
                folded_value))))
        (forall left (is-list left)
          (forall right (is-list right)
            (computes-to
              (fold-right function initial (append left right))
              (fold-right
                function
                (fold-right function initial right)
                left)))))))
  (by
    (intro function)
    (intro initial)
    (intro combines_values)
    (list-induction left
      (by
        (intro right)
        (obtain right_result right_result_proof
          (fold_right_computes_to_value function initial right))
        (calc
          (fold-right function initial (append nil right))
          (==
            (fold-right function initial right)
            (by
              (simpa only (append_nil_returns_right right))))
          (==
            right_result
            (by
              (exact right_result_proof)))
          (==
            (fold-right function right_result nil)
            (by
              (exact (symm (fold_right_nil function right_result)))))
          (==
            (fold-right
              function
              (fold-right function initial right)
              nil)
            (by
              (simpa only (symm right_result_proof))))))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (obtain tail_right tail_right_proof
          (append_computes_to_list tail right))
        (obtain right_result right_result_proof
          (fold_right_computes_to_value function initial right))
        (calc
          (fold-right
            function
            initial
            (append (cons head tail) right))
          (==
            (fold-right
              function
              initial
              (cons head (append tail right)))
            (by
              (simpa only (append_cons head tail right))))
          (==
            (fold-right function initial (cons head tail_right))
            (by
              (simpa only tail_right_proof)))
          (==
            (function head (fold-right function initial tail_right))
            (by
              (exact fold_right_cons function initial head tail_right)))
          (==
            (function
              head
              (fold-right
                function
                initial
                (append tail right)))
            (by
              (simpa only (symm tail_right_proof))))
          (==
            (function
              head
              (fold-right
                function
                (fold-right function initial right)
                tail))
            (by
              (simpa only (induction_hypothesis right))))
          (==
            (function
              head
              (fold-right function right_result tail))
            (by
              (simpa only right_result_proof)))
          (==
            (fold-right
              function
              right_result
              (cons head tail))
            (by
              (exact
                (symm
                  (fold_right_cons
                    function
                    right_result
                    head
                    tail)))))
          (==
            (fold-right
              function
              (fold-right function initial right)
              (cons head tail))
            (by
              (simpa only (symm right_result_proof)))))))))

(theorem fold_left_append
  (forall function (is-value function)
    (implies
      (forall accumulator (is-value accumulator)
        (forall value (is-value value)
          (exists folded_value (is-value folded_value)
            (computes-to
              (function accumulator value)
              folded_value))))
      (forall left (is-list left)
        (forall initial (is-value initial)
          (forall right (is-list right)
            (computes-to
              (fold-left function initial (append left right))
              (fold-left
                function
                (fold-left function initial left)
                right)))))))
  (by
    (intro function)
    (intro combines_values)
    (list-induction left
      (by
        (intro initial)
        (intro right)
        (simpa only
          (append_nil_returns_right right)
          (fold_left_nil function initial)))
      head
      tail
      induction_hypothesis
      (by
        (intro initial)
        (intro right)
        (obtain tail_right tail_right_proof
          (append_computes_to_list tail right))
        (obtain next_initial next_initial_proof
          (combines_values initial head))
        (calc
          (fold-left
            function
            initial
            (append (cons head tail) right))
          (==
            (fold-left
              function
              initial
              (cons head (append tail right)))
            (by
              (simpa only (append_cons head tail right))))
          (==
            (fold-left function initial (cons head tail_right))
            (by
              (simpa only tail_right_proof)))
          (==
            (fold-left
              function
              (function initial head)
              tail_right)
            (by
              (exact fold_left_cons function initial head tail_right)))
          (==
            (fold-left function next_initial tail_right)
            (by
              (simpa only next_initial_proof)))
          (==
            (fold-left
              function
              next_initial
              (append tail right))
            (by
              (simpa only (symm tail_right_proof))))
          (==
            (fold-left
              function
              (fold-left function next_initial tail)
              right)
            (by
              (simpa only
                (induction_hypothesis next_initial right))))
          (==
            (fold-left
              function
              (fold-left
                function
                (function initial head)
                tail)
              right)
            (by
              (simpa only (symm next_initial_proof))))
          (==
            (fold-left
              function
              (fold-left function initial (cons head tail))
              right)
            (by
              (simpa only
                (symm
                  (fold_left_cons
                    function
                    initial
                    head
                    tail))))))))))

(theorem fold_right_map
  (forall fold_function (is-value fold_function)
    (forall map_function (is-value map_function)
      (forall initial (is-value initial)
        (implies
          (forall value (is-value value)
            (exists mapped_value (is-value mapped_value)
              (computes-to
                (map_function value)
                mapped_value)))
          (implies
            (forall fold_value (is-value fold_value)
              (forall accumulator (is-value accumulator)
                (exists folded_value (is-value folded_value)
                  (computes-to
                    (fold_function fold_value accumulator)
                    folded_value))))
            (forall list (is-list list)
              (computes-to
                (fold-right
                  fold_function
                  initial
                  (map map_function list))
                (fold-right
                  (lambda composed_value
                    (lambda composed_accumulator
                      (fold_function
                        (map_function composed_value)
                        composed_accumulator)))
                  initial
                  list))))))))
  (by
    (intro fold_function)
    (intro map_function)
    (intro initial)
    (intro maps_values)
    (intro folds_values)
    (have composed_folds_values
      (forall composed_value (is-value composed_value)
        (forall composed_accumulator (is-value composed_accumulator)
          (exists composed_folded_value (is-value composed_folded_value)
            (computes-to
              ((lambda composed_input
                 (lambda composed_result
                   (fold_function
                     (map_function composed_input)
                     composed_result)))
               composed_value
               composed_accumulator)
              composed_folded_value))))
      (by
        (intro composed_value)
        (intro composed_accumulator)
        (obtain mapped_value mapped_value_proof
          (maps_values composed_value))
        (obtain folded_value folded_value_proof
          (folds_values mapped_value composed_accumulator))
        (exists folded_value
          (by
            (calc
              ((lambda composed_input
                 (lambda composed_result
                   (fold_function
                     (map_function composed_input)
                     composed_result)))
               composed_value
               composed_accumulator)
              (==
                (fold_function
                  (map_function composed_value)
                  composed_accumulator)
                (by
                  (eval)))
              (==
                (fold_function mapped_value composed_accumulator)
                (by
                  (simpa only mapped_value_proof)))
              (==
                folded_value
                (by
                  (exact folded_value_proof)))))))
      (by
        (list-induction list
          (by
            (simpa only
              (map_nil map_function)
              (fold_right_nil fold_function initial)
              (fold_right_nil
                (lambda composed_value
                  (lambda composed_accumulator
                    (fold_function
                      (map_function composed_value)
                      composed_accumulator)))
                initial)))
          head
          tail
          induction_hypothesis
          (by
            (obtain mapped_head mapped_head_proof
              (maps_values head))
            (obtain mapped_tail mapped_tail_proof
              (map_computes_to_list map_function tail))
            (obtain composed_tail_result composed_tail_result_proof
              (fold_right_computes_to_value
                (lambda composed_value
                  (lambda composed_accumulator
                    (fold_function
                      (map_function composed_value)
                      composed_accumulator)))
                initial
                tail))
            (calc
              (fold-right
                fold_function
                initial
                (map map_function (cons head tail)))
              (==
                (fold-right
                  fold_function
                  initial
                  (cons
                    (map_function head)
                    (map map_function tail)))
                (by
                  (simpa only (map_cons map_function head tail))))
              (==
                (fold-right
                  fold_function
                  initial
                  (cons mapped_head (map map_function tail)))
                (by
                  (simpa only mapped_head_proof)))
              (==
                (fold-right
                  fold_function
                  initial
                  (cons mapped_head mapped_tail))
                (by
                  (simpa only mapped_tail_proof)))
              (==
                (fold_function
                  mapped_head
                  (fold-right fold_function initial mapped_tail))
                (by
                  (exact
                    fold_right_cons
                    fold_function
                    initial
                    mapped_head
                    mapped_tail)))
              (==
                (fold_function
                  mapped_head
                  (fold-right
                    fold_function
                    initial
                    (map map_function tail)))
                (by
                  (simpa only (symm mapped_tail_proof))))
              (==
                (fold_function
                  mapped_head
                  (fold-right
                    (lambda composed_value
                      (lambda composed_accumulator
                        (fold_function
                          (map_function composed_value)
                          composed_accumulator)))
                    initial
                    tail))
                (by
                  (simpa only induction_hypothesis)))
              (==
                (fold_function
                  (map_function head)
                  (fold-right
                    (lambda composed_value
                      (lambda composed_accumulator
                        (fold_function
                          (map_function composed_value)
                          composed_accumulator)))
                    initial
                    tail))
                (by
                  (simpa only (symm mapped_head_proof))))
              (==
                (fold_function
                  (map_function head)
                  composed_tail_result)
                (by
                  (rewrite composed_tail_result_proof)
                  (eval)))
              (==
                ((lambda composed_value
                   (lambda composed_accumulator
                     (fold_function
                       (map_function composed_value)
                       composed_accumulator)))
                 head
                 composed_tail_result)
                (by
                  (exact
                    (symm
                      (eval-to
                        ((lambda composed_value
                           (lambda composed_accumulator
                             (fold_function
                               (map_function composed_value)
                               composed_accumulator)))
                         head
                         composed_tail_result)
                        (fold_function
                          (map_function head)
                          composed_tail_result))))))
              (==
                ((lambda composed_value
                   (lambda composed_accumulator
                     (fold_function
                       (map_function composed_value)
                       composed_accumulator)))
                 head
                 (fold-right
                   (lambda composed_value
                     (lambda composed_accumulator
                       (fold_function
                         (map_function composed_value)
                         composed_accumulator)))
                   initial
                   tail))
                (by
                  (rewrite (symm composed_tail_result_proof))
                  (eval)))
              (==
                (fold-right
                  (lambda composed_value
                    (lambda composed_accumulator
                      (fold_function
                        (map_function composed_value)
                        composed_accumulator)))
                  initial
                  (cons head tail))
                (by
                  (exact
                    (symm
                      (fold_right_cons
                        (lambda composed_value
                          (lambda composed_accumulator
                            (fold_function
                              (map_function composed_value)
                              composed_accumulator)))
                        initial
                        head
                        tail))))))))))))

(theorem fold_left_map
  (forall fold_function (is-value fold_function)
    (forall map_function (is-value map_function)
      (implies
        (forall value (is-value value)
          (exists mapped_value (is-value mapped_value)
            (computes-to
              (map_function value)
              mapped_value)))
        (implies
          (forall accumulator (is-value accumulator)
            (forall fold_value (is-value fold_value)
              (exists folded_value (is-value folded_value)
                (computes-to
                  (fold_function accumulator fold_value)
                  folded_value))))
          (forall list (is-list list)
            (forall initial (is-value initial)
              (computes-to
                (fold-left
                  fold_function
                  initial
                  (map map_function list))
                (fold-left
                  (lambda composed_accumulator
                    (lambda composed_value
                      (fold_function
                        composed_accumulator
                        (map_function composed_value))))
                  initial
                  list))))))))
  (by
    (intro fold_function)
    (intro map_function)
    (intro maps_values)
    (intro folds_values)
    (list-induction list
      (by
        (intro initial)
        (simpa only
          (map_nil map_function)
          (fold_left_nil fold_function initial)
          (fold_left_nil
            (lambda composed_accumulator
              (lambda composed_value
                (fold_function
                  composed_accumulator
                  (map_function composed_value))))
            initial)))
      head
      tail
      induction_hypothesis
      (by
        (intro initial)
        (obtain mapped_head mapped_head_proof
          (maps_values head))
        (obtain mapped_tail mapped_tail_proof
          (map_computes_to_list map_function tail))
        (obtain next_initial next_initial_proof
          (folds_values initial mapped_head))
        (calc
          (fold-left
            fold_function
            initial
            (map map_function (cons head tail)))
          (==
            (fold-left
              fold_function
              initial
              (cons
                (map_function head)
                (map map_function tail)))
            (by
              (simpa only (map_cons map_function head tail))))
          (==
            (fold-left
              fold_function
              initial
              (cons mapped_head (map map_function tail)))
            (by
              (simpa only mapped_head_proof)))
          (==
            (fold-left
              fold_function
              initial
              (cons mapped_head mapped_tail))
            (by
              (simpa only mapped_tail_proof)))
          (==
            (fold-left
              fold_function
              (fold_function initial mapped_head)
              mapped_tail)
            (by
              (exact
                fold_left_cons
                fold_function
                initial
                mapped_head
                mapped_tail)))
          (==
            (fold-left
              fold_function
              (fold_function initial mapped_head)
              (map map_function tail))
            (by
              (simpa only (symm mapped_tail_proof))))
          (==
            (fold-left
              fold_function
              next_initial
              (map map_function tail))
            (by
              (simpa only next_initial_proof)))
          (==
            (fold-left
              (lambda composed_accumulator
                (lambda composed_value
                  (fold_function
                    composed_accumulator
                    (map_function composed_value))))
              next_initial
              tail)
            (by
              (simpa only (induction_hypothesis next_initial))))
          (==
            (fold-left
              (lambda composed_accumulator
                (lambda composed_value
                  (fold_function
                    composed_accumulator
                    (map_function composed_value))))
              (fold_function initial mapped_head)
              tail)
            (by
              (rewrite (symm next_initial_proof))
              (eval)))
          (==
            (fold-left
              (lambda composed_accumulator
                (lambda composed_value
                  (fold_function
                    composed_accumulator
                    (map_function composed_value))))
              (fold_function initial (map_function head))
              tail)
            (by
              (rewrite (symm mapped_head_proof))
              (eval)))
          (==
            (fold-left
              (lambda composed_accumulator
                (lambda composed_value
                  (fold_function
                    composed_accumulator
                    (map_function composed_value))))
              ((lambda composed_accumulator
                 (lambda composed_value
                   (fold_function
                     composed_accumulator
                     (map_function composed_value))))
               initial
               head)
              tail)
            (by
              (rewrite
                (symm
                  (eval-to
                    ((lambda composed_accumulator
                       (lambda composed_value
                         (fold_function
                           composed_accumulator
                           (map_function composed_value))))
                     initial
                     head)
                    (fold_function initial (map_function head)))))
              (eval)))
          (==
            (fold-left
              (lambda composed_accumulator
                (lambda composed_value
                  (fold_function
                    composed_accumulator
                    (map_function composed_value))))
              initial
              (cons head tail))
            (by
              (exact
                (symm
                  (fold_left_cons
                    (lambda composed_accumulator
                      (lambda composed_value
                        (fold_function
                          composed_accumulator
                          (map_function composed_value))))
                    initial
                    head
                    tail))))))))))

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

(theorem concat_map_append
  (forall function (is-value function)
    (implies
      (forall value (is-value value)
        (computes-to-list mapped_list (function value)))
      (forall left (is-list left)
        (forall right (is-list right)
          (computes-to
            (concat-map function (append left right))
            (append
              (concat-map function left)
              (concat-map function right)))))))
  (by
    (intro function)
    (intro maps_values_to_lists)
    (list-induction left
      (by
        (intro right)
        (obtain mapped_right mapped_right_proof
          (concat_map_computes_to_list function right))
        (simpa only
          (append_nil_returns_right right)
          (concat_map_nil function)
          mapped_right_proof
          (append_nil_returns_right mapped_right)))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (obtain mapped_head mapped_head_proof
          (maps_values_to_lists head))
        (obtain tail_right tail_right_proof
          (append_computes_to_list tail right))
        (obtain mapped_tail mapped_tail_proof
          (concat_map_computes_to_list function tail))
        (obtain mapped_right mapped_right_proof
          (concat_map_computes_to_list function right))
        (calc
          (concat-map function (append (cons head tail) right))
          (==
            (concat-map function (cons head (append tail right)))
            (by
              (simpa only (append_cons head tail right))))
          (==
            (concat-map function (cons head tail_right))
            (by
              (simpa only tail_right_proof)))
          (==
            (append (function head) (concat-map function tail_right))
            (by
              (exact concat_map_cons function head tail_right)))
          (==
            (append
              (function head)
              (concat-map function (append tail right)))
            (by
              (simpa only (symm tail_right_proof))))
          (==
            (append
              (function head)
              (append
                (concat-map function tail)
                (concat-map function right)))
            (by
              (simpa only (induction_hypothesis right))))
          (==
            (append
              mapped_head
              (append
                (concat-map function tail)
                (concat-map function right)))
            (by
              (simpa only mapped_head_proof)))
          (==
            (append
              mapped_head
              (append mapped_tail (concat-map function right)))
            (by
              (simpa only mapped_tail_proof)))
          (==
            (append mapped_head (append mapped_tail mapped_right))
            (by
              (simpa only mapped_right_proof)))
          (==
            (append (append mapped_head mapped_tail) mapped_right)
            (by
              (exact
                (symm (append_assoc mapped_head mapped_tail mapped_right)))))
          (==
            (append
              (concat-map function (cons head tail))
              (concat-map function right))
            (by
              (simpa only
                (concat_map_cons function head tail)
                mapped_head_proof
                mapped_tail_proof
                mapped_right_proof))))))))

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

(theorem drop_drop
  (forall left (is-list left)
    (forall right (is-list right)
      (forall list (is-list list)
        (computes-to
          (drop right (drop left list))
          (drop (append left right) list)))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro list)
        (have dropped_zero
          (computes-to (drop nil list) list)
          (by
            (exact drop_zero list))
          (by
            (have append_nil_right
              (computes-to (append nil right) right)
              (by
                (exact append_nil_returns_right right))
              (by
                (specialize append_count_forward
                  drop_congr_count_computation
                  (append nil right)
                  right
                  list)
                (calc
                  (drop right (drop nil list))
                  (==
                    (drop right list)
                    (by
                      (exact
                        drop_congr_list_computation
                        right
                        (drop nil list)
                        list)))
                  (==
                    (drop (append nil right) list)
                    (by
                      (exact
                        (symm append_count_forward))))))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (intro right)
        (list-induction list
          (by
            (obtain appended_tail appended_tail_proof
              (append_computes_to_list left_tail right))
            (have appended_count_shape
              (computes-to
                (append (cons left_head left_tail) right)
                (cons left_head appended_tail))
              (by
                (calc
                  (append (cons left_head left_tail) right)
                  (==
                    (cons left_head (append left_tail right))
                    (by
                      (exact
                        append_cons
                        left_head
                        left_tail
                        right)))
                  (==
                    (cons left_head appended_tail)
                    (by
                      (simpa only appended_tail_proof)))))
              (by
                (have dropped_left
                  (computes-to
                    (drop (cons left_head left_tail) nil)
                    nil)
                  (by
                    (exact drop_nil (cons left_head left_tail)))
                  (by
                    (specialize appended_count_forward
                      drop_congr_count_computation
                      (append (cons left_head left_tail) right)
                      (cons left_head appended_tail)
                      nil)
                    (calc
                      (drop right (drop (cons left_head left_tail) nil))
                      (==
                        (drop right nil)
                        (by
                          (exact
                            drop_congr_list_computation
                            right
                            (drop (cons left_head left_tail) nil)
                            nil)))
                      (==
                        nil
                        (by
                          (exact drop_nil right)))
                      (==
                        (drop (cons left_head appended_tail) nil)
                        (by
                          (exact
                            (symm
                              (drop_nil
                                (cons left_head appended_tail))))))
                      (==
                        (drop
                          (append (cons left_head left_tail) right)
                          nil)
                        (by
                          (exact
                            (symm appended_count_forward))))))))))
          head
          tail
          list_induction_hypothesis
          (by
            (obtain appended_tail appended_tail_proof
              (append_computes_to_list left_tail right))
            (obtain dropped_tail dropped_tail_proof
              (drop_computes_to_list left_tail tail))
            (have appended_count_shape
              (computes-to
                (append (cons left_head left_tail) right)
                (cons left_head appended_tail))
              (by
                (calc
                  (append (cons left_head left_tail) right)
                  (==
                    (cons left_head (append left_tail right))
                    (by
                      (exact
                        append_cons
                        left_head
                        left_tail
                        right)))
                  (==
                    (cons left_head appended_tail)
                    (by
                      (simpa only appended_tail_proof)))))
              (by
                (have dropped_left_value
                  (computes-to
                    (drop
                      (cons left_head left_tail)
                      (cons head tail))
                    dropped_tail)
                  (by
                    (calc
                      (drop
                        (cons left_head left_tail)
                        (cons head tail))
                      (==
                        (drop left_tail tail)
                        (by
                          (exact
                            drop_cons
                            left_head
                            left_tail
                            head
                            tail)))
                      (==
                        dropped_tail
                          (by
                            (exact dropped_tail_proof)))))
                  (by
                    (specialize dropped_tail_forward
                      drop_congr_list_computation
                      right
                      (drop left_tail tail)
                      dropped_tail)
                    (specialize appended_count_forward
                      drop_congr_count_computation
                      (append (cons left_head left_tail) right)
                      (cons left_head appended_tail)
                      (cons head tail))
                    (calc
                      (drop
                        right
                        (drop
                          (cons left_head left_tail)
                          (cons head tail)))
                      (==
                        (drop right dropped_tail)
                        (by
                          (exact
                            drop_congr_list_computation
                            right
                            (drop
                              (cons left_head left_tail)
                              (cons head tail))
                            dropped_tail)))
                      (==
                        (drop right (drop left_tail tail))
                        (by
                          (exact
                            (symm dropped_tail_forward))))
                      (==
                        (drop (append left_tail right) tail)
                        (by
                          (exact (induction_hypothesis right tail))))
                      (==
                        (drop appended_tail tail)
                        (by
                          (exact
                            drop_congr_count_computation
                            (append left_tail right)
                            appended_tail
                            tail)))
                      (==
                        (drop
                          (cons left_head appended_tail)
                          (cons head tail))
                        (by
                          (exact
                            (symm
                              (drop_cons
                                left_head
                                appended_tail
                                head
                                tail)))))
                      (==
                        (drop
                          (append (cons left_head left_tail) right)
                          (cons head tail))
                        (by
                          (exact
                            (symm appended_count_forward)))))))))))
  )
)
)
)

(theorem take_drop_commute
  (forall take_count (is-list take_count)
    (forall drop_count (is-list drop_count)
      (forall list (is-list list)
        (computes-to
          (take take_count (drop drop_count list))
          (drop
            drop_count
            (take (append drop_count take_count) list))))))
  (by
    (intro take_count)
    (list-induction drop_count
      (by
        (intro list)
        (obtain taken_list taken_list_proof
          (take_computes_to_list take_count list))
        (have append_nil_right
          (computes-to (append nil take_count) take_count)
          (by
            (exact append_nil_returns_right take_count))
          (by
            (have take_appended
              (computes-to
                (take (append nil take_count) list)
                taken_list)
              (by
                (specialize take_count_forward
                  take_congr_count_computation
                  (append nil take_count)
                  take_count
                  list)
                (calc
                  (take (append nil take_count) list)
                  (==
                    (take take_count list)
                    (by
                      (exact take_count_forward)))
                  (==
                    taken_list
                    (by
                      (exact taken_list_proof)))))
              (by
                (have dropped_zero
                  (computes-to (drop nil list) list)
                  (by
                    (exact drop_zero list))
                  (by
                    (specialize rhs_drop_forward
                      drop_congr_list_computation
                      nil
                      (take (append nil take_count) list)
                      taken_list)
                    (calc
                      (take take_count (drop nil list))
                      (==
                        (take take_count list)
                        (by
                          (exact
                            take_congr_list_computation
                            take_count
                            (drop nil list)
                            list)))
                      (==
                        taken_list
                        (by
                          (exact taken_list_proof)))
                      (==
                        (drop nil taken_list)
                        (by
                          (exact (symm (drop_zero taken_list)))))
                      (==
                        (drop
                          nil
                          (take (append nil take_count) list))
                        (by
                          (exact (symm rhs_drop_forward))))))))))))
      drop_head
      drop_tail
      induction_hypothesis
      (by
        (list-induction list
          (by
            (obtain appended_tail appended_tail_proof
              (append_computes_to_list drop_tail take_count))
            (have appended_count_shape
              (computes-to
                (append (cons drop_head drop_tail) take_count)
                (cons drop_head appended_tail))
              (by
                (calc
                  (append (cons drop_head drop_tail) take_count)
                  (==
                    (cons drop_head (append drop_tail take_count))
                    (by
                      (exact
                        append_cons
                        drop_head
                        drop_tail
                        take_count)))
                  (==
                    (cons drop_head appended_tail)
                    (by
                      (simpa only appended_tail_proof)))))
              (by
                (have take_appended_nil
                  (computes-to
                    (take
                      (append (cons drop_head drop_tail) take_count)
                      nil)
                    nil)
                  (by
                    (specialize take_count_forward
                      take_congr_count_computation
                      (append (cons drop_head drop_tail) take_count)
                      (cons drop_head appended_tail)
                      nil)
                    (calc
                      (take
                        (append (cons drop_head drop_tail) take_count)
                        nil)
                      (==
                        (take (cons drop_head appended_tail) nil)
                        (by
                          (exact take_count_forward)))
                      (==
                        nil
                        (by
                          (exact
                            take_nil
                            (cons drop_head appended_tail))))))
                  (by
                    (specialize rhs_drop_forward
                      drop_congr_list_computation
                      (cons drop_head drop_tail)
                      (take
                        (append (cons drop_head drop_tail) take_count)
                        nil)
                      nil)
                    (have dropped_nil
                      (computes-to
                        (drop (cons drop_head drop_tail) nil)
                        nil)
                      (by
                        (exact
                          drop_nil
                          (cons drop_head drop_tail)))
                      (by
                        (calc
                          (take
                            take_count
                            (drop (cons drop_head drop_tail) nil))
                          (==
                            (take take_count nil)
                            (by
                              (exact
                                take_congr_list_computation
                                take_count
                                (drop (cons drop_head drop_tail) nil)
                                nil)))
                          (==
                            nil
                            (by
                              (exact take_nil take_count)))
                          (==
                            (drop (cons drop_head drop_tail) nil)
                            (by
                              (exact
                                (symm
                                  (drop_nil
                                    (cons drop_head drop_tail))))))
                          (==
                            (drop
                              (cons drop_head drop_tail)
                              (take
                                (append
                                  (cons drop_head drop_tail)
                                  take_count)
                                nil))
                            (by
                              (exact (symm rhs_drop_forward))))))))))))
          head
          tail
          list_induction_hypothesis
          (by
            (obtain appended_tail appended_tail_proof
              (append_computes_to_list drop_tail take_count))
            (obtain dropped_tail dropped_tail_proof
              (drop_computes_to_list drop_tail tail))
            (obtain taken_tail taken_tail_proof
              (take_computes_to_list appended_tail tail))
            (have appended_count_shape
              (computes-to
                (append (cons drop_head drop_tail) take_count)
                (cons drop_head appended_tail))
              (by
                (calc
                  (append (cons drop_head drop_tail) take_count)
                  (==
                    (cons drop_head (append drop_tail take_count))
                    (by
                      (exact
                        append_cons
                        drop_head
                        drop_tail
                        take_count)))
                  (==
                    (cons drop_head appended_tail)
                    (by
                      (simpa only appended_tail_proof)))))
              (by
                (have dropped_left_value
                  (computes-to
                    (drop
                      (cons drop_head drop_tail)
                      (cons head tail))
                    dropped_tail)
                  (by
                    (calc
                      (drop
                        (cons drop_head drop_tail)
                        (cons head tail))
                      (==
                        (drop drop_tail tail)
                        (by
                          (exact
                            drop_cons
                            drop_head
                            drop_tail
                            head
                            tail)))
                      (==
                        dropped_tail
                        (by
                          (exact dropped_tail_proof)))))
                  (by
                    (have take_tail_open
                      (computes-to
                        (take (append drop_tail take_count) tail)
                        taken_tail)
                      (by
                        (specialize take_tail_count_forward
                          take_congr_count_computation
                          (append drop_tail take_count)
                          appended_tail
                          tail)
                        (calc
                          (take (append drop_tail take_count) tail)
                          (==
                            (take appended_tail tail)
                            (by
                              (exact take_tail_count_forward)))
                          (==
                            taken_tail
                            (by
                              (exact taken_tail_proof)))))
                      (by
                        (have taken_whole_value
                          (computes-to
                            (take
                              (append
                                (cons drop_head drop_tail)
                                take_count)
                              (cons head tail))
                            (cons head taken_tail))
                          (by
                            (specialize take_count_forward
                              take_congr_count_computation
                              (append
                                (cons drop_head drop_tail)
                                take_count)
                              (cons drop_head appended_tail)
                              (cons head tail))
                            (calc
                              (take
                                (append
                                  (cons drop_head drop_tail)
                                  take_count)
                                (cons head tail))
                              (==
                                (take
                                  (cons drop_head appended_tail)
                                  (cons head tail))
                                (by
                                  (exact take_count_forward)))
                              (==
                                (cons head (take appended_tail tail))
                                (by
                                  (exact
                                    take_cons
                                    drop_head
                                    appended_tail
                                    head
                                    tail)))
                              (==
                                (cons head taken_tail)
                                (by
                                  (simpa only taken_tail_proof)))))
                          (by
                            (specialize dropped_tail_forward
                              take_congr_list_computation
                              take_count
                              (drop drop_tail tail)
                              dropped_tail)
                            (specialize drop_tail_taken_forward
                              drop_congr_list_computation
                              drop_tail
                              (take
                                (append drop_tail take_count)
                                tail)
                              taken_tail)
                            (specialize rhs_drop_forward
                              drop_congr_list_computation
                              (cons drop_head drop_tail)
                              (take
                                (append
                                  (cons drop_head drop_tail)
                                  take_count)
                                (cons head tail))
                              (cons head taken_tail))
                            (calc
                              (take
                                take_count
                                (drop
                                  (cons drop_head drop_tail)
                                  (cons head tail)))
                              (==
                                (take take_count dropped_tail)
                                (by
                                  (exact
                                    take_congr_list_computation
                                    take_count
                                    (drop
                                      (cons drop_head drop_tail)
                                      (cons head tail))
                                    dropped_tail)))
                              (==
                                (take
                                  take_count
                                  (drop drop_tail tail))
                                (by
                                  (exact
                                    (symm
                                      dropped_tail_forward))))
                              (==
                                (drop
                                  drop_tail
                                  (take
                                    (append drop_tail take_count)
                                    tail))
                                (by
                                  (exact
                                    (induction_hypothesis tail))))
                              (==
                                (drop drop_tail taken_tail)
                                (by
                                  (exact drop_tail_taken_forward)))
                              (==
                                (drop
                                  (cons drop_head drop_tail)
                                  (cons head taken_tail))
                                (by
                                  (exact
                                    (symm
                                      (drop_cons
                                        drop_head
                                        drop_tail
                                        head
                                        taken_tail)))))
                              (==
                                (drop
                                  (cons drop_head drop_tail)
                                  (take
                                    (append
                                      (cons drop_head drop_tail)
                                      take_count)
                                    (cons head tail)))
                                (by
                                  (exact
                                    (symm rhs_drop_forward))))))))))))))))
  )
)
)

(theorem map_take
  (forall function (is-value function)
    (implies
      (forall value (is-value value)
        (exists mapped_value (is-value mapped_value)
          (computes-to (function value) mapped_value)))
      (forall count (is-list count)
        (forall list (is-list list)
          (computes-to
            (map function (take count list))
            (take count (map function list)))))))
  (by
    (intro function)
    (intro maps_values)
    (list-induction count
      (by
        (intro list)
        (obtain mapped_list mapped_list_proof
          (map_computes_to_list function list))
        (calc
          (map function (take nil list))
          (==
            (map function nil)
            (by
              (simpa only (take_zero list))))
          (==
            nil
            (by
              (exact map_nil function)))
          (==
            (take nil mapped_list)
            (by
              (exact (symm (take_zero mapped_list)))))
          (==
            (take nil (map function list))
            (by
              (simpa only (symm mapped_list_proof))))))
      count_head
      count_tail
      count_induction_hypothesis
      (by
        (list-induction list
          (by
            (calc
              (map function (take (cons count_head count_tail) nil))
              (==
                (map function nil)
                (by
                  (simpa only (take_nil (cons count_head count_tail)))))
              (==
                nil
                (by
                  (exact map_nil function)))
              (==
                (take (cons count_head count_tail) (map function nil))
                (by
                  (simpa only
                    (map_nil function)
                    (take_nil (cons count_head count_tail)))))))
          head
          tail
          list_induction_hypothesis
          (by
            (obtain mapped_head mapped_head_proof
              (maps_values head))
            (obtain taken_tail taken_tail_proof
              (take_computes_to_list count_tail tail))
            (obtain mapped_tail mapped_tail_proof
              (map_computes_to_list function tail))
            (calc
              (map
                function
                (take
                  (cons count_head count_tail)
                  (cons head tail)))
              (==
                (map function (cons head (take count_tail tail)))
                (by
                  (simpa only
                    (take_cons count_head count_tail head tail))))
              (==
                (map function (cons head taken_tail))
                (by
                  (simpa only taken_tail_proof)))
              (==
                (cons (function head) (map function taken_tail))
                (by
                  (exact map_cons function head taken_tail)))
              (==
                (cons mapped_head (map function taken_tail))
                (by
                  (simpa only mapped_head_proof)))
              (==
                (cons
                  mapped_head
                  (map function (take count_tail tail)))
                (by
                  (simpa only (symm taken_tail_proof))))
              (==
                (cons
                  mapped_head
                  (take count_tail (map function tail)))
                (by
                  (simpa only (count_induction_hypothesis tail))))
              (==
                (cons mapped_head (take count_tail mapped_tail))
                (by
                  (simpa only mapped_tail_proof)))
              (==
                (take
                  (cons count_head count_tail)
                  (map function (cons head tail)))
                (by
                  (simpa only
                    (map_cons function head tail)
                    mapped_head_proof
                    mapped_tail_proof
                    (take_cons
                      count_head
                      count_tail
                      mapped_head
                      mapped_tail)))))))))))

(theorem map_drop
  (forall function (is-value function)
    (implies
      (forall value (is-value value)
        (exists mapped_value (is-value mapped_value)
          (computes-to (function value) mapped_value)))
      (forall count (is-list count)
        (forall list (is-list list)
          (computes-to
            (map function (drop count list))
            (drop count (map function list)))))))
  (by
    (intro function)
    (intro maps_values)
    (list-induction count
      (by
        (intro list)
        (obtain mapped_list mapped_list_proof
          (map_computes_to_list function list))
        (calc
          (map function (drop nil list))
          (==
            (map function list)
            (by
              (simpa only (drop_zero list))))
          (==
            mapped_list
            (by
              (exact mapped_list_proof)))
          (==
            (drop nil mapped_list)
            (by
              (exact (symm (drop_zero mapped_list)))))
          (==
            (drop nil (map function list))
            (by
              (simpa only (symm mapped_list_proof))))))
      count_head
      count_tail
      count_induction_hypothesis
      (by
        (list-induction list
          (by
            (calc
              (map function (drop (cons count_head count_tail) nil))
              (==
                (map function nil)
                (by
                  (simpa only (drop_nil (cons count_head count_tail)))))
              (==
                nil
                (by
                  (exact map_nil function)))
              (==
                (drop (cons count_head count_tail) (map function nil))
                (by
                  (simpa only
                    (map_nil function)
                    (drop_nil (cons count_head count_tail)))))))
          head
          tail
          list_induction_hypothesis
          (by
            (obtain mapped_head mapped_head_proof
              (maps_values head))
            (obtain mapped_tail mapped_tail_proof
              (map_computes_to_list function tail))
            (calc
              (map
                function
                (drop
                  (cons count_head count_tail)
                  (cons head tail)))
              (==
                (map function (drop count_tail tail))
                (by
                  (simpa only
                    (drop_cons count_head count_tail head tail))))
              (==
                (drop count_tail (map function tail))
                (by
                  (simpa only (count_induction_hypothesis tail))))
              (==
                (drop count_tail mapped_tail)
                (by
                  (simpa only mapped_tail_proof)))
              (==
                (drop
                  (cons count_head count_tail)
                  (map function (cons head tail)))
                (by
                  (simpa only
                    (map_cons function head tail)
                    mapped_head_proof
                    mapped_tail_proof
                    (drop_cons
                      count_head
                      count_tail
                      mapped_head
                      mapped_tail)))))))))))

(theorem option_map_nth
  (forall function (is-value function)
    (implies
      (forall value (is-value value)
        (exists mapped_value (is-value mapped_value)
          (computes-to (function value) mapped_value)))
      (forall index (is-list index)
        (forall list (is-list list)
          (computes-to
            (option-map function (nth index list))
            (nth index (map function list)))))))
  (by
    (intro function)
    (intro maps_values)
    (list-induction index
      (by
        (list-induction list
          (by
            (simpa only
              nth_zero_nil
              (option_map_none function)
              (map_nil function)))
          head
          tail
          list_induction_hypothesis
          (by
            (obtain mapped_head mapped_head_proof
              (maps_values head))
            (obtain mapped_tail mapped_tail_proof
              (map_computes_to_list function tail))
            (have mapped_list
              (computes-to
                (map function (cons head tail))
                (cons mapped_head mapped_tail))
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
                      (simpa only mapped_tail_proof)))))
              (by
                (calc
                  (option-map function (nth nil (cons head tail)))
                  (==
                    (option-map function (some head))
                    (by
                      (simpa only (nth_zero_cons head tail))))
                  (==
                    (some mapped_head)
                    (by
                      (apply option_map_some function head mapped_head)))
                  (==
                    (nth nil (cons mapped_head mapped_tail))
                    (by
                      (exact
                        (symm (nth_zero_cons mapped_head mapped_tail)))))
                  (==
                    (nth nil (map function (cons head tail)))
                    (by
                      (simpa only (symm mapped_list))))))))))
      index_head
      index_tail
      induction_hypothesis
      (by
        (list-induction list
          (by
            (simpa only
              (nth_cons_nil index_head index_tail)
              (option_map_none function)
              (map_nil function)))
          head
          tail
          list_induction_hypothesis
          (by
            (obtain mapped_head mapped_head_proof
              (maps_values head))
            (obtain mapped_tail mapped_tail_proof
              (map_computes_to_list function tail))
            (have mapped_list
              (computes-to
                (map function (cons head tail))
                (cons mapped_head mapped_tail))
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
                      (simpa only mapped_tail_proof)))))
              (by
                (calc
                  (option-map
                    function
                    (nth
                      (cons index_head index_tail)
                      (cons head tail)))
                  (==
                    (option-map function (nth index_tail tail))
                    (by
                      (simpa only
                        (nth_cons_cons
                          index_head
                          index_tail
                          head
                          tail))))
                  (==
                    (nth index_tail (map function tail))
                    (by
                      (exact (induction_hypothesis tail))))
                  (==
                    (nth index_tail mapped_tail)
                    (by
                      (simpa only mapped_tail_proof)))
                  (==
                    (nth
                      (cons index_head index_tail)
                      (cons mapped_head mapped_tail))
                    (by
                      (exact
                        (symm
                          (nth_cons_cons
                            index_head
                            index_tail
                            mapped_head
                            mapped_tail)))))
                  (==
                    (nth
                      (cons index_head index_tail)
                      (map function (cons head tail)))
                    (by
                      (simpa only (symm mapped_list)))))))))))))

(theorem option_map_find
  (forall function (is-value function)
    (implies
      (forall value (is-value value)
        (exists mapped_value (is-value mapped_value)
          (computes-to (function value) mapped_value)))
      (forall predicate (is-value predicate)
        (implies
          (forall value (is-value value)
            (is-bool (predicate value)))
          (forall list (is-list list)
            (computes-to
              (option-map
                function
                (find
                  (lambda find_value
                    (predicate (function find_value)))
                  list))
              (find predicate (map function list))))))))
  (by
    (intro function)
    (intro maps_values)
    (intro predicate)
    (intro predicate_returns_bool)
    (list-induction list
      (by
        (simpa only
          (find_nil
            (lambda find_value_nil
              (predicate (function find_value_nil))))
          (option_map_none function)
          (map_nil function)
          (find_nil predicate)))
      head
      tail
      induction_hypothesis
      (by
        (obtain mapped_head mapped_head_proof
          (maps_values head))
        (obtain mapped_tail mapped_tail_proof
          (map_computes_to_list function tail))
        (have mapped_list
          (computes-to
            (map function (cons head tail))
            (cons mapped_head mapped_tail))
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
                  (simpa only mapped_tail_proof)))))
          (by
            (or-elim
              (predicate_returns_bool mapped_head)
              predicate_true
              (by
                (have transformed_predicate_true
                  (computes-to
                    ((lambda find_value_true
                       (predicate (function find_value_true)))
                     head)
                    (quote :true))
                  (by
                    (calc
                      ((lambda find_value_true
                         (predicate (function find_value_true)))
                       head)
                      (==
                        (predicate (function head))
                        (by
                          (eval)))
                      (==
                        (predicate mapped_head)
                        (by
                          (simpa only mapped_head_proof)))
                      (==
                        (quote :true)
                        (by
                          (exact predicate_true)))))
                  (by
                    (have transformed_find_head
                      (computes-to
                        (find
                          (lambda find_value_true
                            (predicate (function find_value_true)))
                          (cons head tail))
                        (some head))
                      (by
                        (apply
                          find_cons_true
                          (lambda find_value_true_cons
                            (predicate (function find_value_true_cons)))
                          head
                          tail))
                      (by
                        (have mapped_find_head
                          (computes-to
                            (find predicate (cons mapped_head mapped_tail))
                            (some mapped_head))
                          (by
                            (apply find_cons_true predicate mapped_head mapped_tail))
                          (by
                            (calc
                              (option-map
                                function
                                (find
                                  (lambda find_value_true
                                    (predicate (function find_value_true)))
                                  (cons head tail)))
                              (==
                                (option-map function (some head))
                                (by
                                  (apply
                                    option_map_congr_option_computation
                                    function
                                    (find
                                      (lambda find_value_true
                                        (predicate (function find_value_true)))
                                      (cons head tail))
                                    (some head))))
                              (==
                                (some mapped_head)
                                (by
                                  (apply option_map_some function head mapped_head)))
                              (==
                                (find predicate (cons mapped_head mapped_tail))
                                (by
                                  (exact (symm mapped_find_head))))
                              (==
                                (find predicate (map function (cons head tail)))
                                (by
                                  (simpa only (symm mapped_list))))))))))))
              predicate_false
              (by
                (have transformed_predicate_false
                  (computes-to
                    ((lambda find_value_false
                       (predicate (function find_value_false)))
                     head)
                    (quote :false))
                  (by
                    (calc
                      ((lambda find_value_false
                         (predicate (function find_value_false)))
                       head)
                      (==
                        (predicate (function head))
                        (by
                          (eval)))
                      (==
                        (predicate mapped_head)
                        (by
                          (simpa only mapped_head_proof)))
                      (==
                        (quote :false)
                        (by
                          (exact predicate_false)))))
                  (by
                    (have transformed_find_tail
                      (computes-to
                        (find
                          (lambda find_value_false
                            (predicate (function find_value_false)))
                          (cons head tail))
                        (find
                          (lambda find_value_false_tail
                            (predicate (function find_value_false_tail)))
                          tail))
                      (by
                        (apply
                          find_cons_false
                          (lambda find_value_false_cons
                            (predicate (function find_value_false_cons)))
                          head
                          tail))
                      (by
                        (have mapped_find_tail
                          (computes-to
                            (find predicate (cons mapped_head mapped_tail))
                            (find predicate mapped_tail))
                          (by
                            (apply
                              find_cons_false
                              predicate
                              mapped_head
                              mapped_tail))
                          (by
                            (calc
                              (option-map
                                function
                                (find
                                  (lambda find_value_false
                                    (predicate (function find_value_false)))
                                  (cons head tail)))
                              (==
                                (option-map
                                  function
                                  (find
                                    (lambda find_value_false_tail
                                      (predicate
                                        (function find_value_false_tail)))
                                    tail))
                                (by
                                  (apply
                                    option_map_congr_option_computation
                                    function
                                    (find
                                      (lambda find_value_false
                                        (predicate (function find_value_false)))
                                      (cons head tail))
                                    (find
                                      (lambda find_value_false_tail
                                        (predicate
                                          (function find_value_false_tail)))
                                      tail))))
                              (==
                                (find predicate (map function tail))
                                (by
                                  (exact induction_hypothesis)))
                              (==
                                (find predicate mapped_tail)
                                (by
                                  (simpa only mapped_tail_proof)))
                              (==
                                (find predicate (cons mapped_head mapped_tail))
                                (by
                                  (exact (symm mapped_find_tail))))
                              (==
                                (find
                                  predicate
                                  (map function (cons head tail)))
                                (by
                                  (simpa only (symm mapped_list)))))))))))))))))))

(theorem option_bind_find_none
  (forall function (is-value function)
    (forall predicate (is-value predicate)
      (forall list (is-list list)
        (implies
          (computes-to (find predicate list) none)
          (computes-to
            (option-bind function (find predicate list))
            none)))))
  (by
    (intro function)
    (intro predicate)
    (intro list)
    (intro find_none)
    (calc
      (option-bind function (find predicate list))
      (==
        (option-bind function none)
        (by
          (apply
            option_bind_congr_option_computation
            function
            (find predicate list)
            none)))
      (==
        none
        (by
          (exact option_bind_none function))))))

(theorem option_bind_find_some
  (forall function (is-value function)
    (forall predicate (is-value predicate)
      (forall list (is-list list)
        (forall value (is-value value)
          (implies
            (computes-to (find predicate list) (some value))
            (computes-to
              (option-bind function (find predicate list))
              (function value)))))))
  (by
    (intro function)
    (intro predicate)
    (intro list)
    (intro value)
    (intro find_some)
    (calc
      (option-bind function (find predicate list))
      (==
        (option-bind function (some value))
        (by
          (apply
            option_bind_congr_option_computation
            function
            (find predicate list)
            (some value))))
      (==
        (function value)
        (by
          (exact option_bind_left_identity function value))))))

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

(theorem length_take
  (forall count (is-list count)
    (forall list (is-list list)
      (computes-to
        (length (take count list))
        (take count (length list)))))
  (by
    (list-induction count
      (by
        (intro list)
        (obtain list_length list_length_proof
          (length_computes_to_list list))
        (calc
          (length (take nil list))
          (==
            (length nil)
            (by
              (simpa only (take_zero list))))
          (==
            nil
            (by
              (exact length_nil)))
          (==
            (take nil list_length)
            (by
              (exact (symm (take_zero list_length)))))
          (==
            (take nil (length list))
            (by
              (simpa only (symm list_length_proof))))))
      count_head
      count_tail
      count_induction_hypothesis
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
            (obtain tail_length tail_length_proof
              (length_computes_to_list tail))
            (calc
              (length (take (cons count_head count_tail) (cons head tail)))
              (==
                (length (cons head (take count_tail tail)))
                (by
                  (simpa only (take_cons count_head count_tail head tail))))
              (==
                (length (cons head taken_tail))
                (by
                  (simpa only taken_tail_proof)))
              (==
                (cons (quote unit) (length taken_tail))
                (by
                  (exact length_cons head taken_tail)))
              (==
                (cons (quote unit) (length (take count_tail tail)))
                (by
                  (simpa only (symm taken_tail_proof))))
              (==
                (cons (quote unit) (take count_tail (length tail)))
                (by
                  (simpa only (count_induction_hypothesis tail))))
              (==
                (cons (quote unit) (take count_tail tail_length))
                (by
                  (simpa only tail_length_proof)))
              (==
                (take (cons count_head count_tail) (cons (quote unit) tail_length))
                (by
                  (exact
                    (symm
                      (take_cons
                        count_head
                        count_tail
                        (quote unit)
                        tail_length)))))
              (==
                (take
                  (cons count_head count_tail)
                  (cons (quote unit) (length tail)))
                (by
                  (simpa only (symm tail_length_proof))))
              (==
                (take
                  (cons count_head count_tail)
                  (length (cons head tail)))
                (by
                  (simpa only (symm (length_cons head tail))))))))))))

(theorem length_drop
  (forall count (is-list count)
    (forall list (is-list list)
      (computes-to
        (length (drop count list))
        (drop count (length list)))))
  (by
    (list-induction count
      (by
        (intro list)
        (obtain list_length list_length_proof
          (length_computes_to_list list))
        (calc
          (length (drop nil list))
          (==
            (length list)
            (by
              (simpa only (drop_zero list))))
          (==
            list_length
            (by
              (exact list_length_proof)))
          (==
            (drop nil list_length)
            (by
              (exact (symm (drop_zero list_length)))))
          (==
            (drop nil (length list))
            (by
              (simpa only (symm list_length_proof))))))
      count_head
      count_tail
      count_induction_hypothesis
      (by
        (list-induction list
          (by
            (eval))
          head
          tail
          list_induction_hypothesis
          (by
            (obtain tail_length tail_length_proof
              (length_computes_to_list tail))
            (calc
              (length (drop (cons count_head count_tail) (cons head tail)))
              (==
                (length (drop count_tail tail))
                (by
                  (simpa only (drop_cons count_head count_tail head tail))))
              (==
                (drop count_tail (length tail))
                (by
                  (exact count_induction_hypothesis tail)))
              (==
                (drop count_tail tail_length)
                (by
                  (simpa only tail_length_proof)))
              (==
                (drop (cons count_head count_tail) (cons (quote unit) tail_length))
                (by
                  (exact
                    (symm
                      (drop_cons
                        count_head
                        count_tail
                        (quote unit)
                        tail_length)))))
              (==
                (drop
                  (cons count_head count_tail)
                  (cons (quote unit) (length tail)))
                (by
                  (simpa only (symm tail_length_proof))))
              (==
                (drop
                  (cons count_head count_tail)
                  (length (cons head tail)))
                (by
                  (simpa only (symm (length_cons head tail))))))))))))

(theorem length_take_add_length_drop
  (forall count (is-list count)
    (forall list (is-list list)
      (computes-to
        (append
          (length (take count list))
          (length (drop count list)))
        (length list))))
  (by
    (intro count)
    (intro list)
    (obtain list_length list_length_proof
      (length_computes_to_list list))
    (calc
      (append
        (length (take count list))
        (length (drop count list)))
      (==
        (append
          (take count (length list))
          (length (drop count list)))
        (by
          (simpa only (length_take count list))))
      (==
        (append
          (take count (length list))
          (drop count (length list)))
        (by
          (simpa only (length_drop count list))))
      (==
        (append
          (take count list_length)
          (drop count (length list)))
        (by
          (simpa only list_length_proof)))
      (==
        (append
          (take count list_length)
          (drop count list_length))
        (by
          (simpa only list_length_proof)))
      (==
        list_length
        (by
          (exact append_take_drop count list_length)))
      (==
        (length list)
        (by
          (exact (symm list_length_proof)))))))

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

(theorem append_length_singleton
  (forall list (is-list list)
    (computes-to
      (append (length list) (cons (quote unit) nil))
      (cons (quote unit) (length list))))
  (by
    (list-induction list
      (by
        (calc
          (append (length nil) (cons (quote unit) nil))
          (==
            (append nil (cons (quote unit) nil))
            (by
              (simpa only length_nil)))
          (==
            (cons (quote unit) nil)
            (by
              (exact append_nil_returns_right (cons (quote unit) nil))))
          (==
            (cons (quote unit) (length nil))
            (by
              (exact
                (symm
                  (eval-to
                    (cons (quote unit) (length nil))
                    (cons (quote unit) nil))))))))
      head
      tail
      induction_hypothesis
      (by
        (obtain tail_length tail_length_proof
          (length_computes_to_list tail))
        (calc
          (append
            (length (cons head tail))
            (cons (quote unit) nil))
          (==
            (append
              (cons (quote unit) (length tail))
              (cons (quote unit) nil))
            (by
              (simpa only (length_cons head tail))))
          (==
            (append
              (cons (quote unit) tail_length)
              (cons (quote unit) nil))
            (by
              (simpa only tail_length_proof)))
          (==
            (cons
              (quote unit)
              (append tail_length (cons (quote unit) nil)))
            (by
              (exact
                append_cons
                (quote unit)
                tail_length
                (cons (quote unit) nil))))
          (==
            (cons
              (quote unit)
              (append (length tail) (cons (quote unit) nil)))
            (by
              (simpa only (symm tail_length_proof))))
          (==
            (cons
              (quote unit)
              (cons (quote unit) (length tail)))
            (by
              (simpa only induction_hypothesis)))
          (==
            (cons
              (quote unit)
              (length (cons head tail)))
            (by
              (simpa only (symm (length_cons head tail))))))))))

(theorem length_reverse
  (forall list (is-list list)
    (computes-to
      (length (reverse list))
      (length list)))
  (by
    (list-induction list
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (obtain reversed_tail reversed_tail_proof
          (reverse_computes_to_list tail))
        (calc
          (length (reverse (cons head tail)))
          (==
            (length
              (append (reverse tail) (cons head nil)))
            (by
              (simpa only (reverse_cons head tail))))
          (==
            (length
              (append reversed_tail (cons head nil)))
            (by
              (simpa only reversed_tail_proof)))
          (==
            (append
              (length reversed_tail)
              (length (cons head nil)))
            (by
              (exact
                length_append
                reversed_tail
                (cons head nil))))
          (==
            (append
              (length (reverse tail))
              (length (cons head nil)))
            (by
              (simpa only (symm reversed_tail_proof))))
          (==
            (append
              (length (reverse tail))
              (cons (quote unit) nil))
            (by
              (simpa only (length_singleton head))))
          (==
            (append
              (length tail)
              (cons (quote unit) nil))
            (by
              (simpa only induction_hypothesis)))
          (==
            (cons (quote unit) (length tail))
            (by
              (exact append_length_singleton tail)))
          (==
            (length (cons head tail))
            (by
              (simpa only (symm (length_cons head tail))))))))))

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

(theorem map_reverse
  (forall function (is-value function)
    (implies
      (forall value (is-value value)
        (exists mapped_value (is-value mapped_value)
          (computes-to (function value) mapped_value)))
      (forall list (is-list list)
        (computes-to
          (map function (reverse list))
          (reverse (map function list))))))
  (by
    (intro function)
    (intro maps_values)
    (list-induction list
      (by
        (calc
          (map function (reverse nil))
          (==
            (map function nil)
            (by
              (simpa only reverse_nil)))
          (==
            nil
            (by
              (exact map_nil function)))
          (==
            (reverse (map function nil))
            (by
              (exact
                (symm
                  (eval-to
                    (reverse (map function nil))
                    nil)))))))
      head
      tail
      induction_hypothesis
      (by
        (obtain mapped_head mapped_head_proof
          (maps_values head))
        (obtain reversed_tail reversed_tail_proof
          (reverse_computes_to_list tail))
        (obtain mapped_tail mapped_tail_proof
          (map_computes_to_list function tail))
        (calc
          (map function (reverse (cons head tail)))
          (==
            (map
              function
              (append (reverse tail) (cons head nil)))
            (by
              (simpa only (reverse_cons head tail))))
          (==
            (map function (append reversed_tail (cons head nil)))
            (by
              (simpa only reversed_tail_proof)))
          (==
            (append
              (map function reversed_tail)
              (map function (cons head nil)))
            (by
              (exact map_append function reversed_tail (cons head nil))))
          (==
            (append
              (map function (reverse tail))
              (map function (cons head nil)))
            (by
              (simpa only (symm reversed_tail_proof))))
          (==
            (append
              (reverse (map function tail))
              (map function (cons head nil)))
            (by
              (simpa only induction_hypothesis)))
          (==
            (append
              (reverse mapped_tail)
              (map function (cons head nil)))
            (by
              (simpa only mapped_tail_proof)))
          (==
            (append
              (reverse mapped_tail)
              (cons (function head) (map function nil)))
            (by
              (simpa only (map_cons function head nil))))
          (==
            (append
              (reverse mapped_tail)
              (cons mapped_head (map function nil)))
            (by
              (simpa only mapped_head_proof)))
          (==
            (append
              (reverse mapped_tail)
              (cons mapped_head nil))
            (by
              (simpa only (map_nil function))))
          (==
            (reverse (cons mapped_head mapped_tail))
            (by
              (exact (symm (reverse_cons mapped_head mapped_tail)))))
          (==
            (reverse (cons (function head) mapped_tail))
            (by
              (simpa only (symm mapped_head_proof))))
          (==
            (reverse (cons (function head) (map function tail)))
            (by
              (simpa only (symm mapped_tail_proof))))
          (==
            (reverse (map function (cons head tail)))
            (by
              (simpa only (symm (map_cons function head tail))))))))))

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

(theorem member_snoc
  (forall value (is-value value)
    (implies
      (forall element (is-value element)
        (is-bool (value-eq value element)))
      (forall list (is-list list)
        (forall snoc_value (is-value snoc_value)
          (computes-to
            (member value (snoc list snoc_value))
            (or
              (member value list)
              (value-eq value snoc_value)))))))
  (by
    (intro value)
    (intro value_eq_returns_bool)
    (list-induction list
      (by
        (intro snoc_value)
        (have snoc_eq_bool
          (is-bool (value-eq value snoc_value))
          (by
            (exact value_eq_returns_bool snoc_value))
          (by
            (have nil_member_bool
              (is-bool (member value nil))
              (by
                (exact
                  member_is_bool_for_comparable_value
                  value
                  nil))
              (by
                (calc
                  (member value (snoc nil snoc_value))
                  (==
                    (member value (cons snoc_value nil))
                    (by
                      (simpa only (snoc_nil snoc_value))))
                  (==
                    (or
                      (value-eq value snoc_value)
                      (member value nil))
                    (by
                      (exact
                        member_cons_or
                        value
                        snoc_value
                        nil)))
                  (==
                    (or
                      (member value nil)
                      (value-eq value snoc_value))
                    (by
                      (exact
                        or_comm
                        (value-eq value snoc_value)
                        (member value nil))))))))))
      head
      tail
      induction_hypothesis
      (by
        (intro snoc_value)
        (obtain tail_snoc tail_snoc_proof
          (snoc_computes_to_list tail snoc_value))
        (have head_eq_bool
          (is-bool (value-eq value head))
          (by
            (exact value_eq_returns_bool head))
          (by
            (have tail_member_bool
              (is-bool (member value tail))
              (by
                (exact
                  member_is_bool_for_comparable_value
                  value
                  tail))
              (by
                (have snoc_eq_bool
                  (is-bool (value-eq value snoc_value))
                  (by
                    (exact value_eq_returns_bool snoc_value))
                  (by
                    (have current_member_step
                      (computes-to
                        (member value (cons head tail))
                        (or
                          (value-eq value head)
                          (member value tail)))
                      (by
                        (exact member_cons_or value head tail))
                      (by
                        (calc
                          (member
                            value
                            (snoc (cons head tail) snoc_value))
                          (==
                            (member
                              value
                              (cons head (snoc tail snoc_value)))
                            (by
                              (simpa only
                                (snoc_cons
                                  head
                                  tail
                                  snoc_value))))
                          (==
                            (member value (cons head tail_snoc))
                            (by
                              (simpa only tail_snoc_proof)))
                          (==
                            (or
                              (value-eq value head)
                              (member value tail_snoc))
                            (by
                              (exact
                                member_cons_or
                                value
                                head
                                tail_snoc)))
                          (==
                            (or
                              (value-eq value head)
                              (member
                                value
                                (snoc tail snoc_value)))
                            (by
                              (simpa only tail_snoc_proof)))
                          (==
                            (or
                              (value-eq value head)
                              (or
                                (member value tail)
                                (value-eq value snoc_value)))
                            (by
                              (rewrite
                                (induction_hypothesis
                                  snoc_value))
                              (eval)))
                          (==
                            (or
                              (or
                                (value-eq value head)
                                (member value tail))
                              (value-eq value snoc_value))
                            (by
                              (have member_snoc_assoc
                                (computes-to
                                  (or
                                    (or
                                      (value-eq value head)
                                      (member value tail))
                                    (value-eq value snoc_value))
                                  (or
                                    (value-eq value head)
                                    (or
                                      (member value tail)
                                      (value-eq value snoc_value))))
                                (by
                                  (apply
                                    or_assoc
                                    (value-eq value head)
                                    (member value tail)
                                    (value-eq value snoc_value)))
                                (by
                                  (exact
                                    (symm member_snoc_assoc))))))
                          (==
                            (or
                              (member value (cons head tail))
                              (value-eq value snoc_value))
                            (by
                              (rewrite (symm current_member_step))
                              (eval)))))))))))))
  )
  )
  )

(theorem tail_snoc_after_snoc
  (forall list (is-list list)
    (forall value (is-value value)
      (forall next (is-value next)
        (computes-to
          (tail (snoc (snoc list value) next))
          (snoc (tail (snoc list value)) next)))))
  (by
    (list-induction list
      (by
        (intro value)
        (intro next)
        (obtain nil_next nil_next_proof
          (snoc_computes_to_list nil next))
        (calc
          (tail (snoc (snoc nil value) next))
          (==
            (tail (snoc (cons value nil) next))
            (by
              (simpa only (snoc_nil value))))
          (==
            (tail (cons value (snoc nil next)))
            (by
              (simpa only (snoc_cons value nil next))))
          (==
            (tail (cons value nil_next))
            (by
              (simpa only nil_next_proof)))
          (==
            nil_next
            (by
              (eval)))
          (==
            (snoc nil next)
            (by
              (simpa only (symm nil_next_proof))))
          (==
            (snoc (tail (cons value nil)) next)
            (by
              (eval)))
          (==
            (snoc (tail (snoc nil value)) next)
            (by
              (rewrite (symm (snoc_nil value)))
              (eval)))))
      head
      tail
      induction_hypothesis
      (by
        (intro value)
        (intro next)
        (obtain tail_snoc tail_snoc_proof
          (snoc_computes_to_list tail value))
        (obtain tail_snoc_next tail_snoc_next_proof
          (snoc_computes_to_list tail_snoc next))
        (calc
          (tail (snoc (snoc (cons head tail) value) next))
          (==
            (tail (snoc (cons head (snoc tail value)) next))
            (by
              (simpa only (snoc_cons head tail value))))
          (==
            (tail (snoc (cons head tail_snoc) next))
            (by
              (simpa only tail_snoc_proof)))
          (==
            (tail (cons head (snoc tail_snoc next)))
            (by
              (simpa only (snoc_cons head tail_snoc next))))
          (==
            (tail (cons head tail_snoc_next))
            (by
              (simpa only tail_snoc_next_proof)))
          (==
            tail_snoc_next
            (by
              (eval)))
          (==
            (snoc tail_snoc next)
            (by
              (simpa only (symm tail_snoc_next_proof))))
          (==
            (snoc (tail (cons head tail_snoc)) next)
            (by
              (eval)))
          (==
            (snoc (tail (cons head (snoc tail value))) next)
            (by
              (simpa only (symm tail_snoc_proof))))
          (==
            (snoc (tail (snoc (cons head tail) value)) next)
              (by
                (simpa only (snoc_cons head tail value))))))))
  )

(theorem all_snoc_true
  (forall predicate (is-value predicate)
    (forall list (is-list list)
      (implies
        (computes-to (all predicate list) (quote :true))
        (forall snoc_value (is-value snoc_value)
          (implies
            (computes-to (predicate snoc_value) (quote :true))
            (computes-to
              (all predicate (snoc list snoc_value))
              (quote :true)))))))
  (by
    (intro predicate)
    (list-induction list
      (by
        (intro list_all_true)
        (intro snoc_value)
        (intro snoc_value_satisfies_predicate)
        (calc
          (all predicate (snoc nil snoc_value))
          (==
            (all predicate (cons snoc_value nil))
            (by
              (simpa only (snoc_nil snoc_value))))
          (==
            (all predicate nil)
            (by
              (apply all_cons_true predicate snoc_value nil)))
          (==
            (quote :true)
            (by
              (exact all_nil predicate)))))
      head
      tail
      induction_hypothesis
      (by
        (intro list_all_true)
        (specialize list_parts all_cons_true_parts predicate head tail)
        (cases list_parts head_satisfies_predicate tail_all_true)
        (intro snoc_value)
        (intro snoc_value_satisfies_predicate)
        (obtain tail_snoc tail_snoc_proof
          (snoc_computes_to_list tail snoc_value))
        (have tail_snoc_all_true
          (computes-to (all predicate tail_snoc) (quote :true))
          (by
            (calc
              (all predicate tail_snoc)
              (==
                (all predicate (snoc tail snoc_value))
                (by
                  (simpa only (symm tail_snoc_proof))))
              (==
                (quote :true)
                (by
                  (exact induction_hypothesis snoc_value)))))
          (by
            (calc
              (all predicate (snoc (cons head tail) snoc_value))
              (==
                (all predicate (cons head (snoc tail snoc_value)))
                (by
                  (simpa only (snoc_cons head tail snoc_value))))
              (==
                (all predicate (cons head tail_snoc))
                (by
                  (simpa only tail_snoc_proof)))
              (==
                (all predicate tail_snoc)
                (by
                  (apply all_cons_true predicate head tail_snoc)))
              (==
                (quote :true)
                (by
                  (exact tail_snoc_all_true))))))))))

(theorem all_lists_snoc
  (forall list (is-list list)
    (implies
      (computes-to (all-lists list) (quote :true))
      (forall value (is-list value)
        (computes-to
          (all-lists (snoc list value))
          (quote :true)))))
  (by
    (list-induction list
      (by
        (intro list_all_lists)
        (intro value)
        (have nil_all_lists
          (computes-to (all-lists nil) (quote :true))
          (by
            (eval))
          (by
            (calc
              (all-lists (snoc nil value))
              (==
                (all-lists (cons value nil))
                (by
                  (simpa only (snoc_nil value))))
              (==
                (quote :true)
                (by
                  (exact all_lists_cons value nil)))))))
      head
      tail
      induction_hypothesis
      (by
        (intro list_all_lists)
        (intro value)
        (specialize all_parts all_lists_cons_true head tail)
        (cases all_parts head_is_list tail_all_lists)
        (specialize tail_snoc_all induction_hypothesis value)
        (obtain tail_snoc tail_snoc_proof
          (snoc_computes_to_list tail value))
        (have tail_snoc_all_value
          (computes-to (all-lists tail_snoc) (quote :true))
          (by
            (calc
              (all-lists tail_snoc)
              (==
                (all-lists (snoc tail value))
                (by
                  (simpa only (symm tail_snoc_proof))))
              (==
                (quote :true)
                (by
                  (exact tail_snoc_all)))))
        (by
          (calc
            (all-lists (snoc (cons head tail) value))
            (==
              (all-lists (cons head (snoc tail value)))
              (by
                (simpa only (snoc_cons head tail value))))
            (==
              (all-lists (cons head tail_snoc))
              (by
                (simpa only tail_snoc_proof)))
            (==
              (quote :true)
              (by
                (exact all_lists_cons head tail_snoc))))))))))

(theorem map_snoc
  (forall function (is-value function)
    (implies
      (forall input_value (is-value input_value)
        (exists mapped_value (is-value mapped_value)
          (computes-to (function input_value) mapped_value)))
      (forall list (is-list list)
        (forall snoc_value (is-value snoc_value)
          (computes-to
            (map function (snoc list snoc_value))
            (snoc (map function list) (function snoc_value)))))))
  (by
    (intro function)
    (intro maps_values)
    (list-induction list
      (by
        (intro snoc_value)
        (obtain mapped_value mapped_value_proof
          (maps_values snoc_value))
        (calc
          (map function (snoc nil snoc_value))
          (==
            (map function (cons snoc_value nil))
            (by
              (simpa only (snoc_nil snoc_value))))
          (==
            (cons (function snoc_value) (map function nil))
            (by
              (exact map_cons function snoc_value nil)))
          (==
            (cons mapped_value (map function nil))
            (by
              (simpa only mapped_value_proof)))
          (==
            (cons mapped_value nil)
            (by
              (simpa only (map_nil function))))
          (==
            (snoc nil mapped_value)
            (by
              (exact (symm (snoc_nil mapped_value)))))
          (==
            (snoc nil (function snoc_value))
            (by
              (simpa only (symm mapped_value_proof))))
          (==
            (snoc (map function nil) (function snoc_value))
            (by
              (rewrite (map_nil function))
              (eval)))))
      head
      tail
      induction_hypothesis
      (by
        (intro snoc_value)
        (obtain mapped_head mapped_head_proof
          (maps_values head))
        (obtain mapped_value mapped_value_proof
          (maps_values snoc_value))
        (obtain tail_snoc tail_snoc_proof
          (snoc_computes_to_list tail snoc_value))
        (obtain mapped_tail mapped_tail_proof
          (map_computes_to_list function tail))
        (have mapped_current
          (computes-to
            (map function (cons head tail))
            (cons mapped_head mapped_tail))
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
                  (simpa only mapped_tail_proof)))))
          (by
            (calc
              (map function (snoc (cons head tail) snoc_value))
              (==
                (map function (cons head (snoc tail snoc_value)))
                (by
                  (simpa only (snoc_cons head tail snoc_value))))
              (==
                (map function (cons head tail_snoc))
                (by
                  (simpa only tail_snoc_proof)))
              (==
                (cons (function head) (map function tail_snoc))
                (by
                  (exact map_cons function head tail_snoc)))
              (==
                (cons
                  (function head)
                  (map function (snoc tail snoc_value)))
                (by
                  (simpa only (symm tail_snoc_proof))))
              (==
                (cons
                  (function head)
                  (snoc (map function tail) (function snoc_value)))
                (by
                  (simpa only (induction_hypothesis snoc_value))))
              (==
                (cons
                  mapped_head
                  (snoc (map function tail) (function snoc_value)))
                (by
                  (simpa only mapped_head_proof)))
              (==
                (cons mapped_head (snoc mapped_tail (function snoc_value)))
                (by
                  (simpa only mapped_tail_proof)))
              (==
                (cons mapped_head (snoc mapped_tail mapped_value))
                (by
                  (simpa only mapped_value_proof)))
              (==
                (snoc (cons mapped_head mapped_tail) mapped_value)
                (by
                  (exact
                    (symm
                      (snoc_cons mapped_head mapped_tail mapped_value)))))
              (==
                (snoc (map function (cons head tail)) mapped_value)
                (by
                  (rewrite mapped_current)
                  (eval)))
              (==
                (snoc
                  (map function (cons head tail))
                  (function snoc_value))
                (by
                  (rewrite mapped_value_proof)
                  (eval))))))))))

(theorem length_snoc
  (forall list (is-list list)
    (forall value (is-value value)
      (computes-to
        (length (snoc list value))
        (cons (quote unit) (length list)))))
  (by
    (list-induction list
      (by
        (intro value)
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (intro value)
        (obtain tail_snoc tail_snoc_proof
          (snoc_computes_to_list tail value))
        (calc
          (length (snoc (cons head tail) value))
          (==
            (length (cons head (snoc tail value)))
            (by
              (simpa only (snoc_cons head tail value))))
          (==
            (length (cons head tail_snoc))
            (by
              (simpa only tail_snoc_proof)))
          (==
            (cons (quote unit) (length tail_snoc))
            (by
              (exact length_cons head tail_snoc)))
          (==
            (cons (quote unit) (length (snoc tail value)))
            (by
              (simpa only (symm tail_snoc_proof))))
          (==
            (cons (quote unit) (cons (quote unit) (length tail)))
            (by
              (simpa only induction_hypothesis)))
          (==
            (cons (quote unit) (length (cons head tail)))
            (by
              (simpa only (symm (length_cons head tail))))))))))

(theorem concat_nil
  (computes-to (concat nil) nil)
  (by
    (eval)))

(theorem concat_cons
  (forall head (is-list head)
    (forall tail (is-list tail)
      (computes-to
        (concat (cons head tail))
        (append head (concat tail)))))
  (by
    (intro head)
    (intro tail)
    (eval)))

(theorem concat_computes_to_list
  (forall lists (is-list lists)
    (implies
      (computes-to (all-lists lists) (quote :true))
      (computes-to-list result (concat lists))))
  (by
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
        (specialize all_parts all_lists_cons_true head tail)
        (cases all_parts head_is_list tail_all_lists)
        (specialize tail_concat_exists induction_hypothesis)
        (obtain concatenated_tail concatenated_tail_proof
          tail_concat_exists)
        (obtain concatenated_result concatenated_result_proof
          (append_computes_to_list head concatenated_tail))
        (exists concatenated_result
          (by
            (calc
              (concat (cons head tail))
              (==
                (append head (concat tail))
                (by
                  (exact concat_cons head tail)))
              (==
                (append head concatenated_tail)
                (by
                  (simpa only concatenated_tail_proof)))
              (==
                concatenated_result
                (by
                  (exact concatenated_result_proof))))))))))

(theorem concat_append
  (forall left (is-list left)
    (implies
      (computes-to (all-lists left) (quote :true))
      (forall right (is-list right)
        (implies
          (computes-to (all-lists right) (quote :true))
          (computes-to
            (concat (append left right))
            (append (concat left) (concat right)))))))
  (by
    (list-induction left
      (by
        (intro left_all_lists)
        (intro right)
        (intro right_all_lists)
        (specialize right_concat_exists concat_computes_to_list right)
        (obtain right_concat right_concat_proof
          right_concat_exists)
        (simpa only
          (append_nil_returns_right right)
          concat_nil
          right_concat_proof
          (append_nil_returns_right right_concat)))
      head
      tail
      induction_hypothesis
      (by
        (intro left_all_lists)
        (intro right)
        (intro right_all_lists)
        (specialize all_parts all_lists_cons_true head tail)
        (cases all_parts head_is_list tail_all_lists)
        (specialize tail_append induction_hypothesis right)
        (obtain tail_right tail_right_proof
          (append_computes_to_list tail right))
        (specialize tail_concat_exists concat_computes_to_list tail)
        (obtain tail_concat tail_concat_proof
          tail_concat_exists)
        (specialize right_concat_exists concat_computes_to_list right)
        (obtain right_concat right_concat_proof
          right_concat_exists)
        (calc
          (concat (append (cons head tail) right))
          (==
            (concat (cons head (append tail right)))
            (by
              (simpa only (append_cons head tail right))))
          (==
            (concat (cons head tail_right))
            (by
              (simpa only tail_right_proof)))
          (==
            (append head (concat tail_right))
            (by
              (exact concat_cons head tail_right)))
          (==
            (append head (concat (append tail right)))
            (by
              (simpa only (symm tail_right_proof))))
          (==
            (append head (append (concat tail) (concat right)))
            (by
              (simpa only tail_append)))
          (==
            (append head (append tail_concat (concat right)))
            (by
              (simpa only tail_concat_proof)))
          (==
            (append head (append tail_concat right_concat))
            (by
              (simpa only right_concat_proof)))
          (==
            (append (append head tail_concat) right_concat)
            (by
              (exact
                (symm (append_assoc head tail_concat right_concat)))))
          (==
            (append (concat (cons head tail)) (concat right))
            (by
              (simpa only
                (concat_cons head tail)
                tail_concat_proof
                right_concat_proof))))))))

(theorem map_length_nil
  (computes-to (map length nil) nil)
  (by
    (eval)))

(theorem map_length_cons
  (forall head (is-list head)
    (forall tail (is-list tail)
      (computes-to
        (map length (cons head tail))
        (cons (length head) (map length tail)))))
  (by
    (intro head)
    (intro tail)
    (eval)))

(theorem map_length_computes_to_list
  (forall lists (is-list lists)
    (implies
      (computes-to (all-lists lists) (quote :true))
      (computes-to-list result (map length lists))))
  (by
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
        (specialize all_parts all_lists_cons_true head tail)
        (cases all_parts head_is_list tail_all_lists)
        (obtain head_length head_length_proof
          (length_computes_to_list head))
        (specialize tail_lengths_exists induction_hypothesis)
        (obtain tail_lengths tail_lengths_proof
          tail_lengths_exists)
        (exists (cons head_length tail_lengths)
          (by
            (calc
              (map length (cons head tail))
              (==
                (cons (length head) (map length tail))
                (by
                  (exact map_length_cons head tail)))
              (==
                (cons head_length (map length tail))
                (by
                  (simpa only head_length_proof)))
              (==
                (cons head_length tail_lengths)
                (by
                  (simpa only tail_lengths_proof))))))))))

(theorem length_concat
  (forall lists (is-list lists)
    (implies
      (computes-to (all-lists lists) (quote :true))
      (computes-to
        (length (concat lists))
        (concat (map length lists)))))
  (by
    (list-induction lists
      (by
        (intro lists_are_lists)
        (calc
          (length (concat nil))
          (==
            (length nil)
            (by
              (simpa only concat_nil)))
          (==
            nil
            (by
              (exact length_nil)))
          (==
            (concat nil)
            (by
              (exact (symm concat_nil))))
          (==
            (concat (map length nil))
            (by
              (rewrite (symm map_length_nil))
              (eval)))))
      head
      tail
      induction_hypothesis
      (by
        (intro lists_are_lists)
        (specialize all_parts all_lists_cons_true head tail)
        (cases all_parts head_is_list tail_all_lists)
        (obtain head_length head_length_proof
          (length_computes_to_list head))
        (specialize tail_concat_exists concat_computes_to_list tail)
        (obtain tail_concat tail_concat_proof
          tail_concat_exists)
        (specialize tail_lengths_exists map_length_computes_to_list tail)
        (obtain tail_lengths tail_lengths_proof
          tail_lengths_exists)
        (calc
          (length (concat (cons head tail)))
          (==
            (length (append head (concat tail)))
            (by
              (simpa only (concat_cons head tail))))
          (==
            (length (append head tail_concat))
            (by
              (simpa only tail_concat_proof)))
          (==
            (append (length head) (length tail_concat))
            (by
              (exact length_append head tail_concat)))
          (==
            (append head_length (length tail_concat))
            (by
              (simpa only head_length_proof)))
          (==
            (append head_length (length (concat tail)))
            (by
              (simpa only (symm tail_concat_proof))))
          (==
            (append head_length (concat (map length tail)))
            (by
              (simpa only induction_hypothesis)))
          (==
            (append head_length (concat tail_lengths))
            (by
              (simpa only tail_lengths_proof)))
          (==
            (concat (cons head_length tail_lengths))
            (by
              (exact (symm (concat_cons head_length tail_lengths)))))
          (==
            (concat (cons (length head) tail_lengths))
            (by
              (simpa only (symm head_length_proof))))
          (==
            (concat (cons (length head) (map length tail)))
            (by
              (simpa only (symm tail_lengths_proof))))
          (==
            (concat (map length (cons head tail)))
            (by
              (simpa only (symm (map_length_cons head tail))))))))))

(theorem concat_map_as_concat_map
  (forall function (is-value function)
    (implies
      (forall value (is-value value)
        (computes-to-list mapped_list (function value)))
      (forall list (is-list list)
        (computes-to
          (concat-map function list)
          (concat (map function list))))))
  (by
    (intro function)
    (intro maps_values_to_lists)
    (have maps_values
      (forall value (is-value value)
        (exists mapped_value (is-value mapped_value)
          (computes-to (function value) mapped_value)))
      (by
        (intro value)
        (obtain mapped_list mapped_list_proof
          (maps_values_to_lists value))
        (exists mapped_list
          (by
            (exact mapped_list_proof))))
      (by
        (list-induction list
          (by
            (eval))
          head
          tail
          induction_hypothesis
          (by
            (obtain mapped_head mapped_head_proof
              (maps_values_to_lists head))
            (obtain mapped_tail mapped_tail_proof
              (map_computes_to_list function tail))
            (calc
              (concat-map function (cons head tail))
              (==
                (append
                  (function head)
                  (concat-map function tail))
                (by
                  (exact concat_map_cons function head tail)))
              (==
                (append mapped_head (concat-map function tail))
                (by
                  (simpa only mapped_head_proof)))
              (==
                (append
                  mapped_head
                  (concat (map function tail)))
                (by
                  (simpa only induction_hypothesis)))
              (==
                (append mapped_head (concat mapped_tail))
                (by
                  (simpa only mapped_tail_proof)))
              (==
                (concat (cons mapped_head mapped_tail))
                (by
                  (exact
                    (symm
                      (concat_cons mapped_head mapped_tail)))))
              (==
                (concat (cons mapped_head (map function tail)))
                (by
                  (simpa only (symm mapped_tail_proof))))
              (==
                (concat
                  (cons (function head) (map function tail)))
                (by
                  (simpa only (symm mapped_head_proof))))
              (==
                (concat (map function (cons head tail)))
                (by
                  (simpa only
                    (symm
                      (map_cons function head tail))))))))))))

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

(theorem is_pair_nil_false
  (computes-to
    (is-pair nil)
    (quote :false))
  (by
    (eval)))

(theorem is_pair_singleton_false
  (forall head (is-value head)
    (computes-to
      (is-pair (cons head nil))
      (quote :false)))
  (by
    (intro head)
    (eval)))

(theorem is_pair_cons_cons_nil_true
  (forall first (is-value first)
    (forall second (is-value second)
      (computes-to
        (is-pair (cons first (cons second nil)))
        (quote :true))))
  (by
    (intro first)
    (intro second)
    (eval)))

(theorem is_pair_cons_cons_cons_false
  (forall first (is-value first)
    (forall second (is-value second)
      (forall third (is-value third)
        (forall tail (is-list tail)
          (computes-to
            (is-pair (cons first (cons second (cons third tail))))
            (quote :false))))))
  (by
    (intro first)
    (intro second)
    (intro third)
    (intro tail)
    (eval)))

(theorem is_pair_cons_cons_true_elim
  (forall first (is-value first)
    (forall second (is-value second)
      (forall rest (is-list rest)
        (implies
          (computes-to
            (is-pair (cons first (cons second rest)))
            (quote :true))
          (computes-to rest nil)))))
  (by
    (intro first)
    (intro second)
    (list-induction rest
      (by
        (intro pair_true)
        (eval))
      third
      extra
      induction_hypothesis
      (by
        (intro pair_true)
        (have pair_false
          (computes-to
            (is-pair (cons first (cons second (cons third extra))))
            (quote :false))
          (by
            (exact
              (is_pair_cons_cons_cons_false
                first
                second
                third
                extra)))
          (by
            (have impossible_eq
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (is-pair
                      (cons first (cons second (cons third extra))))
                    (by
                      (exact (symm pair_false))))
                  (==
                    (quote :true)
                    (by
                      (exact pair_true)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to (cons third extra) nil)))))))))))

(theorem is_pair_cons_true_elim
  (forall first (is-value first)
    (forall tail (is-list tail)
      (implies
        (computes-to
          (is-pair (cons first tail))
          (quote :true))
        (exists second (is-value second)
          (computes-to tail (cons second nil))))))
  (by
    (intro first)
    (list-induction tail
      (by
        (intro pair_true)
        (have pair_false
          (computes-to
            (is-pair (cons first nil))
            (quote :false))
          (by
            (exact (is_pair_singleton_false first)))
          (by
            (have impossible_eq
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (is-pair (cons first nil))
                    (by
                      (exact (symm pair_false))))
                  (==
                    (quote :true)
                    (by
                      (exact pair_true)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (exists second (is-value second)
                      (computes-to nil (cons second nil))))))))))
      second
      rest
      induction_hypothesis
      (by
        (intro pair_true)
        (specialize rest_nil
          is_pair_cons_cons_true_elim
          first
          second
          rest)
        (exists second
          (by
            (calc
              (cons second rest)
              (==
                (cons second nil)
                (by
                  (simpa only rest_nil))))))))))

(theorem is_pair_true_elim
  (forall value (is-value value)
    (implies
      (computes-to (is-pair value) (quote :true))
      (exists first (is-value first)
        (exists second (is-value second)
          (computes-to
            value
            (cons first (cons second nil)))))))
  (by
    (value-induction value
      value_is_symbol
      (by
        (intro pair_true)
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
        (specialize value_not_list
          is_symbol_true_implies_is_list_value_false
          value)
        (have pair_false
          (computes-to (is-pair value) (quote :false))
          (by
            (simpa only value_not_list))
          (by
            (have impossible_eq
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (is-pair value)
                    (by
                      (exact (symm pair_false))))
                  (==
                    (quote :true)
                    (by
                      (exact pair_true)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (exists first (is-value first)
                      (exists second (is-value second)
                        (computes-to
                          value
                          (cons first (cons second nil))))))))))))
      value_is_lambda
      (by
        (intro pair_true)
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
        (specialize value_not_list
          is_lambda_true_implies_is_list_value_false
          value)
        (have pair_false
          (computes-to (is-pair value) (quote :false))
          (by
            (simpa only value_not_list))
          (by
            (have impossible_eq
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (is-pair value)
                    (by
                      (exact (symm pair_false))))
                  (==
                    (quote :true)
                    (by
                      (exact pair_true)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (exists first (is-value first)
                      (exists second (is-value second)
                        (computes-to
                          value
                          (cons first (cons second nil))))))))))))
      (by
        (intro pair_true)
        (have pair_false
          (computes-to (is-pair nil) (quote :false))
          (by
            (exact is_pair_nil_false))
          (by
            (have impossible_eq
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (is-pair nil)
                    (by
                      (exact (symm pair_false))))
                  (==
                    (quote :true)
                    (by
                      (exact pair_true)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (exists first (is-value first)
                      (exists second (is-value second)
                        (computes-to
                          nil
                          (cons first (cons second nil))))))))))))
      head
      tail
      head_induction_hypothesis
      tail_induction_hypothesis
      (by
        (intro pair_true)
        (specialize tail_parts
          is_pair_cons_true_elim
          head
          tail)
        (obtain second tail_is_singleton tail_parts)
        (exists head
          (by
            (exists second
              (by
                (calc
                  (cons head tail)
                  (==
                    (cons head (cons second nil))
                    (by
                      (simpa only tail_is_singleton))))))))))))

(theorem all_is_pair_cons_true_parts
  (forall head (is-value head)
    (forall tail (is-list tail)
      (implies
        (computes-to
          (all is-pair (cons head tail))
          (quote :true))
        (and
          (computes-to (is-pair head) (quote :true))
          (computes-to (all is-pair tail) (quote :true))))))
  (by
    (intro head)
    (intro tail)
    (intro all_true)
    (have unfolded_all_true
      (computes-to
        (all
          (lambda value
            (if
              (is-list-value value)
              (list-case value
                (quote :false)
                first_cell
                (list-case (tail first_cell)
                  (quote :false)
                  second_cell
                  (list-case (tail second_cell)
                    (quote :true)
                    extra_cell
                    (quote :false))))
              (quote :false)))
          (cons head tail))
        (quote :true))
      (by
        (calc
          (all
            (lambda value
              (if
                (is-list-value value)
                (list-case value
                  (quote :false)
                  first_cell
                  (list-case (tail first_cell)
                    (quote :false)
                    second_cell
                    (list-case (tail second_cell)
                      (quote :true)
                      extra_cell
                      (quote :false))))
                (quote :false)))
            (cons head tail))
          (==
            (all is-pair (cons head tail))
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact all_true)))))
      (by
        (specialize all_parts
          all_cons_true_parts
          (lambda value
            (if
              (is-list-value value)
              (list-case value
                (quote :false)
                first_cell
                (list-case (tail first_cell)
                  (quote :false)
                  second_cell
                  (list-case (tail second_cell)
                    (quote :true)
                    extra_cell
                    (quote :false))))
              (quote :false)))
          head
          tail)
        (cases all_parts
          head_lambda_true
          tail_lambda_true)
        (split
          (by
            (calc
              (is-pair head)
              (==
                ((lambda value
                   (if
                     (is-list-value value)
                     (list-case value
                       (quote :false)
                       first_cell
                       (list-case (tail first_cell)
                         (quote :false)
                         second_cell
                         (list-case (tail second_cell)
                           (quote :true)
                           extra_cell
                           (quote :false))))
                     (quote :false)))
                 head)
                (by
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact head_lambda_true)))))
          (by
            (calc
              (all is-pair tail)
              (==
                (all
                  (lambda value
                    (if
                      (is-list-value value)
                      (list-case value
                        (quote :false)
                        first_cell
                        (list-case (tail first_cell)
                          (quote :false)
                          second_cell
                          (list-case (tail second_cell)
                            (quote :true)
                            extra_cell
                            (quote :false))))
                      (quote :false)))
                  tail)
                (by
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact tail_lambda_true))))))))))

(theorem zip_pair_shape
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (all is-pair (zip left right))
        (quote :true))))
  (by
    (list-induction left
      (by
        (intro right)
        (eval))
      left_head
      left_tail
      left_induction_hypothesis
      (by
        (list-induction right
          (by
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (have zipped_head_is_pair
              (computes-to
                (is-pair (cons left_head (cons right_head nil)))
                (quote :true))
              (by
                (apply
                  is_pair_cons_cons_nil_true
                  left_head
                  right_head))
              (by
                (obtain zipped_tail zipped_tail_proof
                  (zip_computes_to_list left_tail right_tail))
                (have tail_pairs
                  (computes-to
                    (all is-pair zipped_tail)
                    (quote :true))
                  (by
                    (calc
                      (all is-pair zipped_tail)
                      (==
                        (all is-pair (zip left_tail right_tail))
                        (by
                          (simpa only (symm zipped_tail_proof))))
                      (==
                        (quote :true)
                        (by
                          (exact
                            (left_induction_hypothesis
                              right_tail))))))
                  (by
                    (calc
                      (all
                        is-pair
                        (zip
                          (cons left_head left_tail)
                          (cons right_head right_tail)))
                      (==
                        (all
                          is-pair
                          (cons
                            (cons left_head (cons right_head nil))
                            (zip left_tail right_tail)))
                        (by
                          (simpa only
                            (zip_cons
                              left_head
                              left_tail
                              right_head
                              right_tail))))
                      (==
                        (all
                          is-pair
                          (cons
                            (cons left_head (cons right_head nil))
                            zipped_tail))
                        (by
                          (simpa only zipped_tail_proof)))
                      (==
                        (all is-pair zipped_tail)
                        (by
                          (simpa only zipped_head_is_pair)))
                          (==
                            (quote :true)
                            (by
                              (exact tail_pairs))))))))))))))

(theorem unzip_pair_shape
  (forall pairs (is-list pairs)
    (implies
      (computes-to
        (all is-pair pairs)
        (quote :true))
      (exists left (is-list left)
        (exists right (is-list right)
          (computes-to
            (unzip pairs)
            (cons left (cons right nil)))))))
  (by
    (list-induction pairs
      (by
        (intro all_pairs)
        (exists nil
          (by
            (exists nil
              (by
                (exact unzip_nil))))))
      head_pair
      tail_pairs
      induction_hypothesis
      (by
        (intro all_pairs)
        (specialize all_parts
          all_is_pair_cons_true_parts
          head_pair
          tail_pairs)
        (cases all_parts
          head_pair_is_pair
          tail_all)
        (specialize head_parts
          is_pair_true_elim
          head_pair)
        (obtain left_head right_head_exists head_parts)
        (obtain right_head head_pair_value right_head_exists)
        (specialize tail_parts induction_hypothesis)
        (obtain tail_left tail_right_exists tail_parts)
        (obtain tail_right tail_unzip tail_right_exists)
        (exists (cons left_head tail_left)
          (by
            (exists (cons right_head tail_right)
              (by
                (calc
                  (unzip (cons head_pair tail_pairs))
                  (==
                    (unzip
                      (cons
                        (cons left_head (cons right_head nil))
                        tail_pairs))
                    (by
                      (simpa only head_pair_value)))
                  (==
                    (cons
                      (cons
                        left_head
                        (head (unzip tail_pairs)))
                      (cons
                        (cons
                          right_head
                          (head (tail (unzip tail_pairs))))
                        nil))
                    (by
                      (exact
                        (unzip_cons
                          left_head
                          right_head
                          tail_pairs))))
                  (==
                    (cons
                      (cons left_head tail_left)
                      (cons
                        (cons right_head tail_right)
                        nil))
                    (by
                      (simpa only tail_unzip))))))))))))

(theorem zip_unzip
  (forall pairs (is-list pairs)
    (implies
      (computes-to
        (all is-pair pairs)
        (quote :true))
      (computes-to
        (zip
          (head (unzip pairs))
          (head (tail (unzip pairs))))
        pairs)))
  (by
    (list-induction pairs
      (by
        (intro all_pairs)
        (eval))
      head_pair
      tail_pairs
      induction_hypothesis
      (by
        (intro all_pairs)
        (specialize all_parts
          all_is_pair_cons_true_parts
          head_pair
          tail_pairs)
        (cases all_parts
          head_pair_is_pair
          tail_all)
        (specialize head_parts
          is_pair_true_elim
          head_pair)
        (obtain left_head right_head_exists head_parts)
        (obtain right_head head_pair_value right_head_exists)
        (specialize tail_shape
          unzip_pair_shape
          tail_pairs)
        (obtain tail_left tail_right_exists tail_shape)
        (obtain tail_right tail_unzip tail_right_exists)
        (have tail_first
          (computes-to
            (head (unzip tail_pairs))
            tail_left)
          (by
            (apply
              list_pair_first_from_computation
              (unzip tail_pairs)
              tail_left
              tail_right))
          (by
            (have tail_second
              (computes-to
                (head (tail (unzip tail_pairs)))
                tail_right)
              (by
                (apply
                  list_pair_second_from_computation
                  (unzip tail_pairs)
                  tail_left
                  tail_right))
              (by
                (have current_unzip
                  (computes-to
                    (unzip (cons head_pair tail_pairs))
                    (cons
                      (cons left_head tail_left)
                      (cons (cons right_head tail_right) nil)))
                  (by
                    (calc
                      (unzip (cons head_pair tail_pairs))
                      (==
                        (cons
                          (cons
                            (head head_pair)
                            (head (unzip tail_pairs)))
                          (cons
                            (cons
                              (head (tail head_pair))
                              (head (tail (unzip tail_pairs))))
                            nil))
                        (by
                          (eval)))
                      (==
                        (cons
                          (cons left_head (head (unzip tail_pairs)))
                          (cons
                            (cons
                              (head (tail head_pair))
                              (head (tail (unzip tail_pairs))))
                            nil))
                        (by
                          (simpa only
                            (pair_first_from_computation
                              head_pair
                              left_head
                              right_head))))
                      (==
                        (cons
                          (cons left_head (head (unzip tail_pairs)))
                          (cons
                            (cons
                              right_head
                              (head (tail (unzip tail_pairs))))
                            nil))
                        (by
                          (simpa only
                            (pair_second_from_computation
                              head_pair
                              left_head
                              right_head))))
                      (==
                        (cons
                          (cons left_head tail_left)
                          (cons
                            (cons
                              right_head
                              (head (tail (unzip tail_pairs))))
                            nil))
                        (by
                          (simpa only tail_first)))
                      (==
                        (cons
                          (cons left_head tail_left)
                          (cons
                            (cons right_head tail_right)
                            nil))
                        (by
                          (simpa only tail_second)))))
                  (by
                    (have current_first
                      (computes-to
                        (head (unzip (cons head_pair tail_pairs)))
                        (cons left_head tail_left))
                      (by
                        (apply
                          list_pair_first_from_computation
                          (unzip (cons head_pair tail_pairs))
                          (cons left_head tail_left)
                          (cons right_head tail_right)))
                      (by
                        (have current_second
                          (computes-to
                            (head
                              (tail
                                (unzip (cons head_pair tail_pairs))))
                            (cons right_head tail_right))
                          (by
                            (apply
                              list_pair_second_from_computation
                              (unzip (cons head_pair tail_pairs))
                              (cons left_head tail_left)
                              (cons right_head tail_right)))
                          (by
                            (specialize zipped_tail induction_hypothesis)
                            (calc
                              (zip
                                (head (unzip (cons head_pair tail_pairs)))
                                (head
                                  (tail
                                    (unzip
                                      (cons head_pair tail_pairs)))))
                              (==
                                (zip
                                  (cons left_head tail_left)
                                  (head
                                    (tail
                                      (unzip
                                        (cons head_pair tail_pairs)))))
                                (by
                                  (rewrite current_first)
                                  (eval)))
                              (==
                                (zip
                                  (cons left_head tail_left)
                                  (cons right_head tail_right))
                                (by
                                  (rewrite current_second)
                                  (eval)))
                              (==
                                (cons
                                  (cons left_head (cons right_head nil))
                                  (zip tail_left tail_right))
                                (by
                                  (exact
                                    (zip_cons
                                      left_head
                                      tail_left
                                      right_head
                                      tail_right))))
                              (==
                                (cons
                                  (cons left_head (cons right_head nil))
                                  (zip
                                    (head (unzip tail_pairs))
                                    tail_right))
                                (by
                                  (simpa only (symm tail_first))))
                              (==
                                (cons
                                  (cons left_head (cons right_head nil))
                                  (zip
                                    (head (unzip tail_pairs))
                                    (head (tail (unzip tail_pairs)))))
                                (by
                                  (simpa only (symm tail_second))))
                              (==
                                (cons
                                  (cons left_head (cons right_head nil))
                                  tail_pairs)
                                (by
                                  (simpa only zipped_tail)))
                              (==
                                (cons head_pair tail_pairs)
                                (by
                                  (simpa only
                                    (symm head_pair_value)))))))))))))))))))

(theorem unzip_zip
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (unzip (zip left right))
        (cons
          (take (length right) left)
          (cons
            (take (length left) right)
            nil)))))
  (by
    (list-induction left
      (by
        (intro right)
        (obtain right_length right_length_proof
          (length_computes_to_list right))
        (calc
          (unzip (zip nil right))
          (==
            (unzip nil)
            (by
              (simpa only (zip_left_nil right))))
          (==
            (cons nil (cons nil nil))
            (by
              (exact unzip_nil)))
          (==
            (cons (take right_length nil) (cons nil nil))
            (by
              (simpa only (take_nil right_length))))
          (==
            (cons
              (take (length right) nil)
              (cons nil nil))
            (by
              (simpa only right_length_proof)))
          (==
            (cons
              (take (length right) nil)
              (cons (take nil right) nil))
            (by
              (simpa only (take_zero right))))
          (==
            (cons
              (take (length right) nil)
              (cons (take (length nil) right) nil))
            (by
              (simpa only length_nil)))))
      left_head
      left_tail
      left_induction_hypothesis
      (by
        (list-induction right
          (by
            (obtain left_length left_length_proof
              (length_computes_to_list
                (cons left_head left_tail)))
            (calc
              (unzip (zip (cons left_head left_tail) nil))
              (==
                (unzip nil)
                (by
                  (simpa only
                    (zip_right_nil
                      (cons left_head left_tail)))))
              (==
                (cons nil (cons nil nil))
                (by
                  (exact unzip_nil)))
              (==
                (cons
                  (take nil (cons left_head left_tail))
                  (cons nil nil))
                (by
                  (simpa only
                    (take_zero
                      (cons left_head left_tail)))))
              (==
                (cons
                  (take (length nil) (cons left_head left_tail))
                  (cons nil nil))
                (by
                  (simpa only length_nil)))
              (==
                (cons
                  (take (length nil) (cons left_head left_tail))
                  (cons (take left_length nil) nil))
                (by
                  (simpa only (take_nil left_length))))
              (==
                (cons
                  (take (length nil) (cons left_head left_tail))
                  (cons
                    (take (length (cons left_head left_tail)) nil)
                    nil))
                (by
                  (simpa only left_length_proof)))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (obtain zipped_tail zipped_tail_proof
              (zip_computes_to_list left_tail right_tail))
            (obtain right_tail_length right_tail_length_proof
              (length_computes_to_list right_tail))
            (obtain left_tail_length left_tail_length_proof
              (length_computes_to_list left_tail))
            (obtain tail_left tail_left_proof
              (take_computes_to_list
                right_tail_length
                left_tail))
            (obtain tail_right tail_right_proof
              (take_computes_to_list
                left_tail_length
                right_tail))
            (have tail_unzipped
              (computes-to
                (unzip (zip left_tail right_tail))
                (cons
                  (take (length right_tail) left_tail)
                  (cons
                    (take (length left_tail) right_tail)
                    nil)))
              (by
                (exact
                  left_induction_hypothesis
                  right_tail))
              (by
                (have tail_unzipped_concrete
                  (computes-to
                    (unzip (zip left_tail right_tail))
                    (cons tail_left (cons tail_right nil)))
                  (by
                    (calc
                      (unzip (zip left_tail right_tail))
                      (==
                        (cons
                          (take (length right_tail) left_tail)
                          (cons
                            (take (length left_tail) right_tail)
                            nil))
                        (by
                          (exact tail_unzipped)))
                      (==
                        (cons
                          (take right_tail_length left_tail)
                          (cons
                            (take (length left_tail) right_tail)
                            nil))
                        (by
                          (simpa only right_tail_length_proof)))
                      (==
                        (cons
                          (take right_tail_length left_tail)
                          (cons
                            (take left_tail_length right_tail)
                            nil))
                        (by
                          (simpa only left_tail_length_proof)))
                      (==
                        (cons
                          tail_left
                          (cons
                            (take left_tail_length right_tail)
                            nil))
                        (by
                          (simpa only tail_left_proof)))
                      (==
                        (cons tail_left (cons tail_right nil))
                        (by
                          (simpa only tail_right_proof)))))
                  (by
                    (have tail_first
                      (computes-to
                        (head
                          (unzip (zip left_tail right_tail)))
                        tail_left)
                      (by
                        (apply
                          list_pair_first_from_computation
                          (unzip (zip left_tail right_tail))
                          tail_left
                          tail_right))
                      (by
                        (have tail_second
                          (computes-to
                            (head
                              (tail
                                (unzip
                                  (zip left_tail right_tail))))
                            tail_right)
                          (by
                            (apply
                              list_pair_second_from_computation
                              (unzip (zip left_tail right_tail))
                              tail_left
                              tail_right))
                          (by
                            (calc
                              (unzip
                                (zip
                                  (cons left_head left_tail)
                                  (cons right_head right_tail)))
                              (==
                                (unzip
                                  (cons
                                    (cons
                                      left_head
                                      (cons right_head nil))
                                    (zip left_tail right_tail)))
                                (by
                                  (simpa only
                                    (zip_cons
                                      left_head
                                      left_tail
                                      right_head
                                      right_tail))))
                              (==
                                (unzip
                                  (cons
                                    (cons
                                      left_head
                                      (cons right_head nil))
                                    zipped_tail))
                                (by
                                  (simpa only zipped_tail_proof)))
                              (==
                                (cons
                                  (cons
                                    left_head
                                    (head (unzip zipped_tail)))
                                  (cons
                                    (cons
                                      right_head
                                      (head
                                        (tail (unzip zipped_tail))))
                                    nil))
                                (by
                                  (exact
                                    unzip_cons
                                    left_head
                                    right_head
                                    zipped_tail)))
                              (==
                                (cons
                                  (cons
                                    left_head
                                    (head
                                      (unzip
                                        (zip left_tail right_tail))))
                                  (cons
                                    (cons
                                      right_head
                                      (head
                                        (tail
                                          (unzip
                                            (zip
                                              left_tail
                                              right_tail)))))
                                    nil))
                                (by
                                  (simpa only zipped_tail_proof)))
                              (==
                                (cons
                                  (cons left_head tail_left)
                                  (cons
                                    (cons
                                      right_head
                                      (head
                                        (tail
                                          (unzip
                                            (zip
                                              left_tail
                                              right_tail)))))
                                    nil))
                                (by
                                  (simpa only tail_first)))
                              (==
                                (cons
                                  (cons left_head tail_left)
                                  (cons
                                    (cons right_head tail_right)
                                    nil))
                                (by
                                  (simpa only tail_second)))
                              (==
                                (cons
                                  (cons
                                    left_head
                                    (take
                                      right_tail_length
                                      left_tail))
                                  (cons
                                    (cons right_head tail_right)
                                    nil))
                                (by
                                  (simpa only tail_left_proof)))
                              (==
                                (cons
                                  (cons
                                    left_head
                                    (take
                                      right_tail_length
                                      left_tail))
                                  (cons
                                    (cons
                                      right_head
                                      (take
                                        left_tail_length
                                        right_tail))
                                    nil))
                                (by
                                  (simpa only tail_right_proof)))
                  (==
                    (cons
                      (take
                        (cons (quote unit) right_tail_length)
                        (cons left_head left_tail))
                      (cons
                        (cons
                          right_head
                          (take left_tail_length right_tail))
                        nil))
                    (by
                      (simpa only
                        (take_cons
                          (quote unit)
                          right_tail_length
                          left_head
                          left_tail))))
                  (==
                    (cons
                      (take
                        (cons (quote unit) right_tail_length)
                        (cons left_head left_tail))
                      (cons
                        (take
                          (cons (quote unit) left_tail_length)
                          (cons right_head right_tail))
                        nil))
                    (by
                      (simpa only
                        (take_cons
                          (quote unit)
                          left_tail_length
                          right_head
                          right_tail))))
                  (==
                    (cons
                      (take
                        (cons (quote unit) (length right_tail))
                        (cons left_head left_tail))
                      (cons
                        (take
                          (cons (quote unit) left_tail_length)
                          (cons right_head right_tail))
                        nil))
                    (by
                      (simpa only
                        right_tail_length_proof)))
                  (==
                    (cons
                      (take
                        (cons (quote unit) (length right_tail))
                        (cons left_head left_tail))
                      (cons
                        (take
                          (cons (quote unit) (length left_tail))
                          (cons right_head right_tail))
                        nil))
                    (by
                      (simpa only
                        left_tail_length_proof)))
                  (==
                    (cons
                      (take
                        (length (cons right_head right_tail))
                        (cons left_head left_tail))
                      (cons
                        (take
                          (cons (quote unit) (length left_tail))
                          (cons right_head right_tail))
                        nil))
                    (by
                      (simpa only
                        (length_cons
                          right_head
                          right_tail))))
                  (==
                    (cons
                      (take
                        (length (cons right_head right_tail))
                        (cons left_head left_tail))
                      (cons
                        (take
                          (length (cons left_head left_tail))
                          (cons right_head right_tail))
                        nil))
                    (by
                      (simpa only
                        (length_cons
                          left_head
                          left_tail)))))))))))
  )
  )
  )
  )
  )
  )
  )
  )

(theorem zip_with_as_map_zip
  (forall function (is-value function)
    (forall left (is-list left)
      (forall right (is-list right)
        (computes-to
          (zip-with function left right)
          (map
            (lambda pair
              (function
                (head pair)
                (head (tail pair))))
            (zip left right))))))
  (by
    (intro function)
    (list-induction left
      (by
        (intro right)
        (simpa only
          (zip_with_left_nil function right)
          (zip_left_nil right)
          (map_nil
            (lambda proof_pair_left_nil
              (function
                (head proof_pair_left_nil)
                (head (tail proof_pair_left_nil)))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (simpa only
              (zip_with_right_nil
                function
                (cons left_head left_tail))
              (zip_right_nil (cons left_head left_tail))
              (map_nil
                (lambda proof_pair_right_nil
                  (function
                    (head proof_pair_right_nil)
                    (head (tail proof_pair_right_nil)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (specialize tail_zip_with_as_map
              induction_hypothesis
              right_tail)
            (obtain zipped_tail zipped_tail_proof
              (zip_computes_to_list left_tail right_tail))
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
                    (zip_with_cons
                      function
                      left_head
                      left_tail
                      right_head
                      right_tail))))
              (==
                (cons
                  (function left_head right_head)
                  (map
                    (lambda proof_pair_tail
                      (function
                        (head proof_pair_tail)
                        (head (tail proof_pair_tail))))
                    (zip left_tail right_tail)))
                (by
                  (simpa only tail_zip_with_as_map)))
              (==
                (cons
                  (function left_head right_head)
                  (map
                    (lambda proof_pair_zipped_tail
                      (function
                        (head proof_pair_zipped_tail)
                        (head (tail proof_pair_zipped_tail))))
                    zipped_tail))
                (by
                  (simpa only zipped_tail_proof)))
              (==
                (cons
                  ((lambda proof_pair_head
                     (function
                       (head proof_pair_head)
                       (head (tail proof_pair_head))))
                   (cons left_head (cons right_head nil)))
                  (map
                    (lambda proof_pair_head_tail
                      (function
                        (head proof_pair_head_tail)
                        (head (tail proof_pair_head_tail))))
                    zipped_tail))
                (by
                  (eval)))
              (==
                (map
                  (lambda proof_pair_cons
                    (function
                      (head proof_pair_cons)
                      (head (tail proof_pair_cons))))
                  (cons
                    (cons left_head (cons right_head nil))
                    zipped_tail))
                (by
                  (simpa only
                    (symm
                      (map_cons
                        (lambda proof_pair_map_cons
                          (function
                            (head proof_pair_map_cons)
                            (head (tail proof_pair_map_cons))))
                        (cons left_head (cons right_head nil))
                        zipped_tail)))))
              (==
                (map
                  (lambda proof_pair_unzipped_tail
                    (function
                      (head proof_pair_unzipped_tail)
                      (head (tail proof_pair_unzipped_tail))))
                  (cons
                    (cons left_head (cons right_head nil))
                    (zip left_tail right_tail)))
                (by
                  (simpa only (symm zipped_tail_proof))))
              (==
                (map
                  (lambda proof_pair_zip
                    (function
                      (head proof_pair_zip)
                      (head (tail proof_pair_zip))))
                  (zip
                    (cons left_head left_tail)
                    (cons right_head right_tail)))
                (by
                  (simpa only
                    (symm
                      (zip_cons
                        left_head
                        left_tail
                        right_head
                        right_tail))))))))))))
