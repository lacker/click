; Nat order and comparison theorems for the standard prelude.

(theorem zero_eq_nil
  (computes-to zero nil)
  (by
    (eval)))

(theorem zero_computes_to_list
  (computes-to-list result zero)
  (by
    (exists nil
      (by
        (eval)))))

(theorem zero_is_nat_value
  (computes-to (is-nat-value zero) (quote :true))
  (by
    (eval)))

(theorem succ_zero
  (computes-to
    (succ zero)
    (cons (quote unit) nil))
  (by
    (eval)))

(theorem succ_injective
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (succ left) (succ right))
        (computes-to left right))))
  (by
    (intro left)
    (intro right)
    (intro successors_equal)
    (calc
      left
      (==
        (tail (succ left))
        (by
          (exact
            (symm
              (eval-to (tail (succ left)) left)))))
      (==
        (tail (succ right))
        (by
          (simpa only successors_equal)))
      (==
        right
        (by
          (eval))))))

(theorem zero_ne_succ
  (forall nat (is-list nat)
    (implies
      (computes-to zero (succ nat))
      (absurd)))
  (by
    (intro nat)
    (intro zero_eq_succ)
    (have nil_eq_cons
      (computes-to nil (cons (quote unit) nat))
      (by
        (calc
          nil
          (==
            zero
            (by
              (exact (symm zero_eq_nil))))
          (==
            (succ nat)
            (by
              (exact zero_eq_succ)))
          (==
            (cons (quote unit) nat)
            (by
              (eval)))))
      (by
        (exact
          (distinct-outcomes nil_eq_cons))))))

(theorem is_zero_zero
  (computes-to (is-zero zero) (quote :true))
  (by
    (eval)))

(theorem is_zero_succ
  (forall nat (is-list nat)
    (computes-to (is-zero (succ nat)) (quote :false)))
  (by
    (intro nat)
    (eval)))

(theorem is_zero_cons_false
  (forall head (is-value head)
    (forall tail (is-list tail)
      (computes-to
        (is-zero (cons head tail))
        (quote :false))))
  (by
    (intro head)
    (intro tail)
    (eval)))

(theorem is_zero_is_bool
  (forall nat (is-list nat)
    (is-bool (is-zero nat)))
  (by
    (list-induction nat
      (by
        (left
          (by
            (eval))))
      head
      tail
      induction_hypothesis
      (by
        (right
          (by
            (eval)))))))

(theorem is_zero_computes_to_bool
  (forall nat (is-list nat)
    (is-bool (is-zero nat)))
  (by
    (intro nat)
    (exact is_zero_is_bool nat)))

(theorem pred_zero
  (computes-to (pred zero) zero)
  (by
    (eval)))

(theorem pred_succ
  (forall nat (is-list nat)
    (computes-to (pred (succ nat)) nat))
  (by
    (intro nat)
    (eval)))

(theorem is_zero_pred_succ
  (forall nat (is-list nat)
    (computes-to
      (is-zero (pred (succ nat)))
      (is-zero nat)))
  (by
    (intro nat)
    (eval)))

(theorem pred_computes_to_list
  (forall nat (is-list nat)
    (computes-to-list result (pred nat)))
  (by
    (list-induction nat
      (by
        (exists nil
          (by
            (eval))))
      head
      tail
      induction_hypothesis
      (by
        (exists tail
          (by
            (eval)))))))

(theorem pred_succ_inverse
  (forall nat (is-list nat)
    (computes-to (pred (succ nat)) nat))
  (by
    (intro nat)
    (exact pred_succ nat)))

(theorem succ_computes_to_list
  (forall nat (is-list nat)
    (computes-to-list result (succ nat)))
  (by
    (intro nat)
    (exists (cons (quote unit) nat)
      (by
        (eval)))))

(theorem range_zero
  (computes-to (range zero) nil)
  (by
    (eval)))

(theorem range_cons
  (forall head (is-value head)
    (forall tail (is-list tail)
      (computes-to
        (range (cons head tail))
        (snoc (range tail) tail))))
  (by
    (intro head)
    (intro tail)
    (eval)))

(theorem range_succ
  (forall nat (is-list nat)
    (computes-to
      (range (succ nat))
      (snoc (range nat) nat)))
  (by
    (intro nat)
    (eval)))

(theorem range_computes_to_list
  (forall count (is-list count)
    (computes-to-list result (range count)))
  (by
    (list-induction count
      (by
        (exists nil
          (by
            (eval))))
      head
      tail
      induction_hypothesis
      (by
        (obtain tail_range tail_range_proof
          induction_hypothesis)
        (obtain snoc_range snoc_range_proof
          (snoc_computes_to_list tail_range tail))
        (exists snoc_range
          (by
            (calc
              (range (cons head tail))
              (==
                (snoc (range tail) tail)
                (by
                  (exact range_cons head tail)))
              (==
                (snoc tail_range tail)
                (by
                  (simpa only tail_range_proof)))
              (==
                snoc_range
                (by
                  (exact snoc_range_proof))))))))))

(theorem min_zero_left
  (forall right (is-list right)
    (computes-to (min zero right) zero))
  (by
    (intro right)
    (eval)))

(theorem min_zero_right
  (forall left (is-list left)
    (computes-to (min left zero) zero))
  (by
    (list-induction left
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (eval)))))

(theorem min_succ_succ
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (min (succ left) (succ right))
        (succ (min left right)))))
  (by
    (intro left)
    (intro right)
    (eval)))

(theorem min_cons
  (forall left_head (is-value left_head)
    (forall left_tail (is-list left_tail)
      (forall right_head (is-value right_head)
        (forall right_tail (is-list right_tail)
          (computes-to
            (min
              (cons left_head left_tail)
              (cons right_head right_tail))
            (succ (min left_tail right_tail)))))))
  (by
    (intro left_head)
    (intro left_tail)
    (intro right_head)
    (intro right_tail)
    (eval)))

(theorem max_zero_left
  (forall right (is-list right)
    (computes-to (max zero right) right))
  (by
    (intro right)
    (eval)))

(theorem max_zero_right
  (forall left (is-list left)
    (computes-to (max left zero) left))
  (by
    (list-induction left
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (eval)))))

(theorem max_succ_succ
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (max (succ left) (succ right))
        (succ (max left right)))))
  (by
    (intro left)
    (intro right)
    (eval)))

(theorem max_cons
  (forall left_head (is-value left_head)
    (forall left_tail (is-list left_tail)
      (forall right_head (is-value right_head)
        (forall right_tail (is-list right_tail)
          (computes-to
            (max
              (cons left_head left_tail)
              (cons right_head right_tail))
            (succ (max left_tail right_tail)))))))
  (by
    (intro left_head)
    (intro left_tail)
    (intro right_head)
    (intro right_tail)
    (eval)))

(theorem min_computes_to_list
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to-list result (min left right))))
  (by
    (list-induction left
      (by
        (intro right)
        (exists nil
          (by
            (eval))))
      left_head
      left_tail
      induction_hypothesis
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
            (specialize tail_result_exists induction_hypothesis right_tail)
            (obtain tail_result tail_result_proof tail_result_exists)
            (exists (cons (quote unit) tail_result)
              (by
                (calc
                  (min (cons left_head left_tail) (cons right_head right_tail))
                  (==
                    (succ (min left_tail right_tail))
                    (by
                      (eval)))
                  (==
                    (succ tail_result)
                    (by
                      (simpa only tail_result_proof)))
                  (==
                    (cons (quote unit) tail_result)
                    (by
                      (eval))))))))))))

(theorem max_computes_to_list
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to-list result (max left right))))
  (by
    (list-induction left
      (by
        (intro right)
        (exists right
          (by
            (eval))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (exists (cons left_head left_tail)
              (by
                (eval))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (specialize tail_result_exists induction_hypothesis right_tail)
            (obtain tail_result tail_result_proof tail_result_exists)
            (exists (cons (quote unit) tail_result)
              (by
                (calc
                  (max (cons left_head left_tail) (cons right_head right_tail))
                  (==
                    (succ (max left_tail right_tail))
                    (by
                      (eval)))
                  (==
                    (succ tail_result)
                    (by
                      (simpa only tail_result_proof)))
                  (==
                    (cons (quote unit) tail_result)
                    (by
                      (eval))))))))))))

(theorem succ_preserves_nat_value
  (forall nat (is-list nat)
    (implies
      (computes-to (is-nat-value nat) (quote :true))
      (computes-to (is-nat-value (succ nat)) (quote :true))))
  (by
    (intro nat)
    (intro nat_is_nat)
    (calc
      (is-nat-value (succ nat))
      (==
        (is-nat-value nat)
        (by
          (eval)))
      (==
        (quote :true)
        (by
          (exact nat_is_nat))))))

(theorem is_nat_value_nil
  (computes-to (is-nat-value nil) (quote :true))
  (by
    (eval)))

(theorem is_nat_value_cons
  (forall head (is-value head)
    (forall tail (is-list tail)
      (computes-to
        (is-nat-value (cons head tail))
        (if
          (symbol-eq head (quote unit))
          (is-nat-value tail)
          (quote :false)))))
  (by
    (intro head)
    (intro tail)
    (calc
      (is-nat-value (cons head tail))
      (==
        (if
          (symbol-eq head (quote unit))
          (is-nat-value (tail (cons head tail)))
          (quote :false))
        (by
          (eval)))
      (==
        (if
          (symbol-eq head (quote unit))
          (is-nat-value tail)
          (quote :false))
        (by
          (rewrite
            (eval-to
              (tail (cons head tail))
              tail))
          (eval))))))

(theorem is_nat_value_cons_true_elim
  (forall head (is-value head)
    (forall tail (is-list tail)
      (implies
        (computes-to
          (is-nat-value (cons head tail))
          (quote :true))
        (and
          (computes-to head (quote unit))
          (computes-to
            (is-nat-value tail)
            (quote :true))))))
  (by
    (intro head)
    (intro tail)
    (intro cons_is_nat)
    (have unfolded
      (computes-to
        (if
          (symbol-eq head (quote unit))
          (is-nat-value tail)
          (quote :false))
        (quote :true))
      (by
        (calc
          (if
            (symbol-eq head (quote unit))
            (is-nat-value tail)
            (quote :false))
          (==
            (is-nat-value (cons head tail))
            (by
              (exact (symm (is_nat_value_cons head tail)))))
          (==
            (quote :true)
            (by
              (exact cons_is_nat)))))
      (by
        (split
          (by
            (exact
              (symbol-eq-true
                (if-true-condition unfolded))))
          (by
            (exact
              (if-true-then unfolded))))))))

(theorem is_nat_value_tail
  (forall head (is-value head)
    (forall tail (is-list tail)
      (implies
        (computes-to
          (is-nat-value (cons head tail))
          (quote :true))
        (computes-to
          (is-nat-value tail)
          (quote :true)))))
  (by
    (intro head)
    (intro tail)
    (intro cons_is_nat)
    (specialize cons_parts is_nat_value_cons_true_elim head tail)
    (cases cons_parts head_unit tail_is_nat)
    (exact tail_is_nat)))

(theorem nat_induction
  (forall predicate (is-value predicate)
    (implies
      (computes-to (predicate zero) (quote :true))
      (implies
        (forall previous (is-list previous)
          (implies
            (computes-to (is-nat-value previous) (quote :true))
            (implies
              (computes-to (predicate previous) (quote :true))
              (computes-to
                (predicate (succ previous))
                (quote :true)))))
        (forall nat (is-list nat)
          (implies
            (computes-to (is-nat-value nat) (quote :true))
            (computes-to (predicate nat) (quote :true)))))))
  (by
    (intro predicate)
    (intro base_case)
    (intro step_case)
    (list-induction nat
      (by
        (intro nat_is_nat)
        (calc
          (predicate nil)
          (==
            (predicate zero)
            (by
              (fold zero)
              (eval)))
          (==
            (quote :true)
            (by
              (exact base_case)))))
      head
      tail
      induction_hypothesis
      (by
        (intro nat_is_nat)
        (specialize cons_parts is_nat_value_cons_true_elim head tail)
        (cases cons_parts head_unit tail_is_nat)
        (specialize tail_predicate induction_hypothesis)
        (specialize succ_tail_predicate step_case tail)
        (calc
          (predicate (cons head tail))
          (==
            (predicate (cons (quote unit) tail))
            (by
              (simpa only head_unit)))
          (==
            (predicate (succ tail))
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact succ_tail_predicate))))))))

(theorem min_preserves_nat_value
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (implies
          (computes-to (is-nat-value right) (quote :true))
          (computes-to
            (is-nat-value (min left right))
            (quote :true))))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro left_is_nat)
        (intro right_is_nat)
        (eval))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro left_is_nat)
            (intro right_is_nat)
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro left_is_nat)
            (intro right_is_nat)
            (specialize left_tail_is_nat
              is_nat_value_tail
              left_head
              left_tail)
            (specialize right_tail_is_nat
              is_nat_value_tail
              right_head
              right_tail)
            (specialize tail_min_is_nat
              induction_hypothesis
              right_tail)
            (obtain tail_min tail_min_proof
              (min_computes_to_list left_tail right_tail))
            (calc
              (is-nat-value
                (min
                  (cons left_head left_tail)
                  (cons right_head right_tail)))
              (==
                (is-nat-value (succ (min left_tail right_tail)))
                (by
                  (simpa only
                    (min_cons
                      left_head
                      left_tail
                      right_head
                      right_tail))))
              (==
                (is-nat-value (succ tail_min))
                (by
                  (simpa only tail_min_proof)))
              (==
                (is-nat-value tail_min)
                (by
                  (eval)))
              (==
                (is-nat-value (min left_tail right_tail))
                (by
                  (simpa only (symm tail_min_proof))))
              (==
                (quote :true)
                (by
                  (exact tail_min_is_nat))))))))))

(theorem max_preserves_nat_value
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (implies
          (computes-to (is-nat-value right) (quote :true))
          (computes-to
            (is-nat-value (max left right))
            (quote :true))))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro left_is_nat)
        (intro right_is_nat)
        (calc
          (is-nat-value (max nil right))
          (==
            (is-nat-value right)
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact right_is_nat)))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro left_is_nat)
            (intro right_is_nat)
            (calc
              (is-nat-value (max (cons left_head left_tail) nil))
              (==
                (is-nat-value (cons left_head left_tail))
                (by
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact left_is_nat)))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro left_is_nat)
            (intro right_is_nat)
            (specialize left_tail_is_nat
              is_nat_value_tail
              left_head
              left_tail)
            (specialize right_tail_is_nat
              is_nat_value_tail
              right_head
              right_tail)
            (specialize tail_max_is_nat
              induction_hypothesis
              right_tail)
            (obtain tail_max tail_max_proof
              (max_computes_to_list left_tail right_tail))
            (calc
              (is-nat-value
                (max
                  (cons left_head left_tail)
                  (cons right_head right_tail)))
              (==
                (is-nat-value (succ (max left_tail right_tail)))
                (by
                  (simpa only
                    (max_cons
                      left_head
                      left_tail
                      right_head
                      right_tail))))
              (==
                (is-nat-value (succ tail_max))
                (by
                  (simpa only tail_max_proof)))
              (==
                (is-nat-value tail_max)
                (by
                  (eval)))
              (==
                (is-nat-value (max left_tail right_tail))
                (by
                  (simpa only (symm tail_max_proof))))
              (==
                (quote :true)
                (by
                  (exact tail_max_is_nat))))))))))

(theorem length_range
  (forall count (is-list count)
    (implies
      (computes-to (is-nat-value count) (quote :true))
      (computes-to
        (length (range count))
        count)))
  (by
    (list-induction count
      (by
        (intro count_is_nat)
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (intro count_is_nat)
        (specialize count_parts is_nat_value_cons_true_elim head tail)
        (cases count_parts head_unit tail_is_nat)
        (obtain tail_range tail_range_proof
          (range_computes_to_list tail))
        (specialize tail_length_range induction_hypothesis)
        (calc
          (length (range (cons head tail)))
          (==
            (length (snoc (range tail) tail))
            (by
              (simpa only (range_cons head tail))))
          (==
            (length (snoc tail_range tail))
            (by
              (simpa only tail_range_proof)))
          (==
            (cons (quote unit) (length tail_range))
            (by
              (exact length_snoc tail_range tail)))
          (==
            (cons (quote unit) (length (range tail)))
            (by
              (simpa only (symm tail_range_proof))))
          (==
            (cons (quote unit) tail)
            (by
              (simpa only tail_length_range)))
          (==
            (cons head tail)
            (by
              (simpa only (symm head_unit)))))))))

(theorem range_all_lists
  (forall count (is-list count)
    (implies
      (computes-to (is-nat-value count) (quote :true))
      (computes-to
        (all-lists (range count))
        (quote :true))))
  (by
    (list-induction count
      (by
        (intro count_is_nat)
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (intro count_is_nat)
        (specialize count_parts is_nat_value_cons_true_elim head tail)
        (cases count_parts head_unit tail_is_nat)
        (obtain tail_range tail_range_proof
          (range_computes_to_list tail))
        (specialize tail_range_all induction_hypothesis)
        (have tail_range_all_value
          (computes-to (all-lists tail_range) (quote :true))
          (by
            (calc
              (all-lists tail_range)
              (==
                (all-lists (range tail))
                (by
                  (simpa only (symm tail_range_proof))))
              (==
                (quote :true)
                (by
                  (exact tail_range_all)))))
          (by
            (calc
              (all-lists (range (cons head tail)))
              (==
                (all-lists (range (cons (quote unit) tail)))
                (by
                  (simpa only head_unit)))
              (==
                (all-lists (snoc (range tail) tail))
                (by
                  (simpa only (range_cons (quote unit) tail))))
              (==
                (all-lists (snoc tail_range tail))
                (by
                  (simpa only tail_range_proof)))
              (==
                (quote :true)
                (by
                  (exact all_lists_snoc tail_range tail))))))))))

(theorem range_all_nat_values
  (forall count (is-list count)
    (implies
      (computes-to (is-nat-value count) (quote :true))
      (computes-to
        (all
          (lambda candidate (is-nat-value candidate))
          (range count))
        (quote :true))))
  (by
    (list-induction count
      (by
        (intro count_is_nat)
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (intro count_is_nat)
        (specialize count_parts is_nat_value_cons_true_elim head tail)
        (cases count_parts head_unit tail_is_nat)
        (obtain tail_range tail_range_proof
          (range_computes_to_list tail))
        (specialize tail_range_all induction_hypothesis)
        (have tail_range_all_value
          (computes-to
            (all
              (lambda candidate (is-nat-value candidate))
              tail_range)
            (quote :true))
          (by
            (calc
              (all
                (lambda candidate (is-nat-value candidate))
                tail_range)
              (==
                (all
                  (lambda candidate (is-nat-value candidate))
                  (range tail))
                (by
                  (simpa only (symm tail_range_proof))))
              (==
                (quote :true)
                (by
                  (exact tail_range_all)))))
          (by
            (have tail_satisfies_nat_predicate
              (computes-to
                ((lambda candidate (is-nat-value candidate)) tail)
                (quote :true))
              (by
                (calc
                  ((lambda candidate (is-nat-value candidate)) tail)
                  (==
                    (is-nat-value tail)
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact tail_is_nat)))))
              (by
                (calc
                  (all
                    (lambda candidate (is-nat-value candidate))
                    (range (cons head tail)))
                  (==
                    (all
                      (lambda candidate (is-nat-value candidate))
                      (range (cons (quote unit) tail)))
                    (by
                      (simpa only head_unit)))
                  (==
                    (all
                      (lambda candidate (is-nat-value candidate))
                      (snoc (range tail) tail))
                    (by
                      (simpa only (range_cons (quote unit) tail))))
                  (==
                    (all
                      (lambda candidate (is-nat-value candidate))
                      (snoc tail_range tail))
                    (by
                      (simpa only tail_range_proof)))
                  (==
                    (quote :true)
                    (by
                      (exact
                        all_snoc_true
                        (lambda candidate (is-nat-value candidate))
                        tail_range
                        tail))))))))))))

(theorem map_succ_computes_to_list
  (forall list (is-list list)
    (implies
      (computes-to (all-lists list) (quote :true))
      (computes-to-list result (map succ list))))
  (by
    (list-induction list
      (by
        (intro list_all_lists)
        (exists nil
          (by
            (eval))))
      head
      tail
      induction_hypothesis
      (by
        (intro list_all_lists)
        (specialize all_parts all_lists_cons_true head tail)
        (cases all_parts head_is_list tail_all_lists)
        (specialize tail_map_exists induction_hypothesis)
        (obtain tail_map tail_map_proof
          tail_map_exists)
        (exists (cons (cons (quote unit) head) tail_map)
          (by
            (calc
              (map succ (cons head tail))
              (==
                (cons (succ head) (map succ tail))
                (by
                  (eval)))
              (==
                (cons (cons (quote unit) head) (map succ tail))
                (by
                  (eval)))
              (==
                (cons (cons (quote unit) head) tail_map)
                (by
                  (simpa only tail_map_proof))))))))))

(theorem map_succ_snoc
  (forall list (is-list list)
    (implies
      (computes-to (all-lists list) (quote :true))
      (forall value (is-list value)
        (computes-to
          (map succ (snoc list value))
          (snoc (map succ list) (cons (quote unit) value))))))
  (by
    (list-induction list
      (by
        (intro list_all_lists)
        (intro value)
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (intro list_all_lists)
        (intro value)
        (specialize all_parts all_lists_cons_true head tail)
        (cases all_parts head_is_list tail_all_lists)
        (specialize tail_map_snoc induction_hypothesis value)
        (obtain tail_snoc tail_snoc_proof
          (snoc_computes_to_list tail value))
        (specialize tail_map_exists map_succ_computes_to_list tail)
        (obtain tail_map tail_map_proof
          tail_map_exists)
        (have current_map
          (computes-to
            (map succ (cons head tail))
            (cons (cons (quote unit) head) tail_map))
          (by
            (calc
              (map succ (cons head tail))
              (==
                (cons (succ head) (map succ tail))
                (by
                  (eval)))
              (==
                (cons (cons (quote unit) head) (map succ tail))
                (by
                  (eval)))
              (==
                (cons (cons (quote unit) head) tail_map)
                (by
                  (simpa only tail_map_proof)))))
        (by
          (calc
            (map succ (snoc (cons head tail) value))
            (==
              (map succ (cons head (snoc tail value)))
              (by
                (simpa only (snoc_cons head tail value))))
            (==
              (map succ (cons head tail_snoc))
              (by
                (simpa only tail_snoc_proof)))
            (==
              (cons (succ head) (map succ tail_snoc))
              (by
                (eval)))
            (==
              (cons (succ head) (map succ (snoc tail value)))
              (by
                (simpa only (symm tail_snoc_proof))))
            (==
              (cons
                (succ head)
                (snoc (map succ tail) (cons (quote unit) value)))
              (by
                (simpa only tail_map_snoc)))
            (==
              (cons
                (cons (quote unit) head)
                (snoc (map succ tail) (cons (quote unit) value)))
              (by
                (eval)))
            (==
              (cons
                (cons (quote unit) head)
                (snoc tail_map (cons (quote unit) value)))
              (by
                (simpa only tail_map_proof)))
            (==
              (snoc
                (cons (cons (quote unit) head) tail_map)
                (cons (quote unit) value))
              (by
                (exact
                  (symm
                    (snoc_cons
                      (cons (quote unit) head)
                      tail_map
                      (cons (quote unit) value))))))
            (==
            (snoc
              (map succ (cons head tail))
              (cons (quote unit) value))
            (by
              (simpa only (symm current_map)))))))))))

(theorem map_succ_range
  (forall count (is-list count)
    (implies
      (computes-to (is-nat-value count) (quote :true))
      (computes-to
        (map succ (range count))
        (tail (range (succ count))))))
  (by
    (list-induction count
      (by
        (intro count_is_nat)
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (intro count_is_nat)
        (specialize count_parts is_nat_value_cons_true_elim head tail)
        (cases count_parts head_unit tail_is_nat)
        (obtain tail_range tail_range_proof
          (range_computes_to_list tail))
        (specialize tail_map_succ induction_hypothesis)
        (specialize tail_range_all range_all_lists tail)
        (have tail_range_all_value
          (computes-to (all-lists tail_range) (quote :true))
          (by
            (calc
              (all-lists tail_range)
              (==
                (all-lists (range tail))
                (by
                  (simpa only (symm tail_range_proof))))
              (==
                (quote :true)
                (by
                  (exact tail_range_all)))))
          (by
            (calc
              (map succ (range (cons head tail)))
              (==
                (map succ (range (cons (quote unit) tail)))
                (by
                  (simpa only head_unit)))
              (==
                (map succ (snoc (range tail) tail))
                (by
                  (simpa only (range_cons (quote unit) tail))))
              (==
                (map succ (snoc tail_range tail))
                (by
                  (simpa only tail_range_proof)))
              (==
                (snoc
                  (map succ tail_range)
                  (cons (quote unit) tail))
                (by
                  (exact map_succ_snoc tail_range tail)))
              (==
                (snoc
                  (map succ (range tail))
                  (cons (quote unit) tail))
                (by
                  (simpa only (symm tail_range_proof))))
              (==
                (snoc
                  (tail (range (succ tail)))
                  (cons (quote unit) tail))
                (by
                  (simpa only tail_map_succ)))
              (==
                (snoc
                  (tail (range (cons (quote unit) tail)))
                  (cons (quote unit) tail))
                (by
                  (eval)))
              (==
                (snoc
                  (tail (snoc (range tail) tail))
                  (cons (quote unit) tail))
                (by
                  (simpa only (range_cons (quote unit) tail))))
              (==
                (snoc
                  (tail (snoc tail_range tail))
                  (cons (quote unit) tail))
                (by
                  (simpa only tail_range_proof)))
              (==
                (tail
                  (snoc
                    (snoc tail_range tail)
                    (cons (quote unit) tail)))
                (by
                  (exact
                    (symm
                      (tail_snoc_after_snoc
                        tail_range
                        tail
                        (cons (quote unit) tail))))))
              (==
                (tail
                  (snoc
                    (snoc (range tail) tail)
                    (cons (quote unit) tail)))
                (by
                  (simpa only (symm tail_range_proof))))
              (==
                (tail
                  (snoc
                    (range (cons (quote unit) tail))
                    (cons (quote unit) tail)))
                (by
                  (simpa only (symm (range_cons (quote unit) tail)))))
              (==
                (tail (range (cons (quote unit) (cons (quote unit) tail))))
                (by
                  (simpa only
                    (symm
                      (range_cons
                        (quote unit)
                        (cons (quote unit) tail))))))
              (==
                (tail (range (succ (cons head tail))))
                (by
                  (simpa only head_unit))))))))))

(theorem pred_preserves_nat_value
  (forall nat (is-list nat)
    (implies
      (computes-to (is-nat-value nat) (quote :true))
      (computes-to (is-nat-value (pred nat)) (quote :true))))
  (by
    (list-induction nat
      (by
        (intro nat_is_nat)
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (intro cons_is_nat)
        (specialize cons_parts is_nat_value_cons_true_elim head tail)
        (cases cons_parts head_unit tail_is_nat)
        (calc
          (is-nat-value (pred (cons head tail)))
          (==
            (is-nat-value tail)
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact tail_is_nat))))))))

(theorem succ_pred_inverse_for_nonzero
  (forall nat (is-list nat)
    (implies
      (computes-to (is-nat-value nat) (quote :true))
      (implies
        (computes-to (is-zero nat) (quote :false))
        (computes-to (succ (pred nat)) nat))))
  (by
    (list-induction nat
      (by
        (intro nat_is_nat)
        (intro nat_nonzero)
        (have impossible_eq
          (computes-to (quote :true) (quote :false))
          (by
            (calc
              (quote :true)
              (==
                (is-zero nil)
                (by
                  (eval)))
              (==
                (quote :false)
                (by
                  (exact nat_nonzero)))))
          (by
            (exact
              (absurd-elim
                (distinct-outcomes impossible_eq)
                (computes-to (succ (pred nil)) nil))))))
      head
      tail
      induction_hypothesis
      (by
        (intro cons_is_nat)
        (intro cons_nonzero)
        (specialize cons_parts is_nat_value_cons_true_elim head tail)
        (cases cons_parts head_unit tail_is_nat)
        (calc
          (succ (pred (cons head tail)))
          (==
            (cons (quote unit) tail)
            (by
              (eval)))
          (==
            (cons head tail)
            (by
              (simpa only (symm head_unit)))))))))

(theorem nat_eq_zero_zero
  (computes-to (nat-eq zero zero) (quote :true))
  (by
    (eval)))

(theorem nat_eq_zero_succ
  (forall right (is-list right)
    (computes-to (nat-eq zero (succ right)) (quote :false)))
  (by
    (intro right)
    (eval)))

(theorem nat_eq_succ_zero
  (forall left (is-list left)
    (computes-to (nat-eq (succ left) zero) (quote :false)))
  (by
    (intro left)
    (eval)))

(theorem nat_eq_succ_succ
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (nat-eq (succ left) (succ right))
        (nat-eq left right))))
  (by
    (intro left)
    (intro right)
    (eval)))

(theorem nat_eq_zero_left
  (forall right (is-list right)
    (computes-to
      (nat-eq zero right)
      (is-zero right)))
  (by
    (intro right)
    (eval)))

(theorem nat_eq_zero_right
  (forall left (is-list left)
    (computes-to
      (nat-eq left zero)
      (is-zero left)))
  (by
    (list-induction left
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (eval)))))

(theorem nat_eq_refl
  (forall nat (is-list nat)
    (computes-to (nat-eq nat nat) (quote :true)))
  (by
    (list-induction nat
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (calc
          (nat-eq (cons head tail) (cons head tail))
          (==
            (nat-eq tail tail)
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact induction_hypothesis))))))))

(theorem nat_eq_is_bool
  (forall left (is-list left)
    (forall right (is-list right)
      (is-bool (nat-eq left right))))
  (by
    (list-induction left
      (by
        (intro right)
        (or-elim
          (is_zero_is_bool right)
          eq_true
          (by
            (left
              (by
                (calc
                  (nat-eq nil right)
                  (==
                    (is-zero right)
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact eq_true)))))))
          eq_false
          (by
            (right
              (by
                (calc
                  (nat-eq nil right)
                  (==
                    (is-zero right)
                    (by
                      (eval)))
                  (==
                    (quote :false)
                    (by
                      (exact eq_false)))))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (right
              (by
                (eval))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (or-elim
              (induction_hypothesis right_tail)
              tail_eq_true
              (by
                (left
                  (by
                    (calc
                      (nat-eq (cons left_head left_tail) (cons right_head right_tail))
                      (==
                        (nat-eq left_tail right_tail)
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact tail_eq_true)))))))
              tail_eq_false
              (by
                (right
                  (by
                    (calc
                      (nat-eq (cons left_head left_tail) (cons right_head right_tail))
                      (==
                        (nat-eq left_tail right_tail)
                        (by
                          (eval)))
                      (==
                        (quote :false)
                        (by
                          (exact tail_eq_false))))))))))))))

(theorem nat_eq_computes_to_bool
  (forall left (is-list left)
    (forall right (is-list right)
      (is-bool (nat-eq left right))))
  (by
    (intro left)
    (intro right)
    (exact nat_eq_is_bool left right)))

(theorem value_eq_nat_eq
  (forall left (is-list left)
    (implies
      (computes-to (is-nat-value left) (quote :true))
      (forall right (is-list right)
        (implies
          (computes-to (is-nat-value right) (quote :true))
          (computes-to
            (value-eq left right)
            (nat-eq left right))))))
  (by
    (list-induction left
      (by
        (intro left_is_nat)
        (list-induction right
          (by
            (intro right_is_nat)
            (calc
              (value-eq nil nil)
              (==
                (quote :true)
                (by
                  (exact value_eq_nil)))
              (==
                (nat-eq nil nil)
                (by
                  (eval)))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro right_is_nat)
            (calc
              (value-eq nil (cons right_head right_tail))
              (==
                (quote :false)
                (by
                  (exact value_eq_nil_cons right_head right_tail)))
              (==
                (nat-eq nil (cons right_head right_tail))
                (by
                  (eval)))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (intro left_is_nat)
        (specialize left_parts is_nat_value_cons_true_elim left_head left_tail)
        (cases left_parts left_head_unit left_tail_is_nat)
        (list-induction right
          (by
            (intro right_is_nat)
            (calc
              (value-eq (cons left_head left_tail) nil)
              (==
                (quote :false)
                (by
                  (exact value_eq_cons_nil left_head left_tail)))
              (==
                (nat-eq (cons left_head left_tail) nil)
                (by
                  (eval)))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro right_is_nat)
            (specialize right_parts is_nat_value_cons_true_elim
              right_head
              right_tail)
            (cases right_parts right_head_unit right_tail_is_nat)
            (specialize tails_equal induction_hypothesis right_tail)
            (calc
              (value-eq
                (cons left_head left_tail)
                (cons right_head right_tail))
              (==
                (value-eq left_tail right_tail)
                (by
                  (simp only
                    left_head_unit
                    right_head_unit
                    (value_eq_cons
                      left_head
                      left_tail
                      right_head
                      right_tail))))
              (==
                (nat-eq left_tail right_tail)
                (by
                  (exact tails_equal)))
              (==
                (nat-eq
                  (cons left_head left_tail)
                  (cons right_head right_tail))
                (by
                  (simpa only
                    (symm left_head_unit)
                    (symm right_head_unit)))))))))))

(theorem is_nat_value_implies_is_list
  (forall value (is-value value)
    (implies
      (computes-to (is-nat-value value) (quote :true))
      (is-list value)))
  (by
    (intro value)
    (intro value_is_nat)
    (have unfolded_is_nat
      (computes-to
        (if
          (is-list-value value)
          (list-case value
            (quote :true)
            cell
            (if
              (symbol-eq (head cell) (quote unit))
              (is-nat-value (tail cell))
              (quote :false)))
          (quote :false))
        (quote :true))
      (by
        (calc
          (if
            (is-list-value value)
            (list-case value
              (quote :true)
              cell
              (if
                (symbol-eq (head cell) (quote unit))
                (is-nat-value (tail cell))
                (quote :false)))
            (quote :false))
          (==
            (is-nat-value value)
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact value_is_nat)))))
      (by
        (specialize list_parts
          if_true_result_with_false_else
          (is-list-value value)
          (list-case value
            (quote :true)
            cell
            (if
              (symbol-eq (head cell) (quote unit))
              (is-nat-value (tail cell))
              (quote :false))))
        (cases list_parts value_is_list_value list_branch_true)
        (exact is_list_value_true_implies_is_list value)))))

(theorem nat_value_eq_is_bool
  (forall left (is-list left)
    (implies
      (computes-to (is-nat-value left) (quote :true))
      (forall right (is-list right)
        (implies
          (computes-to (is-nat-value right) (quote :true))
          (is-bool (value-eq left right))))))
  (by
    (intro left)
    (intro left_is_nat)
    (intro right)
    (intro right_is_nat)
    (have value_eq_as_nat_eq
      (computes-to
        (value-eq left right)
        (nat-eq left right))
      (by
        (exact value_eq_nat_eq left right))
      (by
        (or-elim
          (nat_eq_is_bool left right)
          nats_equal
          (by
            (left
              (by
                (calc
                  (value-eq left right)
                  (==
                    (nat-eq left right)
                    (by
                      (exact value_eq_as_nat_eq)))
                  (==
                    (quote :true)
                    (by
                      (exact nats_equal)))))))
          nats_distinct
          (by
            (right
              (by
                (calc
                  (value-eq left right)
                  (==
                    (nat-eq left right)
                    (by
                      (exact value_eq_as_nat_eq)))
                  (==
                    (quote :false)
                    (by
                      (exact nats_distinct))))))))))))

(theorem member_is_bool_for_nat_list
  (forall value (is-list value)
    (implies
      (computes-to (is-nat-value value) (quote :true))
      (forall list (is-list list)
        (implies
          (computes-to
            (all
              (lambda candidate (is-nat-value candidate))
              list)
            (quote :true))
          (is-bool (member value list))))))
  (by
    (intro value)
    (intro value_is_nat)
    (list-induction list
      (by
        (intro list_all_nat)
        (right
          (by
            (exact member_nil value))))
      head
      tail
      induction_hypothesis
      (by
        (intro list_all_nat)
        (specialize list_parts all_cons_true_parts
          (lambda candidate (is-nat-value candidate))
          head
          tail)
        (cases list_parts head_is_nat tail_all_nat)
        (have head_is_nat_direct
          (computes-to (is-nat-value head) (quote :true))
          (by
            (calc
              (is-nat-value head)
              (==
                ((lambda candidate (is-nat-value candidate)) head)
                (by
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact head_is_nat)))))
          (by
            (have head_is_list
              (is-list head)
              (by
                (exact is_nat_value_implies_is_list head))
              (by
                (specialize value_head_eq_bool
                  nat_value_eq_is_bool
                  value
                  head)
                (or-elim
                  value_head_eq_bool
                  values_equal
                  (by
                    (left
                      (by
                        (exact member_cons_true value head tail))))
                  values_distinct
                  (by
                    (specialize tail_member_bool induction_hypothesis)
                    (or-elim
                      tail_member_bool
                      tail_member_true
                      (by
                        (left
                          (by
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
                                  (apply
                                    member_cons_false
                                    value
                                    head
                                    tail)))
                              (==
                                (quote :false)
                                (by
                                  (exact tail_member_false))))))))))))))))))

(theorem member_cons_or_nat_list
  (forall value (is-list value)
    (implies
      (computes-to (is-nat-value value) (quote :true))
      (forall head (is-value head)
        (forall tail (is-list tail)
          (implies
            (computes-to
              (all
                (lambda candidate (is-nat-value candidate))
                (cons head tail))
              (quote :true))
            (computes-to
              (member value (cons head tail))
              (or (value-eq value head) (member value tail))))))))
  (by
    (intro value)
    (intro value_is_nat)
    (intro head)
    (intro tail)
    (intro list_all_nat)
    (specialize list_parts all_cons_true_parts
      (lambda candidate (is-nat-value candidate))
      head
      tail)
    (cases list_parts head_is_nat tail_all_nat)
    (have head_is_nat_direct
      (computes-to (is-nat-value head) (quote :true))
      (by
        (calc
          (is-nat-value head)
          (==
            ((lambda candidate (is-nat-value candidate)) head)
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact head_is_nat)))))
      (by
        (have head_is_list
          (is-list head)
          (by
            (exact is_nat_value_implies_is_list head))
          (by
            (have tail_member_bool
              (is-bool (member value tail))
              (by
                (exact member_is_bool_for_nat_list value tail))
              (by
                (specialize value_head_eq_bool
                  nat_value_eq_is_bool
                  value
                  head)
                (or-elim
                  value_head_eq_bool
                  values_equal
                  (by
                    (have branch_true
                      (computes-to
                        (or
                          (value-eq value head)
                          (member value tail))
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
                              (apply
                                member_cons_true
                                value
                                head
                                tail)))
                          (==
                            (or
                              (value-eq value head)
                              (member value tail))
                            (by
                              (exact (symm branch_true))))))))
                  values_distinct
                  (by
                    (have branch_false
                      (computes-to
                        (or
                          (value-eq value head)
                          (member value tail))
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
                              (apply
                                member_cons_false
                                value
                                head
                                tail)))
                          (==
                            (or
                              (value-eq value head)
                              (member value tail))
                            (by
                              (exact (symm branch_false)))))))))))))))))

(theorem member_snoc_nat_list
  (forall value (is-list value)
    (implies
      (computes-to (is-nat-value value) (quote :true))
      (forall list (is-list list)
        (implies
          (computes-to
            (all
              (lambda candidate (is-nat-value candidate))
              list)
            (quote :true))
          (forall snoc_value (is-list snoc_value)
            (implies
              (computes-to
                (is-nat-value snoc_value)
                (quote :true))
              (computes-to
                (member value (snoc list snoc_value))
                (or
                  (member value list)
                  (value-eq value snoc_value)))))))))
  (by
    (intro value)
    (intro value_is_nat)
    (list-induction list
      (by
        (intro list_all_nat)
        (intro snoc_value)
        (intro snoc_value_is_nat)
        (have snoc_value_satisfies_nat_predicate
          (computes-to
            ((lambda candidate (is-nat-value candidate)) snoc_value)
            (quote :true))
          (by
            (calc
              ((lambda candidate (is-nat-value candidate)) snoc_value)
              (==
                (is-nat-value snoc_value)
                (by
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact snoc_value_is_nat)))))
          (by
            (have singleton_all_nat
          (computes-to
            (all
              (lambda candidate (is-nat-value candidate))
              (cons snoc_value nil))
            (quote :true))
          (by
            (calc
              (all
                (lambda candidate (is-nat-value candidate))
                (cons snoc_value nil))
              (==
                (all
                  (lambda candidate (is-nat-value candidate))
                  nil)
                (by
                  (apply
                    all_cons_true
                    (lambda candidate (is-nat-value candidate))
                    snoc_value
                    nil)))
              (==
                (quote :true)
                (by
                  (exact
                    all_nil
                    (lambda candidate (is-nat-value candidate)))))))
          (by
            (have cons_member
              (computes-to
                (member value (cons snoc_value nil))
                (or
                  (value-eq value snoc_value)
                  (member value nil)))
              (by
                (exact
                  member_cons_or_nat_list
                  value
                  snoc_value
                  nil))
              (by
                (have snoc_value_eq_bool
                  (is-bool (value-eq value snoc_value))
                  (by
                    (exact nat_value_eq_is_bool value snoc_value))
                  (by
                    (have nil_member_bool
                      (is-bool (member value nil))
                      (by
                        (exact
                          member_is_bool_for_nat_list
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
                              (exact cons_member)))
                          (==
                            (or
                              (member value nil)
                              (value-eq value snoc_value))
                            (by
                              (apply
                                or_comm
                                (value-eq value snoc_value)
                                (member value nil))))))))))))))))
      head
      tail
      induction_hypothesis
      (by
        (intro list_all_nat)
        (specialize list_parts all_cons_true_parts
          (lambda candidate (is-nat-value candidate))
          head
          tail)
        (cases list_parts head_is_nat tail_all_nat)
        (intro snoc_value)
        (intro snoc_value_is_nat)
        (have snoc_value_satisfies_nat_predicate
          (computes-to
            ((lambda candidate (is-nat-value candidate)) snoc_value)
            (quote :true))
          (by
            (calc
              ((lambda candidate (is-nat-value candidate)) snoc_value)
              (==
                (is-nat-value snoc_value)
                (by
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact snoc_value_is_nat)))))
          (by
            (obtain tail_snoc tail_snoc_proof
              (snoc_computes_to_list tail snoc_value))
        (have tail_snoc_all_nat
          (computes-to
            (all
              (lambda candidate (is-nat-value candidate))
              tail_snoc)
            (quote :true))
          (by
            (calc
              (all
                (lambda candidate (is-nat-value candidate))
                tail_snoc)
              (==
                (all
                  (lambda candidate (is-nat-value candidate))
                  (snoc tail snoc_value))
                (by
                  (simpa only (symm tail_snoc_proof))))
              (==
                (quote :true)
                (by
                  (exact
                    all_snoc_true
                    (lambda candidate (is-nat-value candidate))
                    tail
                    snoc_value)))))
          (by
            (have current_member_step
              (computes-to
                (member value (cons head tail))
                (or
                  (value-eq value head)
                  (member value tail)))
              (by
                (exact
                  member_cons_or_nat_list
                  value
                  head
                  tail))
              (by
                (have head_tail_snoc_all_nat
                  (computes-to
                    (all
                      (lambda candidate (is-nat-value candidate))
                      (cons head tail_snoc))
                    (quote :true))
                  (by
                    (calc
                      (all
                        (lambda candidate (is-nat-value candidate))
                        (cons head tail_snoc))
                      (==
                        (all
                          (lambda candidate (is-nat-value candidate))
                          tail_snoc)
                        (by
                          (apply
                            all_cons_true
                            (lambda candidate (is-nat-value candidate))
                            head
                            tail_snoc)))
                      (==
                        (quote :true)
                        (by
                          (exact tail_snoc_all_nat)))))
                  (by
                    (have snoc_member_step
                  (computes-to
                    (member value (cons head tail_snoc))
                    (or
                      (value-eq value head)
                      (member value tail_snoc)))
                  (by
                    (exact
                      member_cons_or_nat_list
                      value
                      head
                      tail_snoc))
                  (by
                    (specialize tail_member_snoc
                      induction_hypothesis
                      snoc_value)
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
                          (exact snoc_member_step)))
                      (==
                        (or
                          (value-eq value head)
                          (member value (snoc tail snoc_value)))
                        (by
                          (simpa only (symm tail_snoc_proof))))
                      (==
                        (or
                          (value-eq value head)
                          (or
                            (member value tail)
                            (value-eq value snoc_value)))
                        (by
                          (rewrite
                            tail_member_snoc)
                          (eval)))
                      (==
                        (or
                          (or
                            (value-eq value head)
                            (member value tail))
                          (value-eq value snoc_value))
                        (by
                          (have head_is_nat_direct
                            (computes-to
                              (is-nat-value head)
                              (quote :true))
                            (by
                              (calc
                                (is-nat-value head)
                                (==
                                  ((lambda candidate
                                    (is-nat-value candidate)) head)
                                  (by
                                    (eval)))
                                (==
                                  (quote :true)
                                  (by
                                    (exact head_is_nat)))))
                            (by
                              (have head_is_list
                                (is-list head)
                                (by
                                  (exact is_nat_value_implies_is_list head))
                                (by
                                  (have value_head_eq_bool
                                    (is-bool (value-eq value head))
                                    (by
                                      (exact
                                        nat_value_eq_is_bool
                                        value
                                        head))
                                    (by
                                      (have tail_member_bool
                                        (is-bool (member value tail))
                                        (by
                                          (exact
                                            member_is_bool_for_nat_list
                                            value
                                            tail))
                                        (by
                                          (have snoc_value_eq_bool
                                            (is-bool
                                              (value-eq
                                                value
                                                snoc_value))
                                            (by
                                              (exact
                                                nat_value_eq_is_bool
                                                value
                                                snoc_value))
                                            (by
                                              (have member_snoc_nat_assoc
                                                (computes-to
                                                  (or
                                                    (or
                                                      (value-eq value head)
                                                      (member value tail))
                                                    (value-eq
                                                      value
                                                      snoc_value))
                                                  (or
                                                    (value-eq value head)
                                                    (or
                                                      (member value tail)
                                                      (value-eq
                                                        value
                                                        snoc_value))))
                                                (by
                                                  (apply
                                                    or_assoc
                                                    (value-eq value head)
                                                    (member value tail)
                                                    (value-eq
                                                      value
                                                      snoc_value)))
                                                (by
                                                  (exact
                                                    (symm
                                                      member_snoc_nat_assoc))))))))))))))))
                      (==
                        (or
                          (member value (cons head tail))
                          (value-eq value snoc_value))
                        (by
                          (rewrite (symm current_member_step))
                          (eval))))))))))))))))))

(theorem is_nat_value_implies_value_eq_comparable
  (forall value (is-list value)
    (implies
      (computes-to (is-nat-value value) (quote :true))
      (computes-to
        (value-eq-comparable value)
        (quote :true))))
  (by
    (list-induction value
      (by
        (intro value_is_nat)
        (exact value_eq_comparable_nil))
      head
      tail
      induction_hypothesis
      (by
        (intro value_is_nat)
        (specialize value_parts
          is_nat_value_cons_true_elim
          head
          tail)
        (cases value_parts head_unit tail_is_nat)
        (specialize tail_comparable induction_hypothesis)
        (have head_comparable
          (computes-to
            (value-eq-comparable head)
            (quote :true))
          (by
            (calc
              (value-eq-comparable head)
              (==
                (value-eq-comparable (quote unit))
                (by
                  (simpa only head_unit)))
              (==
                (quote :true)
                (by
                  (eval)))))
          (by
            (apply
              value_eq_comparable_cons
              head
              tail))))))
  )

(theorem nat_eq_pred_succ
  (forall nat (is-list nat)
    (computes-to
      (nat-eq (pred (succ nat)) nat)
      (quote :true)))
  (by
    (intro nat)
    (calc
      (nat-eq (pred (succ nat)) nat)
      (==
        (nat-eq nat nat)
        (by
          (simpa only (pred_succ nat))))
      (==
        (quote :true)
        (by
          (exact nat_eq_refl nat))))))

(theorem nat_le_zero_left
  (forall right (is-list right)
    (computes-to (nat-le zero right) (quote :true)))
  (by
    (intro right)
    (eval)))

(theorem nat_le_zero_right
  (forall left (is-list left)
    (computes-to
      (nat-le left zero)
      (is-zero left)))
  (by
    (list-induction left
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (eval)))))

(theorem nat_le_succ_zero
  (forall left (is-list left)
    (computes-to (nat-le (succ left) zero) (quote :false)))
  (by
    (intro left)
    (eval)))

(theorem nat_le_succ_succ
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (nat-le (succ left) (succ right))
        (nat-le left right))))
  (by
    (intro left)
    (intro right)
    (eval)))

(theorem nat_le_refl
  (forall nat (is-list nat)
    (computes-to (nat-le nat nat) (quote :true)))
  (by
    (list-induction nat
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (calc
          (nat-le (cons head tail) (cons head tail))
          (==
            (nat-le tail tail)
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact induction_hypothesis))))))))

(theorem min_le_left
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (nat-le (min left right) left)
        (quote :true))))
  (by
    (list-induction left
      (by
        (intro right)
        (calc
          (nat-le (min nil right) nil)
          (==
            (nat-le nil nil)
            (by
              (eval)))
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
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (obtain tail_min tail_min_proof
              (min_computes_to_list left_tail right_tail))
            (calc
              (nat-le
                (min (cons left_head left_tail) (cons right_head right_tail))
                (cons left_head left_tail))
              (==
                (nat-le
                  (succ (min left_tail right_tail))
                  (cons left_head left_tail))
                (by
                  (eval)))
              (==
                (nat-le
                  (succ tail_min)
                  (cons left_head left_tail))
                (by
                  (simpa only tail_min_proof)))
              (==
                (nat-le
                  (cons (quote unit) tail_min)
                  (cons left_head left_tail))
                (by
                  (eval)))
              (==
                (nat-le tail_min left_tail)
                (by
                  (eval)))
              (==
                (nat-le (min left_tail right_tail) left_tail)
                (by
                  (simpa only (symm tail_min_proof))))
              (==
                (quote :true)
                (by
                  (exact induction_hypothesis right_tail))))))))))

(theorem min_le_right
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (nat-le (min left right) right)
        (quote :true))))
  (by
    (list-induction left
      (by
        (intro right)
        (calc
          (nat-le (min nil right) right)
          (==
            (nat-le nil right)
            (by
              (eval)))
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
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (obtain tail_min tail_min_proof
              (min_computes_to_list left_tail right_tail))
            (calc
              (nat-le
                (min (cons left_head left_tail) (cons right_head right_tail))
                (cons right_head right_tail))
              (==
                (nat-le
                  (succ (min left_tail right_tail))
                  (cons right_head right_tail))
                (by
                  (eval)))
              (==
                (nat-le
                  (succ tail_min)
                  (cons right_head right_tail))
                (by
                  (simpa only tail_min_proof)))
              (==
                (nat-le
                  (cons (quote unit) tail_min)
                  (cons right_head right_tail))
                (by
                  (eval)))
              (==
                (nat-le tail_min right_tail)
                (by
                  (eval)))
              (==
                (nat-le (min left_tail right_tail) right_tail)
                (by
                  (simpa only (symm tail_min_proof))))
              (==
                (quote :true)
                (by
                  (exact induction_hypothesis right_tail))))))))))

(theorem left_le_max
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (nat-le left (max left right))
        (quote :true))))
  (by
    (list-induction left
      (by
        (intro right)
        (calc
          (nat-le nil (max nil right))
          (==
            (nat-le nil right)
            (by
              (simpa only (max_zero_left right))))
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
            (calc
              (nat-le
                (cons left_head left_tail)
                (max (cons left_head left_tail) nil))
              (==
                (nat-le
                  (cons left_head left_tail)
                  (cons left_head left_tail))
                (by
                  (simpa only
                    (max_zero_right (cons left_head left_tail)))))
              (==
                (quote :true)
                (by
                  (exact nat_le_refl (cons left_head left_tail))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (obtain tail_max tail_max_proof
              (max_computes_to_list left_tail right_tail))
            (calc
              (nat-le
                (cons left_head left_tail)
                (max (cons left_head left_tail) (cons right_head right_tail)))
              (==
                (nat-le
                  (cons left_head left_tail)
                  (succ (max left_tail right_tail)))
                (by
                  (eval)))
              (==
                (nat-le
                  (cons left_head left_tail)
                  (succ tail_max))
                (by
                  (simpa only tail_max_proof)))
              (==
                (nat-le
                  (cons left_head left_tail)
                  (cons (quote unit) tail_max))
                (by
                  (eval)))
              (==
                (nat-le left_tail tail_max)
                (by
                  (eval)))
              (==
                (nat-le left_tail (max left_tail right_tail))
                (by
                  (simpa only (symm tail_max_proof))))
              (==
                (quote :true)
                (by
                  (exact induction_hypothesis right_tail))))))))))

(theorem right_le_max
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (nat-le right (max left right))
        (quote :true))))
  (by
    (list-induction left
      (by
        (intro right)
        (calc
          (nat-le right (max nil right))
          (==
            (nat-le right right)
            (by
              (simpa only (max_zero_left right))))
          (==
            (quote :true)
            (by
              (exact nat_le_refl right)))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (obtain tail_max tail_max_proof
              (max_computes_to_list left_tail right_tail))
            (calc
              (nat-le
                (cons right_head right_tail)
                (max (cons left_head left_tail) (cons right_head right_tail)))
              (==
                (nat-le
                  (cons right_head right_tail)
                  (succ (max left_tail right_tail)))
                (by
                  (eval)))
              (==
                (nat-le
                  (cons right_head right_tail)
                  (succ tail_max))
                (by
                  (simpa only tail_max_proof)))
              (==
                (nat-le
                  (cons right_head right_tail)
                  (cons (quote unit) tail_max))
                (by
                  (eval)))
              (==
                (nat-le right_tail tail_max)
                (by
                  (eval)))
              (==
                (nat-le right_tail (max left_tail right_tail))
                (by
                  (simpa only (symm tail_max_proof))))
              (==
                (quote :true)
                (by
                  (exact induction_hypothesis right_tail))))))))))

(theorem min_comm
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (min left right)
        (min right left))))
  (by
    (list-induction left
      (by
        (list-induction right
          (by
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (eval))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (calc
              (min (cons left_head left_tail) (cons right_head right_tail))
              (==
                (succ (min left_tail right_tail))
                (by
                  (eval)))
              (==
                (succ (min right_tail left_tail))
                (by
                  (simpa only (induction_hypothesis right_tail))))
              (==
                (min (cons right_head right_tail) (cons left_head left_tail))
                (by
                  (eval))))))))))

(theorem max_comm
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (max left right)
        (max right left))))
  (by
    (list-induction left
      (by
        (list-induction right
          (by
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (eval))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (calc
              (max (cons left_head left_tail) (cons right_head right_tail))
              (==
                (succ (max left_tail right_tail))
                (by
                  (eval)))
              (==
                (succ (max right_tail left_tail))
                (by
                  (simpa only (induction_hypothesis right_tail))))
              (==
                (max (cons right_head right_tail) (cons left_head left_tail))
                (by
                  (eval))))))))))

(theorem min_assoc
  (forall left (is-list left)
    (forall middle (is-list middle)
      (forall right (is-list right)
        (computes-to
          (min (min left middle) right)
          (min left (min middle right))))))
  (by
    (list-induction left
      (by
        (intro middle)
        (intro right)
        (obtain middle_right middle_right_proof
          (min_computes_to_list middle right))
        (calc
          (min (min nil middle) right)
          (==
            nil
            (by
              (eval)))
          (==
            (min nil middle_right)
            (by
              (exact
                (symm
                  (eval-to
                    (min nil middle_right)
                    nil)))))
          (==
            (min nil (min middle right))
            (by
              (simpa only (symm middle_right_proof))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction middle
          (by
            (intro right)
            (calc
              (min (min (cons left_head left_tail) nil) right)
              (==
                nil
                (by
                  (eval)))
              (==
                (min (cons left_head left_tail) (min nil right))
                (by
                  (exact
                    (symm
                      (eval-to
                        (min (cons left_head left_tail) (min nil right))
                        nil)))))))
          middle_head
          middle_tail
          middle_induction_hypothesis
          (by
            (list-induction right
              (by
                (obtain left_middle left_middle_proof
                  (min_computes_to_list left_tail middle_tail))
                (calc
                  (min
                    (min
                      (cons left_head left_tail)
                      (cons middle_head middle_tail))
                    nil)
                  (==
                    (min (succ (min left_tail middle_tail)) nil)
                    (by
                      (simpa only
                        (min_cons
                          left_head
                          left_tail
                          middle_head
                          middle_tail))))
                  (==
                    (min (succ left_middle) nil)
                    (by
                      (simpa only left_middle_proof)))
                  (==
                    nil
                    (by
                      (eval)))
                  (==
                    (min
                      (cons left_head left_tail)
                      (min (cons middle_head middle_tail) nil))
                    (by
                      (exact
                        (symm
                          (eval-to
                            (min
                              (cons left_head left_tail)
                              (min (cons middle_head middle_tail) nil))
                            nil)))))))
              right_head
              right_tail
              right_induction_hypothesis
              (by
                (obtain left_middle left_middle_proof
                  (min_computes_to_list left_tail middle_tail))
                (obtain middle_right middle_right_proof
                  (min_computes_to_list middle_tail right_tail))
                (have min_succ_middle_right
                  (computes-to
                    (min (cons left_head left_tail) (succ middle_right))
                    (succ (min left_tail middle_right)))
                  (by
                    (calc
                      (min (cons left_head left_tail) (succ middle_right))
                      (==
                        (min
                          (cons left_head left_tail)
                          (cons (quote unit) middle_right))
                        (by
                          (eval)))
                      (==
                        (succ (min left_tail middle_right))
                        (by
                          (exact
                            (min_cons
                              left_head
                              left_tail
                              (quote unit)
                              middle_right))))))
                  (by
                    (calc
                      (min
                        (min
                          (cons left_head left_tail)
                          (cons middle_head middle_tail))
                        (cons right_head right_tail))
                      (==
                        (min
                          (succ (min left_tail middle_tail))
                          (cons right_head right_tail))
                        (by
                          (simpa only
                            (min_cons
                              left_head
                              left_tail
                              middle_head
                              middle_tail))))
                      (==
                        (min
                          (succ left_middle)
                          (cons right_head right_tail))
                        (by
                          (simpa only left_middle_proof)))
                      (==
                        (succ (min left_middle right_tail))
                        (by
                          (eval)))
                      (==
                        (succ (min (min left_tail middle_tail) right_tail))
                        (by
                          (simpa only (symm left_middle_proof))))
                      (==
                        (succ (min left_tail (min middle_tail right_tail)))
                        (by
                          (simpa only
                            (induction_hypothesis middle_tail right_tail))))
                      (==
                        (succ (min left_tail middle_right))
                        (by
                          (simpa only middle_right_proof)))
                      (==
                        (min (cons left_head left_tail) (succ middle_right))
                        (by
                          (exact (symm min_succ_middle_right))))
                      (==
                        (min
                          (cons left_head left_tail)
                          (succ (min middle_tail right_tail)))
                        (by
                          (simpa only (symm middle_right_proof))))
                      (==
                        (min
                          (cons left_head left_tail)
                          (min
                            (cons middle_head middle_tail)
                            (cons right_head right_tail)))
                        (by
                          (simpa only
                            (symm
                              (min_cons
                                middle_head
                                middle_tail
                                right_head
                                right_tail))))))))))))))))

(theorem max_assoc
  (forall left (is-list left)
    (forall middle (is-list middle)
      (forall right (is-list right)
        (computes-to
          (max (max left middle) right)
          (max left (max middle right))))))
  (by
    (list-induction left
      (by
        (intro middle)
        (intro right)
        (obtain middle_right middle_right_proof
          (max_computes_to_list middle right))
        (calc
          (max (max nil middle) right)
          (==
            (max middle right)
            (by
              (eval)))
          (==
            middle_right
            (by
              (exact middle_right_proof)))
          (==
            (max nil middle_right)
            (by
              (exact
                (symm
                  (eval-to
                    (max nil middle_right)
                    middle_right)))))
          (==
            (max nil (max middle right))
            (by
              (simpa only (symm middle_right_proof))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction middle
          (by
            (intro right)
            (calc
              (max (max (cons left_head left_tail) nil) right)
              (==
                (max (cons left_head left_tail) right)
                (by
                  (eval)))
              (==
                (max (cons left_head left_tail) (max nil right))
                (by
                  (rewrite
                    (symm
                      (eval-to
                        (max nil right)
                        right)))
                  (eval)))))
          middle_head
          middle_tail
          middle_induction_hypothesis
          (by
            (list-induction right
              (by
                (obtain left_middle left_middle_proof
                  (max_computes_to_list left_tail middle_tail))
                (calc
                  (max
                    (max
                      (cons left_head left_tail)
                      (cons middle_head middle_tail))
                    nil)
                  (==
                    (max (succ (max left_tail middle_tail)) nil)
                    (by
                      (simpa only
                        (max_cons
                          left_head
                          left_tail
                          middle_head
                          middle_tail))))
                  (==
                    (max (succ left_middle) nil)
                    (by
                      (simpa only left_middle_proof)))
                  (==
                    (succ left_middle)
                    (by
                      (eval)))
                  (==
                    (succ (max left_tail middle_tail))
                    (by
                      (simpa only (symm left_middle_proof))))
                  (==
                    (max
                      (cons left_head left_tail)
                      (cons middle_head middle_tail))
                    (by
                      (simpa only
                        (symm
                          (max_cons
                            left_head
                            left_tail
                            middle_head
                            middle_tail)))))
                  (==
                    (max
                      (cons left_head left_tail)
                      (max (cons middle_head middle_tail) nil))
                    (by
                      (rewrite
                        (symm
                          (eval-to
                            (max (cons middle_head middle_tail) nil)
                            (cons middle_head middle_tail))))
                      (eval)))))
              right_head
              right_tail
              right_induction_hypothesis
              (by
                (obtain left_middle left_middle_proof
                  (max_computes_to_list left_tail middle_tail))
                (obtain middle_right middle_right_proof
                  (max_computes_to_list middle_tail right_tail))
                (have max_succ_middle_right
                  (computes-to
                    (max (cons left_head left_tail) (succ middle_right))
                    (succ (max left_tail middle_right)))
                  (by
                    (calc
                      (max (cons left_head left_tail) (succ middle_right))
                      (==
                        (max
                          (cons left_head left_tail)
                          (cons (quote unit) middle_right))
                        (by
                          (eval)))
                      (==
                        (succ (max left_tail middle_right))
                        (by
                          (exact
                            (max_cons
                              left_head
                              left_tail
                              (quote unit)
                              middle_right))))))
                  (by
                    (calc
                      (max
                        (max
                          (cons left_head left_tail)
                          (cons middle_head middle_tail))
                        (cons right_head right_tail))
                      (==
                        (max
                          (succ (max left_tail middle_tail))
                          (cons right_head right_tail))
                        (by
                          (simpa only
                            (max_cons
                              left_head
                              left_tail
                              middle_head
                              middle_tail))))
                      (==
                        (max
                          (succ left_middle)
                          (cons right_head right_tail))
                        (by
                          (simpa only left_middle_proof)))
                      (==
                        (succ (max left_middle right_tail))
                        (by
                          (eval)))
                      (==
                        (succ (max (max left_tail middle_tail) right_tail))
                        (by
                          (simpa only (symm left_middle_proof))))
                      (==
                        (succ (max left_tail (max middle_tail right_tail)))
                        (by
                          (simpa only
                            (induction_hypothesis middle_tail right_tail))))
                      (==
                        (succ (max left_tail middle_right))
                        (by
                          (simpa only middle_right_proof)))
                      (==
                        (max (cons left_head left_tail) (succ middle_right))
                        (by
                          (exact (symm max_succ_middle_right))))
                      (==
                        (max
                          (cons left_head left_tail)
                          (succ (max middle_tail right_tail)))
                        (by
                          (simpa only (symm middle_right_proof))))
                      (==
                        (max
                          (cons left_head left_tail)
                          (max
                            (cons middle_head middle_tail)
                            (cons right_head right_tail)))
                        (by
                          (simpa only
                            (symm
                              (max_cons
                                middle_head
                                middle_tail
                                right_head
                                right_tail))))))))))))))))

(theorem min_left
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-le left right) (quote :true))
        (computes-to
          (nat-eq (min left right) left)
          (quote :true)))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro left_le_right)
        (eval))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
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
                      (nat-eq (min (cons left_head left_tail) nil)
                        (cons left_head left_tail))
                      (quote :true)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro left_le_right)
            (have tail_le
              (computes-to (nat-le left_tail right_tail) (quote :true))
              (by
                (calc
                  (nat-le left_tail right_tail)
                  (==
                    (nat-le
                      (cons left_head left_tail)
                      (cons right_head right_tail))
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact left_le_right)))))
              (by
                (obtain tail_min tail_min_proof
                  (min_computes_to_list left_tail right_tail))
                (calc
                  (nat-eq
                    (min (cons left_head left_tail) (cons right_head right_tail))
                    (cons left_head left_tail))
                  (==
                    (nat-eq
                      (succ (min left_tail right_tail))
                      (cons left_head left_tail))
                    (by
                      (eval)))
                  (==
                    (nat-eq
                      (succ tail_min)
                      (cons left_head left_tail))
                    (by
                      (simpa only tail_min_proof)))
                  (==
                    (nat-eq
                      (cons (quote unit) tail_min)
                      (cons left_head left_tail))
                    (by
                      (eval)))
                  (==
                    (nat-eq tail_min left_tail)
                    (by
                      (eval)))
                  (==
                    (nat-eq (min left_tail right_tail) left_tail)
                    (by
                      (simpa only (symm tail_min_proof))))
                  (==
                    (quote :true)
                    (by
                      (exact induction_hypothesis right_tail))))))))))))

(theorem min_right
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-le right left) (quote :true))
        (computes-to
          (nat-eq (min left right) right)
          (quote :true)))))
  (by
    (intro left)
    (intro right)
    (intro right_le_left)
    (calc
      (nat-eq (min left right) right)
      (==
        (nat-eq (min right left) right)
        (by
          (simpa only (min_comm left right))))
      (==
        (quote :true)
        (by
          (exact min_left right left))))))

(theorem max_right
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-le left right) (quote :true))
        (computes-to
          (nat-eq (max left right) right)
          (quote :true)))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro left_le_right)
        (calc
          (nat-eq (max nil right) right)
          (==
            (nat-eq right right)
            (by
              (simpa only (max_zero_left right))))
          (==
            (quote :true)
            (by
              (exact nat_eq_refl right)))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
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
                      (nat-eq
                        (max (cons left_head left_tail) nil)
                        nil)
                      (quote :true)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro left_le_right)
            (have tail_le
              (computes-to (nat-le left_tail right_tail) (quote :true))
              (by
                (calc
                  (nat-le left_tail right_tail)
                  (==
                    (nat-le
                      (cons left_head left_tail)
                      (cons right_head right_tail))
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact left_le_right)))))
              (by
                (obtain tail_max tail_max_proof
                  (max_computes_to_list left_tail right_tail))
                (calc
                  (nat-eq
                    (max (cons left_head left_tail) (cons right_head right_tail))
                    (cons right_head right_tail))
                  (==
                    (nat-eq
                      (succ (max left_tail right_tail))
                      (cons right_head right_tail))
                    (by
                      (eval)))
                  (==
                    (nat-eq
                      (succ tail_max)
                      (cons right_head right_tail))
                    (by
                      (simpa only tail_max_proof)))
                  (==
                    (nat-eq
                      (cons (quote unit) tail_max)
                      (cons right_head right_tail))
                    (by
                      (eval)))
                  (==
                    (nat-eq tail_max right_tail)
                    (by
                      (eval)))
                  (==
                    (nat-eq (max left_tail right_tail) right_tail)
                    (by
                      (simpa only (symm tail_max_proof))))
                  (==
                    (quote :true)
                    (by
                      (exact induction_hypothesis right_tail))))))))))))

(theorem max_left
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-le right left) (quote :true))
        (computes-to
          (nat-eq (max left right) left)
          (quote :true)))))
  (by
    (intro left)
    (intro right)
    (intro right_le_left)
    (calc
      (nat-eq (max left right) left)
      (==
        (nat-eq (max right left) left)
        (by
          (simpa only (max_comm left right))))
      (==
        (quote :true)
        (by
          (exact max_right right left))))))

(theorem length_zip_min
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (length (zip left right))
        (min (length left) (length right)))))
  (by
    (list-induction left
      (by
        (intro right)
        (obtain right_length right_length_proof
          (length_computes_to_list right))
        (have length_nil_zero
          (computes-to (length nil) zero)
          (by
            (calc
              (length nil)
              (==
                nil
                (by
                  (exact length_nil)))
              (==
                zero
                (by
                  (exact (symm zero_eq_nil))))))
          (by
            (calc
              (length (zip nil right))
              (==
                nil
                (by
                  (eval)))
              (==
                zero
                (by
                  (exact (symm zero_eq_nil))))
              (==
                (min zero right_length)
                (by
                  (exact (symm (min_zero_left right_length)))))
              (==
                (min (length nil) right_length)
                (by
                  (rewrite (symm length_nil_zero))
                  (eval)))
              (==
                (min (length nil) (length right))
                (by
                  (simpa only (symm right_length_proof))))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (obtain left_length left_length_proof
              (length_computes_to_list (cons left_head left_tail)))
            (have length_nil_zero
              (computes-to (length nil) zero)
              (by
                (calc
                  (length nil)
                  (==
                    nil
                    (by
                      (exact length_nil)))
                  (==
                    zero
                    (by
                      (exact (symm zero_eq_nil))))))
              (by
                (calc
                  (length (zip (cons left_head left_tail) nil))
                  (==
                    nil
                    (by
                      (eval)))
                  (==
                    zero
                    (by
                      (exact (symm zero_eq_nil))))
                  (==
                    (min left_length zero)
                    (by
                      (exact (symm (min_zero_right left_length)))))
                  (==
                    (min
                      (length (cons left_head left_tail))
                      zero)
                    (by
                      (rewrite (symm left_length_proof))
                      (eval)))
                  (==
                    (min
                      (length (cons left_head left_tail))
                      (length nil))
                    (by
                      (rewrite (symm length_nil_zero))
                      (eval)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (obtain zipped_tail zipped_tail_proof
              (zip_computes_to_list left_tail right_tail))
            (obtain left_length left_length_proof
              (length_computes_to_list left_tail))
            (obtain right_length right_length_proof
              (length_computes_to_list right_tail))
            (obtain tail_min tail_min_proof
              (min_computes_to_list left_length right_length))
            (calc
              (length
                (zip
                  (cons left_head left_tail)
                  (cons right_head right_tail)))
              (==
                (length
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
                (length
                  (cons
                    (cons left_head (cons right_head nil))
                    zipped_tail))
                (by
                  (simpa only zipped_tail_proof)))
              (==
                (cons (quote unit) (length zipped_tail))
                (by
                  (exact
                    length_cons
                    (cons left_head (cons right_head nil))
                    zipped_tail)))
              (==
                (cons
                  (quote unit)
                  (length (zip left_tail right_tail)))
                (by
                  (simpa only (symm zipped_tail_proof))))
              (==
                (cons
                  (quote unit)
                  (min (length left_tail) (length right_tail)))
                (by
                  (simpa only (induction_hypothesis right_tail))))
              (==
                (cons
                  (quote unit)
                  (min left_length (length right_tail)))
                (by
                  (simpa only left_length_proof)))
              (==
                (cons
                  (quote unit)
                  (min left_length right_length))
                (by
                  (simpa only right_length_proof)))
              (==
                (cons (quote unit) tail_min)
                (by
                  (simpa only tail_min_proof)))
              (==
                (succ tail_min)
                (by
                  (eval)))
              (==
                (succ (min left_length right_length))
                (by
                  (simpa only (symm tail_min_proof))))
              (==
                (min
                  (cons (quote unit) left_length)
                  (cons (quote unit) right_length))
                (by
                  (exact
                    (symm
                      (min_cons
                        (quote unit)
                        left_length
                        (quote unit)
                        right_length)))))
              (==
                (min
                  (cons (quote unit) (length left_tail))
                  (cons (quote unit) right_length))
                (by
                  (simpa only (symm left_length_proof))))
              (==
                (min
                  (cons (quote unit) (length left_tail))
                  (cons (quote unit) (length right_tail)))
                (by
                  (simpa only (symm right_length_proof))))
              (==
                (min
                  (length (cons left_head left_tail))
                  (cons (quote unit) (length right_tail)))
                (by
                  (simpa only (length_cons left_head left_tail))))
              (==
                (min
                  (length (cons left_head left_tail))
                  (length (cons right_head right_tail)))
                (by
                  (simpa only (length_cons right_head right_tail)))))))))))

(theorem nat_le_of_equal_lists
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to left right)
        (computes-to (nat-le left right) (quote :true)))))
  (by
    (intro left)
    (intro right)
    (intro values_equal)
    (calc
      (nat-le left right)
      (==
        (nat-le right right)
        (by
          (simpa only values_equal)))
      (==
        (quote :true)
        (by
          (exact nat_le_refl right))))))

(theorem nat_le_is_bool
  (forall left (is-list left)
    (forall right (is-list right)
      (is-bool (nat-le left right))))
  (by
    (list-induction left
      (by
        (intro right)
        (left
          (by
            (eval))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (right
              (by
                (eval))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (or-elim
              (induction_hypothesis right_tail)
              tail_le_true
              (by
                (left
                  (by
                    (calc
                      (nat-le (cons left_head left_tail) (cons right_head right_tail))
                      (==
                        (nat-le left_tail right_tail)
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact tail_le_true)))))))
              tail_le_false
              (by
                (right
                  (by
                    (calc
                      (nat-le (cons left_head left_tail) (cons right_head right_tail))
                      (==
                        (nat-le left_tail right_tail)
                        (by
                          (eval)))
                      (==
                        (quote :false)
                        (by
                          (exact tail_le_false))))))))))))))

(theorem nat_le_computes_to_bool
  (forall left (is-list left)
    (forall right (is-list right)
      (is-bool (nat-le left right))))
  (by
    (intro left)
    (intro right)
    (exact nat_le_is_bool left right)))

(theorem nat_lt_zero_zero
  (computes-to (nat-lt zero zero) (quote :false))
  (by
    (eval)))

(theorem nat_lt_zero_succ
  (forall right (is-list right)
    (computes-to (nat-lt zero (succ right)) (quote :true)))
  (by
    (intro right)
    (eval)))

(theorem nat_lt_zero_cons_true
  (forall head (is-value head)
    (forall tail (is-list tail)
      (computes-to
        (nat-lt zero (cons head tail))
        (quote :true))))
  (by
    (intro head)
    (intro tail)
    (eval)))

(theorem nat_le_cons_zero_false
  (forall head (is-value head)
    (forall tail (is-list tail)
      (computes-to
        (nat-le (cons head tail) zero)
        (quote :false))))
  (by
    (intro head)
    (intro tail)
    (eval)))

(theorem nat_lt_cons_zero_false
  (forall head (is-value head)
    (forall tail (is-list tail)
      (computes-to
        (nat-lt (cons head tail) zero)
        (quote :false))))
  (by
    (intro head)
    (intro tail)
    (eval)))

(theorem nat_lt_zero_right_false
  (forall left (is-list left)
    (computes-to (nat-lt left zero) (quote :false)))
  (by
    (list-induction left
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (exact nat_lt_cons_zero_false head tail)))))

(theorem nat_lt_zero_implies_is_zero_false
  (forall nat (is-list nat)
    (implies
      (computes-to (nat-lt zero nat) (quote :true))
      (computes-to (is-zero nat) (quote :false))))
  (by
    (list-induction nat
      (by
        (intro nat_positive)
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
                  (exact nat_positive)))))
          (by
            (exact
              (absurd-elim
                (distinct-outcomes impossible_eq)
                (computes-to (is-zero nil) (quote :false)))))))
      head
      tail
      induction_hypothesis
      (by
        (intro nat_positive)
        (exact is_zero_cons_false head tail)))))

(theorem is_zero_false_implies_nat_lt_zero
  (forall nat (is-list nat)
    (implies
      (computes-to (is-zero nat) (quote :false))
      (computes-to (nat-lt zero nat) (quote :true))))
  (by
    (list-induction nat
      (by
        (intro nat_not_zero)
        (have impossible_eq
          (computes-to (quote :true) (quote :false))
          (by
            (calc
              (quote :true)
              (==
                (is-zero nil)
                (by
                  (eval)))
              (==
                (quote :false)
                (by
                  (exact nat_not_zero)))))
          (by
            (exact
              (absurd-elim
                (distinct-outcomes impossible_eq)
                (computes-to (nat-lt zero nil) (quote :true)))))))
      head
      tail
      induction_hypothesis
      (by
        (intro nat_not_zero)
        (exact nat_lt_zero_cons_true head tail)))))

(theorem nat_lt_zero_implies_nat_le_zero_false
  (forall nat (is-list nat)
    (implies
      (computes-to (nat-lt zero nat) (quote :true))
      (computes-to (nat-le nat zero) (quote :false))))
  (by
    (list-induction nat
      (by
        (intro nat_positive)
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
                  (exact nat_positive)))))
          (by
            (exact
              (absurd-elim
                (distinct-outcomes impossible_eq)
                (computes-to (nat-le nil zero) (quote :false)))))))
      head
      tail
      induction_hypothesis
      (by
        (intro nat_positive)
        (exact nat_le_cons_zero_false head tail)))))

(theorem nat_lt_zero_implies_nat_lt_nat_zero_false
  (forall nat (is-list nat)
    (implies
      (computes-to (nat-lt zero nat) (quote :true))
      (computes-to (nat-lt nat zero) (quote :false))))
  (by
    (list-induction nat
      (by
        (intro nat_positive)
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
                  (exact nat_positive)))))
          (by
            (exact
              (absurd-elim
                (distinct-outcomes impossible_eq)
                (computes-to (nat-lt nil zero) (quote :false)))))))
      head
      tail
      induction_hypothesis
      (by
        (intro nat_positive)
        (exact nat_lt_cons_zero_false head tail)))))

(theorem nat_lt_succ_zero
  (forall left (is-list left)
    (computes-to (nat-lt (succ left) zero) (quote :false)))
  (by
    (intro left)
    (eval)))

(theorem nat_lt_succ_succ
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (nat-lt (succ left) (succ right))
        (nat-lt left right))))
  (by
    (intro left)
    (intro right)
    (eval)))

(theorem nat_lt_succ_right_or_eq
  (forall right (is-list right)
    (implies
      (computes-to (is-nat-value right) (quote :true))
      (forall left (is-list left)
        (implies
          (computes-to (is-nat-value left) (quote :true))
          (computes-to
            (nat-lt left (succ right))
            (or (nat-lt left right) (nat-eq left right)))))))
  (by
    (list-induction right
      (by
        (intro right_is_nat)
        (list-induction left
          (by
            (intro left_is_nat)
            (eval))
          left_head
          left_tail
          left_induction_hypothesis
          (by
            (intro left_is_nat)
            (calc
              (nat-lt (cons left_head left_tail) (succ nil))
              (==
                (nat-lt left_tail nil)
                (by
                  (eval)))
              (==
                (nat-lt left_tail zero)
                (by
                  (simpa only zero_eq_nil)))
              (==
                (quote :false)
                (by
                  (exact nat_lt_zero_right_false left_tail)))
              (==
                (or
                  (nat-lt (cons left_head left_tail) nil)
                  (nat-eq (cons left_head left_tail) nil))
                (by
                  (eval)))))))
      right_head
      right_tail
      right_induction_hypothesis
      (by
        (intro right_is_nat)
        (specialize right_parts
          is_nat_value_cons_true_elim
          right_head
          right_tail)
        (cases right_parts right_head_unit right_tail_is_nat)
        (list-induction left
          (by
            (intro left_is_nat)
            (eval))
          left_head
          left_tail
          left_induction_hypothesis
          (by
            (intro left_is_nat)
            (specialize left_parts
              is_nat_value_cons_true_elim
              left_head
              left_tail)
            (cases left_parts left_head_unit left_tail_is_nat)
            (specialize tail_step
              right_induction_hypothesis
              left_tail)
            (calc
              (nat-lt
                (cons left_head left_tail)
                (succ (cons right_head right_tail)))
              (==
                (nat-lt left_tail (cons right_head right_tail))
                (by
                  (eval)))
              (==
                (nat-lt
                  left_tail
                  (cons (quote unit) right_tail))
                (by
                  (simpa only right_head_unit)))
              (==
                (nat-lt left_tail (succ right_tail))
                (by
                  (eval)))
              (==
                (or
                  (nat-lt left_tail right_tail)
                  (nat-eq left_tail right_tail))
                (by
                  (exact tail_step)))
              (==
                (or
                  (nat-lt
                    (cons left_head left_tail)
                    (cons right_head right_tail))
                  (nat-eq
                    (cons left_head left_tail)
                    (cons right_head right_tail)))
                (by
                  (eval)))))))))
  )

(theorem member_range_iff_lt
  (forall value (is-list value)
    (implies
      (computes-to (is-nat-value value) (quote :true))
      (forall upper (is-list upper)
        (implies
          (computes-to (is-nat-value upper) (quote :true))
          (computes-to
            (member value (range upper))
            (nat-lt value upper))))))
  (by
    (intro value)
    (intro value_is_nat)
    (list-induction upper
      (by
        (intro upper_is_nat)
        (calc
          (member value (range nil))
          (==
            (quote :false)
            (by
              (eval)))
          (==
            (nat-lt value nil)
            (by
              (fold zero)
              (exact (symm (nat_lt_zero_right_false value)))))))
      head
      tail
      induction_hypothesis
      (by
        (intro upper_is_nat)
        (specialize upper_parts is_nat_value_cons_true_elim head tail)
        (cases upper_parts head_unit tail_is_nat)
        (obtain tail_range tail_range_proof
          (range_computes_to_list tail))
        (specialize tail_member_range induction_hypothesis)
        (have tail_range_all_nat
          (computes-to
            (all
              (lambda candidate (is-nat-value candidate))
              tail_range)
            (quote :true))
          (by
            (calc
              (all
                (lambda candidate (is-nat-value candidate))
                tail_range)
              (==
                (all
                  (lambda candidate (is-nat-value candidate))
                  (range tail))
                (by
                  (simpa only (symm tail_range_proof))))
              (==
                (quote :true)
                (by
                  (exact range_all_nat_values tail)))))
          (by
            (have member_tail_snoc
              (computes-to
                (member value (snoc tail_range tail))
                (or
                  (member value tail_range)
                  (value-eq value tail)))
              (by
                (exact member_snoc_nat_list value tail_range tail))
              (by
                (have value_tail_eq_nat_eq
                  (computes-to
                    (value-eq value tail)
                    (nat-eq value tail))
                  (by
                    (exact value_eq_nat_eq value tail))
                  (by
                    (have value_lt_cons_tail
                      (computes-to
                        (nat-lt value (cons head tail))
                        (or
                          (nat-lt value tail)
                          (nat-eq value tail)))
                      (by
                        (calc
                          (nat-lt value (cons head tail))
                          (==
                            (nat-lt value (cons (quote unit) tail))
                            (by
                              (simpa only head_unit)))
                          (==
                            (nat-lt value (succ tail))
                            (by
                              (eval)))
                          (==
                            (or
                              (nat-lt value tail)
                              (nat-eq value tail))
                            (by
                              (exact
                                nat_lt_succ_right_or_eq
                                tail
                                value)))))
                      (by
                        (calc
                          (member value (range (cons head tail)))
                          (==
                            (member
                              value
                              (range (cons (quote unit) tail)))
                            (by
                              (simpa only head_unit)))
                          (==
                            (member
                              value
                              (snoc (range tail) tail))
                            (by
                              (simpa only (range_cons (quote unit) tail))))
                          (==
                            (member value (snoc tail_range tail))
                            (by
                              (simpa only tail_range_proof)))
                          (==
                            (or
                              (member value tail_range)
                              (value-eq value tail))
                            (by
                              (exact member_tail_snoc)))
                          (==
                            (or
                              (member value (range tail))
                              (value-eq value tail))
                            (by
                              (simpa only (symm tail_range_proof))))
                          (==
                            (or
                              (nat-lt value tail)
                              (value-eq value tail))
                            (by
                              (rewrite tail_member_range)
                              (eval)))
                          (==
                            (or
                              (nat-lt value tail)
                              (nat-eq value tail))
                            (by
                              (rewrite value_tail_eq_nat_eq)
                              (eval)))
                          (==
                            (nat-lt value (cons head tail))
                            (by
                              (exact
                                (symm value_lt_cons_tail)))))))))))))))))

(theorem nat_lt_irrefl
  (forall nat (is-list nat)
    (computes-to (nat-lt nat nat) (quote :false)))
  (by
    (list-induction nat
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (calc
          (nat-lt (cons head tail) (cons head tail))
          (==
            (nat-lt tail tail)
            (by
              (eval)))
          (==
            (quote :false)
            (by
              (exact induction_hypothesis))))))))

(theorem nat_lt_is_bool
  (forall left (is-list left)
    (forall right (is-list right)
      (is-bool (nat-lt left right))))
  (by
    (list-induction left
      (by
        (list-induction right
          (by
            (right
              (by
                (eval))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (left
              (by
                (eval))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (right
              (by
                (eval))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (or-elim
              (induction_hypothesis right_tail)
              tail_lt_true
              (by
                (left
                  (by
                    (calc
                      (nat-lt (cons left_head left_tail) (cons right_head right_tail))
                      (==
                        (nat-lt left_tail right_tail)
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact tail_lt_true)))))))
              tail_lt_false
              (by
                (right
                  (by
                    (calc
                      (nat-lt (cons left_head left_tail) (cons right_head right_tail))
                      (==
                        (nat-lt left_tail right_tail)
                        (by
                          (eval)))
                      (==
                        (quote :false)
                        (by
                          (exact tail_lt_false))))))))))))))

(theorem nat_lt_computes_to_bool
  (forall left (is-list left)
    (forall right (is-list right)
      (is-bool (nat-lt left right))))
  (by
    (intro left)
    (intro right)
    (exact nat_lt_is_bool left right)))

(theorem nat_le_list_suffix_cons
  (forall tail (is-list tail)
    (forall head (is-value head)
      (computes-to
        (nat-le tail (cons head tail))
        (quote :true))))
  (by
    (list-induction tail
      (by
        (intro head)
        (eval))
      tail_head
      tail_tail
      induction_hypothesis
      (by
        (intro head)
        (calc
          (nat-le (cons tail_head tail_tail) (cons head (cons tail_head tail_tail)))
          (==
            (nat-le tail_tail (cons tail_head tail_tail))
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact induction_hypothesis tail_head))))))))

(theorem nat_lt_list_suffix_cons
  (forall tail (is-list tail)
    (forall head (is-value head)
      (computes-to
        (nat-lt tail (cons head tail))
        (quote :true))))
  (by
    (list-induction tail
      (by
        (intro head)
        (eval))
      tail_head
      tail_tail
      induction_hypothesis
      (by
        (intro head)
        (calc
          (nat-lt (cons tail_head tail_tail) (cons head (cons tail_head tail_tail)))
          (==
            (nat-lt tail_tail (cons tail_head tail_tail))
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact induction_hypothesis tail_head))))))))

(theorem nat_le_self_succ
  (forall nat (is-list nat)
    (computes-to
      (nat-le nat (succ nat))
      (quote :true)))
  (by
    (intro nat)
    (calc
      (nat-le nat (succ nat))
      (==
        (nat-le nat (cons (quote unit) nat))
        (by
          (eval)))
      (==
        (quote :true)
        (by
          (exact nat_le_list_suffix_cons nat (quote unit)))))))

(theorem nat_lt_self_succ
  (forall nat (is-list nat)
    (computes-to
      (nat-lt nat (succ nat))
      (quote :true)))
  (by
    (intro nat)
    (calc
      (nat-lt nat (succ nat))
      (==
        (nat-lt nat (cons (quote unit) nat))
        (by
          (eval)))
      (==
        (quote :true)
        (by
          (exact nat_lt_list_suffix_cons nat (quote unit)))))))

(theorem nat_lt_succ_self
  (forall nat (is-list nat)
    (computes-to
      (nat-lt nat (succ nat))
      (quote :true)))
  (by
    (intro nat)
    (exact nat_lt_self_succ nat)))

(theorem nat_lt_implies_nat_le
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-lt left right) (quote :true))
        (computes-to (nat-le left right) (quote :true)))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro lt_true)
        (eval))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro lt_true)
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
                      (exact lt_true)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to
                      (nat-le (cons left_head left_tail) nil)
                      (quote :true)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro lt_true)
            (have tail_lt_true
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
                      (exact lt_true)))))
              (by
                (specialize tail_le_true induction_hypothesis right_tail)
                (calc
                  (nat-le (cons left_head left_tail) (cons right_head right_tail))
                  (==
                    (nat-le left_tail right_tail)
                    (by
                      (eval)))
                  (==
                      (quote :true)
                      (by
                        (exact tail_le_true))))))))))))

(theorem nat_lt_implies_le
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-lt left right) (quote :true))
        (computes-to (nat-le left right) (quote :true)))))
  (by
    (intro left)
    (intro right)
    (intro lt_true)
    (apply nat_lt_implies_nat_le left right)))

(theorem nat_le_false_implies_nat_lt_right_left
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-le left right) (quote :false))
        (computes-to (nat-lt right left) (quote :true)))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro le_false)
        (have impossible_eq
          (computes-to (quote :true) (quote :false))
          (by
            (calc
              (quote :true)
              (==
                (nat-le nil right)
                (by
                  (eval)))
              (==
                (quote :false)
                (by
                  (exact le_false)))))
          (by
            (exact
              (absurd-elim
                (distinct-outcomes impossible_eq)
                (computes-to (nat-lt right nil) (quote :true)))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro le_false)
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro le_false)
            (have tail_le_false
              (computes-to (nat-le left_tail right_tail) (quote :false))
              (by
                (calc
                  (nat-le left_tail right_tail)
                  (==
                    (nat-le (cons left_head left_tail) (cons right_head right_tail))
                    (by
                      (eval)))
                  (==
                    (quote :false)
                    (by
                      (exact le_false)))))
              (by
                (specialize tail_lt induction_hypothesis right_tail)
                (calc
                  (nat-lt (cons right_head right_tail) (cons left_head left_tail))
                  (==
                    (nat-lt right_tail left_tail)
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact tail_lt))))))))))))

(theorem nat_lt_false_implies_nat_le_right_left
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-lt left right) (quote :false))
        (computes-to (nat-le right left) (quote :true)))))
  (by
    (list-induction left
      (by
        (list-induction right
          (by
            (intro lt_false)
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro lt_false)
            (have impossible_eq
              (computes-to (quote :true) (quote :false))
              (by
                (calc
                  (quote :true)
                  (==
                    (nat-lt nil (cons right_head right_tail))
                    (by
                      (eval)))
                  (==
                    (quote :false)
                    (by
                      (exact lt_false)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to
                      (nat-le (cons right_head right_tail) nil)
                      (quote :true)))))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro lt_false)
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro lt_false)
            (have tail_lt_false
              (computes-to (nat-lt left_tail right_tail) (quote :false))
              (by
                (calc
                  (nat-lt left_tail right_tail)
                  (==
                    (nat-lt (cons left_head left_tail) (cons right_head right_tail))
                    (by
                      (eval)))
                  (==
                    (quote :false)
                    (by
                      (exact lt_false)))))
              (by
                (specialize tail_le induction_hypothesis right_tail)
                (calc
                  (nat-le (cons right_head right_tail) (cons left_head left_tail))
                  (==
                    (nat-le right_tail left_tail)
                    (by
                      (eval)))
                  (==
                  (quote :true)
                  (by
                    (exact tail_le))))))))))))

(theorem nat_le_total
  (forall left (is-list left)
    (forall right (is-list right)
      (or
        (computes-to (nat-le left right) (quote :true))
        (computes-to (nat-le right left) (quote :true)))))
  (by
    (intro left)
    (intro right)
    (or-elim
      (nat_le_is_bool left right)
      left_le_right
      (by
        (left
          (by
            (exact left_le_right))))
      left_not_le_right
      (by
        (have right_lt_left
          (computes-to (nat-lt right left) (quote :true))
          (by
            (exact nat_le_false_implies_nat_lt_right_left left right))
          (by
            (right
              (by
                (exact nat_lt_implies_nat_le right left)))))))))

(theorem nat_le_trans
  (forall left (is-list left)
    (forall middle (is-list middle)
      (forall right (is-list right)
        (implies
          (computes-to (nat-le left middle) (quote :true))
          (implies
            (computes-to (nat-le middle right) (quote :true))
            (computes-to (nat-le left right) (quote :true)))))))
  (by
    (list-induction left
      (by
        (intro middle)
        (intro right)
        (intro left_le_middle)
        (intro middle_le_right)
        (eval))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction middle
          (by
            (intro right)
            (intro left_le_middle)
            (intro middle_le_right)
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
                      (exact left_le_middle)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to
                      (nat-le (cons left_head left_tail) right)
                      (quote :true)))))))
          middle_head
          middle_tail
          middle_induction_hypothesis
          (by
            (list-induction right
              (by
                (intro left_le_middle)
                (intro middle_le_right)
                (have impossible_eq
                  (computes-to (quote :false) (quote :true))
                  (by
                    (calc
                      (quote :false)
                      (==
                        (nat-le (cons middle_head middle_tail) nil)
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact middle_le_right)))))
                  (by
                    (exact
                      (absurd-elim
                        (distinct-outcomes impossible_eq)
                        (computes-to
                          (nat-le (cons left_head left_tail) nil)
                          (quote :true)))))))
              right_head
              right_tail
              right_induction_hypothesis
              (by
                (intro left_le_middle)
                (intro middle_le_right)
                (have tail_left_le_middle
                  (computes-to (nat-le left_tail middle_tail) (quote :true))
                  (by
                    (calc
                      (nat-le left_tail middle_tail)
                      (==
                        (nat-le (cons left_head left_tail) (cons middle_head middle_tail))
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact left_le_middle)))))
                  (by
                    (have tail_middle_le_right
                      (computes-to (nat-le middle_tail right_tail) (quote :true))
                      (by
                        (calc
                          (nat-le middle_tail right_tail)
                          (==
                            (nat-le (cons middle_head middle_tail) (cons right_head right_tail))
                            (by
                              (eval)))
                          (==
                            (quote :true)
                            (by
                              (exact middle_le_right)))))
                      (by
                        (specialize tail_trans induction_hypothesis middle_tail right_tail)
                        (calc
                          (nat-le (cons left_head left_tail) (cons right_head right_tail))
                          (==
                            (nat-le left_tail right_tail)
                            (by
                              (eval)))
                          (==
                        (quote :true)
                        (by
                          (exact tail_trans))))))))))))))))

(theorem nat_le_succ_right
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-le left right) (quote :true))
        (computes-to
          (nat-le left (succ right))
          (quote :true)))))
  (by
    (intro left)
    (intro right)
    (intro left_le_right)
    (obtain right_succ right_succ_proof
      (succ_computes_to_list right))
    (have right_le_succ
      (computes-to (nat-le right right_succ) (quote :true))
      (by
        (calc
          (nat-le right right_succ)
          (==
            (nat-le right (succ right))
            (by
              (simpa only (symm right_succ_proof))))
          (==
            (quote :true)
            (by
              (exact nat_le_self_succ right)))))
      (by
        (specialize trans nat_le_trans left right right_succ)
        (calc
          (nat-le left (succ right))
          (==
            (nat-le left right_succ)
            (by
              (simpa only right_succ_proof)))
          (==
            (quote :true)
            (by
              (exact trans))))))))

(theorem length_filter_le
  (forall predicate (is-value predicate)
    (implies
      (forall value (is-value value)
        (is-bool (predicate value)))
      (forall list (is-list list)
        (computes-to
          (nat-le
            (length (filter predicate list))
            (length list))
          (quote :true)))))
  (by
    (intro predicate)
    (intro predicate_returns_bool)
    (list-induction list
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (obtain filtered_tail filtered_tail_proof
          (filter_computes_to_list predicate tail))
        (obtain filtered_tail_length filtered_tail_length_proof
          (length_computes_to_list filtered_tail))
        (obtain tail_length tail_length_proof
          (length_computes_to_list tail))
        (have tail_le
          (computes-to
            (nat-le filtered_tail_length tail_length)
            (quote :true))
          (by
            (calc
              (nat-le filtered_tail_length tail_length)
              (==
                (nat-le
                  (length filtered_tail)
                  tail_length)
                (by
                  (simpa only (symm filtered_tail_length_proof))))
              (==
                (nat-le
                  (length (filter predicate tail))
                  tail_length)
                (by
                  (simpa only (symm filtered_tail_proof))))
              (==
                (nat-le
                  (length (filter predicate tail))
                  (length tail))
                (by
                  (simpa only (symm tail_length_proof))))
              (==
                (quote :true)
                (by
                  (exact induction_hypothesis)))))
          (by
            (or-elim
              (predicate_returns_bool head)
              predicate_true
              (by
                (calc
                  (nat-le
                    (length (filter predicate (cons head tail)))
                    (length (cons head tail)))
                  (==
                    (nat-le
                      (length (cons head (filter predicate tail)))
                      (length (cons head tail)))
                    (by
                      (simpa only
                        (filter_cons_true
                          predicate
                          head
                          tail))))
                  (==
                    (nat-le
                      (length (cons head filtered_tail))
                      (length (cons head tail)))
                    (by
                      (simpa only filtered_tail_proof)))
                  (==
                    (nat-le
                      (cons (quote unit) (length filtered_tail))
                      (length (cons head tail)))
                    (by
                      (simpa only
                        (length_cons head filtered_tail))))
                  (==
                    (nat-le
                      (cons (quote unit) filtered_tail_length)
                      (length (cons head tail)))
                    (by
                      (simpa only filtered_tail_length_proof)))
                  (==
                    (nat-le
                      (cons (quote unit) filtered_tail_length)
                      (cons (quote unit) (length tail)))
                    (by
                      (simpa only (length_cons head tail))))
                  (==
                    (nat-le
                      (cons (quote unit) filtered_tail_length)
                      (cons (quote unit) tail_length))
                    (by
                      (simpa only tail_length_proof)))
                  (==
                    (nat-le filtered_tail_length tail_length)
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact tail_le)))))
              predicate_false
              (by
                (have tail_le_succ
                  (computes-to
                    (nat-le
                      filtered_tail_length
                      (cons (quote unit) tail_length))
                    (quote :true))
                  (by
                    (calc
                      (nat-le
                        filtered_tail_length
                        (cons (quote unit) tail_length))
                      (==
                        (nat-le
                          filtered_tail_length
                          (succ tail_length))
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (apply
                            nat_le_succ_right
                            filtered_tail_length
                            tail_length)))))
                  (by
                    (calc
                      (nat-le
                        (length (filter predicate (cons head tail)))
                        (length (cons head tail)))
                      (==
                        (nat-le
                          (length (filter predicate tail))
                          (length (cons head tail)))
                        (by
                          (simpa only
                            (filter_cons_false
                              predicate
                              head
                              tail))))
                      (==
                        (nat-le
                          (length filtered_tail)
                          (length (cons head tail)))
                        (by
                          (simpa only filtered_tail_proof)))
                      (==
                        (nat-le
                          filtered_tail_length
                          (length (cons head tail)))
                        (by
                          (simpa only filtered_tail_length_proof)))
                      (==
                        (nat-le
                          filtered_tail_length
                          (cons (quote unit) (length tail)))
                        (by
                          (simpa only (length_cons head tail))))
                      (==
                        (nat-le
                          filtered_tail_length
                          (cons (quote unit) tail_length))
                        (by
                          (simpa only tail_length_proof)))
                      (==
                        (quote :true)
                        (by
                          (exact tail_le_succ))))))))))))))

(theorem nat_lt_trans
  (forall left (is-list left)
    (forall middle (is-list middle)
      (forall right (is-list right)
        (implies
          (computes-to (nat-lt left middle) (quote :true))
          (implies
            (computes-to (nat-lt middle right) (quote :true))
            (computes-to (nat-lt left right) (quote :true)))))))
  (by
    (list-induction left
      (by
        (list-induction middle
          (by
            (intro right)
            (intro left_lt_middle)
            (intro middle_lt_right)
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
                      (exact left_lt_middle)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to (nat-lt nil right) (quote :true)))))))
          middle_head
          middle_tail
          middle_induction_hypothesis
          (by
            (list-induction right
              (by
                (intro left_lt_middle)
                (intro middle_lt_right)
                (have impossible_eq
                  (computes-to (quote :false) (quote :true))
                  (by
                    (calc
                      (quote :false)
                      (==
                        (nat-lt (cons middle_head middle_tail) nil)
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact middle_lt_right)))))
                  (by
                    (exact
                      (absurd-elim
                        (distinct-outcomes impossible_eq)
                        (computes-to (nat-lt nil nil) (quote :true)))))))
              right_head
              right_tail
              right_induction_hypothesis
              (by
                (intro left_lt_middle)
                (intro middle_lt_right)
                (eval))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction middle
          (by
            (intro right)
            (intro left_lt_middle)
            (intro middle_lt_right)
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
                      (exact left_lt_middle)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to
                      (nat-lt (cons left_head left_tail) right)
                      (quote :true)))))))
          middle_head
          middle_tail
          middle_induction_hypothesis
          (by
            (list-induction right
              (by
                (intro left_lt_middle)
                (intro middle_lt_right)
                (have impossible_eq
                  (computes-to (quote :false) (quote :true))
                  (by
                    (calc
                      (quote :false)
                      (==
                        (nat-lt (cons middle_head middle_tail) nil)
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact middle_lt_right)))))
                  (by
                    (exact
                      (absurd-elim
                        (distinct-outcomes impossible_eq)
                        (computes-to
                          (nat-lt (cons left_head left_tail) nil)
                          (quote :true)))))))
              right_head
              right_tail
              right_induction_hypothesis
              (by
                (intro left_lt_middle)
                (intro middle_lt_right)
                (have tail_left_lt_middle
                  (computes-to (nat-lt left_tail middle_tail) (quote :true))
                  (by
                    (calc
                      (nat-lt left_tail middle_tail)
                      (==
                        (nat-lt (cons left_head left_tail) (cons middle_head middle_tail))
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact left_lt_middle)))))
                  (by
                    (have tail_middle_lt_right
                      (computes-to (nat-lt middle_tail right_tail) (quote :true))
                      (by
                        (calc
                          (nat-lt middle_tail right_tail)
                          (==
                            (nat-lt (cons middle_head middle_tail) (cons right_head right_tail))
                            (by
                              (eval)))
                          (==
                            (quote :true)
                            (by
                              (exact middle_lt_right)))))
                      (by
                        (specialize tail_trans induction_hypothesis middle_tail right_tail)
                        (calc
                          (nat-lt (cons left_head left_tail) (cons right_head right_tail))
                          (==
                            (nat-lt left_tail right_tail)
                            (by
                              (eval)))
                          (==
                            (quote :true)
                        (by
                          (exact tail_trans))))))))))))))))

(theorem nat_le_lt_trans
  (forall left (is-list left)
    (forall middle (is-list middle)
      (forall right (is-list right)
        (implies
          (computes-to (nat-le left middle) (quote :true))
          (implies
            (computes-to (nat-lt middle right) (quote :true))
            (computes-to (nat-lt left right) (quote :true)))))))
  (by
    (list-induction left
      (by
        (list-induction middle
          (by
            (intro right)
            (intro left_le_middle)
            (intro middle_lt_right)
            (exact middle_lt_right))
          middle_head
          middle_tail
          middle_induction_hypothesis
          (by
            (list-induction right
              (by
                (intro left_le_middle)
                (intro middle_lt_right)
                (have impossible_eq
                  (computes-to (quote :false) (quote :true))
                  (by
                    (calc
                      (quote :false)
                      (==
                        (nat-lt (cons middle_head middle_tail) nil)
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact middle_lt_right)))))
                  (by
                    (exact
                      (absurd-elim
                        (distinct-outcomes impossible_eq)
                        (computes-to (nat-lt nil nil) (quote :true)))))))
              right_head
              right_tail
              right_induction_hypothesis
              (by
                (intro left_le_middle)
                (intro middle_lt_right)
                (eval))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction middle
          (by
            (intro right)
            (intro left_le_middle)
            (intro middle_lt_right)
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
                      (exact left_le_middle)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to
                      (nat-lt (cons left_head left_tail) right)
                      (quote :true)))))))
          middle_head
          middle_tail
          middle_induction_hypothesis
          (by
            (list-induction right
              (by
                (intro left_le_middle)
                (intro middle_lt_right)
                (have impossible_eq
                  (computes-to (quote :false) (quote :true))
                  (by
                    (calc
                      (quote :false)
                      (==
                        (nat-lt (cons middle_head middle_tail) nil)
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact middle_lt_right)))))
                  (by
                    (exact
                      (absurd-elim
                        (distinct-outcomes impossible_eq)
                        (computes-to
                          (nat-lt (cons left_head left_tail) nil)
                          (quote :true)))))))
              right_head
              right_tail
              right_induction_hypothesis
              (by
                (intro left_le_middle)
                (intro middle_lt_right)
                (have tail_left_le_middle
                  (computes-to (nat-le left_tail middle_tail) (quote :true))
                  (by
                    (calc
                      (nat-le left_tail middle_tail)
                      (==
                        (nat-le (cons left_head left_tail) (cons middle_head middle_tail))
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact left_le_middle)))))
                  (by
                    (have tail_middle_lt_right
                      (computes-to (nat-lt middle_tail right_tail) (quote :true))
                      (by
                        (calc
                          (nat-lt middle_tail right_tail)
                          (==
                            (nat-lt (cons middle_head middle_tail) (cons right_head right_tail))
                            (by
                              (eval)))
                          (==
                            (quote :true)
                            (by
                              (exact middle_lt_right)))))
                      (by
                        (specialize tail_trans induction_hypothesis middle_tail right_tail)
                        (calc
                          (nat-lt (cons left_head left_tail) (cons right_head right_tail))
                          (==
                            (nat-lt left_tail right_tail)
                            (by
                              (eval)))
                          (==
                            (quote :true)
                            (by
                              (exact tail_trans))))))))))))))))

(theorem nat_lt_le_trans
  (forall left (is-list left)
    (forall middle (is-list middle)
      (forall right (is-list right)
        (implies
          (computes-to (nat-lt left middle) (quote :true))
          (implies
            (computes-to (nat-le middle right) (quote :true))
            (computes-to (nat-lt left right) (quote :true)))))))
  (by
    (list-induction left
      (by
        (list-induction middle
          (by
            (intro right)
            (intro left_lt_middle)
            (intro middle_le_right)
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
                      (exact left_lt_middle)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to (nat-lt nil right) (quote :true)))))))
          middle_head
          middle_tail
          middle_induction_hypothesis
          (by
            (list-induction right
              (by
                (intro left_lt_middle)
                (intro middle_le_right)
                (have impossible_eq
                  (computes-to (quote :false) (quote :true))
                  (by
                    (calc
                      (quote :false)
                      (==
                        (nat-le (cons middle_head middle_tail) nil)
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact middle_le_right)))))
                  (by
                    (exact
                      (absurd-elim
                        (distinct-outcomes impossible_eq)
                        (computes-to (nat-lt nil nil) (quote :true)))))))
              right_head
              right_tail
              right_induction_hypothesis
              (by
                (intro left_lt_middle)
                (intro middle_le_right)
                (eval))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction middle
          (by
            (intro right)
            (intro left_lt_middle)
            (intro middle_le_right)
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
                      (exact left_lt_middle)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to
                      (nat-lt (cons left_head left_tail) right)
                      (quote :true)))))))
          middle_head
          middle_tail
          middle_induction_hypothesis
          (by
            (list-induction right
              (by
                (intro left_lt_middle)
                (intro middle_le_right)
                (have impossible_eq
                  (computes-to (quote :false) (quote :true))
                  (by
                    (calc
                      (quote :false)
                      (==
                        (nat-le (cons middle_head middle_tail) nil)
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact middle_le_right)))))
                  (by
                    (exact
                      (absurd-elim
                        (distinct-outcomes impossible_eq)
                        (computes-to
                          (nat-lt (cons left_head left_tail) nil)
                          (quote :true)))))))
              right_head
              right_tail
              right_induction_hypothesis
              (by
                (intro left_lt_middle)
                (intro middle_le_right)
                (have tail_left_lt_middle
                  (computes-to (nat-lt left_tail middle_tail) (quote :true))
                  (by
                    (calc
                      (nat-lt left_tail middle_tail)
                      (==
                        (nat-lt (cons left_head left_tail) (cons middle_head middle_tail))
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact left_lt_middle)))))
                  (by
                    (have tail_middle_le_right
                      (computes-to (nat-le middle_tail right_tail) (quote :true))
                      (by
                        (calc
                          (nat-le middle_tail right_tail)
                          (==
                            (nat-le (cons middle_head middle_tail) (cons right_head right_tail))
                            (by
                              (eval)))
                          (==
                            (quote :true)
                            (by
                              (exact middle_le_right)))))
                      (by
                        (specialize tail_trans induction_hypothesis middle_tail right_tail)
                        (calc
                          (nat-lt (cons left_head left_tail) (cons right_head right_tail))
                          (==
                            (nat-lt left_tail right_tail)
                            (by
                              (eval)))
                          (==
                            (quote :true)
                            (by
                              (exact tail_trans))))))))))))))))

(theorem nat_eq_symm
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (nat-eq left right)
        (nat-eq right left))))
  (by
    (list-induction left
      (by
        (list-induction right
          (by
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (eval))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (calc
              (nat-eq (cons left_head left_tail) (cons right_head right_tail))
              (==
                (nat-eq left_tail right_tail)
                (by
                  (eval)))
              (==
                (nat-eq right_tail left_tail)
                (by
                  (exact induction_hypothesis right_tail)))
              (==
                (nat-eq (cons right_head right_tail) (cons left_head left_tail))
                (by
                  (eval))))))))))

(theorem nat_eq_trans
  (forall left (is-list left)
    (forall middle (is-list middle)
      (forall right (is-list right)
        (implies
          (computes-to (nat-eq left middle) (quote :true))
          (implies
            (computes-to (nat-eq middle right) (quote :true))
            (computes-to (nat-eq left right) (quote :true)))))))
  (by
    (list-induction left
      (by
        (list-induction middle
          (by
            (intro right)
            (intro left_eq_middle)
            (intro middle_eq_right)
            (exact middle_eq_right))
          middle_head
          middle_tail
          middle_induction_hypothesis
          (by
            (intro right)
            (intro left_eq_middle)
            (intro middle_eq_right)
            (have impossible_eq
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (nat-eq nil (cons middle_head middle_tail))
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact left_eq_middle)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to (nat-eq nil right) (quote :true)))))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction middle
          (by
            (intro right)
            (intro left_eq_middle)
            (intro middle_eq_right)
            (have impossible_eq
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (nat-eq (cons left_head left_tail) nil)
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact left_eq_middle)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to
                      (nat-eq (cons left_head left_tail) right)
                      (quote :true)))))))
          middle_head
          middle_tail
          middle_induction_hypothesis
          (by
            (list-induction right
              (by
                (intro left_eq_middle)
                (intro middle_eq_right)
                (have impossible_eq
                  (computes-to (quote :false) (quote :true))
                  (by
                    (calc
                      (quote :false)
                      (==
                        (nat-eq (cons middle_head middle_tail) nil)
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact middle_eq_right)))))
                  (by
                    (exact
                      (absurd-elim
                        (distinct-outcomes impossible_eq)
                        (computes-to
                          (nat-eq (cons left_head left_tail) nil)
                          (quote :true)))))))
              right_head
              right_tail
              right_induction_hypothesis
              (by
                (intro left_eq_middle)
                (intro middle_eq_right)
                (have tail_left_eq_middle
                  (computes-to (nat-eq left_tail middle_tail) (quote :true))
                  (by
                    (calc
                      (nat-eq left_tail middle_tail)
                      (==
                        (nat-eq (cons left_head left_tail) (cons middle_head middle_tail))
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact left_eq_middle)))))
                  (by
                    (have tail_middle_eq_right
                      (computes-to (nat-eq middle_tail right_tail) (quote :true))
                      (by
                        (calc
                          (nat-eq middle_tail right_tail)
                          (==
                            (nat-eq (cons middle_head middle_tail) (cons right_head right_tail))
                            (by
                              (eval)))
                          (==
                            (quote :true)
                            (by
                              (exact middle_eq_right)))))
                      (by
                        (specialize tail_trans induction_hypothesis middle_tail right_tail)
                        (calc
                          (nat-eq (cons left_head left_tail) (cons right_head right_tail))
                          (==
                            (nat-eq left_tail right_tail)
                            (by
                              (eval)))
                          (==
                            (quote :true)
                        (by
                          (exact tail_trans))))))))))))))))

(theorem nat_eq_sound
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (implies
          (computes-to (is-nat-value right) (quote :true))
          (implies
            (computes-to (nat-eq left right) (quote :true))
            (computes-to left right))))))
  (by
    (list-induction left
      (by
        (list-induction right
          (by
            (intro left_is_nat)
            (intro right_is_nat)
            (intro eq_true)
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro left_is_nat)
            (intro right_is_nat)
            (intro eq_true)
            (have impossible_eq
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (nat-eq nil (cons right_head right_tail))
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact eq_true)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to nil (cons right_head right_tail)))))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro left_is_nat)
            (intro right_is_nat)
            (intro eq_true)
            (have impossible_eq
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (nat-eq (cons left_head left_tail) nil)
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact eq_true)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to (cons left_head left_tail) nil))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro left_is_nat)
            (intro right_is_nat)
            (intro eq_true)
            (specialize left_parts is_nat_value_cons_true_elim left_head left_tail)
            (cases left_parts left_head_unit left_tail_is_nat)
            (specialize right_parts is_nat_value_cons_true_elim right_head right_tail)
            (cases right_parts right_head_unit right_tail_is_nat)
            (have tail_eq_true
              (computes-to (nat-eq left_tail right_tail) (quote :true))
              (by
                (calc
                  (nat-eq left_tail right_tail)
                  (==
                    (nat-eq (cons left_head left_tail) (cons right_head right_tail))
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact eq_true)))))
              (by
                (specialize tails_equal induction_hypothesis right_tail)
                (have heads_equal
                  (computes-to left_head right_head)
                  (by
                    (calc
                      left_head
                      (==
                        (quote unit)
                        (by
                          (exact left_head_unit)))
                      (==
                        right_head
                        (by
                          (exact (symm right_head_unit))))))
	                  (by
	                    (specialize result cons_congr left_head left_tail right_head right_tail)
	                    (exact result)))))))))))

(theorem nat_eq_true_implies_equal
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (implies
          (computes-to (is-nat-value right) (quote :true))
          (implies
            (computes-to (nat-eq left right) (quote :true))
            (computes-to left right))))))
  (by
    (intro left)
    (intro right)
    (intro left_is_nat)
    (intro right_is_nat)
    (intro eq_true)
    (apply nat_eq_sound left right)))

(theorem nat_eq_false_implies_not_equal
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-eq left right) (quote :false))
        (implies
          (computes-to left right)
          (absurd)))))
  (by
    (intro left)
    (intro right)
    (intro eq_false)
    (intro values_equal)
    (have eq_true
      (computes-to (nat-eq left right) (quote :true))
      (by
        (calc
          (nat-eq left right)
          (==
            (nat-eq right right)
            (by
              (simpa only values_equal)))
          (==
            (quote :true)
            (by
              (exact nat_eq_refl right)))))
      (by
        (have impossible_eq
          (computes-to (quote :true) (quote :false))
          (by
            (calc
              (quote :true)
              (==
                (nat-eq left right)
                (by
                  (exact (symm eq_true))))
              (==
                (quote :false)
                (by
                  (exact eq_false)))))
          (by
            (exact (distinct-outcomes impossible_eq))))))))

(theorem nat_lt_implies_nat_eq_false
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-lt left right) (quote :true))
        (computes-to (nat-eq left right) (quote :false)))))
  (by
    (list-induction left
      (by
        (list-induction right
          (by
            (intro lt_true)
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
                      (exact lt_true)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to (nat-eq nil nil) (quote :false)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro lt_true)
            (eval))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro lt_true)
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
                      (exact lt_true)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to
                      (nat-eq (cons left_head left_tail) nil)
                      (quote :false)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro lt_true)
            (have tail_lt_true
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
                      (exact lt_true)))))
              (by
                (specialize tail_eq_false induction_hypothesis right_tail)
                (calc
                  (nat-eq (cons left_head left_tail) (cons right_head right_tail))
                  (==
                    (nat-eq left_tail right_tail)
                    (by
                      (eval)))
                  (==
                    (quote :false)
                    (by
                      (exact tail_eq_false))))))))))))

(theorem nat_lt_as_le_and_not_eq
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-lt left right) (quote :true))
        (and
          (computes-to (nat-le left right) (quote :true))
          (computes-to (nat-eq left right) (quote :false))))))
  (by
    (intro left)
    (intro right)
    (intro left_lt_right)
    (split
      (by
        (apply nat_lt_implies_nat_le left right))
      (by
        (apply nat_lt_implies_nat_eq_false left right)))))

(theorem nat_eq_false_implies_nat_lt_or_nat_lt
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-eq left right) (quote :false))
        (or
          (computes-to (nat-lt left right) (quote :true))
          (computes-to (nat-lt right left) (quote :true))))))
  (by
    (list-induction left
      (by
        (list-induction right
          (by
            (intro eq_false)
            (have impossible_eq
              (computes-to (quote :true) (quote :false))
              (by
                (calc
                  (quote :true)
                  (==
                    (nat-eq nil nil)
                    (by
                      (eval)))
                  (==
                    (quote :false)
                    (by
                      (exact eq_false)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (or
                      (computes-to (nat-lt nil nil) (quote :true))
                      (computes-to (nat-lt nil nil) (quote :true))))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro eq_false)
            (left
              (by
                (eval))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro eq_false)
            (right
              (by
                (eval))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro eq_false)
            (have tail_eq_false
              (computes-to (nat-eq left_tail right_tail) (quote :false))
              (by
                (calc
                  (nat-eq left_tail right_tail)
                  (==
                    (nat-eq (cons left_head left_tail) (cons right_head right_tail))
                    (by
                      (eval)))
                  (==
                    (quote :false)
                    (by
                      (exact eq_false)))))
              (by
                (specialize tail_result induction_hypothesis right_tail)
                (or-elim
                  tail_result
                  tail_left_lt_right
                  (by
                    (left
                      (by
                        (calc
                          (nat-lt (cons left_head left_tail) (cons right_head right_tail))
                          (==
                            (nat-lt left_tail right_tail)
                            (by
                              (eval)))
                          (==
                            (quote :true)
                            (by
                              (exact tail_left_lt_right)))))))
                  tail_right_lt_left
                  (by
                    (right
                      (by
                        (calc
                          (nat-lt (cons right_head right_tail) (cons left_head left_tail))
                          (==
                            (nat-lt right_tail left_tail)
                            (by
                              (eval)))
                          (==
                            (quote :true)
                            (by
                              (exact tail_right_lt_left))))))))))))))))

(theorem nat_eq_implies_nat_le_left_right
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-eq left right) (quote :true))
        (computes-to (nat-le left right) (quote :true)))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro eq_true)
        (eval))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro eq_true)
            (have impossible_eq
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (nat-eq (cons left_head left_tail) nil)
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact eq_true)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to
                      (nat-le (cons left_head left_tail) nil)
                      (quote :true)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro eq_true)
            (have tail_eq_true
              (computes-to (nat-eq left_tail right_tail) (quote :true))
              (by
                (calc
                  (nat-eq left_tail right_tail)
                  (==
                    (nat-eq (cons left_head left_tail) (cons right_head right_tail))
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact eq_true)))))
              (by
                (specialize tail_le_true induction_hypothesis right_tail)
                (calc
                  (nat-le (cons left_head left_tail) (cons right_head right_tail))
                  (==
                    (nat-le left_tail right_tail)
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact tail_le_true))))))))))))

(theorem nat_eq_implies_nat_le_right_left
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-eq left right) (quote :true))
        (computes-to (nat-le right left) (quote :true)))))
  (by
    (intro left)
    (intro right)
    (intro eq_true)
    (have reversed_eq_true
      (computes-to (nat-eq right left) (quote :true))
      (by
        (calc
          (nat-eq right left)
          (==
            (nat-eq left right)
            (by
              (exact (symm (nat_eq_symm left right)))))
          (==
            (quote :true)
            (by
              (exact eq_true)))))
      (by
        (specialize right_le_left nat_eq_implies_nat_le_left_right right left)
        (exact right_le_left)))))

(theorem nat_le_antisymm
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-le left right) (quote :true))
        (implies
          (computes-to (nat-le right left) (quote :true))
          (computes-to (nat-eq left right) (quote :true))))))
  (by
    (list-induction left
      (by
        (list-induction right
          (by
            (intro left_le_right)
            (intro right_le_left)
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro left_le_right)
            (intro right_le_left)
            (have impossible_eq
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (nat-le (cons right_head right_tail) nil)
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact right_le_left)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to
                      (nat-eq nil (cons right_head right_tail))
                      (quote :true)))))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro left_le_right)
            (intro right_le_left)
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
                      (nat-eq (cons left_head left_tail) nil)
                      (quote :true)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro left_le_right)
            (intro right_le_left)
            (have tail_left_le_right
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
                (have tail_right_le_left
                  (computes-to (nat-le right_tail left_tail) (quote :true))
                  (by
                    (calc
                      (nat-le right_tail left_tail)
                      (==
                        (nat-le (cons right_head right_tail) (cons left_head left_tail))
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact right_le_left)))))
                  (by
                    (specialize tail_eq_true induction_hypothesis right_tail)
                    (calc
                      (nat-eq (cons left_head left_tail) (cons right_head right_tail))
                      (==
                        (nat-eq left_tail right_tail)
                        (by
                          (eval)))
                      (==
                          (quote :true)
                        (by
                          (exact tail_eq_true))))))))))))))

(theorem nat_le_and_ne_implies_lt
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-le left right) (quote :true))
        (implies
          (computes-to (nat-eq left right) (quote :false))
          (computes-to (nat-lt left right) (quote :true))))))
  (by
    (intro left)
    (intro right)
    (intro left_le_right)
    (intro eq_false)
    (specialize lt_cases nat_eq_false_implies_nat_lt_or_nat_lt left right)
    (or-elim
      lt_cases
      left_lt_right
      (by
        (exact left_lt_right))
      right_lt_left
      (by
        (have right_le_left
          (computes-to (nat-le right left) (quote :true))
          (by
            (exact nat_lt_implies_nat_le right left))
          (by
            (have eq_true
              (computes-to (nat-eq left right) (quote :true))
              (by
                (exact nat_le_antisymm left right))
              (by
                (have impossible_eq
                  (computes-to (quote :true) (quote :false))
                  (by
                    (calc
                      (quote :true)
                      (==
                        (nat-eq left right)
                        (by
                          (exact (symm eq_true))))
                      (==
                        (quote :false)
                        (by
                          (exact eq_false)))))
                  (by
                    (exact
                      (absurd-elim
                        (distinct-outcomes impossible_eq)
                        (computes-to
                          (nat-lt left right)
                          (quote :true))))))))))))))

(theorem nat_le_implies_nat_lt_cons_right
  (forall left (is-list left)
    (forall right (is-list right)
      (forall head (is-value head)
        (implies
          (computes-to (nat-le left right) (quote :true))
          (computes-to
            (nat-lt left (cons head right))
            (quote :true))))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro head)
        (intro left_le_right)
        (eval))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro head)
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
                      (nat-lt (cons left_head left_tail) (cons head nil))
                      (quote :true)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro head)
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
                (specialize tail_lt_cons induction_hypothesis right_tail right_head)
                (calc
                  (nat-lt (cons left_head left_tail) (cons head (cons right_head right_tail)))
                  (==
                    (nat-lt left_tail (cons right_head right_tail))
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact tail_lt_cons))))))))))))
