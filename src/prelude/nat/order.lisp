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
