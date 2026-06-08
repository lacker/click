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

(theorem succ_computes_to_list
  (forall nat (is-list nat)
    (computes-to-list result (succ nat)))
  (by
    (intro nat)
    (exists (cons (quote unit) nat)
      (by
        (eval)))))

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
        (eval)))))

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
        (eval)))))

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
        (eval)))))

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
        (eval)))))

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
