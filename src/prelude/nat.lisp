; Nat definitions for the standard prelude.
; Natural numbers are unary lists of the prelude `unit` symbol.

(def zero nil)

(def succ
  (lambda nat
    (cons (quote unit) nat)))

(def is-nat-value
  (lambda value
    (if
      (is-list-value value)
      (list-case value
        (quote :true)
        cell
        (if
          (symbol-eq (head cell) (quote unit))
          (is-nat-value (tail cell))
          (quote :false)))
      (quote :false))))

(def is-zero
  (lambda nat
    (null nat)))

(def pred
  (lambda nat
    (list-case nat
      nil
      cell
      (tail cell))))

(def add
  (lambda left
    (lambda right
      (append left right))))

(def sub
  (lambda left
    (lambda right
      (list-case right
        left
        right_cell
        (list-case left
          nil
          left_cell
          (sub (tail left_cell) (tail right_cell)))))))

(def mul
  (lambda left
    (lambda right
      (list-case left
        nil
        cell
        (add right (mul (tail cell) right))))))

(def nat-eq
  (lambda left
    (lambda right
      (list-case left
        (is-zero right)
        left_cell
        (list-case right
          (quote :false)
          right_cell
          (nat-eq (tail left_cell) (tail right_cell)))))))

(def nat-le
  (lambda left
    (lambda right
      (list-case left
        (quote :true)
        left_cell
        (list-case right
          (quote :false)
          right_cell
          (nat-le (tail left_cell) (tail right_cell)))))))

(def nat-lt
  (lambda left
    (lambda right
      (list-case left
        (list-case right
          (quote :false)
          right_cell
          (quote :true))
        left_cell
        (list-case right
          (quote :false)
          right_cell
          (nat-lt (tail left_cell) (tail right_cell)))))))

(theorem add_is_append
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (add left right)
        (append left right))))
  (by
    (intro left)
    (intro right)
    (eval)))

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

(theorem add_zero_left
  (forall right (is-list right)
    (computes-to (add zero right) right))
  (by
    (intro right)
    (eval)))

(theorem add_computes_to_list
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to-list result (add left right))))
  (by
    (intro left)
    (intro right)
    (rewrite (add_is_append left right))
    (exact append_computes_to_list left right)))

(theorem add_cons
  (forall head (is-value head)
    (forall tail (is-list tail)
      (forall right (is-list right)
        (computes-to
          (add (cons head tail) right)
          (cons head (add tail right))))))
  (by
    (intro head)
    (intro tail)
    (intro right)
    (simp only append_cons)))

(theorem nat_le_left_add
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (nat-le left (add left right))
        (quote :true))))
  (by
    (list-induction left
      (by
        (intro right)
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (obtain tail_sum tail_sum_proof
          (add_computes_to_list tail right))
        (calc
          (nat-le (cons head tail) (add (cons head tail) right))
          (==
            (nat-le (cons head tail) (cons head (add tail right)))
            (by
              (simpa only (add_cons head tail right))))
          (==
            (nat-le (cons head tail) (cons head tail_sum))
            (by
              (simpa only tail_sum_proof)))
          (==
            (nat-le tail tail_sum)
            (by
              (eval)))
          (==
            (nat-le tail (add tail right))
            (by
              (simpa only (symm tail_sum_proof))))
          (==
            (quote :true)
            (by
              (exact induction_hypothesis right))))))))

(theorem nat_lt_left_add_succ_right
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (nat-lt left (add left (succ right)))
        (quote :true))))
  (by
    (list-induction left
      (by
        (intro right)
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (obtain right_succ right_succ_proof
          (succ_computes_to_list right))
        (obtain tail_sum tail_sum_proof
          (add_computes_to_list tail right_succ))
        (calc
          (nat-lt (cons head tail) (add (cons head tail) (succ right)))
          (==
            (nat-lt (cons head tail) (add (cons head tail) right_succ))
            (by
              (simpa only right_succ_proof)))
          (==
            (nat-lt (cons head tail) (cons head (add tail right_succ)))
            (by
              (simpa only (add_cons head tail right_succ))))
          (==
            (nat-lt (cons head tail) (cons head tail_sum))
            (by
              (simpa only tail_sum_proof)))
          (==
            (nat-lt tail tail_sum)
            (by
              (eval)))
          (==
            (nat-lt tail (add tail right_succ))
            (by
              (simpa only (symm tail_sum_proof))))
          (==
            (nat-lt tail (add tail (succ right)))
            (by
              (simpa only (symm right_succ_proof))))
          (==
            (quote :true)
            (by
              (exact induction_hypothesis right))))))))

(theorem nat_le_right_add
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (nat-le right (add left right))
        (quote :true))))
  (by
    (list-induction left
      (by
        (intro right)
        (calc
          (nat-le right (add nil right))
          (==
            (nat-le right right)
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact nat_le_refl right)))))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (obtain tail_sum tail_sum_proof
          (add_computes_to_list tail right))
        (have right_le_tail_sum
          (computes-to (nat-le right tail_sum) (quote :true))
          (by
            (calc
              (nat-le right tail_sum)
              (==
                (nat-le right (add tail right))
                (by
                  (simpa only (symm tail_sum_proof))))
              (==
                (quote :true)
                (by
                  (exact induction_hypothesis right)))))
          (by
            (have tail_sum_le_cons
              (computes-to
                (nat-le tail_sum (cons head tail_sum))
                (quote :true))
              (by
                (exact nat_le_list_suffix_cons tail_sum head))
              (by
                (specialize right_le_cons nat_le_trans right tail_sum (cons head tail_sum))
                (calc
                  (nat-le right (add (cons head tail) right))
                  (==
                    (nat-le right (cons head (add tail right)))
                    (by
                      (simpa only (add_cons head tail right))))
                  (==
                    (nat-le right (cons head tail_sum))
                    (by
                      (simpa only tail_sum_proof)))
                  (==
                    (quote :true)
                    (by
                      (exact right_le_cons))))))))))))

(theorem nat_lt_nil_left_add
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-lt nil left) (quote :true))
        (computes-to
          (nat-lt nil (add left right))
          (quote :true)))))
  (by
    (intro left)
    (intro right)
    (intro left_positive)
    (obtain sum sum_proof
      (add_computes_to_list left right))
    (have left_le_sum
      (computes-to (nat-le left sum) (quote :true))
      (by
        (calc
          (nat-le left sum)
          (==
            (nat-le left (add left right))
            (by
              (simpa only (symm sum_proof))))
          (==
            (quote :true)
            (by
              (exact nat_le_left_add left right)))))
      (by
        (specialize result nat_lt_le_trans nil left sum)
        (calc
          (nat-lt nil (add left right))
          (==
            (nat-lt nil sum)
            (by
              (simpa only sum_proof)))
          (==
            (quote :true)
            (by
              (exact result)))))))
)

(theorem nat_le_add_right_mono
  (forall left (is-list left)
    (forall right (is-list right)
      (forall suffix (is-list suffix)
        (implies
          (computes-to (nat-le left right) (quote :true))
          (computes-to
            (nat-le (add left suffix) (add right suffix))
            (quote :true))))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro suffix)
        (intro left_le_right)
        (calc
          (nat-le (add nil suffix) (add right suffix))
          (==
            (nat-le suffix (add right suffix))
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact nat_le_right_add right suffix)))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro suffix)
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
                      (nat-le (add (cons left_head left_tail) suffix) (add nil suffix))
                      (quote :true)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro suffix)
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
                (obtain left_sum left_sum_proof
                  (add_computes_to_list left_tail suffix))
                (obtain right_sum right_sum_proof
                  (add_computes_to_list right_tail suffix))
                (specialize tail_mono induction_hypothesis right_tail suffix)
                (calc
                  (nat-le (add (cons left_head left_tail) suffix) (add (cons right_head right_tail) suffix))
                  (==
                    (nat-le (cons left_head (add left_tail suffix)) (add (cons right_head right_tail) suffix))
                    (by
                      (simpa only (add_cons left_head left_tail suffix))))
                  (==
                    (nat-le (cons left_head left_sum) (add (cons right_head right_tail) suffix))
                    (by
                      (simpa only left_sum_proof)))
                  (==
                    (nat-le (cons left_head left_sum) (cons right_head (add right_tail suffix)))
                    (by
                      (simpa only (add_cons right_head right_tail suffix))))
                  (==
                    (nat-le (cons left_head left_sum) (cons right_head right_sum))
                    (by
                      (simpa only right_sum_proof)))
                  (==
                    (nat-le left_sum right_sum)
                    (by
                      (eval)))
                  (==
                    (nat-le (add left_tail suffix) right_sum)
                    (by
                      (simpa only (symm left_sum_proof))))
                  (==
                    (nat-le (add left_tail suffix) (add right_tail suffix))
                    (by
                      (simpa only (symm right_sum_proof))))
                  (==
                    (quote :true)
                    (by
                      (exact tail_mono))))))))))))

(theorem nat_lt_add_right_mono
  (forall left (is-list left)
    (forall right (is-list right)
      (forall suffix (is-list suffix)
        (implies
          (computes-to (nat-lt left right) (quote :true))
          (computes-to
            (nat-lt (add left suffix) (add right suffix))
            (quote :true))))))
  (by
    (list-induction left
      (by
        (list-induction right
          (by
            (intro suffix)
            (intro left_lt_right)
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
                      (nat-lt (add nil suffix) (add nil suffix))
                      (quote :true)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro suffix)
            (intro left_lt_right)
            (obtain right_sum right_sum_proof
              (add_computes_to_list right_tail suffix))
            (have suffix_le_right_sum
              (computes-to (nat-le suffix right_sum) (quote :true))
              (by
                (calc
                  (nat-le suffix right_sum)
                  (==
                    (nat-le suffix (add right_tail suffix))
                    (by
                      (simpa only (symm right_sum_proof))))
                  (==
                    (quote :true)
                    (by
                      (exact nat_le_right_add right_tail suffix)))))
              (by
                (specialize suffix_lt_cons nat_le_implies_nat_lt_cons_right suffix right_sum right_head)
                (calc
                  (nat-lt (add nil suffix) (add (cons right_head right_tail) suffix))
                  (==
                    (nat-lt suffix (add (cons right_head right_tail) suffix))
                    (by
                      (eval)))
                  (==
                    (nat-lt suffix (cons right_head (add right_tail suffix)))
                    (by
                      (simpa only (add_cons right_head right_tail suffix))))
                  (==
                    (nat-lt suffix (cons right_head right_sum))
                    (by
                      (simpa only right_sum_proof)))
                  (==
                    (quote :true)
                    (by
                      (exact suffix_lt_cons)))))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro suffix)
            (intro left_lt_right)
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
                      (nat-lt (add (cons left_head left_tail) suffix) (add nil suffix))
                      (quote :true)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro suffix)
            (intro left_lt_right)
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
                (obtain left_sum left_sum_proof
                  (add_computes_to_list left_tail suffix))
                (obtain right_sum right_sum_proof
                  (add_computes_to_list right_tail suffix))
                (specialize tail_mono induction_hypothesis right_tail suffix)
                (calc
                  (nat-lt (add (cons left_head left_tail) suffix) (add (cons right_head right_tail) suffix))
                  (==
                    (nat-lt (cons left_head (add left_tail suffix)) (add (cons right_head right_tail) suffix))
                    (by
                      (simpa only (add_cons left_head left_tail suffix))))
                  (==
                    (nat-lt (cons left_head left_sum) (add (cons right_head right_tail) suffix))
                    (by
                      (simpa only left_sum_proof)))
                  (==
                    (nat-lt (cons left_head left_sum) (cons right_head (add right_tail suffix)))
                    (by
                      (simpa only (add_cons right_head right_tail suffix))))
                  (==
                    (nat-lt (cons left_head left_sum) (cons right_head right_sum))
                    (by
                      (simpa only right_sum_proof)))
                  (==
                    (nat-lt left_sum right_sum)
                    (by
                      (eval)))
                  (==
                    (nat-lt (add left_tail suffix) right_sum)
                    (by
                      (simpa only (symm left_sum_proof))))
                  (==
                    (nat-lt (add left_tail suffix) (add right_tail suffix))
                    (by
                      (simpa only (symm right_sum_proof))))
                  (==
                    (quote :true)
                    (by
                      (exact tail_mono))))))))))))

(theorem nat_le_add_left_mono
  (forall left (is-list left)
    (forall right (is-list right)
      (forall prefix (is-list prefix)
        (implies
          (computes-to (nat-le left right) (quote :true))
          (computes-to
            (nat-le (add prefix left) (add prefix right))
            (quote :true))))))
  (by
    (intro left)
    (intro right)
    (list-induction prefix
      (by
        (intro left_le_right)
        (calc
          (nat-le (add nil left) (add nil right))
          (==
            (nat-le left right)
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact left_le_right)))))
      prefix_head
      prefix_tail
      induction_hypothesis
      (by
        (intro left_le_right)
        (obtain left_sum left_sum_proof
          (add_computes_to_list prefix_tail left))
        (obtain right_sum right_sum_proof
          (add_computes_to_list prefix_tail right))
        (specialize tail_mono induction_hypothesis)
        (calc
          (nat-le (add (cons prefix_head prefix_tail) left) (add (cons prefix_head prefix_tail) right))
          (==
            (nat-le (cons prefix_head (add prefix_tail left)) (add (cons prefix_head prefix_tail) right))
            (by
              (simpa only (add_cons prefix_head prefix_tail left))))
          (==
            (nat-le (cons prefix_head left_sum) (add (cons prefix_head prefix_tail) right))
            (by
              (simpa only left_sum_proof)))
          (==
            (nat-le (cons prefix_head left_sum) (cons prefix_head (add prefix_tail right)))
            (by
              (simpa only (add_cons prefix_head prefix_tail right))))
          (==
            (nat-le (cons prefix_head left_sum) (cons prefix_head right_sum))
            (by
              (simpa only right_sum_proof)))
          (==
            (nat-le left_sum right_sum)
            (by
              (eval)))
          (==
            (nat-le (add prefix_tail left) right_sum)
            (by
              (simpa only (symm left_sum_proof))))
          (==
            (nat-le (add prefix_tail left) (add prefix_tail right))
            (by
              (simpa only (symm right_sum_proof))))
          (==
            (quote :true)
            (by
              (exact tail_mono))))))))

(theorem nat_lt_add_left_mono
  (forall left (is-list left)
    (forall right (is-list right)
      (forall prefix (is-list prefix)
        (implies
          (computes-to (nat-lt left right) (quote :true))
          (computes-to
            (nat-lt (add prefix left) (add prefix right))
            (quote :true))))))
  (by
    (intro left)
    (intro right)
    (list-induction prefix
      (by
        (intro left_lt_right)
        (calc
          (nat-lt (add nil left) (add nil right))
          (==
            (nat-lt left right)
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact left_lt_right)))))
      prefix_head
      prefix_tail
      induction_hypothesis
      (by
        (intro left_lt_right)
        (obtain left_sum left_sum_proof
          (add_computes_to_list prefix_tail left))
        (obtain right_sum right_sum_proof
          (add_computes_to_list prefix_tail right))
        (specialize tail_mono induction_hypothesis)
        (calc
          (nat-lt (add (cons prefix_head prefix_tail) left) (add (cons prefix_head prefix_tail) right))
          (==
            (nat-lt (cons prefix_head (add prefix_tail left)) (add (cons prefix_head prefix_tail) right))
            (by
              (simpa only (add_cons prefix_head prefix_tail left))))
          (==
            (nat-lt (cons prefix_head left_sum) (add (cons prefix_head prefix_tail) right))
            (by
              (simpa only left_sum_proof)))
          (==
            (nat-lt (cons prefix_head left_sum) (cons prefix_head (add prefix_tail right)))
            (by
              (simpa only (add_cons prefix_head prefix_tail right))))
          (==
            (nat-lt (cons prefix_head left_sum) (cons prefix_head right_sum))
            (by
              (simpa only right_sum_proof)))
          (==
            (nat-lt left_sum right_sum)
            (by
              (eval)))
          (==
            (nat-lt (add prefix_tail left) right_sum)
            (by
              (simpa only (symm left_sum_proof))))
          (==
            (nat-lt (add prefix_tail left) (add prefix_tail right))
            (by
              (simpa only (symm right_sum_proof))))
          (==
            (quote :true)
            (by
              (exact tail_mono))))))))

(theorem nat_le_add_left_cancel
  (forall left (is-list left)
    (forall right (is-list right)
      (forall prefix (is-list prefix)
        (implies
          (computes-to
            (nat-le (add prefix left) (add prefix right))
            (quote :true))
          (computes-to (nat-le left right) (quote :true))))))
  (by
    (intro left)
    (intro right)
    (list-induction prefix
      (by
        (intro prefixed_le)
        (calc
          (nat-le left right)
          (==
            (nat-le (add nil left) (add nil right))
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact prefixed_le)))))
      prefix_head
      prefix_tail
      induction_hypothesis
      (by
        (intro prefixed_le)
        (obtain left_sum left_sum_proof
          (add_computes_to_list prefix_tail left))
        (obtain right_sum right_sum_proof
          (add_computes_to_list prefix_tail right))
        (have tail_prefixed_le
          (computes-to
            (nat-le (add prefix_tail left) (add prefix_tail right))
            (quote :true))
          (by
            (calc
              (nat-le (add prefix_tail left) (add prefix_tail right))
              (==
                (nat-le left_sum (add prefix_tail right))
                (by
                  (simpa only left_sum_proof)))
              (==
                (nat-le left_sum right_sum)
                (by
                  (simpa only right_sum_proof)))
              (==
                (nat-le
                  (cons prefix_head left_sum)
                  (cons prefix_head right_sum))
                (by
                  (eval)))
              (==
                (nat-le
                  (cons prefix_head (add prefix_tail left))
                  (cons prefix_head right_sum))
                (by
                  (simpa only (symm left_sum_proof))))
              (==
                (nat-le
                  (cons prefix_head (add prefix_tail left))
                  (cons prefix_head (add prefix_tail right)))
                (by
                  (simpa only (symm right_sum_proof))))
              (==
                (nat-le
                  (add (cons prefix_head prefix_tail) left)
                  (cons prefix_head (add prefix_tail right)))
                (by
                  (simpa only (symm (add_cons prefix_head prefix_tail left)))))
              (==
                (nat-le
                  (add (cons prefix_head prefix_tail) left)
                  (add (cons prefix_head prefix_tail) right))
                (by
                  (simpa only (symm (add_cons prefix_head prefix_tail right)))))
              (==
                (quote :true)
                (by
                  (exact prefixed_le)))))
          (by
            (specialize tail_cancel induction_hypothesis)
            (exact tail_cancel)))))))

(theorem nat_lt_add_left_cancel
  (forall left (is-list left)
    (forall right (is-list right)
      (forall prefix (is-list prefix)
        (implies
          (computes-to
            (nat-lt (add prefix left) (add prefix right))
            (quote :true))
          (computes-to (nat-lt left right) (quote :true))))))
  (by
    (intro left)
    (intro right)
    (list-induction prefix
      (by
        (intro prefixed_lt)
        (calc
          (nat-lt left right)
          (==
            (nat-lt (add nil left) (add nil right))
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact prefixed_lt)))))
      prefix_head
      prefix_tail
      induction_hypothesis
      (by
        (intro prefixed_lt)
        (obtain left_sum left_sum_proof
          (add_computes_to_list prefix_tail left))
        (obtain right_sum right_sum_proof
          (add_computes_to_list prefix_tail right))
        (have tail_prefixed_lt
          (computes-to
            (nat-lt (add prefix_tail left) (add prefix_tail right))
            (quote :true))
          (by
            (calc
              (nat-lt (add prefix_tail left) (add prefix_tail right))
              (==
                (nat-lt left_sum (add prefix_tail right))
                (by
                  (simpa only left_sum_proof)))
              (==
                (nat-lt left_sum right_sum)
                (by
                  (simpa only right_sum_proof)))
              (==
                (nat-lt
                  (cons prefix_head left_sum)
                  (cons prefix_head right_sum))
                (by
                  (eval)))
              (==
                (nat-lt
                  (cons prefix_head (add prefix_tail left))
                  (cons prefix_head right_sum))
                (by
                  (simpa only (symm left_sum_proof))))
              (==
                (nat-lt
                  (cons prefix_head (add prefix_tail left))
                  (cons prefix_head (add prefix_tail right)))
                (by
                  (simpa only (symm right_sum_proof))))
              (==
                (nat-lt
                  (add (cons prefix_head prefix_tail) left)
                  (cons prefix_head (add prefix_tail right)))
                (by
                  (simpa only (symm (add_cons prefix_head prefix_tail left)))))
              (==
                (nat-lt
                  (add (cons prefix_head prefix_tail) left)
                  (add (cons prefix_head prefix_tail) right))
                (by
                  (simpa only (symm (add_cons prefix_head prefix_tail right)))))
              (==
                (quote :true)
                (by
                  (exact prefixed_lt)))))
          (by
            (specialize tail_cancel induction_hypothesis)
            (exact tail_cancel)))))))

(theorem add_succ_left
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (add (succ left) right)
        (succ (add left right)))))
  (by
    (intro left)
    (intro right)
    (obtain sum sum_proof
      (add_computes_to_list left right))
    (calc
      (add (succ left) right)
      (==
        (add (cons (quote unit) left) right)
        (by
          (eval)))
      (==
        (cons (quote unit) (add left right))
        (by
          (exact add_cons (quote unit) left right)))
      (==
        (cons (quote unit) sum)
        (by
          (simpa only sum_proof)))
      (==
        (succ sum)
        (by
          (eval)))
      (==
        (succ (add left right))
        (by
          (simpa only (symm sum_proof)))))))

(theorem pred_add_succ_left
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (pred (add (succ left) right))
        (add left right))))
  (by
    (intro left)
    (intro right)
    (obtain sum sum_proof
      (add_computes_to_list left right))
    (calc
      (pred (add (succ left) right))
      (==
        (pred (succ (add left right)))
        (by
          (simpa only (add_succ_left left right))))
      (==
        (pred (succ sum))
        (by
          (simpa only sum_proof)))
      (==
        sum
        (by
          (exact pred_succ sum)))
      (==
        (add left right)
        (by
          (simpa only (symm sum_proof)))))))

(theorem is_zero_add_succ_left
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (is-zero (add (succ left) right))
        (quote :false))))
  (by
    (intro left)
    (intro right)
    (obtain sum sum_proof
      (add_computes_to_list left right))
    (calc
      (is-zero (add (succ left) right))
      (==
        (is-zero (succ sum))
        (by
          (simpa only (add_succ_left left right) sum_proof)))
      (==
        (quote :false)
        (by
          (eval))))))

(theorem add_cons_unit_right
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (computes-to
          (add left (cons (quote unit) right))
          (succ (add left right))))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro left_is_nat)
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (intro cons_is_nat)
        (specialize cons_parts is_nat_value_cons_true_elim head tail)
        (cases cons_parts head_unit tail_is_nat)
        (specialize tail_succ induction_hypothesis right)
        (obtain tail_sum tail_sum_proof
          (add_computes_to_list tail right))
        (calc
          (add (cons head tail) (cons (quote unit) right))
          (==
            (cons head (add tail (cons (quote unit) right)))
            (by
              (exact add_cons head tail (cons (quote unit) right))))
          (==
            (cons head (succ (add tail right)))
            (by
              (simpa only tail_succ)))
          (==
            (cons head (succ tail_sum))
            (by
              (simpa only tail_sum_proof)))
          (==
            (cons head (cons (quote unit) tail_sum))
            (by
              (eval)))
          (==
            (cons (quote unit) (cons (quote unit) tail_sum))
            (by
              (simpa only head_unit)))
          (==
            (succ (cons (quote unit) tail_sum))
            (by
              (eval)))
          (==
            (succ (cons head tail_sum))
            (by
              (simpa only (symm head_unit))))
          (==
            (succ (cons head (add tail right)))
            (by
              (simpa only (symm tail_sum_proof))))
          (==
            (succ (add (cons head tail) right))
            (by
              (rewrite (symm (add_cons head tail right)))
              (eval))))))))

(theorem add_succ_right
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (computes-to
          (add left (succ right))
          (succ (add left right))))))
  (by
    (intro left)
    (intro right)
    (intro left_is_nat)
    (specialize add_cons_unit_right_step add_cons_unit_right left right)
    (calc
      (add left (succ right))
      (==
        (add left (cons (quote unit) right))
        (by
          (eval)))
      (==
        (succ (add left right))
        (by
          (exact add_cons_unit_right_step))))))

(theorem pred_add_succ_right
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (computes-to
          (pred (add left (succ right)))
          (add left right)))))
  (by
    (intro left)
    (intro right)
    (intro left_is_nat)
    (obtain sum sum_proof
      (add_computes_to_list left right))
    (specialize left_succ add_succ_right left right)
    (calc
      (pred (add left (succ right)))
      (==
        (pred (succ (add left right)))
        (by
          (simpa only left_succ)))
      (==
        (pred (succ sum))
        (by
          (simpa only sum_proof)))
      (==
        sum
        (by
          (exact pred_succ sum)))
      (==
        (add left right)
        (by
          (simpa only (symm sum_proof)))))))

(theorem is_zero_add_succ_right
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (computes-to
          (is-zero (add left (succ right)))
          (quote :false)))))
  (by
    (intro left)
    (intro right)
    (intro left_is_nat)
    (obtain sum sum_proof
      (add_computes_to_list left right))
    (specialize left_succ add_succ_right left right)
    (calc
      (is-zero (add left (succ right)))
      (==
        (is-zero (succ (add left right)))
        (by
          (simpa only left_succ)))
      (==
        (is-zero (succ sum))
        (by
          (simpa only sum_proof)))
      (==
        (quote :false)
        (by
          (eval))))))

(theorem add_zero_right
  (forall nat (is-list nat)
    (computes-to (add nat zero) nat))
  (by
    (intro nat)
    (calc
      (add nat zero)
      (==
        (append nat nil)
        (by
          (eval)))
      (==
        nat
        (by
          (exact append_right_nil nat))))))

(theorem add_nat_suffix_preserves_nat_value
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value right) (quote :true))
        (computes-to
          (is-nat-value (add left right))
          (is-nat-value left)))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro right_is_nat)
        (calc
          (is-nat-value (add nil right))
          (==
            (is-nat-value right)
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact right_is_nat)))
          (==
            (is-nat-value nil)
            (by
              (eval)))))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (intro right_is_nat)
        (obtain tail_sum tail_sum_proof
          (add_computes_to_list tail right))
        (specialize tail_suffix_preserves_nat induction_hypothesis right)
        (calc
          (is-nat-value (add (cons head tail) right))
          (==
            (is-nat-value (cons head (add tail right)))
            (by
              (simpa only (add_cons head tail right))))
          (==
            (is-nat-value (cons head tail_sum))
            (by
              (simpa only tail_sum_proof)))
          (==
            (if
              (symbol-eq head (quote unit))
              (is-nat-value tail_sum)
              (quote :false))
            (by
              (exact is_nat_value_cons head tail_sum)))
          (==
            (if
              (symbol-eq head (quote unit))
              (is-nat-value (add tail right))
              (quote :false))
            (by
              (simpa only (symm tail_sum_proof))))
          (==
            (if
              (symbol-eq head (quote unit))
              (is-nat-value tail)
              (quote :false))
            (by
              (simpa only tail_suffix_preserves_nat)))
          (==
            (is-nat-value (cons head tail))
            (by
              (exact (symm (is_nat_value_cons head tail))))))))))

(theorem add_preserves_nat_value
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (implies
          (computes-to (is-nat-value right) (quote :true))
          (computes-to
            (is-nat-value (add left right))
            (quote :true))))))
  (by
    (intro left)
    (intro right)
    (intro left_is_nat)
    (intro right_is_nat)
    (specialize suffix_preserves add_nat_suffix_preserves_nat_value left right)
    (calc
      (is-nat-value (add left right))
      (==
        (is-nat-value left)
        (by
          (exact suffix_preserves)))
      (==
        (quote :true)
        (by
          (exact left_is_nat))))))

(theorem add_assoc
  (forall left (is-list left)
    (forall middle (is-list middle)
      (forall right (is-list right)
        (computes-to
          (add (add left middle) right)
          (add left (add middle right))))))
  (by
    (intro left)
    (intro middle)
    (intro right)
    (obtain left_middle left_middle_proof
      (add_computes_to_list left middle))
    (obtain middle_right middle_right_proof
      (add_computes_to_list middle right))
    (calc
      (add (add left middle) right)
      (==
        (add left_middle right)
        (by
          (simpa only left_middle_proof)))
      (==
        (append left_middle right)
        (by
          (exact add_is_append left_middle right)))
      (==
        (append (add left middle) right)
        (by
          (simpa only (symm left_middle_proof))))
      (==
        (append (append left middle) right)
        (by
          (simpa only (add_is_append left middle))))
      (==
        (append left (append middle right))
        (by
          (exact append_assoc left middle right)))
      (==
        (append left (add middle right))
        (by
          (rewrite (symm (add_is_append middle right)))
          (eval)))
      (==
        (append left middle_right)
        (by
          (simpa only middle_right_proof)))
      (==
        (add left middle_right)
        (by
          (exact (symm (add_is_append left middle_right)))))
      (==
        (add left (add middle right))
        (by
          (simpa only (symm middle_right_proof)))))))

(theorem add_comm
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (implies
          (computes-to (is-nat-value right) (quote :true))
          (computes-to
            (add left right)
            (add right left))))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro left_is_nat)
        (intro right_is_nat)
        (calc
          (add nil right)
          (==
            right
            (by
              (eval)))
          (==
            (add right zero)
            (by
              (exact (symm (add_zero_right right)))))
          (==
            (add right nil)
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
        (specialize tail_comm induction_hypothesis right)
        (specialize right_succ_tail add_succ_right right tail)
        (obtain right_tail right_tail_proof
          (add_computes_to_list right tail))
        (calc
          (add (cons head tail) right)
          (==
            (cons head (add tail right))
            (by
              (exact add_cons head tail right)))
          (==
            (cons head (add right tail))
            (by
              (simpa only tail_comm)))
          (==
            (cons head right_tail)
            (by
              (simpa only right_tail_proof)))
          (==
            (cons (quote unit) right_tail)
            (by
              (simpa only head_unit)))
          (==
            (succ right_tail)
            (by
              (eval)))
          (==
            (succ (add right tail))
            (by
              (simpa only (symm right_tail_proof))))
          (==
            (add right (succ tail))
            (by
              (exact (symm right_succ_tail))))
          (==
            (add right (cons (quote unit) tail))
            (by
              (eval)))
          (==
            (add right (cons head tail))
            (by
              (simpa only (symm head_unit)))))))))

(theorem add_swap
  (forall left (is-list left)
    (forall right (is-list right)
      (forall rest (is-list rest)
        (implies
          (computes-to (is-nat-value left) (quote :true))
          (implies
            (computes-to (is-nat-value right) (quote :true))
            (computes-to
              (add left (add right rest))
              (add right (add left rest))))))))
  (by
    (intro left)
    (intro right)
    (intro rest)
    (intro left_is_nat)
    (intro right_is_nat)
    (specialize left_right_comm add_comm left right)
    (calc
      (add left (add right rest))
      (==
        (add (add left right) rest)
        (by
          (exact (symm (add_assoc left right rest)))))
      (==
        (add (add right left) rest)
        (by
          (simpa only left_right_comm)))
      (==
        (add right (add left rest))
        (by
          (exact add_assoc right left rest))))))

(theorem sub_zero_right
  (forall left (is-list left)
    (computes-to (sub left zero) left))
  (by
    (intro left)
    (eval)))

(theorem sub_zero_left
  (forall right (is-list right)
    (computes-to (sub zero right) zero))
  (by
    (list-induction right
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (eval)))))

(theorem sub_succ_succ
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (sub (succ left) (succ right))
        (sub left right))))
  (by
    (intro left)
    (intro right)
    (eval)))

(theorem sub_computes_to_list
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to-list result (sub left right))))
  (by
    (list-induction left
      (by
        (list-induction right
          (by
            (exists nil
              (by
                (eval))))
          zero_right_head
          zero_right_tail
          zero_right_induction_hypothesis
          (by
            (exists nil
              (by
                (eval))))))
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
            (obtain difference difference_proof
              (induction_hypothesis right_tail))
            (exists difference
              (by
                (calc
                  (sub (cons left_head left_tail) (cons right_head right_tail))
                  (==
                    (sub left_tail right_tail)
                    (by
                      (eval)))
                  (==
                    difference
                    (by
                      (exact difference_proof)))))))))))
)

(theorem add_sub_cancel_left
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (sub (add left right) left)
        right)))
  (by
    (list-induction left
      (by
        (intro right)
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (obtain sum sum_proof
          (add_computes_to_list tail right))
        (calc
          (sub (add (cons head tail) right) (cons head tail))
          (==
            (sub (cons head (add tail right)) (cons head tail))
            (by
              (simpa only (add_cons head tail right))))
          (==
            (sub (cons head sum) (cons head tail))
            (by
              (simpa only sum_proof)))
          (==
            (sub sum tail)
            (by
              (eval)))
          (==
            (sub (add tail right) tail)
            (by
              (simpa only (symm sum_proof))))
          (==
            right
            (by
              (exact induction_hypothesis right))))))))

(theorem add_sub_cancel_right
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (implies
          (computes-to (is-nat-value right) (quote :true))
          (computes-to
            (sub (add left right) right)
            left)))))
  (by
    (intro left)
    (intro right)
    (intro left_is_nat)
    (intro right_is_nat)
    (obtain sum sum_proof
      (add_computes_to_list left right))
    (specialize left_right_comm add_comm left right)
    (calc
      (sub (add left right) right)
      (==
        (sub sum right)
        (by
          (simpa only sum_proof)))
      (==
        (sub (add left right) right)
        (by
          (simpa only (symm sum_proof))))
      (==
        (sub (add right left) right)
        (by
          (simpa only left_right_comm)))
      (==
        left
        (by
          (exact add_sub_cancel_left right left))))))

(theorem sub_self
  (forall nat (is-list nat)
    (computes-to (sub nat nat) zero))
  (by
    (list-induction nat
      (by
        (eval))
      head
      tail
      induction_hypothesis
      (by
        (calc
          (sub (cons head tail) (cons head tail))
          (==
            (sub tail tail)
            (by
              (eval)))
          (==
            zero
            (by
              (exact induction_hypothesis)))))))
)

(theorem nat_le_sub_left
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (nat-le (sub left right) left)
        (quote :true))))
  (by
    (list-induction left
      (by
        (list-induction right
          (by
            (eval))
          zero_right_head
          zero_right_tail
          zero_right_induction_hypothesis
          (by
            (eval))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (calc
              (nat-le (sub (cons left_head left_tail) nil) (cons left_head left_tail))
              (==
                (nat-le (cons left_head left_tail) (cons left_head left_tail))
                (by
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact nat_le_refl (cons left_head left_tail))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (obtain difference difference_proof
              (sub_computes_to_list left_tail right_tail))
            (have difference_le_tail
              (computes-to
                (nat-le difference left_tail)
                (quote :true))
              (by
                (calc
                  (nat-le difference left_tail)
                  (==
                    (nat-le (sub left_tail right_tail) left_tail)
                    (by
                      (simpa only (symm difference_proof))))
                  (==
                    (quote :true)
                    (by
                      (exact induction_hypothesis right_tail)))))
              (by
                (have tail_le_cons
                  (computes-to
                    (nat-le left_tail (cons left_head left_tail))
                    (quote :true))
                  (by
                    (exact nat_le_list_suffix_cons left_tail left_head))
                  (by
                    (specialize difference_le_cons
                      nat_le_trans
                      difference
                      left_tail
                      (cons left_head left_tail))
                    (calc
                      (nat-le
                        (sub (cons left_head left_tail) (cons right_head right_tail))
                        (cons left_head left_tail))
                      (==
                        (nat-le (sub left_tail right_tail) (cons left_head left_tail))
                        (by
                          (eval)))
                      (==
                        (nat-le difference (cons left_head left_tail))
                        (by
                          (simpa only difference_proof)))
                      (==
                        (quote :true)
                        (by
                          (exact difference_le_cons))))))))))))
))

(theorem nat_le_implies_sub_zero
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-le left right) (quote :true))
        (computes-to (sub left right) zero))))
  (by
    (list-induction left
      (by
        (list-induction right
          (by
            (intro left_le_right)
            (eval))
          zero_right_head
          zero_right_tail
          zero_right_induction_hypothesis
          (by
            (intro left_le_right)
            (eval))))
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
                    (computes-to (sub (cons left_head left_tail) nil) zero))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
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
                (specialize tail_sub_zero induction_hypothesis right_tail)
                (calc
                  (sub (cons left_head left_tail) (cons right_head right_tail))
                  (==
                    (sub left_tail right_tail)
                    (by
                      (eval)))
                  (==
                    zero
                    (by
                      (exact tail_sub_zero)))))))))))
)

(theorem nat_le_add_sub_cancel
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (implies
          (computes-to (is-nat-value right) (quote :true))
          (implies
            (computes-to (nat-le right left) (quote :true))
            (computes-to
              (add right (sub left right))
              left))))))
  (by
    (list-induction left
      (by
        (list-induction right
          (by
            (intro left_is_nat)
            (intro right_is_nat)
            (intro right_le_left)
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro left_is_nat)
            (intro right_is_nat)
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
                      (add
                        (cons right_head right_tail)
                        (sub nil (cons right_head right_tail)))
                      nil))))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro left_is_nat)
            (intro right_is_nat)
            (intro right_le_left)
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro left_is_nat)
            (intro right_is_nat)
            (intro right_le_left)
            (specialize left_parts
              is_nat_value_cons_true_elim
              left_head
              left_tail)
            (cases left_parts left_head_unit left_tail_is_nat)
            (specialize right_parts
              is_nat_value_cons_true_elim
              right_head
              right_tail)
            (cases right_parts right_head_unit right_tail_is_nat)
            (have tail_le_left
              (computes-to (nat-le right_tail left_tail) (quote :true))
              (by
                (calc
                  (nat-le right_tail left_tail)
                  (==
                    (nat-le
                      (cons right_head right_tail)
                      (cons left_head left_tail))
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact right_le_left)))))
              (by
                (specialize tail_cancel induction_hypothesis right_tail)
                (obtain difference difference_proof
                  (sub_computes_to_list left_tail right_tail))
                (calc
                  (add
                    (cons right_head right_tail)
                    (sub
                      (cons left_head left_tail)
                      (cons right_head right_tail)))
                  (==
                    (add
                      (cons right_head right_tail)
                      (sub left_tail right_tail))
                    (by
                      (eval)))
                  (==
                    (add (cons right_head right_tail) difference)
                    (by
                      (simpa only difference_proof)))
                  (==
                    (cons right_head (add right_tail difference))
                    (by
                      (exact add_cons right_head right_tail difference)))
                  (==
                    (cons
                      right_head
                      (add right_tail (sub left_tail right_tail)))
                    (by
                      (simpa only (symm difference_proof))))
                  (==
                    (cons right_head left_tail)
                    (by
                      (simpa only tail_cancel)))
                  (==
                    (cons (quote unit) left_tail)
                    (by
                      (simpa only right_head_unit)))
                  (==
                    (cons left_head left_tail)
                    (by
                      (simpa only (symm left_head_unit))))))))))))
)

(theorem nat_le_of_add_sub_cancel
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to
          (add right (sub left right))
          left)
        (computes-to (nat-le right left) (quote :true)))))
  (by
    (intro left)
    (intro right)
    (intro add_sub_left)
    (obtain difference difference_proof
      (sub_computes_to_list left right))
    (calc
      (nat-le right left)
      (==
        (nat-le right (add right (sub left right)))
        (by
          (rewrite (symm add_sub_left))
          (eval)))
      (==
        (nat-le right (add right difference))
        (by
          (rewrite difference_proof)
          (eval)))
      (==
        (quote :true)
        (by
          (exact nat_le_left_add right difference))))))

(theorem nat_lt_right_left_implies_nat_lt_zero_sub
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-lt right left) (quote :true))
        (computes-to
          (nat-lt zero (sub left right))
          (quote :true)))))
  (by
    (list-induction left
      (by
        (list-induction right
          (by
            (intro right_lt_left)
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
                      (exact right_lt_left)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to
                      (nat-lt zero (sub nil nil))
                      (quote :true)))))))
          zero_right_head
          zero_right_tail
          zero_right_induction_hypothesis
          (by
            (intro right_lt_left)
            (have impossible_eq
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (nat-lt (cons zero_right_head zero_right_tail) nil)
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact right_lt_left)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to
                      (nat-lt zero (sub nil (cons zero_right_head zero_right_tail)))
                      (quote :true))))))))
)
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro right_lt_left)
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro right_lt_left)
            (have tail_lt_left
              (computes-to (nat-lt right_tail left_tail) (quote :true))
              (by
                (calc
                  (nat-lt right_tail left_tail)
                  (==
                    (nat-lt (cons right_head right_tail) (cons left_head left_tail))
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact right_lt_left)))))
              (by
                (specialize tail_positive induction_hypothesis right_tail)
                (calc
                  (nat-lt zero (sub (cons left_head left_tail) (cons right_head right_tail)))
                  (==
                    (nat-lt nil (sub left_tail right_tail))
                    (by
                      (eval)))
                  (==
                    (nat-lt zero (sub left_tail right_tail))
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact tail_positive)))))))))))
)

(theorem nat_lt_zero_sub_implies_nat_lt_right_left
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to
          (nat-lt zero (sub left right))
          (quote :true))
        (computes-to (nat-lt right left) (quote :true)))))
  (by
    (list-induction left
      (by
        (list-induction right
          (by
            (intro sub_positive)
            (have impossible_eq
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (nat-lt zero (sub nil nil))
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact sub_positive)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to (nat-lt nil nil) (quote :true)))))))
          zero_right_head
          zero_right_tail
          zero_right_induction_hypothesis
          (by
            (intro sub_positive)
            (have impossible_eq
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (nat-lt zero (sub nil (cons zero_right_head zero_right_tail)))
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact sub_positive)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (computes-to
                      (nat-lt (cons zero_right_head zero_right_tail) nil)
                      (quote :true))))))))
)
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro sub_positive)
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro sub_positive)
            (have tail_sub_positive
              (computes-to
                (nat-lt zero (sub left_tail right_tail))
                (quote :true))
              (by
                (calc
                  (nat-lt zero (sub left_tail right_tail))
                  (==
                    (nat-lt nil (sub left_tail right_tail))
                    (by
                      (eval)))
                  (==
                    (nat-lt zero (sub (cons left_head left_tail) (cons right_head right_tail)))
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact sub_positive)))))
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
                      (exact tail_lt)))))))))))
)

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
