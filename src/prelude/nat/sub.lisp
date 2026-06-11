; Nat subtraction theorems for the standard prelude.

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

(theorem sub_preserves_nat_value
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (implies
          (computes-to (is-nat-value right) (quote :true))
          (computes-to
            (is-nat-value (sub left right))
            (quote :true))))))
  (by
    (list-induction left
      (by
        (list-induction right
          (by
            (intro left_is_nat)
            (intro right_is_nat)
            (eval))
          zero_right_head
          zero_right_tail
          zero_right_induction_hypothesis
          (by
            (intro left_is_nat)
            (intro right_is_nat)
            (eval))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro left_is_nat)
            (intro right_is_nat)
            (calc
              (is-nat-value (sub (cons left_head left_tail) nil))
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
            (specialize tail_sub_is_nat induction_hypothesis right_tail)
            (calc
              (is-nat-value
                (sub
                  (cons left_head left_tail)
                  (cons right_head right_tail)))
              (==
                (is-nat-value (sub left_tail right_tail))
                (by
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact tail_sub_is_nat))))))))))

(theorem sub_add_right
  (forall left (is-list left)
    (forall right (is-list right)
      (forall middle (is-list middle)
        (computes-to
          (sub (sub left right) middle)
          (sub left (add right middle))))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro middle)
        (obtain sum sum_proof
          (add_computes_to_list right middle))
        (calc
          (sub (sub nil right) middle)
          (==
            (sub zero middle)
            (by
              (fold zero)
              (simpa only (sub_zero_left right))))
          (==
            zero
            (by
              (exact sub_zero_left middle)))
          (==
            (sub zero sum)
            (by
              (exact (symm (sub_zero_left sum)))))
          (==
            (sub nil sum)
            (by
              (eval)))
          (==
            (sub nil (add right middle))
            (by
              (simpa only (symm sum_proof))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro middle)
            (eval))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (intro middle)
            (specialize tail_result induction_hypothesis right_tail middle)
            (obtain right_tail_middle right_tail_middle_proof
              (add_computes_to_list right_tail middle))
            (calc
              (sub
                (sub
                  (cons left_head left_tail)
                  (cons right_head right_tail))
                middle)
              (==
                (sub (sub left_tail right_tail) middle)
                (by
                  (eval)))
              (==
                (sub left_tail (add right_tail middle))
                (by
                  (exact tail_result)))
              (==
                (sub left_tail right_tail_middle)
                (by
                  (simpa only right_tail_middle_proof)))
              (==
                (sub
                  (cons left_head left_tail)
                  (cons right_head right_tail_middle))
                (by
                  (eval)))
              (==
                (sub
                  (cons left_head left_tail)
                  (cons right_head (add right_tail middle)))
                (by
                  (simpa only (symm right_tail_middle_proof))))
              (==
                (sub
                  (cons left_head left_tail)
                  (add (cons right_head right_tail) middle))
                (by
                  (simpa only (add_cons right_head right_tail middle)))))))))
)
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

(theorem nat_le_of_sub_zero
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (sub left right) zero)
        (computes-to (nat-le left right) (quote :true)))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro sub_left_right_zero)
        (eval))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro sub_left_right_zero)
            (have impossible_eq
              (computes-to (quote :true) (quote :false))
              (by
                (calc
                  (quote :true)
                  (==
                    (nat-lt zero (cons left_head left_tail))
                    (by
                      (eval)))
                  (==
                    (nat-lt zero (sub (cons left_head left_tail) nil))
                    (by
                      (eval)))
                  (==
                    (nat-lt zero zero)
                    (by
                      (simpa only sub_left_right_zero)))
                  (==
                    (quote :false)
                    (by
                      (eval)))))
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
            (intro sub_left_right_zero)
            (have tail_sub_zero
              (computes-to (sub left_tail right_tail) zero)
              (by
                (calc
                  (sub left_tail right_tail)
                  (==
                    (sub (cons left_head left_tail) (cons right_head right_tail))
                    (by
                      (eval)))
                  (==
                    zero
                    (by
                      (exact sub_left_right_zero)))))
              (by
                (specialize tail_le_right induction_hypothesis right_tail)
                (calc
                  (nat-le (cons left_head left_tail) (cons right_head right_tail))
                  (==
                    (nat-le left_tail right_tail)
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact tail_le_right)))))))))))
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

(theorem nat_le_add_sub_cancel_right
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (implies
          (computes-to (is-nat-value right) (quote :true))
          (implies
            (computes-to (nat-le right left) (quote :true))
            (computes-to
              (add (sub left right) right)
              left))))))
  (by
    (intro left)
    (intro right)
    (intro left_is_nat)
    (intro right_is_nat)
    (intro right_le_left)
    (obtain difference difference_proof
      (sub_computes_to_list left right))
    (have difference_is_nat
      (computes-to (is-nat-value difference) (quote :true))
      (by
        (calc
          (is-nat-value difference)
          (==
            (is-nat-value (sub left right))
            (by
              (simpa only (symm difference_proof))))
          (==
            (quote :true)
            (by
              (exact sub_preserves_nat_value left right)))))
      (by
        (specialize commuted add_comm difference right)
        (specialize left_cancel nat_le_add_sub_cancel left right)
        (calc
          (add (sub left right) right)
          (==
            (add difference right)
            (by
              (simpa only difference_proof)))
          (==
            (add right difference)
            (by
              (exact commuted)))
          (==
            (add right (sub left right))
            (by
              (simpa only (symm difference_proof))))
          (==
            left
            (by
              (exact left_cancel)))))))
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

(theorem nat_le_of_add_sub_cancel_right
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (implies
          (computes-to (is-nat-value right) (quote :true))
          (implies
            (computes-to
              (add (sub left right) right)
              left)
            (computes-to (nat-le right left) (quote :true)))))))
  (by
    (intro left)
    (intro right)
    (intro left_is_nat)
    (intro right_is_nat)
    (intro right_sub_left)
    (obtain difference difference_proof
      (sub_computes_to_list left right))
    (have difference_is_nat
      (computes-to (is-nat-value difference) (quote :true))
      (by
        (calc
          (is-nat-value difference)
          (==
            (is-nat-value (sub left right))
            (by
              (simpa only (symm difference_proof))))
          (==
            (quote :true)
            (by
              (exact sub_preserves_nat_value left right)))))
      (by
        (specialize commuted add_comm difference right)
        (have left_sub_right
          (computes-to
            (add right (sub left right))
            left)
          (by
            (calc
              (add right (sub left right))
              (==
                (add right difference)
                (by
                  (simpa only difference_proof)))
              (==
                (add difference right)
                (by
                  (exact (symm commuted))))
              (==
                (add (sub left right) right)
                (by
                  (simpa only (symm difference_proof))))
              (==
                left
                (by
                  (exact right_sub_left)))))
          (by
            (specialize result nat_le_of_add_sub_cancel left right)
            (exact result))))))
)

(theorem sub_add_cancel
  (forall left (is-list left)
    (forall right (is-list right)
      (forall middle (is-list middle)
        (implies
          (computes-to (is-nat-value left) (quote :true))
          (implies
            (computes-to (is-nat-value right) (quote :true))
            (implies
              (computes-to (nat-le right left) (quote :true))
              (computes-to
                (sub (add left middle) right)
                (add (sub left right) middle))))))))
  (by
    (intro left)
    (intro right)
    (intro middle)
    (intro left_is_nat)
    (intro right_is_nat)
    (intro right_le_left)
    (obtain difference difference_proof
      (sub_computes_to_list left right))
    (obtain rest rest_proof
      (add_computes_to_list difference middle))
    (specialize cancel nat_le_add_sub_cancel left right)
    (calc
      (sub (add left middle) right)
      (==
        (sub (add (add right (sub left right)) middle) right)
        (by
          (rewrite (symm cancel))
          (eval)))
      (==
        (sub (add (add right difference) middle) right)
        (by
          (simpa only difference_proof)))
      (==
        (sub (add right (add difference middle)) right)
        (by
          (simpa only (add_assoc right difference middle))))
      (==
        (sub (add right rest) right)
        (by
          (simpa only rest_proof)))
      (==
        rest
        (by
          (exact add_sub_cancel_left right rest)))
      (==
        (add difference middle)
        (by
          (simpa only (symm rest_proof))))
      (==
        (add (sub left right) middle)
        (by
          (simpa only (symm difference_proof)))))))

(theorem sub_add_left
  (forall left (is-list left)
    (forall right (is-list right)
      (forall middle (is-list middle)
        (implies
          (computes-to (is-nat-value left) (quote :true))
          (implies
            (computes-to (is-nat-value right) (quote :true))
            (implies
              (computes-to (is-nat-value middle) (quote :true))
              (implies
                (computes-to (nat-le right left) (quote :true))
                (computes-to
                  (sub (add middle left) right)
                  (add middle (sub left right))))))))))
  (by
    (intro left)
    (intro right)
    (intro middle)
    (intro left_is_nat)
    (intro right_is_nat)
    (intro middle_is_nat)
    (intro right_le_left)
    (obtain difference difference_proof
      (sub_computes_to_list left right))
    (have difference_is_nat
      (computes-to (is-nat-value difference) (quote :true))
      (by
        (calc
          (is-nat-value difference)
          (==
            (is-nat-value (sub left right))
            (by
              (simpa only (symm difference_proof))))
          (==
            (quote :true)
            (by
              (exact sub_preserves_nat_value left right)))))
      (by
        (specialize middle_left_comm add_comm middle left)
        (specialize cancel sub_add_cancel left right middle)
        (specialize difference_middle_comm add_comm difference middle)
        (calc
          (sub (add middle left) right)
          (==
            (sub (add left middle) right)
            (by
              (simpa only middle_left_comm)))
          (==
            (add (sub left right) middle)
            (by
              (exact cancel)))
          (==
            (add difference middle)
            (by
              (simpa only difference_proof)))
          (==
            (add middle difference)
            (by
              (exact difference_middle_comm)))
          (==
            (add middle (sub left right))
            (by
              (simpa only (symm difference_proof))))))))
)

(theorem nat_le_sub_right_mono
  (forall left (is-list left)
    (forall right (is-list right)
      (forall middle (is-list middle)
        (implies
          (computes-to (nat-le left right) (quote :true))
          (computes-to
            (nat-le (sub left middle) (sub right middle))
            (quote :true))))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro middle)
        (intro left_le_right)
        (obtain right_difference right_difference_proof
          (sub_computes_to_list right middle))
        (calc
          (nat-le (sub nil middle) (sub right middle))
          (==
            (nat-le zero (sub right middle))
            (by
              (fold zero)
              (simpa only (sub_zero_left middle))))
          (==
            (nat-le zero right_difference)
            (by
              (simpa only right_difference_proof)))
          (==
            (quote :true)
            (by
              (exact nat_le_zero_left right_difference)))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro middle)
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
                        (sub (cons left_head left_tail) middle)
                        (sub nil middle))
                      (quote :true)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (list-induction middle
              (by
                (intro left_le_right)
                (calc
                  (nat-le
                    (sub (cons left_head left_tail) nil)
                    (sub (cons right_head right_tail) nil))
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
              middle_head
              middle_tail
              middle_induction_hypothesis
              (by
                (intro left_le_right)
                (have tail_le_right
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
                    (specialize tail_mono
                      induction_hypothesis
                      right_tail
                      middle_tail)
                    (calc
                      (nat-le
                        (sub
                          (cons left_head left_tail)
                          (cons middle_head middle_tail))
                        (sub
                          (cons right_head right_tail)
                          (cons middle_head middle_tail)))
                      (==
                        (nat-le
                          (sub left_tail middle_tail)
                          (sub right_tail middle_tail))
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact tail_mono)))))))))))))
)

(theorem nat_le_sub_left_anti
  (forall left (is-list left)
    (forall right (is-list right)
      (forall middle (is-list middle)
        (implies
          (computes-to (nat-le left right) (quote :true))
          (computes-to
            (nat-le (sub middle right) (sub middle left))
            (quote :true))))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro middle)
        (intro left_le_right)
        (calc
          (nat-le (sub middle right) (sub middle nil))
          (==
            (nat-le (sub middle right) middle)
            (by
              (eval)))
          (==
            (quote :true)
            (by
              (exact nat_le_sub_left middle right)))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro middle)
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
                        (sub middle nil)
                        (sub middle (cons left_head left_tail)))
                      (quote :true)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (list-induction middle
              (by
                (intro left_le_right)
                (eval))
              middle_head
              middle_tail
              middle_induction_hypothesis
              (by
                (intro left_le_right)
                (have tail_le_right
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
                    (specialize tail_anti
                      induction_hypothesis
                      right_tail
                      middle_tail)
                    (calc
                      (nat-le
                        (sub
                          (cons middle_head middle_tail)
                          (cons right_head right_tail))
                        (sub
                          (cons middle_head middle_tail)
                          (cons left_head left_tail)))
                      (==
                        (nat-le
                          (sub middle_tail right_tail)
                          (sub middle_tail left_tail))
                        (by
                          (eval)))
                      (==
                          (quote :true)
                        (by
                          (exact tail_anti)))))))))))))
)

(theorem sub_monotone_left
  (forall left (is-list left)
    (forall right (is-list right)
      (forall middle (is-list middle)
        (implies
          (computes-to (nat-le left right) (quote :true))
          (computes-to
            (nat-le (sub left middle) (sub right middle))
            (quote :true))))))
  (by
    (intro left)
    (intro right)
    (intro middle)
    (intro left_le_right)
    (exact nat_le_sub_right_mono left right middle)))

(theorem sub_monotone_right
  (forall left (is-list left)
    (forall right (is-list right)
      (forall middle (is-list middle)
        (implies
          (computes-to (nat-le left right) (quote :true))
          (computes-to
            (nat-le (sub middle right) (sub middle left))
            (quote :true))))))
  (by
    (intro left)
    (intro right)
    (intro middle)
    (intro left_le_right)
    (exact nat_le_sub_left_anti left right middle)))

(theorem nat_lt_sub_right_mono
  (forall left (is-list left)
    (forall right (is-list right)
      (forall middle (is-list middle)
        (implies
          (computes-to (nat-lt left right) (quote :true))
          (implies
            (computes-to (nat-le middle left) (quote :true))
            (computes-to
              (nat-lt (sub left middle) (sub right middle))
              (quote :true)))))))
  (by
    (list-induction left
      (by
        (list-induction right
          (by
            (intro middle)
            (intro left_lt_right)
            (intro middle_le_left)
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
                      (nat-lt
                        (sub nil middle)
                        (sub nil middle))
                      (quote :true)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (list-induction middle
              (by
                (intro left_lt_right)
                (intro middle_le_left)
                (eval))
              middle_head
              middle_tail
              middle_induction_hypothesis
              (by
                (intro left_lt_right)
                (intro middle_le_left)
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
                          (exact middle_le_left)))))
                  (by
                    (exact
                      (absurd-elim
                        (distinct-outcomes impossible_eq)
                        (computes-to
                          (nat-lt
                            (sub nil (cons middle_head middle_tail))
                            (sub
                              (cons right_head right_tail)
                              (cons middle_head middle_tail)))
                          (quote :true)))))))))))
      left_head
      left_tail
      induction_hypothesis
      (by
        (list-induction right
          (by
            (intro middle)
            (intro left_lt_right)
            (intro middle_le_left)
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
                        (sub (cons left_head left_tail) middle)
                        (sub nil middle))
                      (quote :true)))))))
          right_head
          right_tail
          right_induction_hypothesis
          (by
            (list-induction middle
              (by
                (intro left_lt_right)
                (intro middle_le_left)
                (calc
                  (nat-lt
                    (sub (cons left_head left_tail) nil)
                    (sub (cons right_head right_tail) nil))
                  (==
                    (nat-lt
                      (cons left_head left_tail)
                      (cons right_head right_tail))
                    (by
                      (eval)))
                  (==
                    (quote :true)
                    (by
                      (exact left_lt_right)))))
              middle_head
              middle_tail
              middle_induction_hypothesis
              (by
                (intro left_lt_right)
                (intro middle_le_left)
                (have tail_lt_right
                  (computes-to (nat-lt left_tail right_tail) (quote :true))
                  (by
                    (calc
                      (nat-lt left_tail right_tail)
                      (==
                        (nat-lt
                          (cons left_head left_tail)
                          (cons right_head right_tail))
                        (by
                          (eval)))
                      (==
                        (quote :true)
                        (by
                          (exact left_lt_right)))))
                  (by
                    (have middle_tail_le_left_tail
                      (computes-to
                        (nat-le middle_tail left_tail)
                        (quote :true))
                      (by
                        (calc
                          (nat-le middle_tail left_tail)
                          (==
                            (nat-le
                              (cons middle_head middle_tail)
                              (cons left_head left_tail))
                            (by
                              (eval)))
                          (==
                            (quote :true)
                            (by
                              (exact middle_le_left)))))
                      (by
                        (specialize tail_mono
                          induction_hypothesis
                          right_tail
                          middle_tail)
                        (calc
                          (nat-lt
                            (sub
                              (cons left_head left_tail)
                              (cons middle_head middle_tail))
                            (sub
                              (cons right_head right_tail)
                              (cons middle_head middle_tail)))
                          (==
                            (nat-lt
                              (sub left_tail middle_tail)
                              (sub right_tail middle_tail))
                            (by
                              (eval)))
                          (==
                            (quote :true)
                            (by
                              (exact tail_mono)))))))))))))
)
)
)

(theorem nat_eq_of_le_and_sub_zero
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (implies
          (computes-to (is-nat-value right) (quote :true))
          (implies
            (computes-to (nat-le left right) (quote :true))
            (implies
              (computes-to (sub right left) zero)
              (computes-to left right)))))))
  (by
    (intro left)
    (intro right)
    (intro left_is_nat)
    (intro right_is_nat)
    (intro left_le_right)
    (intro sub_right_left_zero)
    (have right_le_left
      (computes-to (nat-le right left) (quote :true))
      (by
        (exact nat_le_of_sub_zero right left))
      (by
        (have eq_true
          (computes-to (nat-eq left right) (quote :true))
          (by
            (exact nat_le_antisymm left right))
          (by
            (exact nat_eq_sound left right))))))
)

(theorem sub_eq_zero_of_nat_le
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-le left right) (quote :true))
        (computes-to (sub left right) zero))))
  (by
    (intro left)
    (intro right)
    (intro left_le_right)
    (exact nat_le_implies_sub_zero left right)))

(theorem sub_eq_zero_of_le
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-le left right) (quote :true))
        (computes-to (sub left right) zero))))
  (by
    (intro left)
    (intro right)
    (intro left_le_right)
    (exact sub_eq_zero_of_nat_le left right)))

(theorem nat_le_of_sub_eq_zero
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (sub left right) zero)
        (computes-to (nat-le left right) (quote :true)))))
  (by
    (intro left)
    (intro right)
    (intro sub_left_right_zero)
    (exact nat_le_of_sub_zero left right)))

(theorem nat_le_implies_exists_add
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (is-nat-value left) (quote :true))
        (implies
          (computes-to (is-nat-value right) (quote :true))
          (implies
            (computes-to (nat-le left right) (quote :true))
            (exists difference (is-list difference)
              (computes-to (add left difference) right)))))))
  (by
    (intro left)
    (intro right)
    (intro left_is_nat)
    (intro right_is_nat)
    (intro left_le_right)
    (obtain difference difference_proof
      (sub_computes_to_list right left))
    (exists difference
      (by
        (specialize cancel nat_le_add_sub_cancel right left)
        (calc
          (add left difference)
          (==
            (add left (sub right left))
            (by
              (simpa only (symm difference_proof))))
          (==
            right
            (by
              (exact cancel)))))))
)

(theorem nat_le_of_exists_add
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (exists difference (is-list difference)
          (computes-to (add left difference) right))
        (computes-to (nat-le left right) (quote :true)))))
  (by
    (intro left)
    (intro right)
    (intro left_prefixes_right)
    (obtain difference add_left_difference left_prefixes_right)
    (calc
      (nat-le left right)
      (==
        (nat-le left (add left difference))
        (by
          (simpa only (symm add_left_difference))))
      (==
        (quote :true)
        (by
          (exact nat_le_left_add left difference)))))
)

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

(theorem sub_pos_of_lt
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-lt right left) (quote :true))
        (computes-to
          (nat-lt zero (sub left right))
          (quote :true)))))
  (by
    (intro left)
    (intro right)
    (intro right_lt_left)
    (exact nat_lt_right_left_implies_nat_lt_zero_sub left right)))

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
