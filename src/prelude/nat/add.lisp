; Nat addition theorems for the standard prelude.

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

(theorem nat_lt_add_right
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-lt zero right) (quote :true))
        (computes-to
          (nat-lt left (add left right))
          (quote :true)))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro right_positive)
        (calc
          (nat-lt nil (add nil right))
          (==
            (nat-lt nil right)
            (by
              (eval)))
          (==
            (nat-lt zero right)
            (by
              (fold zero)
              (eval)))
          (==
            (quote :true)
            (by
              (exact right_positive)))))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (intro right_positive)
        (obtain tail_sum tail_sum_proof
          (add_computes_to_list tail right))
        (calc
          (nat-lt (cons head tail) (add (cons head tail) right))
          (==
            (nat-lt (cons head tail) (cons head (add tail right)))
            (by
              (simpa only (add_cons head tail right))))
          (==
            (nat-lt (cons head tail) (cons head tail_sum))
            (by
              (simpa only tail_sum_proof)))
          (==
            (nat-lt tail tail_sum)
            (by
              (eval)))
          (==
            (nat-lt tail (add tail right))
            (by
              (simpa only (symm tail_sum_proof))))
          (==
            (quote :true)
            (by
              (exact induction_hypothesis right))))))))

(theorem nat_lt_add_left
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (nat-lt zero left) (quote :true))
        (computes-to
          (nat-lt right (add left right))
          (quote :true)))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro left_positive)
        (have impossible_eq
          (computes-to (quote :false) (quote :true))
          (by
            (calc
              (quote :false)
              (==
                (nat-lt zero nil)
                (by
                  (fold zero)
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact left_positive)))))
          (by
            (exact
              (absurd-elim
                (distinct-outcomes impossible_eq)
                (computes-to
                  (nat-lt right (add nil right))
                  (quote :true)))))))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (intro left_positive)
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
                  (exact nat_le_right_add tail right)))))
          (by
            (specialize right_lt_cons
              nat_le_implies_nat_lt_cons_right
              right
              tail_sum
              head)
            (calc
              (nat-lt right (add (cons head tail) right))
              (==
                (nat-lt right (cons head (add tail right)))
                (by
                  (simpa only (add_cons head tail right))))
              (==
                (nat-lt right (cons head tail_sum))
                (by
                  (simpa only tail_sum_proof)))
              (==
                (quote :true)
                (by
                  (exact right_lt_cons))))))))))

(theorem nat_le_add_right
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (nat-le left (add left right))
        (quote :true))))
  (by
    (intro left)
    (intro right)
    (exact nat_le_left_add left right)))

(theorem nat_le_add_left
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (nat-le right (add left right))
        (quote :true))))
  (by
    (intro left)
    (intro right)
    (exact nat_le_right_add left right)))

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

(theorem nat_le_add_cancel_left
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
    (intro prefix)
    (intro prefixed_le)
    (exact nat_le_add_left_cancel left right prefix)))

(theorem nat_lt_add_cancel_left
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
    (intro prefix)
    (intro prefixed_lt)
    (exact nat_lt_add_left_cancel left right prefix)))

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

(theorem min_add_distrib
  (forall prefix (is-list prefix)
    (forall left (is-list left)
      (forall right (is-list right)
        (implies
          (computes-to (is-nat-value prefix) (quote :true))
          (computes-to
            (min (add prefix left) (add prefix right))
            (add prefix (min left right)))))))
  (by
    (list-induction prefix
      (by
        (intro left)
        (intro right)
        (intro prefix_is_nat)
        (obtain inner_min inner_min_proof
          (min_computes_to_list left right))
        (calc
          (min (add nil left) (add nil right))
          (==
            (min left right)
            (by
              (eval)))
          (==
            inner_min
            (by
              (exact inner_min_proof)))
          (==
            (add nil inner_min)
            (by
              (exact
                (symm
                  (eval-to (add nil inner_min) inner_min)))))
          (==
            (add nil (min left right))
            (by
              (simpa only (symm inner_min_proof))))))
      head
      tail
      induction_hypothesis
      (by
        (intro left)
        (intro right)
        (intro prefix_is_nat)
        (specialize prefix_parts is_nat_value_cons_true_elim head tail)
        (cases prefix_parts head_unit tail_is_nat)
        (specialize tail_distrib induction_hypothesis left right)
        (obtain tail_left tail_left_proof
          (add_computes_to_list tail left))
        (obtain tail_right tail_right_proof
          (add_computes_to_list tail right))
        (obtain inner_min inner_min_proof
          (min_computes_to_list left right))
        (obtain tail_inner tail_inner_proof
          (add_computes_to_list tail inner_min))
        (calc
          (min
            (add (cons head tail) left)
            (add (cons head tail) right))
          (==
            (min
              (cons head (add tail left))
              (add (cons head tail) right))
            (by
              (simpa only (add_cons head tail left))))
          (==
            (min
              (cons head tail_left)
              (add (cons head tail) right))
            (by
              (simpa only tail_left_proof)))
          (==
            (min
              (cons head tail_left)
              (cons head (add tail right)))
            (by
              (simpa only (add_cons head tail right))))
          (==
            (min
              (cons head tail_left)
              (cons head tail_right))
            (by
              (simpa only tail_right_proof)))
          (==
            (succ (min tail_left tail_right))
            (by
              (exact min_cons head tail_left head tail_right)))
          (==
            (succ (min (add tail left) tail_right))
            (by
              (simpa only (symm tail_left_proof))))
          (==
            (succ (min (add tail left) (add tail right)))
            (by
              (simpa only (symm tail_right_proof))))
          (==
            (succ (add tail (min left right)))
            (by
              (simpa only tail_distrib)))
          (==
            (succ (add tail inner_min))
            (by
              (simpa only inner_min_proof)))
          (==
            (succ tail_inner)
            (by
              (simpa only tail_inner_proof)))
          (==
            (cons (quote unit) tail_inner)
            (by
              (eval)))
          (==
            (cons head tail_inner)
            (by
              (simpa only (symm head_unit))))
          (==
            (cons head (add tail inner_min))
            (by
              (simpa only (symm tail_inner_proof))))
          (==
            (add (cons head tail) inner_min)
            (by
              (exact (symm (add_cons head tail inner_min)))))
          (==
            (add (cons head tail) (min left right))
            (by
              (simpa only (symm inner_min_proof)))))))))

(theorem max_add_distrib
  (forall prefix (is-list prefix)
    (forall left (is-list left)
      (forall right (is-list right)
        (implies
          (computes-to (is-nat-value prefix) (quote :true))
          (computes-to
            (max (add prefix left) (add prefix right))
            (add prefix (max left right)))))))
  (by
    (list-induction prefix
      (by
        (intro left)
        (intro right)
        (intro prefix_is_nat)
        (obtain inner_max inner_max_proof
          (max_computes_to_list left right))
        (calc
          (max (add nil left) (add nil right))
          (==
            (max left right)
            (by
              (eval)))
          (==
            inner_max
            (by
              (exact inner_max_proof)))
          (==
            (add nil inner_max)
            (by
              (exact
                (symm
                  (eval-to (add nil inner_max) inner_max)))))
          (==
            (add nil (max left right))
            (by
              (simpa only (symm inner_max_proof))))))
      head
      tail
      induction_hypothesis
      (by
        (intro left)
        (intro right)
        (intro prefix_is_nat)
        (specialize prefix_parts is_nat_value_cons_true_elim head tail)
        (cases prefix_parts head_unit tail_is_nat)
        (specialize tail_distrib induction_hypothesis left right)
        (obtain tail_left tail_left_proof
          (add_computes_to_list tail left))
        (obtain tail_right tail_right_proof
          (add_computes_to_list tail right))
        (obtain inner_max inner_max_proof
          (max_computes_to_list left right))
        (obtain tail_inner tail_inner_proof
          (add_computes_to_list tail inner_max))
        (calc
          (max
            (add (cons head tail) left)
            (add (cons head tail) right))
          (==
            (max
              (cons head (add tail left))
              (add (cons head tail) right))
            (by
              (simpa only (add_cons head tail left))))
          (==
            (max
              (cons head tail_left)
              (add (cons head tail) right))
            (by
              (simpa only tail_left_proof)))
          (==
            (max
              (cons head tail_left)
              (cons head (add tail right)))
            (by
              (simpa only (add_cons head tail right))))
          (==
            (max
              (cons head tail_left)
              (cons head tail_right))
            (by
              (simpa only tail_right_proof)))
          (==
            (succ (max tail_left tail_right))
            (by
              (exact max_cons head tail_left head tail_right)))
          (==
            (succ (max (add tail left) tail_right))
            (by
              (simpa only (symm tail_left_proof))))
          (==
            (succ (max (add tail left) (add tail right)))
            (by
              (simpa only (symm tail_right_proof))))
          (==
            (succ (add tail (max left right)))
            (by
              (simpa only tail_distrib)))
          (==
            (succ (add tail inner_max))
            (by
              (simpa only inner_max_proof)))
          (==
            (succ tail_inner)
            (by
              (simpa only tail_inner_proof)))
          (==
            (cons (quote unit) tail_inner)
            (by
              (eval)))
          (==
            (cons head tail_inner)
            (by
              (simpa only (symm head_unit))))
          (==
            (cons head (add tail inner_max))
            (by
              (simpa only (symm tail_inner_proof))))
          (==
            (add (cons head tail) inner_max)
            (by
              (exact (symm (add_cons head tail inner_max)))))
          (==
            (add (cons head tail) (max left right))
            (by
              (simpa only (symm inner_max_proof)))))))))

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

(theorem add_left_cancel
  (forall left (is-list left)
    (forall right (is-list right)
      (forall prefix (is-list prefix)
        (implies
          (computes-to (add prefix left) (add prefix right))
          (computes-to left right)))))
  (by
    (intro left)
    (intro right)
    (list-induction prefix
      (by
        (intro prefixed_equal)
        (calc
          left
          (==
            (add nil left)
            (by
              (exact
                (symm
                  (eval-to (add nil left) left)))))
          (==
            (add nil right)
            (by
              (exact prefixed_equal)))
          (==
            right
            (by
              (eval)))))
      prefix_head
      prefix_tail
      induction_hypothesis
      (by
        (intro prefixed_equal)
        (obtain left_sum left_sum_proof
          (add_computes_to_list prefix_tail left))
        (obtain right_sum right_sum_proof
          (add_computes_to_list prefix_tail right))
        (have tail_prefixed_equal
          (computes-to
            (add prefix_tail left)
            (add prefix_tail right))
          (by
            (have cons_sums_equal
              (computes-to
                (cons prefix_head left_sum)
                (cons prefix_head right_sum))
              (by
                (calc
                  (cons prefix_head left_sum)
                  (==
                    (cons prefix_head (add prefix_tail left))
                    (by
                      (simpa only (symm left_sum_proof))))
                  (==
                    (add (cons prefix_head prefix_tail) left)
                    (by
                      (exact (symm (add_cons prefix_head prefix_tail left)))))
                  (==
                    (add (cons prefix_head prefix_tail) right)
                    (by
                      (exact prefixed_equal)))
                  (==
                    (cons prefix_head (add prefix_tail right))
                    (by
                      (exact add_cons prefix_head prefix_tail right)))
                  (==
                    (cons prefix_head right_sum)
                    (by
                      (simpa only right_sum_proof)))))
              (by
                (have sums_equal
                  (computes-to left_sum right_sum)
                  (by
                    (apply
                      cons_injective_tail
                      prefix_head
                      left_sum
                      prefix_head
                      right_sum))
                  (by
                    (calc
                      (add prefix_tail left)
                      (==
                        left_sum
                        (by
                          (exact left_sum_proof)))
                      (==
                        right_sum
                        (by
                          (exact sums_equal)))
                      (==
                        (add prefix_tail right)
                        (by
                          (exact (symm right_sum_proof))))))))))
          (by
            (specialize tail_cancel induction_hypothesis)
            (exact tail_cancel)))))))

(theorem add_right_cancel
  (forall left (is-list left)
    (forall right (is-list right)
      (forall suffix (is-list suffix)
        (implies
          (computes-to (is-nat-value left) (quote :true))
          (implies
            (computes-to (is-nat-value right) (quote :true))
            (implies
              (computes-to (is-nat-value suffix) (quote :true))
              (implies
                (computes-to (add left suffix) (add right suffix))
                (computes-to left right))))))))
  (by
    (intro left)
    (intro right)
    (intro suffix)
    (intro left_is_nat)
    (intro right_is_nat)
    (intro suffix_is_nat)
    (intro suffixed_equal)
    (have prefixed_equal
      (computes-to (add suffix left) (add suffix right))
      (by
        (calc
          (add suffix left)
          (==
            (add left suffix)
            (by
              (exact add_comm suffix left)))
          (==
            (add right suffix)
            (by
              (exact suffixed_equal)))
          (==
            (add suffix right)
            (by
              (exact add_comm right suffix)))))
      (by
        (apply add_left_cancel left right suffix)))))

(theorem add_left_eq_zero
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (add left right) zero)
        (computes-to left zero))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro sum_zero)
        (exact (symm zero_eq_nil)))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (intro sum_zero)
        (obtain tail_sum tail_sum_proof
          (add_computes_to_list tail right))
        (have impossible_eq
          (computes-to (cons head tail_sum) nil)
          (by
            (calc
              (cons head tail_sum)
              (==
                (cons head (add tail right))
                (by
                  (simpa only (symm tail_sum_proof))))
              (==
                (add (cons head tail) right)
                (by
                  (exact (symm (add_cons head tail right)))))
              (==
                zero
                (by
                  (exact sum_zero)))
              (==
                nil
                (by
                  (exact zero_eq_nil)))))
          (by
            (have contradiction
              (absurd)
              (by
                (apply cons_not_nil head tail_sum))
              (by
                (exact
                  (absurd-elim
                    contradiction
                    (computes-to (cons head tail) zero)))))))))))

(theorem add_right_eq_zero
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (add left right) zero)
        (computes-to right zero))))
  (by
    (list-induction left
      (by
        (intro right)
        (intro sum_zero)
        (calc
          right
          (==
            (add nil right)
            (by
              (exact
                (symm
                  (eval-to (add nil right) right)))))
          (==
            zero
            (by
              (exact sum_zero)))))
      head
      tail
      induction_hypothesis
      (by
        (intro right)
        (intro sum_zero)
        (obtain tail_sum tail_sum_proof
          (add_computes_to_list tail right))
        (have impossible_eq
          (computes-to (cons head tail_sum) nil)
          (by
            (calc
              (cons head tail_sum)
              (==
                (cons head (add tail right))
                (by
                  (simpa only (symm tail_sum_proof))))
              (==
                (add (cons head tail) right)
                (by
                  (exact (symm (add_cons head tail right)))))
              (==
                zero
                (by
                  (exact sum_zero)))
              (==
                nil
                (by
                  (exact zero_eq_nil)))))
          (by
            (have contradiction
              (absurd)
              (by
                (apply cons_not_nil head tail_sum))
              (by
                (exact
                  (absurd-elim
                    contradiction
                    (computes-to right zero)))))))))))

(theorem add_eq_zero_cases
  (forall left (is-list left)
    (forall right (is-list right)
      (implies
        (computes-to (add left right) zero)
        (and
          (computes-to left zero)
          (computes-to right zero)))))
  (by
    (intro left)
    (intro right)
    (intro sum_zero)
    (split
      (by
        (apply add_left_eq_zero left right))
      (by
        (apply add_right_eq_zero left right)))))

(theorem nat_le_add_right_cancel
  (forall left (is-list left)
    (forall right (is-list right)
      (forall suffix (is-list suffix)
        (implies
          (computes-to (is-nat-value left) (quote :true))
          (implies
            (computes-to (is-nat-value right) (quote :true))
            (implies
              (computes-to (is-nat-value suffix) (quote :true))
              (implies
                (computes-to
                  (nat-le (add left suffix) (add right suffix))
                  (quote :true))
                (computes-to (nat-le left right) (quote :true)))))))))
  (by
    (intro left)
    (intro right)
    (intro suffix)
    (intro left_is_nat)
    (intro right_is_nat)
    (intro suffix_is_nat)
    (intro suffixed_le)
    (have prefixed_le
      (computes-to
        (nat-le (add suffix left) (add suffix right))
        (quote :true))
      (by
        (calc
          (nat-le (add suffix left) (add suffix right))
          (==
            (nat-le (add left suffix) (add suffix right))
            (by
              (simpa only (add_comm suffix left))))
          (==
            (nat-le (add left suffix) (add right suffix))
            (by
              (simpa only (add_comm suffix right))))
          (==
            (quote :true)
            (by
              (exact suffixed_le)))))
      (by
        (specialize prefix_cancel nat_le_add_left_cancel left right suffix)
        (exact prefix_cancel)))))

(theorem nat_lt_add_right_cancel
  (forall left (is-list left)
    (forall right (is-list right)
      (forall suffix (is-list suffix)
        (implies
          (computes-to (is-nat-value left) (quote :true))
          (implies
            (computes-to (is-nat-value right) (quote :true))
            (implies
              (computes-to (is-nat-value suffix) (quote :true))
              (implies
                (computes-to
                  (nat-lt (add left suffix) (add right suffix))
                  (quote :true))
                (computes-to (nat-lt left right) (quote :true)))))))))
  (by
    (intro left)
    (intro right)
    (intro suffix)
    (intro left_is_nat)
    (intro right_is_nat)
    (intro suffix_is_nat)
    (intro suffixed_lt)
    (have prefixed_lt
      (computes-to
        (nat-lt (add suffix left) (add suffix right))
        (quote :true))
      (by
        (calc
          (nat-lt (add suffix left) (add suffix right))
          (==
            (nat-lt (add left suffix) (add suffix right))
            (by
              (simpa only (add_comm suffix left))))
          (==
            (nat-lt (add left suffix) (add right suffix))
            (by
              (simpa only (add_comm suffix right))))
          (==
            (quote :true)
            (by
              (exact suffixed_lt)))))
      (by
        (specialize prefix_cancel nat_lt_add_left_cancel left right suffix)
        (exact prefix_cancel)))))

(theorem nat_le_add_cancel_right
  (forall left (is-list left)
    (forall right (is-list right)
      (forall suffix (is-list suffix)
        (implies
          (computes-to (is-nat-value left) (quote :true))
          (implies
            (computes-to (is-nat-value right) (quote :true))
            (implies
              (computes-to (is-nat-value suffix) (quote :true))
              (implies
                (computes-to
                  (nat-le (add left suffix) (add right suffix))
                  (quote :true))
                (computes-to (nat-le left right) (quote :true)))))))))
  (by
    (intro left)
    (intro right)
    (intro suffix)
    (intro left_is_nat)
    (intro right_is_nat)
    (intro suffix_is_nat)
    (intro suffixed_le)
    (exact nat_le_add_right_cancel left right suffix)))

(theorem nat_lt_add_cancel_right
  (forall left (is-list left)
    (forall right (is-list right)
      (forall suffix (is-list suffix)
        (implies
          (computes-to (is-nat-value left) (quote :true))
          (implies
            (computes-to (is-nat-value right) (quote :true))
            (implies
              (computes-to (is-nat-value suffix) (quote :true))
              (implies
                (computes-to
                  (nat-lt (add left suffix) (add right suffix))
                  (quote :true))
                (computes-to (nat-lt left right) (quote :true)))))))))
  (by
    (intro left)
    (intro right)
    (intro suffix)
    (intro left_is_nat)
    (intro right_is_nat)
    (intro suffix_is_nat)
    (intro suffixed_lt)
    (exact nat_lt_add_right_cancel left right suffix)))

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
