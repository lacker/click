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

(def mul
  (lambda left
    (lambda right
      (list-case left
        nil
        cell
        (add right (mul (tail cell) right))))))

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
              (rewrite (symm (eval-to zero nil)))
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
          (rewrite (symm (eval-to zero nil)))
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
              (exact (symm (eval-to zero nil)))))
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
              (exact (symm (eval-to zero nil)))))
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
