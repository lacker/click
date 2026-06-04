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
    (calc
      (add (cons head tail) right)
      (==
        (append (cons head tail) right)
        (by
          (eval)))
      (==
        (cons head (append tail right))
        (by
          (exact append_cons head tail right)))
      (==
        (cons head (add tail right))
        (by
          (rewrite (symm (add_is_append tail right)))
          (eval))))))

(theorem add_succ_left
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (add (succ left) right)
        (succ (add left right)))))
  (by
    (intro left)
    (intro right)
    (exists-elim
      (add_computes_to_list left right)
      sum
      sum_proof)
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
          (rewrite sum_proof)
          (eval)))
      (==
        (succ sum)
        (by
          (eval)))
      (==
        (succ (add left right))
        (by
          (rewrite (symm sum_proof))
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
        (exists-elim
          (add_computes_to_list tail right)
          tail_sum
          tail_sum_proof)
        (calc
          (is-nat-value (add (cons head tail) right))
          (==
            (is-nat-value (cons head (add tail right)))
            (by
              (rewrite (add_cons head tail right))
              (eval)))
          (==
            (is-nat-value (cons head tail_sum))
            (by
              (rewrite tail_sum_proof)
              (eval)))
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
              (rewrite (symm tail_sum_proof))
              (eval)))
          (==
            (if
              (symbol-eq head (quote unit))
              (is-nat-value tail)
              (quote :false))
            (by
              (rewrite
                (implies-elim
                  (forall-elim (assume induction_hypothesis) right)
                  (assume right_is_nat)))
              (eval)))
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
    (calc
      (is-nat-value (add left right))
      (==
        (is-nat-value left)
        (by
          (exact
            (implies-elim
              (forall-elim
                (forall-elim
                  (known add_nat_suffix_preserves_nat_value)
                  left)
                right)
              (assume right_is_nat)))))
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
    (exists-elim
      (add_computes_to_list left middle)
      left_middle
      left_middle_proof)
    (exists-elim
      (add_computes_to_list middle right)
      middle_right
      middle_right_proof)
    (calc
      (add (add left middle) right)
      (==
        (add left_middle right)
        (by
          (rewrite left_middle_proof)
          (eval)))
      (==
        (append left_middle right)
        (by
          (exact add_is_append left_middle right)))
      (==
        (append (add left middle) right)
        (by
          (rewrite (symm left_middle_proof))
          (eval)))
      (==
        (append (append left middle) right)
        (by
          (rewrite (add_is_append left middle))
          (eval)))
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
          (rewrite middle_right_proof)
          (eval)))
      (==
        (add left middle_right)
        (by
          (exact (symm (add_is_append left middle_right)))))
      (==
        (add left (add middle right))
        (by
          (rewrite (symm middle_right_proof))
          (eval))))))

(theorem mul_zero_left
  (forall right (is-list right)
    (computes-to (mul zero right) zero))
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
        (exists-elim
          (forall-elim (assume induction_hypothesis) right)
          tail_product
          tail_product_proof)
        (exists-elim
          (add_computes_to_list right tail_product)
          product
          product_proof)
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
                  (rewrite tail_product_proof)
                  (eval)))
              (==
                product
                (by
                  (exact product_proof))))))))))

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
        (exists-elim
          (mul_computes_to_list tail nil)
          tail_product
          tail_product_proof)
        (calc
          (mul (cons head tail) zero)
          (==
            (mul (cons head tail) nil)
            (by
              (rewrite (eval-to zero nil))
              (eval)))
          (==
            (add nil (mul tail nil))
            (by
              (exact mul_cons head tail nil)))
          (==
            (add zero tail_product)
            (by
              (rewrite tail_product_proof)
              (eval)))
          (==
            tail_product
            (by
              (exact add_zero_left tail_product)))
          (==
            (mul tail nil)
            (by
              (rewrite (symm tail_product_proof))
              (eval)))
          (==
            (mul tail zero)
            (by
              (rewrite (symm (eval-to zero nil)))
              (eval)))
          (==
            zero
            (by
              (exact induction_hypothesis))))))))

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
          (rewrite (eval-to zero nil))
          (eval)))
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
          (rewrite (mul_zero_left right))
          (eval)))
      (==
        right
        (by
          (exact add_zero_right right))))))
