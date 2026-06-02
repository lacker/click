; List definitions for the standard prelude.

(def reverse_acc
  ((lambda fixed_point_function
     ((lambda fixed_point_self
        (fixed_point_function
          (lambda fixed_point_value
            ((fixed_point_self fixed_point_self) fixed_point_value))))
      (lambda fixed_point_self
        (fixed_point_function
          (lambda fixed_point_value
            ((fixed_point_self fixed_point_self) fixed_point_value))))))
   (lambda self
     (lambda list
       (lambda acc
         (list-case list
           acc
           cell
           ((self (tail cell))
            (cons (head cell) acc))))))))

(def reverse
  (lambda list
    ((reverse_acc list) nil)))

(def append
  ((lambda fixed_point_function
     ((lambda fixed_point_self
        (fixed_point_function
          (lambda fixed_point_value
            ((fixed_point_self fixed_point_self) fixed_point_value))))
      (lambda fixed_point_self
        (fixed_point_function
          (lambda fixed_point_value
            ((fixed_point_self fixed_point_self) fixed_point_value))))))
   (lambda self
     (lambda left
       (lambda right
         (list-case left
           right
           cell
           (cons
             (head cell)
             ((self (tail cell)) right))))))))

(theorem reverse_acc_computes_to_list
  (forall list (is-list list)
    (forall acc (is-list acc)
      (computes-to-list result (reverse_acc list acc))))
  (proof
    (list-induction list
      (forall acc (is-list acc)
        (computes-to-list result (reverse_acc list acc)))
      (forall-intro acc (is-list acc)
        (exists-intro result (is-list result)
          (computes-to (reverse_acc nil acc) result)
          acc
          (eval-to (reverse_acc nil acc) acc)))
      head
      tail
      induction_hypothesis
      (forall-intro acc (is-list acc)
        (rewrite
          (symm
            (eval-same
              (reverse_acc (cons head tail) acc)
              (reverse_acc tail (cons head acc))))
          (forall-elim
            (assume induction_hypothesis)
            (cons head acc))
          rewrite_target
          (computes-to-list result rewrite_target))))))

(theorem reverse_computes_to_list
  (forall list (is-list list)
    (computes-to-list result (reverse list)))
  (proof
    (forall-intro list (is-list list)
      (rewrite
        (symm
          (eval-to
            (reverse list)
            (reverse_acc list nil)))
        (forall-elim
          (forall-elim
            (known reverse_acc_computes_to_list)
            list)
          nil)
        rewrite_target
        (computes-to-list result rewrite_target)))))

(theorem reverse_nil_computes_to_list
  (computes-to-list result (reverse nil))
  (proof
    (forall-elim
      (known reverse_computes_to_list)
      nil)))

(theorem reverse_nil
  (computes-to (reverse nil) nil)
  (proof
    (eval-to (reverse nil) nil)))

(theorem reverse_singleton
  (forall head (is-value head)
    (computes-to
      (reverse (cons head nil))
      (cons head nil)))
  (proof
    (forall-intro head (is-value head)
      (eval-same
        (reverse (cons head nil))
        (cons head nil)))))

(theorem append_nil_computes_to_list
  (forall right (is-list right)
    (computes-to-list result (append nil right)))
  (proof
    (forall-intro right (is-list right)
      (exists-intro result (is-list result)
        (computes-to (append nil right) result)
        right
        (eval-to (append nil right) right)))))

(theorem append_computes_to_list
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to-list result (append left right))))
  (proof
    (list-induction left
      (forall right (is-list right)
        (computes-to-list result (append left right)))
      (forall-intro right (is-list right)
        (exists-intro result (is-list result)
          (computes-to (append nil right) result)
          right
          (eval-to (append nil right) right)))
      head
      tail
      induction_hypothesis
      (forall-intro right (is-list right)
        (exists-elim
          (forall-elim
            (assume induction_hypothesis)
            right)
          tail_result
          tail_result_proof
          (exists-intro result (is-list result)
            (computes-to (append (cons head tail) right) result)
            (cons head tail_result)
            (rewrite
              (assume tail_result_proof)
              (eval-same
                (append (cons head tail) right)
                (cons head (append tail right)))
              rewrite_target
              (computes-to
                (append (cons head tail) right)
                (cons head rewrite_target)))))))))

(theorem append_nil_returns_right
  (forall right (is-list right)
    (computes-to (append nil right) right))
  (proof
    (forall-intro right (is-list right)
      (eval-to (append nil right) right))))

(theorem append_right_nil
  (forall left (is-list left)
    (computes-to (append left nil) left))
  (proof
    (list-induction left
      (computes-to (append left nil) left)
      (eval-to (append nil nil) nil)
      head
      tail
      induction_hypothesis
      (rewrite
        (assume induction_hypothesis)
        (eval-same
          (append (cons head tail) nil)
          (cons head (append tail nil)))
        rewrite_target
        (computes-to
          (append (cons head tail) nil)
          (cons head rewrite_target))))))

(theorem append_cons
  (forall head (is-value head)
    (forall tail (is-list tail)
      (forall right (is-list right)
        (computes-to
          (append (cons head tail) right)
          (cons head (append tail right))))))
  (proof
    (forall-intro head (is-value head)
      (forall-intro tail (is-list tail)
        (forall-intro right (is-list right)
          (eval-same
            (append (cons head tail) right)
            (cons head (append tail right))))))))

(theorem append_singleton
  (forall head (is-value head)
    (forall right (is-list right)
      (computes-to
        (append (cons head nil) right)
        (cons head right))))
  (proof
    (forall-intro head (is-value head)
      (forall-intro right (is-list right)
        (eval-same
          (append (cons head nil) right)
          (cons head right))))))

(theorem append_assoc
  (forall left (is-list left)
    (forall middle (is-list middle)
      (forall right (is-list right)
        (computes-to
          (append (append left middle) right)
          (append left (append middle right))))))
  (proof
    (list-induction left
      (forall middle (is-list middle)
        (forall right (is-list right)
          (computes-to
            (append (append left middle) right)
            (append left (append middle right)))))
      (forall-intro middle (is-list middle)
        (forall-intro right (is-list right)
          (trans
            (symm
              (rewrite
                (forall-elim
                  (known append_nil_returns_right)
                  middle)
                (eval-to
                  (append (append nil middle) right)
                  (append (append nil middle) right))
                rewrite_target
                (computes-to
                  (append rewrite_target right)
                  (append (append nil middle) right))))
            (symm
              (exists-elim
                (forall-elim
                  (forall-elim
                    (known append_computes_to_list)
                    middle)
                  right)
                middle_right
                middle_right_proof
                (rewrite
                  (symm
                    (assume middle_right_proof))
                  (forall-elim
                    (known append_nil_returns_right)
                    middle_right)
                  rewrite_target
                  (computes-to
                    (append nil rewrite_target)
                    rewrite_target)))))))
      head
      tail
      induction_hypothesis
      (forall-intro middle (is-list middle)
        (forall-intro right (is-list right)
          (exists-elim
            (forall-elim
              (forall-elim
                (known append_computes_to_list)
                tail)
              middle)
            tail_middle
            tail_middle_proof
            (exists-elim
              (forall-elim
                (forall-elim
                  (known append_computes_to_list)
                  middle)
                right)
              middle_right
              middle_right_proof
              (trans
                (symm
                  (rewrite
                    (forall-elim
                      (forall-elim
                        (forall-elim
                          (known append_cons)
                          head)
                        tail)
                      middle)
                    (eval-to
                      (append (append (cons head tail) middle) right)
                      (append (append (cons head tail) middle) right))
                    rewrite_target
                    (computes-to
                      (append rewrite_target right)
                      (append (append (cons head tail) middle) right))))
                (trans
                  (rewrite
                    (symm
                      (assume tail_middle_proof))
                    (forall-elim
                      (forall-elim
                        (forall-elim
                          (known append_cons)
                          head)
                        tail_middle)
                      right)
                    rewrite_target
                    (computes-to
                      (append (cons head rewrite_target) right)
                      (cons head (append rewrite_target right))))
                  (trans
                    (rewrite
                      (forall-elim
                        (forall-elim
                          (assume induction_hypothesis)
                          middle)
                        right)
                      (eval-to
                        (cons head (append (append tail middle) right))
                        (cons head (append (append tail middle) right)))
                      rewrite_target
                      (computes-to
                        (cons head (append (append tail middle) right))
                        (cons head rewrite_target)))
                    (symm
                      (rewrite
                        (symm
                          (assume middle_right_proof))
                        (forall-elim
                          (forall-elim
                            (forall-elim
                              (known append_cons)
                              head)
                            tail)
                          middle_right)
                        rewrite_target
                        (computes-to
                          (append (cons head tail) rewrite_target)
                          (cons head (append tail rewrite_target)))))))))))))))
