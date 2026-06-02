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

(theorem reverse_acc_append
  (forall list (is-list list)
    (forall acc (is-list acc)
      (computes-to
        (reverse_acc list acc)
        (append (reverse list) acc))))
  (proof
    (list-induction list
      (forall acc (is-list acc)
        (computes-to
          (reverse_acc list acc)
          (append (reverse list) acc)))
      (forall-intro acc (is-list acc)
        (eval-same
          (reverse_acc nil acc)
          (append (reverse nil) acc)))
      head
      tail
      induction_hypothesis
      (forall-intro acc (is-list acc)
        (exists-elim
          (forall-elim
            (known reverse_computes_to_list)
            tail)
          tail_reversed
          tail_reversed_proof
          (trans
            (trans
              (eval-same
                (reverse_acc (cons head tail) acc)
                (reverse_acc tail (cons head acc)))
              (rewrite
                (assume tail_reversed_proof)
                (forall-elim
                  (assume induction_hypothesis)
                  (cons head acc))
                rewrite_target
                (computes-to
                  (reverse_acc tail (cons head acc))
                  (append rewrite_target (cons head acc)))))
            (trans
              (symm
                (rewrite
                  (forall-elim
                    (forall-elim
                      (known append_singleton)
                      head)
                    acc)
                  (forall-elim
                    (forall-elim
                      (forall-elim
                        (known append_assoc)
                        tail_reversed)
                      (cons head nil))
                    acc)
                  rewrite_target
                  (computes-to
                    (append (append tail_reversed (cons head nil)) acc)
                    (append tail_reversed rewrite_target))))
              (rewrite
                (symm
                  (trans
                    (trans
                      (eval-to
                        (reverse (cons head tail))
                        (reverse_acc (cons head tail) nil))
                      (eval-same
                        (reverse_acc (cons head tail) nil)
                        (reverse_acc tail (cons head nil))))
                    (rewrite
                      (assume tail_reversed_proof)
                      (forall-elim
                        (assume induction_hypothesis)
                        (cons head nil))
                      rewrite_target
                      (computes-to
                        (reverse_acc tail (cons head nil))
                        (append rewrite_target (cons head nil))))))
                (eval-to
                  (append (append tail_reversed (cons head nil)) acc)
                  (append (append tail_reversed (cons head nil)) acc))
                rewrite_target
                (computes-to
                  (append (append tail_reversed (cons head nil)) acc)
                  (append rewrite_target acc))))))))))

(theorem reverse_cons
  (forall head (is-value head)
    (forall tail (is-list tail)
      (computes-to
        (reverse (cons head tail))
        (append (reverse tail) (cons head nil)))))
  (proof
    (forall-intro head (is-value head)
      (forall-intro tail (is-list tail)
        (trans
          (trans
            (eval-to
              (reverse (cons head tail))
              (reverse_acc (cons head tail) nil))
            (eval-same
              (reverse_acc (cons head tail) nil)
              (reverse_acc tail (cons head nil))))
          (forall-elim
            (forall-elim
              (known reverse_acc_append)
              tail)
            (cons head nil)))))))

(theorem reverse_acc_reverse
  (forall list (is-list list)
    (forall acc (is-list acc)
      (computes-to
        (reverse (reverse_acc list acc))
        (append (reverse acc) list))))
  (proof
    (list-induction list
      (forall acc (is-list acc)
        (computes-to
          (reverse (reverse_acc list acc))
          (append (reverse acc) list)))
      (forall-intro acc (is-list acc)
        (exists-elim
          (forall-elim
            (known reverse_computes_to_list)
            acc)
          acc_reversed
          acc_reversed_proof
          (trans
            (rewrite
              (eval-to
                (reverse_acc nil acc)
                acc)
              (eval-to
                (reverse (reverse_acc nil acc))
                (reverse (reverse_acc nil acc)))
              rewrite_target
              (computes-to
                (reverse (reverse_acc nil acc))
                (reverse rewrite_target)))
            (trans
              (assume acc_reversed_proof)
              (trans
                (symm
                  (forall-elim
                    (known append_right_nil)
                    acc_reversed))
                (rewrite
                  (symm
                    (assume acc_reversed_proof))
                  (eval-to
                    (append acc_reversed nil)
                    (append acc_reversed nil))
                  rewrite_target
                  (computes-to
                    (append acc_reversed nil)
                    (append rewrite_target nil))))))))
      head
      tail
      induction_hypothesis
      (forall-intro acc (is-list acc)
        (exists-elim
          (forall-elim
            (known reverse_computes_to_list)
            acc)
          acc_reversed
          acc_reversed_proof
          (trans
            (trans
              (rewrite
                (eval-same
                  (reverse_acc (cons head tail) acc)
                  (reverse_acc tail (cons head acc)))
                (eval-to
                  (reverse (reverse_acc (cons head tail) acc))
                  (reverse (reverse_acc (cons head tail) acc)))
                rewrite_target
                (computes-to
                  (reverse (reverse_acc (cons head tail) acc))
                  (reverse rewrite_target)))
              (forall-elim
                (assume induction_hypothesis)
                (cons head acc)))
            (trans
              (rewrite
                (rewrite
                  (assume acc_reversed_proof)
                  (forall-elim
                    (forall-elim
                      (known reverse_cons)
                      head)
                    acc)
                  rewrite_target
                  (computes-to
                    (reverse (cons head acc))
                    (append rewrite_target (cons head nil))))
                (eval-to
                  (append (reverse (cons head acc)) tail)
                  (append (reverse (cons head acc)) tail))
                rewrite_target
                (computes-to
                  (append (reverse (cons head acc)) tail)
                  (append rewrite_target tail)))
              (trans
                (rewrite
                  (forall-elim
                    (forall-elim
                      (known append_singleton)
                      head)
                    tail)
                  (forall-elim
                    (forall-elim
                      (forall-elim
                        (known append_assoc)
                        acc_reversed)
                      (cons head nil))
                    tail)
                  rewrite_target
                  (computes-to
                    (append (append acc_reversed (cons head nil)) tail)
                    (append acc_reversed rewrite_target)))
                (rewrite
                  (symm
                    (assume acc_reversed_proof))
                  (eval-to
                    (append acc_reversed (cons head tail))
                    (append acc_reversed (cons head tail)))
                  rewrite_target
                  (computes-to
                    (append acc_reversed (cons head tail))
                    (append rewrite_target (cons head tail))))))))))))

(theorem reverse_double
  (forall list (is-list list)
    (computes-to
      (reverse (reverse list))
      list))
  (proof
    (forall-intro list (is-list list)
      (trans
        (rewrite
          (eval-to
            (reverse list)
            (reverse_acc list nil))
          (eval-to
            (reverse (reverse list))
            (reverse (reverse list)))
          rewrite_target
          (computes-to
            (reverse (reverse list))
            (reverse rewrite_target)))
        (trans
          (forall-elim
            (forall-elim
              (known reverse_acc_reverse)
              list)
            nil)
          (trans
            (rewrite
              (known reverse_nil)
              (eval-to
                (append (reverse nil) list)
                (append (reverse nil) list))
              rewrite_target
              (computes-to
                (append (reverse nil) list)
                (append rewrite_target list)))
            (forall-elim
              (known append_nil_returns_right)
              list)))))))

(theorem reverse_acc_of_append
  (forall left (is-list left)
    (forall right (is-list right)
      (forall acc (is-list acc)
        (computes-to
          (reverse_acc (append left right) acc)
          (reverse_acc right (reverse_acc left acc))))))
  (proof
    (list-induction left
      (forall right (is-list right)
        (forall acc (is-list acc)
          (computes-to
            (reverse_acc (append left right) acc)
            (reverse_acc right (reverse_acc left acc)))))
      (forall-intro right (is-list right)
        (forall-intro acc (is-list acc)
          (eval-same
            (reverse_acc (append nil right) acc)
            (reverse_acc right (reverse_acc nil acc)))))
      head
      tail
      induction_hypothesis
      (forall-intro right (is-list right)
        (forall-intro acc (is-list acc)
          (exists-elim
            (forall-elim
              (forall-elim
                (known append_computes_to_list)
                tail)
              right)
            tail_right
            tail_right_proof
            (trans
              (rewrite
                (forall-elim
                  (forall-elim
                    (forall-elim
                      (known append_cons)
                      head)
                    tail)
                  right)
                (eval-to
                  (reverse_acc (append (cons head tail) right) acc)
                  (reverse_acc (append (cons head tail) right) acc))
                rewrite_target
                (computes-to
                  (reverse_acc (append (cons head tail) right) acc)
                  (reverse_acc rewrite_target acc)))
              (trans
                (rewrite
                  (assume tail_right_proof)
                  (eval-to
                    (reverse_acc (cons head (append tail right)) acc)
                    (reverse_acc (cons head (append tail right)) acc))
                  rewrite_target
                  (computes-to
                    (reverse_acc (cons head (append tail right)) acc)
                    (reverse_acc (cons head rewrite_target) acc)))
                (trans
                  (eval-same
                    (reverse_acc (cons head tail_right) acc)
                    (reverse_acc tail_right (cons head acc)))
                  (trans
                    (rewrite
                      (symm
                        (assume tail_right_proof))
                      (eval-to
                        (reverse_acc tail_right (cons head acc))
                        (reverse_acc tail_right (cons head acc)))
                      rewrite_target
                      (computes-to
                        (reverse_acc tail_right (cons head acc))
                        (reverse_acc rewrite_target (cons head acc))))
                    (trans
                      (forall-elim
                        (forall-elim
                          (assume induction_hypothesis)
                          right)
                        (cons head acc))
                      (rewrite
                        (symm
                          (eval-same
                            (reverse_acc (cons head tail) acc)
                            (reverse_acc tail (cons head acc))))
                        (eval-to
                          (reverse_acc right (reverse_acc tail (cons head acc)))
                          (reverse_acc right (reverse_acc tail (cons head acc))))
                        rewrite_target
                        (computes-to
                          (reverse_acc right (reverse_acc tail (cons head acc)))
                          (reverse_acc right rewrite_target))))))))))))))

(theorem reverse_append
  (forall left (is-list left)
    (forall right (is-list right)
      (computes-to
        (reverse (append left right))
        (append (reverse right) (reverse left)))))
  (proof
    (forall-intro left (is-list left)
      (forall-intro right (is-list right)
        (exists-elim
          (forall-elim
            (forall-elim
              (known append_computes_to_list)
              left)
            right)
          appended
          appended_proof
          (exists-elim
            (forall-elim
              (forall-elim
                (known reverse_acc_computes_to_list)
                left)
              nil)
            left_reversed_acc
            left_reversed_acc_proof
            (trans
              (rewrite
                (assume appended_proof)
                (eval-to
                  (reverse (append left right))
                  (reverse (append left right)))
                rewrite_target
                (computes-to
                  (reverse (append left right))
                  (reverse rewrite_target)))
              (trans
                (eval-to
                  (reverse appended)
                  (reverse_acc appended nil))
                (trans
                  (rewrite
                    (symm
                      (assume appended_proof))
                    (eval-to
                      (reverse_acc appended nil)
                      (reverse_acc appended nil))
                    rewrite_target
                    (computes-to
                      (reverse_acc appended nil)
                      (reverse_acc rewrite_target nil)))
                  (trans
                    (forall-elim
                      (forall-elim
                        (forall-elim
                          (known reverse_acc_of_append)
                          left)
                        right)
                      nil)
                    (trans
                      (rewrite
                        (assume left_reversed_acc_proof)
                        (eval-to
                          (reverse_acc right (reverse_acc left nil))
                          (reverse_acc right (reverse_acc left nil)))
                        rewrite_target
                        (computes-to
                          (reverse_acc right (reverse_acc left nil))
                          (reverse_acc right rewrite_target)))
                      (trans
                        (forall-elim
                          (forall-elim
                            (known reverse_acc_append)
                            right)
                          left_reversed_acc)
                        (rewrite
                          (symm
                            (trans
                              (eval-to
                                (reverse left)
                                (reverse_acc left nil))
                              (assume left_reversed_acc_proof)))
                          (eval-to
                            (append (reverse right) left_reversed_acc)
                            (append (reverse right) left_reversed_acc))
                          rewrite_target
                          (computes-to
                            (append (reverse right) left_reversed_acc)
                            (append (reverse right) rewrite_target)))))))))))))))
