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

(theorem reverse_acc_computes_to_list
  (forall list
    (implies
      (is-list list)
      (forall acc
        (implies
          (is-list acc)
          (computes-to-list result (reverse_acc list acc))))))
  (proof
    (list-induction list
      (forall acc
        (implies
          (is-list acc)
          (computes-to-list result (reverse_acc list acc))))
      (forall-intro acc
        (implies-intro acc_is_list
          (is-list acc)
          (exists-intro result
            (and
              (computes-to (reverse_acc nil acc) result)
              (is-list result))
            acc
            (and-intro
              (eval-to (reverse_acc nil acc) acc)
              (assume acc_is_list)))))
      head
      tail
      head_is_value
      tail_is_list
      induction_hypothesis
      (forall-intro acc
        (implies-intro acc_is_list
          (is-list acc)
          (rewrite
            (symm
              (eval-same
                (reverse_acc (cons head tail) acc)
                (reverse_acc tail (cons head acc))))
            (implies-elim
              (forall-elim
                (assume induction_hypothesis)
                (cons head acc))
              (list-cons
                head
                acc
                (assume head_is_value)
                (assume acc_is_list)))
            rewrite_target
            (computes-to-list result rewrite_target)))))))

(theorem reverse_computes_to_list
  (forall list
    (implies
      (is-list list)
      (computes-to-list result (reverse list))))
  (proof
    (forall-intro list
      (implies-intro list_is_list
        (is-list list)
        (rewrite
          (symm
            (eval-to
              (reverse list)
              (reverse_acc list nil)))
          (implies-elim
            (forall-elim
              (implies-elim
                (forall-elim
                  (known reverse_acc_computes_to_list)
                  list)
                (assume list_is_list))
              nil)
            (list-nil))
          rewrite_target
          (computes-to-list result rewrite_target))))))
