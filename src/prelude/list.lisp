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
  (forall-list list
    (forall-list acc
      (computes-to-list result (reverse_acc list acc))))
  (proof
    (list-induction list
      (forall-list acc
        (computes-to-list result (reverse_acc list acc)))
      (forall-list-intro acc
        (exists-list-intro result
          (computes-to (reverse_acc nil acc) result)
          acc
          (eval-to (reverse_acc nil acc) acc)))
      head
      tail
      induction_hypothesis
      (forall-list-intro acc
        (rewrite
          (symm
            (eval-same
              (reverse_acc (cons head tail) acc)
              (reverse_acc tail (cons head acc))))
          (forall-list-elim
            (assume induction_hypothesis)
            (cons head acc))
          rewrite_target
          (computes-to-list result rewrite_target))))))

(theorem reverse_computes_to_list
  (forall-list list
    (computes-to-list result (reverse list)))
  (proof
    (forall-list-intro list
      (rewrite
        (symm
          (eval-to
            (reverse list)
            (reverse_acc list nil)))
        (forall-list-elim
          (forall-list-elim
            (known reverse_acc_computes_to_list)
            list)
          nil)
        rewrite_target
        (computes-to-list result rewrite_target)))))

(theorem reverse_nil_computes_to_list
  (computes-to-list result (reverse nil))
  (proof
    (forall-list-elim
      (known reverse_computes_to_list)
      nil)))

(theorem append_nil_computes_to_list
  (forall-list right
    (computes-to-list result (append nil right)))
  (proof
    (forall-list-intro right
      (exists-list-intro result
        (computes-to (append nil right) result)
        right
        (eval-to (append nil right) right)))))

(theorem append_computes_to_list
  (forall-list left
    (forall-list right
      (computes-to-list result (append left right))))
  (proof
    (list-induction left
      (forall-list right
        (computes-to-list result (append left right)))
      (forall-list-intro right
        (exists-list-intro result
          (computes-to (append nil right) result)
          right
          (eval-to (append nil right) right)))
      head
      tail
      induction_hypothesis
      (forall-list-intro right
        (exists-list-elim
          (forall-list-elim
            (assume induction_hypothesis)
            right)
          tail_result
          tail_result_proof
          (exists-list-intro result
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
