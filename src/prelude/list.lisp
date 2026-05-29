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
          (computes-to-list result (reverse_acc list acc)))))))

(theorem reverse_computes_to_list
  (forall list
    (implies
      (is-list list)
      (computes-to-list result (reverse list)))))
