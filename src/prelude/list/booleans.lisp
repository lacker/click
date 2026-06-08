; Boolean and symbol helper theorems for the standard prelude.

(theorem if_true
  (forall then
    (forall else
      (computes-to
        (if (quote :true) then else)
        then)))
  (by
    (intro then)
    (intro else)
    (eval)))

(theorem if_false
  (forall then
    (forall else
      (computes-to
        (if (quote :false) then else)
        else)))
  (by
    (intro then)
    (intro else)
    (eval)))

(theorem if_condition_true
  (forall condition
    (forall then
      (forall else
        (implies
          (computes-to condition (quote :true))
          (computes-to
            (if condition then else)
            then)))))
  (by
    (intro condition)
    (intro then)
    (intro else)
    (simpa only else)))

(theorem if_condition_false
  (forall condition
    (forall then
      (forall else
        (implies
          (computes-to condition (quote :false))
          (computes-to
            (if condition then else)
            else)))))
  (by
    (intro condition)
    (intro then)
    (intro else)
    (simpa only else)))

(theorem if_true_result_with_false_else
  (forall condition
    (forall then_branch
      (implies
        (computes-to
          (if condition then_branch (quote :false))
          (quote :true))
        (and
          (computes-to condition (quote :true))
          (computes-to then_branch (quote :true))))))
  (proof
    (forall-intro condition
      (forall-intro then_branch
        (implies-intro if_is_true
          (computes-to
            (if condition then_branch (quote :false))
            (quote :true))
          (and-intro
            (if-true-condition (assume if_is_true))
            (if-true-then (assume if_is_true))))))))

(theorem if_true_result_with_error_then
  (forall condition
    (forall else_branch
      (implies
        (computes-to
          (if condition (error 0) else_branch)
          (quote :true))
        (and
          (computes-to condition (quote :false))
          (computes-to else_branch (quote :true))))))
  (proof
    (forall-intro condition
      (forall-intro else_branch
        (implies-intro if_is_true
          (computes-to
            (if condition (error 0) else_branch)
            (quote :true))
          (and-intro
            (if-effect-then-condition-false (assume if_is_true))
            (if-effect-then-else (assume if_is_true))))))))

(theorem if_true_result_with_false_then
  (forall condition
    (forall else_branch
      (implies
        (computes-to
          (if condition (quote :false) else_branch)
          (quote :true))
        (and
          (computes-to condition (quote :false))
          (computes-to else_branch (quote :true))))))
  (by
    (intro condition)
    (intro else_branch)
    (have condition_is_bool
      (is-bool condition)
      (proof
        (if-value-condition-bool (assume else_branch))))
    (or-elim condition_is_bool
      condition_true
      (by
        (have impossible_eq
          (computes-to (quote :false) (quote :true))
          (by
            (calc
              (quote :false)
              (==
                (if condition (quote :false) else_branch)
                (by
                  (simpa only condition_true)))
              (==
                (quote :true)
                (by
                  (exact else_branch)))))
          (by
            (exact
              (absurd-elim
                (distinct-outcomes impossible_eq)
                (and
                  (computes-to condition (quote :false))
                  (computes-to else_branch (quote :true))))))))
      condition_false
      (by
        (split
          (by
            (exact condition_false))
          (by
            (calc
              else_branch
              (==
                (if condition (quote :false) else_branch)
                (by
                  (simpa only condition_false)))
              (==
                (quote :true)
                (by
                  (exact else_branch))))))))))

(theorem symbol_eq_unit_unit
  (computes-to
    (symbol-eq (quote unit) (quote unit))
    (quote :true))
  (by
    (eval)))

(theorem symbol_eq_true_false
  (computes-to
    (symbol-eq (quote :true) (quote :false))
    (quote :false))
  (by
    (eval)))

(theorem symbol_eq_true
  (forall left
    (forall right
      (implies
        (computes-to
          (symbol-eq left right)
          (quote :true))
        (computes-to left right))))
  (proof
    (forall-intro left
      (forall-intro right
        (implies-intro symbol_eq_is_true
          (computes-to
            (symbol-eq left right)
            (quote :true))
          (symbol-eq-true (assume symbol_eq_is_true)))))))
