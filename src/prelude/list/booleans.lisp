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

(theorem if_false_result_with_true_then
  (forall condition
    (forall else_branch
      (implies
        (computes-to
          (if condition (quote :true) else_branch)
          (quote :false))
        (and
          (computes-to condition (quote :false))
          (computes-to else_branch (quote :false))))))
  (by
    (intro condition)
    (intro else_branch)
    (have condition_is_bool
      (is-bool condition)
      (proof
        (if-value-condition-bool (assume else_branch)))
      (by
        (or-elim condition_is_bool
          condition_true
          (by
            (have impossible_eq
              (computes-to (quote :true) (quote :false))
              (by
                (calc
                  (quote :true)
                  (==
                    (if condition (quote :true) else_branch)
                    (by
                      (simpa only condition_true)))
                  (==
                    (quote :false)
                    (by
                      (exact else_branch)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (and
                      (computes-to condition (quote :false))
                      (computes-to else_branch (quote :false))))))))
          condition_false
          (by
            (split
              (by
                (exact condition_false))
              (by
                (calc
                  else_branch
                  (==
                    (if condition (quote :true) else_branch)
                    (by
                      (simpa only condition_false)))
                  (==
                    (quote :false)
                    (by
                      (exact else_branch)))))))))))
  )

(theorem if_false_result_with_true_else
  (forall condition
    (forall then_branch
      (implies
        (computes-to
          (if condition then_branch (quote :true))
          (quote :false))
        (and
          (computes-to condition (quote :true))
          (computes-to then_branch (quote :false))))))
  (by
    (intro condition)
    (intro then_branch)
    (have condition_is_bool
      (is-bool condition)
      (proof
        (if-value-condition-bool (assume then_branch)))
      (by
        (or-elim condition_is_bool
          condition_true
          (by
            (split
              (by
                (exact condition_true))
              (by
                (calc
                  then_branch
                  (==
                    (if condition then_branch (quote :true))
                    (by
                      (simpa only condition_true)))
                  (==
                    (quote :false)
                    (by
                      (exact then_branch)))))))
          condition_false
          (by
            (have impossible_eq
              (computes-to (quote :true) (quote :false))
              (by
                (calc
                  (quote :true)
                  (==
                    (if condition then_branch (quote :true))
                    (by
                      (simpa only condition_false)))
                  (==
                    (quote :false)
                    (by
                      (exact then_branch)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes impossible_eq)
                    (and
                      (computes-to condition (quote :true))
                      (computes-to then_branch (quote :false)))))))))))))

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

(theorem symbol_eq_refl
  (forall value (is-value value)
    (implies
      (computes-to (is-symbol value) (quote :true))
      (computes-to
        (symbol-eq value value)
        (quote :true))))
  (by
    (intro value)
    (intro value_is_symbol)
    (eval)))

(theorem true_is_bool
  (is-bool (quote :true))
  (by
    (left
      (by
        (eval)))))

(theorem false_is_bool
  (is-bool (quote :false))
  (by
    (right
      (by
        (eval)))))

(theorem is_bool_elim
  (forall value (is-bool value)
    (or
      (computes-to value (quote :true))
      (computes-to value (quote :false))))
  (by
    (intro value)
    (exact value)))

(theorem bool_distinct
  (implies
    (computes-to (quote :true) (quote :false))
    (absurd))
  (by
    (intro true_is_false)
    (exact (distinct-outcomes true_is_false))))

(theorem not_true
  (forall value
    (implies
      (computes-to value (quote :true))
      (computes-to (not value) (quote :false))))
  (by
    (intro value)
    (calc
      (not value)
      (==
        (not (quote :true))
        (by
          (simpa only value)))
      (==
        (quote :false)
        (by
          (eval))))))

(theorem not_false
  (forall value
    (implies
      (computes-to value (quote :false))
      (computes-to (not value) (quote :true))))
  (by
    (intro value)
    (calc
      (not value)
      (==
        (not (quote :false))
        (by
          (simpa only value)))
      (==
        (quote :true)
        (by
          (eval))))))

(theorem not_computes_to_bool
  (forall value
    (implies
      (is-bool value)
      (is-bool (not value))))
  (by
    (intro value)
    (or-elim value
      value_true
      (by
        (right
          (by
            (apply not_true value))))
      value_false
      (by
        (left
          (by
            (apply not_false value)))))))

(theorem not_congr
  (forall left
    (forall right
      (implies
        (computes-to left right)
        (computes-to (not left) (not right)))))
  (by
    (intro left)
    (intro right)
    (simpa only right)))

(theorem not_true_elim
  (forall condition (is-bool condition)
    (implies
      (computes-to (not condition) (quote :true))
      (computes-to condition (quote :false))))
  (by
    (intro condition)
    (intro not_is_true)
    (or-elim condition
      condition_true
      (by
        (have not_is_false
          (computes-to
            (not condition)
            (quote :false))
          (by
            (apply not_true condition))
          (by
            (have false_is_true
              (computes-to
                (quote :false)
                (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (not condition)
                    (by
                      (exact (symm not_is_false))))
                  (==
                    (quote :true)
                    (by
                      (exact not_is_true)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes false_is_true)
                    (computes-to
                      condition
                      (quote :false)))))))))
      condition_false
      (by
        (exact condition_false)))))

(theorem not_false_elim
  (forall condition (is-bool condition)
    (implies
      (computes-to (not condition) (quote :false))
      (computes-to condition (quote :true))))
  (by
    (intro condition)
    (intro not_is_false)
    (or-elim condition
      condition_true
      (by
        (exact condition_true))
      condition_false
      (by
        (have not_is_true
          (computes-to
            (not condition)
            (quote :true))
          (by
            (apply not_false condition))
          (by
            (have true_is_false
              (computes-to
                (quote :true)
                (quote :false))
              (by
                (calc
                  (quote :true)
                  (==
                    (not condition)
                    (by
                      (exact (symm not_is_true))))
                  (==
                    (quote :false)
                    (by
                      (exact not_is_false)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes true_is_false)
                    (computes-to
                      condition
                      (quote :true))))))))))))

(theorem if_computes_to_bool
  (forall condition (is-bool condition)
    (forall then_branch (is-bool then_branch)
      (forall else_branch (is-bool else_branch)
        (is-bool (if condition then_branch else_branch)))))
  (by
    (intro condition)
    (intro then_branch)
    (intro else_branch)
    (or-elim condition
      condition_true
      (by
        (or-elim then_branch
          then_true
          (by
            (left
              (by
                (simpa only condition_true then_true))))
          then_false
          (by
            (right
              (by
                (simpa only condition_true then_false))))))
      condition_false
      (by
        (or-elim else_branch
          else_true
          (by
            (left
              (by
                (simpa only condition_false else_true))))
          else_false
          (by
            (right
              (by
                (simpa only condition_false else_false)))))))))

(theorem if_same
  (forall condition (is-bool condition)
    (forall branch
      (computes-to
        (if condition branch branch)
        branch)))
  (by
    (intro condition)
    (intro branch)
    (or-elim condition
      condition_true
      (by
        (apply if_condition_true condition branch branch))
      condition_false
      (by
        (apply if_condition_false condition branch branch)))))

(theorem if_not
  (forall condition (is-bool condition)
    (forall then_branch
      (forall else_branch
        (computes-to
          (if (not condition) then_branch else_branch)
          (if condition else_branch then_branch)))))
  (by
    (intro condition)
    (intro then_branch)
    (intro else_branch)
    (or-elim condition
      condition_true
      (by
        (have not_condition_false
          (computes-to (not condition) (quote :false))
          (by
            (apply not_true condition))
          (by
            (have right_is_else
              (computes-to
                (if condition else_branch then_branch)
                else_branch)
              (by
                (apply if_condition_true condition else_branch then_branch))
              (by
                (calc
                  (if (not condition) then_branch else_branch)
                  (==
                    (if (quote :false) then_branch else_branch)
                    (by
                      (simpa only not_condition_false)))
                  (==
                    else_branch
                    (by
                      (eval)))
                  (==
                    (if condition else_branch then_branch)
                    (by
                      (exact (symm right_is_else))))))))))
      condition_false
      (by
        (have not_condition_true
          (computes-to (not condition) (quote :true))
          (by
            (apply not_false condition))
          (by
            (have right_is_then
              (computes-to
                (if condition else_branch then_branch)
                then_branch)
              (by
                (apply if_condition_false condition else_branch then_branch))
              (by
                (calc
                  (if (not condition) then_branch else_branch)
                  (==
                    (if (quote :true) then_branch else_branch)
                    (by
                      (simpa only not_condition_true)))
                  (==
                    then_branch
                    (by
                      (eval)))
                  (==
                    (if condition else_branch then_branch)
                    (by
                      (exact (symm right_is_then)))))))))))))

(theorem if_congr_condition
  (forall left_condition
    (forall right_condition
      (implies
        (computes-to left_condition right_condition)
        (forall then_branch
          (forall else_branch
            (computes-to
              (if left_condition then_branch else_branch)
              (if right_condition then_branch else_branch)))))))
  (by
    (intro left_condition)
    (intro right_condition)
    (intro then_branch)
    (intro else_branch)
    (simpa only right_condition)))

(theorem if_congr_then
  (forall condition
    (forall left_then
      (forall right_then
        (implies
          (computes-to left_then right_then)
          (forall else_branch
            (computes-to
              (if condition left_then else_branch)
              (if condition right_then else_branch)))))))
  (by
    (intro condition)
    (intro left_then)
    (intro right_then)
    (intro else_branch)
    (simpa only right_then)))

(theorem if_congr_else
  (forall condition
    (forall then_branch
      (forall left_else
        (forall right_else
          (implies
            (computes-to left_else right_else)
            (computes-to
              (if condition then_branch left_else)
              (if condition then_branch right_else)))))))
  (by
    (intro condition)
    (intro then_branch)
    (intro left_else)
    (intro right_else)
    (simpa only right_else)))

(theorem and_true_left
  (forall left
    (implies
      (computes-to left (quote :true))
      (forall right
        (implies
          (is-bool right)
          (computes-to
            (and left right)
            right)))))
  (by
    (intro left)
    (intro right)
    (or-elim right
      right_true
      (by
        (calc
          (and left right)
          (==
            (quote :true)
            (by
              (simpa only left right_true)))
          (==
            right
            (by
              (exact (symm right_true))))))
      right_false
      (by
        (calc
          (and left right)
          (==
            (quote :false)
            (by
              (simpa only left right_false)))
          (==
            right
            (by
              (exact (symm right_false)))))))))

(theorem and_false_left
  (forall left
    (implies
      (computes-to left (quote :false))
      (forall right
        (implies
          (is-bool right)
          (computes-to
            (and left right)
            (quote :false))))))
  (by
    (intro left)
    (intro right)
    (or-elim right
      right_true
      (by
        (simpa only left right_true))
      right_false
      (by
        (simpa only left right_false)))))

(theorem and_computes_to_bool
  (forall left
    (implies
      (is-bool left)
      (forall right
        (implies
          (is-bool right)
          (is-bool (and left right))))))
  (by
    (intro left)
    (intro right)
    (or-elim left
      left_true
      (by
        (or-elim right
          right_true
          (by
            (left
              (by
                (calc
                  (and left right)
                  (==
                    right
                    (by
                      (apply and_true_left left right)))
                  (==
                    (quote :true)
                    (by
                      (exact right_true)))))))
          right_false
          (by
            (right
              (by
                (calc
                  (and left right)
                  (==
                    right
                    (by
                      (apply and_true_left left right)))
                  (==
                    (quote :false)
                    (by
                      (exact right_false)))))))))
      left_false
      (by
        (right
          (by
            (apply and_false_left left right)))))))

(theorem and_true_intro
  (forall left
    (implies
      (computes-to left (quote :true))
      (forall right
        (implies
          (computes-to right (quote :true))
          (computes-to
            (and left right)
            (quote :true))))))
  (by
    (intro left)
    (intro right)
    (have right_bool
      (is-bool right)
      (by
        (left
          (by
            (exact right))))
      (by
        (calc
          (and left right)
          (==
            right
            (by
              (apply and_true_left left right)))
          (==
            (quote :true)
            (by
              (exact right))))))))

(theorem and_true_elim_left
  (forall left
    (implies
      (is-bool left)
      (forall right
        (implies
          (is-bool right)
          (implies
            (computes-to
              (and left right)
              (quote :true))
            (computes-to left (quote :true)))))))
  (by
    (intro left)
    (intro right)
    (intro and_true)
    (or-elim left
      left_true
      (by
        (exact left_true))
      left_false
      (by
        (have and_is_false
          (computes-to
            (and left right)
            (quote :false))
          (by
            (apply and_false_left left right))
          (by
            (have false_is_true
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (and left right)
                    (by
                      (exact (symm and_is_false))))
                  (==
                    (quote :true)
                    (by
                      (exact and_true)))))
              (by
                (exact
                    (absurd-elim
                      (distinct-outcomes false_is_true)
                    (computes-to left (quote :true))))))))))))

(theorem and_true_elim_right
  (forall left
    (implies
      (is-bool left)
      (forall right
        (implies
          (is-bool right)
          (implies
            (computes-to
              (and left right)
              (quote :true))
            (computes-to right (quote :true)))))))
  (by
    (intro left)
    (intro right)
    (intro and_true)
    (or-elim left
      left_true
      (by
        (have and_is_right
          (computes-to
            (and left right)
            right)
          (by
            (apply and_true_left left right))
          (by
            (calc
              right
              (==
                (and left right)
                (by
                  (exact (symm and_is_right))))
              (==
                (quote :true)
                (by
                  (exact and_true)))))))
      left_false
      (by
        (have and_is_false
          (computes-to
            (and left right)
            (quote :false))
          (by
            (apply and_false_left left right))
          (by
            (have false_is_true
              (computes-to (quote :false) (quote :true))
              (by
                (calc
                  (quote :false)
                  (==
                    (and left right)
                    (by
                      (exact (symm and_is_false))))
                  (==
                    (quote :true)
                    (by
                      (exact and_true)))))
              (by
                (exact
                      (absurd-elim
                        (distinct-outcomes false_is_true)
                    (computes-to right (quote :true))))))))))))

(theorem and_false_cases
  (forall left
    (implies
      (is-bool left)
      (forall right
        (implies
          (is-bool right)
          (implies
            (computes-to
              (and left right)
              (quote :false))
            (or
              (computes-to left (quote :false))
              (computes-to right (quote :false))))))))
  (by
    (intro left)
    (intro right)
    (intro and_false)
    (or-elim left
      left_true
      (by
        (right
          (by
            (have and_is_right
              (computes-to
                (and left right)
                right)
              (by
                (apply and_true_left left right))
              (by
                (calc
                  right
                  (==
                    (and left right)
                    (by
                      (exact (symm and_is_right))))
                  (==
                    (quote :false)
                    (by
                      (exact and_false)))))))))
      left_false
      (by
        (left
          (by
            (exact left_false)))))))

(theorem or_true_left
  (forall left
    (implies
      (computes-to left (quote :true))
      (forall right
        (implies
          (is-bool right)
          (computes-to
            (or left right)
            (quote :true))))))
  (by
    (intro left)
    (intro right)
    (or-elim right
      right_true
      (by
        (simpa only left right_true))
      right_false
      (by
        (simpa only left right_false)))))

(theorem or_false_left
  (forall left
    (implies
      (computes-to left (quote :false))
      (forall right
        (implies
          (is-bool right)
          (computes-to
            (or left right)
            right)))))
  (by
    (intro left)
    (intro right)
    (or-elim right
      right_true
      (by
        (calc
          (or left right)
          (==
            (quote :true)
            (by
              (simpa only left right_true)))
          (==
            right
            (by
              (exact (symm right_true))))))
      right_false
      (by
        (calc
          (or left right)
          (==
            (quote :false)
            (by
              (simpa only left right_false)))
          (==
            right
            (by
              (exact (symm right_false)))))))))

(theorem or_computes_to_bool
  (forall left
    (implies
      (is-bool left)
      (forall right
        (implies
          (is-bool right)
          (is-bool (or left right))))))
  (by
    (intro left)
    (intro right)
    (or-elim left
      left_true
      (by
        (left
          (by
            (apply or_true_left left right))))
      left_false
      (by
        (or-elim right
          right_true
          (by
            (left
              (by
                (calc
                  (or left right)
                  (==
                    right
                    (by
                      (apply or_false_left left right)))
                  (==
                    (quote :true)
                    (by
                      (exact right_true)))))))
          right_false
          (by
            (right
              (by
                (calc
                  (or left right)
                  (==
                    right
                    (by
                      (apply or_false_left left right)))
                  (==
                    (quote :false)
                    (by
                      (exact right_false))))))))))))

(theorem or_false_intro
  (forall left
    (implies
      (computes-to left (quote :false))
      (forall right
        (implies
          (computes-to right (quote :false))
          (computes-to
            (or left right)
            (quote :false))))))
  (by
    (intro left)
    (intro right)
    (have right_bool
      (is-bool right)
      (by
        (right
          (by
            (exact right))))
      (by
        (calc
          (or left right)
          (==
            right
            (by
              (apply or_false_left left right)))
          (==
            (quote :false)
            (by
              (exact right))))))))

(theorem or_false_elim_left
  (forall left
    (implies
      (is-bool left)
      (forall right
        (implies
          (is-bool right)
          (implies
            (computes-to
              (or left right)
              (quote :false))
            (computes-to left (quote :false)))))))
  (by
    (intro left)
    (intro right)
    (intro or_false)
    (or-elim left
      left_true
      (by
        (have or_is_true
          (computes-to
            (or left right)
            (quote :true))
          (by
            (apply or_true_left left right))
          (by
            (have true_is_false
              (computes-to (quote :true) (quote :false))
              (by
                (calc
                  (quote :true)
                  (==
                    (or left right)
                    (by
                      (exact (symm or_is_true))))
                  (==
                    (quote :false)
                    (by
                      (exact or_false)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes true_is_false)
                    (computes-to left (quote :false)))))))))
      left_false
      (by
        (exact left_false)))))

(theorem or_false_elim_right
  (forall left
    (implies
      (is-bool left)
      (forall right
        (implies
          (is-bool right)
          (implies
            (computes-to
              (or left right)
              (quote :false))
            (computes-to right (quote :false)))))))
  (by
    (intro left)
    (intro right)
    (intro or_false)
    (or-elim left
      left_true
      (by
        (have or_is_true
          (computes-to
            (or left right)
            (quote :true))
          (by
            (apply or_true_left left right))
          (by
            (have true_is_false
              (computes-to (quote :true) (quote :false))
              (by
                (calc
                  (quote :true)
                  (==
                    (or left right)
                    (by
                      (exact (symm or_is_true))))
                  (==
                    (quote :false)
                    (by
                      (exact or_false)))))
              (by
                (exact
                  (absurd-elim
                    (distinct-outcomes true_is_false)
                    (computes-to right (quote :false)))))))))
      left_false
      (by
        (have or_is_right
          (computes-to
            (or left right)
            right)
          (by
            (apply or_false_left left right))
          (by
            (calc
              right
              (==
                (or left right)
                (by
                  (exact (symm or_is_right))))
              (==
                (quote :false)
                (by
                  (exact or_false))))))))))

(theorem or_true_cases
  (forall left
    (implies
      (is-bool left)
      (forall right
        (implies
          (is-bool right)
          (implies
            (computes-to
              (or left right)
              (quote :true))
            (or
              (computes-to left (quote :true))
              (computes-to right (quote :true))))))))
  (by
    (intro left)
    (intro right)
    (intro or_true)
    (or-elim left
      left_true
      (by
        (left
          (by
            (exact left_true))))
      left_false
      (by
        (right
          (by
            (have or_is_right
              (computes-to
                (or left right)
                right)
              (by
                (apply or_false_left left right))
              (by
                (calc
                  right
                  (==
                    (or left right)
                    (by
                      (exact (symm or_is_right))))
                  (==
                    (quote :true)
                    (by
                      (exact or_true))))))))))))

(theorem and_prop_to_bool
  (forall left
    (implies
      (computes-to left (quote :true))
      (forall right
        (implies
          (computes-to right (quote :true))
          (computes-to
            (and left right)
            (quote :true))))))
  (by
    (intro left)
    (intro right)
    (apply and_true_intro left right)))

(theorem and_bool_to_prop
  (forall left (is-bool left)
    (forall right (is-bool right)
      (implies
        (computes-to
          (and left right)
          (quote :true))
        (and
          (computes-to left (quote :true))
          (computes-to right (quote :true))))))
  (by
    (intro left)
    (intro right)
    (intro and_true)
    (split
      (by
        (apply and_true_elim_left left right))
      (by
        (apply and_true_elim_right left right)))))

(theorem or_prop_to_bool_left
  (forall left
    (implies
      (computes-to left (quote :true))
      (forall right (is-bool right)
        (computes-to
          (or left right)
          (quote :true)))))
  (by
    (intro left)
    (intro right)
    (apply or_true_left left right)))

(theorem or_prop_to_bool_right
  (forall left (is-bool left)
    (forall right
      (implies
        (computes-to right (quote :true))
        (computes-to
          (or left right)
          (quote :true)))))
  (by
    (intro left)
    (intro right)
    (have right_bool
      (is-bool right)
      (by
        (left
          (by
            (exact right))))
      (by
        (or-elim left
          left_true
          (by
            (apply or_true_left left right))
          left_false
          (by
            (calc
              (or left right)
              (==
                right
                (by
                  (apply or_false_left left right)))
              (==
                (quote :true)
                (by
                  (exact right))))))))))

(theorem or_bool_to_prop
  (forall left (is-bool left)
    (forall right (is-bool right)
      (implies
        (computes-to
          (or left right)
          (quote :true))
        (or
          (computes-to left (quote :true))
          (computes-to right (quote :true))))))
  (by
    (intro left)
    (intro right)
    (intro or_true)
    (apply or_true_cases left right)))

(theorem not_bool_to_absurd
  (forall value
    (implies
      (computes-to value (quote :true))
      (implies
        (computes-to (not value) (quote :true))
        (absurd))))
  (by
    (intro value)
    (intro not_is_true)
    (have not_is_false
      (computes-to (not value) (quote :false))
      (by
        (apply not_true value))
      (by
        (have false_is_true
          (computes-to (quote :false) (quote :true))
          (by
            (calc
              (quote :false)
              (==
                (not value)
                (by
                  (exact (symm not_is_false))))
              (==
                (quote :true)
                (by
                  (exact not_is_true)))))
          (by
            (exact (distinct-outcomes false_is_true))))))))

(theorem not_absurd_to_bool_false
  (forall value (is-bool value)
    (implies
      (implies
        (computes-to value (quote :true))
        (absurd))
      (computes-to value (quote :false))))
  (by
    (intro value)
    (intro value_true_absurd)
    (or-elim value
      value_true
      (by
        (exact
          (absurd-elim
            (implies-elim
              (assume value_true_absurd)
              (assume value_true))
            (computes-to value (quote :false)))))
      value_false
      (by
        (exact value_false)))))

(theorem not_not
  (forall value
    (implies
      (is-bool value)
      (computes-to (not (not value)) value)))
  (by
    (intro value)
    (or-elim value
      value_true
      (by
        (simpa only value_true))
      value_false
      (by
        (simpa only value_false)))))

(theorem and_true_right
  (forall value
    (implies
      (is-bool value)
      (computes-to
        (and value (quote :true))
        value)))
  (by
    (intro value)
    (or-elim value
      value_true
      (by
        (simpa only value_true))
      value_false
      (by
        (simpa only value_false)))))

(theorem and_false_right
  (forall value
    (implies
      (is-bool value)
      (computes-to
        (and value (quote :false))
        (quote :false))))
  (by
    (intro value)
    (or-elim value
      value_true
      (by
        (simpa only value_true))
      value_false
      (by
        (simpa only value_false)))))

(theorem or_true_right
  (forall value
    (implies
      (is-bool value)
      (computes-to
        (or value (quote :true))
        (quote :true))))
  (by
    (intro value)
    (or-elim value
      value_true
      (by
        (simpa only value_true))
      value_false
      (by
        (simpa only value_false)))))

(theorem or_false_right
  (forall value
    (implies
      (is-bool value)
      (computes-to
        (or value (quote :false))
        value)))
  (by
    (intro value)
    (or-elim value
      value_true
      (by
        (simpa only value_true))
      value_false
      (by
        (simpa only value_false)))))

(theorem and_comm
  (forall left
    (implies
      (is-bool left)
      (forall right
        (implies
          (is-bool right)
          (computes-to
            (and left right)
            (and right left))))))
  (by
    (intro left)
    (intro right)
    (or-elim left
      left_true
      (by
        (or-elim right
          right_true
          (by
            (simpa only left_true right_true))
          right_false
          (by
            (simpa only left_true right_false))))
      left_false
      (by
        (or-elim right
          right_true
          (by
            (simpa only left_false right_true))
          right_false
          (by
            (simpa only left_false right_false)))))))

(theorem and_assoc
  (forall left
    (implies
      (is-bool left)
      (forall middle
        (implies
          (is-bool middle)
          (forall right
            (implies
              (is-bool right)
              (computes-to
                (and (and left middle) right)
                (and left (and middle right)))))))))
  (by
    (intro left)
    (intro middle)
    (intro right)
    (or-elim left
      left_true
      (by
        (or-elim middle
          middle_true
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_true middle_true right_true))
              right_false
              (by
                (simpa only left_true middle_true right_false))))
          middle_false
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_true middle_false right_true))
              right_false
              (by
                (simpa only left_true middle_false right_false))))))
      left_false
      (by
        (or-elim middle
          middle_true
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_false middle_true right_true))
              right_false
              (by
                (simpa only left_false middle_true right_false))))
          middle_false
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_false middle_false right_true))
              right_false
              (by
                (simpa only left_false middle_false right_false)))))))))

(theorem and_idempotent
  (forall value
    (implies
      (is-bool value)
      (computes-to
        (and value value)
        value)))
  (by
    (intro value)
    (or-elim value
      value_true
      (by
        (simpa only value_true))
      value_false
      (by
        (simpa only value_false)))))

(theorem or_comm
  (forall left
    (implies
      (is-bool left)
      (forall right
        (implies
          (is-bool right)
          (computes-to
            (or left right)
            (or right left))))))
  (by
    (intro left)
    (intro right)
    (or-elim left
      left_true
      (by
        (or-elim right
          right_true
          (by
            (simpa only left_true right_true))
          right_false
          (by
            (simpa only left_true right_false))))
      left_false
      (by
        (or-elim right
          right_true
          (by
            (simpa only left_false right_true))
          right_false
          (by
            (simpa only left_false right_false)))))))

(theorem or_assoc
  (forall left
    (implies
      (is-bool left)
      (forall middle
        (implies
          (is-bool middle)
          (forall right
            (implies
              (is-bool right)
              (computes-to
                (or (or left middle) right)
                (or left (or middle right)))))))))
  (by
    (intro left)
    (intro middle)
    (intro right)
    (or-elim left
      left_true
      (by
        (or-elim middle
          middle_true
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_true middle_true right_true))
              right_false
              (by
                (simpa only left_true middle_true right_false))))
          middle_false
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_true middle_false right_true))
              right_false
              (by
                (simpa only left_true middle_false right_false))))))
      left_false
      (by
        (or-elim middle
          middle_true
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_false middle_true right_true))
              right_false
              (by
                (simpa only left_false middle_true right_false))))
          middle_false
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_false middle_false right_true))
              right_false
              (by
                (simpa only left_false middle_false right_false)))))))))

(theorem or_idempotent
  (forall value
    (implies
      (is-bool value)
      (computes-to
        (or value value)
        value)))
  (by
    (intro value)
    (or-elim value
      value_true
      (by
        (simpa only value_true))
      value_false
      (by
        (simpa only value_false)))))

(theorem and_absorb_or
  (forall left
    (implies
      (is-bool left)
      (forall right
        (implies
          (is-bool right)
          (computes-to
            (and left (or left right))
            left)))))
  (by
    (intro left)
    (intro right)
    (or-elim left
      left_true
      (by
        (or-elim right
          right_true
          (by
            (simpa only left_true right_true))
          right_false
          (by
            (simpa only left_true right_false))))
      left_false
      (by
        (or-elim right
          right_true
          (by
            (simpa only left_false right_true))
          right_false
          (by
            (simpa only left_false right_false)))))))

(theorem or_absorb_and
  (forall left
    (implies
      (is-bool left)
      (forall right
        (implies
          (is-bool right)
          (computes-to
            (or left (and left right))
            left)))))
  (by
    (intro left)
    (intro right)
    (or-elim left
      left_true
      (by
        (or-elim right
          right_true
          (by
            (simpa only left_true right_true))
          right_false
          (by
            (simpa only left_true right_false))))
      left_false
      (by
        (or-elim right
          right_true
          (by
            (simpa only left_false right_true))
          right_false
          (by
            (simpa only left_false right_false)))))))

(theorem and_distrib_or_left
  (forall left
    (implies
      (is-bool left)
      (forall middle
        (implies
          (is-bool middle)
          (forall right
            (implies
              (is-bool right)
              (computes-to
                (and left (or middle right))
                (or (and left middle) (and left right)))))))))
  (by
    (intro left)
    (intro middle)
    (intro right)
    (or-elim left
      left_true
      (by
        (or-elim middle
          middle_true
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_true middle_true right_true))
              right_false
              (by
                (simpa only left_true middle_true right_false))))
          middle_false
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_true middle_false right_true))
              right_false
              (by
                (simpa only left_true middle_false right_false))))))
      left_false
      (by
        (or-elim middle
          middle_true
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_false middle_true right_true))
              right_false
              (by
                (simpa only left_false middle_true right_false))))
          middle_false
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_false middle_false right_true))
              right_false
              (by
                (simpa only left_false middle_false right_false)))))))))

(theorem and_distrib_or_right
  (forall left
    (implies
      (is-bool left)
      (forall middle
        (implies
          (is-bool middle)
          (forall right
            (implies
              (is-bool right)
              (computes-to
                (and (or left middle) right)
                (or (and left right) (and middle right)))))))))
  (by
    (intro left)
    (intro middle)
    (intro right)
    (or-elim left
      left_true
      (by
        (or-elim middle
          middle_true
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_true middle_true right_true))
              right_false
              (by
                (simpa only left_true middle_true right_false))))
          middle_false
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_true middle_false right_true))
              right_false
              (by
                (simpa only left_true middle_false right_false))))))
      left_false
      (by
        (or-elim middle
          middle_true
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_false middle_true right_true))
              right_false
              (by
                (simpa only left_false middle_true right_false))))
          middle_false
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_false middle_false right_true))
              right_false
              (by
                (simpa only left_false middle_false right_false)))))))))

(theorem or_distrib_and_left
  (forall left
    (implies
      (is-bool left)
      (forall middle
        (implies
          (is-bool middle)
          (forall right
            (implies
              (is-bool right)
              (computes-to
                (or left (and middle right))
                (and (or left middle) (or left right)))))))))
  (by
    (intro left)
    (intro middle)
    (intro right)
    (or-elim left
      left_true
      (by
        (or-elim middle
          middle_true
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_true middle_true right_true))
              right_false
              (by
                (simpa only left_true middle_true right_false))))
          middle_false
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_true middle_false right_true))
              right_false
              (by
                (simpa only left_true middle_false right_false))))))
      left_false
      (by
        (or-elim middle
          middle_true
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_false middle_true right_true))
              right_false
              (by
                (simpa only left_false middle_true right_false))))
          middle_false
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_false middle_false right_true))
              right_false
              (by
                (simpa only left_false middle_false right_false)))))))))

(theorem or_distrib_and_right
  (forall left
    (implies
      (is-bool left)
      (forall middle
        (implies
          (is-bool middle)
          (forall right
            (implies
              (is-bool right)
              (computes-to
                (or (and left middle) right)
                (and (or left right) (or middle right)))))))))
  (by
    (intro left)
    (intro middle)
    (intro right)
    (or-elim left
      left_true
      (by
        (or-elim middle
          middle_true
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_true middle_true right_true))
              right_false
              (by
                (simpa only left_true middle_true right_false))))
          middle_false
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_true middle_false right_true))
              right_false
              (by
                (simpa only left_true middle_false right_false))))))
      left_false
      (by
        (or-elim middle
          middle_true
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_false middle_true right_true))
              right_false
              (by
                (simpa only left_false middle_true right_false))))
          middle_false
          (by
            (or-elim right
              right_true
              (by
                (simpa only left_false middle_false right_true))
              right_false
              (by
                (simpa only left_false middle_false right_false)))))))))

(theorem not_and
  (forall left
    (implies
      (is-bool left)
      (forall right
        (implies
          (is-bool right)
          (computes-to
            (not (and left right))
            (or (not left) (not right)))))))
  (by
    (intro left)
    (intro right)
    (or-elim left
      left_true
      (by
        (or-elim right
          right_true
          (by
            (simpa only left_true right_true))
          right_false
          (by
            (simpa only left_true right_false))))
      left_false
      (by
        (or-elim right
          right_true
          (by
            (simpa only left_false right_true))
          right_false
          (by
            (simpa only left_false right_false)))))))

(theorem not_or
  (forall left
    (implies
      (is-bool left)
      (forall right
        (implies
          (is-bool right)
          (computes-to
            (not (or left right))
            (and (not left) (not right)))))))
  (by
    (intro left)
    (intro right)
    (or-elim left
      left_true
      (by
        (or-elim right
          right_true
          (by
            (simpa only left_true right_true))
          right_false
          (by
            (simpa only left_true right_false))))
      left_false
      (by
        (or-elim right
          right_true
          (by
            (simpa only left_false right_true))
          right_false
          (by
            (simpa only left_false right_false)))))))
