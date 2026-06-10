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
