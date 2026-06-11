; A tiny C0 language model.
;
; This is intentionally a small executable model, not a parser for real C.
; C syntax, typing, and semantics are represented as ordinary Click values and
; computations so the existing kernel can prove facts about them.

(def c-type-int32
  (quote :c-type-int32))

(def c-type-bool
  (quote :c-type-bool))

(def c-int32
  (lambda bits
    (cons
      (quote :c-int32)
      (cons bits nil))))

(def c-int32-bits
  (lambda value
    (head (tail value))))

(def c-is-int32
  (lambda value
    (if
      (is-list-value value)
      (list-case value
        (quote :false)
        cell
        (and
          (symbol-eq (head cell) (quote :c-int32))
          (and
            (is-singleton (tail cell))
            (is-bv32 (head (tail cell))))))
      (quote :false))))

(def c-int32-zero
  (c-int32 (bv32 0)))

(def c-int32-one
  (c-int32 (bv32 1)))

(def c-int32-two
  (c-int32 (bv32 2)))

(def c-int32-max
  (c-int32 (bv32 2147483647)))

(def c-int32-lt-raw
  (lambda left
    (lambda right
      (bv32-slt
        (c-int32-bits left)
        (c-int32-bits right)))))

(def c-int32-lt
  (lambda left
    (lambda right
      (if
        (c-is-int32 left)
        (if
          (c-is-int32 right)
          (c-int32-lt-raw left right)
          (quote :false))
        (quote :false)))))

(def c-int32-expr
  (lambda value
    (cons
      (quote :c-int32-expr)
      (cons value nil))))

(def c-var-expr
  (lambda name
    (cons
      (quote :c-var-expr)
      (cons name nil))))

(def c-lt-expr
  (lambda left
    (lambda right
      (cons
        (quote :c-lt-expr)
        (cons left (cons right nil))))))

(def c-add-expr
  (lambda left
    (lambda right
      (cons
        (quote :c-add-expr)
        (cons left (cons right nil))))))

(def c-assign-stmt
  (lambda name
    (lambda expr
      (cons
        (quote :c-assign-stmt)
        (cons name (cons expr nil))))))

(def c-seq-stmt
  (lambda first
    (lambda second
      (cons
        (quote :c-seq-stmt)
        (cons first (cons second nil))))))

(def c-if-stmt
  (lambda condition
    (lambda then_branch
      (lambda else_branch
        (cons
          (quote :c-if-stmt)
          (cons condition (cons then_branch (cons else_branch nil))))))))

(def c-return-stmt
  (lambda expr
    (cons
      (quote :c-return-stmt)
      (cons expr nil))))

(def c-empty-env
  nil)

(def c-env-bind
  (lambda name
    (lambda value
      (lambda env
        (cons
          (cons name (cons value nil))
          env)))))

(def c-lookup
  (lambda name
    (lambda env
      (list-case env
        none
        cell
        (if
          (symbol-eq (head (head cell)) name)
          (some (head (tail (head cell))))
          (c-lookup name (tail cell)))))))

(def c-store-set
  (lambda name
    (lambda value
      (lambda store
        (list-case store
          (cons (cons name (cons value nil)) nil)
          cell
          (if
            (symbol-eq (head (head cell)) name)
            (cons
              (cons name (cons value nil))
              (tail cell))
            (cons
              (head cell)
              (c-store-set name value (tail cell)))))))))

(def c-expr-value
  (lambda value
    (cons
      (quote :c-expr-value)
      (cons value nil))))

(def c-ub-signed-overflow
  (quote :c-ub-signed-overflow))

(def c-expr-ub
  (lambda reason
    (cons
      (quote :c-expr-ub)
      (cons reason nil))))

(def c-expr-ub-reason
  (lambda expr_result
    (head (tail expr_result))))

(def c-expr-runtime-error
  (cons (quote :c-expr-runtime-error) nil))

(def c-expr-nonvalue-result
  (lambda expr_result
    (if
      (symbol-eq (head expr_result) (quote :c-expr-ub))
      expr_result
      c-expr-runtime-error)))

(def c-stmt-normal
  (lambda store
    (cons
      (quote :c-stmt-normal)
      (cons store nil))))

(def c-stmt-return
  (lambda value
    (cons
      (quote :c-stmt-return)
      (cons value nil))))

(def c-stmt-ub
  (lambda reason
    (cons
      (quote :c-stmt-ub)
      (cons reason nil))))

(def c-stmt-runtime-error
  (cons (quote :c-stmt-runtime-error) nil))

(def c-expr-result-to-stmt-nonvalue
  (lambda expr_result
    (if
      (symbol-eq (head expr_result) (quote :c-expr-ub))
      (c-stmt-ub (c-expr-ub-reason expr_result))
      c-stmt-runtime-error)))

(def c-int32-add
  (lambda left
    (lambda right
      (if
        (c-is-int32 left)
        (if
          (c-is-int32 right)
          (if
            (bv32-sadd-overflows
              (c-int32-bits left)
              (c-int32-bits right))
            (c-expr-ub c-ub-signed-overflow)
            (c-expr-value
              (c-int32
                (bv32-add
                  (c-int32-bits left)
                  (c-int32-bits right)))))
          c-expr-runtime-error)
        c-expr-runtime-error))))

(def c-value-has-type
  (lambda value
    (lambda type
      (if
        (symbol-eq type c-type-int32)
        (c-is-int32 value)
        (if
          (symbol-eq type c-type-bool)
          (or
            (value-eq value (quote :true))
            (value-eq value (quote :false)))
          (quote :false))))))

(def c-has-type
  (lambda type_env
    (lambda expr
      (lambda type
        (if
          (symbol-eq (head expr) (quote :c-int32-expr))
          (and
            (symbol-eq type c-type-int32)
            (c-is-int32 (head (tail expr))))
          (if
            (symbol-eq (head expr) (quote :c-var-expr))
            (list-case
              (c-lookup (head (tail expr)) type_env)
              (quote :false)
              option_cell
              (symbol-eq type (head (tail option_cell))))
            (if
              (symbol-eq (head expr) (quote :c-lt-expr))
              (and
                (symbol-eq type c-type-bool)
                (and
                  (c-has-type type_env (head (tail expr)) c-type-int32)
                  (c-has-type type_env (head (tail (tail expr))) c-type-int32)))
              (if
                (symbol-eq (head expr) (quote :c-add-expr))
                (and
                  (symbol-eq type c-type-int32)
                  (and
                    (c-has-type type_env (head (tail expr)) c-type-int32)
                    (c-has-type
                      type_env
                      (head (tail (tail expr)))
                      c-type-int32)))
                (quote :false)))))))))

(def c-stmt-well-typed
  (lambda type_env
    (lambda stmt
      (lambda return_type
        (if
          (symbol-eq (head stmt) (quote :c-assign-stmt))
          (list-case
            (c-lookup (head (tail stmt)) type_env)
            (quote :false)
            option_cell
            (c-has-type
              type_env
              (head (tail (tail stmt)))
              (head (tail option_cell))))
          (if
            (symbol-eq (head stmt) (quote :c-seq-stmt))
            (and
              (c-stmt-well-typed type_env (head (tail stmt)) return_type)
              (c-stmt-well-typed type_env (head (tail (tail stmt))) return_type))
            (if
              (symbol-eq (head stmt) (quote :c-if-stmt))
              (and
                (c-has-type type_env (head (tail stmt)) c-type-bool)
                (and
                  (c-stmt-well-typed
                    type_env
                    (head (tail (tail stmt)))
                    return_type)
                  (c-stmt-well-typed
                    type_env
                    (head (tail (tail (tail stmt))))
                    return_type)))
              (if
                (symbol-eq (head stmt) (quote :c-return-stmt))
                (c-has-type type_env (head (tail stmt)) return_type)
                (quote :false)))))))))

(def c-eval-expr
  (lambda store
    (lambda expr
      (if
        (symbol-eq (head expr) (quote :c-int32-expr))
        (if
          (c-is-int32 (head (tail expr)))
          (c-expr-value (head (tail expr)))
          c-expr-runtime-error)
        (if
          (symbol-eq (head expr) (quote :c-var-expr))
          (list-case
            (c-lookup (head (tail expr)) store)
            c-expr-runtime-error
            option_cell
            (c-expr-value (head (tail option_cell))))
          (if
            (symbol-eq (head expr) (quote :c-lt-expr))
            ((lambda left_result
               (if
                 (symbol-eq (head left_result) (quote :c-expr-value))
                 ((lambda right_result
                    (if
                      (symbol-eq (head right_result) (quote :c-expr-value))
                      (if
                        (c-is-int32 (head (tail left_result)))
                        (if
                          (c-is-int32 (head (tail right_result)))
                          (c-expr-value
                            (c-int32-lt
                              (head (tail left_result))
                              (head (tail right_result))))
                          c-expr-runtime-error)
                        c-expr-runtime-error)
                      (c-expr-nonvalue-result right_result)))
                  (c-eval-expr store (head (tail (tail expr)))))
                 (c-expr-nonvalue-result left_result)))
             (c-eval-expr store (head (tail expr))))
            (if
              (symbol-eq (head expr) (quote :c-add-expr))
              ((lambda left_result
                 (if
                   (symbol-eq (head left_result) (quote :c-expr-value))
                   ((lambda right_result
                      (if
                        (symbol-eq (head right_result) (quote :c-expr-value))
                        (if
                          (c-is-int32 (head (tail left_result)))
                          (if
                            (c-is-int32 (head (tail right_result)))
                            (c-int32-add
                              (head (tail left_result))
                              (head (tail right_result)))
                            c-expr-runtime-error)
                          c-expr-runtime-error)
                        (c-expr-nonvalue-result right_result)))
                    (c-eval-expr store (head (tail (tail expr)))))
                   (c-expr-nonvalue-result left_result)))
               (c-eval-expr store (head (tail expr))))
              c-expr-runtime-error)))))))

(def c-exec-stmt
  (lambda store
    (lambda stmt
      (if
        (symbol-eq (head stmt) (quote :c-assign-stmt))
        ((lambda expr_result
           (if
             (symbol-eq (head expr_result) (quote :c-expr-value))
             (c-stmt-normal
               (c-store-set
                 (head (tail stmt))
                 (head (tail expr_result))
                 store))
             (c-expr-result-to-stmt-nonvalue expr_result)))
         (c-eval-expr store (head (tail (tail stmt)))))
        (if
          (symbol-eq (head stmt) (quote :c-seq-stmt))
          ((lambda first_result
             (if
               (symbol-eq (head first_result) (quote :c-stmt-normal))
               (c-exec-stmt
                 (head (tail first_result))
                 (head (tail (tail stmt))))
               first_result))
           (c-exec-stmt store (head (tail stmt))))
          (if
            (symbol-eq (head stmt) (quote :c-if-stmt))
            ((lambda condition_result
               (if
                 (symbol-eq (head condition_result) (quote :c-expr-value))
                 (if
                   (c-value-has-type (head (tail condition_result)) c-type-bool)
                   (if
                     (head (tail condition_result))
                     (c-exec-stmt store (head (tail (tail stmt))))
                     (c-exec-stmt store (head (tail (tail (tail stmt))))))
                   c-stmt-runtime-error)
                 (c-expr-result-to-stmt-nonvalue condition_result)))
             (c-eval-expr store (head (tail stmt))))
            (if
              (symbol-eq (head stmt) (quote :c-return-stmt))
              ((lambda expr_result
                 (if
                   (symbol-eq (head expr_result) (quote :c-expr-value))
                   (c-stmt-return (head (tail expr_result)))
                   (c-expr-result-to-stmt-nonvalue expr_result)))
               (c-eval-expr store (head (tail stmt))))
              c-stmt-runtime-error)))))))

(def c-max-type-env
  (c-env-bind
    (quote b)
    c-type-int32
    (c-env-bind
      (quote a)
      c-type-int32
      c-empty-env)))

(def c-max-store
  (lambda a
    (lambda b
      (c-env-bind
        (quote b)
        b
        (c-env-bind
          (quote a)
          a
          c-empty-env)))))

(def c-max-body
  (c-if-stmt
    (c-lt-expr
      (c-var-expr (quote a))
      (c-var-expr (quote b)))
    (c-return-stmt (c-var-expr (quote b)))
    (c-return-stmt (c-var-expr (quote a)))))

(theorem c_eval_expr_deterministic
  (forall store
    (forall expr
      (forall left_result
        (forall right_result
          (implies
            (computes-to (c-eval-expr store expr) left_result)
            (implies
              (computes-to (c-eval-expr store expr) right_result)
              (computes-to left_result right_result)))))))
  (by
    (intro store)
    (intro expr)
    (intro left_result)
    (intro right_result)
    (intro right_eval)
    (calc
      left_result
      (==
        (c-eval-expr store expr)
        (by
          (exact (symm right_result))))
      (==
        right_result
        (by
          (exact right_eval))))))

(theorem c_exec_stmt_deterministic
  (forall store
    (forall stmt
      (forall left_result
        (forall right_result
          (implies
            (computes-to (c-exec-stmt store stmt) left_result)
            (implies
              (computes-to (c-exec-stmt store stmt) right_result)
              (computes-to left_result right_result)))))))
  (by
    (intro store)
    (intro stmt)
    (intro left_result)
    (intro right_result)
    (intro right_exec)
    (calc
      left_result
      (==
        (c-exec-stmt store stmt)
        (by
          (exact (symm right_result))))
      (==
        right_result
        (by
          (exact right_exec))))))

(theorem c_int32_zero_has_type
  (computes-to
    (c-value-has-type c-int32-zero c-type-int32)
    (quote :true))
  (by
    (eval 4096)))

(theorem c_int32_one_has_type
  (computes-to
    (c-value-has-type c-int32-one c-type-int32)
    (quote :true))
  (by
    (eval 4096)))

(theorem c_int32_two_has_type
  (computes-to
    (c-value-has-type c-int32-two c-type-int32)
    (quote :true))
  (by
    (eval 4096)))

(theorem c_int32_max_has_type
  (computes-to
    (c-value-has-type c-int32-max c-type-int32)
    (quote :true))
  (by
    (eval 4096)))

(theorem c_int32_zero_one_lt
  (computes-to
    (c-int32-lt c-int32-zero c-int32-one)
    (quote :true))
  (by
    (eval 8192)))

(theorem c_int32_one_zero_not_lt
  (computes-to
    (c-int32-lt c-int32-one c-int32-zero)
    (quote :false))
  (by
    (eval 8192)))

(theorem c_int32_one_one_add
  (computes-to
    (c-int32-add c-int32-one c-int32-one)
    (c-expr-value c-int32-two))
  (by
    (eval 4096)))

(theorem c_int32_max_one_add_overflows
  (computes-to
    (c-int32-add c-int32-max c-int32-one)
    (c-expr-ub c-ub-signed-overflow))
  (by
    (eval 4096)))

(theorem c_int32_expr_preserves_type
  (forall type_env (is-list type_env)
    (forall value
      (and
        (is-value value)
        (computes-to (c-is-int32 value) (quote :true)))
      (and
        (computes-to
          (c-has-type type_env (c-int32-expr value) c-type-int32)
          (quote :true))
        (computes-to
          (c-value-has-type value c-type-int32)
          (quote :true)))))
  (by
    (intro type_env)
    (intro value)
    (cases value value_is_value value_is_int32
      (by
        (split
          (by
            (have value_is_int32_bool
              (is-bool (c-is-int32 value))
              (by
                (left
                  (by
                    (exact value_is_int32))))
              (by
                (have true_is_true
                  (computes-to (quote :true) (quote :true))
                  (by
                    (eval))
                  (by
                    (calc
                      (c-has-type type_env (c-int32-expr value) c-type-int32)
                      (==
                        (and
                          (symbol-eq c-type-int32 c-type-int32)
                          (c-is-int32 value))
                        (by
                          (eval)))
                      (==
                        (and
                          (quote :true)
                          (c-is-int32 value))
                        (by
                          (eval)))
                      (==
                        (c-is-int32 value)
                        (by
                          (apply and_true_left
                            (quote :true)
                            (c-is-int32 value))))
                      (==
                        (quote :true)
                        (by
                          (exact value_is_int32)))))))))
          (by
            (calc
              (c-value-has-type value c-type-int32)
              (==
                (c-is-int32 value)
                (by
                  (eval)))
              (==
                (quote :true)
                (by
                  (exact value_is_int32))))))))))

(theorem c_lt_literal_zero_one_eval
  (computes-to
    (c-eval-expr
      c-empty-env
      (c-lt-expr (c-int32-expr c-int32-zero) (c-int32-expr c-int32-one)))
    (c-expr-value (quote :true)))
  (by
    (eval 4096)))

(theorem c_lt_literal_one_zero_eval
  (computes-to
    (c-eval-expr
      c-empty-env
      (c-lt-expr (c-int32-expr c-int32-one) (c-int32-expr c-int32-zero)))
    (c-expr-value (quote :false)))
  (by
    (eval 4096)))

(theorem c_add_literal_one_one_has_type
  (computes-to
    (c-has-type
      c-empty-env
      (c-add-expr (c-int32-expr c-int32-one) (c-int32-expr c-int32-one))
      c-type-int32)
    (quote :true))
  (by
    (eval 4096)))

(theorem c_add_literal_max_one_has_type
  (computes-to
    (c-has-type
      c-empty-env
      (c-add-expr (c-int32-expr c-int32-max) (c-int32-expr c-int32-one))
      c-type-int32)
    (quote :true))
  (by
    (eval 4096)))

(theorem c_add_literal_one_one_eval
  (computes-to
    (c-eval-expr
      c-empty-env
      (c-add-expr (c-int32-expr c-int32-one) (c-int32-expr c-int32-one)))
    (c-expr-value c-int32-two))
  (by
    (eval 4096)))

(theorem c_add_literal_max_one_ub
  (computes-to
    (c-eval-expr
      c-empty-env
      (c-add-expr (c-int32-expr c-int32-max) (c-int32-expr c-int32-one)))
    (c-expr-ub c-ub-signed-overflow))
  (by
    (eval 4096)))

(theorem c_return_add_overflow_ub
  (computes-to
    (c-exec-stmt
      c-empty-env
      (c-return-stmt
        (c-add-expr (c-int32-expr c-int32-max) (c-int32-expr c-int32-one))))
    (c-stmt-ub c-ub-signed-overflow))
  (by
    (eval 4096)))

(theorem c_max_body_well_typed
  (computes-to
    (c-stmt-well-typed c-max-type-env c-max-body c-type-int32)
    (quote :true))
  (by
    (eval 4096)))

(theorem c_max_zero_one_returns_one
  (computes-to
    (c-exec-stmt (c-max-store c-int32-zero c-int32-one) c-max-body)
    (c-stmt-return c-int32-one))
  (by
    (eval 8192)))

(theorem c_max_one_zero_returns_one
  (computes-to
    (c-exec-stmt (c-max-store c-int32-one c-int32-zero) c-max-body)
    (c-stmt-return c-int32-one))
  (by
    (eval 8192)))
