; A tiny C0 language model.
;
; This is intentionally a small executable model, not a parser for real C.
; C syntax, typing, and semantics are represented as ordinary Click values and
; computations so the existing kernel can prove facts about them.

(def c-type-int32
  (quote :c-type-int32))

(def c-type-bool
  (quote :c-type-bool))

(def c-width-1
  (cons (quote unit) nil))

(def c-width-2
  (append c-width-1 c-width-1))

(def c-width-4
  (append c-width-2 c-width-2))

(def c-width-8
  (append c-width-4 c-width-4))

(def c-width-16
  (append c-width-8 c-width-8))

(def c-int32-width
  (append c-width-16 c-width-16))

(def c-int31-width
  (tail c-int32-width))

(def c-is-bit
  (lambda value
    (or
      (symbol-eq value (quote :true))
      (symbol-eq value (quote :false)))))

(def c-is-bit-list32
  (lambda bits
    (and
      (nat-eq (length bits) c-int32-width)
      (all c-is-bit bits))))

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
            (c-is-bit-list32 (head (tail cell))))))
      (quote :false))))

(def c-int32-zero-bits
  (replicate c-int32-width (quote :false)))

(def c-int32-one-bits
  (append
    (replicate c-int31-width (quote :false))
    (cons (quote :true) nil)))

(def c-int32-zero
  (c-int32 c-int32-zero-bits))

(def c-int32-one
  (c-int32 c-int32-one-bits))

(def c-bit-eq
  (lambda left
    (lambda right
      (if left
        right
        (not right)))))

(def c-bit-lt
  (lambda left
    (lambda right
      (if left
        (quote :false)
        right))))

(def c-uint-bits-lt
  (lambda left_bits
    (lambda right_bits
      (list-case left_bits
        (quote :false)
        left_cell
        (list-case right_bits
          (quote :false)
          right_cell
          (if
            (c-bit-eq (head left_cell) (head right_cell))
            (c-uint-bits-lt (tail left_cell) (tail right_cell))
            (c-bit-lt (head left_cell) (head right_cell))))))))

(def c-int32-lt-bits
  (lambda left_bits
    (lambda right_bits
      (if
        (head left_bits)
        (if
          (head right_bits)
          (c-uint-bits-lt left_bits right_bits)
          (quote :true))
        (if
          (head right_bits)
          (quote :false)
          (c-uint-bits-lt left_bits right_bits))))))

(def c-int32-lt-raw
  (lambda left
    (lambda right
      (c-int32-lt-bits
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

(def c-expr-runtime-error
  (cons (quote :c-expr-runtime-error) nil))

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

(def c-stmt-runtime-error
  (cons (quote :c-stmt-runtime-error) nil))

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
              (quote :false))))))))

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
                      c-expr-runtime-error))
                  (c-eval-expr store (head (tail (tail expr)))))
                 c-expr-runtime-error))
             (c-eval-expr store (head (tail expr))))
            c-expr-runtime-error))))))

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
             c-stmt-runtime-error))
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
                 c-stmt-runtime-error))
             (c-eval-expr store (head (tail stmt))))
            (if
              (symbol-eq (head stmt) (quote :c-return-stmt))
              ((lambda expr_result
                 (if
                   (symbol-eq (head expr_result) (quote :c-expr-value))
                   (c-stmt-return (head (tail expr_result)))
                   c-stmt-runtime-error))
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
    (eval 32768)))

(theorem c_lt_literal_one_zero_eval
  (computes-to
    (c-eval-expr
      c-empty-env
      (c-lt-expr (c-int32-expr c-int32-one) (c-int32-expr c-int32-zero)))
    (c-expr-value (quote :false)))
  (by
    (eval 32768)))

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
    (eval 65536)))

(theorem c_max_one_zero_returns_one
  (computes-to
    (c-exec-stmt (c-max-store c-int32-one c-int32-zero) c-max-body)
    (c-stmt-return c-int32-one))
  (by
    (eval 65536)))
