; Nat definitions for the standard prelude.
; Natural numbers are unary lists of the prelude `unit` symbol.

(def zero nil)

(def succ
  (lambda nat
    (cons (quote unit) nat)))

(def is-nat-value
  (lambda value
    (if
      (is-list-value value)
      (list-case value
        (quote :true)
        cell
        (if
          (symbol-eq (head cell) (quote unit))
          (is-nat-value (tail cell))
          (quote :false)))
      (quote :false))))

(def is-zero
  (lambda nat
    (null nat)))

(def pred
  (lambda nat
    (list-case nat
      nil
      cell
      (tail cell))))

(def range
  (lambda count
    (list-case count
      nil
      cell
      (snoc
        (range (tail cell))
        (tail cell)))))

(def add
  (lambda left
    (lambda right
      (append left right))))

(def sub
  (lambda left
    (lambda right
      (list-case right
        left
        right_cell
        (list-case left
          nil
          left_cell
          (sub (tail left_cell) (tail right_cell)))))))

(def mul
  (lambda left
    (lambda right
      (list-case left
        nil
        cell
        (add right (mul (tail cell) right))))))

(def nat-eq
  (lambda left
    (lambda right
      (list-case left
        (is-zero right)
        left_cell
        (list-case right
          (quote :false)
          right_cell
          (nat-eq (tail left_cell) (tail right_cell)))))))

(def nat-le
  (lambda left
    (lambda right
      (list-case left
        (quote :true)
        left_cell
        (list-case right
          (quote :false)
          right_cell
          (nat-le (tail left_cell) (tail right_cell)))))))

(def nat-lt
  (lambda left
    (lambda right
      (list-case left
        (list-case right
          (quote :false)
          right_cell
          (quote :true))
        left_cell
        (list-case right
          (quote :false)
          right_cell
          (nat-lt (tail left_cell) (tail right_cell)))))))
