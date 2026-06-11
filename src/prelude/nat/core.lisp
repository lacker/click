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

(def min
  (lambda left
    (lambda right
      (list-case left
        nil
        left_cell
        (list-case right
          nil
          right_cell
          (succ (min (tail left_cell) (tail right_cell))))))))

(def max
  (lambda left
    (lambda right
      (list-case left
        right
        left_cell
        (list-case right
          left
          right_cell
          (succ (max (tail left_cell) (tail right_cell))))))))

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

(theorem succ_congr
  (forall left
    (forall right
      (implies
        (computes-to left right)
        (computes-to (succ left) (succ right)))))
  (by
    (intro left)
    (intro right)
    (simpa only right)))

(theorem pred_congr
  (forall left
    (forall right
      (implies
        (computes-to left right)
        (computes-to (pred left) (pred right)))))
  (by
    (intro left)
    (intro right)
    (simpa only right)))

(theorem add_congr_left
  (forall left
    (forall right
      (implies
        (computes-to left right)
        (forall addend
          (computes-to
            (add left addend)
            (add right addend))))))
  (by
    (intro left)
    (intro right)
    (intro addend)
    (simpa only right)))

(theorem add_congr_right
  (forall addend
    (forall left
      (forall right
        (implies
          (computes-to left right)
          (computes-to
            (add addend left)
            (add addend right))))))
  (by
    (intro addend)
    (intro left)
    (intro right)
    (simpa only right)))

(theorem add_congr
  (forall left
    (forall right
      (implies
        (computes-to left right)
        (forall left_addend
          (forall right_addend
            (implies
              (computes-to left_addend right_addend)
              (computes-to
                (add left left_addend)
                (add right right_addend))))))))
  (by
    (intro left)
    (intro right)
    (intro left_addend)
    (intro right_addend)
    (simpa only right right_addend)))

(theorem sub_congr_left
  (forall left
    (forall right
      (implies
        (computes-to left right)
        (forall subtrahend
          (computes-to
            (sub left subtrahend)
            (sub right subtrahend))))))
  (by
    (intro left)
    (intro right)
    (intro subtrahend)
    (simpa only right)))

(theorem sub_congr_right
  (forall minuend
    (forall left
      (forall right
        (implies
          (computes-to left right)
          (computes-to
            (sub minuend left)
            (sub minuend right))))))
  (by
    (intro minuend)
    (intro left)
    (intro right)
    (simpa only right)))

(theorem sub_congr
  (forall left
    (forall right
      (implies
        (computes-to left right)
        (forall left_subtrahend
          (forall right_subtrahend
            (implies
              (computes-to left_subtrahend right_subtrahend)
              (computes-to
                (sub left left_subtrahend)
                (sub right right_subtrahend))))))))
  (by
    (intro left)
    (intro right)
    (intro left_subtrahend)
    (intro right_subtrahend)
    (simpa only right right_subtrahend)))

(theorem mul_congr_left
  (forall left
    (forall right
      (implies
        (computes-to left right)
        (forall factor
          (computes-to
            (mul left factor)
            (mul right factor))))))
  (by
    (intro left)
    (intro right)
    (intro factor)
    (simpa only right)))

(theorem mul_congr_right
  (forall factor
    (forall left
      (forall right
        (implies
          (computes-to left right)
          (computes-to
            (mul factor left)
            (mul factor right))))))
  (by
    (intro factor)
    (intro left)
    (intro right)
    (simpa only right)))

(theorem mul_congr
  (forall left
    (forall right
      (implies
        (computes-to left right)
        (forall left_factor
          (forall right_factor
            (implies
              (computes-to left_factor right_factor)
              (computes-to
                (mul left left_factor)
                (mul right right_factor))))))))
  (by
    (intro left)
    (intro right)
    (intro left_factor)
    (intro right_factor)
    (simpa only right right_factor)))

(theorem nat_eq_congr_left
  (forall left
    (forall right
      (implies
        (computes-to left right)
        (forall compared
          (computes-to
            (nat-eq left compared)
            (nat-eq right compared))))))
  (by
    (intro left)
    (intro right)
    (intro compared)
    (simpa only right)))

(theorem nat_eq_congr_right
  (forall compared
    (forall left
      (forall right
        (implies
          (computes-to left right)
          (computes-to
            (nat-eq compared left)
            (nat-eq compared right))))))
  (by
    (intro compared)
    (intro left)
    (intro right)
    (simpa only right)))

(theorem nat_eq_congr
  (forall left
    (forall right
      (implies
        (computes-to left right)
        (forall left_compared
          (forall right_compared
            (implies
              (computes-to left_compared right_compared)
              (computes-to
                (nat-eq left left_compared)
                (nat-eq right right_compared))))))))
  (by
    (intro left)
    (intro right)
    (intro left_compared)
    (intro right_compared)
    (simpa only right right_compared)))

(theorem nat_le_congr_left
  (forall left
    (forall right
      (implies
        (computes-to left right)
        (forall upper
          (computes-to
            (nat-le left upper)
            (nat-le right upper))))))
  (by
    (intro left)
    (intro right)
    (intro upper)
    (simpa only right)))

(theorem nat_le_congr_right
  (forall lower
    (forall left
      (forall right
        (implies
          (computes-to left right)
          (computes-to
            (nat-le lower left)
            (nat-le lower right))))))
  (by
    (intro lower)
    (intro left)
    (intro right)
    (simpa only right)))

(theorem nat_le_congr
  (forall left
    (forall right
      (implies
        (computes-to left right)
        (forall left_upper
          (forall right_upper
            (implies
              (computes-to left_upper right_upper)
              (computes-to
                (nat-le left left_upper)
                (nat-le right right_upper))))))))
  (by
    (intro left)
    (intro right)
    (intro left_upper)
    (intro right_upper)
    (simpa only right right_upper)))

(theorem nat_lt_congr_left
  (forall left
    (forall right
      (implies
        (computes-to left right)
        (forall upper
          (computes-to
            (nat-lt left upper)
            (nat-lt right upper))))))
  (by
    (intro left)
    (intro right)
    (intro upper)
    (simpa only right)))

(theorem nat_lt_congr_right
  (forall lower
    (forall left
      (forall right
        (implies
          (computes-to left right)
          (computes-to
            (nat-lt lower left)
            (nat-lt lower right))))))
  (by
    (intro lower)
    (intro left)
    (intro right)
    (simpa only right)))

(theorem nat_lt_congr
  (forall left
    (forall right
      (implies
        (computes-to left right)
        (forall left_upper
          (forall right_upper
            (implies
              (computes-to left_upper right_upper)
              (computes-to
                (nat-lt left left_upper)
                (nat-lt right right_upper))))))))
  (by
    (intro left)
    (intro right)
    (intro left_upper)
    (intro right_upper)
    (simpa only right right_upper)))
