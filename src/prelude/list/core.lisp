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

(def snoc
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
       (lambda value
         (list-case list
           (cons value nil)
           cell
           (cons
             (head cell)
             ((self (tail cell)) value))))))))

(def concat
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
     (lambda lists
       (list-case lists
         nil
        cell
        ((append (head cell))
         (self (tail cell))))))))

(def length
  (lambda list
    (list-case list
      nil
      cell
      (cons
        (quote unit)
        (length (tail cell))))))

(def take
  (lambda count
    (lambda list
      (list-case count
        nil
        count_cell
        (list-case list
          nil
          list_cell
          (cons
            (head list_cell)
            (take (tail count_cell) (tail list_cell))))))))

(def drop
  (lambda count
    (lambda list
      (list-case count
        list
        count_cell
        (list-case list
          nil
          list_cell
          (drop (tail count_cell) (tail list_cell)))))))

(def split-at
  (lambda count
    (lambda list
      (cons
        (take count list)
        (cons (drop count list) nil)))))

(def nth
  (lambda index
    (lambda list
      (list-case index
        (list-case list
          (quote :none)
          list_cell
          (some (head list_cell)))
        index_cell
        (list-case list
          (quote :none)
          list_cell
          (nth (tail index_cell) (tail list_cell)))))))

(def replicate
  (lambda count
    (lambda value
      (list-case count
        nil
        count_cell
        (cons
          value
          (replicate (tail count_cell) value))))))

(def intersperse
  (lambda separator
    (lambda list
      (list-case list
        nil
        cell
        (list-case (tail cell)
          (cons (head cell) nil)
          tail_cell
          (cons
            (head cell)
            (cons
              separator
              (intersperse separator (tail cell)))))))))

(def intercalate
  (lambda separator
    (lambda lists
      (list-case lists
        nil
        cell
        (list-case (tail cell)
          (head cell)
          tail_cell
          (append
            (head cell)
            (append
              separator
              (intercalate separator (tail cell)))))))))

(def map
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
     (lambda function
       (lambda list
         (list-case list
           nil
           cell
           (cons
             (function (head cell))
             ((self function) (tail cell)))))))))

(def concat-map
  (lambda function
    (lambda list
      (list-case list
        nil
        cell
        (append
          (function (head cell))
          (concat-map function (tail cell)))))))

(def fold-right
  (lambda function
    (lambda initial
      (lambda list
        (list-case list
          initial
          cell
          (function
            (head cell)
            (fold-right function initial (tail cell))))))))

(def fold-left
  (lambda function
    (lambda initial
      (lambda list
        (list-case list
          initial
          cell
          (fold-left
            function
            (function initial (head cell))
            (tail cell)))))))

(def zip
  (lambda left
    (lambda right
      (list-case left
        nil
        left_cell
        (list-case right
          nil
          right_cell
          (cons
            (cons
              (head left_cell)
              (cons (head right_cell) nil))
            (zip
              (tail left_cell)
              (tail right_cell))))))))

(def unzip
  (lambda pairs
    (list-case pairs
      (cons nil (cons nil nil))
      cell
      (cons
        (cons
          (head (head cell))
          (head (unzip (tail cell))))
        (cons
          (cons
            (head (tail (head cell)))
            (head (tail (unzip (tail cell)))))
          nil)))))

(def zip-with
  (lambda function
    (lambda left
      (lambda right
        (list-case left
          nil
          left_cell
          (list-case right
            nil
            right_cell
            (cons
              (function (head left_cell) (head right_cell))
              (zip-with
                function
                (tail left_cell)
                (tail right_cell)))))))))

(def filter
  (lambda predicate
    (lambda list
      (list-case list
        nil
        cell
        (if
          (predicate (head cell))
          (cons
            (head cell)
            (filter predicate (tail cell)))
          (filter predicate (tail cell)))))))

(def partition
  (lambda predicate
    (lambda list
      (list-case list
        (cons nil (cons nil nil))
        cell
        (if
          (predicate (head cell))
          (cons
            (cons
              (head cell)
              (head (partition predicate (tail cell))))
            (cons
              (head (tail (partition predicate (tail cell))))
              nil))
          (cons
            (head (partition predicate (tail cell)))
            (cons
              (cons
                (head cell)
                (head (tail (partition predicate (tail cell)))))
              nil)))))))

(def any
  (lambda predicate
    (lambda list
      (list-case list
        (quote :false)
        cell
        (if
          (predicate (head cell))
          (quote :true)
          (any predicate (tail cell)))))))

(def all
  (lambda predicate
    (lambda list
      (list-case list
        (quote :true)
        cell
        (if
          (predicate (head cell))
          (all predicate (tail cell))
          (quote :false))))))

(def find
  (lambda predicate
    (lambda list
      (list-case list
        (quote :none)
        cell
        (if
          (predicate (head cell))
          (some (head cell))
          (find predicate (tail cell)))))))

(def is-symbol
  (lambda value
    (symbol-eq (value-kind value) (quote :symbol))))

(def is-lambda
  (lambda value
    (symbol-eq (value-kind value) (quote :lambda))))

(def is-list-value
  (lambda value
    (symbol-eq (value-kind value) (quote :list))))

(def all-lists
  (lambda lists
    (list-case lists
      (quote :true)
      cell
      (if
        (is-list-value (head cell))
        (all-lists (tail cell))
        (quote :false)))))

(def none
  (quote :none))

(def some
  (lambda value
    (cons
      (quote :some)
      (cons value nil))))

(def is-none
  (lambda option
    (symbol-eq option (quote :none))))

(def is-some
  (lambda option
    (if
      (is-list-value option)
      (list-case option
        (quote :false)
        option_cell
        (if
          (symbol-eq (head option_cell) (quote :some))
          (is-singleton (tail option_cell))
          (quote :false)))
      (quote :false))))

(def value-eq
  (lambda left
    (lambda right
      (if
        (is-lambda left)
        (error 0)
        (if
          (is-lambda right)
          (error 0)
          (if
            (is-symbol left)
            (symbol-eq left right)
            (if
              (is-symbol right)
              (quote :false)
              (list-case left
                (list-case right
                  (quote :true)
                  right_cell
                  (quote :false))
                left_cell
                (list-case right
                  (quote :false)
                  right_cell
                  (if
                    (value-eq (head left_cell) (head right_cell))
                    (value-eq (tail left_cell) (tail right_cell))
                    (quote :false)))))))))))

(def value-eq-comparable
  (lambda value
    (if
      (is-lambda value)
      (quote :false)
      (if
        (is-symbol value)
        (quote :true)
        (list-case value
          (quote :true)
          cell
          (if
            (value-eq-comparable (head cell))
            (value-eq-comparable (tail cell))
            (quote :false)))))))

(def member
  (lambda value
    (lambda list
      (list-case list
        (quote :false)
        cell
        (if
          (value-eq value (head cell))
          (quote :true)
          (member value (tail cell)))))))

(def elem-index
  (lambda value
    (lambda list
      (list-case list
        none
        cell
        (if
          (value-eq value (head cell))
          (some nil)
          ((lambda tail_result
             (if
               (is-some tail_result)
               (some
                 (cons
                   (quote unit)
                   (head (tail tail_result))))
               none))
           (elem-index value (tail cell))))))))

(def last
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
       (list-case list
         (error 0)
         cell
         (list-case (tail cell)
           (head cell)
           rest_cell
           (self (tail cell))))))))

(def init
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
       (list-case list
         (error 0)
         cell
         (list-case (tail cell)
           nil
           rest_cell
           (cons
             (head cell)
             (self (tail cell)))))))))

(def null
  (lambda list
    (list-case list
      (quote :true)
      cell
      (quote :false))))

(def is-singleton
  (lambda list
    (list-case list
      (quote :false)
      cell
      (list-case (tail cell)
        (quote :true)
        rest_cell
        (quote :false)))))
