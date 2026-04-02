(lambda b
  (pi A type
    (pi t (var A)
      (pi f (var A)
        (var A))))
  (lambda A type
    (lambda t (var A)
      (lambda f (var A)
        (app
          (app
            (app (var b) (var A))
            (var t))
          (var f))))))
