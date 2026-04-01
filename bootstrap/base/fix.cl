(lambda f
  (app
    (lambda x1
      (app
        (var f)
        (lambda y1
          (app
            (app (var x1) (var x1))
            (var y1)))))
    (lambda x2
      (app
        (var f)
        (lambda y2
          (app
            (app (var x2) (var x2))
            (var y2)))))))
