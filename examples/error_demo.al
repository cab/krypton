; This file contains intentional errors to demonstrate ariadne error reporting

; Missing closing paren
(type Point (struct [x Int] [y Int)

; Invalid token
(def foo [x] -> Int
  (+ x 2@3))
