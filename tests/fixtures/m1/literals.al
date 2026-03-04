# expect: ok
(def int_lit (fn [] 42))
(def neg_int (fn [] (- 0 1)))
(def float_lit (fn [] 3.14))
(def bool_true (fn [] true))
(def bool_false (fn [] false))
(def string_lit (fn [] "hello world"))
(def unit_lit (fn [] (tuple)))
