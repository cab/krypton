# expect: ok
(def identity (fn [x] x))
(def multi_param (fn [a b c] (+ a (+ b c))))
(def higher_order (fn [f x] (f x)))
(def closure (fn [x] (fn [y] (+ x y))))
