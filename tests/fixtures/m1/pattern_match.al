# expect: ok
(def match_wildcard (fn [x]
  (match x
    (_ 0))))

(def match_literal (fn [x]
  (match x
    (1 "one")
    (2 "two")
    (_ "other"))))

(def match_constructor (fn [opt]
  (match opt
    ((None) 0)
    ((Some x) x))))

(def match_tuple (fn [pair]
  (match pair
    ((tuple a b) (+ a b)))))
