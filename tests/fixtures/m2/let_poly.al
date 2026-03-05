# expect: ok
(def main (fn [] (do (let id (fn [x] x)) (let a (id 1)) (let b (id true)) b)))
