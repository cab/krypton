# expect: ok
(type Point (record (x Int) (y Int)))

(type Shape (| (Circle Int) (Rect Int Int)))

(def area (fn [s]
  (match s
    ((Circle r) (* r r))
    ((Rect w h) (* w h)))))

(def origin (fn [] (let x 0)))

(def main (fn []
  (do
    (let p (origin))
    (let s (Circle 5))
    (area s))))
