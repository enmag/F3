(asdf:operate 'asdf:load-op 'ap-zot)

(asdf:operate 'asdf:load-op 'ezot) ; change to 'bezot to use a bi-infinite time domain

(use-package :trio-utils)
(use-package :ap-zot)

(defvar h 1)
(defvar k 1)

;; THEOREM: G ((F[0,31] a) -> (F[0,30] a))
(defvar mtl `(alw (impl (diamond 0 31 a) (diamond 0 30 a))))

(setf mtl (normalize (basicize mtl))) ; putting the formulas in normal form

(defvar rho (compute-granularity `(mtl))) ; computing the granularity (r_\phi, R_\phi)

(defvar delta (/ (nth-divisor h (car rho)) (* k (cadr rho)))) ; computing delta

(defvar mtl-u (under-approximation mtl delta)) ; under-approximation of MTL property

(setf mtl-u `(alw ,mtl-u))

(defvar phi- `(not ,mtl-u))

(format t "~%Found: ~S~%"
        (loop for bound from 2 do
              (let ((res
                     (ezot::zot bound `(next ,phi-))))
                (when res (return (cons bound "IS FALSE"))
                      )))
        )
