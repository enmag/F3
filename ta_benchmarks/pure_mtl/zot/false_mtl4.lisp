(asdf:operate 'asdf:load-op 'ap-zot)

                                        ;change to 'bezot to use a bi-infinite time domain
(asdf:operate 'asdf:load-op 'ezot)

(use-package :trio-utils)
(use-package :ap-zot)


                                        ; this is the time bound for zot
(defvar h 1)
(defvar k 1)

;; THEOREM: ! ( G [0,3] (F [0,1] a));
(defvar mtl `(not (box 0 3 (diamond 0 1 a))))

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
