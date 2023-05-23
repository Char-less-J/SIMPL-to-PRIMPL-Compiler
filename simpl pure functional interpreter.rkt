#lang racket
;; AST types
(struct skip ())
(struct seq (s1 s2))
(struct print (s))
;; Interpreter result
(struct result (state output))
;; Monad operations
(define (>>= x y) (lambda (output)
                    (let ([z (x output)]) ((y (result-state z))
                                           (result-output z)))))
(lambda (output)
  ((y (result-state (x output)))
   (result-output (x output))))
;; z is new output-state pair produced by function x applied to output
;; (y (result-state z)) operator y applied to state produces a new function
;; (result-output z) new function applied to new output to get final output
(seq s1 s2)
is same as:
(>>= (interp s1 (+ state 1))
                      (lambda (x) (interp s2 (+ x 1))))
is same as:
(lambda (output)
       (let ([z ((interp s1 (+ state 1)) output)])
       ((interp s2 (+ (result-state z) 1))
         (result-output z))
         ))


(define (>> x y) (>>= x (lambda (_) y)))
(define (return state) (lambda (output) (result state output)))
;; Writing to output
(define (put-str s) (lambda (output)
                      (result 0 (string-append output s))))
;; Interpretation function for statements
(define (interp stmt state)
  (match stmt
    [(skip) (return state)]
    [(seq s1 s2) (>>= (interp s1 (+ state 1))
                      (lambda (x) (interp s2 (+ x 1))))]
    [(print s) (>> (put-str (number->string state))
                   (>> (put-str s) (return state)))]))
;; Interprets a statement, and prints the resulting state and produced output
(define (interp-show stmt)
  (define res ((interp stmt 0) ""))
  (printf "output: ~a~nstate: ~a~n" (result-output res) (result-state res)))