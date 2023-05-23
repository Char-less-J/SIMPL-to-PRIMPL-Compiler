#lang racket
(require test-engine/racket-tests)
;;#########################################################################
;;#################### Structs of language ################################
;;#########################################################################
(struct bin (op fst snd) #:transparent) ; op is a symbol; fst, snd are ASTs.
(struct fun (param body) #:transparent) ; param is a symbol; body is an AST.
(struct app (fn arg) #:transparent) ; fn and arg are ASTs.
;; An AST is a (union bin fun app).
;;######### Structs To implement #######
(struct seq (fst snd) #:transparent)

(struct newbox (exp) #:transparent)
(struct openbox (exp) #:transparent)
(struct setbox (bexp vexp) #:transparent)


;;#########################################################################
;;#################### Post interpretation ################################
;;#########################################################################
(struct addr (name address) #:transparent)
;; An address is a (addr n v), where n is a symbol and v is a value.
;; An environment (env) is a list of addresses.
(struct room (address val) #:transparent)
;;a store is a list of room, location-value pairs


(struct closure (var body envt) #:transparent)
;; A closure is a (closure v bdy env), where
;; v is a symbol, bdy is an AST, and env is a environment.
;; A value is a (union number closure).

(struct result (val newstore) #:transparent)
;;#########################################################################
;;################ Functions for Interpretation ###########################
;;#########################################################################
;; parse: sexp -> AST
(define (parse sx)
  (match sx
    [`(with ((,nm ,nmd)) ,bdy) (app (fun nm (parse bdy)) (parse nmd))]
    [`(+ ,x ,y) (bin '+ (parse x) (parse y))]
    [`(* ,x ,y) (bin '* (parse x) (parse y))]
    [`(- ,x ,y) (bin '- (parse x) (parse y))]
    [`(/ ,x ,y) (bin '/ (parse x) (parse y))]
    [`(fun (,x) ,bdy) (fun x (parse bdy))]
    [`(seq ,fst ,snd) (seq (parse fst) (parse snd))]
    [`(setbox ,var ,newval) (setbox (parse var) (parse newval))]
    [`(box ,exp) (newbox (parse exp))]
    [`(unbox ,exp) (openbox (parse exp))]
    [`(,f ,x) (app (parse f) (parse x))]
    [x x]))

; op-trans: symbol -> (number number -> number)
; converts symbolic representation of arithmetic function to actual Racket function
(define (op-trans op)
  (match op
    ['+ +]
    ['* *]
    ['- -]
    ['/ /]))

;; find-addr: symbol 
(define (find-addr name addrs)
  (cond
    [(empty? addrs) (error 'interp "unbound ~a" name)]
    [(symbol=? name (addr-name (car addrs))) (addr-address (car addrs))]
    [else (find-addr name (cdr addrs))]))

;; lookup: symbol store -> value
;; looks up a substitution in an environment (topmost one)
(define (fetch location store)
  (cond
    [(empty? store) (error 'interp "unbound ~a" location)]
    [(= location (room-address (car store))) (room-val (car store))]
    [else (fetch location (cdr store))]))

;; name-to-val
(define (name-to-val name addrs store)
  (fetch (find-addr name addrs) store))

(define (newloc store)
  (define (newloc-h lst acc)
    (cond [(empty? lst) acc]
          [true (newloc-h (cdr lst) (add1 acc))]))
  (newloc-h store 0))
;; interp: AST env -> (result value newstore)
(define (interp ast env store)
  (match ast
    [(fun v bdy) (result (closure v bdy env) store)]
    [(app fun-exp arg-exp)
       (match (interp fun-exp env store)
         [(result (closure v bdy cl-env) newstore)
          (match (interp arg-exp env newstore)
            [(result arg-val nnewstore)
             (interp bdy
                     (cons (addr v (newloc nnewstore)) cl-env)
                     (cons (room (newloc nnewstore) arg-val) nnewstore)
                     )])])]
    [(bin op x y)
     (result ((op-trans op) (result-val(interp x env store))
                            (result-val(interp y env (result-newstore(interp x env store)))))
             (result-newstore (interp y env (result-newstore(interp x env store)))))]
    [(newbox expr)
     (match (interp expr env store)
       [(result newval newstore)
        (result (newloc newstore)
                (cons (room (newloc newstore) newval)
                      newstore))])]
    [(openbox expr)
     (match (interp expr env store)
       [(result address newstore)
        (result (fetch address newstore)
                newstore)])]
    [(setbox addr newval)
     (match (interp addr env store)
       [(result addr-evaled newstore-1)
        (match (interp newval env newstore-1)
          [(result newval-2 newstore-2)
           (result (void 1) (cons (room addr-evaled
                                        newval-2)
                                  newstore-2))])])]
    [(seq first second)
     (interp second env (result-newstore(interp first env store)))]
    [x (cond
         [(number? x) (result x store)]
         [true (result (name-to-val x env store) store)])]
    ))

;;#########################################################################
;;################ Testing ###########################
;;#########################################################################
#|
(define exp '(+ 3 5))
(define exp2 '(with ((x 0))
                   (+ (seq (setbox x 5) x)
                      (seq (setbox x 6) x))))
(define exp3 '(with ((x (box 15)))
                    (with ((y (box 0)))
                    (seq (setbox x 9)
                         (seq (setbox (box(unbox(box 9))) 28)
                              (seq (setbox x (+ (unbox x)(unbox (box(unbox(box 28))))))
                                   (unbox x)))))))
(define exp4 '(with ((x 9)) x))
(define exp5 '(unbox (box (with ((x (box 0)))
                                (seq (setbox x 99)
                                     (+ 2 (unbox x)))))))
(define exp6 '(with ((x (box 0)))
                    (seq (setbox x 99)
                         (+ 2 (unbox x)))))
(define boxes '(with ((x (box(box(box 0)))))
                     (seq (setbox x (box(box(box 22))))
                          (+ 9 (unbox(unbox(unbox(unbox x))))))))
;(parse '(+ 3 5))
;(parse exp3)
(result-val (interp (result-val(interp (parse boxes) empty empty)) empty empty))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define x (box 9))
(set-box! (box (unbox (box 9))) 8)
(unbox x)
(let ((x (box 0))) (begin (set-box! x 999)
                          (+ 2 (unbox x))))

(let ((x (box(box(box(box(box 98))))))(y (box 77)))
        (begin (set-box! x 9)
               (set-box! (box(unbox(box(unbox(box 98))))) 28)
               (set-box! x (+ (unbox x)(unbox (box(unbox(box(unbox(box 98))))))))
               (unbox x)))
;|#
;(interp (parse '(unbox (setbox (box (+ (* 123 321) 786)) 1980))) empty empty)
;second case invalid
;(interp (parse '(setbox (box (+ (* 123 321) 786)) 1980)) empty empty)
;(interp (parse '(with ((x (box (+ (* 123 321) 786)))) (setbox x 1980))) empty empty)
;(interp (parse '(with ((x (box (+ (* 123 321) 786)))) (seq (setbox x 1980) (unbox x)))) empty empty)
;(interp (parse '(with ((f (fun (x) (setbox x 555)))) (with ((x (box 1328))) (seq (f x) (unbox x))))) empty empty)
;(interp (parse '(fun (x) (setbox x 555))) empty empty)
;(interp (parse '(with ((f (fun (x) (setbox x 555)))) (f (box 1980)))) empty empty)
; completely inadequate tests
;(let [(x 5)]
;  (begin
;    (set! x 6)
;    x))
;(interp (parse '(with ((x 7)) (+ (seq (set x 0) x) (+ x 5) ))) empty empty)
;(interp (parse '(with ((x 7)) (+  (+ x 7) (+ x 5) ))) empty empty)
;(interp (parse '(with ((x 2)) (seq (set x 6) (+ x 2)))) empty empty)
;(interp (parse '(with ((f (fun (x) (set x 5)))) (f 10))) empty empty)
;(interp (parse '(with ((apple 2)) (with ((orange 4)) (* apple orange)))) empty empty)
;(interp (parse '(with ((x (* 2 2))) (+ x 3))) empty empty)
;(interp (parse '(with ((f (fun (x) (+ x 1)))) (+ (f 3) 1))) empty empty)