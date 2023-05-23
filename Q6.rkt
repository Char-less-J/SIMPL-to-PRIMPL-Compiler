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
(struct set (var newval) #:transparent)

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
    [`(,f ,x) (app (parse f) (parse x))]
    [`(seq ,fst ,snd) (seq (parse fst) (parse snd))]
    [`(set ,var ,newval) (set (parse var) (parse newval))]
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
    [(empty? addrs) (error 'interp "Invalid Name for Address ~a" name)]
    [(symbol=? name (addr-name (car addrs))) (addr-address (car addrs))]
    [else (find-addr name (cdr addrs))]))

;; lookup: symbol store -> value
;; looks up a substitution in an environment (topmost one)
(define (fetch location store)
  (cond
    [(empty? store) (error 'interp "Invalid Address ~a" location)]
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
    [(set var newval)
     (result (void 1) (cons (room (find-addr var env) (result-val (interp newval env store)))
                            (result-newstore (interp newval env store))))]
    [(seq first second)
     (interp second env (result-newstore(interp first env store)))]
    [x (if (number? x)
           (result x store)
           (interp (name-to-val x env store)
                   env
                   store))]
    ))
;;#########################################################################
;;################ Testing ###########################
;;#########################################################################
#|
(define exp '(+ 3 5))
(define exp2 '(with ((x 0))
                   (+ (seq (set x 5) x)
                      (seq (set x 6) x))))
(parse '(+ 3 5))
(parse exp2)
(result-val (interp (parse exp2) empty empty))
;|#