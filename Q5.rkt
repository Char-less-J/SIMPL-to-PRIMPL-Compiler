#lang racket
(require test-engine/racket-tests)
;;#########################################################################
;;#################### Structs of language ################################
;;#########################################################################
(struct bin (op fst snd) #:transparent) ; op is a symbol; fst, snd are ASTs.
(struct fun (param body) #:transparent) ; param is a symbol; body is an AST.
(struct app (fn arg) #:transparent) ; fn and arg are ASTs.
;; An AST is a (union bin fun app).
(struct sub (name val) #:transparent)
;; A substitution is a (sub n v), where n is a symbol and v is a value.
;; An environment (env) is a list of substitutions.
(struct closure (var body envt) #:transparent #:mutable)
;; A closure is a (closure v bdy env), where
;; v is a symbol, bdy is an AST, and env is a environment.
;; A value is a (union number closure).

;;######### Structs To implement #######
;; nm: a name to be substituted
;; nmd: definition for the name
;; body: an expression containing nm as a part of it, to be substituted
(struct rec (nm nmd body) #:transparent)
(struct ifzero (t tb fb) #:transparent)

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
    [`(rec ((,nm ,nmd)) ,bdy)
     (rec (parse nm)
       (parse nmd)
       (parse bdy))]
    [`(ifzero ,t ,tb, fb) (ifzero (parse t)
                                  (parse tb)
                                  (parse fb))]
    [x x]))

; op-trans: symbol -> (number number -> number)
; converts symbolic representation of arithmetic function to actual Racket function
(define (op-trans op)
  (match op
    ['+ +]
    ['* *]
    ['- -]
    ['/ /]))

;; lookup: symbol env -> value
;; looks up a substitution in an environment (topmost one)
(define (lookup var env)
  (cond
    [(empty? env) (error 'interp "unbound variable ~a" var)]
    [(symbol=? var (sub-name (first env))) (sub-val (first env))]
    [else (lookup var (rest env))]))

;; reclos: rec env -> closure
;; given a rec and a env, produce a closure
(define (reclos record envir)
  (define clos (closure (rec-nm record) ; parameter
                        (rec-body record) ; body to substitute parameter in
                        'undefined)) ; env defining substitution rules
  (define new-envir (cons (sub (rec-nm record)
                               (rec-nmd record))
                          envir))
  (set-closure-envt! clos new-envir)
  clos
  )

;; interp: AST env -> value
(define (interp ast env)
  (match ast
    [(fun v bdy) (closure v bdy env)]
    [(app fun-exp arg-exp)
       (match (interp fun-exp env)
         [(closure v bdy cl-env)
          (interp bdy (cons (sub v (interp arg-exp env)) cl-env))])]
    [(bin op x y)
       ((op-trans op) (interp x env) (interp y env))]
    [(ifzero test trueb falseb)
     (if (zero? (interp test env))
         (interp trueb env)
         (interp falseb env)
       )]
    [(rec nm def bdy)
     (match (reclos (rec nm def bdy) env)
       [(closure para body new-env) ; the circular closure with name, definition, and new env with the definition
        (interp bdy new-env)]
       )]
    [x (if (number? x)
           x
           (interp (lookup x env) env))]
    ))