#lang racket
;(require "Q8.rkt")
;(require "primpl_interp.rkt")
(provide compile-simpl)
;;Grammar
#|
(vars[(id number) ...] stmt ...)
stmt =
(print aexp)
(print string)
(set id aexp)
(seq stmt ...)
(iif bexp stmt stmt)
(skip)
(while bexp stmt ...)
----------------------
 aexp	=	 (+ aexp aexp)
 	|	 (* aexp aexp)
  	|	 (- aexp aexp)
  	|	 (div aexp aexp)
  	|	 (mod aexp aexp)
  	|	 number
  	|	 id
bexp 	=	 (= aexp aexp)
  	|	 (> aexp aexp)
  	|	 (< aexp aexp)
  	|	 (>= aexp aexp)
  	|	 (<= aexp aexp)
  	|	 (not bexp)
  	|	 (and bexp ...)
  	|	 (or bexp ...)
  	|	 true
  	|	 false
|#
;;output program
#|
1. code, body of simpl program
2. data statements for vars
3. temporary vars (stack)
|#
;;Translation stages
#|
1. convert vars into data of a-primpl
2. rewrite while and seq into pairs
2. convert statements into code

|#
;;Todo: 
;AND/or
(define (compile-pop)
  (list
   (list 'sub 'SP 'SP 1);move stack pointer down
   ))
(define (compile-push v)
   (list
    (list 'move (list 0 'SP) v);push value v to stack
    (list 'add 'SP 'SP 1);move stack up by one
    ))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;; Compile Expressions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (compile-op op aexp1 aexp2)
  (append
   (compile-aexp aexp1);compute & push first value to stack
   (compile-aexp aexp2);compute and push second value to stack
   (list
    (list op (list -2 'SP) (list -2 'SP) (list -1 'SP));operate on the two top vals of stack, and store the result to second top
    )
   (compile-pop)
   ))
(define (compile-bexp bexp)
  ; This needs to work on;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define (recursive-compile op exp-lst)
    (define (rec-comp-h op exp-lst);for and/or with more than 1 terms
      (cond
        [(empty? exp-lst) '()]
        [true
         (append
          (compile-bexp (car exp-lst));compute & push first value to stack
          (list
           (list op (list -2 'SP) (list -2 'SP) (list -1 'SP));operate on the two top vals of stack, and store the result to second top
           )
          (compile-pop);pop the unessesary first one
          (rec-comp-h op (cdr exp-lst)) ;the code to do op on the rest of args
          )]))
    (cond
      [(empty? exp-lst); case for (and) & (or)
       (cond [(equal? op 'land) (compile-push #t)]
             [(equal? op 'lor) (compile-push #f)])]
                        
      [(empty? (cdr exp-lst)) ; case for (and bexp) and (or bexp)
       (compile-bexp (car exp-lst))]
      [true
       (append
        (compile-bexp (car exp-lst));evaluate first bexp and push to stack
        (rec-comp-h op (cdr exp-lst));do so for other bexp
        )]))
    
  (match bexp
    [`(=, aexp1, aexp2) (compile-op 'equal aexp1 aexp2)]
    [`(>, aexp1, aexp2) (compile-op 'gt aexp1 aexp2)]
    [`(<, aexp1, aexp2) (compile-op 'lt aexp1 aexp2)]
    [`(>=, aexp1, aexp2) (compile-op 'ge aexp1 aexp2)]
    [`(<=, aexp1, aexp2) (compile-op 'le aexp1 aexp2)]
    [`(!=, aexp1, aexp2) (compile-op 'not-equal aexp1 aexp2)]
    [`(not, bexp1) (append
                    (compile-bexp bexp1);compute value of bexp and push to stack
                    (list
                     (list 'lnot (list -1 'SP) (list -1 'SP)); "not" the value in stack, and store it back
                     ))]
    [`(and,bexp1 ...) (recursive-compile 'land (cdr bexp))]
    [`(or,bexp1 ...) (recursive-compile 'lor (cdr bexp))]
    ['true (compile-push #t)]
    ['false (compile-push #f)]
    ))
(define (compile-aexp aexp)
  (match aexp
    [`(+, aexp1, aexp2) (compile-op 'add aexp1 aexp2)]
    [`(*, aexp1, aexp2) (compile-op 'mul aexp1 aexp2)]
    [`(-, aexp1, aexp2) (compile-op 'sub aexp1 aexp2)]
    [`(div, aexp1, aexp2) (compile-op 'div aexp1 aexp2)]
    [`(mod, aexp1, aexp2) (compile-op 'mod aexp1 aexp2)]
    [x (compile-push x)] ;num or id doesn't matter, A-primpl is left to interpret this
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;; Compile Statements ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (compile-stmt stmt)
  (define (compile-iif bexp stmt1 stmt2 LABEL0 LABEL1 LABEL2)
    (append
     (compile-bexp bexp)
     (list
      (list 'branch (list -1 'SP) LABEL0);branch with current stack value pushed by previous part
      (list 'jump LABEL1)
      (list 'label LABEL0)
      )
     (compile-pop);after using value to determine branch, remove it from stack
     (compile-stmt stmt1)
     (list
      (list 'jump LABEL2)
      (list 'label LABEL1)
      )
     (compile-pop);after using value to determine branch, remove it from stack
     (compile-stmt stmt2)
     (list
      (list 'label LABEL2)
      )
      ))
  (define (compile-while seq-lst bexp LABEL0 LABEL1 LABEL2)
    (append
     (list
      (list 'label LABEL0)
      )
     (compile-bexp bexp)
     (list
      (list 'branch (list -1 'SP) LABEL1);branch with current stack value pushed by previous part
      (list 'jump LABEL2)
      (list 'label LABEL1)
      )
     (compile-pop);after determining branch, compile-pop val
     (compile-stmt (cons 'seq seq-lst))
     (list
      (list 'jump LABEL0)
      (list 'label LABEL2)
      )
     (compile-pop));after detemining branch, compile-pop val
       )
  (match stmt
    [`(print, exp)
     (cond
       [(string? exp)(list (list 'print-string exp))]
       [true (append
              (compile-aexp exp);compute instruction and store in stack
              (list
               (list 'print-val (list -1 'SP));print the value from stack
               )
              (compile-pop)
              )])]
    [`(set, id, aexp)
     (append
      (compile-aexp aexp);compute instruction and store in stack
      (list
       (list 'move id (list -1 'SP));store value in stack to id location
       )
      (compile-pop)
       )]
    [(cons 'seq (cons stmt1 lst));lst is (cons stmt empty) or empty or other
     (cond [(empty? lst) (compile-stmt stmt1)]
           [true (append                  
                   (compile-stmt stmt1)
                   (compile-stmt (cons 'seq lst)))])]
      ;(list (compile-stmt stmt1) (compile-stmt stmt2)))]
    [`(iif, bexp, stmt1, stmt2)
     (compile-iif bexp stmt1 stmt2 (gensym "LABEL0")(gensym "LABEL1")(gensym "LABEL2"))]
    [`(skip) '()]
    [(cons 'while (cons bexp seq-lst))
     (compile-while seq-lst bexp (gensym "LABEL0") (gensym "LABEL1") (gensym "LABEL2"))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;; Compile: Main Parts ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Parameters: Program - list 
(define (modify-vars vars)
  (define (conversion var)
    (list 'data (car var)
          (cadr var)))
  (map conversion vars))
#|
(define (print-result bin)
  (cond [(empty? bin) empty]
        [true (if (result? (car bin))
                  (cons (print-result(result-lst (car bin))) (print-result (cdr bin)))
                  (cons (car bin) (print-result (cdr bin))))]))
|#
(define (compile-simpl program)
  (define (compile-simpl-h instr)
    (match instr
      ['() '()]
      [(cons 'vars (cons data code))
       (append (compile-stmt (cons 'seq code))
               (modify-vars data))] ;;; Concat left to be implemented
      [stmt (compile-stmt stmt)]))
  (define instr-body (compile-simpl-h program))
  (define stack-pointer-loc (+ 3(length instr-body)))
  (reverse (cons (list 'data 'SP stack-pointer-loc) (reverse instr-body))))
;;;;;;;;;;;;;;;;;;; Test ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
(modify-vars '(vars [(i 1) (j 0) (acc 0)]))
(print-result
 (result-lst
  (compile-stmt
 '(seq
  (while (> x 0)
     (set y (* 2 y))
     (set x (- x 1)))
  (print y)))))

(define progra
 '(vars [(x 5) (y 1) (z 4)] ;vars declared based on other vars?
        (seq
         (while (> x 0)
                (set y (* 2 y))
                (set x (- x 1)))
         (print y))))
(define program
 '(vars [(x 99) (y 1)] ;vars declared based on other vars?
        (seq
         (while (and (> x 0) (not (> y 99)))
                (set y (* 2 y))
                (set x (- x 1)))
         (print "result is: ")
         (print y)
         (print "\n")
         (iif (or (> x y))
              (seq (skip) (skip) (skip))
              (seq (set y x) (print "set!\n")))
         (print "new result is: ")
         (print y))))
;(compile-stmt program1)
;(compile-simpl program1)
(compile-simpl program)
(define primpl-code (primpl-assemble (compile-simpl program)))
primpl-code
(load-primp primpl-code)
(run-primp)
;(append '(1 2 (3 4)) '(3 4) '(4) '(5) '(3 4))
|#