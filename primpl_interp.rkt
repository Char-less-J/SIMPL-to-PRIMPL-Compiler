#lang racket

(provide load-primp run-primp)

(define MEM-SIZE 10000)

(define mem (make-vector MEM-SIZE 0))
(define pc 0)
(define halted? #f)

;; primp-error: string value ... -> void
;; prints error message and other useful information

(define (primp-error . args)
  (apply printf args)
  (printf "PC: ~a" pc)
  (set! halted? #t)
  (error 'PRIMP "halted with error"))

;; valid-mem?: nat -> Boolean
;; checks for valid memory location

(define (valid-mem? i)
  (and (number? i) (>= i 0) (< i MEM-SIZE)))

;; mem-get: nat -> value
;; produces M[i], with error checking

(define (mem-get i)
  (cond
    [(valid-mem? i) (vector-ref mem i)]
    [else (primp-error "memory index out of range ~a\n" i)]))

;; mem-set!: nat value -> void
;; modifies M[i], with error checking

(define (mem-set! i newv)
  (cond
    [(valid-mem? i) (vector-set! mem i newv)]
    [else (primp-error "memory index out of range ~a\n" i)]))


;; load-primp: (listof list) -> void
;; initializes memory and PC, loads program into memory

(define (load-primp prog-list)
  (set! halted? #f)
  (set! pc 0)
  (vector-fill! mem 0)
  (for [(i MEM-SIZE)
        (c (in-list prog-list))]
    (mem-set! i c)))

;; run-primp: -> void
;; runs the PRIMP machine

(define (run-primp)
  (let loop ()
    (unless halted?
      (fetch-execute-once)
      (loop))))

;; fetch-execute-once: -> void
;; one step of fetch-execute cycle

(define (fetch-execute-once)
  (define inst (mem-get pc))
  (cond
    [(list? inst)
       (set! pc (add1 pc))
       (dispatch-inst inst)]
    [else
       (set! halted? #t)]))

;; dispatch-inst : S-exp primp -> void
;; Looks up inst in dispatch table and executes the
;; associated function.

(define (dispatch-inst inst)
  (when (empty? inst)
    (primp-error "Bad instruction: ~a\n" inst))
  (apply 
    (hash-ref dispatch-table 
              (first inst)
              (lambda () 
                (primp-error "Bad instruction: ~a\n" inst)))
         (rest inst)))

;; get-op-imm-or-mem: (union (list nat) nat Boolean) -> value
;; gets immediate operand or operand from memory location

(define (get-op-imm-or-mem op)
  (match op
    [(or (? number? v) (? boolean? v)) v] ; immediate 
    [x (get-op-mem op)])) ; rest

;; get-op-mem: (list nat) -> value
;; gets operand from memory location (indirect or indexed)

(define (get-op-mem op)
  (match op
    [`(,i) (mem-get i)] ; indirect
    [`(,i (,j)) (mem-get (+ i (mem-get j)))] ; indexed
    [x (primp-error "Bad operand: ~a\n" op)]))

;; set-dest!: (list nat) value -> void
;; sets new value of memory location

(define (set-dest! op v)
  (match op
    [`(,i) (mem-set! i v)] ; indirect
    [`(,i (,j)) (mem-set! (+ i (mem-get j)) v)] ; indexed
    [x (primp-error "Bad destination: ~a\n" op)]))

;; contracts for instructions: primp value ... -> void
;; side effects listed with each instruction

;; print-string : Print a string
(define (print-string s)
  (printf "~a" s))

;; print-val : Print an immediate value or contents of memory location
(define (print-val op)
  (define val (get-op-imm-or-mem op))
  (printf "~a" val))

;; bin-num-op : M[dest] <- src1 op src2
(define ((bin-num-op op) dest src1 src2)
  (define opnd1 (get-op-imm-or-mem src1))
  (define opnd2 (get-op-imm-or-mem src2))
  (unless (number? opnd1)
    (error 'PRIMP "First arithmetic operand not number: ~a ~a" opnd1 opnd2))
  (unless (number? opnd2)
    (error 'PRIMP "Second arithmetic operand not number: ~a ~a" opnd1 opnd2))
  (set-dest! dest (op opnd1 opnd2)))

;; add : M[dest] <- opnd1 + opnd2
(define add (bin-num-op +))

;; sub : M[dest] <- opnd1 - opnd2
(define sub (bin-num-op -))

;; mul : M[dest] <- opnd1 * opnd2
(define mul (bin-num-op *))

;; zero-source-error: (union (list nat) n string -> void

(define (zero-source-error src msg)
  (when (zero? (get-op-imm-or-mem src))
    (primp-error msg)))

;; div : M[dest] <- opnd1 / opnd2 [integer division]
(define (div dest src1 src2)
  (zero-source-error src2 "Divide by zero\n")
  ((bin-num-op quotient) dest src1 src2))

;; mod : M[dest] <- opnd1 mod opnd2
(define (mod dest src1 src2)
  (zero-source-error src2 "Modulus is zero\n")
  ((bin-num-op modulo) dest src1 src2))

;; equal : M[dest] <- opnd1 = opnd2
(define equal (bin-num-op equal?))

;; not-equal: M[dest] <- opnd1 <> opnd2
(define not-equal (bin-num-op (negate equal?)))

;; gt : M[dest] <- opnd1 = opnd2
(define gt (bin-num-op >))

;; ge : M[dest] <- opnd1 = opnd2
(define ge (bin-num-op >=))

;; lt : M[dest] <- opnd1 = opnd2
(define lt (bin-num-op <))

;; le : M[dest] <- opnd1 = opnd2
(define le (bin-num-op <=))

;; bin-logical-op : M[dest] <- opnd1 op opnd2
(define ((bin-logical-op op) dest src1 src2)
  (define opnd1 (get-op-imm-or-mem src1))
  (define opnd2 (get-op-imm-or-mem src2))
  (unless (boolean? opnd1)
    (primp-error "First logical operand not Boolean: ~a ~a\n" opnd1 opnd2))
  (unless (boolean? opnd2)
    (primp-error "Second logical operand not Boolean: ~a ~a\n" opnd1 opnd2))
  (set-dest! dest (op opnd1 opnd2)))

(define land (bin-logical-op (lambda (b1 b2) (and b1 b2))))

(define lor (bin-logical-op (lambda (b1 b2) (or b1 b2))))

(define (lnot dest src)
  (define opnd (get-op-imm-or-mem src))
  (unless (boolean? opnd)
    (primp-error "Logical operand not Boolean: ~a\n" opnd))
  (set-dest! dest (not opnd)))

;; move : M[dest] <- M[src]

(define (move dest src)
  (set-dest! dest (get-op-imm-or-mem src)))

;; jump: PC <- loc

(define (jump loc)
  (define tgt (get-op-imm-or-mem loc))
  (unless (valid-mem? tgt)
    (primp-error "Illegal jump target: ~a\n" tgt))
  (set! pc tgt))

;; jsr : M[dest] <- PC ; PC <- loc

(define (jsr dest loc)
  (define tgt (get-op-imm-or-mem loc))
  (unless (valid-mem? tgt)
    (primp-error "Illegal jsr target: ~a\n" tgt))
  (set-dest! dest pc)
  (set! pc tgt))

;; branch : PC <- loc if opnd

(define (branch opnd loc)
  (define tgt (get-op-imm-or-mem loc))  
  (unless (valid-mem? tgt)
    (primp-error "Illegal branch target: ~a\n" tgt))
  (define tested (get-op-imm-or-mem opnd))
  (unless (boolean? tested)
    (primp-error "Tested value in branch not Boolean: ~a\n" tested))
  (when tested (set! pc tgt)))

;; dispatch table 

(define dispatch-table
  (hash
    'print-val print-val
    'print-string print-string
    'add add
    'sub sub
    'mul mul
    'div div
    'mod mod
    'equal equal
    'not-equal not-equal
    'gt gt
    'ge ge
    'lt lt
    'le le
    'land land
    'lor lor
    'lnot lnot
    'move move
    'jump jump
    'jsr jsr
    'branch branch))

;(vars [(x 10) (y 1)]
;  (while (> x 0)
;    (set y (* 2 y))
;    (set x (- x 1))
;    (print y)
;    (print "\n")))

(define test-prog
  '((gt (11) (9) 0)      ; 0: tmp1 <- x > 0
    (branch (11) 3)      ; 1: if tmp1 goto 3
    (jump 8)             ; 2: goto 8
    (mul (10) 2 (10))    ; 3: y <- 2 * y
    (sub (9) (9) 1)      ; 4: x <- x - 1
    (print-val (10))     ; 5: print y
    (print-string "\n")  ; 6: print "\n"
    (jump 0)             ; 7: goto 0
     0                   ; 8: 0 [number, halts program]
     10                  ; 9: x 
     1                   ; 10: y
     0                   ; 11: tmp1
     ))

;(load-primp test-prog)
;'((gt (11) 10 0) (branch (11) 3) (jump 8) (mul (10) 2 1) (sub (9) 10 1) (print-val 1) (print-string "\n") (jump 0) 0 10 1 0)
;(run-primp)


;;;;Q9
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
  (define (recursive-compile op exp-lst)
   (cond
      [(empty? (cdr exp-lst)) '()]
      [true       
       (list
        (compile-bexp (car exp-lst))
        (recursive-compile op (cdr exp-lst))
        )]))
  (match bexp
    [`(=, aexp1, aexp2) (compile-op 'equal aexp1 aexp2)]
    [`(>, aexp1, aexp2) (compile-op 'gt aexp1 aexp2)]
    [`(<, aexp1, aexp2) (compile-op 'lt aexp1 aexp2)]
    [`(>=, aexp1, aexp2) (compile-op 'ge aexp1 aexp2)]
    [`(<=, aexp1, aexp2) (compile-op 'le aexp1 aexp2)]
    [`(not, bexp1) (append
                    (compile-bexp bexp1);compute value of bexp and push to stack
                    (list
                     (list 'lnot (list -1 'SP) (list -1 'SP)); "not" the value in stack, and store it back
                     ))]
    [`(and,bexp1 ...) (recursive-compile 'and (cdr bexp))]
    [`(or,bexp1 ...) (recursive-compile 'or (cdr bexp))]
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
    [`(iif, bexp, stmt1, stmt2)
     (compile-iif bexp stmt1 stmt2 (gensym "LABEL0")(gensym "LABEL1")(gensym "LABEL2"))]
    [`(skip) (list '(lit 0))]
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