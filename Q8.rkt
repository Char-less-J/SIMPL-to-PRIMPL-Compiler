#lang racket
;(require "primpl_interp.rkt")
(provide primpl-assemble)
(struct sub (type name val))
;;;;;;;;;;;;;;;;;;;;;;;;; 0-th pass: expanding data ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (concat-lst head tail) ;; concat the reversed head to tail
  (if (empty? head)
      tail
      (concat-lst (cdr head) (cons (car head) tail))))
(define (data-to-lst sexpr)
  ;build list from form 1
  (define (buildlst iter val acc)
    (cond [(= 0 iter) acc]
          [true (buildlst (sub1 iter) val (cons (list 'lit val) acc))]))
  ;convert numbers to lit numbers 
  (define (nums-to-litnums lst)
    (define (num-to-lit-h lst acc)
      (if (empty? lst)
          acc
          (num-to-lit-h (cdr lst) (cons (list 'lit (car lst)) acc))))
    (reverse(num-to-lit-h lst empty)))
  (match sexpr
    [(list 'data name (list nat val)) (cons (list 'data-label name) (buildlst nat val empty))]
    [data-lst (cons (list 'data-label (cadr data-lst)) (nums-to-litnums (cddr data-lst)))]))
(define (expand-data instr) ; returns expanded a-primpl list without data statement
  (define (expand-data-h instr acc)
    (cond
      [(empty? instr) acc]
      [(equal? (caar instr) 'data) ;; case for expansion
       (expand-data-h (cdr instr)
                      (concat-lst (data-to-lst (car instr)) acc))]                               
      [true (expand-data-h (cdr instr) (cons (car instr) acc))]))
  (reverse (expand-data-h instr empty)))

;;; Can we use a name/label without (lit) directly as an instruction?

;;;;;;;;;;;;;;;;;;;;;;;;;;; First Pass: Table Setup ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (no-duplicate name table)
  (if (equal? "nothing found haha" (hash-ref table name "nothing found haha")) #t #f))

(define (table-build instr)
  (define table (hash))
  (define (table-build-h instr env cur-addr) ;produce env for substitution
    (cond
      [(empty? instr) env]
      [true (match (car instr)
              [`(const, symb, val) (if (no-duplicate symb env)
                                       (table-build-h (cdr instr)
                                                      (hash-set env symb (sub 'const symb val))
                                                      cur-addr)
                                       (error "contains duplicate"))]
              [`(label, name) (if (no-duplicate name env)
                                  (table-build-h (cdr instr)
                                                 (hash-set env name (sub 'label name cur-addr))
                                                 cur-addr)
                                  (error "contains duplicate"))]
              [`(data-label, name) (if (no-duplicate name env)
                                       (table-build-h (cdr instr)
                                                 (hash-set env name (sub 'data-label name cur-addr))
                                                 cur-addr)
                                       (error "contains duplicate"))]
              [cur-instr (table-build-h (cdr instr)
                                        env
                                        (add1 cur-addr))])]))
    (table-build-h instr table 0))
;;;;;;;;;;;;; Lookup Functions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (lookup name env)
  (hash-ref env name (λ() (error "undefined ~a" name))))
(define (primitive-val? name)
  (define (prim-h name)
    (or (number? name)(boolean? name)(string? name)))
  (if (and (list? name) (empty? (cdr name)))
      (primitive-val? (car name))
      (prim-h name)
      ))
(define (name-to-val name env ind-const ind-label ind-data) ; given a symbol, turn it into value
  (define (opd-dest-to-name term env ind-const ind-label ind-data)
    (match term
      [(list imm ind) (list (name-to-val-h imm env 0 -1 0) ; label can't be value, otherwise it works
                            (name-to-val-h ind env -1 1 1))];const can't be address
      [name (name-to-val-h name env ind-const ind-label ind-data)]))
  (define (name-to-val-h name env ind-const ind-label ind-data)
    (cond
      [(primitive-val? name) name]
      [true (match (lookup name env)
              [(sub type name val)
               (cond [(or (and (symbol=? type 'const) (= 1 ind-const))
                          (and (symbol=? type 'label) (= 1 ind-label))
                          (and (symbol=? type 'data-label) (= 1 ind-data)))
                      (list (recurse-lookup val env))]
                     [(or (and (symbol=? type 'const) (= 0 ind-const))
                          (and (symbol=? type 'label) (= 0 ind-label))
                          (and (symbol=? type 'data-label) (= 0 ind-data)))
                      (recurse-lookup val env)]
                     [true (error "incorrect use")])])]))
  (define (recurse-lookup name env)
    (if (equal? (hash-ref env name "name not a key") "name not a key")
        name
        (recurse-lookup (sub-val(hash-ref env name)) env)))
  (opd-dest-to-name name env ind-const ind-label ind-data))
;;;;;;;;;;;;;;;;;;;;; Circular reference Check ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (circular? table)
  (define keys (hash-keys table))
  (define max-depth (length keys))
  (define (circular-key? key depth)
    (cond [(< (+ 3 max-depth) depth) #t]
          [(equal? (hash-ref table key "key is not key") "key is not key") #f];if not key not in table, it ends, so not circular
          [true (circular-key? (sub-val (hash-ref table key)) (add1 depth))]))
  (define (loop keys)
    (if (empty? keys)
        #f
        (or (circular-key? (car keys) 0)
            (loop (cdr keys)))))
  (loop keys))
;;;;;;;;;;;;;;;;;;;;;;;;;; Second Pass: translate ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (convert instr env)
  ;; 1 is indirect, 0 is direct, -1 is incorrect usage.
  ;; order: const, label, data-label
  (match instr
    [`(halt) 0]
    [`(lit, num) (name-to-val num env 0 0 0)]
    [(list op dest opd1 opd2) (list op
                                    (name-to-val dest env -1 1 1)
                                    (name-to-val opd1 env 0 1 1)
                                    (name-to-val opd2 env 0 1 1))]
    [`(lnot, dest, opd) (list 'lnot
                              (name-to-val dest env -1 1 1)
                              (name-to-val opd env 0 1 1))]

    [`(jump, opd) (list 'jump (name-to-val opd env 1 0 0))]
    [`(jsr, dest, opd) (list 'jsr
                             (name-to-val dest env -1 1 1)
                             (name-to-val opd env 1 0 0))]
    [`(branch, opd1, opd2) (list 'branch
                                 (name-to-val opd1 env 0 1 1)
                                 (name-to-val opd2 env 1 0 0))]
    [`(move, dest, opd) (list 'move
                              (name-to-val dest env -1 1 1)
                              (name-to-val opd env 0 1 1))]
    [`(print-val, opd) (list 'print-val (name-to-val opd env 0 -1 1))]
    [`(print-string, string) (list 'print-string string)]
    [num num]))
(define (remove-pseudo code)
  (cond [(empty? code) empty]
        [(or (equal? (caar code) 'label)
             (equal? (caar code) 'const)
             (equal? (caar code) 'data-label))
         (remove-pseudo (cdr code))]
        [true (cons (car code) (remove-pseudo (cdr code)))]))
(define (primpl-assemble a-primpl-code)
  (define expanded-code (expand-data a-primpl-code))
  (define table (table-build expanded-code))
  (when (circular? table) (error "circular definitions"));check circular
  (define code (remove-pseudo expanded-code))
  (define (primpl-assemble-h a-instructions acc env store)
    (cond
      [(empty? a-instructions) (reverse acc)] ;if instruction ends, return
      [true ;read instructions 1 by 1, with lookup tables fixed
       (primpl-assemble-h (cdr a-instructions)
                          (cons (convert (car a-instructions) env) acc)
                          env
                          store)]))
  (primpl-assemble-h code empty table code))
;|#
;;;;;;;;;;;;;;;;;;;;;;;; Test ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
(define program
  '((label LOOP-TOP)        ; loop-top:
    (const Waha haWa)
    (gt TMP1 X 0)           ;  tmp1 <- (x > 0)
    (branch TMP1 LOOP-CONT) ;  if tmp1 goto loop-cont
    (jump LOOP-DONE)        ;  goto loop-done
    (label LOOP-CONT)       ; loop-cont:
    (mul Y 2 Y)             ;  y <- 2 * y
    (sub X X 1)             ;  x <- x - 1
    (print-val Y)           ;  print y
    (print-string "\n")     ;  print "\n"
    (const ten Waha)
    (const haWa 10)
    (jump LOOP-TOP)         ;  goto loop-top
    (label LOOP-DONE)       ; loop-done:
    (halt)                  ;  halt
    (data X ten)
    (data Y 1)
    (data TMP1 0)))

;(expand-data tst3)
;(primpl-assemble tst3)
;(define expanded (expand-data program))
;(define lookup-table (table-build expanded))
;(define pseudo-removed (remove-pseudo expanded))
;pseudo-removed
;(print-table lookup-table)

;(define primplgram (primpl-assemble program))
;primplgram
;(load-primp primplgram)
;(run-primp)

(and true)
(or true)
(and false)
(or false)
(append '(1) '() '() '() '())
|#