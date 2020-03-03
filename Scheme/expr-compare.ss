#lang racket
(provide expr-compare)
(define LAMBDA (string->symbol "\u03BB"))

;define helper functions for hashmap. put key value, and get value from key
(define put-keyval
  (lambda (h key val)
    (cond [(equal? h '()) (hash-set (hash) key val)]
          [(hash-set h key val)])))

(define get-val
  (lambda (h key)
    (hash-ref h key "Not Found")))

;Check if expression x is lambda or λ symbol
(define (lambda? x)
  (member x '(lambda λ)))

;Check if an expression is a lambda function. Exp must be a list of length 3 whose first
;element is lambda or λ and whose second element is also a list
(define lambda-fun?
  (lambda (exp)
    (if (and (and (and (list? exp) (lambda? (car exp))) (equal? (length exp) 3)) (list? (cadr exp)))
        #t
        #f)))

;Check for quote function. Must be a list of length 2, and first element quote
(define quote-fun?
  (lambda (exp)
    (if (and (and (list? exp) (equal? (car exp) 'quote)) (equal? (length exp) 2))
        #t
        #f)))

;Check for if function. Must be a list of 4 elements and first element if
(define if-fun?
  (lambda (exp)
    (if (and (and (list? exp) (equal? (car exp) 'if)) (equal? (length exp) 4))
        #t
        #f)))

;Helper function to reverse list. Uses accumulator technique as seen in lecture for linear complexity
(define revapp
  (lambda (l accu)
    (cond [(not (list? l)) (cons (l) accu)]
          [(equal? l '()) accu]
          [(revapp (cdr l) (cons (car l) accu))])))

;Sub hash function replacs occurrance of a key in a hashmap with itself. This is to avoid
;Overwriting inner arguments within functions with renamed variable from outer function.
;This is to respect scope of variable definitions
(define sub-hash
  (lambda (args hash)
    (cond [(equal? args '())
           hash]
          [(put-keyval (sub-hash (cdr args) hash) (car args) (car args))])))

;Manage symbol replacement for cases of lambda functions. Check arguments of new lambda function
; and overwrite accurrance of arguments within hashmap to prevent overwrite within the body of lambda exp
(define lambda-replace
  (lambda (e hash)
    (cons (car e) (cons (cadr e) (list (replace-merged (caddr e) (sub-hash (cadr e) hash)))))))


;Recurse over an expression and check elements to see if they need to be renamed.
;lambda's must be treated differently to respect variable scope.
(define replace-merged
  (lambda (e hash)
    (cond [(equal? hash '()) e]
          [(not (list? e))
           (let ([newVal (get-val hash e)])
             (if (equal? newVal "Not Found")
                 e
                 newVal))]
          [(equal? e '()) '()]
          [(lambda-fun? e)
           (listify (lambda-replace e hash))]
          [(list? (car e))
           (cons (replace-merged (car e) hash) (listify (replace-merged (cdr e) hash)))]
          [(let ([newVal (get-val hash (car e))])
             (if (equal? newVal "Not Found")
                 (cons (car e) (listify (replace-merged (cdr e) hash)))
                 (cons newVal (listify (replace-merged (cdr e) hash)))))])))

;This function takes two symbols from lambda expressions
;If either of the symbols is λ, return λ.
;If both are lambda, return lambda
(define merge-λ
  (lambda (λ1 λ2)
    (if (or (equal? λ1 'λ) (equal? λ2 'λ))
        'λ
        'lambda)))

;This function simply wraps an expression in a list, if the expression is not already a list
(define (listify l)
  (if (not (list? l))
      (list l)
      l))

;This function takes two verified lambda expressions. Gets the merge of the head symbol and
;concatanates it with a merge of the arguments and the merge of the bodies. In order to apply the argument efficiently, we
;reverse the argument list so when each argument is processed, it can simply be cons'd, thus retaining original order
(define lambda-merge
  (lambda (λ1 λ2)
    (let ([mergesym (merge-λ (car λ1) (car λ2))])
      (cons mergesym (listify (lambda-arg-merge (revapp (cadr λ1) '()) (revapp (cadr λ2) '()) (caddr λ1) (caddr λ2) '() '() '()))))))

;This function compares arguments between lambda functions, creates new variables whwere the variable names differ.
;Accumulates two hash maps, with a key for all variables that changed for each of the expressions
;Function is recursive. Once the arguments have all been processed, returns the cons
;Of the merged arguments and the expr-compare of replaced variables for the body of each of the lambdas
(define lambda-arg-merge
  (lambda (argsx argsy expx expy argAccu hash1 hash2)
    (cond [(and (not (list? argsx)) (not (list? argsy)))
           (if (equal? argsx argsy)
               (cons argsx (list (expr-compare expx expy)))
               (let ([newSym (string->symbol (string-append (symbol->string argsx)) "!" (symbol->string argsy))])
                 (cons newSym
                       (list (expr-compare
                        (replace-merged expx (put-keyval hash1 argsx newSym))
                        (replace-merged expy (put-keyval hash2 argsy newSym)))))))]
          [(and (and (list? argsx) (list? argsy)) (equal? (length argsx) (length argsy)))
           (if (equal? argsx '())
               (cons argAccu (list (expr-compare
                              (replace-merged expx hash1)
                              (replace-merged expy hash2))))
               (if (not (equal? (car argsx) (car argsy)))
                   (let ([newSym (string->symbol (string-append (symbol->string (car argsx)) "!" (symbol->string (car argsy))))])
                     (lambda-arg-merge
                      (cdr argsx)
                      (cdr argsy)
                      expx expy
                      (cons newSym (listify argAccu))
                      (put-keyval hash1 (car argsx) newSym)
                      (put-keyval hash2 (car argsy) newSym)))
                   (lambda-arg-merge
                      (cdr argsx)
                      (cdr argsy)
                      expx expy
                      (cons (car argsx) (listify argAccu))
                      hash1 hash2)))]
          [(quasiquote (if % (unquote (cons argsx (listify expx))) (unquote (cons argsy (listify expy)))))]
          )))

;Main function expr-compare. Function is recursive. Handles specific cases to either merge the expressions in an if % x y
; or to find similarities within expressions
(define expr-compare
  (lambda (x y)
    (cond [(equal? x y) x]
        [(and (boolean? x) (boolean? y)) 
         (if x '% '(not %))]
        [(or (not (list? x)) 
             (not (list? y)))
         (list 'if '% x y)]
        [(not (equal? (length x) (length y)))
         (list 'if '% x y)]
        [(and (and (lambda-fun? x) (lambda-fun? y)) (equal? (length (cadr x)) (length (cadr y))))
          (lambda-merge x y)]
        [(and (lambda-fun? x) (lambda-fun? y))
         (list 'if '% x y)]
        [(xor (lambda-fun? x) (lambda-fun? y))
          (list 'if '% x y)]
        [(and (quote-fun? x) (quote-fun? y))
         (list 'if '% x y)]
        [(if-fun? x)
         (if (if-fun? y)
             (cons 'if (listify (expr-compare (cdr x) (cdr y))))
             (list 'if '% x y))]
        [(cons (expr-compare (car x) (car y)) (listify (expr-compare (cdr x) (cdr y))))]
        )))

;test-expr-compare evaluates a test expression x and evaluates our expr-compare function with both expressions x and y,
; with % as true, and evaluates expression y and expr-compare x y with % as false. Should return #t if implementation is correct
(define (test-expr-compare x y) 
  (and (equal? (eval x)
               (eval `(let ((% #t)) , (expr-compare x y))))
       (equal? (eval y)
               (eval `(let ((% #f)) , (expr-compare x y))))))

;expressions x and y uses several aspect of the grammar to test our implementation.
; calling functions append, cons, using lambda expressions if and cond statement, list construction
; procedure calls, quasiquote and unquote functions, with variables and string literals
(define test-expr-x
  '(append (cons ((lambda (λ) (if λ
                              "test"
                              "notest")) #t)
                   ((λ (lambda) (cond [lambda (list "noexpr")]
                                      [(list "expr")])) #f))
             ((lambda (argc) (list (quasiquote (unquote argc)))) "x")))

(define test-expr-y
 '(append (cons ((λ (lambda) (if lambda
                              "notest"
                              "test")) #f)
                   ((lambda (λ) (cond [λ (list "expr")]
                                      [(list "noexpr")])) #t))
             ((λ (argz) (list argz)) "y")))
