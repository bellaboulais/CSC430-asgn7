#lang typed/racket
(require typed/rackunit)

;; Assignment 4


; ----------------------------- ;
; ----- DATA DEFINITIONS ------ ;
; ----------------------------- ;

; textbook definition for a tstruct
(define-syntax tstruct
  (syntax-rules ()
    [(_ name fields)
     (struct name fields #:transparent)]))
(tstruct fdC ([name : Symbol] [args : (Listof Symbol)] [body : ExprC]))

 
; Define the ExprC for the ZODE4 language
(define-type ExprC (U numC idC strC ifC locals lamC appC))                 
(tstruct numC ([n : Real]))                           
(tstruct idC ([name : Symbol]))                           
(tstruct strC ([str : String]))
(tstruct ifC ([test : ExprC] [then : ExprC] [else : ExprC]))
(tstruct locals ([bindings : (Listof Clause)] [body : ExprC]))
(tstruct lamC ([args : (Listof Symbol)] [body : ExprC]))
(tstruct appC ([f : ExprC] [args : (Listof ExprC)])) 

; Define the Clause: inside locals... ex. add6 = {curradd 6} : 
(tstruct Clause ([id : Symbol] [expr : ExprC]))

; Define our value types -> represents an evaluated expression
(define-type Value (U numV boolV strV closV primV)) 
(tstruct boolV ([b : (U #t #f)]))                   ; boolV: boolean value
(tstruct strV ([s : String]))                       ; strV: string value
(tstruct closV ([args : (Listof Symbol)] [body : ExprC] [env : Env])) ; closV: closure value
(tstruct primV ([p : Symbol]))                      ; primV: primitive value
(tstruct numV ([n : Real]))                         ; numV: number value

; Define our env and top-env
(define-type Env (Listof (List Symbol Value)))
(define top-env (list (list '+ (primV '+))
                      (list '- (primV '-))
                      (list '* (primV '*))
                      (list '/ (primV '/))
                      (list '<= (primV '<=))
                      (list 'equal? (primV 'equal?))
                      (list 'true (boolV #t))
                      (list 'false (boolV #f))
                      (list 'error (primV 'error))
                      ))


; ----------------------------- ;
; ----- INTERP FUNCTIONS ------ ;
; ----------------------------- ;

; lookup NOT COMPLETE (waiting on more primitives to write more test cases)
;  PARAMS:  x : Symbol
;           env : Env
;  RETURNS: Value
;  PURPOSE: lookup the value of x in the environment env
(: lookup (Symbol Env -> Value))
(define (lookup [x : Symbol] [env : Env])
  (cond
    [(empty? env) (error 'lookup "ZODE: Variable not found ~e" x)]
    [(equal? x (first (first env))) (second (first env))]
    [else (lookup x (rest env))])) 

; extend-env
;  PARAMS:  clauses : Clauses
;           env : Env
;  RETURNS: Env
;  PURPOSE: extend the environment env with the definitions in another environment.
(: extend-env ((Listof Symbol) (Listof Value) Env -> Env))
(define (extend-env params argval env)
  (define new-bindings
    (map (lambda (param [arg : Value])
           (list param arg))
         params argval))
  (cast (append new-bindings env) Env)) 
   

; top-interp
(: top-interp (Sexp -> String)) 
;   PARAMS:  s : Sexp 
;   RETURNS: String
;   PURPOSE:  
(define (top-interp s)
  (define parsed-s (parse s))
  ;(display "parse: ")
  ;(displayln parsed-s)
  (define interp-s (interp parsed-s top-env))
  ;(display "interp: ")
  ;(displayln interp-s)
  (serialize interp-s))

 
; serialize
(: serialize (Value -> String))
;   PARAMS:   v:    Value           the value to serialize
;   RETURNS:  String
;   PURPOSE:  convert a value to a string
(define (serialize v)
  (match v
    [(numV n) (~v n)]
    [(boolV b) (if b "true" "false")]
    [(strV s) (~v s)]
    [(closV arg body _) "#<procedure>"]
    [(primV p) "#<primop>"]))


; interp
(: interp (ExprC Env -> Value))
;   PARAMS:   e:    ExprC           the expression to interpret
;             env:  Envrionment     list of functions defined in the current environment
;   RETURNS:  Value
;   PURPOSE:  
(define (interp e env)
  ;(display "interp function: ")
  ;(displayln e)
  ;(displayln "")
  (match e                                                                     
    [(numC n) (numV n)]  
    [(idC x) (lookup x env)] 
    [(strC s) (strV s)] 
    [(ifC test then els) (match (interp test env)
                           [(boolV #t) (interp then env)]
                           [(boolV #f) (interp els env)]
                           [else (error 'interp "ZODE: Invalid if expression: ~e" e)])]
    [(lamC args body)
     (closV args body env)] 
    [(appC f args) (match (interp f env)
                     [(closV params body env2)
                      (define argval (map (lambda ([arg : ExprC]) (interp arg env)) args))
                      (cond
                        [(= (length params) (length args))
                         (interp body (extend-env params argval env2))]
                        [else (error 'interp "ZODE: Invalid number of arguments: ~e" e)])]
                     [(primV p) (interp-primitive p args env)]
                     [else (error 'interp "ZODE: Invalid application: ~e" e)])]))


; interp-primitive
(: interp-primitive (Symbol (Listof ExprC) Env -> Value))
;   PARAMS:   p:    Symbol          the primitive to interpret
;             args: (Listof Value)  the arguments to the primitive
;   RETURNS:  Value
;   PURPOSE:  helper for interp to interpret primitives
(define (interp-primitive [p : Symbol][exprs : (Listof ExprC)] [env : Env])
  (match p 
    ['+ (2num-op (interp (first exprs) env) (interp (second exprs) env) +)]
    ['- (2num-op (interp (first exprs) env) (interp (second exprs) env) -)]
    ['* (2num-op (interp (first exprs) env) (interp (second exprs) env) *)]
    ['/ (define e1 (interp (first exprs) env))
        (define e2 (interp (second exprs) env))
        (cond
          [(equal? e2 (numV 0))
           (error 'division "ZODE: Division by zero ~e" e2)]
          [else (2num-op (interp (first exprs) env) (interp (second exprs) env) /)])]
    ['<= (define e1 (interp (first exprs) env))
         (define e2 (interp (second exprs) env))
         (cond 
           [(and (numV? e1) (numV? e2))
            (boolV (<= (numV-n e1) (numV-n e2)))] 
           [else (error 'interp-primitive "ZODE: Invalid arguments for <= ~e" exprs)])]
    ['equal? (boolV (equal? (interp (first exprs) env) (interp (second exprs) env)))]
    ['true (boolV #t)]
    ['false (boolV #f)] 
    ['error (error 'user-error "ZODE: error ~e" (serialize (interp (first exprs) env)))]
    [else (error 'interp-primitive "ZODE: Invalid primitive ~e" p)]))

; 2num-op
(: 2num-op (Value Value (Real Real -> Real) -> Value))
;   PARAMS:   l:    Value           the left operand
;             r:    Value           the right operand
;             operator: (Number Number -> Number) the operator to apply
;   RETURNS:  Value
;   PURPOSE:  helper for interp-primitive to apply a binary operator to two numbers
(define (2num-op [l : Value] [r : Value] [operator : (Real Real -> Real)]) : Value
  (cond
    [(and (numV? l) (numV? r))
     (numV (operator (numV-n l) (numV-n r)))] 
    [else
     (error 'num+ "ZODE: primitive + expects numbers as arguments, given ~e and ~e" l r)]))



; ---------------------------- ; 
; ----- PARSER FUNCTIONS ----- ;
; ---------------------------- ;

; parse  
(: parse (Sexp -> ExprC))
;   PARAMS:   s :  Sexp 
;   RETURNS:  ExprC
;   PURPOSE:  
(define (parse s)
  (match s
    [(? real? n) (numC n)] ; real                           
    [(? symbol? s) (idC s)] ; variable
    [(? string? str) (strC str)] ; string
    [(list 'if ': test ': then ': else) (ifC (parse test) (parse then) (parse else))] ; if
    
    [(list 'locals ': clauses ... ': body) ; locals
     (define parsed-clauses (parse-clause (cast clauses Sexp)))
     (define parsed-body (parse body))
     (define ids (cast (map (lambda ([clause : Clause]) (Clause-id clause)) parsed-clauses) (Listof Symbol)))
     (if (equal? ids (remove-duplicates ids))
         (appC (lamC ids parsed-body)
               (map (lambda ([c : Clause]) (Clause-expr c)) parsed-clauses))
         (error 'parse "ZODE: Duplicate arguments in lambda expression: ~a" ids))]
    
    [(list 'lamb ': args ... ': body) ; lambC
     (if (andmap symbol? args)
         (if (equal? args (remove-duplicates args))
             (lamC (cast args (Listof Symbol)) (parse body))
             (error 'parse "ZODE: Duplicate arguments in lambda expression: ~a" args))
         (error 'parse "ZODE: Invalid arguments for lambda expression: ~a" args))]
    [(list f args ...) ; appC
     (define parsed-args (map (lambda ([arg : Sexp]) (parse arg)) args))
     (match f
       [(or '+ '- '* '/) ; Check if f is a mathematical operation
        (cond
          [(check-if parsed-args)
           (appC (parse f) parsed-args)]
          [else (error 'parse "ZODE: Invalid arguments for operation ~a" f)])]
       ['locals (error 'parse "ZODE: Invalid locals argument ~a" args)]
       ['if (error 'parse "ZODE: Invalid if argument ~a" args)]
       ['lamb (error 'parse "ZODE: Invalid lamb argument ~a" args)]
       [else (appC (parse f) parsed-args)])]))  

 
(: check-if ((Listof ExprC) -> Boolean))
; helper function to check for key word if
(define (check-if lst) 
  (cond
    [(empty? lst) #t]
    [(equal? (first lst) (idC 'if))
     #f]
    [else (check-if (rest lst))]))

 
; parse-clause
(: parse-clause (Sexp -> (Listof Clause)))
;   PARAMS:   s :  Sexp
;   RETURNS:  list of Clause
;   PURPOSE:  parse clauses from locals statement  
(define (parse-clause s)
  (match s
    [(list (? symbol? id) '= expr)
     (cond
       [(equal? id ':)
        (error 'parse-clause "ZODE: Invalid clause expression ~e" s)]
       [else (list (Clause id (parse expr)))])]
    [(list (? symbol? id) '= expr ': rest ...)
     (cons (Clause id (parse expr)) (parse-clause rest))] 
    [else (error 'parse-clause "ZODE: Invalid clause expression ~e" s)]))

 
; ---------------------- ;
; ----- TEST CASES ----- ; 
; ---------------------- ;

; ----- defs for test cases ----- ; 
; test parsed functions
(define testpfunc0 (list (Clause 'curradd (lamC (list 'x) (appC (idC '+) (list (idC 'x) (idC 'x)))))))
(define testpfunc1 (list (Clause 'add6 (appC (idC 'curradd) (list (numC 6))))))

;   test environments with numbers
(define testenv1 (list (list 'x (numV 5))))
(define testenv2 (list (list 'x (numV 5)) (list 'y (numV 6))))
;   test environments with functions
(define testenv3 (list (list 'x (closV (list 'x) (idC 'x) testenv1))))
(define testenv4 (list (list 'x (closV (list 'x) (idC 'x) top-env))))
;   test environments with strings
(define testenv5 (list (list 'x (strV "hello"))))
;   test environments with booleans
(define testenv6 (list (list 'tv (boolV #t))))
(define testenv7 (list (list 'fv (boolV #f))))

; ----- INTERPRETER TEST CASES ----- ;

; ----- lookup test cases -----
;   test lookup with numbers
(check-equal? (lookup 'x (list (list 'x (numV 5)))) (numV 5))
(check-equal? (lookup 'x (list (list 'x (strV "hello")))) (strV "hello"))
;   test lookup with the primitive functions
(check-equal? (lookup '+ top-env) (primV '+))
(check-equal? (lookup '- top-env) (primV '-))
(check-equal? (lookup '* top-env) (primV '*)) 
(check-equal? (lookup '/ top-env) (primV '/))
;   test lookup with functions
(check-equal? (lookup 'x testenv3) (closV (list 'x) (idC 'x) testenv1))
(check-equal? (lookup 'x testenv4) (closV (list 'x) (idC 'x) top-env))
;   test lookup with strings
(check-equal? (lookup 'x testenv5) (strV "hello")) 
;   test lookup with booleans
(check-equal? (lookup 'tv testenv6) (boolV #t))
(check-equal? (lookup 'fv testenv7) (boolV #f)) 
;   test lookup with a variable not found
(check-exn #px"ZODE: Variable not found" (λ () (lookup 'y (list (list 'x (numV 5))))))


; ----- interp test cases -----
; test interp with numbers
(check-equal? (interp (numC 5) top-env) (numV 5))
; test interp with strings
(check-equal? (interp (strC "hello") top-env) (strV "hello"))
; test interp with if expressions
(check-equal? (interp (ifC (idC 'tv) (numC 5) (numC 6)) testenv6) (numV 5))
(check-equal? (interp (ifC (idC 'fv) (numC 5) (numC 6)) testenv7) (numV 6))
; test interp with functions
(check-equal? (interp (lamC (list 'x) (idC 'x)) top-env) (closV (list 'x) (idC 'x) top-env))
; test interp with primitive functions
(check-equal? (interp (appC (idC '+) (list (numC 5) (numC 6))) top-env) (numV 11))
(check-equal? (interp (appC (idC '-) (list (numC 5) (numC 6))) top-env) (numV -1))
(check-equal? (interp (appC (idC '*) (list (numC 5) (numC 6))) top-env) (numV 30))
(check-equal? (interp (appC (idC '/) (list (numC 6) (numC 5))) top-env) (numV 6/5))
; test interp with lambdas
(check-equal? (interp (appC (lamC (list 'x) (appC (idC '+) (list (idC 'x) (idC 'x))))
                            (list (numC 6))) top-env) (numV 12))
(check-equal? (interp (appC (lamC (list 'x) (appC (idC '+) (list (idC 'x) (idC 'x))))
                            (list (numC -6))) top-env) (numV -12))
(check-equal? (interp (appC (lamC (list 'x) (appC (idC '+) (list (idC 'x) (idC 'x))))
                            (list (numC 0))) top-env) (numV 0))

; test errors for interp and lookup 
(check-exn (regexp (regexp-quote "lookup: ZODE: Variable not found 'unknown"))
           (lambda () (interp (idC 'unknown) top-env)))
(check-exn (regexp (regexp-quote "lookup: ZODE: Variable not found 'unknown"))
           (lambda () (interp (appC (idC 'unknown) '()) top-env)))
(check-exn (regexp (regexp-quote "interp: ZODE: Invalid if expression: (ifC (numC 5) (numC 6) (numC 7))"))
           (lambda () (interp (ifC (numC 5) (numC 6) (numC 7)) top-env)))
(check-exn (regexp (regexp-quote "interp: ZODE: Invalid application: (appC (numC 5) (list (numC 6)))"))
           (lambda () (interp (appC (numC 5) (list (numC 6))) top-env)))


; ----- interp-primitive test cases -----
(check-equal? (interp-primitive '+ (list (numC 5) (numC 6)) top-env) (numV 11))
(check-equal? (interp-primitive '- (list (numC 5) (numC 6)) top-env) (numV -1))
(check-equal? (interp-primitive '* (list (numC 5) (numC 6)) top-env) (numV 30))
(check-equal? (interp-primitive '/ (list (numC 6) (numC 5)) top-env) (numV 6/5))
(check-equal? (interp-primitive '<= (list (numC 5) (numC 6)) top-env) (boolV #t))
(check-equal? (interp-primitive 'equal? (list (numC 5) (numC 6)) top-env) (boolV #f))
(check-equal? (interp-primitive 'true (list (numC 5) (numC 6)) top-env) (boolV #t))
(check-equal? (interp-primitive 'false (list (numC 5) (numC 6)) top-env) (boolV #f))
(check-exn (regexp (regexp-quote "interp-primitive: ZODE: Invalid arguments for <= (list (strC \"2\") (numC 6))"))
           (lambda () (interp-primitive '<= (list (strC "2") (numC 6)) top-env))) 
(check-exn (regexp (regexp-quote "interp-primitive: ZODE: Invalid primitive 'invalid-primitive"))
           (lambda () (interp-primitive 'invalid-primitive (list (numC 5) (numC 6)) top-env)))
(check-exn (regexp (regexp-quote "user-error: ZODE: error \"5\""))
           (lambda () (interp-primitive 'error (list (numC 5) (numC 6)) top-env)))
(check-exn (regexp (regexp-quote "division: ZODE: Division by zero"))
           (lambda () (interp-primitive '/ (list (numC 5) (numC 0)) top-env)))

 
; ----- 2num-op test cases -----
(check-exn
 (regexp
  (regexp-quote "num+: ZODE: primitive + expects numbers as arguments, given (strV \"hey\") and (numV 6)"))
 (lambda () (2num-op (strV "hey") (numV 6) +)))

; ----- serialize test cases -----
(check-equal? (serialize (numV 5)) "5")
(check-equal? (serialize (boolV #t)) "true") 
(check-equal? (serialize (boolV #f)) "false")
(check-equal? (serialize (strV "hello")) "\"hello\"")
(check-equal? (serialize (closV (list 'x) (idC 'x) top-env)) "#<procedure>")
(check-equal? (serialize (primV '+)) "#<primop>")


; ----- PARSER TEST CASES ----- ;

; parse test cases desugars locals into lambs? 
(check-equal? (parse 3) (numC 3))
(check-equal? (parse 'x) (idC 'x))
(check-equal? (parse "30") (strC "30"))
(check-equal? (parse '{if : true : 5 : 6})
              (ifC (idC 'true) (numC 5) (numC 6)))
(check-equal? (parse '{f 5 6})
              (appC (idC 'f) (list (numC 5) (numC 6))))
(check-equal? (parse '{if : false : 5 : 6}) 
              (ifC (idC 'false) (numC 5) (numC 6))) 
(check-equal? (parse '{lamb : x : {+ x x}})
              (lamC (list 'x) (appC (idC '+) (list (idC 'x) (idC 'x)))))
(check-exn (regexp (regexp-quote "parse: ZODE: Invalid arguments for operation +"))
           (lambda () (parse '(+ if 4))))
(check-exn (regexp (regexp-quote "parse: ZODE: Duplicate arguments in lambda expression: (x x)"))
           (lambda () (parse '(lamb : x x : 3))))
(check-exn (regexp (regexp-quote "parse: ZODE: Invalid arguments for lambda expression: (3 4 5)"))
           (lambda () (parse '(lamb : 3 4 5 : 6))))
(check-exn (regexp (regexp-quote "parse: ZODE: Invalid if argument (: : 0 : 1)"))
           (lambda () (parse '(if : : 0 : 1))))
(check-exn (regexp (regexp-quote "parse: ZODE: Invalid lamb argument (: i : Hello 31/7 +)"))
           (lambda () (parse '(lamb : i : "Hello" 31/7 +))))
(check-exn (regexp (regexp-quote "parse-clause: ZODE: Invalid clause expression '(: = \"\")"))
           (lambda () (parse '(locals : : = "" : "World"))))
(check-exn (regexp (regexp-quote "parse-clause: ZODE: Invalid clause expression '(: = \"\")"))
           (lambda () (parse '(locals : x = 2 : : = "" : "World"))))


; test cases for top-interp               
(check-equal? (top-interp '{+ 5 6}) "11")
(check-equal? (top-interp '{{lamb : x : {+ x x}} 2}) "4")
(check-equal? (top-interp (quote (if : true : + : -))) "#<primop>")
(check-exn
 (regexp
  (regexp-quote
   "interp: ZODE: Invalid number of arguments: (appC (lamC '() (numC 9)) (list (numC 17)))"))
 (lambda () (top-interp '((lamb : : 9) 17))))
(check-equal? (top-interp (quote ((lamb : seven : (seven)) 
                    ((lamb : minus :(lamb : : (minus (+ 3 10) (* 2 3))))
                     (lamb : x y : (+ x (* -1 y))))))) "7")

; test cases for locals
(check-exn (regexp (regexp-quote "parse-clause: ZODE: Invalid clause expression"))
           (lambda () (parse '{locals : z = : y = 98 : {+ z y}})))
(check-exn (regexp (regexp-quote "parse: ZODE: Duplicate arguments in lambda expression: (z z)"))
           (lambda () (parse '(locals : z = (lamb : : 3) : z = 9 : (z)))))
(check-exn (regexp (regexp-quote "parse: ZODE: Invalid locals argument (: x = 5 :)"))
           (lambda () (parse '(locals : x = 5 :))))
(check-equal? (parse '{locals : z = {+ 9 14} : y = 98 : {+ z y}})
             (appC (lamC '(z y) (appC (idC '+) (list (idC 'z) (idC 'y))))
                  (list (appC (idC '+) (list (numC 9) (numC 14))) (numC 98))))
(check-equal? (parse '{locals : x = 2 : y = 6 : {+ x y}})
            (appC (lamC '(x y) (appC (idC '+) (list (idC 'x) (idC 'y))))
                 (list (numC 2) (numC 6)))) 
 