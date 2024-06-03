#lang typed/racket
(require typed/rackunit)

;; Failed 8 handin errors still. Struggling with appC in type-check,
;; when f is a function name from locals (f = ....) it types checks f,
;; which won't be in the type env. Also don't have type-check done for locals.


;; Assignment 7

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
(define-type ExprC (U numC idC strC ifC locals locals-rec lamC appC))                 
(tstruct numC ([n : Real]))                           
(tstruct idC ([name : Symbol]))                           
(tstruct strC ([str : String]))
(tstruct ifC ([test : ExprC] [then : ExprC] [else : ExprC]))
(tstruct locals ([bindings : (Listof Clause)] [body : ExprC])) 
(tstruct locals-rec ([id : Symbol] [lamdef : lamC] [expr : ExprC]))
;(tstruct lamC ([args : (Listof Symbol)] [body : ExprC]))
(tstruct lamC ([types : (Listof Ty)] [args : (Listof Symbol)] [ret-type : (Option Ty)] [expr : ExprC])) ; lamb-def
(tstruct appC ([f : ExprC] [args : (Listof ExprC)])) 

; Define the Clause: inside locals... ex. add6 = {curradd 6} :
; (tstruct Clause ([id : Symbol] [expr : ExprC]))
(tstruct Clause ([type : Ty] [id : Symbol] [expr : ExprC]))

; Define our value types -> represents an evaluated expression
(define-type Value (U numV boolV strV closV primV)) 
(tstruct boolV ([b : (U #t #f)]))                  
(tstruct strV ([s : String]))
(tstruct closV ([args : (Listof Symbol)] [body : ExprC] [env : Env]))
(tstruct primV ([p : Symbol]))                     
(tstruct numV ([n : Real]))                      

; Define our env and top-env
(define-type Env (Listof (List Symbol Value)))
(define top-env (list (list '+ (primV '+))
                      (list '- (primV '-))
                      (list '* (primV '*))
                      (list '/ (primV '/))
                      (list '<= (primV '<=))
                      (list 'num-eq? (primV 'num-eq?))
                      (list 'str-eq? (primV 'str-eq?))
                      (list 'true (boolV #t))
                      (list 'false (boolV #f))
                      (list 'error (primV 'error))
                      ))

; Define Type definitions
(define-type Ty (U 'num 'bool 'str fun-ty))
(tstruct fun-ty ([args : (Listof Ty)] [ret : Ty]))

;; Type Environment
(define-type TEnv (Listof (List Symbol Ty)))
(define base-tenv
  (list
   (list '+ 'num)
   (list '- 'num)
   (list '* 'num)
   (list '/ 'num)
   (list '<= 'bool)
   (list 'num-eq? 'bool)
   (list 'str-eq? 'bool)
   (list 'substring 'str)
   (list 'true 'bool)
   (list 'false 'bool)))

;(define base-tenv
 ; (list
  ; (list '+ (fun-ty (list 'num 'num) 'num))
  ; (list '- (fun-ty (list 'num 'num) 'num))
  ; (list '* (fun-ty (list 'num 'num) 'num))
  ; (list '/ (fun-ty (list 'num 'num) 'num))
  ; (list '<= 'bool)
  ; (list 'num-eq? (fun-ty (list 'num 'num) 'bool))
  ; (list 'str-eq? (fun-ty (list 'str 'str) 'bool))
  ; (list 'substring (fun-ty (list 'str 'num 'num) 'str))
  ; (list 'true 'bool)
  ; (list 'false 'bool)))


;------------------------------ ;
; ------ MAIN FUNCTIONS ------- ;
; ----------------------------- ;

; top-interp
; PURPOSE: evaluate a program
(: top-interp (Sexp -> String))
(define (top-interp s)
  (define parsed-s (parse s))
  ;(display "\nparsed-s: ") (displayln parsed-s)
  (define type-checked (type-check parsed-s base-tenv))
  ;(display "typed-checked: ") (displayln type-checked)
  (define interp-s (interp parsed-s top-env))
  ;(display "interp-s: ") (displayln interp-s)
  (serialize interp-s)) 

 
; serialize 
;   PURPOSE:  convert a value to a string
(: serialize (Value -> String))
(define (serialize v)
  (match v
    [(numV n) (~v n)]
    [(boolV b) (if b "true" "false")]
    [(strV s) (~v s)]
    [(closV arg body _) "#<procedure>"]
    [(primV p) "#<primop>"]))


; parse
; PURPOSE : parse S-expressions into ExprC's
(: parse (Sexp -> ExprC))
(define (parse s)
  (match s
    [(? real? s) (numC s)]                           
    [(? symbol? s) (idC s)]
    [(? string? s) (strC s)]
    [(list 'if ': test ': then ': else) (ifC (parse test) (parse then) (parse else))]
    [(list 'locals ': clauses ... ': body) 
     (parse-locals s)]
    ;[(list 'locals-rec ': id '= lam-def ': expr) 
    ; (define parsed-lam (parse lam-def))
     ;(if (lamC? parsed-lam)
      ;   (locals-rec (cast id Symbol) parsed-lam (parse expr))
       ;  (error 'parse "ZODE: Expected a lambda expression in local-rec"))]
    [(list 'lamb ': args ... '-> ret-type ': body)
     (parse-lamC s)]
    [(list f args ...)  
     (define parsed-args (map (lambda ([arg : Sexp]) (parse arg)) args))
     (match f
       [(or '+ '- '* '/) ; Check if f is a mathematical operation
        (cond
          [(check-key-word parsed-args)
           (appC (parse f) parsed-args)]
          [else (error 'parse "ZODE: Invalid arguments for operation ~a" f)])]
       ['locals (error 'parse "ZODE: Invalid locals argument ~a" args)]
       ['if (error 'parse "ZODE: Invalid if argument ~a" args)]
       ['lamb (error 'parse "ZODE: Invalid lamb argument ~a" args)]
       [else (appC (parse f) parsed-args)])]))  


; interp
; PURPOSE:  turn ExprC's from parse into values and evaluate
(: interp (ExprC Env -> Value))
(define (interp e env)
  (match e                                                                     
    [(numC n) (numV n)]  
    [(idC x) (lookup x env)] 
    [(strC s) (strV s)] 
    [(ifC test then els) (match (interp test env)
                           [(boolV #t) (interp then env)]
                           [(boolV #f) (interp els env)]
                           [else (error 'interp "ZODE: Invalid if expression: ~e" e)])]
    [(lamC types args ret-type body)
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


; type-check
; PURPOSE: type-check an expression
(: type-check (ExprC TEnv -> Ty))
(define (type-check e tenv)
  (match e
    [(numC _) 'num]
    [(idC _) (lookup-type e tenv)]
    [(strC _) 'str]
    [(ifC test then els)
     (let ([test-type (type-check test tenv)]
           [then-type (type-check then tenv)]
           [else-type (type-check els tenv)])
       (if (and (equal? test-type 'bool) (equal? then-type else-type))
           then-type
           (error 'type-check "ZODE: Invalid types in if expression")))]
    ;[(locals-rec id lamdef expr) (displayln "implement local-rec type check") 'num] ; NEED TO IMPLEMENT
    [(lamC types args ret-type body)
     (cond
       [(equal? ret-type #f) (type-check body tenv)]
       [else ret-type])]
    [(appC f args)
     (type-check f tenv)])) 



; ----------------------------- ;
; ------- TYPE FUNCTIONS ------ ;
; ----------------------------- ;

; parse-type
; PURPOSE: Parse Sexp into Ty
(: parse-type (Sexp -> Ty))
(define (parse-type s)
  (match s
    ['num 'num]
    ['bool 'bool] 
    ['str 'str]
    [(list args ... '-> ret)
     (define parsed-args (map (lambda ([arg : Sexp]) (parse-type arg)) (cast args (Listof Sexp))))
     (fun-ty parsed-args (parse-type ret))]
    [else (error 'parse-type "ZODE: Invalid type ~a" s)]))

(: lookup-type (ExprC TEnv -> Ty))
(define (lookup-type x tenv)
  (match x
    [(idC s)
     (cond
       [(empty? tenv) (error 'lookup-type "ZODE: Variable not found ~e" x)]
       [(equal? s (first (first tenv))) (second (first tenv))]
       [else (lookup-type x (rest tenv))])]
    [else (error 'lookup-type "ZODE: Variable not a symbol ~e" x)])) 
 


; ----------------------------- ;
; -- INTERP HELPER FUNCTIONS -- ; 
; ----------------------------- ;
 
; lookup 
; PURPOSE: lookup the value of x in the environment env
(: lookup (Symbol Env -> Value))
(define (lookup x env)
  (cond
    [(empty? env) (error 'lookup "ZODE: Variable not found ~e" x)]
    [(equal? x (first (first env))) (second (first env))]
    [else (lookup x (rest env))])) 

; extend-env
; PURPOSE: extend the environment env with the definitions in another environment.
(: extend-env ((Listof Symbol) (Listof Value) Env -> Env))
(define (extend-env params argval env)
  (define new-bindings
    (map (lambda (param [arg : Value])
           (list param arg))
         params argval))
  (cast (append new-bindings env) Env)) 
  

; interp-primitive
;   PARAMS:   p:    Symbol          the primitive to interpret
;             args: (Listof Value)  the arguments to the primitive
;   RETURNS:  Value
;   PURPOSE:  helper for interp to interpret primitives
(: interp-primitive (Symbol (Listof ExprC) Env -> Value))
(define (interp-primitive p exprs env)
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
    ['num-eq? (boolV (equal? (interp (first exprs) env) (interp (second exprs) env)))]
    ['str-eq? (boolV (equal? (interp (first exprs) env) (interp (second exprs) env)))] 
    ['true (boolV #t)] 
    ['false (boolV #f)] 
    ['error (error 'user-error "ZODE: error ~e" (serialize (interp (first exprs) env)))]
    [else (error 'interp-primitive "ZODE: Invalid primitive ~e" p)]))


; 2num-op
;   PARAMS:   l:    Value           the left operand
;             r:    Value           the right operand
;             operator: (Number Number -> Number) the operator to apply
;   RETURNS:  Value
;   PURPOSE:  helper for interp-primitive to apply a binary operator to two numbers
(: 2num-op (Value Value (Real Real -> Real) -> Value))
(define (2num-op l r operator) 
  (cond
    [(and (numV? l) (numV? r))
     (numV (operator (numV-n l) (numV-n r)))] 
    [else
     (error 'num+ "ZODE: primitive + expects numbers as arguments, given ~e and ~e" l r)]))



; ---------------------------- ; 
; -- PARSE HELPER FUNCTIONS -- ;
; ---------------------------- ;

; check-key-word
; PURPOSE: helper function to check for key word if
(: check-key-word ((Listof ExprC) -> Boolean))
(define (check-key-word lst)
  (cond
    [(empty? lst) #t]
    [(or (equal? (first lst) (idC 'if))
         (equal? (first lst) (idC 'locals))
         (equal? (first lst) (idC 'local-rec))
         (equal? (first lst) (idC '=))
         (equal? (first lst) (idC '->))
         (equal? (first lst) (idC 'lamb)))
     #f]
    [else (check-key-word (rest lst))]))

; parse-lamC
; PURPOSE: parse lamC from lamb statement
(: parse-lamC (Sexp -> lamC))
(define (parse-lamC s)
  (match s
    [(list 'lamb ': args ... '-> ret-type ': body)
     (define vars-and-types (map (lambda ([arg : Sexp])
                                   (match arg
                                     [(list ty var)
                                      (list ty var)]
                                     [else (error 'parse-lamC "Invalid argument: ~a" arg)]))
                                 (cast args (Listof Sexp))))
     (define variables (map (lambda ([tv : (List Sexp Sexp)]) (second tv))
                            (cast vars-and-types (Listof (List Sexp Sexp)))))
     (define types (map (lambda ([tv : (List Sexp Sexp)]) (first tv))
                        (cast vars-and-types (Listof (List Sexp Sexp)))))
     (define parsed-types (map (lambda ([t : Sexp]) (parse-type t))
                               (cast types (Listof Sexp))))
     (if (andmap symbol? variables)
         (if (equal? variables (remove-duplicates variables))
             (lamC parsed-types (cast variables (Listof Symbol))
                   (parse-type ret-type) (parse body))
             (error 'parse "ZODE: Duplicate arguments in lambda expression: ~a" args))
         (error 'parse "ZODE: Invalid arguments for lambda expression: ~a" args))]))

; parse-locals
; PURPOSE: parse locals 
(: parse-locals (Sexp -> appC))
(define (parse-locals s)
  (match s
    [(list 'locals ': clauses ... ': body) 
     (define parsed-clauses (parse-clause (cast clauses Sexp)))
     (define parsed-body (parse body))
     (define ids (cast (map (lambda ([clause : Clause]) (Clause-id clause)) parsed-clauses) (Listof Symbol)))
     (define types (cast (map (lambda ([clause : Clause]) (Clause-type clause)) parsed-clauses) (Listof Ty)))
     (if (equal? ids (remove-duplicates ids))
         (appC (lamC types ids #f parsed-body)
               (map (lambda ([c : Clause]) (Clause-expr c)) parsed-clauses))
         (error 'parse "ZODE: Duplicate arguments in lambda expression: ~a" ids))]))
 
; parse-clause
; PURPOSE:  parse clauses from locals statement
(: parse-clause (Sexp -> (Listof Clause)))
(define (parse-clause s)
  (match s
    [(list ty (? symbol? id) '= expr)
     (list (Clause (parse-type ty) id (parse expr)))]
    [(list ty (? symbol? id) '= expr ': rest ...)
     (cons (Clause (parse-type ty) id (parse expr)) (parse-clause rest))] 
    [else (error 'parse-clause "ZODE: Invalid clause expression ~e" s)]))
 

(top-interp '(locals : (num num num num num -> num)
                     f = (lamb : (num a) (num b) (num c) (num d) (num e) -> num
                               : (+ (+ a b) (+ (- 0 c) (+ d e))))
                     : (f 10 9 8 7 6)))

; ---------------------- ;
; ----- TEST CASES ----- ; 
; ---------------------- ;

; ----- defs for test cases ----- ; 
; test parsed functions
(define testpfunc0 (list (Clause 'num 'curradd (lamC '(num) '(x) 'num (appC (idC '+) (list (idC 'x) (idC 'x)))))))
(define testpfunc1 (list (Clause 'num 'add6 (appC (idC 'curradd) (list (numC 6))))))

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
(check-equal? (interp (lamC '(num) '(x) 'num (idC 'x)) top-env) (closV (list 'x) (idC 'x) top-env))
; test interp with primitive functions
(check-equal? (interp (appC (idC '+) (list (numC 5) (numC 6))) top-env) (numV 11))
(check-equal? (interp (appC (idC '-) (list (numC 5) (numC 6))) top-env) (numV -1))
(check-equal? (interp (appC (idC '*) (list (numC 5) (numC 6))) top-env) (numV 30))
(check-equal? (interp (appC (idC '/) (list (numC 6) (numC 5))) top-env) (numV 6/5))
; test interp with lambdas
(check-equal? (interp (appC (lamC '(num) '(x) 'num (appC (idC '+) (list (idC 'x) (idC 'x))))
                            (list (numC 6))) top-env) (numV 12))
(check-equal? (interp (appC (lamC '(num) '(x) 'num (appC (idC '+) (list (idC 'x) (idC 'x))))
                            (list (numC -6))) top-env) (numV -12))
(check-equal? (interp (appC (lamC '(num) '(x) 'num (appC (idC '+) (list (idC 'x) (idC 'x))))
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
(check-equal? (interp-primitive 'num-eq? (list (numC 5) (numC 6)) top-env) (boolV #f))
(check-equal? (interp-primitive 'str-eq? (list (strC "hi") (strC "hi")) top-env) (boolV #t))
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

; Type test cases
(check-equal? (parse-type '(str num -> str)) (fun-ty '(str num) 'str))
(check-exn (regexp (regexp-quote "parse-type: ZODE: Invalid type invalid"))
           (lambda () (parse-type 'invalid)))
(check-exn (regexp (regexp-quote "parse-type: ZODE: Invalid type (num ->)"))
           (lambda () (parse-type '(num ->))))
(check-exn (regexp (regexp-quote "lookup-type: ZODE: Variable not found (idC 'foo)"))
           (lambda () (lookup-type (idC 'foo) base-tenv)))
(check-exn (regexp (regexp-quote "lookup-type: ZODE: Variable not a symbol (strC \"x\")"))
           (lambda () (lookup-type (strC "x") base-tenv)))

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
(check-equal? (parse '{lamb : [num x] -> num : {+ x x}})
              (lamC '(num) '(x) 'num (appC (idC '+) (list (idC 'x) (idC 'x)))))
(check-equal? (parse '{lamb : [str x] -> bool : {str-eq? x "hi"}})
              (lamC '(str) '(x) 'bool (appC (idC 'str-eq?) (list (idC 'x) (strC "hi")))))
(check-exn (regexp (regexp-quote "parse: ZODE: Invalid arguments for operation +"))
           (lambda () (parse '(+ if 4))))
(check-exn (regexp (regexp-quote "parse: ZODE: Duplicate arguments in lambda expression: ((num x) (num x))"))
           (lambda () (parse '(lamb : [num x] [num x] -> num : 3)))) 
(check-exn (regexp (regexp-quote "parse: ZODE: Invalid arguments for lambda expression: ((num 3) (num 4) (num 5))"))
           (lambda () (parse '(lamb : [num 3] [num 4] [num 5] -> num : 6))))
(check-exn (regexp (regexp-quote "parse: ZODE: Invalid if argument (: : 0 : 1)"))
           (lambda () (parse '(if : : 0 : 1))))
(check-exn (regexp (regexp-quote "parse: ZODE: Invalid lamb argument (: (str i) -> str : Hello 31/7 +)"))
           (lambda () (parse '(lamb : [str i] -> str : "Hello" 31/7 +))))
(check-exn (regexp (regexp-quote "parse-clause: ZODE: Invalid clause expression '(: = \"\")"))
          (lambda () (parse '(locals : : = "" : "World"))))
(check-exn (regexp (regexp-quote "parse-clause: ZODE: Invalid clause expression '(: = \"\")"))
          (lambda () (parse '(locals : num x = 2 : : = "" : "World"))))
(check-exn (regexp (regexp-quote "parse-clause: ZODE: Invalid clause expression '(: num x = 5)"))
          (lambda () (parse-clause '(: num x = 5))))


; test cases for top-interp 
(check-equal? (top-interp '5) "5")
(check-equal? (top-interp "hi") "\"hi\"")
(check-equal? (top-interp '{+ 5 6}) "11")
(check-equal? (top-interp '{{lamb : [num x] -> num : {+ x x}} 2}) "4")
(check-equal? (top-interp (quote (if : true : + : -))) "#<primop>")
(check-equal? (top-interp '{locals : num z = {+ 9 14} : num y = 98 : {+ z y}}) "121")
(check-exn
 (regexp
  (regexp-quote
   "parse-lamC: Invalid argument: ()"))
 (lambda () (top-interp '((lamb : [] -> num : 9) 17))))
(check-exn
 (regexp
  (regexp-quote
   "interp: ZODE: Invalid number of arguments: "))
 (lambda () (top-interp '((lamb : [num x] [num y] -> num : 9) 17))))
(check-exn
 (regexp
  (regexp-quote
   "type-check: ZODE: Invalid types in if expression"))
 (lambda () (top-interp '(if : 7 : + : -))))


; test cases for locals 
(check-exn (regexp (regexp-quote "parse-clause: ZODE: Invalid clause expression"))
          (lambda () (parse '{locals : num z = : num y = 98 : {+ z y}})))
(check-exn (regexp (regexp-quote "parse: ZODE: Duplicate arguments in lambda expression: (z z)"))
          (lambda () (parse '(locals : num z = 10 : num z = 9 : (z)))))
(check-exn (regexp (regexp-quote "parse: ZODE: Invalid locals argument (: num x = 5 :)"))
          (lambda () (parse '(locals : num x = 5 :)))) 
(check-equal? (parse '{locals : num z = {+ 9 14} : num y = 98 : {+ z y}})
            (appC (lamC '(num num) '(z y) #f (appC (idC '+) (list (idC 'z) (idC 'y))))
                (list (appC (idC '+) (list (numC 9) (numC 14))) (numC 98))))
(check-equal? (parse '{locals : num x = 2 : num y = 6 : {+ x y}})
           (appC (lamC '(num num) '(x y) #f (appC (idC '+) (list (idC 'x) (idC 'y))))
               (list (numC 2) (numC 6))))

;(top-interp '{locals-rec
 ;: square-helper = {lamb : [num n] -> num
  ;                       : {if : {<= n 0} 
   ;                            : 0
    ;                           : {+ n {square-helper {- n 2}}}}}
 ;: {locals : {num -> num} square = {lamb : [num n] -> num
  ;                                       : {square-helper {- {* 2 n} 1}}}
   ;        : {square 13}}})


