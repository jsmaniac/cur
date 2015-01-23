#lang s-exp "redex-core.rkt"
(require "sugar.rkt")
(provide define-relation)

(begin-for-syntax
  (define-syntax-class dash
    (pattern x:id
           #:fail-unless (regexp-match #rx"-+" (symbol->string (syntax-e #'x)))
           "Invalid dash"))

  (define-syntax-class decl (pattern (x:id (~datum :) t:id)))

  ;; TODO: Automatically infer decl ... by binding all free identifiers?
  (define-syntax-class inferrence-rule
    (pattern (d:decl ...
              x*:expr ...
              line:dash lab:id
              (name:id y* ...))
              #:with rule #'(lab : (forall* d ...
                                     (->* x* ... (name y* ...)))))))
(define-syntax (define-relation syn)
  (syntax-parse syn
    [(_ (n:id types* ...) rules:inferrence-rule ...)
     #:fail-unless (andmap (curry equal? (length (syntax->datum #'(types* ...))))
                           (map length (syntax->datum #'((rules.y* ...)
                                                          ...))))
     "Mismatch between relation declared and relation definition"
     #:fail-unless (andmap (curry equal? (syntax->datum #'n))
                           (syntax->datum #'(rules.name ...)))
     "Mismatch between relation declared name and result of inference rule"
      #`(data n : (->* types* ... Type)
          rules.rule ...)]))

(begin-for-syntax
  (require racket/syntax)
  (define (new-name . id*)
    (apply format-id #f (for/fold ([str "~a"])
                                  ([_ (cdr id*)])
                          (string-append str "-~a")) (map syntax->datum id*)))

  (define (fresh-name id)
    (datum->syntax id (gensym (syntax->datum id)))))

(module+ test
  (begin-for-syntax
    (require rackunit)
    (define (check-id-equal? v1 v2)
      (check-equal?
        (syntax->datum v1)
        (syntax->datum v2)))
    (define (check-id-match? v1 v2)
       (check-regexp-match
         v1
         (symbol->string (syntax->datum v2))))
    (check-id-match?
      #px"term\\d+"
      (fresh-name #'term))
    (check-id-equal?
      #'stlc-lambda
      (new-name #'stlc #'lambda))
    (check-id-match?
      #px"stlc-term\\d+"
      (new-name #'stlc (fresh-name #'term)))))

(begin-for-syntax
  (define lang-name (make-parameter #'name))
  (define nts (make-parameter (make-immutable-hash)))

  (define-syntax-class nt
    (pattern e:id #:fail-unless (hash-has-key? (nts) (syntax->datum #'e)) #f
             #:attr name (hash-ref (nts) (syntax->datum #'e))
             #:attr type (hash-ref (nts) (syntax->datum #'e))))

  (define (flatten-args arg arg*)
    (for/fold ([ls (syntax->list arg)])
              ([e (syntax->list arg*)])
      (append ls (syntax->list e))))

  (define-syntax-class (right-clause type)
    #;(pattern (~datum var)
             #:attr clause-context #`(#,(new-name (lang-name) #'var) :
                                      (-> #,(hash-ref (nts) 'var) #,(hash-ref (nts) type)))
             #:attr name #'var
             #:attr arg-context #'(var))
    (pattern e:nt
             #:attr clause-context #`(#,(new-name #'e.name #'->
                                                  (hash-ref (nts) type)) :
                                      (-> e.type #,(hash-ref (nts) type)))
             #:attr name (fresh-name #'e.name)
             #:attr arg-context #'(e.type))
    (pattern x:id
             #:attr clause-context #`(#,(new-name (lang-name) #'x) :
                                      #,(hash-ref (nts) type))
             #:attr name (new-name (lang-name) #'x)
             #:attr arg-context #'())
    (pattern ((~var e (right-clause type)) (~var e* (right-clause type)) ...)
             #:attr name (fresh-name #'e.name)
             #:attr clause-context #`(e.name : (->* #,@(flatten-args #'e.arg-context #'(e*.arg-context ...))
                                                    #,(hash-ref (nts) type)))
             #:attr arg-context #`(#,@(flatten-args #'e.arg-context #'(e*.arg-context ...)))))

  (define-syntax-class (right type)
    (pattern ((~var r (right-clause type)) ...)
             #:attr clause #'(r.clause-context ...)))

  #;(define-syntax-class left
    (pattern (type:id (nt*:id ...+))
             #:do ))

  (define-syntax-class nt-clauses
    (pattern ((type:id (nt*:id ...+)
              (~do (nts (for/fold ([ht (nts)])
                                  ([nt (syntax->datum #'(type nt* ...))])
                          (hash-set ht nt (new-name (lang-name) #'type)))))
              (~datum ::=)
              . (~var rhs* (right (syntax->datum #'type)))) ...)
             #:with defs (with-syntax ([(name* ...)
                                        (map (λ (x) (hash-ref (nts) x))
                                             (syntax->datum #'(type ...)))])
                           #`((data name* : Type . rhs*.clause)
                              ...)))))

(define-syntax (define-language syn)
  (syntax-parse syn
    [(_ name:id (~do (lang-name #'name))
        (~do (nts (hash-set (make-immutable-hash) 'var #'var)))
        (~optional (~seq #:vars (x*:id ...)
           (~do (nts (for/fold ([ht (nts)])
                               ([v (syntax->datum #'(x* ...))])
                       (hash-set ht v (hash-ref ht 'var)))))))
        . clause*:nt-clauses)
     (let ([var (hash-ref (nts) 'var)])
       #`(begin
           #,@(if (attribute x*)
                  #`((data #,var : Type (avar : (-> nat #,var))))
                  #'())
           . clause*.defs))]))

; TODO: Not quite working yet. I think it has something to do with
; begin.
(define-language stlc
  #:vars (x)
  (val (v) ::= true false)
  (type (A B) ::= bool (-> A B))
  (term (e) ::= var v (e e) (lambda x A e)))