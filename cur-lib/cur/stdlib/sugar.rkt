#lang s-exp "../cur.rkt"
(provide
  ->
  lambda
  (rename-out
    [-> →]
    [-> forall]
    [-> ∀]
    [lambda λ])
  #%app
  define
  elim
  define-type
  match
  recur
  let

  ;; type-check
  ::

  ;; reflection in syntax
  run
  step
  step-n
  query-type)

(require
  (only-in "../cur.rkt"
    [elim real-elim]
    [#%app real-app]
    [lambda real-lambda]
    [define real-define]))

;; Exceptions and such
(begin-for-syntax
  (define-struct (exn:cur:type exn:cur) () #:transparent)

  (define (raise-cur-type-infer-error name v . other)
    (format
     "~aCur type error;~n  Could not infer any type~n    term: ~a~a"
     (if name (format "~a:" name) "")
     v
     (for/fold ([str ""])
               ([other other])
       (format "~a~n    context: ~a" str other)))))

(begin-for-syntax
  #| TODO
   | Design of "typed" macros for Cur.
   |
   | We can use syntax classes to emulate typed macros. The syntax
   | class calls the type-checker to ensure the term parsed term is
   | well-typed. This *must* not expand the the matched type as a side-effect.
   | Unfortunately, to handle binding, patterns that have variables
   | must thread binding information through while parsing in syntax
   | parse. This would be simple if we had implicit monad syntax for
   | it, but otherwise we must explicitly thread the environment
   | information through the syntax classes. How annoying.
   |
   | Ideas:
   |   Could create a "env" compile-time parameter...
   |   Could expose Gamma, in some way...
   |   Could use Racket namespaces? Might requrie abandoning Redex
   |
   |
   |#
  (define (deduce-type-error term expected)
    (format
     "Expected ~a ~a, but ~a."
     (syntax->datum term)
     expected
     (syntax-parse term
       [x:id
        "seems to be an unbound variable"]
       [_ "could not infer a type."])))

  (define-syntax-class cur-syntax
    (pattern e:expr))

  (define-syntax-class well-typed-cur-term
    (pattern
     e:cur-syntax
     #:attr type (type-infer/syn #'e)
     #:fail-unless (attribute type)
     (raise-cur-type-infer-error #f #'e))))

;; For delaying a type-check until the term is under a binder
;; NB: This is an impressively awesome solution..... need to write something about it.
(define-syntax (delayed-check syn)
  (syntax-parse syn
    [(_ e:well-typed-cur-term) #'e]))

(begin-for-syntax
  (define-syntax-class parameter-declaration
    #:commit
    (pattern
     (name:id (~datum :) ~! type:cur-syntax))

    (pattern
     type:cur-syntax
     ;; NB: Anonymous parameters are not bound in the local env
     #:attr name (format-id #'type "~a" (gensym 'anon-parameter))))

  (define-syntax-class well-typed-parameter-declaration
    #:commit
    (pattern
     (name:id (~datum :) ~! _type:cur-syntax)
     #:attr type #'(delayed-check _type))

    (pattern
     _type:cur-syntax
     ;; TODO: Duplicate code in parameter-declaration
     #:attr type #'(delayed-check _type)
     #:attr name (format-id #'type "~a" (gensym 'anon-parameter))))

  (define-syntax-class well-typed-parameter-list
    (pattern
     (d:well-typed-parameter-declaration ...+)
     #:attr names (attribute d.name)
     #:attr types (attribute d.type))))

;; A multi-arity function type; takes parameter declaration of either
;; a binding (name : type), or type whose name is generated.
;; E.g.
;; (-> (A : Type) A A)

(define-syntax (-> syn)
  (syntax-parse syn
    [(_ d:parameter-declaration ...+ e:cur-syntax)
     #:with ds #'(d ...)
     #:declare ds well-typed-parameter-list
     (foldr (lambda (src name type r)
              (quasisyntax/loc src
                (forall (#,name : #,type) #,r)))
            #'(delayed-check e)
            (syntax->list (attribute ds))
            (attribute ds.names)
            (attribute ds.types))]))

;; TODO: Add forall macro that allows specifying *names*, with types
;; inferred. unlike -> which require types but not names
;; E.g.
;; (forall x (y : Nat) (== Nat x y))

;; TODO: Allows argument-declarations to have types inferred, similar
;; to above TODO forall
(define-syntax (lambda syn)
  (syntax-parse syn
    [(_ d:parameter-declaration ... e:cur-syntax)
     #:with ds #'(d ...)
     #:declare ds well-typed-parameter-list
     (foldr (lambda (src name type r)
              (quasisyntax/loc src
                (real-lambda (#,name : #,type) #,r)))
            #'(delayed-check e)
            (syntax->list (attribute ds))
            (attribute ds.names)
            (attribute ds.types))]))

(begin-for-syntax
  (define-syntax-class forall-type
    (pattern
     ((~literal forall) ~! (parameter-name:id (~datum :) parameter-type) body)))

  (define-syntax-class cur-function
    (pattern
     e:expr
     #:attr type (type-infer/syn #'e)
     #:fail-unless (attribute type)
     (deduce-type-error
      #'e
      "to be a function")
     #:fail-unless (syntax-parse (attribute type)
                     [t:forall-type #t]
                     [_ #f])
     (format
      "Expected ~a to be a function, but inferred type ~a"
      (syntax->datum #'e)
      (syntax->datum (attribute type))))))

(define-syntax (#%app syn)
  (syntax-parse syn
    [(_ f:well-typed-cur-term ~! e:well-typed-cur-term ...+)
     ;; Have to thread each argument through, to handle dependency.
     (for/fold ([type (attribute f.type)])
               ([arg (attribute e)]
                [inferred-type (attribute e.type)])
       (define/syntax-parse expected:forall-type type)
       (define expected-type (attribute expected.parameter-type))
       (unless (type-check/syn? arg expected-type)
         (raise-syntax-error
          '#%app
          (format
           "Expected ~a to have type ~a, but inferred type ~a."
           (syntax->datum arg)
           (syntax->datum expected-type)
           (syntax->datum inferred-type))
          syn
          arg))
       (normalize/syn
        #`(real-app
           (real-lambda (expected.parameter-name : expected.parameter-type)
                        expected.body)
           #,arg)))
     (for/fold ([app (quasisyntax/loc syn
                       (real-app f #,(first (attribute e))))])
               ([arg (rest (attribute e))])
       (quasisyntax/loc arg
         (real-app #,app #,arg)))]))

(define-syntax define-type
  (syntax-rules ()
    [(_ (name (a : t) ...) body)
     (define name (forall (a : t) ... body))]
    [(_ name type)
     (define name type)]))

;; TODO: Allow inferring types as in above TODOs for lambda, forall
(define-syntax (define syn)
  (syntax-case syn ()
    [(define (name (x : t) ...) body)
     (quasisyntax/loc syn
       (real-define name (lambda (x : t) ... body)))]
    [(define id body)
     (quasisyntax/loc syn
       (real-define id body))]))

(define-syntax (elim syn)
  (syntax-parse syn
    [(_ t1 t2 e ...)
     (maybe-cur-apply
      #`(real-elim t1 t2)
      (attribute e))]))

;; Quite fragie to give a syntactic treatment of pattern matching -> eliminator. Replace with "Elimination with a Motive"
(begin-for-syntax
  (define ih-dict (make-hash))

  (define (maybe-cur-apply f ls)
    (if (null? ls)
        f
        #`(#,f #,@ls)))

  (define-syntax-class curried-application
    (pattern
     ((~literal real-app) name:id e:expr)
     #:attr args
     (list #'e))

    (pattern
     ((~literal real-app) a:curried-application e:expr)
     #:attr name #'a.name
     #:attr args
     ;; TODO BUG: repeated appends are not performant; cons then reverse in inductive-type-declaration
     (append
      (attribute a.args)
      (list #'e))))

  (define-syntax-class inductive-type-declaration
    (pattern
     x:id
     #:attr inductive-name
     #'x
     #:attr indices
     '()
     #:attr names
     '()
     #:attr types
     '()
     #:attr decls
     (list #`(#,(gensym 'anon-discriminant) : x))
     #:attr abstract-indices
     values)

    (pattern
     ;; BUG TODO NB: Because the inductive type may have been inferred, it may appear in Curnel syntax, i.e., nested applications starting with dep-app
     ;; Best to ensure it *always* is in Curnel form, and pattern match on that.
     a:curried-application
     #:attr inductive-name
     (attribute a.name)
     #:attr indices
     (attribute a.args)
     #:attr names
     (for/list ([e (attribute indices)])
       (format-id e "~a" (gensym 'anon-index)))
     #:attr types
     ;; TODO: Detect failure, report error/suggestions
     (for/list ([e (attribute indices)])
       (or (type-infer/syn e)
           (raise-syntax-error
            'match
            (format
             "Could not infer type of index ~a"
             e)
            e)))
     #:attr decls
     (append
      (for/list ([name (attribute names)]
                 [type (attribute types)]
                 [src (attribute indices)])
        (quasisyntax/loc src
          (#,name : #,type)))
      (list
       (quasisyntax/loc #'a
         (#,(gensym 'anon-discriminant) : (inductive-name #,@(attribute names))))))
     #:attr abstract-indices
     (lambda (return)
       ;; NB: unhygenic
       ;; Normalize at compile-time, for efficiency at run-time
       (normalize/syn
        #:local-env
        (for/fold ([d (make-immutable-hash)])
                  ([name (attribute names)]
                   [type (attribute types)])
          (dict-set d name type))
        (maybe-cur-apply
         #`(lambda
               ;; TODO: utteraly fragile; relines on the indices being referred to by name, not computed
               ;; works only for simple type familes and simply matches on them
               #,@(for/list ([name (attribute indices)]
                             [type (attribute types)])
                    #`(#,name : #,type))
             #,return)
         (attribute names))))))

  ;; todo: Support just names, inferring types
  (define-syntax-class match-declaration
    (pattern
     ;; TODO: Use parameter-declaration defined earlier
     (name:id (~datum :) type:expr)
     #:attr decl
     #'(name : type)))

  (define-syntax-class match-prepattern
    ;; TODO: Check that x is a valid constructor for the inductive type
    (pattern
     x:id
     #:attr local-env
     '()
     #:attr decls
     '()
     #:attr types
     '()
     #:attr names
     '())

    (pattern
     (x:id d:match-declaration ...+)
     #:attr local-env
     (for/fold ([d (make-immutable-hash)])
               ([name (attribute d.name)]
                [type (attribute d.type)])
       (dict-set d name type))
     #:attr decls
     (attribute d.decl)
     #:attr names
     (attribute d.name)
     #:attr types
     (attribute d.type)))

  (define-syntax-class (match-pattern D motive)
    (pattern
     d:match-prepattern
     #:attr decls
     ;; Infer the inductive hypotheses, add them to the pattern decls
     ;; and update the dictionarty for the recur form
     (call-with-values
      (thunk
       (for/fold ([decls (attribute d.decls)]
                  [local-env (attribute d.local-env)])
                 ([type-syn (attribute d.types)]
                  [name-syn (attribute d.names)]
                  [src (attribute d.decls)]
                  ;; NB: Non-hygenic
                  ;; BUG TODO: This fails when D is an inductive applied to arguments...
                  #:when (cur-equal? type-syn D))
         (define/syntax-parse type:inductive-type-declaration (cur-expand type-syn))
         (let ([ih-name (quasisyntax/loc src #,(format-id name-syn "ih-~a" name-syn))]
               ;; Normalize at compile-time, for efficiency at run-time
               [ih-type (normalize/syn #:local-env local-env
                                       (maybe-cur-apply motive
                                                        (append (attribute type.indices) (list name-syn))))])
           (dict-set! ih-dict (syntax->datum name-syn) ih-name)
           (values (append decls (list #`(#,ih-name : #,ih-type)))
                   (dict-set local-env ih-name ih-type)))))
      (lambda (x y) x))))

  (define-syntax-class (match-preclause maybe-return-type)
    (pattern
     (p:match-prepattern b:expr)
     #:attr return-type
     ;; TODO: Check that the infered type matches maybe-return-type, if it is provied
     (or maybe-return-type
         ;; Ignore errors when trying to infer this type; other attempt might succeed
         (with-handlers ([values (lambda _ #f)])
           (type-infer/syn #:local-env (attribute p.local-env) #'b)))))

  (define-syntax-class (match-clause D motive)
    (pattern
     ((~var p (match-pattern D motive))
      ;; TODO: nothing more advanced?
      b:expr)
     #:attr method
     (quasisyntax/loc #'p
       #,(if (null? (attribute p.decls))
         #'b
         #`(lambda #,@(attribute p.decls) b))))))

(define-syntax (recur syn)
  (syntax-case syn ()
    [(_ id)
     (dict-ref
      ih-dict
      (syntax->datum #'id)
      (lambda ()
        (raise-syntax-error
         'match
         ;; TODO: Detect when inside a match to provide better error
         (format
          "Cannot recur on ~a. Ether not inside a match or ~a is not an inductive argument."
          (syntax->datum #'id)
          (syntax->datum #'id))
         syn)))]))

(define-syntax (match syn)
  (syntax-parse syn
    [(_ d
        ~!
        (~optional
         (~seq #:in ~! t)
         #:defaults
         ([t (or (type-infer/syn #'d)
                 (raise-syntax-error
                  'match
                  "Could not infer discrimnant's type. Try using #:in to declare it."
                  syn))]))
        (~optional (~seq #:return ~! maybe-return-type))
        (~peek (~seq (~var prec (match-preclause (attribute maybe-return-type))) ...))
        ~!
        (~parse D:inductive-type-declaration (cur-expand (attribute t)))
        (~bind (return-type (ormap values (attribute prec.return-type))))
        (~do (unless (attribute return-type)
               (raise-syntax-error
                'match
                "Could not infer return type. Try using #:return to declare it."
                syn)))
        ;; BUG TODO: return-type is inferred with the indexes of the branches, but those must be abstracted in the motive...
        ;; Replace each of the D.indicies with the equivalent name from D.decls
        (~bind (motive (quasisyntax/loc syn
                         (lambda #,@(attribute D.decls)
                           #,((attribute D.abstract-indices) (attribute return-type))))))
        (~var c (match-clause (attribute D) (attribute motive))) ...)
     ;; TODO: Make all syntax extensions type check, report good error, rather than fail at Curnel
     (quasisyntax/loc syn
       (elim
        D.inductive-name
        #,(or
           (type-infer/syn (attribute return-type))
           (raise-syntax-error
            'match
            "Could not infer type of motive. Sorry, you'll have to use elim."
            syn))
        motive
        c.method ...
        #,@(attribute D.indices)
        d))]))

(begin-for-syntax
  (define-syntax-class let-clause
    (pattern
      (~or (x:id e) ((x:id (~datum :) t) e))
      #:attr id #'x
      #:attr expr #'e
      #:attr type (cond
                    [(attribute t)
                     ;; TODO: Code duplication in ::
                     (unless (type-check/syn? #'e #'t)
                       (raise-syntax-error
                         'let
                         (format "Term ~a does not have expected type ~a. Inferred type was ~a"
                                 (cur->datum #'e) (cur->datum #'t) (cur->datum (type-infer/syn #'e)))
                         #'e (quasisyntax/loc #'x (x e))))
                     #'t]
                    [(type-infer/syn #'e)]
                    [else
                      (raise-syntax-error
                        'let
                        "Could not infer type of let bound expression"
                        #'e (quasisyntax/loc #'x (x e)))]))))
(define-syntax (let syn)
  (syntax-parse syn
    [(let (c:let-clause ...) body)
     #'((lambda (c.id : c.type) ... body) c.e ...)]))

;; Normally type checking will only happen if a term is actually used. This forces a term to be
;; checked against a particular type.
(define-syntax (:: syn)
  (syntax-case syn ()
    [(_ pf t)
     (begin
       ;; TODO: Code duplication in let-clause pattern
       (unless (type-check/syn? #'pf #'t)
         (raise-syntax-error
           '::
           (format "Term ~a does not have expected type ~a. Inferred type was ~a"
                   (cur->datum #'pf) (cur->datum #'t) (cur->datum (type-infer/syn #'pf)))
           syn))
       #'(void))]))

(define-syntax (run syn)
  (syntax-case syn ()
    [(_ expr) (normalize/syn #'expr)]))

(define-syntax (step syn)
  (syntax-case syn ()
    [(_ expr)
     (let ([t (step/syn #'expr)])
       (displayln (cur->datum t))
       t)]))

(define-syntax (step-n syn)
  (syntax-case syn ()
    [(_ n expr)
     (for/fold
       ([expr #'expr])
       ([i (in-range (syntax->datum #'n))])
       #`(step #,expr))]))

(define-syntax (query-type syn)
  (syntax-case syn ()
    [(_ term)
     (begin
       (printf "\"~a\" has type \"~a\"~n" (syntax->datum #'term) (syntax->datum (type-infer/syn #'term)))
       ;; Void is undocumented and a hack, but sort of works
       #'(void))]))
