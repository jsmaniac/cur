#lang racket/base
;; This module just provide module language sugar over the redex model.

(require
  "redex-core.rkt"
  redex/reduction-semantics
  racket/provide-syntax
  (for-syntax
    (except-in racket import)
    syntax/parse
    racket/syntax
    (except-in racket/provide-transform export)
    racket/require-transform
    "redex-core.rkt"
    redex/reduction-semantics))
(provide
  ;; Basic syntax
  for-syntax
  only-in
  except-in
  all-defined-out
  rename-in
  rename-out
  prefix-out
  prefix-in
  submod
  #%module-begin
  (rename-out
    [dep-module+ module+]
    [dep-provide provide]
    [dep-require require]

    [dep-lambda lambda]
    [dep-app #%app]

    [dep-forall forall]

    [dep-inductive data]

    [dep-elim elim]

    [dep-top #%top]
    [dep-top-interaction #%top-interaction]

    ;      [dep-datum #%datum]
    [dep-define define]
    [dep-void void])
  begin
  Type
  ;; DYI syntax extension
  define-syntax
  begin-for-syntax
  define-for-syntax
  syntax-case
  syntax-rules
  define-syntax-rule
  (for-syntax
   (all-from-out syntax/parse)
   (all-from-out racket)
   (all-from-out racket/syntax)
   raise-curnel-type-error
   raise-curnel-syntax-error
   cur->datum
   cur-expand
   type-infer/syn
   type-check/syn?
   normalize/syn
   step/syn
   cur-equal?))

;; Exceptions
(begin-for-syntax
  (provide
   (struct-out exn:cur)
   (struct-out exn:cur:curnel)
   (struct-out exn:cur:curnel:type)
   (struct-out exn:cur:curnel:syntax))
  (define-struct (exn:cur exn) () #:transparent)
  (define-struct (exn:cur:curnel exn:cur) () #:transparent)
  (define-struct (exn:cur:curnel:type exn:cur) () #:transparent)
  (define-struct (exn:cur:curnel:syntax exn:cur) () #:transparent)

  (define (raise-curnel-type-error name v . other)
    (raise
     (make-exn:cur:curnel:type
      (for/fold ([msg (format "~a: Cur type error;~n  Typing judgment did not hold in Curnel~n    term: ~a" name v)])
                ([t other])
        (format "~a~n   additional context: ~a" msg t))
      (current-continuation-marks))))

  (define (raise-curnel-syntax-error name v [more ""])
    (raise
     (make-exn:cur:curnel:syntax
      (format "~a: Cur syntax error;~n  Term is invalid Curnel syntax;~a~n    term: ~a" name more v)
      (current-continuation-marks)))))

(begin-for-syntax
  ;; TODO: Gamma and Delta seem to get reset inside a module+
  (define gamma
    (make-parameter
      (term ∅)
      (lambda (x)
        (unless (Γ? x)
          (raise-curnel-syntax-error 'term-environment "term is not a well-formed Γ"))
        x)))

  (define delta
    (make-parameter
      (term ∅)
      (lambda (x)
        (unless (Δ? x)
          (raise-curnel-syntax-error 'inductive-delcaration x "term is not a well-formed Δ"))
        x)))

  ;; These should be provided by core, so details of envs can be hidden.
  (define (extend-Γ/term env x t)
    (term (Γ-set ,(env) ,x ,t)))

  (define (extend-Γ/term! env x t) (env (extend-Γ/term env x t)))

  (define (extend-Γ/syn env x t)
    (extend-Γ/term env (syntax->datum x) (cur->datum t)))

  (define (extend-Γ/syn! env x t) (env (extend-Γ/syn env x t)))

  (define (extend-Δ/term env x t c*)
    (term (Δ-set ,(env) ,x ,t (,@c*))))

  (define (extend-Δ/term! env x t c*)
    (env (extend-Δ/term env x t c*)))

  (define (extend-Δ/syn env x t c*)
    (extend-Δ/term env (syntax->datum x) (cur->datum t)
                   (for/list ([c (syntax->list c*)])
                     (syntax-case c ()
                       [(c : ct)
                        (parameterize ([gamma (extend-Γ/syn gamma x t)])
                          (term (,(syntax->datum #'c) : ,(cur->datum #'ct))))]))))

  (define (extend-Δ/syn! env x t c*)
    (env (extend-Δ/syn env x t c*)))

  (define subst? (list/c (listof x?)  (listof e?)))
  (define bind-subst
    (make-parameter
     (list null null)
     (lambda (x)
       (unless (subst? x)
         (raise-curnel-syntax-error 'top-level-bindings x))
       x)))

  (define (add-binding/term! x t)
    (let ([vars (first (bind-subst))]
          [exprs (second (bind-subst))])
      (bind-subst (list (cons x vars) (cons t exprs)))))

  (define (subst-bindings t)
    (term (subst-all ,t ,(first (bind-subst)) ,(second (bind-subst)))))

  (define (type-infer/term t)
    (let ([t (judgment-holds (type-infer ,(delta) ,(gamma) ,(subst-bindings t) t_0) t_0)])
      (and (pair? t) (car t))))

  (define (type-check/term? e t)
    (and (judgment-holds (type-check ,(delta) ,(gamma) ,(subst-bindings e) ,(subst-bindings t))) #t))

  ;; TODO: Blanket disarming is probably a bad idea.
  (define orig-insp (variable-reference->module-declaration-inspector (#%variable-reference)))
  (define (disarm syn) (syntax-disarm syn orig-insp))

  ;; Locally expand everything down to core forms.
  (define (core-expand syn)
    (disarm
      (local-expand
        syn
        'expression
        (append (syntax-e #'(term reduce subst-all dep-top #%app λ Π elim Unv #%datum void))))))

  ;; Only type-check at the top-level, to prevent exponential
  ;; type-checking. Redex is expensive enough.
  (define inner-expand? (make-parameter #f))

  ;; Reifiy cur syntax into curnel datum
  (define (cur->datum syn)
    ;; Main loop; avoid type
    (define reified-term
      (parameterize ([inner-expand? #t])
        (let cur->datum ([syn syn])
          (syntax-parse (core-expand syn)
            #:literals (term reduce #%app subst-all)
            #:datum-literals (elim Π λ : Unv)
            [x:id (syntax->datum #'x)]
            [(subst-all e _ _) (syntax->datum #'e)]
            [(reduce Δ e) (cur->datum #'e)]
            [(term e) (cur->datum #'e)]
            [(Unv i) (term (Unv ,(syntax->datum #'i)))]
            ;; TODO: should really check that b is one of the binders
            ;; Maybe make a syntax class for the binders, core forms,
            ;; etc.
            [(b:id (x:id : t) e)
             (let* ([x (syntax->datum #'x)]
                    [t (cur->datum #'t)]
                    [e (parameterize ([gamma (extend-Γ/term gamma x t)])
                         (cur->datum #'e))])
               (term (,(syntax->datum #'b) (,x : ,t) ,e)))]
            [(elim t1 t2)
             (let* ([t1 (cur->datum #'t1)]
                    [t2 (cur->datum #'t2)])
               (term (elim ,t1 ,t2)))]
            [(#%app e1 e2)
             (term (,(cur->datum #'e1) ,(cur->datum #'e2)))]))))
    (unless (or (inner-expand?) (type-infer/term reified-term))
      #;(printf "Delta: ~s~nGamma: ~s~n" (delta) (gamma))
      (raise-curnel-type-error 'cur->datum reified-term syn))
    reified-term)

  (define (datum->cur syn t)
    (let datum->cur ([t t])
      (match t
        [(list (quote term) e)
         (quasisyntax/loc syn
           (datum->cur e))]
        [(list (quote Unv) i)
         (quasisyntax/loc syn
           (Type #,i))]
        [(list (quote Π) (list x (quote :) t) body)
         (quasisyntax/loc syn
           (dep-forall (#,(datum->syntax syn x) : #,(datum->cur t)) #,(datum->cur body)))]
        [(list (quote λ) (list x (quote :) t) body)
         (quasisyntax/loc syn
           (dep-lambda (#,(datum->syntax syn x) : #,(datum->cur t)) #,(datum->cur body)))]
        [(list (list (quote elim) t1) t2)
         (quasisyntax/loc syn
           (dep-elim #,(datum->cur t1) #,(datum->cur t2)))]
        [(list e1 e2)
         (quasisyntax/loc syn
           (dep-app #,(datum->cur e1) #,(datum->cur e2)))]
        [_
         (quasisyntax/loc syn
           #,(datum->syntax syn t))])))

  (define (eval-cur syn)
    (term (reduce ,(delta) ,(subst-bindings (cur->datum syn)))))

  (define (syntax->curnel-syntax syn)
    (quasisyntax/loc
      syn
      ;; TODO: this subst-all should be #,(subst-bindings (cur->datum syn)), but doesn't work
      (term (reduce #,(delta) (subst-all #,(cur->datum syn) #,(first (bind-subst)) #,(second (bind-subst)))))))

  ;; Reflection tools
  ;; TODO: Reflection tools should catch internal errors, e.g., from eval-cur et al. to
  ;; ensure users can provide better error messages. But should not catch errors caused by user macros.

  (define (local-env->gamma env)
    (for/fold ([gamma (gamma)])
              ([(x t) (in-dict env)])
      (extend-Γ/syn (thunk gamma) x t)))

  (define (normalize/syn syn  #:local-env [env '()])
    (parameterize ([gamma (local-env->gamma env)])
      (datum->cur
       syn
       (eval-cur syn))))

  (define (step/syn syn)
    (datum->cur
      syn
      (term (step ,(delta) ,(subst-bindings (cur->datum syn))))))

  ;; Are these two terms equivalent in type-systems internal equational reasoning?
  (define (cur-equal? e1 e2)
    (and (judgment-holds (equivalent ,(delta) ,(eval-cur e1) ,(eval-cur e2))) #t))

  ;; TODO: Document local-env
  (define (type-infer/syn #:local-env [env '()] syn)
    (parameterize ([gamma (local-env->gamma env)])
      (with-handlers ([exn:cur:curnel:type? (lambda _ #f)])
        (let ([t (type-infer/term (eval-cur syn))])
        (and t (datum->cur syn t))))))

  (define (type-check/syn? syn type)
    (with-handlers ([exn:cur:curnel:type? (lambda _ #f)])
      (type-check/term? (eval-cur syn) (eval-cur type))))

  ;; Takes a Cur term syn and an arbitrary number of identifiers ls. The cur term is
  ;; expanded until expansion reaches a Curnel form, or one of the
  ;; identifiers in ls.
  ;; TODO: Holy crap boilerplate
  (define (cur-expand syn #:local-env [env '()] . ls)
    (parameterize ([gamma (local-env->gamma env)])
      (disarm
       (local-expand
        syn
        'expression
        (append (syntax-e #'(Type dep-inductive dep-lambda dep-app dep-elim dep-forall dep-top))
                ls))))))

;; -----------------------------------------------------------------
;; Require/provide macros

#| TODO NB XXX
 | This is code some of the most hacky awful code I've ever written. But it works. ish
 |#
(begin-for-syntax
  (define envs (list #'(void)))

  (define (cur-identifier-bound? id)
    (let ([x (syntax->datum id)])
      (and (x? x)
        (or (term (Γ-ref ,(gamma) ,x))
          (term (Δ-ref-type ,(delta) ,x))))))

  (define (filter-cur-exports syn modes)
    (partition (compose cur-identifier-bound? export-local-id)
               (apply append (map (lambda (e) (expand-export e modes))
                                  (syntax->list syn))))))
(define-syntax extend-env-and-provide
  (make-provide-transformer
    (lambda (syn modes)
      (syntax-case syn ()
        [(_ e ...)
         (let-values ([(cur ~cur) (filter-cur-exports #'(e ...) modes)])
           #| TODO: Ignoring the built envs for now
           (set! envs (for/list ([e cur])
           (let* ([x (syntax->datum (export-local-id e))]
                  [t (type-infer/term x)]
                  [env (if (term (lookup ,(gamma) ,x)) #'gamma #'delta)])
             #`(extend-env/term! #,env #,(export-out-sym e) #,t))))
           |#
        ~cur)]))))

(define-syntax (export-envs syn)
  (syntax-case syn ()
    [(_ gamma-out delta-out bind-out)
     (begin
       #`(begin-for-syntax
          (define gamma-out (term #,(gamma)))
          (define delta-out (term #,(delta)))
          (define bind-out '#,(bind-subst))))]))

;; TODO: This can only handle a single provide form, otherwise generates multiple *-out
(define-syntax (dep-provide syn)
  (syntax-case syn ()
    [(_ e ...)
     (begin
       #| TODO NB:
        | Ignoring the built envs above, for now.  The local-lift export seems to get executed before
        | the filtered environment is built.
        |#
       ;; TODO: rename out will need to rename variables in gamma and ; delta.
       (syntax-local-lift-module-end-declaration
         #`(export-envs gamma-out delta-out bind-out))
       #`(provide (extend-env-and-provide e ...)
                  (for-syntax gamma-out delta-out bind-out)))]))
(begin-for-syntax
  (define out-gammas #`())
  (define out-deltas #`())
  (define out-binds #`())
  (define gn 0)
  (define sn 0)
  (define bn 0)
  (define (filter-cur-imports syn)
    (for/fold ([imports '()]
               [sources '()])
              ([req-spec (syntax->list syn)])
      (let-values ([(more-imports more-sources) (expand-import req-spec)])
        (values (for/fold ([imports imports])
                          ([imp more-imports])
                  (cond
                    [(equal? (import-src-sym imp) 'gamma-out)
                     (let ([new-id (format-id (import-orig-stx imp)
                                              "gamma-out~a" gn)])
                       ;; TODO: Fewer set!s
                       ;; TODO: Do not DIY gensym
                       (set! gn (add1 gn))
                       (set! out-gammas
                             #`(#,@out-gammas (gamma (term (Γ-union
                                                             ,(gamma)
                                                             ,#,new-id)))))
                       (cons (struct-copy import imp [local-id new-id])
                             imports))]
                    ;; TODO: Many shared code between these two clauses
                    [(equal? (import-src-sym imp) 'delta-out)
                     (let ([new-id (format-id (import-orig-stx imp)
                                              "delta-out~a" sn)])
                       ;; TODO: Fewer set!s
                       ;; TODO: Do not DIY gensym
                       (set! sn (add1 sn))
                       (set! out-deltas
                             #`(#,@out-deltas (delta (term (Δ-union
                                                             ,(delta)
                                                             ,#,new-id)))))
                       (cons (struct-copy import imp [local-id new-id])
                             imports))]
                    ;; TODO: Many shared code between these two clauses
                    [(equal? (import-src-sym imp) 'bind-out)
                     (let ([new-id (format-id (import-orig-stx imp)
                                              "bind-out~a" bn)])
                       ;; TODO: Fewer set!s
                       ;; TODO: Do not DIY gensym
                       (set! bn (add1 bn))
                       (set! out-binds
                             #`(#,@out-binds (bind-subst (list (append
                                                                 (first #,new-id)
                                                                 (first (bind-subst)))
                                                               (append
                                                                 (second #,new-id)
                                                                 (second (bind-subst)))))))
                       (cons (struct-copy import imp [local-id new-id])
                             imports))]
                    [else (cons imp imports)]))
                (append sources more-sources))))))

(define-syntax extend-env-and-require
  (make-require-transformer
    (lambda (syn)
      (syntax-case syn ()
        [(_ e ...) (filter-cur-imports #'(e ...))]))))

;; TODO: rename in will need to rename variables in gamma and delta.
(define-syntax (import-envs syn)
  (syntax-case syn ()
    [(_) #`(begin-for-syntax #,@out-gammas #,@out-deltas
                             #,@out-binds)]))

(define-syntax (dep-require syn)
  (syntax-case syn ()
    [(_ e ...)
     #`(begin
         (require (extend-env-and-require e ...))
         (import-envs))]))

(define-syntax (dep-module+ syn)
  (syntax-case syn ()
    [(_ name body ...)
     #`(module+ name
         (begin-for-syntax
           (gamma (term #,(gamma)))
           (delta (term #,(delta)))
           (bind-subst '#,(bind-subst)))
         body ...)]))

;; -----------------------------------------------------------------
;; Core wrapper macros
;;
;; TODO: Can these be simplified further?
(define-syntax (dep-lambda syn)
  (syntax-case syn (:)
    [(_ (x : t) e)
     (syntax->curnel-syntax
       (quasisyntax/loc syn (λ (x : t) e)))]))

(define-syntax (dep-app syn)
  (syntax-parse syn
    [(_ e1:expr e2:expr)
     (syntax->curnel-syntax
       (quasisyntax/loc syn (#%app e1 e2)))]))

(define-syntax (dep-forall syn)
  (syntax-case syn (:)
    [(_ (x : t) e)
     (syntax->curnel-syntax
       (quasisyntax/loc syn (Π (x : t) e)))]))

(define-syntax (Type syn)
  (syntax-case syn ()
    [(_ i)
     (syntax->curnel-syntax
       (quasisyntax/loc syn (Unv i)))]
    [_ (quasisyntax/loc syn (Type 0))]))

(define-syntax (dep-inductive syn)
  (syntax-case syn (:)
    [(_ i : ti (x1 : t1) ...)
     (begin
       (extend-Δ/syn! delta #'i #'ti #'((x1 : t1) ...))
       #'(void))]))

(define-syntax (dep-elim syn)
  (syntax-case syn ()
    [(_ D T)
     (syntax->curnel-syntax
       (quasisyntax/loc syn (elim D T)))]))

(define-syntax-rule (dep-void) (void))

;; TODO: Not sure if this is the correct behavior for #%top
(define-syntax (dep-top syn)
  (syntax-case syn ()
    [(_ . id)
     ;; TODO NB FIXME: HACKS HACKS HACKS
     (let ([t (core-expand #'id)])
       (if (equal? (syntax->datum t) '(void))
           #'(void)
           (syntax->curnel-syntax t)))]))

(define-syntax (dep-top-interaction syn)
  (syntax-case syn ()
    [(_ . form)
     (begin
       ;; TODO NB FIXME: HACKS
       #`(begin
           (export-envs gamma-out delta-out bind-out)
           (begin-for-syntax
             (define nm (map (lambda (x) (namespace-variable-value x #f (lambda x #t))) (namespace-mapped-symbols)))
             (bind-subst (first (memf subst? nm)))
             (gamma (first (memf Γ? nm)))
             (delta (first (memf Δ? nm))))
          form))]))

(define-syntax (dep-define syn)
  (syntax-parse syn
    [(_ id:id e)
     (let ([e (cur->datum #'e)]
           [id (syntax->datum #'id)])
       ;; NB: Have to roll our own namespace rather than use built-in define so id is resolved at
       ;; compile time in redex, and at runtime in racket.
       (extend-Γ/term! gamma id (type-infer/term e))
       (add-binding/term! id e)
       #'(void))]))
