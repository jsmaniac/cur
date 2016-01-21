#lang s-exp "cur.rkt"
;; Olly: The OTT-Like LibrarY
;; TODO: Automagically create a parser from bnf grammar
(require
  "stdlib/sugar.rkt"
  "stdlib/nat.rkt"
  ;; TODO: "real-"? More like "curnel-"
  (only-in "cur.rkt" [#%app real-app] [elim real-elim] [forall real-forall] [lambda real-lambda]))

(provide
  define-relation
  define-language
  generate-coq

  ;; private; exported for testing only
  (for-syntax
   typeset-relation
   typeset-bnf
   cur->coq))

;; Generate Coq from Cur:

(begin-for-syntax
  (define coq-defns (make-parameter ""))

  (define (coq-lift-top-level str)
    (coq-defns (format "~a~a~n" (coq-defns) str)))

  (define (constructor-args syn)
    (syntax-parse (type-infer/syn syn)
      #:datum-literals (Π :)
      [(Π (x:id : t) body)
       (cons #'x (constructor-args #'body))]
      [_ null]))

  (define (sanitize-id str)
    (let ([replace-by `((: _) (- _))])
      (for/fold ([str str])
                ([p replace-by])
        (string-replace str (symbol->string (first p))
                        (symbol->string (second p))))))

  (define (cur->coq syn)
    (parameterize ([coq-defns ""])
      (define output
        (let cur->coq ([syn syn]
                       [local-env (make-immutable-hash)])
          (syntax-parse (cur-expand #:local-env local-env syn #'define #'begin)
            ;; TODO: Need to add these to a literal set and export it
            ;; Or, maybe overwrite syntax-parse
            #:literals (real-lambda real-forall data real-app real-elim define begin Type)
            [(begin e ...)
             (for/fold ([str ""])
                       ([e (syntax->list #'(e ...))])
               (format "~a~n" (cur->coq e local-env)))]
            [(define name:id body)
             (begin
               (coq-lift-top-level
                (format "Definition ~a := ~a.~n"
                        (cur->coq #'name local-env)
                        (cur->coq #'body local-env)))
               "")]
            [(define (name:id (x:id : t) ...) body)
             (begin
               (define-values (args body-local-env)
                 (for/fold ([str ""]
                            [local-env local-env])
                           ([n (syntax->list #'(x ...))]
                            [t (syntax->list #'(t ...))])
                   (values
                    (format
                     "~a(~a : ~a) "
                     str
                     (cur->coq n local-env)
                     (cur->coq t local-env))
                    (dict-set local-env n t))))
               (coq-lift-top-level
                (format "Function ~a ~a := ~a.~n"
                        (cur->coq #'name local-env)
                        args
                        (cur->coq #'body body-local-env)))
               "")]
            [(real-lambda ~! (x:id (~datum :) t) body:expr)
             (format "(fun ~a : ~a => ~a)" (syntax-e #'x) (cur->coq #'t local-env)
                     (cur->coq #'body (dict-set local-env #'x #'t)))]
            [(real-forall ~! (x:id (~datum :) t) body:expr)
             (format "(forall ~a : ~a, ~a)" (syntax-e #'x) (cur->coq #'t local-env)
                     (cur->coq #'body (dict-set local-env #'x #'t)))]
            [(data ~! n:id (~datum :) t (x*:id (~datum :) t*) ...)
             (begin
               (coq-lift-top-level
                (format "Inductive ~a : ~a :=~a."
                        (sanitize-id (format "~a" (syntax-e #'n)))
                        (cur->coq #'t local-env)
                        (call-with-values
                         (thunk
                          (for/fold ([strs ""]
                                     [local-env (dict-set local-env #'n #'t)])
                                    ([x (attribute x*)]
                                     [t (attribute t*)])
                            (values
                             (format "~a~n| ~a : ~a" strs (syntax-e x)
                                     (cur->coq t local-env))
                             (dict-set local-env x t))))
                         (lambda (x y) x))))
               "")]
            [(Type i) "Type"]
            [(real-elim var t)
             (format "~a_rect" (cur->coq #'var local-env))]
            [(real-app e1 e2)
             (format "(~a ~a)" (cur->coq #'e1 local-env) (cur->coq #'e2 local-env))]
            [e:id (sanitize-id (format "~a" (syntax->datum #'e)))])))
      (format
       "~a~a"
       (coq-defns)
       (if (regexp-match "^\\s*$" output)
           ""
           (format "Eval compute in ~a." output))))))

(define-syntax (generate-coq syn)
  (syntax-parse syn
    [(_ (~optional (~seq #:file file))
        (~optional (~seq #:exists flag))
        body:expr)
     (parameterize ([current-output-port
                     (if (attribute file)
                         (open-output-file
                          (syntax->datum #'file)
                          #:exists
                          (if (attribute flag)
                              ;; TODO: AHH WHAT?
                              (eval (syntax->datum #'flag))
                              'error))
                         (current-output-port))])
       (displayln (cur->coq #'body))
       #'(begin))]))

;; TODO: Should these display or return a string?
(begin-for-syntax
  (define (display-mathpartir)
    (displayln
     "%% Requires mathpartir, http://pauillac.inria.fr/~remy/latex/mathpartir.html")
    (displayln
     "%% or mttex, https://github.com/wilbowma/mttex")
    (displayln
     "\\usepackage{mathpartir}"))

  (define (display-bnf)
    (displayln
     "%% Some auxillary defs. These should deleted if using mttex, https://github.com/wilbowma/mttex")
    (displayln
     "\\newcommand{\\bnfdef}{{\\bf ::=}}")
    (displayln
     "\\newcommand{\\bnfalt}{{\\bf \\mid}}")))

;; ------------------------------------
;; define-relation

(begin-for-syntax
  (define-syntax-class horizontal-line
    (pattern
     x:id
     #:when (regexp-match? #rx"-+" (symbol->string (syntax-e #'x)))))

  (define-syntax-class hypothesis
    (pattern (x:id (~datum :) t))
    (pattern (~not e:horizontal-line)))

  ;; Alias syntax-classes with names for better error messages
  (define-syntax-class rule-name
    (pattern x:id))

  (define-syntax-class relation-name
    (pattern x:id))

  (define-syntax-class relation-index
    (pattern e:expr))

  (define-syntax-class (conclusion n args lab)
    (pattern
     (name:id arg:expr ...)
     #:attr rule-label-symbol (syntax-e lab)
     #:attr rule-name-symbol (syntax-e #'name)
     #:attr relation-name-symbol (syntax-e n)
     #:fail-unless (eq? (attribute rule-name-symbol) (attribute relation-name-symbol))
     (format "In rule ~a, name of conclusion ~a did not match name of relation ~a"
             (attribute rule-label-symbol)
             (attribute rule-name-symbol)
             (attribute relation-name-symbol))
     #:attr rule-arg-count (length (attribute arg))
     #:attr relation-arg-count (length args)
     #:fail-unless (= (attribute rule-arg-count) (attribute relation-arg-count))
     (format "In rule ~a, conclusion applied to ~a arguments, while relation declared to have ~a arguments"
             (attribute rule-label-symbol)
             (attribute rule-arg-count)
             (attribute relation-arg-count))))

  ;; TODO: Automatically infer hypotheses that are merely declarations by binding all free identifiers?
  ;; TODO: Automatically infer hypotheses as above for meta-variables that are the
  ;; same as bnf grammar, as a simple first case
  (define-syntax-class (inferrence-rule name indices)
    (pattern (h:hypothesis ...
              #;line:horizontal-line
              (~optional line:horizontal-line)
              ~!
              lab:rule-name
              (~var t (conclusion name indices (attribute lab))))
             #:with constr-decl
             ;; TODO: quasisyntax/loc
             #'(lab : (-> h ... (t.name t.arg ...)))
             ;; TODO: convert meta-vars such as e1 to e_1
             #:attr latex
             (format
              "\\inferrule~n{~a}~n{~a}"
              (string-trim
               (for/fold ([str ""])
                         ;; TODO: Perhaps omit hypotheses that are merely delcarations of free variables
                         ([hyp (syntax->datum #'(h ...))])
                 (format "~a~a \\+" str hyp))
               " \\+"
               #:left? #f)
              (format "~a" (syntax->datum #'(t.name t.arg ...))))))

  ;; TODO: Should this display or return a string?
  (define (typeset-relation form rules-latex)
    (display-mathpartir)
    (printf
     "\\fbox{$~a$}$~n$\\begin{mathpar}~n~a~n\\end{mathpar}"
     form
     (string-trim
      (for/fold ([str ""])
                ([rule rules-latex])
        (format "~a~a\\and~n" str rule))
      "\\and"
      #:left? #f))))

(define-syntax (define-relation syn)
  (syntax-parse syn
    [(_ (name:relation-name index:relation-index ...)
        (~optional (~seq #:output-coq coq-file:str))
        (~optional (~seq #:output-latex latex-file:str))
        (~var rule (inferrence-rule (attribute name) (attribute index))) ...)
      (let ([output #`(data name : (-> index ... Type) rule.constr-decl ...)])
        (when (attribute latex-file)
          (with-output-to-file (syntax->datum #'latex-file)
            (thunk
             (typeset-relation
              (syntax->datum #'(name index ...))
              (attribute rule.latex)))
            #:exists 'append))
        (when (attribute coq-file)
          (with-output-to-file (syntax->datum #'coq-file)
            (thunk (displayln (cur->coq output)))
            #:exists 'append))
        output)]))

;; ------------------------------------
;; define-language

(begin-for-syntax
  ;; A mutable dictionary from non-terminal meta-variables names to their types.
  (define mv-map (make-parameter #f))

  ;; A set containing the meta-variables that represent variables.
  (define vars (make-parameter #f))

  ;; The language name for the language currently being parsed
  (define lang-name (make-parameter #f))

  ;; A meta-variable is any identifiers that belongs to the mv-map
  (define-syntax-class meta-variable
    (pattern
     x:id
     #:attr sym (syntax->datum #'x)
     #:fail-unless (dict-has-key? (mv-map) (attribute sym)) #f
     #:attr type (dict-ref (mv-map) (attribute sym))))

  ;; A var-meta-variable is a meta-variable that is declared to be
  ;; treated as a variable in the defined language.
  (define-syntax-class var-meta-variable
    (pattern
     x:id
     #:fail-unless (set-member? (vars) (syntax->datum #'x)) #f))

  ;; A terminal is a idnetifiers that is not a meta-variable. A terminal will always represent a constructor.
  (define-syntax-class terminal
    (pattern
     x:id
     #:attr sym (syntax->datum #'x)
     #:fail-when (dict-has-key? (mv-map) (attribute sym)) #f
     #:attr constructor-name
     (quasisyntax/loc #'x
       #,(format-id #'x "~a-~a" (lang-name) #'x))))

  ;; A terminal-args can appear as the argument to a terminal in
  ;; an expression, or as a sub-expression in a terminal-args.
  ;; Each terminal-args export args, a list of types the
  ;; terminal-args represents and the list of types the non-terminal's
  ;; constructor expects in this case.
  (define-syntax-class (terminal-args non-terminal-type)
    ;; A meta-variable is a terminal-args
    (pattern
     e:meta-variable
     #:attr args
     (list #'e.type)
     #:attr latex
     (format "~a" (syntax-e #'e)))

    ;; An identifier is a terminal-args, but is treated as syntax
    (pattern
     x:id
     #:attr args
     '()
     #:attr latex
     (format "~a" (syntax-e #'x)))

    ;; So is an empty list
    (pattern
     ()
     #:attr args
     '()
     #:attr latex
     "")

    ;; We use De-Bruijn indices, so binding positions are removed.
    (pattern
     (#:bind x:var-meta-variable . (~var t (terminal-args non-terminal-type)))
     #:attr args
     (attribute t.args)
     #:attr latex
     (format "~a ~a" (syntax-e #'x) (attribute t.latex)))

    ;; A terminal-args applied to other nested expressions is a terminal-args
    (pattern
     ((~var h (terminal-args non-terminal-type))
      (~var t (terminal-args non-terminal-type)) ...)
     #:attr args
     (for/fold ([ls (attribute h.args)])
               ([args (attribute t.args)])
       (append ls args))
     #:attr latex
     (format "~a ~a" (attribute h.latex) (apply string-append (attribute t.latex)))))

  ;; a expression is parameterized by the name of the non-terminal to
  ;; which is belongs,
  ;; Each expression exports a constr-decl, which declares a
  ;; constructor for the non-terminal type.
  (define-syntax-class (expression non-terminal-type)
    ;; A meta-variable is a valid expression.
    ;; Generates a conversion constructor in constr-decl, and the type of
    (pattern
     e:meta-variable
     #:attr constructor-name
     (quasisyntax/loc #'e #,(format-id #'e "~a->~a" #'e.type non-terminal-type))
     #:attr constr-decl
     (quasisyntax/loc #'e (constructor-name : (-> e.type #,non-terminal-type)))
     #:attr latex
     (format "~a" (syntax-e #'e)))

    ;; An identifier is a valid expression, generating a base constructor.
    (pattern
     x:terminal
     #:attr constr-decl
     (quasisyntax/loc #'x (x.constructor-name : #,non-terminal-type))
     #:attr latex
     (format "~a" (syntax-e #'x)))

    ;; A terminal applied to a terminal-args is a valid expression.
    (pattern
     (x:terminal . (~var c (terminal-args non-terminal-type)))
     #:attr constr-decl
     (quasisyntax/loc #'x (x.constructor-name : (-> #,@(attribute c.args) #,non-terminal-type)))
     #:attr latex
     (format "(~a ~a)" (syntax-e #'x) (attribute c.latex))))

  (define-syntax-class non-terminal-def
    (pattern
     (name:id
      (meta-var:id ...+)
      (~optional (~datum ::=))
      ;; Create a name for the type of this non-terminal, from the
      ;; language name and the non-terminal name.
      (~bind [nt-type (quasisyntax/loc #'name #,(format-id #'name "~a-~a" (lang-name) #'name))])
      ;; Imperatively update the map from meta-variables to the
      ;; nt-type, to be used when generating the types of the constructors
      ;; for this and later non-terminal.
      (~do (for ([mv (syntax->datum #'(meta-var ...))])
             (dict-set! (mv-map) mv (attribute nt-type))))
      (~var c (expression (attribute nt-type))) ...)
     ;; Generates the inductive data type for this non-terminal definition.
     #:attr def
     (quasisyntax/loc #'name (data nt-type : Type c.constr-decl ...))
     #:attr latex
     (format
      "\\mbox{\\textit{~a}} & ~a & \\bnfdef & ~a\\\\~n"
      (symbol->string (syntax->datum #'name))
      (string-trim
       (for/fold ([str ""])
                 ([nt (syntax->datum #'(meta-var ...))])
         (format "~a~a," str nt))
       ","
       #:left? #f)
      (string-trim
       (for/fold ([str ""])
                 ([expr (attribute c.latex)])
         (format "~a~a \\bnfalt " str expr))
       " \\bnfalt "
       #:left? #f))))

  ;; TODO: Should this display or return a string?
  (define (typeset-bnf nt-latex)
    (display-mathpartir)
    (display-bnf)
    (printf
     "\begin{displaymath}~n\\begin{array}{lrrl}~n~a~n\\end{array}~n\end{displaymath}"
     (apply string-append nt-latex))))

;; TODO: For better error messages, add context
;; TODO: Extend define-language with syntax such as ....
;;   (term (e) ::= (e1 e2) ((lambda (x) e)
(define-syntax (define-language syn)
  (define/syntax-parse
    (_ name:id
       (~optional (~seq #:vars (x:id ...)))
       (~optional (~seq #:output-coq coq-file:str))
       (~optional (~seq #:output-latex latex-file:str))
       .
       non-terminal-defs)
    syn)
  (parameterize ([mv-map (make-hash)]
                 [lang-name #'name]
                 [vars (apply set (map syntax->datum (or (attribute x) '())))])
    (cond
      [(attribute x) =>
       (lambda (xls)
         (for ([x xls])
           (dict-set! (mv-map) (syntax-e x) #'Nat)))])
    (syntax-parse #'non-terminal-defs
      [(def:non-terminal-def ...)
       (let ([output (quasisyntax/loc #'name (begin def.def ...))])
         (when (attribute latex-file)
           (with-output-to-file (syntax-e #'latex-file)
             (thunk (typeset-bnf (attribute def.latex)))
             #:exists 'append))
         (when (attribute coq-file)
           (with-output-to-file (syntax-e #'coq-file)
             (thunk (displayln (cur->coq output)))
             #:exists 'append))
         output)])))

;; See stlc.rkt for examples
