#lang racket/base

(require
  racket/function
  redex/reduction-semantics)

(provide
  (all-defined-out))

(set-cache-size! 10000)

;; Test suite setup.
(module+ test
  (require
    rackunit
    (only-in racket/set set=?))
  (define-syntax-rule (check-holds (e ...))
    (check-true
      (judgment-holds (e ...))))
  (define-syntax-rule (check-not-holds (e ...))
    (check-false
      (judgment-holds (e ...))))
  (define-syntax-rule (check-equiv? e1 e2)
    (check (default-equiv) e1 e2))
  (define-syntax-rule (check-not-equiv? e1 e2)
    (check (compose not (default-equiv)) e1 e2)))

#| References:
 |  http://www3.di.uminho.pt/~mjf/pub/SFV-CIC-2up.pdf
 |  https://www.cs.uoregon.edu/research/summerschool/summer11/lectures/oplss-herbelin1.pdf
 |  http://www.emn.fr/z-info/ntabareau/papers/universe_polymorphism.pdf
 |  http://people.cs.kuleuven.be/~jesper.cockx/Without-K/Pattern-matching-without-K.pdf
 |  http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.37.74
 |  http://eb.host.cs.st-andrews.ac.uk/writings/thesis.pdf
 |#

#| ttL is the core language of Cur. Very similar to TT (Idirs core) and Luo's UTT. Surface
 | langauge should provide short-hand, such as -> for non-dependent function types, and type
 | inference.
 |#
(define-language ttL
  (i ::= natural)
  (U ::= (Unv i))
  (x ::= variable-not-otherwise-mentioned)
  (t e ::= (Π (x : t) t) (λ (x : t) t) (elim t t) x U (t t))
  ;; Σ (signature). (inductive-name : type ((constructor : type) ...))
  ;; NB: Σ is a map from a name x to a pair of it's type and a map of constructor names to their types
  (Σ   ::= ∅ (Σ (x : t ((x : t) ...)))))

(define x? (redex-match? ttL x))
(define t? (redex-match? ttL t))
(define e? (redex-match? ttL e))
(define U? (redex-match? ttL U))
(define Σ? (redex-match? ttL Σ))

(module+ test
  (define-term Type (Unv 0))
  (check-true (x? (term T)))
  (check-true (x? (term A)))
  (check-true (x? (term truth)))
  (check-true (x? (term zero)))
  (check-true (x? (term s)))
  (check-true (t? (term zero)))
  (check-true (t? (term s)))
  (check-true (x? (term nat)))
  (check-true (t? (term nat)))
  (check-true (t? (term A)))
  (check-true (t? (term S)))
  (check-true (U? (term (Unv 0))))
  (check-true (U? (term Type)))
  (check-true (e? (term (λ (x_0 : (Unv 0)) x_0))))
  (check-true (t? (term (λ (x_0 : (Unv 0)) x_0))))
  (check-true (t? (term (λ (x_0 : (Unv 0)) x_0))))

  ;; TODO: Rename these signatures, and use them in all future tests.
  (define Σ (term ((∅ (nat : (Unv 0) ((zero : nat) (s : (Π (x : nat) nat)))))
                        (bool : (Unv 0) ((true : bool) (false : bool))))))
  (define Σ0 (term ∅))
  (define Σ3 (term (∅ (and : (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Unv 0))) ()))))
  (define Σ4 (term (∅ (and : (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Unv 0)))
                             ((conj : (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Π (a : A) (Π (b : B) ((and A) B)))))))))))
  (check-true (Σ? Σ0))
  (check-true (Σ? Σ))
  (check-true (Σ? Σ4))
  (check-true (Σ? Σ3))
  (check-true (Σ? Σ4))
  (define sigma (term ((((((∅ (true : (Unv 0) ((T : true))))
                           (false : (Unv 0) ()))
                          (equal : (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Unv 0)))
                                 ()))
                         (nat : (Unv 0) ()))
                        (heap : (Unv 0) ()))
                       (pre : (Π (temp808 : heap) (Unv 0)) ()))))
  (check-true (Σ? (term (∅ (true : (Unv 0) ((T : true)))))))
  (check-true (Σ? (term (∅ (false : (Unv 0) ())))))
  (check-true (Σ? (term (∅ (equal : (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Unv 0)))
                                  ())))))
  (check-true (Σ? (term (∅ (nat : (Unv 0) ())))))
  (check-true (Σ? (term (∅ (pre : (Π (temp808 : heap) (Unv 0)) ())))))

  (check-true (Σ? (term ((∅ (true : (Unv 0) ((T : true)))) (false : (Unv 0) ())))))
  (check-true (Σ? (term (((∅ (true : (Unv 0) ((T : true)))) (false : (Unv 0) ()))
                                                            (equal : (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Unv 0)))
                                                                   ())))))
  (check-true (Σ? sigma)))

;;; ------------------------------------------------------------------------
;;; Primitive Operations on signatures Σ (those operations that do not require contexts)

;;; TODO: Might be worth maintaining the above bijection between Σ and maps for performance reasons

;; NB: Depends on clause order
(define-metafunction ttL
  Σ-ref-type : Σ x -> t or #f
  [(Σ-ref-type ∅ x) #f]
  [(Σ-ref-type (Σ (x : t any)) x) t]
  [(Σ-ref-type (Σ (x_0 : t_0 ((x_1 : t_1) ... (x : t) (x_2 : t_2) ...))) x) t]
  [(Σ-ref-type (Σ (x_0 : t_0 any)) x) (Σ-ref-type Σ x)])

(define-metafunction ttL
  Σ-union : Σ Σ -> Σ
  [(Σ-union Σ ∅) Σ]
  [(Σ-union Σ_2 (Σ_1 (x : t any)))
   ((Σ-union Σ_2 Σ_1) (x : t any))])

;; Returns the inductively defined type that x constructs
;; NB: Depends on clause order
(define-metafunction ttL
  Σ-key-by-constructor : Σ x -> x
  [(Σ-key-by-constructor (Σ (x : t ((x_0 : t_0) ... (x_c : t_c) (x_1 : t_1) ...))) x_c)
   x]
  [(Σ-key-by-constructor (Σ (x_1 : t_1 any)) x)
   (Σ-key-by-constructor Σ x)])

(module+ test
  (check-equal?
    (term (Σ-key-by-constructor ,Σ zero))
    (term nat))
  (check-equal?
    (term (Σ-key-by-constructor ,Σ s))
    (term nat)))

;; Returns the constructor map for the inductively defined type x_D in the signature Σ
(define-metafunction ttL
  Σ-ref-constructor-map : Σ x -> ((x : t) ...) or #f
  ;; NB: Depends on clause order
  [(Σ-ref-constructor-map ∅ x_D) #f]
  [(Σ-ref-constructor-map (Σ (x_D : t_D any)) x_D)
   any]
  [(Σ-ref-constructor-map (Σ (x_1 : t_1 any)) x_D)
   (Σ-ref-constructor-map Σ x_D)])

(module+ test
  (check-equal?
    (term (Σ-ref-constructor-map ,Σ nat))
    (term ((zero : nat) (s : (Π (x : nat) nat)))))
  (check-equal?
    (term (Σ-ref-constructor-map ,sigma false))
    (term ())))

;; Get the list of constructors for the inducitvely defined type x_D
(define-metafunction ttL
  Σ-ref-constructors : Σ x -> (x ...) or #f
  ;; NB: Depends on clause order
  [(Σ-ref-constructors ∅ x_D) #f]
  [(Σ-ref-constructors (Σ (x_D : t_D ((x : t) ...))) x_D)
   (x ...)]
  [(Σ-ref-constructors (Σ (x_1 : t_1 any)) x_D)
   (Σ-ref-constructors Σ x_D)])

;; Get the index of the constructor x_ci in the list of constructors for x_D
(define-metafunction ttL
  Σ-constructor-index : Σ x x -> natural or #f
  [(Σ-constructor-index Σ x_D x_ci)
   ,(for/fold ([i 0])
              ([c (term (Σ-ref-constructors Σ x_D))])
              #:break (eq? (term x_ci) c)
      (add1 i))])

;;; ------------------------------------------------------------------------
;;; Universe typing

;; Types of Universes
(define-judgment-form ttL
  #:mode (unv-ok I O)
  #:contract (unv-ok U U)

  [(where i_1 ,(add1 (term i_0)))
   -----------------
   (unv-ok (Unv i_0) (Unv i_1))])

;; NB: Based on CIC predicativity rules. should be able to simplify
(define-judgment-form ttL
  #:mode (unv-kind I I O)
  #:contract (unv-kind U U U)

  [----------------
   (unv-kind (Unv 0) (Unv 0) (Unv 0))]

  [----------------
   (unv-kind (Unv 0) (Unv i) (Unv i))]

  [----------------
   (unv-kind (Unv i) (Unv 0) (Unv 0))]

  [(where i_3 ,(max (term i_1) (term i_2)))
   ----------------
   (unv-kind (Unv i_1) (Unv i_2) (Unv i_3))])

;;; ------------------------------------------------------------------------
;;; Substitution and α-equivalence

(define-judgment-form ttL
  #:mode (α-equivalent I I)
  #:contract (α-equivalent t t)

  [----------------- "α-x"
   (α-equivalent x x)]

  [----------------- "α-U"
   (α-equivalent U U)]

  [(α-equivalent t_1 (subst t_3 x_1 x_0))
   (α-equivalent t_0 t_2)
   ----------------- "α-binder"
   (α-equivalent (any (x_0 : t_0) t_1)
                 (any (x_1 : t_2) t_3))]

  [(α-equivalent e_0 e_2)
   (α-equivalent e_1 e_3)
   ----------------- "α-app"
   (α-equivalent (e_0 e_1) (e_2 e_3))]

  [(α-equivalent e_0 e_2)
   (α-equivalent e_1 e_3)
   ----------------- "α-elim"
   (α-equivalent (elim e_0 e_1) (elim e_2 e_3))])

(module+ test
  ;; NB: Hack to allow checking contexts or terms without explicitly defining on contexts
  (default-equiv (lambda (x y) (term (α-equivalent (in-hole ,x Type) (in-hole ,y Type)))))
  (check-equiv? (term x) (term x))
  (check-not-equiv? (term x) (term y))
  (check-equiv? (term (λ (x : A) x)) (term (λ (y : A) y))))

;; NB: Copy and pasted from Redex examples
(define-metafunction ttL
  subst-vars : (x any) ... any -> any
  [(subst-vars (x_1 any_1) x_1) any_1]
  [(subst-vars (x_1 any_1) (any_2 ...))
   ((subst-vars (x_1 any_1) any_2) ...)]
  [(subst-vars (x_1 any_1) any_2) any_2]
  [(subst-vars (x_1 any_1) (x_2 any_2) ... any_3)
   (subst-vars (x_1 any_1) (subst-vars (x_2 any_2) ... any_3))]
  [(subst-vars any) any])

;; NB TODO: Why do I not have tests for substitutions?!?!?!?!?!?!?!!?!?!?!?!?!?!!??!?!
(define-metafunction ttL
  subst : t x t -> t
  [(subst U x t) U]
  [(subst x x t) t]
  [(subst x_0 x t) x_0]
  [(subst (any (x : t_0) t_1) x t)
   (any (x : (subst t_0 x t)) t_1)]
  [(subst (any (x_0 : t_0) t_1) x t)
   (any (x_new : (subst (subst-vars (x_0 x_new) t_0) x t))
     (subst (subst-vars (x_0 x_new) t_1) x t))
   (where x_new ,(variable-not-in (term (x_0 t_0 x t t_1)) (term x_0)))]
  [(subst (e_0 e_1) x t) ((subst e_0 x t) (subst e_1 x t))]
  [(subst (elim e_0 e_1) x t) (elim (subst e_0 x t) (subst e_1 x t))])

(module+ test
  (check-true (t? (term (Π (a : A) (Π (b : B) ((and A) B))))))
  (check-equiv?
    (term (Π (a : S) (Π (b : B) ((and S) B))))
    (term (subst (Π (a : A) (Π (b : B) ((and A) B))) A S))))

(define-metafunction ttL
  subst-all : t (x ...) (e ...) -> t
  [(subst-all t () ()) t]
  [(subst-all t (x_0 x ...) (e_0 e ...))
   (subst-all (subst t x_0 e_0) (x ...) (e ...))])

;;; ------------------------------------------------------------------------
;;; Operations that involve contexts.

(define-extended-language tt-ctxtL ttL
  ;; Telescope.
  ;; NB: There is a bijection between this an a vector of maps from x to t
  (Ξ Φ ::= hole (Π (x : t) Ξ))
  ;; Apply context
  ;; NB: There is a bijection between this an a vector expressions
  (Θ   ::= hole (Θ e)))

(define Ξ? (redex-match? tt-ctxtL Ξ))
(define Φ? (redex-match? tt-ctxtL Φ))
(define Θ? (redex-match? tt-ctxtL Θ))

;; TODO: Might be worth it to actually maintain the above bijections, for performance reasons.

;; Return the parameters of x_D as a telescope Ξ
;; TODO: Define generic traversals of Σ and Γ ?
(define-metafunction tt-ctxtL
  Σ-ref-parameter-Ξ : Σ x -> Ξ
  [(Σ-ref-parameter-Ξ (Σ (x_D : (in-hole Ξ U) any)) x_D)
   Ξ]
  [(Σ-ref-parameter-Ξ (Σ (x_1 : t_1 any)) x_D)
   (Σ-ref-parameter-Ξ Σ x_D)])

(module+ test
  (check-equiv?
    (term (Σ-ref-parameter-Ξ ,Σ nat))
    (term hole))
  (check-equiv?
    (term (Σ-ref-parameter-Ξ ,Σ4 and))
    (term (Π (A : Type) (Π (B : Type) hole)))))

;; Applies the term t to the telescope Ξ.
;; TODO: Test
;; TODO: This essentially eta-expands t at the type-level. Why is this necessary? Shouldn't it be true
;; that (equivalent t (Ξ-apply Ξ t))
(define-metafunction tt-ctxtL
  Ξ-apply : Ξ t -> t
  [(Ξ-apply hole t) t]
  [(Ξ-apply (Π (x : t) Ξ) t_0) (Ξ-apply Ξ (t_0 x))])

;; Compute the number of arguments in a Ξ
(define-metafunction tt-ctxtL
  Ξ-length : Ξ -> natural
  [(Ξ-length hole) 0]
  [(Ξ-length (Π (x : t) Ξ)) ,(add1 (term (Ξ-length Ξ)))])

;; Compute the number of applications in a Θ
(define-metafunction tt-ctxtL
  Θ-length : Θ -> natural
  [(Θ-length hole) 0]
  [(Θ-length (Θ e)) ,(add1 (term (Θ-length Θ)))])

;; Reference an expression in Θ by index; index 0 corresponds to the the expression applied to a hole.
(define-metafunction tt-ctxtL
  Θ-ref : Θ natural -> e or #f
  [(Θ-ref hole natural) #f]
  [(Θ-ref (in-hole Θ (hole e)) 0) e]
  [(Θ-ref (in-hole Θ (hole e)) natural) (Θ-ref Θ ,(sub1 (term natural)))])

;; TODO: The next 3 metafunctons are a mess. They should probably be organized like this:
;; Σ-elim-telescope : Σ x_D U -> Ξ
;;   This one should do all the work currently done in DTR-Elim_D
;; Σ-methods-telescope : Σ x_D t_P -> Ξ
;; Σ-constructor-method-telescope : Σ x_D x_c t_P -> Ξ
;; Σ-constructor-inductive-telescope : Σ x_D x_c -> Ξ
;; Σ-constructor-inductive-hypotheses : Σ x_D x_c t_P -> Ξ

;; Returns the inductive hypotheses required for eliminating the
;; inductively defined type x_D with motive t_P, where the telescope
;; Φ are the inductive arguments to a constructor for x_D
(define-metafunction tt-ctxtL
  hypotheses-for : x t Φ -> Φ
  [(hypotheses-for x_D t_P hole) hole]
  [(hypotheses-for x_D t_P (name any_0 (Π (x : (in-hole Φ (in-hole Θ x_D))) Φ_1)))
   (Π (x_h : (in-hole Φ ((in-hole Θ t_P) (Ξ-apply Φ x))))
      (hypotheses-for x_D t_P Φ_1))
   (where x_h ,(variable-not-in (term (x_D t_P any_0)) 'x-ih))])

;; Returns the inductive arguments to a constructor for the
;; inducitvely defined type x_D, where the telescope Φ are the
;; non-parameter arguments to the constructor.
(define-metafunction tt-ctxtL
  inductive-args : x Φ -> Φ
  [(inductive-args x_D hole) hole]
  [(inductive-args x_D (Π (x : (in-hole Φ (in-hole Θ x_D))) Φ_1))
   (Π (x : (in-hole Φ (in-hole Θ x_D))) (inductive-args x_D Φ_1))]
  ;; NB: Depends on clause order
  [(inductive-args x_D (Π (x : t) Φ_1))
   (inductive-args x_D Φ_1)])

;; Returns the methods required for eliminating the inductively
;; defined type x_D, whose constructors are ((x_ci : t_ci) ...), with motive t_P.
(define-metafunction tt-ctxtL
  methods-for : x t ((x : t) ...) -> Ξ
  [(methods-for x_D t_P ()) hole]
  [(methods-for x_D t_P (name any_0 ((x_ci : (in-hole Φ (in-hole Θ x_D)))
                          (x_c : t) ...)))
   (Π (x_mi : (in-hole Φ (in-hole Φ_h ((in-hole Θ t_P) (Ξ-apply Φ x_ci)))))
      (methods-for x_D t_P ((x_c : t) ...)))
   (where Φ_h (hypotheses-for x_D t_P (inductive-args x_D Φ)))
   (where x_mi ,(variable-not-in (term (x_D t_P any_0)) 'x-mi))])

(module+ test
  (check-equiv?
    (term (methods-for nat P ((zero : nat) (s : (Π (x : nat) nat)))))
    (term (Π (m-zero : (P zero))
             (Π (m-s : (Π (x : nat) (Π (ih-x : (P x)) (P (s x)))))
                hole))))
  ;; NB: does not pass because of removed reduction from methods-for
  (check-equiv?
    (term (methods-for nat (λ (x : nat) nat) ((zero : nat) (s : (Π (x : nat) nat)))))
    (term (Π (m-zero : nat) (Π (m-s : (Π (x : nat) (Π (ih-x : nat) nat)))
                                   hole))))
  ;; NB: does not pass because of removed reduction from methods-for
  (check-equiv?
    (term (methods-for and
                       (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B)) true)))
                       ((conj : (Π (A : Type) (Π (B : Type) (Π (a : A) (Π (b : B)
                                                                             ((and A) B)))))))))
    (term (Π (m-conj : (Π (A : Type) (Π (B : Type) (Π (a : A) (Π (b : B) true)))))
             hole)))
  (check-true (x? (term false)))
  (check-true (Ξ? (term hole)))
  (check-true (t? (term (λ (y : false) (Π (x : Type) x)))))
  (check-true (redex-match? ttL ((x : t) ...) (term ())))
  (check-equiv?
    (term (methods-for false (λ (y : false) (Π (x : Type) x))
                       ()))
    (term hole)))

;;; ------------------------------------------------------------------------
;;; Dynamic semantics

(define-extended-language tt-redL tt-ctxtL
  ;; NB: (in-hole Θv (elim x U)) is only a value when it's a partially applied elim.
  ;; TODO: Perhaps (elim x U) should step to an eta-expanded version of elim
  (v   ::= x U (Π (x : t) t) (λ (x : t) t) (elim x U) (in-hole Θv x) (in-hole Θv (elim x U)))
  (Θv  ::= hole (Θv v))
  ;; call-by-value, plus reduce under Π (helps with typing checking)
  (E   ::= hole (E e) (v E) (Π (x : v) E) (Π (x : E) e)))

(define Θv? (redex-match? tt-redL Θv))
(define E? (redex-match? tt-redL E))
(define v? (redex-match? tt-redL v))

(module+ test
  (check-true (v? (term (λ (x_0 : (Unv 0)) x_0))))
  (check-true (v? (term (refl Nat))))
  (check-true (v? (term ((refl Nat) z)))))

;; Create the recursive applications of elim to the recursive
;; arguments of an inductive constructor.
;; TODO: Poorly documented, and poorly tested.
;; Probably the source of issue #20
(define-metafunction tt-redL
  elim-recur : x U e Θ Θ Θ (x ...) -> Θ
  [(elim-recur x_D U e_P Θ
               (in-hole Θ_m (hole e_mi))
               (in-hole Θ_i (hole (in-hole Θ_r x_ci)))
               (x_c0 ... x_ci x_c1 ...))
   ((elim-recur x_D U e_P Θ Θ_m Θ_i (x_c0 ... x_ci x_c1 ...))
    (in-hole (Θ (in-hole Θ_r x_ci)) ((elim x_D U) e_P)))]
  [(elim-recur x_D U e_P Θ Θ_i Θ_nr (x ...)) hole])

(module+ test
  (check-true
    (redex-match? tt-redL (in-hole Θ_i (hole (in-hole Θ_r zero))) (term (hole zero))))
  (check-equiv?
    (term (elim-recur nat Type (λ (x : nat) nat)
                      ((hole (s zero)) (λ (x : nat) (λ (ih-x : nat) (s (s x)))))
                      ((hole (s zero)) (λ (x : nat) (λ (ih-x : nat) (s (s x)))))
                      (hole zero)
                      (zero s)))
    (term (hole (((((elim nat Type) (λ (x : nat) nat))
                   (s zero))
                  (λ (x : nat) (λ (ih-x : nat) (s (s x)))))
                 zero))))
  (check-equiv?
    (term (elim-recur nat Type (λ (x : nat) nat)
                      ((hole (s zero)) (λ (x : nat) (λ (ih-x : nat) (s (s x)))))
                      ((hole (s zero)) (λ (x : nat) (λ (ih-x : nat) (s (s x)))))
                      (hole (s zero))
                      (zero s)))
    (term (hole (((((elim nat Type) (λ (x : nat) nat))
                   (s zero))
                  (λ (x : nat) (λ (ih-x : nat) (s (s x)))))
                 (s zero))))))

(define tt-->
  (reduction-relation tt-redL
    (--> (Σ (in-hole E ((any (x : t_0) t_1) t_2)))
         (Σ (in-hole E (subst t_1 x t_2)))
         -->β)
    (--> (Σ (in-hole E (in-hole Θv ((elim x_D U) v_P))))
         (Σ (in-hole E (in-hole Θ_r (in-hole Θv_i v_mi))))
         #|
          | The elim form must appear applied like so:
          | (elim x_D U v_P m_0 ... m_i m_j ... m_n p ... (c_i a ...))
          |
          | Where:
          |   x_D       is the inductive being eliminated
          |   U         is the universe of the result of the motive
          |   v_P       is the motive
          |   m_{0..n}  are the methods
          |   p ...     are the parameters of x_D
          |   c_i       is a constructor of x_d
          |   a ...     are the arguments to c_i
          | Unfortunately, Θ contexts turn all this inside out:
          | TODO: Write better abstractions for this notation
          |#
          ;; Split Θv into its components
         (where (in-hole (Θv_p (in-hole Θv_i x_ci)) Θv_m) Θv)
         ;; Check that Θ_p actually matches the parameters of x_D, to ensure it doesn't capture other
         ;; arguments.
         (side-condition (equal? (term (Θ-length Θv_p)) (term (Ξ-length (Σ-ref-parameter-Ξ Σ x_D)))))
         ;; Ensure x_ci is actually a constructor for x_D
         (where (x_c* ...) (Σ-ref-constructors Σ x_D))
         (side-condition (memq (term x_ci) (term (x_c* ...))))
         ;; There should be a number of methods equal to the number of constructors; to ensure E
         ;; doesn't capture methods and Θv_m doesn't capture other arguments
         (side-condition (equal? (length (term (x_c* ...)))  (term (Θ-length Θv_m))))
         ;; Find the method for constructor x_ci, relying on the order of the arguments.
         (where v_mi (Θ-ref Θv_m (Σ-constructor-index Σ x_D x_ci)))
         ;; Generate the inductive recursion
         (where Θ_r (elim-recur x_D U v_P (in-hole Θv_p Θv_m) Θv_m Θv_i (x_c* ...)))
         -->elim)))

(define-metafunction tt-redL
  step : Σ e -> e
  [(step Σ e)
   e_r
   (where (_ e_r) ,(car (apply-reduction-relation tt--> (term (Σ e)))))])

(define-metafunction tt-redL
  reduce : Σ e -> e
  [(reduce Σ e)
   e_r
   (where (_ e_r)
     ,(let ([r (apply-reduction-relation* tt--> (term (Σ e)) #:cache-all? #t)])
        (unless (null? (cdr r))
          (error "Church-rosser broken" r))
        (car r)))])

;; TODO: Move equivalence up here, and use in these tests.
(module+ test
  (check-equiv? (term (reduce ∅ (Unv 0))) (term (Unv 0)))
  (check-equiv? (term (reduce ∅ ((λ (x : t) x) (Unv 0)))) (term (Unv 0)))
  (check-equiv? (term (reduce ∅ ((Π (x : t) x) (Unv 0)))) (term (Unv 0)))
  (check-equiv? (term (reduce ∅ (Π (x : t) ((Π (x_0 : t) x_0) (Unv 0)))))
                (term (Π (x : t) (Unv 0))))
  (check-equiv? (term (reduce ∅ (Π (x : t) ((Π (x_0 : t) (x_0 x)) x))))
                  (term (Π (x : t) (x x))))
  (check-equiv? (term (reduce ,Σ (((((elim nat Type) (λ (x : nat) nat))
                                                       (s zero))
                                    (λ (x : nat) (λ (ih-x : nat)
                                                        (s (s x)))))
                                   zero)))
                (term (s zero)))
  (check-equiv? (term (reduce ,Σ (((((elim nat Type) (λ (x : nat) nat))
                                                       (s zero))
                                    (λ (x : nat) (λ (ih-x : nat)
                                                        (s (s x)))))
                                   (s zero))))
                (term (s (s zero))))
  (check-equiv? (term (reduce ,Σ (((((elim nat Type) (λ (x : nat) nat))
                                                       (s zero))
                                    (λ (x : nat) (λ (ih-x : nat) (s (s x)))))
                                   (s (s (s zero))))))
                (term (s (s (s (s zero))))))

  (check-equiv?
    (term (reduce ,Σ
                  (((((elim nat Type) (λ (x : nat) nat))
                     (s (s zero)))
                    (λ (x : nat) (λ (ih-x : nat) (s ih-x))))
                   (s (s zero)))))
    (term (s (s (s (s zero))))))
  (check-equiv?
    (term (step ,Σ
                  (((((elim nat Type) (λ (x : nat) nat))
                     (s (s zero)))
                    (λ (x : nat) (λ (ih-x : nat) (s ih-x))))
                   (s (s zero)))))
    (term
      (((λ (x : nat) (λ (ih-x : nat) (s ih-x)))
        (s zero))
       (((((elim nat Type) (λ (x : nat) nat))
          (s (s zero)))
         (λ (x : nat) (λ (ih-x : nat) (s ih-x))))
        (s zero)))))
  (check-equiv?
    (term (step ,Σ (step ,Σ
                 (((λ (x : nat) (λ (ih-x : nat) (s ih-x)))
                   (s zero))
                  (((((elim nat Type) (λ (x : nat) nat))
                     (s (s zero)))
                    (λ (x : nat) (λ (ih-x : nat) (s ih-x))))
                   (s zero))))))
    (term
      ((λ (ih-x1 : nat) (s ih-x1))
       (((λ (x : nat) (λ (ih-x : nat) (s ih-x)))
         zero)
        (((((elim nat Type) (λ (x : nat) nat))
           (s (s zero)))
          (λ (x : nat) (λ (ih-x : nat) (s ih-x))))
         zero))))))

(define-judgment-form tt-redL
  #:mode (equivalent I I I)
  #:contract (equivalent Σ t t)

  [(where t_2 (reduce Σ t_0))
   (where t_3 (reduce Σ t_1))
   (α-equivalent t_2 t_3)
   ----------------- "≡-αβ"
   (equivalent Σ t_0 t_1)])

(define-extended-language tt-typingL tt-redL
  ;; NB: There may be a bijection between Γ and Ξ. That's
  ;; NB: interesting.
  (Γ   ::= ∅ (Γ x : t)))
(define Γ? (redex-match? tt-typingL Γ))

(define-metafunction tt-typingL
  Γ-union : Γ Γ -> Γ
  [(Γ-union Γ ∅) Γ]
  [(Γ-union Γ_2 (Γ_1 x : t))
   ((Γ-union Γ_2 Γ_1) x : t)])

;; NB: Depends on clause order
(define-metafunction tt-typingL
  Γ-ref : Γ x -> t or #f
  [(Γ-ref ∅ x) #f]
  [(Γ-ref (Γ x : t) x) t]
  [(Γ-ref (Γ x_0 : t_0) x_1) (Γ-ref Γ x_1)])

;; NB: Depends on clause order
(define-metafunction tt-typingL
  Γ-remove : Γ x -> Γ
  [(Γ-remove ∅ x) ∅]
  [(Γ-remove (Γ x : t) x) Γ]
  [(Γ-remove (Γ x_0 : t_0) x_1) (Γ-remove Γ x_1)])

;; TODO: Add positivity checking.
(define-metafunction ttL
  positive : t any -> #t or #f
  [(positive any_1 any_2) #t])
;; NB: These tests may or may not fail because positivity checking is not implemented.
(module+ test
  (check-true (term (positive nat nat)))
  (check-true (term (positive (Π (x : (Unv 0)) (Π (y : (Unv 0)) (Unv 0))) #f)))
  (check-true (term (positive (Π (x : nat) nat) nat)))
  ;; (nat -> nat) -> nat
  ;; Not sure if this is actually supposed to pass
  (check-false (term (positive (Π (x : (Π (y : nat) nat)) nat) nat)))
  ;; ((Unv 0) -> nat) -> nat
  (check-true (term (positive (Π (x : (Π (y : (Unv 0)) nat)) nat) nat)))
  ;; (((nat -> (Unv 0)) -> nat) -> nat)
  (check-true (term (positive (Π (x : (Π (y : (Π (x : nat) (Unv 0))) nat)) nat) nat)))
  ;; Not sure if this is actually supposed to pass
  (check-false (term (positive (Π (x : (Π (y : (Π (x : nat) nat)) nat)) nat) nat)))

  (check-true (term (positive (Unv 0) #f))))

;; Holds when the signature Σ and typing context Γ are well-formed.
(define-judgment-form tt-typingL
  #:mode (wf I I)
  #:contract (wf Σ Γ)

  [----------------- "WF-Empty"
   (wf ∅ ∅)]

  [(type-infer Σ Γ t t_0)
   (wf Σ Γ)
   ----------------- "WF-Var"
   (wf Σ (Γ x : t))]

  [(wf Σ ∅)
   (type-infer Σ ∅ t_D U_D)
   (type-infer Σ (∅ x_D : t_D) t_c U_c) ...
   ;; NB: Ugh this should be possible with pattern matching alone ....
   (side-condition ,(map (curry equal? (term Ξ_D)) (term (Ξ_D* ...))))
   (side-condition ,(map (curry equal? (term x_D)) (term (x_D* ...))))
   (side-condition (positive t_D (t_c ...)))
   ----------------- "WF-Inductive"
   (wf (Σ (x_D : (name t_D (in-hole Ξ_D t))
               ;; Checks that a constructor for x actually produces an x, i.e., that
               ;; the constructor is well-formed.
               ((x_c : (name t_c (in-hole Ξ_D* (in-hole Φ (in-hole Θ x_D*))))) ...))) ∅)])
(module+ test
  (check-true (judgment-holds (wf ,Σ0 ∅)))
  (check-true (redex-match? tt-redL (in-hole Ξ (Unv 0)) (term (Unv 0))))
  (check-true (redex-match? tt-redL (in-hole Ξ (in-hole Φ (in-hole Θ nat)))
                            (term (Π (x : nat) nat))))
  (define (bindings-equal? l1 l2)
    (map set=? l1 l2))
  (check-pred
    (curry bindings-equal?
           (list (list
                   (make-bind 'Ξ (term (Π (x : nat) hole)))
                   (make-bind 'Φ (term hole))
                   (make-bind 'Θ (term hole)))
                 (list
                   (make-bind 'Ξ (term hole))
                   (make-bind 'Φ (term (Π (x : nat) hole)))
                   (make-bind 'Θ (term hole)))))
    (map match-bindings (redex-match tt-redL (in-hole Ξ (in-hole Φ (in-hole Θ nat)))
                                     (term (Π (x : nat) nat)))))
  (check-pred
    (curry bindings-equal?
           (list
             (list
               (make-bind 'Φ (term (Π (x : nat) hole)))
               (make-bind 'Θ (term hole)))))
    (map match-bindings (redex-match tt-redL (in-hole hole (in-hole Φ (in-hole Θ nat)))
                                     (term (Π (x : nat) nat)))))

  (check-true
    (redex-match? tt-redL
                  (in-hole hole (in-hole hole (in-hole hole nat)))
                  (term nat)))
  (check-true
    (redex-match? tt-redL
                  (in-hole hole (in-hole (Π (x : nat) hole) (in-hole hole nat)))
                  (term (Π (x : nat) nat))))
  (check-holds (wf (∅ (nat : (Unv 0) ())) ∅))

  (check-holds (wf ,Σ0 ∅))
  (check-holds (type-infer ∅ ∅ (Unv 0) U))
  (check-holds (type-infer ∅ (∅ nat : (Unv 0)) nat U))
  (check-holds (type-infer ∅ (∅ nat : (Unv 0)) (Π (x : nat) nat) U))
  (check-true (term (positive nat (nat (Π (x : nat) nat)))))
  (check-holds
    (wf (∅ (nat : (Unv 0) ((zero : nat)))) ∅))
  (check-holds
    (wf (∅ (nat : (Unv 0) ((s : (Π (x : nat) nat))))) ∅))
  (check-holds (wf ,Σ ∅))

  (check-holds (wf ,Σ3 ∅))
  (check-holds (wf ,Σ4 ∅))
  (check-holds (wf (∅ (truth : (Unv 0) ())) ∅))
  (check-holds (wf ∅ (∅ x : (Unv 0))))
  (check-holds (wf (∅ (nat : (Unv 0) ())) (∅ x : nat)))
  (check-holds (wf (∅ (nat : (Unv 0) ())) (∅ x : (Π (x : nat) nat)))))


;; Holds when an apply context Θ provides arguments that match the
;; telescope Ξ
(define-judgment-form tt-typingL
  #:mode (telescope-types I I I I)
  #:contract (telescope-types Σ Γ Θ Ξ)

  [----------------- "TT-Hole"
   (telescope-types Σ Γ hole hole)]

  [(type-check Σ Γ e t)
   (telescope-types Σ Γ Θ Ξ)
   ----------------- "TT-Match"
   (telescope-types Σ Γ (in-hole Θ (hole e)) (Π (x : t) Ξ))])
(module+ test
  (check-holds
    (telescope-types ,Σ ∅ (hole zero) (Π (x : nat) hole)))
  (check-true
    (redex-match? tt-redL (in-hole Θ (hole e))
                  (term ((hole zero) (λ (x : nat) x)))))
  (check-holds
    (telescope-types ,Σ ∅ (hole zero)
                     (methods-for nat
                                  (λ (x : nat) nat)
                                  ((zero : nat)))))
  (check-holds
    (type-check ,Σ ∅ (λ (x : nat) (λ (ih-x : nat) x))
                (Π (x : nat) (Π (ih-x : nat) nat))))
  (check-holds
    (telescope-types ,Σ ∅
                     ((hole zero)
                      (λ (x : nat) (λ (ih-x : nat) x)))
                     (methods-for nat
                                  (λ (x : nat) nat)
                                  (Σ-ref-constructor-map ,Σ nat))))
  (check-holds
    (telescope-types (,Σ4 (true : (Unv 0) ((tt : true))))
                     ∅ (hole (λ (A : (Unv 0)) (λ (B : (Unv 0))
                                                    (λ (a : A) (λ (b : B) tt)))))
                     (methods-for and
                                  (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B)) true)))
                                  (Σ-ref-constructor-map ,Σ4 and))))
  (check-holds
    (telescope-types ,sigma (∅ x : false)
                     hole
                     (methods-for false (λ (y : false) (Π (x : Type) x))
                                  ()))))

;; TODO: Bi-directional and inference?
;; TODO: http://www.cs.ox.ac.uk/ralf.hinze/WG2.8/31/slides/stephanie.pdf

;; Holds when e has type t under signature Σ and typing context Γ
(define-judgment-form tt-typingL
  #:mode (type-infer I I I O)
  #:contract (type-infer Σ Γ e t)

  [(unv-ok U_0 U_1)
   (wf Σ Γ)
   ----------------- "DTR-Axiom"
   (type-infer Σ Γ U_0 U_1)]

  [(where t (Σ-ref-type Σ x))
   ----------------- "DTR-Inductive"
   (type-infer Σ Γ x t)]

  [(where t (Γ-ref Γ x))
   ----------------- "DTR-Start"
   (type-infer Σ Γ x t)]

  [(type-infer Σ Γ t_0 U_1)
   (type-infer Σ (Γ x : t_0) t U_2)
   (unv-kind U_1 U_2 U)
   ----------------- "DTR-Product"
   (type-infer Σ Γ (Π (x : t_0) t) U)]

  [(type-infer Σ Γ e_0 (Π (x_0 : t_0) t_1))
   (type-check Σ Γ e_1 t_0)
   (where t_3 (reduce Σ ((Π (x_0 : t_0) t_1) e_1)))
   ----------------- "DTR-Application"
   (type-infer Σ Γ (e_0 e_1) t_3)]

  [(type-infer Σ (Γ x : t_0) e t_1)
   (type-infer Σ Γ (Π (x : t_0) t_1) U)
   ----------------- "DTR-Abstraction"
   (type-infer Σ Γ (λ (x : t_0) e) (Π (x : t_0) t_1))]

  [(type-infer Σ Γ x_D (in-hole Ξ t_D))
   (where Ξ (Σ-ref-parameter-Ξ Σ x_D))
   ;; A fresh name to bind the discriminant
   (where x ,(variable-not-in (term (Σ Γ x_D Ξ)) 'x-D))
   ;; The telescope (∀ a -> ... -> (D a ...) hole), i.e.,
   ;; of the parameters and the inductive type applied to the
   ;; parameters
   (where Ξ_P*D (in-hole Ξ (Π (x : (Ξ-apply Ξ x_D)) hole)))
   ;; A fresh name for the motive
   (where x_P ,(variable-not-in (term (Σ Γ x_D Ξ Ξ_P*D x)) 'x-P))
   ;; The types of the methods for this inductive.
   (where Ξ_m (methods-for x_D x_P (Σ-ref-constructor-map Σ x_D)))
   ----------------- "DTR-Elim_D"
   (type-infer Σ Γ (elim x_D U)
     ;; The type of (elim x_D U) is something like:
     ;;  (∀ (P : (∀ a -> ... -> (D a ...) -> U))
     ;;     (method_ci ...) -> ... ->
     ;;     (a -> ... -> (D a ...) ->
     ;;       (P a ... (D a ...))))
     ;;
     ;; x_D   is an inductively defined type
     ;; U     is the sort the motive
     ;; x_P   is the name of the motive
     ;; Ξ_P*D is the telescope of the parameters of x_D and
     ;;       the witness of type x_D (applied to the parameters)
     ;; Ξ_m   is the telescope of the methods for x_D
     (Π (x_P : (in-hole Ξ_P*D U))
        ;; The methods Ξ_m for each constructor of type x_D
        (in-hole Ξ_m
          ;; And finally, the parameters and discriminant
          (in-hole Ξ_P*D
            ;; The result is (P a ... (x_D a ...)), i.e., the motive
            ;; applied to the paramters and discriminant
            (Ξ-apply Ξ_P*D x_P)))))])

(define-judgment-form tt-typingL
  #:mode (type-check I I I I)
  #:contract (type-check Σ Γ e t)

  [(type-infer Σ Γ e t_0)
   (equivalent Σ t t_0)
   ----------------- "DTR-Check"
   (type-check Σ Γ e t)])
(module+ test
  (check-holds (type-infer ∅ ∅ (Unv 0) (Unv 1)))
  (check-holds (type-infer ∅ (∅ x : (Unv 0)) (Unv 0) (Unv 1)))
  (check-holds (type-infer ∅ (∅ x : (Unv 0)) x (Unv 0)))
  (check-holds (type-infer ∅ ((∅ x_0 : (Unv 0)) x_1 : (Unv 0))
                           (Π (x_3 : x_0) x_1) (Unv 0)))
  (check-holds (type-infer ∅ (∅ x_0 : (Unv 0)) x_0 U_1))
  (check-holds (type-infer ∅ ((∅ x_0 : (Unv 0)) x_2 : x_0) (Unv 0) U_2))
  (check-holds (unv-kind (Unv 0) (Unv 0) (Unv 0)))
  (check-holds (type-infer ∅ (∅ x_0 : (Unv 0)) (Π (x_2 : x_0) (Unv 0)) t))

  (check-holds (type-infer ∅ ∅ (λ (x : (Unv 0)) x) (Π (x : (Unv 0)) (Unv 0))))
  (check-holds (type-infer ∅ ∅ (λ (y : (Unv 0)) (λ (x : y) x))
                           (Π (y : (Unv 0)) (Π (x : y) y))))

  (check-equal? (list (term (Unv 1)))
                (judgment-holds
                  (type-infer ∅ ((∅ x1 : (Unv 0)) x2 : (Unv 0)) (Π (t6 : x1) (Π (t2 : x2) (Unv 0)))
                              U)
                  U))
  ;; ---- Elim
  ;; TODO: Clean up/Reorganize these tests
  (check-true
    (redex-match? tt-typingL
                    (in-hole Θ_m (((elim x_D U) e_D) e_P))
                    (term ((((elim truth Type) T) (Π (x : truth) (Unv 1))) (Unv 0)))))
  (define Σtruth (term (∅ (truth : (Unv 0) ((T : truth))))))
  (check-holds (type-infer ,Σtruth ∅ truth (in-hole Ξ U)))
  (check-holds (type-infer ,Σtruth ∅ T (in-hole Θ_ai truth)))
  (check-holds (type-infer ,Σtruth ∅ (λ (x : truth) (Unv 1))
                           (in-hole Ξ (Π (x : (in-hole Θ truth)) U))))

  ;; NB: Does not pass due to removed reduction in methods-for
  (check-equiv?
    (term (methods-for truth (λ (x : truth) (Unv 1)) ((T : truth))))
    (term (Π (m-T : (Unv 1)) hole)))
  (check-holds (telescope-types ,Σtruth ∅ (hole (Unv 0))
                                (methods-for truth
                                             (λ (x : truth) (Unv 1))
                                             ((T : truth)))))
  (check-holds (type-infer ,Σtruth ∅ (elim truth Type) t))
  (check-holds (type-check (∅ (truth : (Unv 0) ((T : truth))))
                           ∅
                           ((((elim truth (Unv 2)) (λ (x : truth) (Unv 1))) (Unv 0))
                            T)
                           (Unv 1)))
  (check-not-holds (type-check (∅ (truth : (Unv 0) ((T : truth))))
                               ∅
                               ((((elim truth (Unv 1)) Type) Type) T)
                               (Unv 1)))
  (check-holds
    (type-infer ∅ ∅ (Π (x2 : (Unv 0)) (Unv 0)) U))
  (check-holds
    (type-infer ∅ (∅ x1 : (Unv 0)) (λ (x2 : (Unv 0)) (Π (t6 : x1) (Π (t2 : x2) (Unv 0))))
                t))
  (check-holds
    (type-infer ,Σ ∅ nat (in-hole Ξ U)))
  (check-holds
    (type-infer ,Σ ∅ zero (in-hole Θ_ai nat)))
  (check-holds
    (type-infer ,Σ ∅ (λ (x : nat) nat)
                (in-hole Ξ (Π (x : (in-hole Θ nat)) U))))
  (define-syntax-rule (nat-test syn ...)
    (check-holds (type-check ,Σ syn ...)))
  (nat-test ∅ (Π (x : nat) nat) (Unv 0))
  (nat-test ∅ (λ (x : nat) x) (Π (x : nat) nat))
  (nat-test ∅ (((((elim nat Type) (λ (x : nat) nat)) zero)
                                    (λ (x : nat) (λ (ih-x : nat) x))) zero)
            nat)
  (nat-test ∅ nat (Unv 0))
  (nat-test ∅ zero nat)
  (nat-test ∅ s (Π (x : nat) nat))
  (nat-test ∅ (s zero) nat)
  ;; TODO: Meta-function auto-currying and such
  (check-holds
      (type-infer ,Σ ∅ ((((elim nat (Unv 0)) (λ (x : nat) nat))
                           zero)
                           (λ (x : nat) (λ (ih-x : nat) x)))
                  t))
  (nat-test ∅ (((((elim nat (Unv 0)) (λ (x : nat) nat))
                    zero)
                    (λ (x : nat) (λ (ih-x : nat) x)))
                   zero)
              nat)
  (nat-test ∅ (((((elim nat (Unv 0)) (λ (x : nat) nat))
                    (s zero))
                    (λ (x : nat) (λ (ih-x : nat) (s (s x)))))
                   zero)
              nat)
  (nat-test ∅ (((((elim nat Type) (λ (x : nat) nat))
                              (s zero))
                                    (λ (x : nat) (λ (ih-x : nat) (s (s x))))) zero)
            nat)
  (nat-test (∅ n : nat)
    (((((elim nat (Unv 0)) (λ (x : nat) nat)) zero) (λ (x : nat) (λ (ih-x : nat) x))) n)
    nat)
  (check-holds
    (type-check (,Σ (bool : (Unv 0) ((btrue : bool) (bfalse : bool))))
                (∅ n2 : nat)
                (((((elim nat (Unv 0)) (λ (x : nat) bool))
                   btrue)
                  (λ (x : nat) (λ (ih-x : bool) bfalse)))
                 n2)
                bool))
  (check-not-holds
    (type-check ,Σ ∅
             ((((elim nat (Unv 0)) nat) (s zero)) zero)
                nat))
  (define lam (term (λ (nat : (Unv 0)) nat)))
  (check-equal?
    (list (term (Π (nat : (Unv 0)) (Unv 0))))
    (judgment-holds (type-infer ,Σ0 ∅ ,lam t) t))
  (check-equal?
    (list (term (Π (nat : (Unv 0)) (Unv 0))))
    (judgment-holds (type-infer ,Σ ∅ ,lam t) t))
  (check-equal?
    (list (term (Π (x : (Π (y : (Unv 0)) y)) nat)))
    (judgment-holds (type-infer (∅ (nat : (Unv 0) ())) ∅ (λ (x : (Π (y : (Unv 0)) y)) (x nat))
                                t) t))
  (check-equal?
    (list (term (Π (y : (Unv 0)) (Unv 0))))
    (judgment-holds (type-infer (∅ (nat : (Unv 0) ())) ∅ (λ (y : (Unv 0)) y) t) t))
  (check-equal?
    (list (term (Unv 0)))
    (judgment-holds (type-infer (∅ (nat : (Unv 0) ())) ∅
                                ((λ (x : (Π (y : (Unv 0)) (Unv 0))) (x nat))
                                 (λ (y : (Unv 0)) y))
                                t) t))
  (check-equal?
    (list (term (Unv 0)) (term (Unv 1)))
    (judgment-holds
      (type-infer ,Σ4 ∅ (Π (S : (Unv 0)) (Π (B : (Unv 0)) (Π (a : S) (Π (b : B) ((and S) B)))))
                  U) U))
  (check-holds
    (type-check ,Σ4 (∅ S : (Unv 0)) conj (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Π (a : A) (Π (b : B) ((and A) B)))))))
  (check-holds
    (type-check ,Σ4 (∅ S : (Unv 0))
                conj (Π (P : (Unv 0)) (Π (Q : (Unv 0)) (Π (x : P) (Π (y : Q) ((and P) Q)))))))
  (check-holds
    (type-check ,Σ4 (∅ S : (Unv 0)) S (Unv 0)))
  (check-holds
    (type-check ,Σ4 (∅ S : (Unv 0)) (conj S)
                (Π (B : (Unv 0)) (Π (a : S) (Π (b : B) ((and S) B))))))
  (check-holds
    (type-check ,Σ4 (∅ S : (Unv 0)) (conj S)
                (Π (B : (Unv 0)) (Π (a : S) (Π (b : B) ((and S) B))))))
  (check-holds
    (type-check ,Σ4 ∅ (λ (S : (Unv 0)) (conj S))
                (Π (S : (Unv 0)) (Π (B : (Unv 0)) (Π (a : S) (Π (b : B) ((and S) B)))))))
  (check-holds
    (type-check (,Σ4 (true : (Unv 0) ((tt : true)))) ∅
                ((((conj true) true) tt) tt)
                ((and true) true)))
  (check-holds
    (type-infer ,Σ4 ∅ and (in-hole Ξ U_D)))
  (check-holds
    (type-infer (,Σ4 (true : (Unv 0) ((tt : true)))) ∅
                ((((conj true) true) tt) tt)
                (in-hole Θ and)))
  (check-holds
    (type-infer (,Σ4 (true : (Unv 0) ((tt : true)))) ∅
                (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B)) true)))
                (in-hole Ξ (Π (x : (in-hole Θ_Ξ and)) U_P))))
  (check-holds
    (type-check (,Σ4 (true : (Unv 0) ((tt : true)))) ∅
             ((((((elim and (Unv 0))
                  (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B))
                                                 true))))
                 (λ (A : (Unv 0))
                    (λ (B : (Unv 0))
                       (λ (a : A)
                          (λ (b : B) tt)))))
                true) true)
              ((((conj true) true) tt) tt))
                true))
  (check-true (Γ? (term (((∅ P : (Unv 0)) Q : (Unv 0)) ab : ((and P) Q)))))
  (check-holds
    (type-infer ,Σ4 ∅ and (in-hole Ξ U)))
  (check-holds
    (type-infer ,Σ4 (((∅ P : Type) Q : Type) ab : ((and P) Q))
                ab (in-hole Θ and)))
  (check-true
    (redex-match? tt-redL
                  (in-hole Ξ (Π (x : (in-hole Θ and)) U))
                  (term (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Π (x : ((and A) B)) (Unv 0)))))))
  (check-holds
    (type-infer ,Σ4 (((∅ P : Type) Q : Type) ab : ((and P) Q))
                (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B))
                                               ((and B) A))))
                (in-hole Ξ (Π (x : (in-hole Θ and)) U))))
  (check-holds
    (equivalent ,Σ4
                (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Π (x : ((and A) B)) (Unv 0))))
                (Π (P : (Unv 0)) (Π (Q : (Unv 0)) (Π (x : ((and P) Q)) (Unv 0))))))
  (check-holds
    (type-infer ,Σ4 ∅
                (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B))
                                               ((and B) A))))
                (in-hole Ξ (Π (x : (in-hole Θ_Ξ and)) U_P))))
  (check-holds
    (type-check ,Σ4
                (((∅ P : (Unv 0)) Q : (Unv 0)) ab : ((and P) Q))
             ((((((elim and (Unv 0))
                  (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B))
                                                 ((and B) A)))))
                 (λ (A : (Unv 0))
                    (λ (B : (Unv 0))
                       (λ (a : A)
                          (λ (b : B) ((((conj B) A) b) a))))))
                P) Q) ab)
                ((and Q) P)))
  (check-holds
    (type-check (,Σ4 (true : (Unv 0) ((tt : true)))) ∅
                (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B)) ((and B) A))))
                (Π (A : (Unv 0)) (Π (B : (Unv 0)) (Π (x : ((and A) B)) (Unv 0))))))
  (check-holds
    (type-infer (,Σ4 (true : (Unv 0) ((tt : true))))
                ((∅ A : Type) B : Type)
                (conj B)
                t))
  (check-holds
    (type-check (,Σ4 (true : (Unv 0) ((tt : true)))) ∅
             ((((((elim and (Unv 0))
                  (λ (A : Type) (λ (B : Type) (λ (x : ((and A) B))
                                                 ((and B) A)))))
                 (λ (A : (Unv 0))
                    (λ (B : (Unv 0))
                       (λ (a : A)
                          (λ (b : B) ((((conj B) A) b) a))))))
                true) true)
              ((((conj true) true) tt) tt))
                ((and true) true)))
  (define gamma (term (∅ temp863 : pre)))
  (check-holds (wf ,sigma ∅))
  (check-holds (wf ,sigma ,gamma))
  (check-holds
    (type-infer ,sigma ,gamma (Unv 0) t))
  (check-holds
    (type-infer ,sigma ,gamma pre t))
  (check-holds
    (type-check ,sigma (,gamma tmp863 : pre) (Unv 0) (Unv 1)))
  (check-holds
    (type-infer ,sigma ,gamma pre t))
  (check-holds
    (type-check ,sigma (,gamma tmp863 : pre) (Unv 0) (Unv 1)))
  (check-holds
    (type-infer ,sigma (,gamma x : false) false (in-hole Ξ U_D)))
  (check-holds
    (type-infer ,sigma (,gamma x : false) x (in-hole Θ false)))
  (check-holds
    (type-infer ,sigma (,gamma x : false) (λ (y : false) (Π (x : Type) x))
                (in-hole Ξ (Π (x : (in-hole Θ false)) U))))
  (check-true
    (redex-match? tt-typingL
                  ((in-hole Θ_m ((elim x_D U) e_P)) e_D)
                  (term (((elim false (Unv 1)) (λ (y : false) (Π (x : Type) x)))
                         x))))
  (check-holds
    (type-check ,sigma (,gamma x : false)
                (((elim false (Unv 0)) (λ (y : false) (Π (x : Type) x))) x)
                (Π (x : (Unv 0)) x)))

  ;; nat-equal? tests
  (define zero?
    (term ((((elim nat Type) (λ (x : nat) bool))
            true)
           (λ (x : nat) (λ (x_ih : bool) false)))))
  (check-holds
    (type-check ,Σ ∅ ,zero? (Π (x : nat) bool)))
  (check-equal?
    (term (reduce ,Σ (,zero? zero)))
    (term true))
  (check-equal?
    (term (reduce ,Σ (,zero? (s zero))))
    (term false))
  (define ih-equal?
    (term ((((elim nat Type) (λ (x : nat) bool))
            false)
           (λ (x : nat) (λ (y : bool) (x_ih x))))))
  (check-holds
    (type-check ,Σ (∅ x_ih : (Π (x : nat) bool))
                ,ih-equal?
                (Π (x : nat) bool)))
  (check-holds
    (type-infer ,Σ ∅ nat (Unv 0)))
  (check-holds
    (type-infer ,Σ ∅ bool (Unv 0)))
  (check-holds
    (type-infer ,Σ ∅ (λ (x : nat) (Π (x : nat) bool)) (Π (x : nat) (Unv 0))))
  (define nat-equal?
    (term ((((elim nat Type) (λ (x : nat) (Π (x : nat) bool)))
            ,zero?)
           (λ (x : nat) (λ (x_ih : (Π (x : nat) bool))
                               ,ih-equal?)))))
  (check-holds
    (type-check ,Σ ∅
                ,nat-equal?
                (Π (x : nat) (Π (y : nat) bool))))
  (check-equal?
    (term (reduce ,Σ ((,nat-equal? zero) (s zero))))
    (term false))
  (check-equal?
    (term (reduce ,Σ ((,nat-equal? (s zero)) zero)))
    (term false))

  ;; == tests
  (define Σ= (term (,Σ (== : (Π (A : (Unv 0)) (Π (a : A) (Π (b : A) (Unv 0))))
                             ((refl : (Π (A : (Unv 0)) (Π (a : A) (((== A) a) a)))))))))
  (check-true (Σ? Σ=))

  (define refl-elim
    (term (((((((elim == (Unv 0)) (λ (A1 : (Unv 0)) (λ (x1 : A1) (λ (y1 : A1) (λ (p2 : (((==
                                                                                              A1)
                                                                                              x1)
                                                                                             y1))
                                                                                      nat)))))
              (λ (A1 : (Unv 0)) (λ (x1 : A1) zero))) bool) true) true) ((refl bool) true))))
  (check-holds
    (type-check ,Σ= ∅ ,refl-elim nat))
  (check-true
    (redex-match?
      tt-redL
      (Σ (in-hole E (in-hole Θ ((elim x_D U) e_P))))
      (term (,Σ= ,refl-elim))))
  (check-true
    (redex-match?
      tt-redL
      (in-hole (Θ_p (in-hole Θ_i x_ci)) Θ_m)
      (term (((((hole
              (λ (A1 : (Unv 0)) (λ (x1 : A1) zero))) bool) true) true) ((refl bool) true)))))
  (check-equiv?
    (term (Σ-ref-parameter-Ξ ,Σ= ==))
    (term (Π (A : Type) (Π (a : A) (Π (b : A) hole)))))
  (check-equal?
    (term (reduce ,Σ= ,refl-elim))
    (term zero)))