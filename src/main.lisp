(defpackage afp-forth-demo
  (:use :cl)
  (:export
   #:*new-forth*
   #:*forth-registers*))

(in-package :afp-forth-demo)

(named-readtables:in-readtable :reader-macros)

#|
registers on the forth machine
- pstack : parameter stack (where parameters will be stored until operation requires them)
- rstack : return stack (holds the instruction of the operation (i.e. forth word) to execute)
- dict : dictionary of words
- compiling :
- dtable : abstract register that maps a forth word to the list structure that created at the
  time that forth was created.
|#
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter *logging-turned-on* nil)
  (defparameter *logging-forth-word-generation* nil)

  (defvar *forth-registers*
    '(pstack rstack pc dict compiling dtable))

  #|

  defines the words in the dictionary
  dictionary = linked list of words that we would use to see if a word is defined.
  name - name of symbol
  prev - previous pointer to previous word in dictionary
  immediate - whether or not word is evaluated at compile-time or run-time like a lisp macro
  thread - used in metaprogramming as well. This helps in determining how to structure code
  specifically, on what level of indirection should a word be compiled to one of the following
  strategies:
  - calling a subroutine (subroutine-threaded code)
  - calling an adjacent memory cell pointing to an instruction (so called indirect/direct threaded code)
  - accessing a fixnum that representing a pointer to the word in the same compilation thread (token threading)
  - Take advantage of Lisp's dynamic typing and cons cell list structure to access the next execution
  form (called cons-threaded code in the book).
  defines:
  - forth-word-name, forth-word-prev, forth-word-immediate, forth-word-thread
  |#
  (defstruct forth-word
    name
    prev
    immediate
    thread)

  (defun forth-lookup (w top-word)
    "lookup word W in dictionary starting at TOP-WORD."
    (if top-word
        (if (eql (forth-word-name top-word) w)
            top-word
            (forth-lookup w (forth-word-prev top-word)))))

  ;; Common Lisp
  ;; (+ 1 2)
  ;; Forth
  ;; 1 2 +
  (defmacro forth-inner-interpreter ()
    "simple interpreter for forth"
    `(loop
       :do (progn
             (when *logging-turned-on*
               (format t "Environment Info~%")
               (format t "----------------~%")
               ;;(format t "Program Counter: ~A~%" pc)
               ;;(format t "rstack: ~A~%" rstack)
               (format t "pstack: ~A~%" pstack))
             (cond
               ((functionp (car pc))
                (progn
                  (when *logging-turned-on*
                    (format t "calling function~%"))
                  (funcall (car pc))))
               ((consp (car pc))
                (progn
                  (when *logging-turned-on*
                    (format t "executing code block. pushing onto rstack...~%"))
                  (push (cdr pc) rstack)
                  (setf pc (car pc))))
               ((null pc)
                (progn
                  (when *logging-turned-on*
                    (format t "returning from function call~%"))
                  (setf pc (pop rstack))))
               (t
                (when *logging-turned-on*
                  (format t "setting up program counter~%"))
                (push (car pc) pstack)
                (setf pc (cdr pc)))))
       :until (and (null pc) (null rstack))))

  ;; dictionary of primitives forms
  ;; prim-form: (name immediate . forms)
  (defparameter *forth-primitive-forms* nil)

  ;;
  (defmacro define-forth-naked-primitive (&body code)
    `(push ',code *forth-primitive-forms*))

  (defmacro define-forth-primitive (&body code)
    `(define-forth-naked-primitive
       ,@code
       (setf pc (cdr pc))))

  ;; NOP - no operation
  (define-forth-primitive nop nil)

  ;; dup - duplicate argument on pstack
  (define-forth-primitive dup nil
    (push (car pstack) pstack))

  ;; swap
  (define-forth-primitive swap nil
    (rotatef (car pstack) (cadr pstack)))

  (define-forth-primitive print nil
    (print (pop pstack)))

  (define-forth-primitive >r nil
    (push (pop pstack) rstack))

  (define-forth-primitive r> nil
    (push (pop rstack) pstack))

  ;; drop nil
  (define-forth-primitive drop nil
    (pop pstack))

  ;; recall once-only macro usage
  (defmacro square (x)
    (alexandria:once-only (x)
      `(* ,x ,x)))

  (square (+ 1 2))

  (defmacro go-forth (forth &body words)
    (alexandria:once-only (forth)
      `(dolist (w ',words)
         (funcall ,forth w))))

  ;; variable representing our standard library
  (defparameter *forth-stdlib* '())

  (defmacro forth-stdlib-add (&body all)
    `(setf *forth-stdlib*
           (nconc *forth-stdlib*
                  ',all)))

  (defmacro new-forth-interpreter ()
    `(anaphoric-macros:alet% ,*forth-registers*
                             (setf dtable (make-hash-table))
                             (when *logging-turned-on*
                               (format t "initializing primitives...~%"))
                             (forth-install-primitives)
                             (when *logging-turned-on*
                               (format t "compiling/adding standard library-functions...~%"))
                             (dolist (v *forth-stdlib*)
                               (funcall anaphoric-macros::this v))
                             (when *logging-turned-on*
                               (format t "creation of interpreter object...~%"))
                             (pandoric-macros:plambda (v) ,*forth-registers*
                               (let ((word (forth-lookup v dict)))
                                 (if word
                                     (forth-handle-found)
                                     (forth-handle-not-found))))))

  (defmacro forth-install-primitives ()
    `(progn
       ,@(mapcar #`(let ((thread (lambda () ,@(cddr a1))))
                     (when *logging-forth-word-generation*
                       (format t "Forth word Info~%")
                       (format t "---------------~%")
                       (format t "Name: ~A~%" ',(car a1))
                       (format t "Immediate: ~A~%" ,(cadr a1))
                       (format t "----------------~%"))
                     (setf dict (make-forth-word
                                 :name ',(car a1)
                                 :prev dict
                                 :immediate ,(cadr a1)
                                 :thread thread)
                           (gethash thread dtable) ',(cddr a1)))
                 *forth-primitive-forms*)))

  #|
  Immediate mode is a mode in forth programming systems that deals with
  determining if a set of forth code is compiled or directly executed
  using a flag.
  if zero, the interpreter is in regular interpreting or executing state
  if nonzero, the interpreter is in compilation state which means that word is only executed if its an immediate word otherwise
  it is compiled.|#

  ;; [interpreting words in forth]
  ;; ] compiling words in forth [
  ;; these two primitives defines out to get in/out immediate mode
  (define-forth-primitive  [ t          ; <- t means immediate
    (setf compiling nil))
  (define-forth-primitive ] nil         ; <- not immediate
    (setf compiling t))

  (defmacro forth-compile-in (v)
    `(setf (forth-word-thread dict)
           (nconc (forth-word-thread dict)
                  (list ,v))))

  (defmacro forth-handle-found ()
    `(progn
       (when *logging-turned-on*
         (format t "Environment Info~%")
         (format t "----------------~%")
         ;;(format t "Program Counter: ~A~%" pc)
         ;;(format t "rstack: ~A~%" rstack)
         (format t "pstack: ~A~%" pstack))
       (if (and compiling
                (not (forth-word-immediate word)))
           (progn
             (when *logging-turned-on*
               (format t "compiling ~A...~%" (forth-word-name word)))
             (forth-compile-in (forth-word-thread word)))
           (progn
             (when *logging-turned-on*
               (format t "setting up ~A to be interpreted...~%"
                       (forth-word-name word)))
             (setf pc (list (forth-word-thread word)))
             (forth-inner-interpreter)))))

  (defmacro forth-handle-not-found ()
    `(progn
       (when *logging-turned-on*
         (format t "Environment Info~%")
         (format t "----------------~%")
         (format t "Program Counter: ~A~%" pc)
         (format t "rstack: ~A~%" rstack)
         (format t "pstack: ~A~%" pstack))
       (cond
         ((and (consp v) (eq (car v) 'quote))
          (if compiling
              (forth-compile-in (cadr v))
              (push (cadr v) pstack)))
         ((and (consp v) (eq (car v) 'postpone))
          (let ((word (forth-lookup (cadr v) dict)))
            (if (not word)
                (error "Postpone failed: ~a" (cadr v)))
            (forth-compile-in (forth-word-thread word))))
         ((symbolp v)
          (error "Word ~a is not found" v))
         (t
          (if compiling
              (forth-compile-in v)
              (progn
                (when *logging-turned-on*
                  (format t "pushing ~A onto pstack~%" v))
                (push v pstack)))))))

  ;;
  ;; creating more forth words for our dictionary to do stuff beyond simple math
  ;;
  (define-forth-primitive create nil
    (setf dict (make-forth-word :prev dict)))

  (define-forth-primitive name nil
    (setf (forth-word-name dict) (pop pstack)))

  (define-forth-primitive immediate nil
    (setf (forth-word-immediate dict) t))


  ;; defining fetch(@) and store(!) for storing/retrieval from memory using cons cells
  (define-forth-primitive @ nil
    (push (car (pop pstack))
          pstack))

  (define-forth-primitive ! nil
    (let ((location (pop pstack)))
      (setf (car location) (pop pstack))))

  (defmacro forth-unary-word-definer (&rest words)
    `(progn
       ,@(mapcar
          #`(define-forth-primitive ,a1 nil
              (push (,a1 (pop pstack))
                    pstack))
          words)))

  (defmacro forth-binary-word-definer (&rest words)
    (alexandria:with-gensyms (top)
      `(progn
         ,@(mapcar
            #`(define-forth-primitive ,a1 nil
                (let ((,top (pop pstack)))
                  (push (,a1 (pop pstack)
                             ,top)
                        pstack)))
            words))))

  ;; grab a bunch of common lisp unary operations useful for forth programming
  (forth-unary-word-definer
   not car cdr cadr caddr cadddr cadar oddp evenp)

  (forth-binary-word-definer
   eq equal + - * / = < > <= >= max min and or)

  ;; add create to the standard library
  (forth-stdlib-add create
    ] create ] [
    '{ name)

  (forth-stdlib-add {
    (postpone [) [
    '} name immediate)

  (define-forth-naked-primitive branch-if nil
    (setf pc (if (pop pstack)
                 (cadr pc)
                 (cddr pc))))

  (forth-stdlib-add
    { r> drop } 'exit name)

  (define-forth-naked-primitive compile nil
    (setf (forth-word-thread dict)
          (nconc (forth-word-thread dict)
                 (list (cadr pc)))
          pc (cddr pc)))

  (define-forth-primitive here nil
    (push (last (forth-word-thread dict))
          pstack))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;
  ;; words for metaprogramming in forth
  ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (forth-stdlib-add
    { compile not
    compile branch-if
    compile nop
    here } 'if name immediate)

  (forth-stdlib-add
    { compile nop
    here swap ! } 'then name immediate)

  (forth-stdlib-add
    { compile 't
    compile branch-if
    compile nop
    here swap
    compile nop
    here swap ! } 'else name immediate)

  (forth-stdlib-add
    { compile nop
    here } 'begin name immediate
    { compile 't
    compile branch-if
    compile nop
    here ! } 'again name immediate)


  (forth-stdlib-add
    { 0 swap - } 'negate name)

  (forth-stdlib-add
    { dup 0 < if negate then } 'abs name)

  (forth-stdlib-add
    { evenp if 0 else 1 then } 'mod2 name)

  (defparameter *new-forth* (new-forth-interpreter))
  (defun get-forth-thread (forth word)
    (pandoric-macros:with-pandoric (dict) forth
      (forth-word-thread
       (forth-lookup word dict))))

  (defun print-forth-thread (forth word)
    (let ((*print-circle* t))
      (print (get-forth-thread forth word))))

  (defmacro assemble-flub (form rest)
    `(if (gethash c go-ht)
         (list* (gethash c go-ht)
                ,form
                ,rest)
         (list* ,form ,rest)))

  (defmacro flubify-aux ()
    `(anaphoric-macros:alambda (c)
       (if c
           (cond
             ((gethash (car c) prim-ht)
              (assemble-flub
               `(funcall
                 ,(gethash (car c) prim-ht))
               (anaphoric-macros:self (cdr c))))
             ((gethash (car c) thread-ht)
              (assemble-flub
               `(funcall #',(car (gethash (car c) thread-ht)))
               (anaphoric-macros:self (cdr c))))
             ((eq (car c) branch-if)
              (assemble-flub
               `(if (pop pstack)
                    (go ,(gethash (cadr c) go-ht)))
               (anaphoric-macros:self (cddr c))))
             ((consp (car c))
              (flubify forth (car c) prim-ht thread-ht branch-if)
              (anaphoric-macros:self c))
             (t
              (assemble-flub
               `(push ',(car c) pstack)
               (anaphoric-macros:self (cdr c))))))))

  (defun flubify (forth thread prim-ht thread-ht branch-if)
    (unless #1=(gethash thread thread-ht)
            (setf #1# (list (gensym)))
            (let ((go-ht (make-hash-table)))
              (funcall
               (anaphoric-macros:alambda (c)
                 (when c
                   (cond
                     ((eq (car c) branch-if)
                      (setf (gethash (cadr c) go-ht)
                            (gensym))
                      (anaphoric-macros:self (cddr c)))
                     ((consp (car c))
                      (flubify forth thread prim-ht thread-ht branch-if)))
                   (anaphoric-macros:self (cdr c))))
               thread)
              (setf #1# (nconc #1# (funcall (flubify-aux) thread))))))

  (defun compile-flubified (thread thread-ht)
    `(labels (,@(let (collect)
                  (maphash
                   (lambda (k v)
                     (declare (ignore k))
                     (push
                      `(,(car v) () (tagbody ,@(cdr v)))
                      collect))
                   thread-ht)
                  (nreverse collect)))
       (funcall #',(car (gethash thread thread-ht)))))

  (defun flubify-thread-shaker (forth thread ht tmp-ht branch-if compile)
    (if (gethash thread tmp-ht)
        (return-from flubify-thread-shaker)
        (setf (gethash thread tmp-ht) t))
    (cond
      ((and (consp thread) (eq (car thread) branch-if))
       (if (cddr thread)
           (flubify-thread-shaker forth (cddr thread) ht tmp-ht branch-if compile)))
      ((and (consp thread) (eq (car thread) compile))
       (error "Can't convert compiling word to lisp"))
      ((consp thread)
       (flubify-thread-shaker forth (car thread) ht tmp-ht branch-if compile)
       (if (cdr thread)
           (flubify-thread-shaker forth (cdr thread) ht tmp-ht branch-if compile)))
      ((not (gethash thread ht))
       (if (functionp thread)
           (setf (gethash thread ht)
                 (pandoric-macros:with-pandoric (dtable) forth
                   (gethash thread dtable)))))))

  (defun forth-to-lisp (forth word)
    (let ((thread (get-forth-thread forth word))
          (shaker-ht (make-hash-table))
          (prim-ht (make-hash-table))
          (thread-ht (make-hash-table))
          (branch-if (get-forth-thread forth 'branch-if))
          (compile (get-forth-thread forth 'compile)))
      (flubify-thread-shaker forth thread shaker-ht (make-hash-table) branch-if compile)
      (maphash (lambda (k v)
                 (declare (ignore v))
                 (setf (gethash k prim-ht) (gensym)))
               shaker-ht)
      (flubify forth thread prim-ht thread-ht branch-if)
      `(let (pstack)
         (let (,@(let (collect)
                   (maphash (lambda (k v)
                              (push `(,(gethash k prim-ht)
                                      (lambda () ,@(butlast v)))
                                    collect))
                            shaker-ht)
                   (nreverse collect)))
           ,(compile-flubified thread thread-ht)))))
  )

;; clumsy way of using our forth interpreter (pre go-forth)
;; forth code : 3 dup * print
(progn
  (funcall *new-forth* 3)
  (funcall *new-forth* 'dup)
  (funcall *new-forth* '*)
  (funcall *new-forth* 'print))

;; simple example of push stuff onto parameter stack
(go-forth *new-forth* 1 2.0 "three" 'four '(f i v e))

(pandoric-macros:with-pandoric (pstack) *new-forth*
  pstack)

;; examples from book on running forth code in our interpreter
;;
;;
(go-forth *new-forth*
  3 dup * print)

;; example of go in and out of compilation mode use []
(go-forth *new-forth*
  create)
(go-forth *new-forth*
  ] dup * [)

#|
above code creates a way of defining functions without using forth's backward balanced
brackets we introduced earlier. below is an example
|#
(setf *new-forth* (new-forth-interpreter))

;;equivalent to
(go-forth *new-forth*
   { dup * } 'square name)
(go-forth *new-forth*
 { square square } 'quartic name)

;; label previous code that we put in compilation mode to square (defining a function)
;; (go-forth *new-forth*
;;   'square name)
;; ;; use function
;; (go-forth *new-forth*
;;   3 square print)

;; (go-forth *new-forth*
;;   5 square print)

;; (go-forth *new-forth*
;;   { dup + } 'double name)

;; (go-forth *new-forth*
;;   5 double square print)

;; (go-forth *new-forth*
;;   1/2 square print)

(go-forth *new-forth*
  { 3 } 'three name
  three three * print)

(go-forth *new-forth*
  { 4.0 } '4 name
  4 4 * print)

(setf *new-forth* (new-forth-interpreter))
(go-forth *new-forth*
  1 '(nil) ! @ print)


(forth-stdlib-add
  { compile branch-if } 'compiled-branch-if name immediate)

(go-forth (setf *new-forth* (new-forth-interpreter))
  { 2 * } 'double name
  { branch-if double "Not doubling" print } 'if-then-double name)

(go-forth *new-forth*
  4 'nil if-then-double print)

(go-forth *new-forth*
  4 't if-then-double print)

(go-forth *new-forth*
  { "exiting..." print
  exit
  "exited" print                        ; this will never get executed
  } 'exit-test name
  exit-test)


(go-forth *new-forth* 5 '(nil) ! )
(go-forth *new-forth* @ print)

(go-forth *new-forth* -5 negate print)

(go-forth (setf *new-forth* (new-forth-interpreter))
  { dup 0 < if negate then } 'abs name)

(setf *logging-turned-on* nil)

(go-forth *new-forth*
  { "hello" print } 'printhello name)
(go-forth *new-forth*
  { if "yes" print then } 'check-condition name)

(go-forth *new-forth* 4 5 < check-condition)
(go-forth *new-forth* 4 5 > check-condition)
(go-forth *new-forth* "hello" print)
(go-forth *new-forth* printhello )
;; (go-forth *new-forth* 4 5 < if "hello" print then )

(go-forth *new-forth* -5 abs print)
(go-forth *new-forth* 5 abs print)

;; usages of mod2
(go-forth *new-forth* 4 mod2 print)
(go-forth *new-forth* 1 mod2 print)

;; example of begin example
(go-forth *new-forth*
  { begin
  dup 1 < if drop exit then
  dup print
  1 -
  again } 'countdown name)
(go-forth *new-forth*
  5 countdown)

(go-forth *new-forth*
  1 countdown)

;; example of swapping pointers made by begin and if so that
;; again and then are run out of order
(go-forth *new-forth*
  { begin
  dup 1 >= if
  dup print
  1 -
  [ swap ]
  again
  then
  drop } 'countdown-for-teh-hax0rz name)

(go-forth *new-forth*
  { 5 countdown-for-teh-hax0rz } 'countdown5 name)

(go-forth *new-forth* 5 countdown-for-teh-hax0rz)
(go-forth *new-forth* countdown5)

(print (forth-to-lisp *new-forth* 'countdown-for-teh-hax0rz))
(compile (forth-to-lisp *new-forth* 'countdown5))
(compile 'countdown-5 (lambda () (forth-to-lisp *new-forth* 'countdown5)))
;; above compiles to
;; (go-forth *new-forth*
;;   { branch-if "yes" "no" print } 'check-condition name immediate)

;; (go-forth *new-forth* -5 abs print)

;; call this for debugging

(pandoric-macros:with-pandoric (pstack rstack) *new-forth*
  (format t "~%pstack:~A~%rstack:~A~%" pstack rstack))

(pandoric-macros:with-pandoric (dict) *new-forth*
  (print (forth-lookup 'again dict)))

(go-forth *new-forth*
  { dup * } 'square name
  { square square } 'quartic name)

(go-forth *new-forth*
  { dup * } 'square name
  { 3 square print } 'square3 name)

(print-forth-thread *new-forth* 'square3)
(print (forth-to-lisp *new-forth* 'square3))


;; example of full recursion
(go-forth *new-forth*
  { [ 'fact name ]
  dup 1 -
  dup 1 > if fact then * })

(go-forth *new-forth*
  { 5 fact print } 'fact5 name)

(eval (forth-to-lisp *new-forth* 'fact5))

(go-forth *new-forth* 5 fact print)

(print-forth-thread *new-forth* 'fact)
