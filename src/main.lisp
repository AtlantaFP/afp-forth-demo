(defpackage afp-forth-demo
  (:use :cl)
  (:export
   #:*new-forth*
   #:*forth-registers*))

(in-package :afp-forth-demo)

(named-readtables:in-readtable :reader-macros)
(defparameter *logging-turned-on* 't)
(defparameter *logging-forth-word-generation* nil)

#|
registers on the forth machine
- pstack : parameter stack (where parameters will be stored until operation requires them)
- rstack : return stack (holds the instruction of the operation (i.e. forth word) to execute)
- dict : dictionary of words
- compiling :
- dtable :
|#
(eval-when (:compile-toplevel :load-toplevel :execute)
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
              (format t "Program Counter: ~A~%" pc)
              (format t "rstack: ~A~%" rstack)
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
         (format t "Program Counter: ~A~%" pc)
         (format t "rstack: ~A~%" rstack)
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

  (forth-stdlib-add
    { compile not
    compile branch-if
    compile nop
    here } 'if name immediate)

  (forth-stdlib-add
    { compile nop
    here swap ! } 'then name immediate)

  (forth-stdlib-add
    { 0 swap - } 'negate name)

  (forth-stdlib-add
    { dup 0 < if negate then } 'abs name)
)

;; clumsy way of using our forth interpreter (pre go-forth)
;; forth code : 3 dup * print
;; (progn
;;   (funcall *new-forth* 3)
;;   (funcall *new-forth* 'dup)
;;   (funcall *new-forth* '*)
;;   (funcall *new-forth* 'print))

;; ;; simple example of push stuff onto parameter stack
;; (go-forth *new-forth* 1 2.0 "three" 'four '(f i v e))

;; (pandoric-macros:with-pandoric (pstack) *new-forth*
;;   pstack)

;; ;; examples from book on running forth code in our interpreter
;; ;;
;; ;;
;; (go-forth *new-forth*
;;   3 dup * print)

;; ;; example of go in and out of compilation mode use []
;; (go-forth *new-forth*
;;   create)
;; (go-forth *new-forth*
;;   ] dup * [)
;; ;; label previous code that we put in compilation mode to square (defining a function)
;; (go-forth *new-forth*
;;   'square name)
;; ;; use function
;; (go-forth *new-forth*
;;   3 square print)

;; #|
;; above code creates a way of defining functions without using forth's backward balanced
;; brackets we introduced earlier. below is an example
;; |#
;; (setf *new-forth* (new-forth-interpreter))

;; equivalent to
;; (defun square (x) (* x x))
;; (go-forth *new-forth*
;;    { dup * } 'square name)

;; (go-forth *new-forth*
;;   5 square print)

;; (go-forth *new-forth*
;;   { dup + } 'double name)

;; (go-forth *new-forth*
;;   5 double square print)

;; (go-forth *new-forth*
;;   1/2 square print)

;; (go-forth *new-forth*
;;   { 3 } 'three name
;;   three three * print)

;; (go-forth *new-forth*
;;   { 4.0 } '4 name
;;   4 4 * print)

;; (setf *new-forth* (new-forth-interpreter))
;; (go-forth *new-forth*
;;   1 '(nil) ! @ print)

;; (go-forth *new-forth*
;;  { square square } 'quartic name)

;; (forth-stdlib-add
;;   { compile branch-if } 'compiled-branch-if name immediate)

;; (go-forth (setf *new-forth* (new-forth-interpreter))
;;   { 2 * } 'double name
;;   { branch-if double "Not doubling" print } 'if-then-double name)

;; (go-forth *new-forth*
;;   4 'nil if-then-double print)

;; (go-forth *new-forth*
;;   4 't if-then-double print)

;; (go-forth *new-forth*
;;   { "exiting..." print
;;   exit
;;   "exited" print                        ; this will never get executed
;;   } 'exit-test name
;;   exit-test)


;; (go-forth *new-forth* 5 '(nil) ! )
;; (go-forth *new-forth* @ print)

;; (go-forth *new-forth* -5 negate print)

;; (step (go-forth (setf *new-forth* (new-forth-interpreter))
;;    { dup 0 < if negate then } 'abs name))

(setf *logging-turned-on* 't)

(defparameter *new-forth* (new-forth-interpreter))
(go-forth *new-forth*
  { "hello" print } 'printhello name)

(go-forth *new-forth* "hello" print)
(go-forth *new-forth* printhello )

(go-forth *new-forth*
  4 5 < not branch-if nop here printhello nop here swap !)
(go-forth *new-forth*
  4 5 < if printhello then )

(go-forth *new-forth*
  4 5 > not branch-if nop here printhello nop here swap !)
;; above compiles to
;; (go-forth *new-forth*
;;   { branch-if "yes" "no" print } 'check-condition name immediate)

(go-forth *new-forth* -5 abs print)

;; call this for debugging

(pandoric-macros:with-pandoric (pstack rstack) *new-forth*
  (format t "pstack:~A~%rstack:~A~%" pstack rstack))


(go-forth *new-forth*
  { dup * } 'square name
  { square square } 'quartic name)

(pandoric-macros:with-pandoric (dict) *new-forth*
  (forth-word-thread
   (forth-lookup 'quartic dict)))

(let ((*print-circle* t))
  (print *)
  t)
