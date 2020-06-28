(defpackage afp-forth-demo
  (:use :cl)
  (:export
   #:*forth-registers*))

(in-package :afp-forth-demo)

(named-readtables:in-readtable :reader-macros)

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
    '(pstack rstack pc dict compiling dtable)))

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
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defmacro forth-inner-interpreter ()
    "simple interpreter for forth"
    `(loop
       :do (cond
             ((functionp (car pc)) (funcall (car pc)))
             ((consp (car pc))
              (push (cdr pc) rstack)
              (setf pc (car pc)))
             ((null pc)
              (setf pc (pop rstack)))
             (t
              (push (car pc) pstack)
              (setf pc (cdr pc))))
       :until (and (null pc) (null rstack)))))

;; dictionary of primitives forms
;; prim-form: (name immediate . forms)
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter *forth-primitive-forms* nil))

;;
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defmacro def-forth-naked-prim (&body code)
    `(push ',code *forth-primitive-forms*))

  (defmacro define-forth-primitive (&body code)
    `(def-forth-naked-prim
       ,@code
       (setf pc (cdr pc)))))

;; NOP - no operation
(define-forth-primitive nop nil)

(define-forth-primitive * nil
  (push (* (pop pstack) (pop pstack)) pstack))

(define-forth-primitive + nil
  (push (+ (pop pstack) (pop pstack)) pstack))

;; a b - => b - a
(define-forth-primitive - nil
  (push (- (pop pstack) (pop pstack)) pstack))

(define-forth-primitive / nil
  (push (/ (pop pstack) (pop pstack)) pstack))

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

;; sketch of forth interpreter that will load up initial dictionary and start
;; looking through passed in
;; (defmacro new-forth-interpreter ()
;;   `(let ,forth-registers
;;      (forth-install-primitives)
;;      (lambda (v)
;;        (let ((word (forth-lookup v dict)))
;; 	 (if word
;; 	     (forth-handle-found)
;; 	     (forth-handle-not-found))))))


;; ;; clumsy way of using our forth interpreter (pre go-forth)
;; ;; forth code : 3 dup * print
;; (progn
;;   (funcall *new-forth* 3)
;;   (funcall *new-forth* 'dup)
;;   (funcall *new-forth* '*)
;;   (funcall *new-forth* 'print))

(defmacro square (x)
  (alexandria:once-only (x)
    `(* ,x ,x)))

(square (+ 1 2))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defmacro go-forth (forth &body words)
    (alexandria:once-only (forth)
      `(dolist (w ',words)
         (funcall ,forth w)))))

;; variable representing our standard library
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar *forth-stdlib* '()))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defmacro forth-stdlib-add (&body all)
    `(setf *forth-stdlib*
           (nconc *forth-stdlib*
                  ',all)))

  (defmacro new-forth-interpreter ()
    `(anaphoric-macros:alet% ,*forth-registers*
                             (setf dtable (make-hash-table))
                             (forth-install-primitives)
                             (dolist (v *forth-stdlib*)
                               (funcall anaphoric-macros::this v))
                             (pandoric-macros:plambda (v) ,*forth-registers*
                               (let ((word (forth-lookup v dict)))
                                 (if word
                                     (forth-handle-found)
                                     (forth-handle-not-found))))))

  (defmacro forth-install-primitives ()
    `(progn
       ,@(mapcar #`(let ((thread (lambda () ,@(cddr a1))))
                     (setf dict (make-forth-word
                                 :name ',(car a1)
                                 :prev dict
                                 :immediate ,(cadr a1)
                                 :thread thread)
                           (gethash thread dtable) ',(cddr a1)))
                 *forth-primitive-forms*))))

#|
Immediate mode is a mode in forth programming systems that deals with
determining if a set of forth code is compiled or directly executed
using a flag that if non-zero tells forth to
|#
;; these two primitives defines out to get in/out immediate mode
(define-forth-primitive  [ t          ; <- t means immediate
  (setf compiling nil))
(define-forth-primitive ] nil         ; <- not immediate
  (setf compiling t))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defmacro forth-compile-in (v)
    `(setf (forth-word-thread dict)
           (nconc (forth-word-thread dict)
                  (list ,v))))

  (defmacro forth-handle-found ()
    `(forth-inner-interpreter))

  (defmacro forth-handle-not-found ()))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter *new-forth* (new-forth-interpreter)))

;; example from Ch. 8 LoL
(go-forth *new-forth* 1 2.0 "three" 'four '(f i v e))
(go-forth *new-forth*
  3 dup * print)

(pandoric-macros:with-pandoric (pstack) *new-forth*
  pstack)

(named-readtables:in-readtable :standard)
