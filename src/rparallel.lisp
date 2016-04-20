;;; Copyright (C) 2013, 2014 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; Interface to Lisp in Parallel (lparallel.org).

(defpackage :rparallel (:use :cl #+lparallel :bordeaux-threads #+lparallel :lparallel))

(in-package :rparallel)
(eval-when (:execute :compile-toplevel :load-toplevel)
  (export '(lockable-object hold-lock
            delay force initiate defer perform task
            do-deferred-results if-in-parallel)))

(defconstant worker-count 2)

#+lparallel
(defvar *pending-tasks* nil)

#+lparallel
(setf *kernel* (make-kernel worker-count))

(defclass lockable-object ()
#-lparallel
    ()
#+lparallel
  ((lock :initform (make-lock) :reader lock))
  )

(defmacro hold-lock (object &body body)
#-lparallel
  `(progn ,@body)
#+lparallel
  `(with-lock-held ((lock ,object))
     ,@body))

#-lparallel
(defmacro delay (exp)
  "Packages expression as a memoized procedure for evaluation later on demand."
  `(let (already-run result)
    #'(lambda ()
        (if already-run
            result
          (setq already-run (not nil)
              result ,exp)))))

#-lparallel
(defgeneric force (object)
  (:method ((delayed-object function))
    "Evaluate delayed-object produced by DELAY."
    (funcall delayed-object))
  (:method ((tail list))
    "List: simply return tail."
    tail))

#-lparallel
(progn
(defmacro initiate (form) form)
(defmacro defer (form) form)
)

#+lparallel
(defmacro initiate (form)
  `(future ,form))

#+lparallel
(defmacro defer (form)
  `(chain (delay ,form)))

(defmacro perform (&body body)
#-lparallel
  `(macrolet ((task (form) form))
     ,@body)
#+lparallel
  (let ((results-var (gensym)))
    `(macrolet ((task (form)
                  (list 'push form ',results-var)))
       (push (future (let (,results-var)
                       ,@body
                       (nreverse ,results-var)))
             *pending-tasks*)
                                               ; Start dispatcher.
       )))

(defmacro do-deferred-results (result-var &body body)
#+lparallel
  (let ((tasks-var (gensym))
        (task-var-1 (gensym))                  ; Dispatchers.
        (task-var-2 (gensym)))                 ; Class consumers.
    `(do ((,tasks-var *pending-tasks* *pending-tasks*))
         ((endp ,tasks-var))
       (setq *pending-tasks* ())
       (dolist (,task-var-1 (nreverse ,tasks-var))
         (do ((,task-var-2 (force ,task-var-1) (rest ,task-var-2))
              ,result-var)
             ((endp ,task-var-2))
           (setq ,result-var (force (first ,task-var-2)))
           ,@body)))))

(defmacro if-in-parallel (form)
#+lparallel
  form)