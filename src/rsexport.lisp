;;; Copyright (C) 2007, 2009, 2011-14, 2016 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html


(defpackage :reasoner
  (:nicknames :rs)
  (:use :rparallel :streams :atms #-closer-mop :cl #+closer-mop :c2cl)
#-(or closer-mop abcl clozure cmu mcl sbcl)
  (:use :clos)
#+(and (not closer-mop) abcl)
  (:use :mop)
#+(and (not closer-mop) (or clozure mcl))
  (:use :ccl)
#+(and (not closer-mop) cmu)
  (:use :clos-mop)
#+(and (not closer-mop) sbcl)
  (:use :sb-mop)
  (:shadow #:variable)
#+(or abcl clisp sbcl)
  (:shadow #:ensure-class #:ensure-class-using-class)
#+clisp
  (:shadow #:subtypep)
#+ecl
  (:shadow #:class-slots)
#+lispworks
  (:shadow #:find-slot-definition)
#+(and (not closer-mop) lispworks)
  (:shadow #:make-method-lambda #:slot-value-using-class))

(in-package reasoner)
(eval-when (:execute :compile-toplevel :load-toplevel)

(export '(make-assumption uniquify-environment
          in-p truep contradictoryp subsumesp
          assumption environment
          head tail
          schedule nschedule backtrack solutions
          order-control-disjunction added-assumption add-contradiction conflictp
          describe-data map-slots classify notice-slot-values
          assume-slot-value assume-slot-values reinitialize-atms
          *atms* *empty-environment* contradictory-value contradictory-value-p
          extended-class extended-object
          instance-name instance-assumption find-instance
          slot-value-typep add-slot-value slot-value-reduce slot-values
          add-slot-value-using-class slot-definition-missing
          validate-combination fetch-node fetch-assumption
          elements remove-slot-value remove-node
          numeric-range symbolic-range big -big true-or-false true false
          zero-or-one zero-or-more exactly-one one-or-more defrange
          numeric-rangep range-max range-min
          ensure-named-instance ensure-named-instance-using-class
          source-form rule-compile uncompile
          defconstraint defrule -> <-> lisp is in includes
          aggregate-min aggregate-max aggregate-sum
          *trace-rule-failure* *rule-trace-output*
          rules-using rules-affecting slot-affected slots-used
          attribute-reference-class attribute-name
          compound-object assembly part component parts
          ))
)

;;; Hide some CLOS implementation idiosyncrasies.

#+(and (not closer-mop) abcl)
(defconstant ensure-class-using-class-fn #'mop:ensure-class-using-class)
#+(and (not closer-mop) clisp)
(defconstant ensure-class-using-class-fn #'clos:ensure-class-using-class)
#+(and (not closer-mop) sbcl)
(defconstant ensure-class-using-class-fn #'sb-mop:ensure-class-using-class)
#+(and closer-mop (or abcl clisp sbcl))
(defconstant ensure-class-using-class-fn #'c2cl:ensure-class-using-class)

#+(or abcl clisp)
(defun ensure-class-using-class (class
                                 name
                                 &rest initargs
                                 &key direct-superclasses
                                 &allow-other-keys)
  (if (and class (null direct-superclasses))
      (apply ensure-class-using-class-fn
             class
             name
             :direct-superclasses (class-direct-superclasses class)
                                               ; Leave value unchanged.
             initargs)
    (apply ensure-class-using-class-fn class name initargs)))

#+sbcl
(defun ensure-class-using-class (class
                                 name
                                 &rest initargs
                                 &key direct-superclasses
                                 &allow-other-keys)
  (if class
      (apply ensure-class-using-class-fn class name initargs)
    (apply ensure-class-using-class-fn
           class
           name
           :direct-superclasses direct-superclasses
                                               ; Supply explicitly to inhibit
                                               ; over-eager defaulting.
           initargs)))

#+(or abcl clisp sbcl)
(defun ensure-class (name &rest initargs)
  (apply #'ensure-class-using-class (find-class name nil)
                                    name
                                    initargs))

#+clisp
(defun subtypep (type-1 type-2 &optional environment)
  (let (subtype-p valid-p normal)
    (ignore-errors
     (multiple-value-setq (subtype-p valid-p)
       (cl:subtypep type-1 type-2 environment))
                                               ; Signals an error if a symbol
                                               ; associated with a class using
                                               ; setf and find-class is received.
     (setq normal (not nil)))
    (if normal
        (values subtype-p valid-p)
      (cl:subtypep (or (if (symbolp type-1) (find-class type-1 nil)) type-1)
                   (or (if (symbolp type-2) (find-class type-2 nil)) type-2)
                   environment))))

#+ecl
(defmethod class-slots ((class t))
  (clos:class-slots class))

#+(and (not closer-mop) lispworks)
(defmacro slot-value-using-class (class object slot)
  `(clos:slot-value-using-class ,class ,object (slot-definition-name ,slot)))