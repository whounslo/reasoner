;;; Copyright (C) 2007, 2009, 2011, 2013 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html


(in-package reasoner)

(defmacro defconstraint (&rest args)
  (let (name qualifier documentation source-form
        (class-name 'constraint))
    (multiple-value-setq (name qualifier documentation source-form)
                   (parse-defrule args))
    `(ensure-named-instance ',name
                            :qualifier ,qualifier
                            :documentation ,documentation
                            :source-form ',source-form
                            :class (find-class ',class-name))))

(defmacro defrule (&rest args)
  (let (name qualifier documentation source-form
        (class-name 'forward-rule))
    (multiple-value-setq (name qualifier documentation source-form)
                   (parse-defrule args))
    `(ensure-named-instance ',name
                            :qualifier ,qualifier
                            :documentation ,documentation
                            :source-form ',source-form
                            :class (find-class ',class-name))))

(defmethod parse-defrule (args)
  (let ((name (car args))
        qualifier
        declarations
        (documentation nil)
        body)
    (setq qualifier (if (and (atom (cadr args))
                             (not (null (cadr args))))
                        (cadr args))
        declarations (if qualifier (caddr args) (cadr args))
        body (if qualifier (cdddr args) (cddr args)))
    (when (stringp (car body))
      (setq documentation (pop body)))
    (values name qualifier documentation (cons declarations body))))

(defun ensure-named-instance (name &rest initargs)
  (apply #'ensure-named-instance-using-class (find-instance name nil)
                                             name
                                             :name name
                                             initargs))

(defmethod ensure-named-instance-using-class ((instance extended-object)
                                              name
                                              &rest initargs
                                              &key class
                                              &allow-other-keys)
  "Updates a named instance."
  (if (eq (class-of instance) (if (symbolp class) (find-class class) class))
      (apply #'reinitialize-instance instance initargs)
    (error "~S already exists as an instance,~@
            but is not of class ~S."
            name (if (symbolp class) class (class-name class)))))

(defmethod ensure-named-instance-using-class ((instance null)
                                              name
                                              &rest initargs
                                              &key class qualifier
                                              &allow-other-keys)
  "Creates a named instance."
  (declare (ignore name))
  (apply #'make-instance class
                         :antecedents (if (eq qualifier :assume)
                                          (list
                                           (make-assumption *atms*)))
                         initargs))

(defmethod uncompile ((wff well-formed-formula))
  (dolist (node (all-slot-values wff 'class-consumers))
    (dolist (class-consumer (datum-value node))
      (dolist (proposition (propositions class-consumer))
        (remove-indexes proposition class-consumer)))
    (when (truep node)
      (remove-node node nil)))
  wff)

(defmethod shared-initialize ((instance well-formed-formula)
                              slot-names
                              &key source-form
                              &allow-other-keys)
  (declare (ignore slot-names))
  (let ((re-compile nil))
    (when source-form
      (unless (and (fetch-node instance 'source-form source-form)
                   (all-slot-values instance 'class-consumers))
        (uncompile instance)
        (setq re-compile (not nil))))
    (call-next-method)
    (when re-compile
      (rule-compile instance))
    instance))

(defmethod shared-initialize :after ((instance constraint)
                                     slot-names
                                     &key body
                                     &allow-other-keys)
  (declare (ignore slot-names))
  (when body
    (uncompile instance)
    (add-class-consumers instance (make-constraint-consumers body nil) ())))

(defmethod shared-initialize :after ((instance forward-rule)
                                     slot-names
                                     &key head neck body
                                     &allow-other-keys)
  (declare (ignore slot-names))
  (when head
    (uncompile instance)
    (add-class-consumers instance
                         (make-all-class-consumers body
                                                   neck
                                                   (collect-head-propositions
                                                    head)
                                                   nil)
                         ())))