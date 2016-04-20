;;; Copyright (C) 2007-2009, 2014 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; Implements:
;;;   :count slot option
;;;   :type slot property inheritance (overriding of standard behaviour)
;;;   extra instance storage
;;; assuming only the existence of:
;;;   class-slots
;;;   slot-definition-name
;;; (or equivalents).

(in-package reasoner)

#-mop
(progn

(defvar *count-slot-options* nil)

(defvar *type-slot-options* nil)

(defvar *finalized-classes* nil)

(defmacro defclass* (name direct-superclasses direct-slots &rest options)
  (let (count-slot-options type-slot-options form)
    (dolist (spec direct-slots)
      (when (find :count spec :test #'eq)
        (setf (getf count-slot-options (car spec)) (getf (cdr spec) :count)))
      (when (find :type spec :test #'eq)
        (setf (getf type-slot-options (car spec)) (getf (cdr spec) :type))))
    (setq form `(defclass ,name
                    ,direct-superclasses
                  ,(mapcar #'(lambda (spec &aux count-slot-name)
                               (setq count-slot-name (getf count-slot-options (car spec)))
                               (if count-slot-name
                                   (remove-if #'(lambda (element)
                                                  (or (eq element :count)
                                                      (eq element count-slot-name)))
                                              spec)
                                 spec))
                     direct-slots)
                  ,@options))
    `(progn
       (push ',(cons name count-slot-options) *count-slot-options*)
       (push ',(cons name type-slot-options) *type-slot-options*)
       ,(macroexpand-1 form))))

(defmethod shared-initialize :after ((class extended-class) slot-names &rest initargs)
  (declare (ignore slot-names initargs))
  
  ;; Redo finalization of a redefined class and its subclasses.
  (setq *finalized-classes* (delete class *finalized-classes*
                                    :test #'(lambda (x y) (subtypep y x)))))
  
(defun find-option (class slot-name options &aux class-options slot-option)
  (dolist (superclass (class-precedence-list class))
    (setq class-options (assoc (class-name superclass)
                               options
                               :test #'eq)
        slot-option (getf (cdr class-options) slot-name))
    (when slot-option
      (return slot-option))))

(defun slot-definition-name (slot-definition)
  (clos::slot-definition-name slot-definition))
  
(defun slot-definition-initargs (slot-definition)
  (clos::slot-definition-initargs slot-definition))

(defmethod class-slots ((class t))
  (clos::class-slots class))

(defmethod class-slots ((class extended-class))
  (let ((slots (call-next-method)))
    (unless (find class *finalized-classes* :test #'eq)
      (dolist (slot slots)
        (finalize-slot-definition class slot))
      (push class *finalized-classes*))
    slots))

(let ((instance-name-table (make-hash-table :test #'eq))
      (instance-node-table (make-hash-table :test #'eq))
      (slot-definition-count (make-hash-table :test #'eq))
      (slot-definition-type (make-hash-table :test #'eq)))
  
  (defun instance-name (instance)
    (gethash instance instance-name-table))
  
  (defmethod (setf extd-instance-name) (new-name (instance extended-object))
    (setf (gethash instance instance-name-table) new-name))
  
  (defun instance-node (instance)
    (gethash instance instance-node-table))
  
  (defun (setf instance-node) (node instance)
    (setf (gethash instance instance-node-table) node))
  
  (defmethod finalize-slot-definition ((class extended-class) slot-definition)
    (let ((slot-name (slot-definition-name slot-definition))
          count-slot-name slot-type)
      (setq count-slot-name (find-option class slot-name *count-slot-options*))
      (when count-slot-name
        (setf (gethash slot-definition slot-definition-count) count-slot-name))
      (setq slot-type (find-option class slot-name *type-slot-options*))
      (when slot-type
        (setf (gethash slot-definition slot-definition-type) slot-type))
      slot-definition))
  
  (defun slot-definition-count (slot-definition)
    (gethash slot-definition slot-definition-count))
  
  (defun slot-definition-type (slot-definition)
    (gethash slot-definition slot-definition-type t))

  ) ;end let
) ;end progn