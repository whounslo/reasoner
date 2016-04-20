;;; Copyright (C) 2012 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; Automatically-generated rules

(in-package reasoner)

(defclass class-slot-dependency ()
  ((name :initarg :name :reader name)
   (option :initarg :option :reader option)
   (value :initarg :value :accessor value)
   (dependee :initarg :dependee :reader dependee)
   (dependent :initform nil :accessor dependent)
   (finalized :initform nil :accessor finalized)))

(defun find-slot-type (class slot-name)
  (let ((slot-definition (find-slot-definition class slot-name)))
    (if slot-definition
        (slot-definition-type slot-definition)
      (error "Slot ~A is missing from class ~A." slot-name class))))

(defmethod generate-inverse-wff ((class extended-class) slot-name-1 slot-name-2)
  (let* ((slot-type (find-slot-type class slot-name-1))
         (variable-1 (make-variable :class-name (class-name class)
                                    :name (gensym)))
         (variable-2 (make-variable :class-name slot-type
                                    :name (gensym)))
         (attribute-reference-1 (make-attribute-reference
                                 :attribute-reference-variable variable-1
                                 :attribute-name slot-name-1))
         (attribute-reference-2 (make-attribute-reference
                                 :attribute-reference-variable variable-2
                                 :attribute-name slot-name-2)))
    (find-slot-type (find-class slot-type) slot-name-2)
                                               ; Check that slot exists.
    `(and
      (or
       ,(make-instance 'relational-proposition
                       'specializer variable-2
                       'attribute-references (list attribute-reference-1))
       (not ,(make-instance 'relational-proposition
                            'specializer variable-1
                            'attribute-references (list attribute-reference-2))))
      (or
       ,(make-instance 'relational-proposition
                       'specializer variable-1
                       'attribute-references (list attribute-reference-2))
       (not ,(make-instance 'relational-proposition
                            'specializer variable-2
                            'attribute-references (list attribute-reference-1)))))))

(defmethod generate-wff ((class extended-class) slot-name (composition cons)
                         &aux variable)
  (flet ((make-body (expression-1 expression-2)
           (if expression-2
               (list 'and expression-2 expression-1)
             expression-1)))
    (setq variable (make-variable :class-name (class-name class)
                                  :name (gensym)))
    (do ((slot-names composition (rest slot-names))
         (next-class class (find-class slot-type))
         (next-variable variable specializer)
         slot-type
         specializer
         (attribute-reference-1 (make-attribute-reference
                                 :attribute-reference-variable variable
                                 :attribute-name slot-name))
         (tail nil
               (make-body (make-instance 'relational-proposition
                                         'specializer specializer
                                         'attribute-references
                                         (list
                                          (make-attribute-reference
                                           :attribute-reference-variable next-variable
                                           :attribute-name (first slot-names))))
                          tail)))
        ((endp slot-names) (values tail
                                   (make-instance 'relational-proposition
                                     'specializer specializer
                                     'attribute-references
                                     (list attribute-reference-1))))
      (setq slot-type (find-slot-type next-class (first slot-names)))
                                               ; Check that slot exists, whether
                                               ; or not we need its type.
      (when (singletonp slot-names)
        (setq slot-type (find-slot-type class slot-name))
                                               ; Use type of destination slot
                                               ; in specializer.
        )
      (when (subtypep slot-type 'range)
        (return
          (values tail
                  (let ((attribute-reference-2
                         (make-attribute-reference
                          :attribute-reference-variable next-variable
                          :attribute-name (first slot-names))))
                    (if (subtypep slot-type 'numeric-range)
                        (make-instance 'arithmetic-proposition
                                       'attribute-references
                                       (list attribute-reference-1)
                                       'relation '=
                                       'prefix-rhs attribute-reference-2)
                      (make-instance 'literal-proposition
                                     'attribute-references
                                     (list attribute-reference-2
                                           attribute-reference-1)))))))
      (setq specializer (make-variable :class-name slot-type
                                       :name (gensym))))))

(defmethod generate-wff ((class extended-class) slot-name (composition
                                                           (eql :transitive)))
  (generate-wff class slot-name (list slot-name slot-name)))

(defmethod generate-wff ((class extended-class) slot-name (composition
                                                           (eql :symmetric)))
  (flet ((swap-variables (proposition)
           (declare (type relational-proposition proposition))
           (with-slots (attribute-references specializer)
               proposition
             (psetf specializer (attribute-reference-variable
                                 (first attribute-references))
               (first attribute-references)
               (make-attribute-reference :attribute-reference-variable specializer
                                         :attribute-name (attribute-name
                                                          (first
                                                           attribute-references)))))
           proposition))
        (multiple-value-bind (body head)
            (generate-wff class slot-name (list slot-name))
          (values body (swap-variables head)))))

(defmacro generated-wff-neck (composition)
  `(case ,composition
     (:symmetric biconditional-token)
     (t implication-token)))

(defmethod add-generated-wff (composition body head)
  (make-instance 'forward-rule
                 :body body
                 :neck (generated-wff-neck composition)
                 :head head))

(defmethod add-generated-wff (composition body (head null))
  (declare (ignore composition))
  (make-instance 'constraint :body body))

(defmethod slot-value-dependentp (class name option)
  (declare (ignore class name option))
  )

(defmethod slot-value-dependentp ((class extended-class) name option)
  (map-dependents class
                  #'(lambda (dependent)
                      (when (and (eq name (name dependent))
                                 (eq option (option dependent)))
                        (return-from slot-value-dependentp (not nil)))))
  nil)

(defmethod add-dependent-wff ((class extended-class)
                              &key name composition inverse &allow-other-keys)
  (flet ((record-dependent (&rest initargs)
           (let ((dependent (apply #'make-instance 'class-slot-dependency
                                                   :name name
                                                   :dependee class
                                                   initargs)))
             (add-dependent class dependent)
             dependent)))
    (when composition
      (unless (slot-value-dependentp class name :composition)
        (record-dependent :option :composition :value composition)))
    (when inverse
      (unless (slot-value-dependentp class name :inverse)
        (record-dependent :option :inverse :value inverse)))
    class))

(defmethod add-dependent-wffs ((class extended-class) direct-slots)
  (dolist (direct-slot direct-slots)
    (apply #'add-dependent-wff class direct-slot)))

(defmethod initialize-instance :after ((class extended-class)
                                       &key direct-slots
                                       &allow-other-keys)
  (add-dependent-wffs class direct-slots))

(defmacro generate-slot-option-wff (class slot-name option value)
  `(ecase ,option
     (:composition
      (generate-wff ,class ,slot-name ,value))
     (:inverse
      (generate-inverse-wff ,class ,slot-name ,value))))

(defun find-dependee (class slot-name)
  (find-class (find-slot-type class slot-name)))

(defmethod add-dependees (class dependency (composition symbol))
  (declare (ignore class dependency))
  )

(defmethod add-dependees (class dependency (composition cons))
  (do ((slot-names composition (rest slot-names))
       (next-class class))
      ((endp slot-names))
    (setq next-class (find-dependee next-class (first slot-names)))
    (unless (slot-value-dependentp next-class (name dependency) :composition)
      (add-dependent next-class dependency))))

(defmethod finalize-dependent :before ((dependent class-slot-dependency))
  (ecase (option dependent)
    (:composition
     (add-dependees (dependee dependent) dependent (value dependent)))
    (:inverse
      (let* ((name (name dependent))
             (dependee (find-dependee (dependee dependent) name)))
        (unless (slot-value-dependentp dependee name :inverse)
         (add-dependent dependee dependent))))))

(defmethod finalize-dependent ((dependent class-slot-dependency))
  (with-accessors ((class dependee)
                   (slot-name name)
                   (option-key option)
                   (option-value value)
                   (wff dependent)
                   (finalized finalized))
      dependent
    (when option-value
      (unless finalized
        (setf finalized (not nil))             ; Lock so won't be generated
                                               ; recursively via
                                               ; FINALIZE-INHERITANCE.
                                               ; If error, cleanup handled by
                                               ; UPDATE-DEPENDENT.
        (multiple-value-bind (body head)
            (generate-slot-option-wff class slot-name option-key option-value)
          (setf wff (add-generated-wff option-value body head)))))))

(defmethod reinitialize-instance :before ((class extended-class)
                                          &key direct-slots
                                          &allow-other-keys)
  (add-dependent-wffs class direct-slots))

(defmethod update-dependent ((class extended-class)
                             (dependency class-slot-dependency)
                             &key direct-slots
                             &allow-other-keys)
  (with-accessors ((slot-name name)
                   (option-key option)
                   (option-value value)
                   (dependee dependee)
                   (wff dependent)
                   (finalized finalized))
      dependency
    (flet ((update-wff ()
             (cond ((not finalized))
                   (wff
                    (multiple-value-bind (body head)
                        (generate-slot-option-wff dependee
                                                  slot-name
                                                  option-key
                                                  option-value)
                      (reinitialize-instance wff
                                             :body body
                                             :neck (generated-wff-neck
                                                    option-value)
                                             :head head)))
                   (t                          ; Error occurred.
                    (setf finalized nil)
                    (finalize-dependent dependency)))))
      (if (eq class dependee)
          (let ((direct-slot (find slot-name
                                   direct-slots
                                   :key #'(lambda (slot)
                                            (getf slot :name))))
                value)
            (cond ((and direct-slot
                        (setq value (getf direct-slot option-key)))
                   (unless (eq value option-value)
                     (setf option-value value)
                     (update-wff)))
                  (direct-slots
                   (setf option-value nil)
                   (when wff (uncompile wff)))))
        (update-wff)))))