;;; Copyright (C) 2007-2014 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html


(in-package reasoner)

(defmacro encapsulate-variables (name &rest definitions)
  (let ((function-name (intern (concatenate 'string (string :reinitialize)
                                                    (string #\-)
                                                    (string name)))))
    `(progn
       ,@definitions
       (defun ,function-name ()
         ,@(mapcar #'(lambda (definition)
                       (destructuring-bind (name variable-name initial-value . tail)
                           definition
                         (declare (ignore name tail))
                         `(setq ,variable-name ,initial-value)))
             definitions)
         (not nil)))))

(defmacro revdolist ((var list-form) &rest body)
  "Reverse DOLIST; non-consing."
  (let ((form (gensym)))
    `(labels ((internal-revdolist (,form)
                (if ,form
                    (let ((,var (car ,form)))
                      (internal-revdolist (cdr ,form))
                      ,@body))))
       (internal-revdolist ,list-form)
       nil)))

;;; ATMS initialization

(encapsulate-variables atms
(defparameter *atms* (make-instance 'atms))

(defparameter *empty-environment* (uniquify-environment *atms* nil)
  "The distinguished environment of no assumptions.")

(defparameter *falsity* (make-instance 'false-node))
) ;end encapsulate-variables

;;; extended-class

(defclass extended-class (standard-class)
    ((rule-index :initform nil :documentation "Proposition - attribute-reference combinations, indexed by attribute-name, that represent classes of nodes to which class-consumers apply."
            )
     (rule-head-index :initform nil :documentation "Proposition - attribute-reference combinations, indexed by attribute-name, that represent classes of nodes produced by class-consumers."
            )
#-(or allegro lispworks sbcl)
     (dependents-finalized :accessor dependents-finalized)))

(eval-when (:execute #+lispworks :compile-toplevel :load-toplevel)
(defmethod validate-superclass ((class extended-class)
                                (superclass standard-class))
  "Declare compatibility of EXTENDED-CLASS and standard-class."
  (not nil))
)

(defmethod initialize-instance :around ((class extended-class)
                                        &rest initargs
                                        &key direct-superclasses
                                        &allow-other-keys)
  (apply #'call-next-method
         class
         (if direct-superclasses
             initargs
           (list* :direct-superclasses
                  (list (find-class 'extended-object))
                  initargs))))

(defmethod reinitialize-instance :around ((class extended-class)
                                          &rest initargs
                                          &key (direct-superclasses nil supp)
                                          &allow-other-keys)
  (apply #'call-next-method
         class
         (if (or direct-superclasses
                 (not supp))
             initargs
           (list* :direct-superclasses
                  (list (find-class 'extended-object))
                  initargs))))

(defmethod finalize-dependent ((dependent t))
  )

(defmethod finalize-dependents ((class t))
  )

(defmethod finalize-dependents ((class extended-class))
  (map-dependents class #'finalize-dependent))

(defmethod finalize-inheritance :after ((class extended-class))
#-(or allegro lispworks sbcl)
  (setf (dependents-finalized class) nil)
#+(or allegro lispworks sbcl)
  (mapc #'finalize-dependents (class-precedence-list class)))

#-(or allegro lispworks sbcl)
(defmethod allocate-instance :after ((class extended-class) &rest initargs)
  (declare (ignore initargs))
  (unless (dependents-finalized class)
    (mapc #'finalize-dependents (class-precedence-list class))
    (setf (dependents-finalized class) (not nil))))

(defmacro class-dependents-finalized-p (class)
#-(or allegro lispworks sbcl)
  `(and (class-finalized-p ,class) (dependents-finalized ,class))
#+(or allegro lispworks sbcl)
  `(class-finalized-p ,class))

;;; Slot definitions

(defclass extended-slot-definition-mixin ()
    ((count :initform nil :initarg :count
        :accessor slot-definition-count
        :documentation "Names a slot that records the number of values that this slot holds."
            )
     (composition :initform nil :initarg :composition
        :accessor slot-definition-composition
        :documentation "A list of slots that can be used to derive this slot's value(s)."
            )
     (inverse :initform nil :initarg :inverse
        :accessor slot-definition-inverse
        :documentation "Names a slot that is the inverse of this slot."
            )))

(defclass extended-direct-slot-definition
          (extended-slot-definition-mixin
           standard-direct-slot-definition)
    ())

(defclass extended-effective-slot-definition
          (extended-slot-definition-mixin
           standard-effective-slot-definition)
    ())

(defmethod direct-slot-definition-class ((class extended-class)
                                         &rest initargs)
  (declare (ignore initargs))
  (find-class 'extended-direct-slot-definition))

(defmethod effective-slot-definition-class ((class extended-class)
                                            &rest initargs)
  (declare (ignore initargs))
  (find-class 'extended-effective-slot-definition))

;;; Reader methods

(defclass extended-reader-method (standard-reader-method)
    ())

(defmethod reader-method-class ((class extended-class)
                                (direct-slot extended-direct-slot-definition)
                                &rest initargs)
  (declare (ignore initargs))
  (find-class 'extended-reader-method))

(defmethod initialize-instance :before ((direct-slot extended-direct-slot-definition)
                                        &key readers
                                             writers
                                        &allow-other-keys
                                        &aux (metaclass 'extended-class))
  (unless (or (null readers) (singletonp readers))
    (error "Multiple reader methods are not permitted with metaclass ~A." metaclass))
  (when writers
    (error "Writer methods are incompatible with metaclass ~A." metaclass)))

(defmethod initialize-instance ((method extended-reader-method)
                                &key qualifiers
                                     lambda-list
                                     specializers
                                     function
                                     slot-definition
                                &allow-other-keys
                                &aux (slot-name (slot-definition-name slot-definition))
                                     (new-lambda-list '(object &optional environment)))
  (declare (ignore lambda-list function))
  (multiple-value-bind (lambda initargs)
      (make-method-lambda (ensure-generic-function (car (slot-definition-readers
                                                         slot-definition))
                                                   :generic-function-class
                                                   'standard-generic-function
                                               ; May not be cl:standard-generic-function.
                                                   :lambda-list new-lambda-list)
                          method
                          `(lambda ,new-lambda-list
                             (slot-value-reduce object ',slot-name environment))
                          nil)
    (apply #'call-next-method
           method
           :qualifiers qualifiers
           :lambda-list new-lambda-list
           :specializers specializers
           :function (compile nil lambda)
                                               ; Drop already-produced
                                               ; method lambda on the floor.
           :slot-definition slot-definition
           initargs)))

;;; :count and :type slot property inheritance.
;;; In the latter case the standard behaviour is overridden.

(defmethod compute-effective-slot-definition ((class extended-class)
                                              name
                                              direct-slot-definitions)
  (declare (ignorable name))
#+(or allegro lispworks sbcl)
  (do ((type-1 (slot-definition-type (car direct-slot-definitions)) type-2)
       type-2
       (direct-slots direct-slot-definitions (cdr direct-slots)))
      ((endp (cdr direct-slots)))
    (setq type-2 (slot-definition-type (cadr direct-slots)))
    (unless (eq type-1 t)
      (multiple-value-bind (is-subtype valid)
          (subtypep type-1 type-2)
        (unless (or is-subtype (not valid))
          (error "While computing the effective slot definition of ~
                     slot ~A, class ~A, ~
                     found definition(s) in superclass(es) ~
                     with incompatible type specifier(s)."
            name
            class)))))
  (let ((effective-slot (call-next-method))
        (count-slot (find-if-not #'null direct-slot-definitions
                                 :key #'slot-definition-count))
        (type-slot (find t direct-slot-definitions
                         :key #'slot-definition-type
                         :test-not #'eq)))
    (when count-slot
      (setf (slot-definition-count effective-slot)
            (slot-definition-count count-slot)))
    (when type-slot
#-allegro
      (setf (slot-definition-type effective-slot)
        (slot-definition-type type-slot))
#+allegro
      (setf (slot-value effective-slot 'type)
        (slot-definition-type type-slot)))
    effective-slot))

;;; Extra instance storage

(defmethod compute-slots ((class extended-class))
  (list* (make-instance 'standard-effective-slot-definition
                        :name 'extd-instance-name)
         (make-instance 'standard-effective-slot-definition
                        :name 'extd-instance-node)
         (call-next-method)))

;;; find-slot-definition

(defmethod slot-definition-count ((slot standard-effective-slot-definition))
  nil)

(defun find-slot-definition (class item
                             &key (direct nil) (test #'eq) (key #'slot-definition-name))
  "Return the named slot definition if there is one, or NIL otherwise."
  (unless (or direct (class-finalized-p class)) (finalize-inheritance class))
  (find item (if direct (class-direct-slots class) (class-slots class))
        :key key :test test))

(defmacro slot-name-p (class slot-name)
  "Determines if there is a slot definition so named in class."
  `(find-slot-definition ,class ,slot-name))

(defun map-slots (class function &key (direct nil) (from-end nil))
  "Applies function to an ordered list of slot definitions for class, with duplicates removed."
  (if direct
      (map nil function (class-direct-slots class))
    (let ((classes (class-precedence-list class)))
      (flet ((shadowedp (class slot-definition-name from-end)
               (find-if #'(lambda (element)
                            (if (eq element class)
                                (return-from shadowedp nil)
                              (find slot-definition-name
                                    (class-direct-slots element)
                                    :test #'eq
                                    :key #'slot-definition-name)))
                        classes
                        :from-end from-end)))
        (revdolist (class classes)
          (dolist (slot-definition (class-direct-slots class))
            (unless (shadowedp class (slot-definition-name slot-definition) from-end)
              (funcall function slot-definition))))))))

;;; find-instance

(defvar *instance-table* (make-hash-table :test #'eq))

(defun find-instance (name &optional (errorp t))
  (cond ((gethash name *instance-table*))
        ((not errorp) nil)
        ((legal-instance-name-p name)
         (error "No instance named: ~S." name))
        (t (error "~S is not a legal name for an instance." name))))

(defun (setf find-instance) (new-value name)
  (if (legal-instance-name-p name)
      (setf (gethash name *instance-table*) new-value)
      (error "~S is not a legal name for an instance." name)))

(defun legal-instance-name-p (x)
  (and (symbolp x)
       (not (keywordp x))))

(defun instance-name (instance)
  (slot-value instance 'extd-instance-name))

(defun (setf instance-name) (new-name instance)
  (reinitialize-instance instance :name new-name))

(defmacro instance-node (instance)
  `(slot-value ,instance 'extd-instance-node))

(defun instance-assumption (instance)
  (datum-assumption (instance-node instance)))

(defmacro all-slot-values-using-class (class object slot)
  `(slot-value-using-class ,class ,object ,slot))

(defmacro all-slot-values (object slot-name)
  "Returns a list of all slot values, or NIL if slot is unbound."
  `(slot-value ,object ,slot-name))

(defmethod slot-unbound ((class extended-class) instance slot-name)
  (declare (ignore instance slot-name))
  nil)

;;; Instance creation and initialization

(defclass extended-object (standard-object)
  ()
  (:metaclass extended-class)
  (:documentation "Instance of the class EXTENDED-CLASS; superclass of all instances of EXTENDED-CLASS except itself."))

(defmethod print-object ((instance extended-object) stream)
  (print-unreadable-object (instance stream :identity t)
    (format stream "~:(~S~)~@[ ~S~]"
            (class-name (class-of instance))
            (instance-name instance)))
  instance)

(defmethod (setf extd-instance-name) (new-name (instance extended-object))
  (setf (slot-value instance 'extd-instance-name) new-name))

(defmethod shared-initialize :before ((instance extended-object)
                                      slot-names
                                      &key (antecedents nil) (name nil)
                                      &allow-other-keys)
  (declare (ignore slot-names))
  (let (instance-node)
    (setq instance-node (instance-node instance))
    (when (or antecedents (not instance-node))
      (add-justification *atms*
                         (or instance-node
                             (setf (instance-node instance)
                               (make-instance 'standard-node
                                              :datum instance)))
                         antecedents
                         :instance-creation)))
  
  (unless (and (instance-name instance)
               (not name))
    (setf (extd-instance-name instance) name))
  (when name
    (setf (find-instance name) instance))
  instance)

(defmethod shared-initialize ((instance extended-object)
                              slot-names &rest initargs
                              &aux (class (class-of instance)))
  (dolist (slot (class-slots class))
    (with-accessors ((slot-initargs slot-definition-initargs)
                     (slot-name slot-definition-name)
                     (slot-type slot-definition-type))
                    slot
      (multiple-value-bind (init-key init-value foundp)
            (get-properties initargs slot-initargs)
        (declare (ignore init-key))
        (cond (foundp
               (let ((nodes (all-slot-values-using-class class instance slot)))
                 (unless (find-node init-value nodes nil)
                   (dolist (node nodes)
                     (remove-node node nil))
                   (when init-value
                     (add-slot-value-using-class class
                                                 instance
                                                 slot
                                                 init-value
                                                 nil
                                                 :initial-value)))))
              ((and (or (eq slot-names t)
                        (member slot-name slot-names :test #'eq))
                    (not (slot-boundp instance slot-name))
                    slot-type
                    (subtypep slot-type 'range))
               (let ((range #+(and mop (not allegro))
                            (make-instance slot-type
                                           :object instance
                                           :slot-name slot-name)
                            #-(and mop (not allegro))
                            (make-instance slot-type
                                           :object instance
                                           :slot-name slot-name
                                           :value (range-elements slot-type))))
                 (add-node-using-class class
                                       instance
                                       slot
                                       range
                                       nil
                                       :initial-value)))))))
  instance)

;;; Slot-value combination

(defmethod combine1 ((values cons)
                     (value extended-object))
  (combine2 values value))

;;; add-slot-value

(defmethod justify-slot-value (object node antecedents informant)
  (add-justification *atms*
                     node
                     (cons (instance-node object)
                           (if (listp antecedents)
                               antecedents
                             (list antecedents)))
                     informant))

(defmethod justify-slot-value (object node (j justification) informant)
  (reinitialize-instance j
                         :informant informant
                         :consequent node
                         :antecedents (cons (instance-node object)
                                            (antecedents j)))
  (add-justification *atms* node j))

(defun subsets (set &optional (count-max 'big))
  (flet ((combinations (set count-max)
           (do ((elements set (cdr elements))
                (sets nil (nconc sets
                                 (cons (list (car elements))
                                       (mapcan #'(lambda (set)
                                                   (if (unbounded< (length set) count-max)
                                                       (list (cons (car elements) set))))
                                               sets)))))
               ((endp elements) sets))))
    (cons nil (combinations set count-max))))

(defun slot-definition-count-max (count-slot-definition)
  (with-accessors ((type slot-definition-type))
      count-slot-definition
    (if (subtypep type 'range)
        (range-max (range-elements type)))))

(defun find-slot-definition-named (class slot-name)
  "Return, assuming class to be finalized, the named slot definition or NIL."
  (declare (optimize (speed 3) (safety 1) (space 0) (debug 0)))
  (dolist (slot (class-slots class) nil)
    (when (eq (slot-definition-name slot) slot-name) (return slot))))

(defun add-slot-value (object slot-name new-value antecedents informant &rest args)
  (let* ((class (class-of object))
         (slot-definition (find-slot-definition-named class slot-name)))
    (apply #'add-slot-value-using-class class
                                        object
                                        slot-definition
                                        new-value
                                        antecedents
                                        informant
                                        :slot-name slot-name
                                        args)))

(defmethod slot-definition-missing
           (class object slot-name operation value antecedents informant
           &key &allow-other-keys)
  (declare (ignore class operation value antecedents informant))
  
  ;; Invoke SLOT-MISSING.
  (slot-boundp object slot-name))

(defmethod add-slot-value-using-class
           (class object (slot null) new-value antecedents informant
            &rest args &key slot-name)
  (apply #'slot-definition-missing class
                                   object
                                   slot-name
                                   'add-slot-value
                                   new-value
                                   antecedents
                                   informant
                                   args))

(defmethod add-slot-value-using-class
           (class object slot (new-value cons) antecedents informant
            &rest args)
  (if (every #'(lambda (object) (typep object 'extended-object)) new-value)
      (dolist (value new-value)
        (apply #'call-next-method class
                                  object
                                  slot
                                  value
                                  antecedents
                                  informant
                                  args))
    (call-next-method)))

(defmethod
    add-slot-value-using-class (class object slot new-value antecedents informant
                                &key (slot-name (slot-definition-name slot))
                                     no-check no-count negated)
  (let ((slot-type (slot-definition-type slot))
        (nodes (all-slot-values-using-class class object slot))
        node)
    (setq node (find-node new-value nodes negated))
    (cond ((null node)
           (setq node (make-instance (cond ((and slot-type
                                                 (subtypep slot-type 'range))
                                            slot-type)
                                           (negated 'excluded-slot-value)
                                           (t 'standard-slot-value))
                                     :object object
                                     :slot-name slot-name
                                     :value new-value))
           (add-node-using-class class
                                 object
                                 slot
                                 node
                                 antecedents
                                 informant
                                 nodes
                                 no-check
                                 no-count
                                 negated))
          (antecedents
           (justify-slot-value object node antecedents informant)))
    node))

(defun add-node-using-class (class object slot node antecedents informant
                             &optional (nodes nil)
                                       (no-check (not nil))
                                       (no-count (not nil))
                                       (negated nil))
  (let (value count-slot-name count-slot count-max)
    (justify-slot-value object node antecedents informant)
    (setf (all-slot-values-using-class class object slot) (cons node nodes))

    ;; Now check for contradictions.
    (unless no-check
      (dolist (n nodes)
        (cond ((not (validate-combination node n nodes)))
              ((null (setq value (combine node n)))
               (let ((antecedents (list node n)))
                 (if (every #'truep antecedents)
                     (error
                "Assertion would cause contradiction of the empty environment."
                                    )
                   (add-contradiction antecedents))))
              ((not (typep node 'range)))

              ;; For values that are ranges, provided one is not a
              ;; subset of the other, assert the value that is
              ;; their intersection.
              ((not (or (slot-value-equal value node)
                        (slot-value-equal value n)))
                                             ; We cannot rely on value
                                             ; combination, when given one
                                             ; value that is a subset of the
                                             ; other, yielding a result that
                                             ; is eq to that value.
               (add-slot-value-using-class class
                                           object
                                           slot
                                           value
                                           (list node n)
                                           :intersection
                                           :no-check t)))))
      
    (when (and (not no-count)
               (not negated)
               (not (typep node 'range))
               (setq count-slot-name (slot-definition-count slot))
               (setq count-slot (find-slot-definition-named class count-slot-name))
               (setq count-max (slot-definition-count-max count-slot)))

      ;; Slot has an associated slot holding its count; update this.
      (dolist (node-subset (subsets nodes count-max))
        (add-consumer *atms*
                      (cons node node-subset)
                      #'(lambda (justification)
                          (add-slot-value object
                                          count-slot-name
                                          (make-numeric-range :min (length
                                                                    (antecedents
                                                                     justification))
                                                              :max 'big)
                                          justification
                                          :count))))))
  node)

(defun find-node (value nodes negated)
  (dolist (node nodes)
    (when (slot-value-equal value node negated)
      (return node))))

(defmethod fetch-node ((object extended-object)
                       slot-name value &optional negated)
  (find-node value (all-slot-values object slot-name) negated))

(defmethod fetch-assumption ((object extended-object)
                             slot-name value &optional negated)
  (let ((node (fetch-node object slot-name value negated)))
    (if node (datum-assumption node))))

(defmethod validate-combination
           ((new-node standard-slot-value) (node standard-slot-value) nodes)
  (declare (ignore nodes))
  (not nil))

(defun add-contradiction (antecedents)
  (add-consumer *atms*
                antecedents
                #'(lambda (justification)
                    (reinitialize-instance justification
                                           :informant 'contradiction
                                           :consequent *falsity*)
                    (add-justification *atms*
                                       *falsity*
                                       justification))
                :before))

(defmethod execute-consumer ((node standard-slot-value))
  "Triggers all class-consumers applicable to an incoming assertion."
  (declare (optimize (speed 3) (safety 1) (space 0) (debug 0)))
  ;; Class-consumers are evaluated upon scheduling of environments.
  (perform
    (dolist (class (class-precedence-list (class-of (datum-object node))))
      (do ((node-classes (node-classes class (datum-slot node))
                         (rest node-classes)))
          ((endp node-classes))
        (let* ((node-class (first node-classes))
               (class-consumer (node-class-consumer node node-class)))
          (when class-consumer
            (task (initiate (match class-consumer node node-class)))))))))

;;; remove-slot-value

(defun remove-slot-value
       (object slot-name value &key negated (recursive (not nil)))
  "Remove a value from a slot, and (optionally) delete it and all data justified solely by it."
  (let ((node (fetch-node object slot-name value negated)))
    (when node
      (unless (truep node)
        (error
        "Attempt to delete a datum that does not hold in the empty environment."
                              ))
                                               ; Cannot delete an assumed
                                               ; datum except by explicity
                                               ; deleting the assumption.
      (remove-node node recursive))))

(defmethod remove-node :after ((n assumption) &optional recursive)
  (declare (ignore recursive))
  (discard-assumption *atms* n))

(defmethod remove-node :before ((n standard-slot-value) &optional recursive)
  "Remove a value from the slot that contains it."
  (declare (ignore recursive))
  (with-accessors ((object datum-object)
                   (slot-name datum-slot))
                  n
         (setf (all-slot-values object slot-name)
               (delete n (all-slot-values object slot-name) :test #'eq))
         (dolist (class (class-precedence-list (class-of object)))
           (dolist (node-class (node-classes class slot-name))
             (apply #'remove-from-cache n node-class)))))

(defmethod remove-node ((n node) &optional (recursive (not nil)))
  "Remove node, and all data justified solely by it."
  (when recursive
    (delete-from-environments n)
    (dolist (justification (consequents n))
      (let ((consequent (consequent justification)))
        (cond ((or (contradictoryp consequent)
                   (not (singletonp (justifications consequent))))
               (setf (justifications consequent)
                 (delete-if #'(lambda (justification)
                                (member n
                                        (antecedents justification)
                                        :test #'eq))
                            (justifications consequent))))
                                               ; Remove justifications for
                                               ; which node is an antecedent.
              (t (setf (justifications consequent) nil)
                 (remove-node consequent))))))
  n)

;;; slot-value-reduce

(defun slot-value-reduce
    (object slot-name &optional (environment *empty-environment*))
  (let ((found nil))
    (flet ((combine (value node)
             (if (or (eq environment t)
                     (in-p node environment))
                 (prog1
                    (if found
                        (combine value node)
                      (elements node))
                    (setq found (not nil)))
               value)))
      (cond ((reduce #'combine (all-slot-values object slot-name)
                     :initial-value nil))
            (found contradictory-value)))))

(defmethod slot-values ((object extended-object) slot-name environment)
  "Returns the values in a slot that hold in an environment."
  (let ((nodes (all-slot-values object slot-name)))
    (if (eq environment t)
        nodes
      (remove-if-not #'(lambda (node)
                         (in-p node environment))
                     nodes))))

;;; describe-data

(defmethod datum-object ((node standard-node)) (datum node))

(defmethod datum-slot ((node standard-node)) nil)

(defmethod assumed-data ((assumptions list))
  (mapcan #'(lambda (assumption)
              (mapcar #'consequent
                      (consequents assumption)))
          assumptions))

(defmethod assumed-data ((e environment))
  (assumed-data (assumptions e)))

(defun describe-data (environment)
  "Prints the assumed data of an environment."
  (let ((assumed-data (assumed-data environment))
          objects object-data)
      (dolist (datum assumed-data)
        (pushnew (datum-object datum) objects :test #'eq))
      (format t "Assumed data of ~S:~%" environment)
      (dolist (object objects)
        (setq object-data (remove object assumed-data
                                  :key #'datum-object
                                  :test-not #'eq))
        (format t "~S~%~{  ~S - ~S~%~}"
                  object
                  (mapcan #'(lambda (slot &aux slot-data)
                              (with-accessors ((slot-name slot-definition-name))
                                              slot
                                (setq slot-data (remove slot-name object-data
                                                        :key #'datum-slot
                                                        :test-not #'eq))
                                (if slot-data
                                    (list slot-name
                                          (if (singletonp slot-data)
                                              (elements (car slot-data))
                                            (reduce #'combine slot-data))))))
                          (class-slots (class-of object)))))
      (values)))

;;; Rule indexing

(defmethod head-node-classes ((class extended-class) slot-name)
  "Returns the classes of nodes, each represented as a list of a proposition and an attribute-reference, generated by class-consumers."
  (gethash slot-name (class-rule-head-index class)))

(defmethod head-node-classes ((class t) slot-name)
  (declare (ignore slot-name))
  nil)

(defmethod node-classes ((class extended-class) slot-name)
  "Yields the node classes, each represented as a list of a proposition and an attribute-reference, of applicable class-consumers."
  (gethash slot-name (class-rule-index class)))

(defmethod node-classes ((class t) slot-name)
  (declare (ignore slot-name))
  nil)

(defmethod class-rule-head-index ((class extended-class))
  (or (slot-value class 'rule-head-index)
      (setf (slot-value class 'rule-head-index) (make-hash-table))))

(defmethod class-rule-index ((class extended-class))
  (or (slot-value class 'rule-index)
      (setf (slot-value class 'rule-index) (make-hash-table))))

(defun collect-node-class-rules (node-classes &aux rules)
  (dolist (node-class node-classes)
                                               ; A node class is represented
                                               ; as a list of a proposition
                                               ; and an attribute reference.
    (pushnew (datum-object (rule-source (class-consumer (car node-class))))
             rules
             :test #'eq))
  rules)

(defun rules-affecting-locally (class slot-name)
  (collect-node-class-rules (head-node-classes class slot-name)))

(defun rules-affecting (class slot-name)
  "Returns the rules that can affect the contents of the given slot."
  (mapcan #'(lambda (class)
              (rules-affecting-locally class slot-name))
    (class-precedence-list class)))

(defun rules-using-locally (class slot-name)
  (collect-node-class-rules (node-classes class slot-name)))

(defun rules-using (class slot-name)
  "Returns the rules that notice data stored in the given slot."
  (mapcan #'(lambda (class)
              (rules-using-locally class slot-name))
    (class-precedence-list class)))

;;; copy-instance

(defmethod copy-instance ((instance standard-object) &rest initargs)
  "Creates a new instance and copies values of slots that have an :initarg option."
  (apply #'make-instance (class-name (class-of instance))
         (mapcan #'(lambda (slot)
                     (with-accessors ((slot-initargs slot-definition-initargs)
                                      (slot-name slot-definition-name))
                                     slot
                       (multiple-value-bind (init-key init-value foundp)
                             (get-properties initargs slot-initargs)
                         (cond (foundp (list init-key init-value))
                               ((null slot-initargs) nil)
                               ((slot-boundp instance slot-name)
                                (list (car slot-initargs)
                                      (slot-value instance slot-name)))))))
                   (class-slots (class-of instance)))))

;;; classify

(defmethod classify ((instance extended-object) (class extended-class) environment)
  "Find class(es) most subordinate to class, under which instance falls (may fall)."
  (flet ((matchp (instance class)
           (flet ((satisfies-type-p (elements type)
                    (typecase elements
                      (numeric-range* (numeric-subrangep elements
                                                         (elements type)))
                      (symbolic-range* (subsetp elements (elements type)))
                      (list (every #'(lambda (element)
                                       (typep (if (typep element
                                                         'excluded-slot-value)
                                                  (datum-value element)
                                                element)
                                              type))
                                   elements)))))
             (map-slots class
                        #'(lambda (slot-definition)
                            (with-accessors ((slot-name slot-definition-name)
                                             (slot-type slot-definition-type))
                                slot-definition
                              (cond ((not (slot-exists-p instance slot-name)))
                                    ((not (slot-boundp instance slot-name)))
                                    ((satisfies-type-p (slot-value-reduce instance
                                                                          slot-name
                                                                          environment)
                                                       (find-class slot-type)))
                                    (t (return-from matchp nil)))))
                        :direct (singletonp (class-direct-superclasses class)))
             (not nil))))
    (let ((result (remove instance
                          (class-direct-subclasses class)
                          :test-not #'matchp)))
      (cond ((null result) (list class))
            ((singletonp result) (classify instance
                                           (car result)
                                           environment))
            (t result)))))

(defmethod notice-slot-values ((instance extended-object)
                               &optional (predicate (complement #'truep)))
  (map-slots (class-of instance)
             #'(lambda (slot-definition)
                 (dolist (node (slot-values instance
                                            (slot-definition-name slot-definition)
                                            t))
                   (when (funcall predicate node)
                     (execute-consumer node))))))

;;; Utilities for making uniquely-named instances and assuming data

(defun make-instances (class-name n names &key (prefix class-name) (package *package*))
  (do ((i 1 (1+ i))
       (j 1 (if (rest rest-names) j (1+ j)))
       (rest-names names (or (rest rest-names) names))
       (instances nil (cons (make-instance class-name
                              :name (if (or (> j 1) (null names))
                                        (intern (format nil "~A-~D"
                                                            (or (first rest-names)
                                                                prefix)
                                                            j)
                                                package)
                                      (first rest-names)))
                            instances)))
      ((> i n) (nreverse instances))))

(defun assume-slot-value (object slot-name value
                          &optional (assumption (make-assumption *atms*))
                                    (no-check (not nil)))
  (add-slot-value object
                  slot-name
                  value
                  assumption
                  :premise
                  :no-check no-check)
  assumption)

(defun assume-slot-values (object initargs
                           &optional (catchall-assumption nil) (no-check (not nil)))
  (do (assumption
       (rest-initargs initargs (cddr rest-initargs))
       (assumptions nil (adjoin (if (and assumption
                                         (or (null catchall-assumption)
                                             (eq assumption catchall-assumption)))
                                    assumption
                                  (assume-slot-value object
                                                     (car rest-initargs)
                                                     (cadr rest-initargs)
                                                     (or catchall-assumption
                                                         (make-assumption *atms*))
                                                     no-check))
                                assumptions
                                :test #'eq)))
      ((endp rest-initargs) (nreverse assumptions))
    (setq assumption (fetch-assumption object
                                       (car rest-initargs)
                                       (cadr rest-initargs)))))