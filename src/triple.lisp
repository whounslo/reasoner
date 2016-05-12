;;; Copyright (C) 2012, 2013, 2014, 2016 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; RDF/XML (de)serialization

(in-package :reasoner-ext)

(eval-when (:execute :compile-toplevel :load-toplevel)
  (import '(rs::numeric-range-intersection rs::validate-superclass
            rs::direct-slot-definition-class rs::effective-slot-definition-class
            rs::extended-direct-slot-definition rs::extended-effective-slot-definition
            rs::compute-effective-slot-definition rs::default-direct-superclass
            rs::slot-definition-composition rs::slot-definition-inverse
            rs::class-dependents-finalized-p))
  (export '(with-rdf with-ontology serialize-objects *allow-multiple-domains*
            with-deserialization-unit
            class-label slot-definition-label resource-label-lang resource-label-text))
  
  (ensure-xml-type-name (intern (string '#:class)
                                (ensure-namespace-package :rdfs)))
  (ensure-xml-type-name (intern (string '#:datatype)
                                (ensure-namespace-package :rdfs)))
  (ensure-xml-type-name (intern (string '#:resource)
                                (ensure-namespace-package :rdfs)))
  (ensure-xml-type-name '(r-d-f i-d description property))
  (ensure-xml-type-name (intern (string '#:class)
                                (ensure-namespace-package :owl)))
  (ensure-xml-type-name (intern (string '#:restriction)
                                (ensure-namespace-package :owl)))
  (ensure-xml-type-name '(ontology object-property datatype-property thing
                          transitive-property symmetric-property
                          functional-property inverse-functional-property
                          )))

(defnamespace :rdf "http://www.w3.org/1999/02/22-rdf-syntax-ns"
  r-d-f description #:resource about i-d #:type #:datatype property)

(defnamespace :rdfs "http://www.w3.org/2000/01/rdf-schema"
  comment label #:class #:resource sub-class-of sub-property-of domain range #:datatype)

(defnamespace :owl "http://www.w3.org/2002/07/owl"
  ontology #:class object-property datatype-property thing same-as
  transitive-property symmetric-property functional-property inverse-of
  inverse-functional-property
  #:restriction on-property cardinality min-cardinality max-cardinality
  all-values-from some-values-from)

(define-xml-name "TransitiveProperty" :transitive :owl)
(define-xml-name "SymmetricProperty" :symmetric :owl)
(define-xml-name "FunctionalProperty" :functional :owl)
(define-xml-name "InverseFunctionalProperty" :inverse-functional :owl)

(define-ignored-elements :rdfs "seeAlso" "isDefinedBy")

(define-ignored-elements :owl
  "equivalentClass" "equivalentProperty" "differentFrom" "AllDifferent"
  "distinctMembers" "versionInfo"
  "imports" "priorVersion" "backwardCompatibleWith" "incompatibleWith"
  "AnnotationProperty" "OntologyProperty" "DeprecatedClass" "DeprecatedProperty")

#+(or allegro ecl lispworks sbcl)
(defstruct (resource-label (:type list)) "Human-readable version of a resource's name."
  lang text)
#-(or allegro ecl lispworks sbcl)
(progn
(defun make-resource-label (&key lang text) (list lang text))
(defun resource-label-lang (label) (car label))
(defun resource-label-text (label) (cadr label))
)

(defclass resource-metaobject (standard-class)
  ((label :reader class-label
          :initarg :label
          :documentation "Human-readable version of a resource's name."))
  (:metaclass standard-class)
  (:default-initargs
     :label nil
     ))

(defclass resource-slot-definition-mixin ()
  ((label :reader slot-definition-label
          :initarg :label
          :documentation "Human-readable version of a property's name."))
  (:metaclass standard-class)
  (:default-initargs
     :label nil
     ))

(defclass resource-direct-slot-definition
          (resource-slot-definition-mixin
           extended-direct-slot-definition)
    ()
  (:metaclass standard-class))

(defclass resource-effective-slot-definition
          (resource-slot-definition-mixin
           extended-effective-slot-definition)
    ()
  (:metaclass standard-class))

(defmethod direct-slot-definition-class ((class resource-metaobject)
                                         &rest initargs)
  (declare (ignore initargs))
  (find-class 'resource-direct-slot-definition))

(defmethod effective-slot-definition-class ((class resource-metaobject)
                                            &rest initargs)
  (declare (ignore initargs))
  (find-class 'resource-effective-slot-definition))

(defclass resource-class (resource-metaobject)
  ()
  (:metaclass standard-class))

(eval-when (:execute #+lispworks :compile-toplevel :load-toplevel)
(defmethod validate-superclass ((class resource-class)
                                (superclass standard-class))
  "Declare compatibility of RESOURCE-CLASS and standard-class."
  (not nil))
)

(defclass xmlrdfs::class (resource-metaobject extended-class)
  ()
  (:metaclass resource-class))

(defclass xmlowl::class (xmlrdfs::class)
  ()
  (:metaclass resource-class))

(defclass xmlrdfs::resource (extended-object)
  ()
  (:metaclass xmlrdfs::class))

(defmethod compute-effective-slot-definition :before ((class xmlrdfs::class)
                                                      name
                                                      direct-slot-definitions)
  (when (find-slot-definition class name
                              :direct (not nil)
                              :key #'slot-definition-count)
    (do ((type-1 (slot-definition-type (car direct-slot-definitions)) type-2)
         type-2
         (direct-slots direct-slot-definitions (cdr direct-slots)))
        ((endp (cdr direct-slots)))
      (setq type-2 (slot-definition-type (cadr direct-slots)))
      (adjust-count-type type-1 type-2))))

(let ((the-class-resource (find-class 'xmlrdfs::resource)))

(setf (find-class 'thing) the-class-resource)

(defmethod default-direct-superclass ((class xmlrdfs::class))
  the-class-resource)

  ) ;end let the-class-resource

(defmethod initialize-instance :after ((class xmlrdfs::class)
                                       &key same-as
                                       &allow-other-keys)
  (when same-as (setf (find-class same-as) class)))

(defmethod reinitialize-instance :after ((class xmlrdfs::class)
                                         &key same-as
                                         &allow-other-keys)
  (when same-as (setf (find-class same-as) class)))

(defun get-id (name)

  ;; Inhibit expansion to URI.
  (symbol-name (get-xml-name name)))

(defun name-attribute (name)
  (if (eq (symbol-package name)
          (or (namespace-package *target-namespace*) *package*))
      (list :i-d (get-id name))
    (list :about name)))

(defparameter *allow-multiple-domains* nil)

(defmethod slot-definition-label ((slot slot-definition))
  nil)

(defmethod serialize-language-label ((label string))
  (as :label label))

(defmethod serialize-language-label ((label cons))
  (as (:label :lang (resource-label-lang label))
    (resource-label-text label)))

(defmethod serialize-label ((label string))
  (serialize-language-label label))

(defmethod serialize-label ((label list))
  (if (singletonp label)
      (serialize-language-label (resource-label-text (first label)))
    (mapc #'serialize-language-label label)))

(defun serialize-property-documentation (slot-definition)
  (let ((comment (documentation slot-definition t))
        (label (slot-definition-label slot-definition)))
    (serialize-label label)
    (when comment
      (as :comment comment))))

(defmethod serialize-property-definition ((class extended-class)
                                          (slot slot-definition)
                                          count-slot
                                          (format (eql :rdfs)))
  (declare (ignore count-slot))
  (let ((slot-name (slot-definition-name slot)))
    (labels ((add-properties (class slot supertype &aux type)
               (setq type (if slot (slot-definition-type slot)))
               (when (and type (not (eq type t)))
                 (unless (eq type supertype)
                   (as (:domain 'xmlrdf::resource (ensure-xml-type-name class)))
                   (as (:range 'xmlrdf::resource (if (subtypep type 'extended-object)
                                                     (ensure-xml-type-name type)
                                                   type)))))
               (when *allow-multiple-domains*
                 (dolist (subclass (class-direct-subclasses class))
                   (add-properties subclass
                                   (find-slot-definition subclass slot-name
                                                         :direct (not nil))
                                   (or type supertype))))))
      (xml-newline)
      (with* :property (name-attribute slot-name)
        (serialize-property-documentation slot)
        (add-properties class slot nil)))))

(defmethod serialize-class ((class extended-class)
                            (format (eql :rdfs))
                            &optional (derived (not nil)))
  (serialize-resource-class class format derived))

(defmethod serialize-class ((class resource-class)
                            (format (eql :rdfs))
                            &optional derived)
  (declare (ignore derived))
  (serialize-resource-class class format 'derived (find-class 'xmlrdfs::class)))

(defmethod serialize-class ((class range-class)
                            (format (eql :rdfs))
                            &optional derived
                            &aux (tag 'xmlrdfs::datatype))
  (declare (ignore derived))
  (as (tag :about (class-name class))))

(defun primary-slot-definition (class slot
                                &aux (name (slot-definition-name slot)))
  (ensure-cpl class)
  (map-slots class
             #'(lambda (slot-definition)
                 (when (eq (slot-definition-name slot-definition)
                           name)
                   (return-from primary-slot-definition slot-definition)))
             :from-end (not nil)))

(defun functional-property-p (min max)
  (and (zerop min) (eql max 1)))

(defmethod serialize-property-definition ((class extended-class)
                                          (slot slot-definition)
                                          count-slot
                                          (format (eql :owl))
                                          &aux tag)
  (with-accessors ((slot-name slot-definition-name)
                   (slot-type slot-definition-type)
                   (slot-composition slot-definition-composition)
                   (slot-inverse slot-definition-inverse))
      slot
    (setq tag (if (subtypep slot-type 'extended-object)
                  :object-property
                :datatype-property))
    (xml-newline)
    (with* tag (name-attribute slot-name)
      (serialize-property-documentation slot)
      (cond ((null slot-composition)
             (multiple-value-bind (min max)
                 (element-occurrence-bounds count-slot)
               (when (functional-property-p min max)
                 (as (:type 'xmlrdf::resource :functional)))))
            ((symbolp slot-composition)
             (as (:type 'xmlrdf::resource slot-composition)))
            ((singletonp slot-composition)
             (let ((slot (find-slot-definition class (first slot-composition))))
               (when slot
                 (as (:sub-property-of 'xmlrdf::resource (slot-definition-name slot)))))))
      (when slot-inverse
        (as (:inverse-of 'xmlrdf::resource slot-inverse)))
      (as (:domain 'xmlrdf::resource (ensure-xml-type-name class)))
      (as (:range 'xmlrdf::resource (if (eq tag :object-property)
                                        (ensure-xml-type-name slot-type)
                                      slot-type))))))

(defun direct-slot-definition-p (class slot count-slot)
  (or (not count-slot)
      (find-slot-definition class slot :direct (not nil) :key #'identity)))

(defmethod serialize-resource-class :before ((class extended-class) format derived
                                             &optional metaclass)
  (declare (ignore metaclass))
  (map-core-slots class
                  #'(lambda (slot count-slot)
                        (when (direct-slot-definition-p class slot count-slot)
                          (when (or (not derived)
                                    (eq slot (primary-slot-definition class slot)))
                            (serialize-property-definition class slot count-slot format)
                            (separate-definitions))))
                  :direct (not nil)))

(defmethod subclass-restriction-p ((class extended-class) format)
  (declare (ignore format))
  nil)

(defmethod subclass-restriction-p ((class resource-class) format)
  (declare (ignore format))
  nil)

(defmethod subclass-restriction-p ((class extended-class) (format (eql :owl)))
  (map-core-slots class
                  #'(lambda (slot count-slot)
                      (when count-slot
                        (multiple-value-bind (min max)
                            (element-occurrence-bounds count-slot)
                          (unless (and (functional-property-p min max)
                                       (eq slot
                                           (primary-slot-definition class slot)))
                            (return-from subclass-restriction-p (not nil))))))
                  :direct (not nil)))

(defmethod serialize-restrictions ((class extended-class) format)
  (declare (ignore format))
  )

(defmethod serialize-restrictions ((class resource-class) format)
  (declare (ignore format))
  )

(defmethod serialize-restrictions ((class extended-class) (format (eql :owl)))
  (flet ((serialize-anonymous-superclass (slot &optional property value)
           (with :sub-class-of
             (with :restriction
               (as (:on-property 'xmlrdf::resource (slot-definition-name slot)))
               (if property
                   (as (property 'xmlrdf::datatype :non-negative-integer)
                     value)
                 (as (:all-values-from 'xmlrdf::resource (slot-definition-type slot))))))))
    (map-core-slots class
                    #'(lambda (slot count-slot &aux primary-slot)
                        (when (direct-slot-definition-p class slot count-slot)
                          (setq primary-slot (primary-slot-definition class slot))
                          (unless (eq slot primary-slot)
                            (when (subtypep (slot-definition-type slot)
                                            (slot-definition-type primary-slot))
                              (serialize-anonymous-superclass slot))))
                        (when count-slot
                          (multiple-value-bind (min max)
                              (element-occurrence-bounds count-slot)
                            (cond ((eql min max)
                                   (serialize-anonymous-superclass slot
                                                                   :cardinality
                                                                   min))
                                  ((and (functional-property-p min max)
                                        (eq slot primary-slot)))
                                  (t
                                   (unless (eql min 0)
                                     (serialize-anonymous-superclass slot
                                                                     :min-cardinality
                                                                     min))
                                   (unless (eql max 'unbounded)
                                     (serialize-anonymous-superclass slot
                                                                     :max-cardinality
                                                                     max)))))))
                    :direct (not nil))))

(defmethod serialize-resource-class (class format derived
                                     &optional (metaclass (class-of class)))
  (let ((type-name (ensure-xml-type-name class))
        (tag (ensure-xml-type-name metaclass))
        (superclasses (class-direct-superclasses class))
        show-superclasses
        (comment (documentation class t))
        (label (class-label class)))
    (setq show-superclasses (and derived
                                 (notevery #'(lambda (superclass)
                                               (eq (class-name superclass)
                                                   'xmlrdfs::resource))
                                           superclasses)))
    (cond ((or comment label
               show-superclasses
               (subclass-restriction-p class format))
           (xml-newline)
           (with* tag (name-attribute type-name)
             (when show-superclasses
               (dolist (superclass superclasses)
                 (as (:sub-class-of 'xmlrdf::resource (ensure-xml-type-name superclass)))))
             (serialize-restrictions class format)
             (serialize-label label)
             (when comment
               (as :comment comment))))
          (t
           (as* tag (name-attribute type-name) nil 'freshline)))))

(defmethod class-label ((class extended-class))
  nil)

(defmethod serialize-class ((class extended-class)
                            (format (eql :owl))
                            &optional (derived (not nil)))
  (serialize-resource-class class format derived))

(defmethod serialize-class ((class resource-class)
                            (format (eql :owl))
                            &optional derived)
  (declare (ignore derived))
  (serialize-resource-class class format 'derived (find-class 'xmlowl::class)))

(defmethod serialize-value ((instance extended-object)
                            (format (eql :rdf))
                            (e environment)
                            tag
                            slot-type
                            &aux (instance-name (instance-name instance)))
  (if instance-name
      (as (tag 'xmlrdf::resource (instance-name instance)))
    (with tag
      (serialize-object instance format e tag slot-type nil))))

(defmethod serialize-slot ((instance extended-object)
                           (slot slot-definition)
                           (format (eql :rdf))
                           (e environment)
                           &aux value)
  (with-accessors ((slot-name slot-definition-name)
                   (slot-type slot-definition-type)
                   (slot-count slot-definition-count))
      slot
    (setq value (slot-value-reduce instance slot-name e))
    (if (or slot-count (subtypep slot-type 'extended-object))
        (revdolist (object value)
          (serialize-value object format e slot-name slot-type))
      (serialize-value value format e slot-name slot-type))))

(defmethod instance-content-p ((instance extended-object) (e environment))
  (map-core-slots (class-of instance)
                  #'(lambda (slot count-slot)
                      (declare (ignore count-slot))
                      (with-accessors ((slot-name slot-definition-name)
                                       (slot-type slot-definition-type))
                          slot
                        (when (if (subtypep slot-type 'extended-object)
                                  (slot-values instance slot-name e)
                                (slot-value-to-content (slot-value-reduce instance
                                                                          slot-name
                                                                          e)
                                                       slot-type))
                          (return-from instance-content-p (not nil)))))))

(defmethod serialize-object ((instance extended-object)
                             (format (eql :rdf))
                             (e environment)
                             &optional tag type (global (not nil))
                             &aux (class (class-of instance))
                                  (instance-name (instance-name instance))
                                  name-attribute)
  (declare (ignore type))
  (unless (or instance-name (not global))
    (error "Attempt to serialize an unnamed instance."))
  (flet ((serialize-slot (slot count-slot)
           (when count-slot
             (setq e (satisfy-occurrence-constraint class
                                                    instance
                                                    slot
                                                    count-slot
                                                    e)))
           (serialize-slot instance slot format e)))
    (setq tag (ensure-xml-type-name (class-name class))
        name-attribute (if instance-name (name-attribute instance-name)))
    (cond ((instance-content-p instance e)
           (xml-newline)
           (with* tag name-attribute
             (map-core-slots class #'serialize-slot)))
          (t (as* tag name-attribute nil 'freshline)))))

(defmethod serialize-object ((instance extended-object)
                             (format (eql :owl))
                             (e environment)
                             &optional tag type global)
  (serialize-object instance :rdf e tag type global))

(defmethod serialize-object ((object t)
                             (format (eql :rdf))
                             (e environment)
                             &optional tag type global
                             &aux (datatype (range-external-type type)))
  (declare (ignore global))
  (serialize-simple-object object
                           tag
                           (list 'xmlrdf::datatype datatype)
                           datatype))

(defmethod serialize-object ((object null)
                             (format (eql :rdf))
                             (e environment)
                             &optional tag type global)
  (declare (ignore tag type global))
  )

(defmethod serialize-objects ((instance extended-object)
                              (format (eql :rdf))
                              (e environment)
                              &optional (global (not nil)))
  (when (instance-name instance)
    (unless global (separate-definitions))
    (serialize-object instance format e))
  (map-core-slots (class-of instance)
                  #'(lambda (slot count-slot)
                      (with-accessors ((slot-name slot-definition-name)
                                       (slot-type slot-definition-type))
                          slot
                        (when (or count-slot
                                  (subtypep slot-type 'extended-object))
                          (dolist (instance (slot-value-reduce instance
                                                               slot-name
                                                               e))
                            (serialize-objects instance format e nil)))))))

(defparameter *rdf-unique-name-fn* (constantly nil))

(defmacro with-rdf ((&key (xml-version nil version-supp)
                          (xml-base nil target-supp)
                          (namespaces nil)
                          (default-namespace nil))
                    &body body)
  `(with-xml (,@(if version-supp
                    `(:version ,xml-version))
              ,@(if target-supp
                    `(:target-namespace ,xml-base))
              :namespaces ,namespaces
              :default-namespace ,default-namespace)
     (let ((*expand-attribute-value* (not nil))
           (*unique-name-fn* *rdf-unique-name-fn*))
       (with* :r-d-f (nconc (if *target-namespace*
                                (list "xml:base"
                                      (namespace-uri-variant *target-namespace*)))
                            (namespace-declarations))
         ,@body))))

(defmacro with-ontology ((&key (xml-version nil version-supp)
                               (about nil)
                               (namespaces nil)
                               (default-namespace nil)
                               (comment nil)
                               (label nil)
                               (label-lang nil))
                         &body body)
  `(with-rdf (,@(if version-supp
                    `(:version ,xml-version))
              :xml-base ,about
              :namespaces ,namespaces
              :default-namespace ,default-namespace)
     (with (:ontology :about "")
       (when ,label
         (as* :label (if ,label-lang (list :lang ,label-lang))
           (princ ,label) 'freshline))
       (when ,comment
         (as :comment
           ,comment)))
     ,@body))

;;; Deserialization

(defun get-resource-name (element &optional about)
  (or (and (not about)
           (let ((*default-namespace* *target-namespace*))
                                               ; ID always relative to base URI.
             (element-attribute element 'i-d :rdf)))
      (element-attribute element 'about :rdf)))

(defun get-resource-reference (element)
  (element-attribute element 'resource :rdf))

(defun ensure-lisp-type-name (name)
  (let ((lisp-name (ensure-lisp-name name)))
    (if (find-class lisp-name nil)
        lisp-name
      name)))

(defmacro modify-slot-specification (specification tag value-form)
  (ecase tag
    
    ;; Property definition.
    (:type `(setf (getf ,specification :composition)
              ,(if value-form `(ensure-lisp-name ,value-form))))
    (:sub-property-of `(setf (getf ,specification :composition)
                         (list ,value-form)))
    (:inverse-of `(setf (getf ,specification :inverse) ,value-form))
    ((:domain :range) (let ((indicator (case tag
                                         (:domain :name)
                                               ; Temporary storage.
                                         (:range :type))))
                        `(let ((value (getf ,specification ,indicator))
                               (new-value (ensure-lisp-type-name ,value-form)))
                           (unless (and value (or (eq value 'xmlrdfs::resource)
                                                  (find-class value nil))
                                        (find-class new-value nil)
                                        (not (subtypep new-value value)))
                             (setf (getf ,specification ,indicator) new-value)))))
    
    ;; Class definition.
    (:on-property `(setf (getf ,specification :name) ,value-form))
    (:all-values-from `(setf (getf ,specification :type) (ensure-lisp-type-name
                                                          ,value-form)))
    (:some-values-from `(progn
                          (setf (getf ,specification :type) (ensure-lisp-type-name
                                                             ,value-form))
                          (setf (getf ,specification :composition) tag)))
    (:cardinality `(setf (getf ,specification :count)
                     (make-numeric-range :min ,value-form
                                         :max ,value-form)))
    (:min-cardinality `(setf (getf ,specification :count)
                         (make-numeric-range :min ,value-form
                                             :max 'big)))
    (:max-cardinality `(setf (getf ,specification :count)
                         (make-numeric-range :min 0
                                             :max ,value-form)))))

(defmacro modify-class-options (options option new-value)
  `(case ,option
     ((:direct-superclasses :direct-slots :label) (push-on-end (getf ,options ,option)
                                                               ,new-value))
     (t (setf (getf ,options ,option) ,new-value))))

(defmacro class-options-p (content)
  `(find :metaclass ,content :test #'eq))

(defmacro member-specification (key-form specifications
                                &key (indicator :name))
  `(member ,key-form ,specifications :test #'eq :key #'(lambda (slot)
                                                         (getf slot ,indicator))))

(defvar *class-slot-specifications* nil)

(defmacro with-deserialization-unit (&body body)
  `(let ((*class-slot-specifications* nil))
     ,@body))

(defun map-slot-specifications (fn)
  (revdolist (item *class-slot-specifications*)
    (destructuring-bind (class-name . slot-specifications)
        item
      (funcall fn class-name slot-specifications))))

(defun find-slot-specification (name)
  (when name
    (map-slot-specifications
     #'(lambda (class-name slot-specifications &aux specification)
         (setq specification (first
                              (member-specification name
                                                    slot-specifications)))
         (when specification
           (modify-slot-specification specification :domain class-name)
           (return-from find-slot-specification specification))))))

(defmacro make-slot-specification
           (&key name (domain ''xmlrdfs::resource) (range ''xmlrdfs::resource) type)
  `(let ((specification (find-slot-specification ,name)))
     (unless specification
       (modify-slot-specification specification :domain ,domain))
     ,@(if range `((modify-slot-specification specification :range ,range)))
     ,@(if type `((modify-slot-specification specification :type ,type)))
     specification))

(defmethod find-element-type (tag (object xmlrdfs::resource))
  (declare (ignore tag))
  nil)

(defmethod find-element-object ((tag (eql 'r-d-f)) element superelements)
  (declare (ignore element superelements))
  tag)

(defmethod find-element-object ((tag (eql 'description)) element superelements)
  (declare (ignore element superelements))
  nil)

(defmethod find-element-object ((tag (eql 'xmlrdfs::datatype)) element superelements)
  (declare (ignore element superelements))
  nil)

(defmethod find-element-object ((tag (eql 'property)) element superelements)
  (declare (ignore element superelements))
  (make-slot-specification :range nil))

(defmethod element-object-missing (class element superelement)
  (declare (ignore class element superelement))
  nil)

(defun ensure-finished (class)
  (unless (class-dependents-finalized-p class) (finish-classes)))

(defmethod element-object-missing ((class xmlrdfs::class) element superelement)
  (declare (ignore superelement))
  (let ((name (get-resource-name element)))
    (or (and name (let ((instance (find-instance name nil)))
                    (when instance
                      (unless (or (eq (class-name class) 'xmlrdfs::resource)
                                               ; Being referred to as 'Thing'.
                                  (eq (class-of instance) class))
                        
                        ;; Forward reference.
                        (change-class instance class)))
                    instance))
        (progn
          (ensure-finished class)
          (make-instance class :name name)))))

(defmethod element-object-missing ((class resource-class) element superelement)
  (declare (ignore element superelement))
  (let (options)
    (modify-class-options options :metaclass class)
    options))

(defmethod find-element-object :around (tag element superelements)
  (or (call-next-method)
      (element-object-missing (or (find-class tag nil)
                                  (find-class (get-tag-lisp-name tag) nil))
                              element
                              (first superelements))))

(defmethod assimilate-content (element (element-content (eql 'r-d-f))
                               subelement tag content)
  (declare (ignore element subelement tag))
  (when (consp content) (call-next-method)))

(defgeneric get-class-reference (object)
  (:method ((class-name symbol))
    (or (find-class class-name nil)
        (find-class (ensure-lisp-name class-name) nil)))
  (:method ((object element))
    (get-class-reference (get-resource-reference object))))

(defmethod assimilate-content (element element-content
                               subelement (tag (eql 'xmlrdf::type)) content)
  (declare (ignore element-content content))
  (setf (element-content element) (element-object-missing (get-class-reference
                                                           subelement)
                                                          element
                                                          nil)))

(defmethod assimilate-content (element (element-content xmlrdfs::resource)
                               subelement (tag (eql 'xmlrdf::type)) content)
  (declare (ignore element content))
  (let ((class (find-class (get-resource-reference subelement))))
    (ensure-finished class)
    (change-class element-content class)))

(defmacro get-instance-reference (element
                                  &optional type &aux (default-type ''xmlrdfs::resource))
  `(let ((name (get-resource-reference ,element)))
    (and name
         (or (find-instance name nil)
             
             ;; Forward reference.
             (make-instance ,(if type `(or ,type ,default-type) default-type)
               :name name)))))

(defmethod assimilate-content
           (element (element-content xmlrdfs::resource) subelement tag (content null))
  (let ((value (get-instance-reference subelement
                                       (default-element-type tag element-content))))
    (when value
      (assimilate-content element element-content subelement tag value))))

(defmethod assimilate-content (element (element-content xmlrdfs::resource)
                               subelement (tag (eql 'same-as)) content)
  (declare (ignore content))
  (let ((object (get-instance-reference subelement)))
    (when object
      (setf (find-instance (get-resource-name element)) object))))

(defmethod find-element-object ((tag (eql 'object-property)) element superelements)
  (declare (ignore element superelements))
  (make-slot-specification))

(defmethod find-element-object ((tag (eql :transitive)) element superelements)
  (declare (ignore superelements))
  (make-slot-specification :name (get-resource-name element 'about)
                           :type :transitive))

(defmethod find-element-object ((tag (eql :symmetric)) element superelements)
  (declare (ignore superelements))
  (make-slot-specification :name (get-resource-name element 'about)
                           :type :symmetric))

(defmethod find-element-object ((tag (eql :functional)) element superelements)
  (declare (ignore superelements))
  (make-slot-specification :name (get-resource-name element 'about)))

(defmethod find-element-object ((tag (eql :inverse-functional)) element superelements)
  (declare (ignore superelements))
  (make-slot-specification :name (get-resource-name element 'about)
                           :type :inverse-functional))

(defmethod find-element-object ((tag (eql 'datatype-property)) element superelements)
  (declare (ignore element superelements))
  (make-slot-specification :range nil))

(defmethod find-element-object ((tag (eql 'sub-class-of)) element superelements)
  (declare (ignore element superelements))
  nil)

(defmethod find-element-object
           ((tag (eql 'xmlowl::restriction)) element superelements)
  (declare (ignore element superelements))
  (make-slot-specification :range nil))

(defmacro class-slot-specifications (class-name)
  `(cdr (assoc ,class-name *class-slot-specifications* :test #'eq)))

(defmacro merge-specifications (place specification)
  `(do ((properties ,specification (cddr properties)))
       ((endp properties))
     (setf (getf ,place (car properties))
       (cadr properties))))

(defun propagate-slot-specification (class-name specification)
  (let ((class-specifications (class-slot-specifications class-name))
        (specifications (expand-slot-specification (list specification))))
    (if class-specifications
        (let* ((name (getf specification :name))
               (rest-specifications (member-specification name
                                                          class-specifications)))
          (cond ((null rest-specifications)
                 (nconc class-specifications specifications))
                ((singletonp specifications)
                 (error "Attempt to redefine property \"~A,\" domain \"~A\"."
                   (get-xml-name name) (get-xml-name class-name)))
                (t                             ; Cardinality.
                 (merge-specifications (car rest-specifications) (car specifications))
                 (let ((specification
                        (car (member-specification (getf (cadr specifications) :name)
                                                   class-specifications))))
                   (if specification
                       (setf (getf specification :type)
                         (numeric-range-intersection (getf specification :type)
                                                     (getf (cadr specifications) :type)))
                                               ; Combine min and max cardinality
                                               ; constraints.
                     (push-on-end class-specifications (cadr specifications)))))))
      (push (cons class-name specifications) *class-slot-specifications*))))

(defun assimilate-to-slot (name specification)
  (let ((class-name (getf specification :name)))
    (modify-slot-specification specification :on-property name)
    (propagate-slot-specification class-name specification)))

(defmethod assimilate-content (element element-content
                               subelement (tag (eql 'property)) (content cons))
  (declare (ignore element element-content))
  (assimilate-to-slot (get-resource-name subelement) content))

(defmacro property-characteristic (slot-specification)
  `(getf ,slot-specification :composition))

(defmacro modify-functional-slot-specification (specification)
  `(progn
     (modify-slot-specification ,specification :min-cardinality 0)
     (modify-slot-specification ,specification :max-cardinality 1)))

(defun finalize-functional-property (element)
  (modify-functional-slot-specification (element-content element))
  (modify-slot-specification (element-content element) :type nil))

(defmethod finalize-content (element (tag (eql :functional)) (content cons))
  (finalize-functional-property element))

(defmethod finalize-content (element (tag (eql 'object-property)) (content cons))
  (when (eq (property-characteristic content) :functional)
    (finalize-functional-property element)))

(defmethod assimilate-content
           (element element-content
            subelement (tag (eql 'object-property)) (content cons))
  (declare (ignore element element-content))
  (assimilate-to-slot (get-resource-name subelement) content))

(defmethod assimilate-content
           (element element-content
            subelement (tag (eql :transitive)) (content cons))
  (declare (ignore element element-content))
  (assimilate-to-slot (get-resource-name subelement) content))

(defmethod assimilate-content
           (element element-content
            subelement (tag (eql :symmetric)) (content cons))
  (declare (ignore element element-content))
  (assimilate-to-slot (get-resource-name subelement) content))

(defmethod assimilate-content
           (element element-content
            subelement (tag (eql :functional)) (content cons))
  (declare (ignore element element-content))
  (assimilate-to-slot (get-resource-name subelement) content))

(defmethod assimilate-content
           (element element-content
            subelement (tag (eql :inverse-functional)) (content cons))
  (declare (ignore element element-content))
  (assimilate-to-slot (get-resource-name subelement) content))

(defmethod assimilate-content
           (element element-content
            subelement (tag (eql 'datatype-property)) (content cons))
  (declare (ignore element element-content))
  (assimilate-to-slot (get-resource-name subelement) content))

(defmethod assimilate-content (element (element-content cons)
                               subelement (tag (eql 'xmlrdf::type)) content)
  (declare (ignore content))
  (modify-slot-specification (element-content element)
                             :type
                             (get-resource-reference subelement)))

(defmethod assimilate-content (element (element-content cons)
                               subelement (tag (eql 'sub-property-of)) content)
  (declare (ignore content))
  (modify-slot-specification (element-content element)
                             :sub-property-of
                             (get-resource-reference subelement)))

(defmethod assimilate-content (element (element-content cons)
                               subelement (tag (eql 'inverse-of)) content)
  (declare (ignore content))
  (modify-slot-specification (element-content element)
                             :inverse-of
                             (get-resource-reference subelement)))

(defmethod assimilate-content (element (element-content cons)
                               subelement (tag (eql 'domain)) content)
  (declare (ignore content))
  (modify-slot-specification (element-content element)
                             :domain
                             (get-resource-reference subelement)))

(defmethod assimilate-content (element (element-content cons)
                               subelement (tag (eql 'range)) content)
  (declare (ignore content))
  (modify-slot-specification (element-content element)
                             :range
                             (get-resource-reference subelement)))

(defmethod assimilate-content (element element-content
                               subelement (tag (eql 'xmlrdfs::class)) (content cons))
  (declare (ignore element element-content))
  (let ((class-name-1 (getf content :same-as))
        (class-name-2 (get-resource-name subelement))
        class-name)
    (unless class-name-2
      (error "Attempt to deserialize an unnamed class."))
    (when class-name-1
      (modify-class-options content :same-as class-name-2))
    (setq class-name (or class-name-1 class-name-2))
    (dolist (specification (getf content :direct-slots))
      (propagate-slot-specification class-name specification))
    (remf content :direct-slots)
    (apply #'ensure-class class-name content)))

(defmethod assimilate-content (element element-content
                               subelement (tag (eql 'xmlowl::class)) (content cons))
  (assimilate-content element element-content subelement 'xmlrdfs::class content))

(defmethod assimilate-content (element element-content
                               subelement (tag (eql 'description)) (content cons))
  (assimilate-content element element-content subelement 'xmlrdfs::class content))

(defmethod assimilate-content
           (element element-content subelement tag (content cons))
  (declare (ignore tag))
  (if (class-options-p content)
      
      ;; Arbitrary metaclass.
      (assimilate-content element element-content subelement 'xmlrdfs::class content)
    (call-next-method)))

(defmethod finalize-content (element (tag (eql 'label)) (content string))
  (declare (ignore element))

  ;; Preserve as string.
  )

(defmethod finalize-content (element (tag (eql 'comment)) (content string))

  ;; Preserve as string.
  (setf (element-content element) (string-trim whitespace content)))

(defmethod assimilate-content (element (element-content cons)
                               subelement (tag (eql 'label)) content)
  
  ;; Modify class or slot specification.
  (modify-class-options (element-content element)
                        :label
                        (make-resource-label :lang (element-attribute subelement
                                                                      'xmlxml::lang
                                                                      :xml
                                                                      "en")
                                             :text content)))

(defmethod assimilate-content (element element-content
                               subelement (tag (eql 'comment)) content)
  (declare (ignore element element-content subelement content))
  
  ;; Ontology header.
  )

(defmethod assimilate-content (element (element-content cons)
                               subelement (tag (eql 'comment)) content)
  (declare (ignore subelement))
  
  ;; Modify class or slot specification.
  (modify-class-options (element-content element) :documentation content))

(defmethod assimilate-content (element (element-content cons)
                               subelement (tag (eql 'same-as)) content)
  (declare (ignore content))
  (modify-class-options (element-content element)
                        :same-as
                        (get-resource-reference subelement)))

(defmethod assimilate-content (element (element-content cons)
                               subelement (tag (eql 'sub-class-of)) content)
  (declare (ignore content))
  (let* ((superclass-name (get-resource-reference subelement))
         (superclass (get-class-reference superclass-name)))
    (when (and superclass
               (subtypep superclass 'extended-class))
                                               ; Metaclass (subclass of a metaclass)?
      (modify-class-options (element-content element) :metaclass 'resource-class))
    (modify-class-options (element-content element)
                          :direct-superclasses
                          (if superclass
                              (class-name superclass)
                            superclass-name))))

(defmethod assimilate-content (element (element-content cons)
                               subelement (tag (eql 'sub-class-of)) (content cons))
  (declare (ignore subelement))
  (modify-class-options (element-content element) :direct-slots content))

(defmethod finalize-content (element (tag (eql 'xmlowl::restriction)) (content cons))
  (when (eq (getf content :composition) 'some-values-from)
    (let ((name (getf content :name)))
      (modify-slot-specification (element-content element)
                                 :on-property
                                 (add-lisp-name-suffix name (getf content :type)))
      (modify-slot-specification (element-content element) :sub-property-of name)
      (modify-slot-specification (element-content element) :min-cardinality 1))))

(defmethod assimilate-content (element (element-content cons)
                               subelement (tag (eql 'on-property)) content)
  (declare (ignore content))
  (modify-slot-specification (element-content element)
                             :on-property
                             (get-resource-reference subelement)))

(defmethod assimilate-content (element (element-content cons)
                               subelement (tag (eql 'all-values-from)) content)
  (declare (ignore content))
  (modify-slot-specification (element-content element)
                             :all-values-from
                             (get-resource-reference subelement)))

(defmethod assimilate-content (element (element-content cons)
                               subelement (tag (eql 'some-values-from)) content)
  (declare (ignore content))
  (modify-slot-specification (element-content element)
                             :some-values-from
                             (get-resource-reference subelement)))

(defmethod assimilate-content (element (element-content cons)
                               subelement (tag (eql 'cardinality)) content)
  (declare (ignore subelement))
  (modify-slot-specification (element-content element) :cardinality content))

(defmethod assimilate-content (element (element-content cons)
                               subelement (tag (eql 'min-cardinality)) content)
  (declare (ignore subelement))
  (modify-slot-specification (element-content element) :min-cardinality content))

(defmethod assimilate-content (element (element-content cons)
                               subelement (tag (eql 'max-cardinality)) content)
  (declare (ignore subelement))
  (modify-slot-specification (element-content element) :max-cardinality content))

(defun finish-classes ()
  (map-slot-specifications
   #'(lambda (class-name slot-specifications)
       (dolist (specification slot-specifications)
         (when (getf specification :inverse)
           (let ((specifications
                  (member-specification (getf specification :inverse)
                                        (class-slot-specifications
                                         (getf specification :type)))))
             (when specifications
               (cond ((eq (property-characteristic specification)
                          :inverse-functional)
                      (modify-slot-specification specification :type nil)
                      (modify-functional-slot-specification (first specifications))
                      (propagate-slot-specification (getf specification :type)
                                                    (first specifications)))
                     ((eq (property-characteristic (first specifications))
                          :inverse-functional)
                      (modify-slot-specification (first specifications) :type nil)
                      (modify-functional-slot-specification specification)
                      (propagate-slot-specification class-name
                                                    specification)))))))))
  (map-slot-specifications
   #'(lambda (class-name slot-specifications &aux (class (find-class class-name)))
       
       ;; Apply accumulated slot specifications to class.
       (ensure-class-using-class class
                                 class-name
                                 :metaclass (class-of class)
                                             ; If absent, most Lisps compare default
                                             ; with actual, and signal an error.
                                 :direct-slots
                                 (finalize-slots class-name
                                                 slot-specifications)))))

(defmethod finalize-content (element (tag (eql 'r-d-f)) content)
  (declare (ignore element content))
  (finish-classes))