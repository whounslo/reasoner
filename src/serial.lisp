;;; Copyright (C) 2011-2014 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; XML serialization

(in-package :reasoner-ext)

(eval-when (:execute :compile-toplevel :load-toplevel)
  (import '(rs::class-precedence-list rs::class-direct-subclasses
            rs::class-slots rs::class-direct-slots
            rs::class-finalized-p rs::finalize-inheritance
            rs::standard-effective-slot-definition
            rs::extended-slot-definition-mixin
            atms:assumptions
            rs::rules-affecting-locally
            rs::range-elements rs::range-class
            rs::well-formed-formula rs::source-form rs::parse
            rs::*rewrite-in-parser* rs::proposition-specializer
            rs::attribute-name rs::attribute-reference-variable
            rs::operatorp rs::unary-minus-p rs::aggregate-function-name-p
            atms:datum-assumption rs::instance-node))
  (export '(*xml-print-pretty* *xml-pprint-indent* *emphasize-type-name*
            *separate-definitions* redirect-to-stream
            *target-namespace* *default-namespace*
            *qualified-local-elements* *qualified-local-attributes*
            with-schema as-top-level-element serialize-class-hierarchy
            serialize-class *use-list-simple-types*
            with-xml serialize-object serialize-slot
            serialize-rules serialize-rule
            range-to-content format-as-type print-as-type
            )))

(defparameter *qualified-local-elements* nil)

(defparameter *qualified-local-attributes* nil)

(defparameter *use-list-simple-types* nil)

(defparameter *expand-attribute-value* nil)

(defun get-namespace (name &aux sym)
  (values (or (find (symbol-package name) *namespaces*
                    :test #'eq :key #'namespace-package)
              (find-if #'(lambda (namespace)
                           (setq sym
                                 (find-symbol (string name)
                                              (ensure-namespace-package namespace))))
                       *namespaces*))
          (or sym name)))

(defmethod pprint-xml-name (stream object &optional colon-p at-sign-p)
  (declare (ignore colon-p at-sign-p))
  (princ object stream))

(defmethod pprint-xml-name (stream (object symbol) &optional colon-p at-sign-p)
  (flet ((qualifiedp (namespace)
           (cond ((eq namespace *default-namespace*)
                  nil)
                 ((null *target-namespace*)
                  (not nil))
                 ((not (eq namespace *target-namespace*))
                  (not nil))
                 (colon-p *qualified-local-attributes*)
                                               ; Attribute name.
                 (at-sign-p)                   ; Attribute value.
        
                 ;; Element name.
                 (t *qualified-local-elements*)))
         (pprint-prefix (namespace)
           (princ (namespace-prefix namespace) stream)
           (write-char xml-prefix-separator stream)))
    (multiple-value-bind (namespace name)
        (get-namespace object)
      (when (and namespace (qualifiedp namespace))
        (if (and at-sign-p *expand-attribute-value*)
            (princ (namespace-uri-variant namespace) stream)
          (pprint-prefix namespace)))
      (if (or colon-p at-sign-p *expand-attribute-value*)
          (princ (get-xml-name name (keywordp object)) stream)
        
        ;; Ensure, unless RDF, that first character is downcase.
        (pprint-subst stream (string (get-xml-name name (keywordp object))))))))

(defun get-xml-global-element-name (symbol &aux (namespace (get-namespace symbol)))
  (if (and (eq namespace *target-namespace*)
           (not (eq namespace *default-namespace*)))
      (let ((*qualified-local-elements* (not nil)))
        (format nil "~/rse::pprint-xml-name/" symbol))
    symbol))

(defun get-xml-unqualified-name (symbol)
  (format nil "~:/rse::pprint-subst/" symbol))

;;; as, with, adapted from: ANSI Common Lisp by Paul Graham, Prentice Hall, 1996.

(defparameter *xml-print-pretty* (not nil))

(defparameter *xml-pprint-indent* 2)

(defmacro xml-newline ()
  '(when *xml-print-pretty*
     (pprint-newline :mandatory)))

(defmacro xml-indent ()
  '(when *xml-print-pretty*
     (pprint-indent :block *xml-pprint-indent*)))

(defmacro xml-unindent ()
  '(when *xml-print-pretty*
     (pprint-indent :block 0)
     (pprint-newline :mandatory)))

(defmacro as* (tag options
               &optional form freshline &aux (form-supp (if form (not nil))))
  `(progn
     ,@(when freshline '((xml-newline)))
     (format t "<~/rse:pprint-xml-name/~
                ~{ ~:/rse:pprint-xml-name/=\"~@/rse:pprint-xml-name/\"~}~@[>~]"
       ,tag ,options ,form-supp)
     ,@(when form-supp `(,form))
     (format t "~:[/~;</~/rse:pprint-xml-name/~]>"
       ,form-supp ,tag)
     ,@(unless freshline '((xml-newline)))))

(defmacro as (tag-and-options &optional content (freshline (not nil)))
  (multiple-value-bind (tag options)
      (parse-tag tag-and-options)
    `(as* ,tag (list ,@options) ,(if content `(princ ,content)) ,freshline)))

(defmacro with* (tag options &body body)
  `(pprint-logical-block (nil nil)
     (format t "<~/rse:pprint-xml-name/~
                ~{ ~:/rse:pprint-xml-name/=\"~@/rse:pprint-xml-name/\"~^~:_~}>"
       ,tag ,options)
     (xml-indent)
     ,@body
     (xml-unindent)
     (format t "</~/rse:pprint-xml-name/>" ,tag)))

(defmacro with (tag-and-options &body body)
  (multiple-value-bind (tag options)
      (parse-tag tag-and-options)
    `(progn
       (xml-newline)
       (with* ,tag (list ,@options)
         ,@body))))

(defun unaffectedp (class slot-definition)
  (flet ((rules-affecting (subclass slot-name)
           (if (eq subclass class)
               (rules-affecting subclass slot-name)
             (rules-affecting-locally subclass slot-name))))
    (with-accessors ((slot-name slot-definition-name))
        slot-definition
      (map-objects class
                   #'class-direct-subclasses
                   #'(lambda (class)
                       (when (rules-affecting class slot-name)
                         (return-from unaffectedp nil)))))
  (not nil)))

(defmethod excluded-slot-p ((slot standard-effective-slot-definition))
  t)

(defmethod excluded-slot-p ((slot extended-slot-definition-mixin))
  (slot-definition-count slot))

(defun map-core-slots (class fn &key (direct nil))
  (unless (or direct (class-finalized-p class)) (finalize-inheritance class))
  (map nil
       #'(lambda (slot-definition &aux name counted-slot-definition)
           (unless (excluded-slot-p slot-definition)
             (setq name (slot-definition-name slot-definition)
                 counted-slot-definition
                   (block counted
                     (map-slots class
                                #'(lambda (slot-definition)
                                    (when (eq (slot-definition-count slot-definition)
                                              name)
                                      (return-from counted slot-definition))))))
             (funcall fn (or counted-slot-definition slot-definition)
                         (if counted-slot-definition slot-definition))))
       (if direct (class-direct-slots class) (class-slots class))))

(defun make-unique-name (symbol &optional (package *package*) (format-string "~A-~D"))
  (let ((suffix (get symbol 'counter 1)))
    (setf (get symbol 'counter) (1+ suffix))
    (intern (format nil format-string symbol suffix) package)))

(defparameter *unique-name-fn* #'make-unique-name)

(defmethod reconcile-slot-values
    (class object slot-definition counted-slot-definition value (e environment)
     &rest args)
  (multiple-value-bind (assumptions valid)
      (apply #'reconcile-slot-values class
                                     object
                                     slot-definition
                                     counted-slot-definition
                                     value
                                     (assumptions e)
                                     args)
    (values (uniquify-environment *atms* assumptions) valid)))

(defmethod reconcile-slot-values
    (class object slot-definition counted-slot-definition value (assumptions list)
     &key (no-check (not nil)) (no-count nil)
     &aux assumption
          (final-assumptions assumptions)
          (valid (not nil)))
  (macrolet ((slot-definition-typep (value slot-definition)
               `(or no-check
                    (slot-value-typep ,value (slot-definition-type ,slot-definition)))))
    (when no-count
      (setq valid (slot-definition-typep value slot-definition))
      (when valid
        (setq assumption (fetch-assumption object
                                           (slot-definition-name slot-definition)
                                           value))))
    (unless assumption
      (unless no-count
        (setq valid (slot-definition-typep value slot-definition)))
      (when valid
        (with-accessors ((counted-slot-name slot-definition-name)
                         (counted-slot-type slot-definition-type))
            counted-slot-definition
          (let* (instances name instance
                 (count 0))
            (dolist (node (slot-values object counted-slot-name t))
              (if no-count
                  (setq instances (nconc instances (elements node)))
                (when (< count value)
                  (let ((assumption (datum-assumption node)))
                    (when assumption
                      (pushnew assumption final-assumptions)))))
              (incf count))
            (when (and no-count (zerop value))
              (setq assumption (make-assumption *atms*))
              (add-slot-value-using-class class
                                          object
                                          slot-definition
                                          value
                                          (list assumption)
                                          :max-count))
            (dotimes (i (- value count))
              (setq name (funcall *unique-name-fn* counted-slot-type)
                  instance (apply #'make-instance
                                  counted-slot-type
                                  (if name (list :name name)))
                  assumption (make-assumption *atms*))
              (cond (no-count
                     (push instance instances)
                     (incf count)
                     (dolist (instance instances)
                       (add-slot-value-using-class class
                                                   object
                                                   counted-slot-definition
                                                   instance
                                                   (list assumption)
                                                   :premise
                                                   :no-count no-count))
                     (add-slot-value-using-class class
                                                 object
                                                 slot-definition
                                                 count
                                                 (list assumption)
                                                 :max-count))
                    (t
                     (add-slot-value-using-class class
                                                 object
                                                 counted-slot-definition
                                                 instance
                                                 (list assumption)
                                                 :premise)
                     (push assumption final-assumptions))))))))
  (when (and no-count valid)
    (pushnew assumption final-assumptions))
  (values final-assumptions valid)))

(defparameter *separate-definitions* (not nil))

(defmacro separate-definitions ()
  '(when *separate-definitions* (xml-newline)))

(defun serialize-class-hierarchy
    (root &optional (format :xml) (tangled nil) (derived nil))
  (flet ((serialize-class (class)
           (separate-definitions)
           (serialize-class class format (or derived (not (eq class root))))))
    (cond ((and (eq format :xml) (not tangled))
           (map-objects root
                        #'class-direct-subclasses
                        #'(lambda (class)
                            (unless (singletonp
                                     (class-direct-superclasses class))
                              (error "Class ~A has multiple superclasses."
                                (class-name class)))))
           (map-objects root
                        #'class-direct-subclasses
                        #'serialize-class))
          (t
           (let (classes)
             (map-objects root
                          #'class-direct-subclasses
                          #'(lambda (class)
                              (pushnew class classes :test #'eq)))
             (mapc #'serialize-class (nreverse classes)))))))

(defun xml-range-bounds (range)
  (let (min max)
    (setq min (range-min range)
          max (range-max range))
    (values (case min (-big 'unbounded) (t min))
            (case max (big 'unbounded) (t max)))))

(defun element-occurrence-bounds (count-slot-definition)
  (let (min max)
    (when count-slot-definition
      (multiple-value-setq (min max)
        (xml-range-bounds (range-elements (slot-definition-type
                                           count-slot-definition)))))
    (values (or min 1)
            (or max 1))))

(defun satisfy-occurrence-constraint
    (class object counted-slot-definition slot-definition environment &key no-count)
  (let ((bound (element-occurrence-bounds slot-definition)))
    
    ;; If initial value of an instance-counting slot
    ;; has a non-zero lower bound, ensure that there are
    ;; that number of instances. If the slot is absent,
    ;; the lower bound defaults to 1.
    (if (plusp bound)
        (let ((value bound))
          (when slot-definition
            (setq value (range-min
                         (slot-value-reduce object
                                            (slot-definition-name slot-definition)
                                            environment))))
          (if (< value bound)
              (reconcile-slot-values class
                                     object
                                     slot-definition
                                     counted-slot-definition
                                     value
                                     environment
                                     :no-count no-count)
            environment))
      environment)))

(defmethod serialize-slot-definition ((class extended-class)
                                      (slot slot-definition)
                                      count-slot
                                      (format (eql :xml))
                                      &aux complex name type-name)
  (with-accessors ((slot-name slot-definition-name)
                   (slot-type slot-definition-type))
      slot
    (setq complex (subtypep slot-type 'extended-object)
        name (if (and complex (eq slot-name slot-type))

                 ;; Ensure that first character is downcase.
                 (get-xml-unqualified-name slot-name)
                 slot-name)
        type-name (if complex
                      (ensure-xml-type-name slot-type)
                    slot-type))
    (if count-slot
        (let ((inner-name (if (eq slot-name slot-type)
                              name
                            (get-xml-unqualified-name slot-type)))
              min max)
          (multiple-value-setq (min max)
            (element-occurrence-bounds count-slot))
          (with (:element :name name)
            (with :complex-type
              (with :sequence
                (as (:element :name inner-name :type type-name
                              :min-occurs min :max-occurs max))))))
      (as (:element :name name :type type-name)))))

(defparameter *restricted-type-suffix* :restriction)

(defun ensure-cpl (class)
  (unless (class-finalized-p class) (finalize-inheritance class)))

(defun map-local-slots (function class superclass)
  (ensure-cpl class)
  (do ((classes (class-precedence-list class) (rest classes)))
      ((eq (first classes) superclass) nil)
    (map nil function (class-direct-slots (first classes)))))

(defun some-local-slot (predicate class superclass superclasses)
  (if (rest superclasses)
      (map-local-slots #'(lambda (slot-definition)
                           (when (funcall predicate slot-definition)
                             (return-from some-local-slot (not nil))))
                       class
                       superclass)
    (find-if predicate (class-direct-slots class))))

(defun restrictionp (slot-definition class superclass)
  (let ((name (slot-definition-name slot-definition)))
    (map-local-slots #'(lambda (slot-definition)
                         (when (eq name (slot-definition-name slot-definition))
                           (return-from restrictionp (not nil))))
                     class
                     superclass)))

(defun extensionp (slot-definition class)
  (null (find-slot-definition class (slot-definition-name slot-definition))))

(defun serialize-documentation (documentation)
  (when documentation
    (with :annotation
      (with :documentation
        (xml-newline)
        (princ documentation)))))

(defmethod serialize-class ((class extended-class)
                            (format (eql :xml))
                            &optional (derived (not nil))
                            &aux (superclasses (if derived
                                                   (class-direct-superclasses class)))
                                 (superclass (first (last superclasses)))
                                 (ssclasses (if derived
                                                (class-direct-superclasses superclass)))
                                 (ssclass (first (last ssclasses)))
                                 superclass-extended)
  (flet ((some-local-slot (predicate)
           (some-local-slot predicate class superclass superclasses))
         (restrictionp (slot-definition)
           (and (restrictionp slot-definition superclass ssclass)
                (or (not superclass-extended)
                    
                    ;; Possible restriction plus extension.
                    (extensionp slot-definition ssclass))))
         (extensionp (slot-definition)
           (extensionp slot-definition superclass))
         (superclass-extended-p ()
           (some-local-slot #'(lambda (slot-definition)
                                (extensionp slot-definition ssclass))
                            superclass
                            ssclass
                            ssclasses)))
    (let ((class-name (class-name class))
          (restricted nil)
          (extended nil)
          superclass-name
          restricted-type-name)
      (when superclass
        (setq superclass-extended (superclass-extended-p)
            restricted (some-local-slot #'restrictionp)
            superclass-name (class-name superclass)))
      (when restricted
        (setq extended (some-local-slot #'extensionp)
            restricted-type-name (ensure-xml-type-name
                                  (if extended
                                      (add-lisp-name-suffix class-name
                                                            *restricted-type-suffix*)
                                    class-name)))
        (with (:complex-type :name restricted-type-name)
          (serialize-documentation (documentation class t))
          (with :complex-content
            (with (:restriction :base (ensure-xml-type-name superclass-name))
              (with :sequence

                ;; Repeat all base type elements.
                (map-core-slots class
                                #'(lambda (slot count-slot)
                                    (when (restrictionp slot)
                                      (serialize-slot-definition class
                                                                 slot
                                                                 count-slot
                                                                 format))))))))
        (when extended (separate-definitions)))
      (unless (and restricted (not extended))
        (with (:complex-type :name (ensure-xml-type-name class-name))
          (serialize-documentation (documentation class t))
          (if superclass  
              (with :complex-content
                (with (:extension :base (if restricted
                                            restricted-type-name
                                          (ensure-xml-type-name superclass-name)))
                  (with :sequence
                                      
                    ;; Exclude base type elements and their restrictions, but
                    ;; incorporate elements derived from other superclasses,
                    ;; if any.
                    (map-core-slots class
                                    #'(lambda (slot count-slot)
                                        (when (extensionp slot)
                                          (serialize-slot-definition class
                                                                     slot
                                                                     count-slot
                                                                     format)))))))
            (with :sequence
              (map-core-slots class
                              #'(lambda (slot count-slot)
                                  (serialize-slot-definition class
                                                             slot
                                                             count-slot
                                                             format))
                              :direct (not nil)))))))))

(defmethod serialize-class ((class range-class)
                            (format (eql :xml))
                            &optional derived
                            &aux (range (elements class)))
  (declare (ignore derived))
  (flet ((with-atomic-type (&key name)
           (let* ((superclass-name (class-name
                                    (first
                                     (class-direct-superclasses class))))
                  (base (case superclass-name
                          (numeric-range :integer)
                          (symbolic-range :string)
                          (t superclass-name))))
             (xml-newline)
             (with* :simple-type (if name (list :name name))
               (serialize-documentation (documentation class t))
               (with (:restriction :base base)
                 (if (subtypep class 'numeric-range)
                     (multiple-value-bind (min max)
                         (xml-range-bounds range)
                       (as (:min-inclusive :value min))
                       (as (:max-inclusive :value max)))
                   (dolist (element range)
                     (as (:enumeration :value element)))))))))
    (if *use-list-simple-types*
        (with (:simple-type :name (class-name class))
          (with :list
            (with-atomic-type)))
      (with-atomic-type :name (class-name class)))))

(defmethod serialize-sequence ((instances cons)
                               (format (eql :xml))
                               (e environment)
                               tag
                               slot-type)
  (with tag
    (revdolist (instance instances)
      (serialize-object instance format e slot-type slot-type nil))))

(defmethod serialize-sequence ((instances null)
                               (format (eql :xml))
                               (e environment)
                               tag
                               slot-type)
  (serialize-object instances format e tag slot-type))

(defmethod range-to-content (value slot-type datatype)
  (declare (ignore datatype))
  (cond ((and (subtypep slot-type 'numeric-range)
              (eql (range-min value) (range-max value)))
         (range-min value))
        ((singletonp value)
         (first value))
        (*use-list-simple-types* value)))

(defun slot-value-to-content (value slot-type)
  (if (subtypep slot-type 'extended-object)
      (first value)
    (range-to-content value slot-type (range-external-type slot-type))))

(defmethod serialize-value ((value cons) format (e environment) tag slot-type)
  (serialize-object (slot-value-to-content value slot-type)
                    format
                    e
                    tag
                    slot-type
                    nil))

(defmethod serialize-slot ((instance extended-object)
                           (slot slot-definition)
                           (format (eql :xml))
                           (e environment)
                           &aux value)
  (with-accessors ((slot-name slot-definition-name)
                   (slot-type slot-definition-type)
                   (slot-count slot-definition-count))
      slot
    (setq value (slot-value-reduce instance slot-name e))
    (if (or slot-count
            (and (subtypep slot-type 'extended-object) (not (singletonp value))))
        (serialize-sequence value format e slot-name slot-type)
      (serialize-value value format e slot-name slot-type))))

(defmethod serialize-object ((instance extended-object)
                             (format (eql :xml))
                             (e environment)
                             &optional tag type (global (not nil))
                             &aux (class (class-of instance))
                                  (class-name (class-name class))
                                  (name (or tag class-name))
                                  (instance-name (instance-name instance)))
  (flet ((serialize-slot (slot count-slot)
           (when (or count-slot
                     (subtypep (slot-definition-type slot) 'extended-object))
             (setq e (satisfy-occurrence-constraint class
                                                    instance
                                                    slot
                                                    count-slot
                                                    e)))
           (serialize-slot instance slot format e)))
    (when global
      (setq name (get-xml-global-element-name name)))
    (unless global (xml-newline))
    (with* name
           (nconc (if global (namespace-declarations))
                  (if instance-name (list *xml-id-attribute* instance-name))
                  (if (and type (not (eq class-name type)))
                      
                      ;; Must identify the derived type.
                      (list :type (ensure-xml-type-name class-name))))
      (map-core-slots class #'serialize-slot))))

(defmethod format-as-type (object datatype)
  (declare (ignore datatype))
  (get-xml-name object))

(defmethod print-as-type (object datatype)
  (princ (format-as-type object datatype)))

(defun serialize-simple-list (list datatype)
  (mapl #'(lambda (elements)
            (print-as-type (first elements) datatype)
            (when (rest elements) (princ #\space)))
    list))

(defmethod print-as-type ((object cons) datatype)
  (serialize-simple-list object datatype))

(defun serialize-simple-object (object tag &optional options (datatype t))
  (as* tag options (print-as-type object datatype) 'freshline))

(defmethod serialize-object ((object t)
                             (format (eql :xml))
                             (e environment)
                             &optional tag type global)
  (declare (ignore global))
  (serialize-simple-object object tag () (range-external-type type)))

(defmethod serialize-object ((object null)
                             (format (eql :xml))
                             (e environment)
                             &optional tag type global)
  (declare (ignore type global))
  (as (tag nil 'true)))

(defmethod serialize-within-rule ((object t)
                                  (format (eql :xml))
                                  &optional (tag (if (operatorp object)
                                                     :operator
                                                   :constant)))
  (as tag (get-xml-name object)))

(defmethod serialize-within-rule ((object cons)
                                  (format (eql :xml))
                                  &optional tag
                                  &aux (elements object))
  (typecase object
    (attribute-reference (serialize-attribute-reference object tag))
    (variable (serialize-variable object))
    (t
     (unless tag
       (setq tag (if (operatorp (first elements))
                     (get-xml-global-element-name :arithmetic-expr)
                   (pop elements))))
     (if (unary-minus-p elements)
         (with (tag :minus 'true)
           (serialize-within-rule (second elements) format))
       (with tag
         (dolist (element elements)
           (serialize-within-rule element format)))))))

(defun serialize-variable (variable
                           &optional (tag (get-xml-global-element-name :variable)))
  (as (tag :name (variable-name variable)
           :type (ensure-xml-type-name (variable-class-name variable)))))

(defun serialize-attribute-reference (attribute-reference &optional tag)
  (unless tag
    (setq tag (get-xml-global-element-name :attribute-reference)))
  (with (tag :name (attribute-name attribute-reference))
    (serialize-variable (attribute-reference-variable attribute-reference))))

(defmethod serialize-within-rule :around ((object proposition)
                                          (format (eql :xml))
                                          &optional (tag (get-xml-global-element-name
                                                          :proposition)))
  (flet ((head-attribute-reference (proposition)
           (first (last (attribute-references proposition)))))
    (with (tag :type (class-name (class-of object)))
      (serialize-attribute-reference (head-attribute-reference object))
      (call-next-method))))

(defun serialize-relation (numeric-relation format)
  (serialize-within-rule (case numeric-relation
                           (< "&lt;")
                           (> "&gt;")
                           (>= "&gt;=")
                           (<= "&lt;=")
                           (t numeric-relation))
                         format
                         (get-xml-global-element-name :relation)))

(defun serialize-rhs (proposition expr format)
  (if (numberp expr)
      (serialize-simple-object expr :value () (proposition-attribute-datatype proposition))
    (serialize-within-rule expr format (get-xml-global-element-name :arithmetic-expr))))

(defmethod serialize-within-rule ((object arithmetic-proposition)
                                  (format (eql :xml))
                                  &optional tag)
  (declare (ignore tag))
  (serialize-relation (relation object) format)
  (serialize-rhs object (prefix-rhs object) format))

(defmethod serialize-within-rule ((object functional-proposition)
                                  (format (eql :xml))
                                  &optional tag)
  (declare (ignore tag))
  (serialize-relation (relation object) format)
  (with-slots (function-name arguments)
      object
    (cond ((aggregate-function-name-p function-name)
           (serialize-within-rule function-name format :aggregate-function-name)
           (serialize-within-rule (first arguments)
                                  format
                                  :relational-attribute-reference)
           (serialize-within-rule (second arguments)
                                  format
                                  :numeric-attribute-reference))
          (t
           (serialize-within-rule function-name format :function-name)
           (serialize-within-rule arguments format :arguments)))))

(defmethod serialize-within-rule ((object lisp-proposition)
                                  (format (eql :xml))
                                  &optional tag)
  (declare (ignore tag))
  (serialize-within-rule (function-name object) format :function-name)
  (serialize-within-rule (arguments object) format :arguments))

(defmethod serialize-within-rule ((object literal-proposition)
                                  (format (eql :xml))
                                  &optional tag)
  (declare (ignore tag))
  (if (slot-boundp object 'value)
      (serialize-simple-object (value object) :value)
    (serialize-attribute-reference (car (attribute-references object))
                                   :value-attribute-reference)))

(defmethod serialize-within-rule ((object numeric-proposition)
                                  (format (eql :xml))
                                  &optional tag)
  (declare (ignore tag))
  (serialize-simple-object (value object)
                           :value
                           ()
                           (proposition-attribute-datatype object)))

(defmethod serialize-within-rule ((object relational-proposition)
                                  (format (eql :xml))
                                  &optional tag)
  (declare (ignore tag))
  (serialize-variable (proposition-specializer object) :specializer))

(defun serialize-rule-label (instance &aux tag)
  (setq tag (get-xml-global-element-name :rule-label))
  (as (tag
       :name (instance-name instance)
       :assume (if (datum-assumption (instance-node instance))
                   'true
                 'false))))

(defun serialize-comment (instance)
  (let ((documentation (documentation instance t))
        tag)
    (when documentation
      (setq tag (get-xml-global-element-name :comment))
      (as tag documentation))))

(defmethod serialize-rule :around ((instance well-formed-formula)
                                   (format (eql :xml)))
  (if (source-form instance t)
      (call-next-method)
    (error "Source of rule ~A is missing." (instance-name instance))))

(defmacro parse-without-rewriting (instance)
  `(let ((*rewrite-in-parser* nil))
    (parse ,instance)))

(defmethod serialize-rule ((instance forward-rule)
                           (format (eql :xml)))
  (let (body neck head tag)
    (multiple-value-setq (body neck head) (parse-without-rewriting instance))
    (setq tag (get-xml-global-element-name (if (eq neck biconditional-token)
                                               :iff
                                             :if)))
    (with tag
      (serialize-rule-label instance)
      (serialize-comment instance)
      (with :head
        (serialize-within-rule head format))
      (when body
        (with :body
          (serialize-within-rule body format))))))

(defmethod serialize-rule ((instance constraint)
                           (format (eql :xml))
                           &aux (tag (get-xml-global-element-name :formula)))
  (with tag
    (serialize-rule-label instance)
    (serialize-comment instance)
    (serialize-within-rule (parse-without-rewriting instance) format)))

(defmethod serialize-object ((instance well-formed-formula)
                             (format (eql :xml))
                             (e environment)
                             &optional tag type global)
  (declare (ignore tag type global))
  (serialize-rule instance format))

(defun make-namespace-attribute-name (namespace)
  (declare (type symbol namespace))
  (let ((default-attribute-name "xmlns"))
    (if (eq namespace *default-namespace*)
        default-attribute-name
      (concatenate 'string default-attribute-name
                           (string xml-prefix-separator)
                           (namespace-prefix namespace)))))

(defun namespace-declarations ()
  (mapcan #'(lambda (namespace)
              (list (make-namespace-attribute-name namespace)
                    (if *expand-attribute-value*
                        (namespace-uri-variant namespace)
                      (namespace-uri namespace))))
    *namespaces*))

(defun serialize-rules (rules &optional (format :xml) comment &aux tag comment-tag)
  (setq tag (get-xml-global-element-name :rule-set))
  (with* tag
         (namespace-declarations)
    (when comment
      (setq comment-tag (get-xml-global-element-name :comment))
      (as comment-tag comment))
    (dolist (rule rules)
      (separate-definitions)
      (serialize-rule (if (symbolp rule)
                          (find-instance rule)
                        rule)
                      format))))

(defmacro as-top-level-element (name &optional (type name))
  (let (xml-name)
    (setq xml-name (if (eq name type)
                       
                       ;; Ensure that first character is downcase.
                       (get-xml-unqualified-name name)
                     name))
    `(as (:element :name ',xml-name :type (ensure-xml-type-name ',type)))))

(defmacro with-namespaces ((&key (target-namespace nil target-supp)
                                 (namespaces nil namespaces-supp)
                                 (default-namespace nil default-supp))
                           &body body)
  `(let* (,@(if target-supp
                `((*target-namespace* ,target-namespace)))
          ,@(if default-supp
                `((*default-namespace* ,default-namespace)))
          ,@(if (or namespaces-supp target-supp)
                `((*namespaces* (if *target-namespace*
                                    (adjoin *target-namespace*
                                            ,(if namespaces-supp
                                                 namespaces
                                               '*namespaces*)
                                            :test #'eq)
                                  ,namespaces)))))
     ,@body))

(defmacro with-schema ((&key (target-namespace :xsd target-supp)
                             (namespaces nil)
                             (default-namespace nil)
                             (documentation nil)
                             (documentation-lang :en))
                       &body body)
  `(with-namespaces (:target-namespace ,target-namespace
                     :namespaces ,namespaces
                     :default-namespace ,default-namespace)
     (let (,@(if (not target-supp)
                 '((*qualified-local-elements* (not nil)))))
       (with* :schema (nconc ,(if target-supp
                                  '(list :target-namespace
                                         (namespace-uri *target-namespace*)))
                             (namespace-declarations)
                             (list "xml:lang" ,documentation-lang))
         ,@(if documentation `((serialize-documentation ,documentation)))
         ,@body))))

(defmacro with-xml ((&key (version "1.0")
                          (target-namespace nil target-supp)
                          (namespaces nil namespaces-supp)
                          (default-namespace nil default-supp))
                    &body body)
  `(with-namespaces (,@(if target-supp `(:target-namespace ,target-namespace))
                     ,@(if namespaces-supp `(:namespaces ,namespaces))
                     ,@(if default-supp `(:default-namespace ,default-namespace)))
     (format t "<?xml version=\"~A\"?>~%" ,version)
     ,@body))

(defmacro redirect-to-stream (stream &body body)
  `(let ((*standard-output* ,stream))
     ,@body))