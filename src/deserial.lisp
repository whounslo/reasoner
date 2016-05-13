;;; Copyright (C) 2011-2014, 2016 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; XML deserialization

(in-package :reasoner-ext)

(eval-when (:execute :compile-toplevel :load-toplevel)
  (shadowing-import 'rs::variable)
  (import '(atms:singletonp
            rs::revdolist rs::class-direct-superclasses
            rs::ensure-class rs::ensure-class-using-class
            rs::slot-definition rs::slot-definition-name
            rs::slot-definition-type rs::slot-definition-count
            rs::ensure-range-class rs::ensure-range-class-using-class
            rs::make-numeric-range rs::numeric-subrangep
            rs::range-external-type rs::find-slot-definition
            rs::forward-rule rs::constraint rs::proposition
            rs::arithmetic-proposition rs::functional-proposition
            rs::lisp-proposition rs::literal-proposition
            rs::numeric-proposition rs::relational-proposition
            rs::attribute-reference rs::attribute-references
            rs::make-attribute-reference rs::make-variable
            rs::variable-name rs::variable-class-name
            rs::collect-rhs-attribute-references
            rs::attribute-reference-class
            rs::relation rs::function-name
            rs::prefix-rhs rs::arguments rs::value rs::specializer
            rs::implication-token rs::biconditional-token))
  (export '(defnamespace make-namespace ensure-namespace-package
            namespace-package namespace-uri find-uri-namespace
            *namespace-package-prefix* *namespaces* *namespace-names*
            *count-slot-suffix* *count-type-suffix* *xml-id-attribute*
            find-prefix-namespace parse-qualified-name
            find-xml-name intern-xml-name parse-as-type
            into-xml-element store-xml-content outof-xml-element pop-elements
            define-ignored-elements *ignored-elements*
            *count-subelements* count-subelements-p
            *assumptions* *assumption*
            deserialize-as-objects deserialize-as-object
            )))

;(define-modify-macro push-on-end (object) 
;  (lambda (place object)
;    (nconc place (list object))))

(defmacro push-on-end (place object)
  `(setf ,place
     (nconc ,place (list ,object))))

(defun map-objects (object paths-fn before-fn &optional after-fn)
  (funcall before-fn object)
  (dolist (object (funcall paths-fn object))
    (map-objects object paths-fn before-fn after-fn))
  (when after-fn
    (funcall after-fn object)))

(defparameter *count-subelements* (not nil))

(defmethod count-subelements-p (object slot-name)
  (declare (ignore object slot-name))
  *count-subelements*)

(defun write-slot-value (object slot-name value &rest args)
  (let* ((class (class-of object))
         (slot-definition (find-slot-definition class slot-name)))
    (apply #'write-slot-value-using-class class
                                          object
                                          slot-definition
                                          value
                                          :premise
                                          :slot-name slot-name
                                          args)))

(defmethod write-slot-value-using-class
           (class object (slot null) value informant &key slot-name (no-error nil))
  (cond (no-error nil)
        ((slot-definition-missing class
                                  object
                                  slot-name
                                  'write-slot-value
                                  value
                                  ()
                                  informant))
        (t (call-next-method))))

(defmethod write-slot-value-using-class (class object slot value informant
                                         &key (slot-name (slot-definition-name slot))
                                              (no-check nil no-check-supp)
                                              (no-error nil)
                                              assumption)
  (cond ((or no-check
             (slot-value-typep value (slot-definition-type slot)))
         (or (fetch-assumption object slot-name value)
             (let ((assumption (or assumption (make-assumption *atms*))))
               (add-slot-value-using-class class
                                           object
                                           slot
                                           value
                                           (list assumption)
                                           informant
                                           :no-check (if no-check-supp
                                                         no-check
                                                       (not nil))
                                           :no-count (not
                                                      (count-subelements-p object
                                                                           slot-name)))
               assumption)))
        (no-error nil)
        (t (error "Slot value ~A is not of type ~A."
             value
             (slot-definition-type slot)))))

;;; XML namespaces

(defnamespace :xml "http://www.w3.org/XML/1998/namespace" lang)

(defnamespace :xmlns "http://www.w3.org/2000/xmlns/")

(defnamespace :xsd "http://www.w3.org/2001/XMLSchema"
  schema annotation #:documentation element name ref #:type
  complex-type #:sequence choice all min-occurs max-occurs unbounded
  complex-content extension restriction base
  simple-type min-inclusive max-inclusive value enumeration
  #:boolean #:integer #:string #:list
  non-negative-integer positive-integer date-time #:time date
  g-year-month g-year g-month-day g-day g-month duration)

(defnamespace :xsi "http://www.w3.org/2001/XMLSchema-instance"
  #:type #:nil)

(eval-when (:execute :compile-toplevel :load-toplevel)
  (ensure-xml-type-name '(arithmetic-proposition functional-proposition
                          lisp-proposition literal-proposition
                          numeric-proposition relational-proposition
                          compound-object assembly part component)))

(defnamespace :rs "http://reasoner.sourceforge.net/reasoner"
  
  ;; Rule language.
  rule-set #:if iff formula rule-label name assume #:comment head body
  if-and-only-if implies #:or #:and #:not
  proposition arithmetic-proposition functional-proposition
  lisp-proposition literal-proposition numeric-proposition
  relational-proposition
  variable attribute-reference name ref #:type
  value value-attribute-reference #:specializer
  relation arithmetic-expr operator constant minus
  function-name arguments aggregate-function-name
  relational-attribute-reference numeric-attribute-reference
  
  ;; Predefined ranges.
  numeric-range symbolic-range true-or-false true false
  
  ;; Composite objects.
  compound-object assembly part component parts)

(defparameter *namespaces* nil)

(defparameter *target-namespace* nil)

(defparameter *default-namespace* nil)

(defconstant xml-prefix-separator #\:)

(defconstant xml-fragment-separator #\#)

(defparameter *xml-id-attribute* :name)

#-sbcl
(defconstant whitespace '(#\Space #\Tab #\Newline))
#+sbcl
(defparameter whitespace '(#\Space #\Tab #\Newline))

;;; XML parser interface

(defun parse-tag (tag-and-options)
  (let* ((options (if (consp tag-and-options)
                      (cdr tag-and-options)))
         (tag (if options
                  (car tag-and-options)
                tag-and-options)))
    (values tag options)))

(defun namespace-uri-variant (name)
  (declare (type symbol name))
  (or (get name 'rdf-uri)
      (let ((uri (namespace-uri name)))
        (if uri (setf (get name 'rdf-uri) (format nil "~A~C"
                                                      uri xml-fragment-separator))))))

(defmacro find-namespace (namespace namespaces errorp &rest args)
  `(cond ((find ,namespace ,namespaces ,@args))
         (,errorp (error "Namespace not found: ~S." ,namespace))))

(defun find-uri-namespace (uri &optional (namespaces *namespaces*) (errorp t))
  (declare (type string uri))
  (when (zerop (length uri)) (return-from find-uri-namespace nil))
  (find-namespace uri namespaces errorp
                  :test #'string=
                  :key (if (eq (char uri (1- (length uri)))
                               xml-fragment-separator)
                           #'namespace-uri-variant
                         #'namespace-uri)))

(defun find-prefix-namespace (prefix &optional (errorp t))
  (declare (type string prefix))
  (find-namespace prefix *namespace-names* errorp
                  :test #'string= :key #'namespace-prefix))

(defun parse-qualified-name (name)
  (declare (type string name))
  (let* ((split (position-if #'(lambda (ch)
                                 (or (eq ch xml-prefix-separator)
                                     (eq ch xml-fragment-separator)))
                             name
                             :from-end (not nil)))
         (prefix (if (and split (plusp split)) (subseq name 0 split)))
         (separator (if split (char name split))))
    (values (if split (subseq name (1+ split)) name)
            (cond ((null separator) *default-namespace*)
                  ((eq separator xml-prefix-separator)
                   (find-prefix-namespace prefix))
                  (prefix (find-uri-namespace prefix *namespace-names*))
                                               ; PREFIX is a uri.
                  (t *target-namespace*)))))

(defmethod find-xml-name ((name string) (namespace symbol) &optional (errorp t))
  (declare (ignore errorp))
  (find-symbol name (ensure-namespace-package namespace)))

(defun find-xml-name-using-known-namespaces (name)
  (dolist (ns *namespaces*)
    (let ((symbol (find-xml-name name ns nil)))
      (when symbol (return symbol)))))

(defun find-xml-name-using-used-packages (name)
  (dolist (package (package-use-list *package*))
    (unless (eq package #.(find-package "COMMON-LISP"))
      (let ((symbol (find-symbol name package))
            lisp-name)
        (when symbol
          (setq lisp-name (get-lisp-name symbol))
          (when (eq (find-symbol (string lisp-name)) lisp-name)
            (return symbol)))))))

(defmethod find-xml-name ((name string) (namespace null) &optional (errorp t))
  (declare (ignore errorp))
  (or (find-xml-name-using-known-namespaces name)
      (find-symbol name)
      (find-xml-name-using-used-packages name)))

(defmethod find-xml-name :around ((name string) (namespace symbol) &optional (errorp t))
  (cond ((call-next-method))
        (errorp (error "Name not found~@[ in namespace ~S~]: ~S."
                       (namespace-prefix namespace) name))))

(defmethod find-xml-name ((name string) (uri string) &optional (errorp t))
  (find-xml-name name (find-uri-namespace uri) errorp))

(defmethod intern-xml-name ((name string) (namespace symbol))
  (intern name (ensure-namespace-package namespace)))

(defmethod intern-xml-name ((name string) (uri string))
  (intern-xml-name name (find-uri-namespace uri)))

(defmethod intern-xml-name ((name string) (namespace null))
  (or (find-xml-name-using-known-namespaces name)
      (intern name)))

(defvar *ignored-elements* nil)

(defmacro define-ignored-elements (namespace-name &body body)
  `(dolist (name ',body)
     (pushnew (intern-xml-name (string name) ,namespace-name) *ignored-elements*
              :test #'eq)))

(defun ignore-element-p (tag)
  (find tag *ignored-elements* :test #'eq :key #'get-lisp-name))

(defun whitespacep (ch)
  (or (not (graphic-char-p ch))
      (eq ch #\space)))

(defun find-token (string start end &optional (predicate #'whitespacep))
  (let* ((start (max (or (position-if (complement predicate) string :start start)
                         start)
                     start))
         (end (min (or (position-if predicate string :start start)
                       end)
                   end)))
    (values start end)))

(defmethod parse-as-type ((object string) datatype start end)
  (declare (ignore datatype))
  (or (parse-integer object :start start :end end :junk-allowed (not nil))
      (get-content-lisp-name (intern-xml-name (subseq object start end) nil))))

(defmethod parse-as-type ((object string) (datatype (eql t)) start end)
  (declare (ignorable start end))
  (call-next-method))

(defmethod parse-content ((content string) datatype)
  (do ((bound (length content))
       (object nil)
       (last-object nil object)
       (objects ())
       (start 0 end)
       end)
      ((eql start bound) (if objects
                             (push-on-end objects object)
                           object))
    (multiple-value-setq (start end) (find-token content start bound))
    (setq object (parse-as-type content datatype start end))
    (when last-object
      (push-on-end objects last-object))))

(defmethod parse-content ((object string) (datatype (eql 'number)))
  (or (parse-integer object :junk-allowed (not nil))
      object))

(defmethod parse-content ((content string) (datatype (eql 'xmlxsd::string)))
  (string-trim whitespace content))

(defmethod parse-content ((content string) (datatype null))

  ;; Defer parsing.
  content)

(defvar *element-default-attribute-fn* (constantly nil))

(defstruct element tag attribute-fn content)

(defun element-attribute (element name &optional namespace default)
  (let ((value (or (funcall (element-attribute-fn element)
                            (string (get-xml-name name 'mandatory))
                            namespace)
                   default)))
    (cond ((null value) value)
          ((parse-integer value :junk-allowed (not nil)))
          (t
           (multiple-value-bind (name namespace)
               (parse-qualified-name value)
             (get-content-lisp-name (intern-xml-name name namespace)))))))

(defparameter *assumptions* nil)

(defparameter *assumption* nil)

(defmethod get-tag-slot-name (name)
  (get-tag-lisp-name name))

(defmethod get-tag-slot-name ((name (eql 'parts)))
  name)

(defun default-element-type (tag object)
  (let ((slot (find-slot-definition (class-of object) (get-tag-slot-name tag))))
    (values (if slot (slot-definition-type slot))
            (if slot (slot-definition-count slot)))))

(defmethod find-element-type (tag object)
  (declare (ignore tag object))
  nil)

(defmethod find-element-type (tag (object extended-object))
  (default-element-type tag object))

(defmethod find-superelement-type (element (superelement null))
  (declare (ignore element))
  nil)

(defmethod find-superelement-type (element superelement)
  (find-element-type (element-tag element) (element-content superelement)))

(defmethod find-element-object (tag element superelements)
  (let ((type (or (element-attribute element 'xmlxsi::type :xsi)
                  (multiple-value-bind (type count)
                      (find-element-type tag (element-content (first superelements)))
                    (if (null count) type))
                  (find-superelement-type (first superelements)
                                          (second superelements)))))
    (if (and type (subtypep type 'extended-object))
        (ensure-named-instance (element-attribute element *xml-id-attribute*)
                               :class type))))

(defmethod find-element-object (tag element (superelements null))
  (ensure-named-instance (element-attribute element *xml-id-attribute*)
                         :class (or (element-attribute element 'xmlxsi::type :xsi)
                                    (let ((name (get-tag-lisp-name tag)))
                                      (or (get name :xml-type) name)))))

(defmethod finalize-content (element tag content)
  (declare (ignore element tag content))
  )

(defmethod finalize-content (element tag (content string))
  (declare (ignore tag))
  (setf (element-content element) (parse-content content (ensure-lisp-name
                                                          (element-attribute element
                                                                             'datatype
                                                                             :rdf)))))

(defmethod assimilate-content (element element-content subelement tag content)
  (declare (ignore element-content subelement tag))
  
  ;;; Default behaviour: propagate content up a level.
  (when content
    (setf (element-content element) content)))

(defmethod assimilate-content (element (element-content cons) subelement tag content)
  (declare (ignore subelement tag))
  (push-on-end (element-content element) content))

(defmethod capture-assumption (assumption)
  (pushnew assumption *assumptions*))

(defmethod assimilate-content
           (element (element-content extended-object) subelement tag content)
  (declare (ignore element subelement))
  (when content
    (capture-assumption (write-slot-value element-content
                                          (get-tag-slot-name tag)
                                          content
                                          :assumption *assumption*))))

(defmethod find-datatype (type)
  (range-external-type type))

(defmethod find-datatype ((type (eql 'xmlxsd::string)))
  type)

(defmethod assimilate-content (element (element-content extended-object)
                               subelement tag (content string))
  (call-next-method element
                    element-content
                    subelement
                    tag
                    (parse-content content
                                   (find-datatype
                                    (or (find-element-type tag element-content)
                                        (error "Cannot determine content type of subelement \"~A\"."
                                          (get-xml-name tag)))))))

(defmethod assimilate-content (element (element-content extended-object)
                               subelement tag (content cons))
  (if (every #'(lambda (object) (typep object 'extended-object)) content)
      (dolist (value content)
        (assimilate-content element
                            element-content
                            subelement
                            tag
                            value))
    (call-next-method)))

(defmethod assimilate-content (element (element-content extended-object)
                               subelement tag (content extended-object))
  (declare (ignore subelement))
  (if (slot-exists-p element-content (get-tag-slot-name tag))
      (call-next-method)
    
    ;; A single object was created from a slot's type because
    ;; it had no :count option - overwrite it.
    (setf (element-content element) (list content))))

(defmethod assimilate-content (element (element-content list)
                               subelement tag (content extended-object))
  (declare (ignore subelement tag))
  (push-on-end (element-content element) content))

;;; Rule ML

(define-xml-name "implies" implication-token :rs)
(define-xml-name "ifAndOnlyIf" biconditional-token :rs)

(defvar *declarations* nil "List of variable declarations; reset when a rule is encountered.")

(defmethod find-element-object ((tag (eql 'rule-set)) element superelements)
  (declare (ignore element superelements))
  (not nil))

(defmethod assimilate-content (element (element-content null)
                               subelement (tag (eql 'xmlrs::comment)) (content string))
  (declare (ignore subelement))
  (setf (element-content element) (list content)))

(defmethod find-element-object :after ((tag (eql 'rule-label)) element superelements)
  (declare (ignore element superelements))
  (setq *declarations* nil))

(defmethod assimilate-content
           (element element-content subelement (tag (eql 'rule-label)) content)
  (declare (ignore element-content content))
  (setf (element-attribute-fn element) (element-attribute-fn subelement)))

(defun finalize-rule (element tag content
                      &aux name qualifier comment instance)
  (flet ((finalize-rule-content (name tag qualifier comment head &optional body)
           (ensure-named-instance name
                                  :qualifier qualifier
                                  :documentation comment
                                  :body body
                                  :neck (ecase tag
                                          (formula)
                                          (xmlrs::if implication-token)
                                          (iff biconditional-token))
                                  :head head
                                  :class (if (eq tag 'formula)
                                             'constraint
                                           'forward-rule))))
    (setq name (element-attribute element 'name :rs)
      qualifier (if (eq (element-attribute element 'assume :rs)
                        'true)
                    :assume)
      comment (if (stringp (first content)) (first content))
      instance (if (eq tag 'formula)
                   (finalize-rule-content name 
                                          tag
                                          qualifier
                                          comment
                                          nil
                                          (if comment (second content) content))
                 (apply #'finalize-rule-content name
                                                tag
                                                qualifier
                                                comment
                                                (if comment (rest content) content))))
    (when qualifier
      (capture-assumption (instance-assumption instance)))))

(defmethod assimilate-content
           (element element-content subelement (tag (eql 'xmlrs::if)) content)
  (declare (ignore element element-content))
  (finalize-rule subelement tag content))

(defmethod assimilate-content
           (element element-content subelement (tag (eql 'iff)) content)
  (declare (ignore element element-content))
  (finalize-rule subelement tag content))

(defmethod assimilate-content
           (element element-content subelement (tag (eql 'formula)) content)
  (declare (ignore element element-content))
  (finalize-rule subelement tag content))

(defmethod finalize-content (element (tag (eql 'xmlrs::comment)) (content string))

  ;; Preserve as string.
  (setf (element-content element) (string-trim whitespace content)))

(defmethod assimilate-content
           (element (element-content null) subelement (tag (eql 'head)) content)
  (declare (ignore subelement))
  (setf (element-content element) (list content)))

(defmethod find-element-object ((tag (eql biconditional-token)) element superelements)
  (declare (ignore element superelements))
  (list 'and))

(defmethod finalize-content (element (tag (eql biconditional-token)) (content cons))
  (declare (ignore element))
  
  ;; A <-> B is re-written as (A or not B) and (not A or B).
  (psetf (second content) `(or ,(second content) (not ,(third content)))
    (third content) `(or ,(third content) (not ,(second content)))))

(defmethod find-element-object ((tag (eql implication-token)) element superelements)
  (declare (ignore element superelements))
  (list 'or))

(defmethod finalize-content (element (tag (eql implication-token)) (content cons))
  (declare (ignore element))
  
  ;; A -> B is re-written as not A or B.
  (setf (second content) `(not ,(second content))))

(defmethod find-element-type (tag (object proposition))
  (declare (ignore tag))
  nil)

(defmethod find-element-object ((tag (eql 'proposition)) element superelements)
  (declare (ignore superelements))
  (make-instance (ensure-lisp-name (element-attribute element 'xmlrs::type :rs))))

(defmethod find-element-object ((tag (eql 'xmlrs::or)) element superelements)
  (declare (ignore element superelements))
  (list 'or))

(defmethod find-element-object ((tag (eql 'xmlrs::and)) element superelements)
  (declare (ignore element superelements))
  (list 'and))

(defmethod find-element-object ((tag (eql 'xmlrs::not)) element superelements)
  (declare (ignore element superelements))
  (list 'not))

(defmethod find-element-object ((tag (eql 'attribute-reference)) element superelements)
  (declare (ignore element superelements))
  (not ()))

(defmethod find-element-object
            ((tag (eql 'relational-attribute-reference)) element superelements)
  (declare (ignore element superelements))
  (not ()))

(defmethod find-element-object
            ((tag (eql 'numeric-attribute-reference)) element superelements)
  (declare (ignore element superelements))
  (not ()))

(defmethod find-element-object
            ((tag (eql 'value-attribute-reference)) element superelements)
  (declare (ignore element superelements))
  (not ()))

(defmethod find-element-object ((tag (eql 'arithmetic-expr)) element superelements)
  (declare (ignore element superelements))
  
  ;; An arithmetic expression may be a single attribute reference or number.
  (not ()))

(defmethod find-element-object ((tag (eql 'variable)) element superelements)
  (declare (ignore element superelements))
  nil)

(defmethod find-element-object ((tag (eql 'xmlrs::specializer)) element superelements)
  (declare (ignore element superelements))
  nil)

(defmethod assimilate-content (element (element-content proposition)
                               subelement tag content)
  (declare (ignore element subelement))
  (setf (slot-value element-content tag) content))

(defmethod assimilate-content (element (element-content literal-proposition)
                               subelement (tag (eql 'value)) content)
  (call-next-method element
                    element-content
                    subelement
                    tag
                    (let ((value (parse-content content t)))
                      (if (symbolp value) (list value) value))))

(defmethod assimilate-content (element (element-content relational-proposition)
                               subelement (tag (eql 'xmlrs::specializer)) content)
  (call-next-method element
                    element-content
                    subelement
                    'specializer
                    content))

(defmethod finalize-content (element (tag (eql 'relation)) (content string))
  (setf (element-content element) (parse-content content t)))

(defmethod finalize-content (element (tag (eql 'function-name)) (content string))
  (setf (element-content element) (parse-content content t)))

(defmethod finalize-content (element (tag (eql 'aggregate-function-name)) (content string))
  (setf (element-content element) (parse-content content t)))

(defmethod finalize-content (element (tag (eql 'constant)) (content string))
  (setf (element-content element) (parse-content content 'number)))

(defmethod assimilate-content (element (element-content functional-proposition)
                               subelement (tag (eql 'aggregate-function-name))
                               content)
  (call-next-method element
                    element-content
                    subelement
                    'function-name
                    content))

(defmethod assimilate-content (element (element-content arithmetic-proposition)
                               subelement (tag (eql 'arithmetic-expr)) content)
  (call-next-method element
                    element-content
                    subelement
                    'prefix-rhs
                    content))

(defmethod assimilate-content (element (element-content arithmetic-proposition)
                               subelement (tag (eql 'value)) content)
  (call-next-method element
                    element-content
                    subelement
                    'prefix-rhs
                    content))

(defmacro proposition-attribute-datatype (proposition)
  `(let* ((attribute-reference (first (attribute-references ,proposition)))
          (slot-definition (find-slot-definition (attribute-reference-class
                                                  attribute-reference)
                                                 (attribute-name attribute-reference))))
     (if slot-definition
         (range-external-type (slot-definition-type slot-definition)))))

(defun finalize-proposition-content (proposition slot-name)
  (let ((value (slot-value proposition slot-name)))
    (when (stringp value)
      (setf (slot-value proposition slot-name)
        (parse-content value (or (proposition-attribute-datatype proposition) t))))))

(defmethod finalize-content (element tag (content arithmetic-proposition))
  (declare (ignore element tag))
  (finalize-proposition-content content 'prefix-rhs))

(defmethod finalize-content (element tag (content numeric-proposition))
  (declare (ignore element tag))
  (finalize-proposition-content content 'value))

(defmethod assimilate-content (element element-content
                               subelement (tag (eql 'operator)) content)
  (call-next-method element
                    element-content
                    subelement
                    tag
                    (list (parse-content content t))))

(defmethod assimilate-content (element (element-content null)
                               subelement (tag (eql 'attribute-reference)) content)
  (call-next-method element
                    element-content
                    subelement
                    tag
                    (list content)))

(defmethod assimilate-content (element (element-content null)
                               subelement (tag (eql 'variable)) content)
  (call-next-method element
                    element-content
                    subelement
                    tag
                    (list content)))

(defmethod assimilate-content (element (element-content null)
                               subelement (tag (eql 'constant)) content)
  (call-next-method element
                    element-content
                    subelement
                    tag
                    (list content)))

(defun finalize-attribute-reference (element content)
  (setf (element-content element)
        (make-attribute-reference
         :attribute-name (element-attribute element 'name :rs)
         :attribute-reference-variable content)))

(defmethod finalize-content (element (tag (eql 'attribute-reference)) content)
  (finalize-attribute-reference element content))

(defmethod finalize-content (element (tag (eql 'value-attribute-reference)) content)
  (finalize-attribute-reference element content))

(defmethod finalize-content (element (tag (eql 'relational-attribute-reference)) content)
  (finalize-attribute-reference element content))

(defmethod finalize-content (element (tag (eql 'numeric-attribute-reference)) content)
  (finalize-attribute-reference element content))

(defmethod assimilate-content (element (element-content proposition)
                               subelement (tag (eql 'attribute-reference)) content)
  (declare (ignore element subelement))
  (push-on-end (slot-value element-content 'attribute-references) content))

(defmethod assimilate-content (element (element-content literal-proposition)
                               subelement (tag (eql 'value-attribute-reference))
                               content)
  (declare (ignore element subelement))
  (push content (slot-value element-content 'attribute-references)))

(defmethod assimilate-content (element (element-content functional-proposition)
                               subelement (tag (eql 'relational-attribute-reference))
                               content)
  (declare (ignore element subelement))
  (push content (slot-value element-content 'arguments)))

(defmethod assimilate-content (element (element-content functional-proposition)
                               subelement (tag (eql 'numeric-attribute-reference))
                               content)
  (declare (ignore element subelement))
  (push-on-end (slot-value element-content 'arguments) content))

(defmethod assimilate-content :after (element (element-content proposition)
                                      subelement (tag (eql 'arguments)) content)
  (declare (ignore element subelement))
  (collect-rhs-attribute-references element-content content))

(defun collect-attribute-reference-arguments (functional-proposition)
  (let ((arguments (slot-value functional-proposition 'arguments)))
    (when (cdr arguments)
      (collect-rhs-attribute-references functional-proposition arguments))))

(defmethod
    assimilate-content :after (element (element-content functional-proposition)
                               subelement (tag (eql 'relational-attribute-reference))
                               content)
  (declare (ignore element subelement content))
  (collect-attribute-reference-arguments element-content))

(defmethod
    assimilate-content :after (element (element-content functional-proposition)
                               subelement (tag (eql 'numeric-attribute-reference))
                               content)
  (declare (ignore element subelement content))
  (collect-attribute-reference-arguments element-content))

(defmethod finalize-content (element (tag (eql 'arithmetic-expr)) content)
  (when (typep content 'variable)
    (finalize-attribute-reference element content)))

(defmethod assimilate-content :around (element element-content
                                       subelement (tag (eql 'arithmetic-expr))
                                       content)
  (call-next-method element
                    element-content
                    subelement
                    tag
                    (if (eq (element-attribute subelement 'minus :rs) 'true)
                        (list '- content)
                      content)))

(defmethod assimilate-content :after (element (element-content arithmetic-proposition)
                                      subelement (tag (eql 'arithmetic-expr))
                                      content)
  (declare (ignore element subelement))
  (collect-rhs-attribute-references element-content content))

(defun finalize-variable (element)
  (let* ((variable-name (or (element-attribute element 'name :rs)
                            (element-attribute element 'ref :rs)))
         (variable (assoc variable-name *declarations* :test #'eq))
         (variable-class-name (variable-class-name variable)))
    (unless variable-class-name
      (setq variable-class-name (element-attribute element 'xmlrs::type :rs))
      (when variable
        
        ;; Forward reference.
        (setf (variable-class-name variable) variable-class-name)))
    (setf (element-content element)
      (or variable
          (car (push (make-variable :name variable-name :class-name variable-class-name)
                     *declarations*))))))

(defmethod finalize-content (element (tag (eql 'variable)) content)
  (declare (ignore content))
  (finalize-variable element))

(defmethod finalize-content (element (tag (eql 'xmlrs::specializer)) content)
  (declare (ignore content))
  (finalize-variable element))

;;; XML Schema

(setf (find-class 'xmlxsd::integer) (find-class 'numeric-range))
(setf (find-class 'non-negative-integer) (find-class 'zero-or-more))
(setf (find-class 'positive-integer) (find-class 'one-or-more))
(setf (find-class 'xmlxsd::boolean) (find-class 'true-or-false))
(deftype xmlxsd::string nil 'string)

(let (class-specifications)
  
  (defmethod find-element-object ((tag (eql 'schema)) element superelements)
    (declare (ignore element superelements))
    (setq class-specifications nil)
    nil)
  
  (defun add-class-specification (class-specification)
    (push class-specification class-specifications))
  
  (defun get-class-specifications ()
    class-specifications)
  
  ) ;end let class-specifications

(defmacro deferred-ensure-class-using-class (&rest args)
  `(add-class-specification (list ,@args)))

(defmethod find-element-object ((tag (eql 'simple-type)) element superelements)
  (declare (ignore element superelements))
  nil)

(defmethod find-element-object ((tag (eql 'complex-type)) element superelements)
  (declare (ignore element superelements))
  nil)

(defmethod find-element-object ((tag (eql 'complex-content)) element superelements)
  (declare (ignore element))
  (element-attribute (first superelements) 'name :xsd))

(defun retrieve-type (content)
  (typecase content
    (string nil)                               ; simpleType or complexType.
    (t content)                                ; null: simpleType or complexType.
    ))

(defun ensure-derived-type (element superelement)
  (let ((type (retrieve-type (element-content superelement))))
    (when type                                 ; complexContent, not simpleType?
      (ensure-class type
                    :direct-superclasses (list (ensure-lisp-name
                                                (element-attribute element 'base :xsd)))
                    :metaclass *default-metaclass*))))

(defmethod find-element-object ((tag (eql 'restriction)) element superelements)
  (ensure-derived-type element (first superelements)))

(defmethod find-element-object ((tag (eql 'extension)) element superelements)
  (ensure-derived-type element (first superelements)))

(defmethod find-element-object ((tag (eql 'xmlxsd::sequence)) element superelements)
  (declare (ignore element superelements))
  nil)

(defmethod find-element-object ((tag (eql 'element)) element superelements)
  (declare (ignore element superelements))
  nil)

(define-ignored-elements :xsd "appinfo")

(defmethod finalize-content (element (tag (eql 'xmlxsd::documentation)) (content string))

  ;; Preserve as string.
  (setf (element-content element) (string-trim whitespace content)))

(defmethod assimilate-content (element element-content
                               subelement (tag (eql 'complex-content)) content)
  (declare (ignore element element-content subelement content))

  ;; Don't overwrite documentation.
  )

(defmethod assimilate-content :around
           (element element-content subelement (tag (eql 'complex-type)) content)
  (declare (ignore element element-content))
  (let ((name (element-attribute subelement 'name :xsd)))
    (if name
        (ensure-class name
                      :documentation content
                      :metaclass *default-metaclass*)
      (call-next-method))))

#+allegro
(defmethod finalize-content (element (tag (eql 'xmlxsd::sequence)) (content string))

  ;; Empty sequence.
  (setf (element-content element) nil))

(defparameter *count-slot-suffix* :count)

(defparameter *count-type-suffix* :numbers)

(defun ensure-count-type (class-name slot-name numeric-range)
  (let ((count-type-name (if (symbolp numeric-range) numeric-range))
        count-type)
    (unless count-type-name
      (setq count-type-name (add-lisp-name-suffix class-name
                                                  slot-name
                                                  *count-type-suffix*)
          count-type (find-class count-type-name nil))
      
      ;; Define type.
      (if count-type
          (ensure-range-class-using-class count-type
                                          count-type-name
                                          :elements numeric-range)
        (let ((supertype-name (case (range-min numeric-range)
                                (0 (case (range-max numeric-range)
                                     (1 'zero-or-one)
                                     (big 'zero-or-more)))
                                (1 (case (range-max numeric-range)
                                     (1 'exactly-one)
                                     (big 'one-or-more))))))
          (ensure-range-class count-type-name
                              :options (if supertype-name
                                           `((include ,supertype-name)))
                              :elements numeric-range
                              :class nil))))
    count-type-name))

(defun adjust-count-type (type supertype)
  (let ((class (find-class type))
        (superclass (find-class supertype)))
    (when (numeric-subrangep (elements class)
                             (elements superclass))
      (ensure-range-class-using-class class
                                      type
                                      :direct-superclasses (list supertype)))))

(defun finalize-slots (class-name specifications)
  (dolist (specification specifications)
    (let ((count-slot-name (getf specification :count))
          count-slot-specification
          count-type-name)
      (cond ((null count-slot-name))
            ((symbolp count-slot-name)
             (setq count-slot-specification (find count-slot-name specifications
                                                  :test #'eq
                                                  :key #'(lambda (specification)
                                                           (getf specification
                                                                 :name)))
                 count-type-name (ensure-count-type class-name
                                                    (getf specification :name)
                                                    (getf count-slot-specification
                                                          :type)))
             (setf (getf count-slot-specification :type) count-type-name))
            (t
             
             ;; Surplus occurrence constraint.
             (setf (getf specification :count) nil)))))
  specifications)

(defun assimilate-top-level-group (element element-content specifications)
  (let* ((class (retrieve-type element-content))
         (name (or (if class (class-name class))
                   (element-attribute element 'name :xsd))))
    (when name
      (deferred-ensure-class-using-class class
                                         name
                                         :direct-slots (finalize-slots name
                                                                       specifications)
                                         :metaclass *default-metaclass*)
      (not nil))))

(defmethod assimilate-content
           (element element-content subelement (tag (eql 'xmlxsd::sequence)) content)
  (declare (ignore subelement))
  (or (assimilate-top-level-group element element-content content)
      (call-next-method)))

(defmethod assimilate-content
           (element element-content subelement (tag (eql 'all)) content)
  (declare (ignore subelement))
  (assimilate-top-level-group element element-content content))

(defun convert-lower-bound (bound)
  (case bound
    ((nil) 1)
    ((unbounded |unbounded|) '-big)
    (t bound)))

(defun convert-upper-bound (bound)
  (case bound
    ((nil) 1)
    ((unbounded |unbounded|) 'big)
    (t bound)))

(defun expand-slot-specification (specifications &optional name)
  (let* ((specification (first specifications))
         (occurrence (getf specification :count))
         count-slot-name)
    (when name
      (unless (getf specification :type)
        
        ;; Preserve reference for later retrieval.
        (setf (getf (first specifications) :ref) (getf specification :name)))
      (setf (getf specification :name) name))
    (unless (singletonp specifications)
      (error "Element declaration \"~A\" has unexpected content."
        (get-xml-name (getf specification :name))))
    (when occurrence
      (setf count-slot-name (add-lisp-name-suffix (getf specification :name)
                                                  *count-slot-suffix*)
        (getf specification :count) count-slot-name)
      (push `(:name ,count-slot-name :type ,occurrence) (rest specifications)))
    specifications))

(defun element-slot-specifications (element content)
  (let ((name (element-attribute element 'name :xsd))
        (type (element-attribute element 'xmlxsd::type :xsd))
        (ref (element-attribute element 'ref :xsd)))
    (if (or type ref)
        
        ;; Innermost element.
        (let ((min-occurs (element-attribute element 'min-occurs :xsd))
              (max-occurs (element-attribute element 'max-occurs :xsd))
              occurrence)
          (when (or min-occurs max-occurs)
            (setq occurrence
                  (make-numeric-range :min (convert-lower-bound min-occurs)
                                      :max (convert-upper-bound max-occurs))))
          (list (list* :name (or name ref)     ; May be temporary.
                       :type (if type (ensure-lisp-name type))
                       (if occurrence (list :count occurrence)))))
      
      ;; Outer element. Pick up inner specification; flesh out.
      (expand-slot-specification content name))))

(defmethod assimilate-content :around
           (element (element-content list) subelement (tag (eql 'element)) content)
  (setf (element-content element) (nconc (element-slot-specifications subelement
                                                                      content)
                                         element-content)))

(defmethod assimilate-content :around
           (element (element-content list) subelement (tag (eql 'choice)) content)
  (declare (ignore subelement))
  (setf (element-content element) (nconc content element-content)))

(defmethod assimilate-content
           (element (element-content string) subelement (tag (eql 'element)) content)

  ;; Global element: overwrite schema documentation.
  (setf (element-content element) (element-slot-specifications subelement content)))

(defmethod assimilate-content (element element-content
                               subelement (tag (eql 'restriction)) (content cons))
  (let ((name (element-attribute element 'name :xsd))
        (superclass (element-attribute subelement 'base :xsd)))
    (ensure-range-class name
                        :options (case superclass
                                   ((nil xmlxsd::string xmlxsd::integer) nil)
                                   (t `((:include ,superclass))))
                        :documentation (if (stringp element-content) element-content)
                        :elements content)))

(defmethod assimilate-content :around
           (element element-content subelement (tag (eql 'min-inclusive)) content)
  (declare (ignore element-content content))
  (push (convert-lower-bound
         (element-attribute subelement 'value :xsd)) (element-content element)))

(defmethod assimilate-content :around
           (element element-content subelement (tag (eql 'max-inclusive)) content)
  (declare (ignore element-content content))
  (push-on-end (element-content element) (convert-upper-bound
                                          (element-attribute subelement
                                                             'value
                                                             :xsd))))

(defmethod assimilate-content :around
           (element element-content subelement (tag (eql 'enumeration)) content)
  (declare (ignore element-content content))
  (push-on-end (element-content element) (element-attribute subelement
                                                            'value
                                                            :xsd)))

(defmethod finalize-content (element (tag (eql 'schema)) (content string))

  ;; Ignore schema documentation.
  (finalize-content element tag nil))

(defmethod finalize-content (element (tag (eql 'schema)) (content list))
  (declare (ignore element))
  (flet ((finish-class (class name &key direct-slots metaclass)
           (flet ((find-global-specification (specification indicator)
                    (find (getf specification indicator)
                          content
                          :test #'eq
                          :key #'(lambda (specification)
                                   (getf specification :name)))))
             (do ((rest-slots direct-slots (rest rest-slots)))
                 ((endp rest-slots))
               (unless (getf (first rest-slots) :type)
                 
                 ;; Global element reference.
                 (setf (getf (first rest-slots) :type)
                   (getf (or (find-global-specification (first rest-slots)
                                                        :name)
                             
                             ;; Reference from inner element.
                             (prog1
                               (find-global-specification (first rest-slots)
                                                          :ref)
                               (remf (first rest-slots) :ref)))
                         :type))))
             (ensure-class-using-class (or class (find-class name))
                                       name
                                       :direct-slots direct-slots
                                       :metaclass metaclass)))
         (adjust-count-types (class name &key direct-slots metaclass)
           (declare (ignore name metaclass))
           (when class
             
             ;; Derived class.
             (let ((superclass (first (class-direct-superclasses class))))
               (dolist (specification direct-slots)
                 (let ((name (getf specification :name))
                       (type (getf specification :type)))
                   (when (find name direct-slots
                               :test #'eq
                               :key #'(lambda (specification)
                                        (getf specification :count)))
                     (let ((slot-definition (find-slot-definition superclass name
                                                                  :direct (not nil))))
                       (when slot-definition
                         
                         ;; Cardinality restriction.
                         (adjust-count-type type
                                            (slot-definition-type
                                             slot-definition)))))))))))
    
    ;; Local elements.
    (revdolist (specification (get-class-specifications))
      (apply #'finish-class specification))
    (dolist (specification (get-class-specifications))
      (apply #'adjust-count-types specification))
    
    ;; Global elements.
    (dolist (specification content)
      (let ((type (getf specification :type)))
        (setf (get (getf specification :name) :xml-type) type)))))

(let ((element-stack ()))

  (defun into-xml-element (tag attribute-fn)
    (push (make-element :tag (get-lisp-name tag)
                        :attribute-fn (or attribute-fn *element-default-attribute-fn*))
          element-stack)
    (unless (or (ignore-element-p (element-tag (first element-stack)))
                (element-content (first element-stack)))
      (let ((object (find-element-object (element-tag (first element-stack))
                                         (first element-stack)
                                         (rest element-stack))))
        (when object
          (setf (element-content (first element-stack)) object)))))

  (defun store-xml-content (content)
    (when content
      (setf (element-content (first element-stack)) content)))

  (defun outof-xml-element ()
    (unless (ignore-element-p (element-tag (first element-stack)))
      (finalize-content (first element-stack)
                        (element-tag (first element-stack))
                        (element-content (first element-stack)))
      (when (second element-stack)
        (assimilate-content (second element-stack)
                            (element-content (second element-stack))
                            (first element-stack)
                            (element-tag (first element-stack))
                            (element-content (first element-stack)))))
    (pop element-stack))

  (defun pop-elements ()
    (setq element-stack nil))

  ) ;end let element-stack

(defmethod deserialize-as-object (element
                                  &key
                                  (tag-fn nil)
                                               ; Tag.
                                  (attribute-fn nil)
                                               ; Named attribute's value.
                                  (content-fn #'cdr)
                                               ; List of objects.
                                  )
  (flet ((element-content (xml-node)
           (let* ((content (funcall content-fn xml-node))
                  (textual (stringp (car content))))
             (values (if textual (car content) content) textual))))
    (map-objects element
                 #'(lambda (xml-node)
                     (multiple-value-bind (content textual)
                         (element-content xml-node)
                       (if textual
                           nil
                         content)))
                 #'(lambda (xml-node)
                     (let (tag attributes)
                       (if tag-fn
                           (setq tag (funcall tag-fn xml-node))
                         (multiple-value-setq (tag attributes)
                           (parse-tag (car xml-node))))
                       (into-xml-element tag
                                         (cond (attribute-fn
                                                #'(lambda (name uri)
                                                    (funcall attribute-fn
                                                             xml-node
                                                             name
                                                             uri)))
                                               (attributes
                                                #'(lambda (name uri)
                                                    (declare (ignore uri))
                                                    (cdr (assoc name attributes
                                                                :test #'eq))))))))
                 #'(lambda (xml-node)
                     (multiple-value-bind (content textual)
                         (element-content xml-node)
                       (when textual
                         (store-xml-content content)))
                     (outof-xml-element)))))

(defmethod deserialize-as-object :around (element &key &allow-other-keys)
  (declare (ignore element))
  (unwind-protect (call-next-method)
    (pop-elements)))

(defmethod deserialize-as-objects ((parse-tree cons)
                                   &key (namespace nil)
                                        (base namespace)
                                        (namespaces *namespace-names*))
  (let (*assumptions*
        (*default-namespace* namespace)
        (*target-namespace* base)
        (*namespaces* (if namespace
                          (adjoin namespace namespaces :test #'eq)
                        namespaces)))
    (dolist (element parse-tree)
      (deserialize-as-object element))
    *assumptions*))