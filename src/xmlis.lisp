;;; Copyright (C) 2011, 2012, 2013 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; Interface to SAX parsers (Allegro, cxml).

(eval-when (:execute :compile-toplevel :load-toplevel)
  (when #+allegro (find-package :cxml) #-allegro t
    (pushnew :cxml *features*)))

#-cxml
(require :sax)

(defpackage #-cxml :net.xml.rs #+cxml :rs-sax
#-cxml
  (:use :reasoner-ext :net.xml.sax :cl)
#+cxml
  (:use :reasoner-ext :sax :cl)
#+cxml
  (:import-from :cxml #:parse)
#+cxml
  (:import-from :sax #:dtd)
  (:import-from :reasoner-ext
                #:rdf #:xml-fragment-separator #:push-on-end #:get-lisp-name)
#-cxml
  (:export #:sax-parse-file #:sax-parse-stream #:sax-parse-string)
#+cxml
  (:export #:parse)
  (:export #:deserializer #:namespace-missing #:default-namespace-missing))

#-cxml
(in-package :net.xml.rs)

#+cxml
(in-package :rs-sax)

(defclass deserializer (#-cxml sax-parser #+cxml abstract-handler)
  ((namespaces :initform (list :xml :xmlns) :accessor namespaces)
   (default-stack :initform nil :accessor defaults)
#-cxml
   (base :initform nil :accessor xml-base)
   (all-content :initform nil :accessor all-content)
   (content-valid :accessor content-valid)))

(defmacro with-prefix-mappings (&body body)
  `(let ((*namespaces* (namespaces parser))
         (*default-namespace* (car (defaults parser)))
         (*target-namespace* (xml-base parser)))
     ,@body))

#-cxml
(defun attribute-triple (attr)
  (multiple-value-bind (name namespace)
      (parse-qualified-name (car attr))
    (cons (cons name namespace) (cdr attr))))

#+cxml
(defun attribute-triple (attr)
  (cons (cons (attribute-local-name attr)
              (let ((uri (attribute-namespace-uri attr)))
                (if uri (find-uri-namespace uri) *default-namespace*)))
        (attribute-value attr)))

(defmethod start-document ((parser deserializer))
  (pop-elements))

#+cxml
(defmethod start-dtd ((parser deserializer) name public-id system-id)
  (declare (ignore name public-id system-id)))

#+cxml
(defmethod end-dtd ((parser deserializer))
  )

#+cxml
(defmethod start-internal-subset ((parser deserializer))
  )

#+cxml
(defmethod end-internal-subset ((parser deserializer))
  )

#+cxml
(defmethod internal-entity-declaration ((parser deserializer) kind name value)
  (declare (ignore kind name value)))

#+cxml
(defmethod entity-resolver ((parser deserializer) resolver)
  (declare (ignore resolver)))

#+cxml
(defmethod dtd ((parser deserializer) dtd)
  (declare (ignore dtd)))

#-cxml
(defmethod start-element :before ((parser deserializer) iri localname qname attrs)
  (declare (ignore iri qname))
  (when (string= localname "RDF")
    (setf (xml-base parser) (cdr (assoc "xml:base" attrs :test #'string=)))))

(defmethod start-element ((parser deserializer) iri localname qname attrs)
  (declare (ignore qname))
  (with-prefix-mappings
    (let ((attributes (mapcar #'attribute-triple attrs)))
      (setf (all-content parser) nil (content-valid parser) (not nil))
      (into-xml-element (find-xml-name localname iri)
                        (if attributes
                            #'(lambda (name namespace)
                                (cdr (find-if #'(lambda (pair)
                                                  (and (string= (caar pair) name)
                                                       (or (null (cdar pair))
                                                           (eq (cdar pair) namespace))))
                                              attributes))))))))

(defmethod end-element ((parser deserializer) iri localname qname)
  (declare (ignore iri localname qname))
  (with-accessors ((content all-content)
                   (valid content-valid))
      parser
    (when content
      (when valid
        (store-xml-content (apply #'concatenate 'string content)))
      (setf content nil))
    (setf valid nil)
    (with-prefix-mappings
      (outof-xml-element))))

(defmethod namespace-missing ((parser deserializer) prefix iri)
  (let* ((namespace-name (find-prefix-namespace prefix nil))
         (uri (if namespace-name (namespace-uri namespace-name))))
    (unless (or (null uri) (string= iri uri))
      (error "A namespace named ~A already exists, but not with uri ~S."
        prefix iri))
    (make-namespace (or namespace-name
                        (get-lisp-name (intern prefix (find-package :keyword))))
                    iri)))

(defmethod default-namespace-missing ((parser deserializer) iri)
  (make-namespace (gensym (string :ns)) iri))

(defmethod new-namespace ((parser deserializer) prefix iri)
  (let* ((is-default (zerop (length prefix)))
         (truncated-iri (subseq iri 0 (position xml-fragment-separator iri
                                                :from-end (not nil))))
         (namespace-name (if is-default
                             (default-namespace-missing parser truncated-iri)
                           (namespace-missing parser prefix truncated-iri))))
    (when is-default
      (push namespace-name (defaults parser)))
    namespace-name))

(defmethod start-prefix-mapping ((parser deserializer) prefix iri)
  (let ((namespace-name (find-uri-namespace iri *namespace-names* nil)))
    (pushnew (cond ((null namespace-name)
                    (new-namespace parser prefix iri))
                   ((eq namespace-name (car (defaults parser)))
                    (let ((package (namespace-package namespace-name))
                          (namespace-name (new-namespace parser prefix iri)))
                      (when package
                        (setf (namespace-package namespace-name) package))
                      namespace-name))
                   (t namespace-name))
             (namespaces parser)
             :test #'eq)))

(defmethod end-prefix-mapping ((parser deserializer) prefix)
  (declare (ignore prefix))
  (with-accessors ((namespaces namespaces)
                   (defaults defaults))
      parser
    (when (eq (pop namespaces) (car defaults))
      (pop defaults))))

#-cxml
(defmethod content ((parser deserializer) content start end ignorable)
  (declare (ignore ignorable))
  (push-on-end (all-content parser) (subseq content start end)))

#-cxml
(defmethod content-character ((parser deserializer) character ignorable)
  (declare (ignore ignorable))
  (push-on-end (all-content parser) (string character)))

#+cxml
(defmethod characters ((parser deserializer) content)
  (push-on-end (all-content parser) content))

#+cxml
(defmethod comment ((parser deserializer) data)
  (declare (ignore data)))

(defmethod end-document ((parser deserializer))
  )