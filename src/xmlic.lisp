;;; Copyright (C) 2011, 2012, 2013 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; Interface to CLLIB XML parser.

(require :cllib-xml "clocc:src;cllib;xml")

(in-package :reasoner-ext)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (import '(cllib::xml-decl cllib:xml-obj
            cllib:xmlo-name cllib:xmlo-tag cllib:xmlo-data
            cllib:xmln-ln cllib:xmln-ns cllib:xmlns-uri
            cllib:xml-find-name cllib::xmlns-get)))

(defun find-xmln (xmln)
  (find-xml-name (xmln-ln xmln)
                   (xmlns-uri (xmln-ns xmln))))

(defun get-xmln (name uri)
  (xml-find-name name (xmlns-get uri)))

(defmethod deserialize-as-object ((element xml-obj)
                                  &key tag-fn attribute-fn content-fn
                                  &aux (rdf nil))
  (declare (ignore tag-fn attribute-fn content-fn))
  (call-next-method element
                    :tag-fn #'(lambda (xml-obj)
                                (let ((name (find-xmln (xmlo-name xml-obj))))
                                  (when (eq name 'rdf) (setq rdf (not nil)))
                                  name))
                                               ; Tag.
                    :attribute-fn #'(lambda (xml-obj name namespace)
                                      (let ((xmln
                                             (if namespace
                                                 (get-xmln name
                                                           (if rdf
                                                               (namespace-uri-variant
                                                                namespace)
                                                             (namespace-uri
                                                              namespace))))))
                                        (or (and xmln (xmlo-tag xml-obj xmln))
                                            (xmlo-tag xml-obj name))))
                                               ; Named attribute's value.
                    :content-fn #'(lambda (xml-obj)
                                    (remove-if #'(lambda (object)
                                                   (and (stringp object)
                                                        (eq (char object 0) #\space)))
                                               (xmlo-data xml-obj)))
                                               ; List of objects.
                    ))

(defmethod deserialize-as-object ((element xml-decl)
                                  &key tag-fn attribute-fn content-fn)
  (declare (ignore tag-fn attribute-fn content-fn))
  )