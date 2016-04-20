;;; Copyright (C) 2011, 2012, 2013 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; XML names and namespaces

(in-package :reasoner-ext)

(defparameter *case-preference* (readtable-case *readtable*))

(defun preserve-case-p (&optional (readtable *readtable*))
  (eq (readtable-case readtable) :preserve))

;;; pprint-subst - intended to be called from within a format string.
;;; Substitutes characters with characters or strings in accordance with
;;; *subst-chars*. The case of characters at word boundaries, delimited
;;; by the substitutions, is controlled by the use of the modifiers:
;;;  colon    all words are capitalized, as if by string-capitalize, except the first
;;;  at-sign  the first character is forced to uppercase; no others are affected
;;;           (if object is a symbol, other characters are forced to lowercase)
;;;  both     all words are capitalized
;;;  neither  the first character is forced to lowercase; no others are affected
;;;           (if object is a symbol, all characters are forced to lowercase)

(defparameter *subst-chars* '((#\- . "") (#\_ . #\space)))

(defun pprint-subst (stream object &optional colon-p at-sign-p &aux (is-symbol (symbolp object)))
  (let ((str (if is-symbol (symbol-name object) object))
        ch
        entry
        (break at-sign-p))
    (dotimes (i (length str))
      (setq ch (char str i)
          entry (assoc ch *subst-chars* :test #'char=))
      (cond ((null entry)
             (write-char (cond (at-sign-p (char-upcase ch))
                               (colon-p
                                (prog1
                                    (cond (break (char-upcase ch))
                                          ((eq *case-preference* :upcase)
                                           (char-downcase ch))
                                          (t ch))
                                  (setq break nil)))
                               ((or (zerop i) is-symbol)
                                (char-downcase ch))
                               (t ch))
                         stream)
             (setq at-sign-p nil
                 break (char= ch #\space)))
            ((characterp (cdr entry))
             (write-char (cdr entry) stream)
             (setq break (char= (cdr entry) #\space)))
            ((setq break (zerop (length (cdr entry)))))
            (t (write-string (cdr entry) stream))))))

(defun set-xml-name (name format-control
                     &optional (package (symbol-package name)))
  (let ((xml-name (intern (format nil format-control name)
                          package)))
    (setf (get xml-name :lisp-name) name
          (get name :xml-name) xml-name)
    xml-name))

(defmethod get-xml-name ((name t) &optional mandatory format-control)
  (declare (ignore mandatory format-control))
  name)

(defmethod get-xml-name ((name symbol)
                         &optional mandatory (format-control
                                              "~:/rse::pprint-subst/"))
  (cond ((get name :xml-name))
        ((and (preserve-case-p) (not mandatory))
         name)
        (t (set-xml-name name format-control))))

(defparameter *emphasize-type-name* (not nil))

(defgeneric ensure-xml-type-name (name)
  (:method ((name symbol))
    (when *emphasize-type-name*
      (get-xml-name name nil "~:@/rse::pprint-subst/"))
    name)
  (:method ((names cons))
    (mapc #'ensure-xml-type-name names))
  (:method ((class standard-class))
    (ensure-xml-type-name (class-name class))))

(defun ensure-symbol (name package)
  
  ;; Avoid re-importing name - might be uninterned, i.e., fresh.
  (or (find-symbol (string name) package)
#+abcl(if (symbol-package name) nil (intern (string name) package))
      (progn (import name package)
        name)))

(defmacro define-xml-name (name lisp-name namespace)
  `(let ((package (namespace-package ,namespace)))
     (set-xml-name (ensure-symbol ,lisp-name package)
                   (string ,name)
                   package)))

(defun pprint-lisp-name (stream object &optional colon-p at-sign-p)
  (declare (type string object) (ignore colon-p at-sign-p))
  (let (ch)
    (dotimes (i (length object))
      (setq ch (char object i))
      (cond ((not (upper-case-p ch)))
            ((zerop i))
            ((lower-case-p (char object (1- i)))
             (write-char #\- stream)))
      (write-char (if (eq *case-preference* :upcase)
                      (char-upcase ch)
                    (char-downcase ch))
                  stream))))

(defun set-lisp-name (xml-name)
  (let ((symbol
         (intern (format nil "~/rse::pprint-lisp-name/" (string xml-name))
                 (symbol-package xml-name))))
    (setf (get symbol :xml-name) xml-name
          (get xml-name :lisp-name) symbol)
    symbol))

(defun get-lisp-name (xml-name)
  (or (get xml-name :lisp-name)
      (set-lisp-name xml-name)))

(defun get-content-lisp-name (xml-name)
  (if (preserve-case-p)
      xml-name
    (get-lisp-name xml-name)))

(defun get-tag-lisp-name (name &optional mandatory)
  
  ;; Name has already been converted by GET-LISP-NAME.
  (if (preserve-case-p)
      (get-xml-name name mandatory)
    name))

(defun ensure-lisp-name (name)
  (or (and (preserve-case-p)
           (get name :lisp-name))
      name))

(defmacro add-lisp-name-suffix (name &rest names)
  `(get-tag-lisp-name (intern (concatenate 'string
                                           (string (ensure-lisp-name ,name))
                                           ,@(mapcan #'(lambda (name)
                                                         `((string #\-)
                                                           (string
                                                            (ensure-lisp-name
                                                             ,name))))
                                                     names))
                              (symbol-package ,name))
                      'mandatory))

(defun namespace-prefix (name)
  (declare (type symbol name))
  (get name 'xml-prefix))

(defun (setf namespace-prefix) (new-value name)
  (declare (type symbol name))
  (setf (get name 'xml-prefix) new-value))

(defun namespace-uri (name)
  (declare (type symbol name))
  (get name 'xml-uri))

(defun (setf namespace-uri) (new-value name)
  (declare (type symbol name))
  (setf (get name 'xml-uri) new-value))

(defun namespace-package (name)
  (declare (type symbol name))
  (get name 'xml-namespace))

(defun (setf namespace-package) (new-value name)
  (declare (type symbol name))
  (setf (get name 'xml-namespace) new-value))

(defparameter *namespace-package-prefix* :xml)

(defun ensure-namespace-package (name)
  (declare (type (and symbol (not null)) name))
  (or (namespace-package name)
      (setf (namespace-package name)
        (make-package (concatenate 'string
                                   (string *namespace-package-prefix*)
                                   (string name))
                      :use ()))))

(defvar *namespace-names* nil)

(defun make-namespace (namespace-name uri &optional package)
  (when (and package (namespace-package namespace-name))
    (error "A namespace named ~A already exists." namespace-name))
  (setf (namespace-prefix namespace-name) (string-downcase
                                           (string namespace-name))
        (namespace-uri namespace-name) uri)
  (when package
    (setf (namespace-package namespace-name) package))
  (pushnew namespace-name *namespace-names* :test #'eq)
  namespace-name)

(defmacro defnamespace (namespace-name uri &body body)
  `(eval-when (:execute :compile-toplevel :load-toplevel)
     (make-namespace ',namespace-name ,uri)
     (ensure-namespace-package ',namespace-name)
     ,@(if (and body (not (consp (car body))))
           `((let ((package (namespace-package ',namespace-name)))
               (dolist (name ',body)
                 (when (consp name) (return))  ; Reached documentation.
                 (etypecase name
                   (string (get-xml-name (intern name package)
                                         'mandatory))
                   (symbol (import (get-xml-name (ensure-symbol name package)
                                                 'mandatory)
                                   package)))))))
     ',namespace-name))