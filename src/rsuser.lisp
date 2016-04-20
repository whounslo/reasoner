;;; Copyright (C) 2007-2009, 2011 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html


(defpackage :reasoner-ext
  (:nicknames :rs-ext :rse)
  (:use :reasoner :cl)
#-mop
  (:import-from :reasoner #:defclass*)
  (:shadow #:defclass)
  (:export #:*default-metaclass* #:yes-or-no #:yes #:no))

(in-package :rs-ext)

(defparameter *default-metaclass* 'extended-class)

#+mop
(defmacro defclass (name direct-superclasses direct-slots &rest options)
  `(cl:defclass ,name
                ,direct-superclasses
                ,direct-slots
                ,@(if (assoc :metaclass options :test #'eq)
                      options
                    (cons `(:metaclass ,*default-metaclass*) options))))

#-mop
(defmacro defclass (name direct-superclasses direct-slots &rest options)
  `(defclass* ,name
              ,direct-superclasses
              ,direct-slots
              ,@(if (assoc :metaclass options :test #'eq)
                    options
                  (cons `(:metaclass ,*default-metaclass*) options))))

(defrange yes-or-no yes no)

(defrange yes yes)

(defrange no no)

(defpackage :reasoner-user
  (:nicknames :rs-user)
  (:use :reasoner-ext :reasoner :cl)
  (:shadowing-import-from :reasoner-ext #:defclass))