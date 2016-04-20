;;; Copyright (C) 2007, 2009, 2011, 2013 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; Multiple-Fault Diagnosis

(in-package :rs-user)

(defrange device-statuses faulty working)

(defrange device-inputs 0 big)

(defclass device (component)
  ((status :type device-statuses)
   (in1 :type device-inputs)
   (in2 :type device-inputs)
   (out :type device-inputs)))

(defclass adder (device)
  ())

(defclass multiplier (device)
  ())

(defclass complex-device (assembly)
  ((mult1 :type multiplier :initarg :mult1)
   (mult2 :type multiplier :initarg :mult2)
   (mult3 :type multiplier :initarg :mult3)
   (add1 :type adder :initarg :add1)
   (add2 :type adder :initarg :add2)))

(defmethod shared-initialize :after ((d complex-device) slot-names &rest initargs)
  (declare (ignore slot-names))
  (do ((name (instance-name d))
       (rest-initargs initargs (cddr rest-initargs)))
      ((endp rest-initargs))
    (when (typep (second rest-initargs) 'component)
      (setf (instance-name (second rest-initargs))
        (intern (concatenate 'string
                             (string name)
                             (string #\-)
                             (string (first rest-initargs))))))))

(defconstraint multiplier-output ((m multiplier))
  m status is working -> m out = m in1 * m in2)

(defconstraint adder-output ((a adder))
  a status is working -> a out = a in1 + a in2)

(defconstraint mult1-add1 ((d complex-device) (m1 multiplier) (a1 adder))
  d mult1 is m1 and d add1 is a1 -> m1 out = a1 in1)

(defconstraint mult2-add1 ((d complex-device) (m2 multiplier) (a1 adder))
  d mult2 is m2 and d add1 is a1 -> m2 out = a1 in2)

(defconstraint mult2-add2 ((d complex-device) (m2 multiplier) (a2 adder))
  d mult2 is m2 and d add2 is a2 -> m2 out = a2 in1)

(defconstraint mult3-add2 ((d complex-device) (m3 multiplier) (a2 adder))
  d mult3 is m3 and d add2 is a2 -> m3 out = a2 in2)

;;; 3---->|----|
;;;       | M1 |--------->|----|
;;; 2---->|----|          | A1 |---->10
;;;                 +---->|----|
;;; 3---->|----|    |
;;;       | M2 |----|
;;; 2---->|----|    |
;;;                 +---->|----|
;;; 3---->|----|          | A2 |---->12
;;;       | M3 |--------->|----|
;;; 2---->|----|
;;;
;;; {m1}, {a1}, {m2,m3}, {m2,a2}
;;; {m1,m2,m3}, {m1,m2,a2}, {m2,m3,a1}, {m2,a1,a2} (with measurement)

(defvar *observations* '((mult1 in1 3)
                         (mult1 in2 2)
                         (mult2 in1 3)
                         (mult2 in2 2)
                         (mult3 in1 3)
                         (mult3 in2 2)
                         (add1 out 10)
                         (add2 out 12)))

(defvar *measurement* '(mult2 out 5))

(defvar *normal-statuses* '((mult1 status working)
                            (mult2 status working)
                            (mult3 status working)
                            (add1 status working)
                            (add2 status working)))

(defun assume-system-data (system data)
  (mapcar #'(lambda (datum)
              (apply #'assume-system-datum system datum))
    data))

(defun assume-system-datum (system role slot-name value)
  (assume-slot-value (car (slot-value-reduce system role t))
                     slot-name
                     value))

(let* ((a1 (make-assumption *atms*))
       (dev (make-instance 'complex-device :name 'dev1 :antecedents (list a1)))
       (observations (assume-system-data dev (cons *measurement* *observations*)))
       (normal-statuses (assume-system-data dev *normal-statuses*)))
  
  (defun faulty-parts (environment)
    (remove 'working (slot-value-reduce dev 'parts environment)
            :key #'(lambda (part)
                     (car (slot-value-reduce part 'status environment)))))
  
  (defun diagnoses (observations verbose &aux environments)
    (setq environments (solutions (uniquify-environment *atms*
                                                        (cons a1 observations))
                                  normal-statuses
                                  *atms*))
    (if verbose
        (mapcar #'faulty-parts environments)
      environments))
  
  (defun diagnoses1 (&key (verbose t))
    (diagnoses (cdr observations) verbose))
  
  (defun diagnoses2 (&key (verbose t))
    (diagnoses observations verbose))
  
  (defun describe-system-status (environment)
    (dolist (part (slot-value-reduce dev 'parts environment))
      (format t "~S - ~S~%"
        part
        (slot-value-reduce part 'status environment))))
) ;end let* a1