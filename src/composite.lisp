;;; Copyright (C) 2011 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; Composite objects: compound objects and assemblies

(in-package reasoner)

(defclass composite-object ()
  ((parts :type part))
  (:metaclass extended-class))

(defclass compound-object (composite-object)
  ((parts :type part :initarg :part :initarg :parts))
  (:metaclass extended-class))

(defclass assembly (composite-object)
  ((parts :type component))
  (:metaclass extended-class))

(defclass part ()
  ()
  (:metaclass extended-class))

(defclass component (part)
  ()
  (:metaclass extended-class))

(defmethod find-part ((object compound-object) slot-name)
  (find slot-name (slot-values object 'parts t)
        :key #'datum-value
        :test #'(lambda (slot-name object)
                  (slot-exists-p object slot-name))))

(defmethod slot-missing ((class extended-class)
                         (object compound-object)
                         slot-name
                         (operation (eql 'slot-boundp))
                         &optional new-value)
  (declare (ignore new-value))
  (if (find-part object slot-name) (not nil) (call-next-method)))

(defmethod slot-missing ((class extended-class)
                         (object compound-object)
                         slot-name
                         (operation (eql 'slot-value))
                         &optional new-value)
  (declare (ignore new-value))
  (let ((slot-value (find-part object slot-name)))
    (if slot-value
        (slot-value (datum-value slot-value) slot-name)
      (call-next-method))))

(defmethod slot-definition-missing ((class extended-class)
                                    (object compound-object)
                                    slot-name
                                    (operation (eql 'add-slot-value))
                                    new-value
                                    antecedents
                                    informant
                                    &rest args)
  (let ((slot-value (find-part object slot-name)))
    (if slot-value
        (apply #'add-slot-value (datum-value slot-value)
                                slot-name
                                new-value
                                antecedents
                                informant
                                args)
      (call-next-method))))

(defmethod add-slot-value-using-class :after ((class extended-class)
                                              (object assembly)
                                              slot
                                              (new-value component)
                                              antecedents
                                              (informant (eql :initial-value))
                                              &rest args
                                              &key slot-name &allow-other-keys)
  (declare (ignore slot))
  (unless (eq slot-name 'parts)
    (apply #'add-slot-value object 'parts new-value antecedents informant args)))

(defmethod initialize-instance ((instance assembly) &rest initargs
                                &aux (class (class-of instance)))
  (do ((slots (class-slots class) (cdr slots))
       antecedents
       count
       pair
       (more-initargs () (nconc more-initargs pair)))
      ((endp slots) (apply #'call-next-method instance
                                              (append initargs
                                                      more-initargs)))
    (with-accessors ((slot-initargs slot-definition-initargs)
                     (slot-type slot-definition-type)
                     (slot-count slot-definition-count))
        (car slots)
      (setq antecedents (if (subtypep slot-type 'assembly)
                            (getf initargs :antecedents))
            count (if slot-count
                      (range-min (range-elements (find-slot-definition class
                                                                       slot-count)))
                    1)
            pair (if (and slot-initargs
                          (not (get-properties initargs slot-initargs))
                          (subtypep slot-type 'component)
                          (plusp count))
                     (list (car slot-initargs)
                           (if (eql count 1)
                               (make-instance slot-type
                                 :antecedents antecedents)
                             (do ((i 0 (1+ i))
                                  (instances () (cons (make-instance slot-type
                                                        :antecedents antecedents)
                                                      instances)))
                                 ((eql i count) instances)))))))))