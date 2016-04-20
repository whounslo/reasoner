;;; Copyright (C) 2007, 2009, 2011, 2012, 2014 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html


(in-package reasoner)

(defrange (numeric-range (:include range)) -big big)

(defrange (symbolic-range (:include range)))

(defrange zero-or-more 0 big)

(defrange (zero-or-one (:include zero-or-more)) 0 1)

(defrange (one-or-more (:include zero-or-more)) 1 big)

(defrange (exactly-one (:include one-or-more)) 1 1)

(defrange true-or-false true false)

(defrange false false)

(defrange true true)

(defmethod initialize-instance :before ((instance symbolic-range)
                                        &key value)
  (unless value
    (error "Attempt to create an empty range.")))

(defmethod initialize-instance ((instance symbolic-range)
                                &key object slot-name value)
  "Ensures that range is initialized as a list of items."
  (call-next-method instance
                    :object object
                    :slot-name slot-name
                    :value (if (listp value) value (list value))))

(defmethod initialize-instance ((instance numeric-range)
                                &key object slot-name value)
  "Ensures that range is initialized as a list of items."
  (call-next-method instance
                    :object object
                    :slot-name slot-name
                    :value (typecase value
                             ((or numeric-range* range-set) value)
                             (t (make-numeric-range :min value :max value)))))

(defmethod range-intersection ((range1 numeric-range)
                               (range2 numeric-range))
  (numeric-range-intersection (elements range1) (elements range2)))

(defmethod range-intersection ((range1 t)
                               (range2 numeric-range))
  (numeric-range-intersection range1 (elements range2)))

(defmethod range-intersection ((range1 symbolic-range)
                               (range2 symbolic-range))
  (intersection (elements range1) (elements range2)))

(defmethod range-intersection ((range1 list)
                               (range2 symbolic-range))
  (intersection range1 (elements range2)))

(defmethod slot-value-equal-1 ((element symbol)
                               (range symbolic-range))
  (and (eql (length (elements range)) 1)
       (eq (car (elements range)) element)))

(defmethod slot-value-equal-1 ((range1 list)
                               (range2 symbolic-range))
  (and (subsetp range1 (elements range2) :test #'eq)
       (subsetp (elements range2) range1 :test #'eq)))

(defmethod slot-value-equal-1 ((range1 t)
                               (range2 numeric-range)
                               &aux ranges)
  (flet ((numeric-range-equal (range1 range2)
           (and (eql (range-min range1) (range-min range2))
                (eql (range-max range1) (range-max range2)))))
    (cond ((and (typep range1 'range-set)
                (typep (elements range2) 'range-set))
           (equal (range-set-elements range1)
                  (range-set-elements (elements range2))))
          ((typep range1 'range-set)
           (setq ranges (range-set-elements range1))
           (and (singletonp ranges)
                (numeric-range-equal (car ranges) (elements range2))))
          ((typep (elements range2) 'range-set)
           (setq ranges (range-set-elements (elements range2)))
           (and (singletonp ranges)
                (numeric-range-equal (car ranges) range1)))
          (t (numeric-range-equal range1 (elements range2))))))