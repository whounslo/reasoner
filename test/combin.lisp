;;; Copyright (C) 2007, 2009 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html

(in-package reasoner)

(defun place-randomly (value list limit &aux (n (random limit)))
  (do ((tail (nthcdr n list) (or (cdr tail) list)))
      ((null (car tail)) (setf (car tail) value))))

(defmethod find-assumed-value ((a assumption) slot-name
                               &optional (environment (first (label a))))
  (slot-value-reduce (datum-object (assumed-datum a))
                     slot-name
                     environment))

(defmethod find-assumed-value ((object extended-object) slot-name
                               &optional (environment t))
  (slot-value-reduce object slot-name environment))

(defun map-elements (range function)
  "Applies function to each element of a fully enumerated numeric range or range set."
  (flet ((map-elements-internal (range)
           (do ((i (range-min range) (1+ i)))
               (nil)
             (funcall function i)
             (when (eql i (range-max range)) (return)))))
    (etypecase range
      (numeric-range* (map-elements-internal range))
      (range-set (dolist (subrange (range-set-elements range))
                   (map-elements-internal subrange))))))

;;; min-conflicts

(defparameter max-steps 100)

(defun min-conflicts (assumptions value-fn reassign-fn
                      &key (index-key (constantly t)) (top-limit 3) (index-limit nil))
  (let (environment index assignment1 value1 siblings candidates)
    (flet ((initial-environment (assumptions)
             (do ((rest-assumptions assumptions (rest rest-assumptions))
                  (environment nil (add-assumption *atms*
                                                   (first rest-assumptions)
                                                   environment
                                                   nil
                                                   'no-check)))
                 ((endp rest-assumptions) environment)))
           (conflictp (assumption)
             (conflictp assumption environment))
           (conflict-count (assumption)
             (conflict-count assumption environment)))
      (setq environment (initial-environment assumptions))
      (dotimes (i max-steps)
        (nschedule *atms* environment)
        (setq assumptions (sort assumptions #'> :key #'conflict-count))
        (unless (conflictp (first assumptions))    ; Solution?
          (return-from min-conflicts (values environment i)))
        
        ;; Select conflict-ridden assignment at random.
        (if index-limit
            (setq index (random index-limit)
                assignment1 (find index assumptions :key index-key :test #'eql))
          (setq assignment1 (nth (random top-limit) assumptions)
              index (funcall index-key assignment1)))
        (setq assumptions (delete assignment1 assumptions :test #'eq)
            siblings (remove index assumptions
                             :key index-key :test (complement #'eql))
            value1 (funcall value-fn assignment1)
            candidates (mapcar #'(lambda (assumption)
                                   (funcall reassign-fn
                                            (datum-object (assumed-datum assumption))
                                            value1))
                               siblings))
        (dolist (candidate candidates)
          (nschedule *atms* (add-assumption *atms*
                                            candidate
                                            assumptions
                                            nil
                                            'no-check)))
        
        ;; Find assignment to swap value with that minimizes conflicts.
        (let ((assignment2 (first siblings))
              (reassignment2 (first candidates))
              reassignment1)
          (mapc #'(lambda (a r)
                    (when (< (conflict-count r) (conflict-count reassignment2))
                      (setq assignment2 a
                          reassignment2 r)))
                (rest siblings)
                (rest candidates))
          (nsubstitute reassignment2 assignment2 assumptions :test #'eq)
          (setq reassignment1 (funcall reassign-fn
                                       (datum-object (assumed-datum assignment1))
                                       (funcall value-fn assignment2))
              environment (add-assumption *atms*
                                          reassignment1
                                          assumptions
                                          nil
                                          'no-check)
              assumptions (cons reassignment1 assumptions))))
      nil)))