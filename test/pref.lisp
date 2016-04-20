;;; Copyright (C) 2011, 2013 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html

(in-package reasoner)

(defun preferred-extension (e1 e2)
  (unless (and e1 e2) (return-from preferred-extension nil))
  (if (< (size e1)
         (size e2))
      e2
    e1))

(defun fetch-premises (node environment)
  (flet ((fetch-premises-internal (justification)
           (union-environments *atms*
                               (mapcan #'(lambda (n)
                                           (let ((e (fetch-premises n environment)))
                                             (if e (list e))))
                                       (antecedents justification)))))
    (with-accessors ((justifications justifications) (label label))
        node
      (cond ((rest justifications)

             ;; Partially regenerate label, to include any subsumed
             ;; environments removed by the ATMS.
             (reduce #'preferred-extension
                     (mapcar #'fetch-premises-internal justifications)))
            ((subsumesp (first label) environment)
             (first label))))))

(defun find-preferred-extension (object slot-name premises more-premises)
  (reduce #'preferred-extension
          (solutions (uniquify-environment *atms* premises)
                     more-premises
                     *atms*)
          :key #'(lambda (e)
                   (let ((node (first (slot-values object slot-name e))))
                     (if node (fetch-premises node e))))))