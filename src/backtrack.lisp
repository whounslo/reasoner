;;; Copyright (C) 2007, 2009-10, 2014 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html

(eval-when (:compile-toplevel)
  (declaim (optimize (speed 3) (safety 1) (space 0) (debug 0))))

(in-package atms)
(eval-when (:execute :compile-toplevel :load-toplevel)
  (import '(streams:flatmap
            streams:singleton
            streams:the-empty-stream
            rparallel:do-deferred-results))
  (export
   '(datum-object map-intersection oneof-disjunction
     conflictp conflict-count
     added-assumption order-control-disjunction
     backtrack add-assumption ensure-environment
     schedule solutions nschedule
     )))

;;; map-intersection applies function to every element that occurs in both
;;; list-1 and list-2. Successive pairs of elements in both lists are assumed
;;; to satisfy predicate.

(defun map-intersection (function list-1 list-2 predicate
                         &key (key #'identity) (test #'eql))
  (do ((rest-list-1 list-1 (rest rest-list-1))
       (rest-list-2 list-2)
       (comparison-fn (complement predicate)))
      ((endp rest-list-1) nil)
    (setq rest-list-2 (member (funcall key (first rest-list-1))
                              rest-list-2
                              :test #'(lambda (item1 item2)
                                        (funcall comparison-fn item2 item1))
                              :key key))
    (when (funcall test (first rest-list-1) (first rest-list-2))
      (funcall function (first rest-list-1)))))

(defmethod oneof-disjunction ((assumptions list) &optional (no-check (not nil)))
  (when assumptions
    (oneof-disjunction (rest assumptions))
    (dolist (a (rest assumptions))
      (when (or no-check
                (not (conflictp (first assumptions) a)))
        (record-binary-contradiction (first assumptions) a)))))

(defmethod datum-object ((object t))
  object)

(defmethod added-assumption ((object t) (a assumption) (assumptions list))
  a)

(defmethod order-control-disjunction ((object t) (e environment) (assumptions list))
  assumptions)

(defmethod backtrack :before
           ((e environment) (control-disjunctions list) (tms atms))
  (when control-disjunctions
    (setf (car control-disjunctions)
      (order-control-disjunction (datum-object
                                  (assumed-datum
                                   (caar control-disjunctions)))
                                 e
                                 (car control-disjunctions)))))

;(defmethod backtrack ((e environment) (control-disjunctions list) (tms atms))
;  (cond (control-disjunctions
;         (do ((d (car control-disjunctions) (cdr d))
;              eprime
;              (solutions nil))
;             ((endp d) solutions)
;           (setq eprime (add-assumption tms (car d) e))
;           (when eprime
;             (setq solutions (nconc solutions
;                                    (backtrack eprime
;                                               (cdr control-disjunctions)
;                                               tms)))
;             (when (contradictoryp e)
;               (return nil)))))
;        (t (nschedule tms e)
;           (if (contradictoryp e)
;               nil
;             (list e)))))

(defmethod backtrack ((e environment) (control-disjunctions list) (tms atms))
  (cond (control-disjunctions
         (flatmap #'(lambda (a &aux eprime)
                      (setq eprime (add-assumption tms a e))
                      (if eprime
                          (prog1
                              (backtrack eprime
                                         (cdr control-disjunctions)
                                         tms)
                            (when (contradictoryp e)
                              (return-from backtrack the-empty-stream)))
                        the-empty-stream))
                  (car control-disjunctions)))
        (t (nschedule tms e)
           (if (contradictoryp e)
               the-empty-stream
             (singleton e)))))

;;; conflictp examines the intersection of assumption's contras and environment.

(defmethod conflictp ((a assumption) (e environment) &optional (ordered (not nil)))
  (conflictp a (assumptions e) ordered))

(defmethod conflictp ((a assumption) (assumptions list) &optional (ordered nil))
  (if ordered
      (map-intersection #'(lambda (a)
                            (declare (ignore a))
                            (return-from conflictp (not nil)))
                        (contras a)
                        assumptions
                        assumption-ordering-predicate
                        :key #'serial-number)
    (some #'(lambda (assumption)
              (conflictp a assumption))
          assumptions)))

;;; conflict-count is like conflictp, but returns the number of conflicts.

(defmethod conflict-count ((a assumption) (e environment) &optional (ordered (not nil)))
  (conflict-count a (assumptions e) ordered))

(defmethod conflict-count ((a assumption) (assumptions list) &optional (ordered nil))
  (if ordered
      (let ((count 0))
        (map-intersection #'(lambda (a)
                              (declare (ignore a))
                              (incf count))
                          (contras a)
                          assumptions
                          assumption-ordering-predicate
                          :key #'serial-number)
        count)
    (count-if #'(lambda (assumption)
                  (conflictp a assumption))
              assumptions)))

(defmethod conflictp ((a1 assumption) (a2 assumption) &optional ordered)
  (declare (ignore ordered))
  (find a1 (contras a2) :test #'eq))

;;; add-assumption adds a single assumption to an environment.
;;; Does nothing (returns NIL) if the result would contain a binary
;;; contradiction.  Also returns NIL if resulting environment is found to be
;;; inconsistent when checked against nogood database. (These checks are
;;; inhibited if no-check is non-NIL.)

(defmethod add-assumption ((tms atms) (a assumption) (e environment)
                           &optional (dont-create nil) (no-check nil)
                                     (at-front nil at-front-supp) (ordered (not nil))
                           &aux (assumptions (assumptions e)))
  "Specialized environment union used where one environment is of length one."
  (flet ((at-front-p ()
           (cond (at-front-supp at-front)
                 (assumptions
                  (funcall assumption-ordering-predicate
                           (serial-number a)
                           (serial-number (first assumptions)))))))
    (add-assumption tms a assumptions dont-create no-check (at-front-p) ordered)))

(defmethod add-assumption :around
                          ((tms atms) (a assumption) (assumptions list)
                           &optional (dont-create nil) (no-check nil)
                                     (at-front nil) (ordered nil))
  (declare (ignore dont-create no-check at-front ordered))
  (multiple-value-bind (result e)
      (call-next-method)
    (when result
      (added-assumption (datum-object (assumed-datum a)) a assumptions))
    (values result e)))

(defmethod add-assumption ((tms atms) (a assumption) (assumptions list)
                           &optional (dont-create nil) (no-check nil)
                                     (at-front nil) (ordered nil))
  "Specialized environment union used where one environment is of length one."
  (flet ((subsumed-by-nogood-p (environment)
           (or (contradictoryp environment)
               (let ((size (size environment))
                     assumptions)
                 (dolist (e (nogoods a))
                   (unless (< (size e) size)
                     (return nil))
                   (setq assumptions (assumptions e))
                   (when (or (not at-front)
                             (eq (first assumptions) a))
                     (when (subsumesp assumptions environment 'ordered)
                       (set-contradictory environment)
                       (return (not nil)))))))))
    (let (superset e)
      (values (if (or (if no-check
                          nil
                        (or (contradictoryp a)
                            (conflictp a assumptions (or at-front ordered))))
                      (progn
                        (setq superset (cons a assumptions))
                        (when (or (not at-front) no-check)
                          (setq e (uniquify-environment tms
                                                        superset
                                                        dont-create)))
                        (cond (no-check nil)
                              ((subsumed-by-nogood-p (or e superset)))
                              (at-front
                               (setq e (uniquify-environment tms
                                                             superset
                                                             dont-create
                                                             'ordered))
                               nil))))
                  nil
                (or e superset))
              e))))

(defmethod contradictoryp ((assumptions list))
  nil)

(defmethod set-contradictory ((assumptions list))
  nil)

(defun execute-pending-consumers (&optional environment)
  (declare (ignorable environment))
  (do-deferred-results matched-node
    (when matched-node
      (if environment
          (execute-consumers environment)
        (mapc #'execute-consumers (label matched-node))))))

(defmethod schedule ((tms atms) (e environment))
  "Run all consumers in all subsets of an environment."
  
  ;; For the environment {A, B, C}, consumers are executed in the order:
  ;; {A}, {B}, {A, B}, {C}, {A, C}, {B, C}, {A, B, C}.
  (let (no-check (subsets nil))
    (dolist (assumption (reverse (assumptions e))) ; Reverse so that ordering
                                                   ; of assumptions is
                                                   ; preserved when adding.
      (setq no-check (not nil)
            subsets
            (nconc subsets
                   (mapcan #'(lambda (subset &aux result e)
                               (multiple-value-setq (result e)
                                 (add-assumption tms
                                                 assumption
                                                 subset
                                                 'dont-create
                                                 no-check
                                                 'at-front))
                               (when result
                                 (when e
                                   (execute-consumers e)
                                   (execute-pending-consumers e)
                                   (when (contradictoryp e)
                                     (setq no-check nil
                                                   ; Check that further environments
                                                   ; generated during this iteration
                                                   ; (i.e., containing assumption)
                                                   ; are not subsumed by this
                                                   ; environment.
                                         result nil))))
                               (if result (list result))
                                                   ; Eliminate contradictory
                                                   ; environment to prevent
                                                   ; generation of supersets.
                               )
                     (cons nil subsets)))))
    subsets))

(defmethod ensure-environment ((tms atms) (e environment)
                               &optional (ordered nil))
  (declare (ignore ordered))
  e)

(defmethod ensure-environment ((tms atms) (assumptions list)
                               &optional (ordered nil))
  (uniquify-environment tms assumptions nil ordered))

(defmethod assumptions ((assumptions list))
  assumptions)
  
(defmethod solutions ((e environment) (choices list) (tms atms)
                      &optional (dont-create nil))
  "Find maximal consistent supersets of environment, with respect to choices."
  (flet ((subsumesp (e1 e2)
           (subsumesp e1 e2 'ordered)))
    (let (subsets)
      (declare (type list subsets))
      (setq subsets (schedule tms
                              (uniquify-environment tms
                                                    (append (assumptions e)
                                                            choices))))
      (unless (zerop (size e))
        (deletef subsets e :test-not #'subsumesp))
      (setq subsets (delete-duplicates subsets :test #'subsumesp))
      (unless dont-create
        (map-into subsets
                  #'(lambda (subset)
                      (ensure-environment tms subset 'ordered))
                  subsets))
      subsets)))

;;; nschedule is the non-consing version of schedule. Environments are
;;; executed in size order and those of the same size in an arbitrary order.

(defmethod nschedule ((tms atms) (e environment) &aux (size (size e)))
  (with-accessors ((index environment-index))
      tms
    (do ((rest-index index (rest rest-index))
         (entry-point (first index) (second rest-index))
                                                   ; Be sure to find newly-
                                                   ; created entry points.
         (exit-point (first index) entry-point))
        ((eql (indexed-size entry-point) size))
      (do ((environments entry-point (rest environments)))
          ((eq environments exit-point))
        (when (and (node-added (first environments))
                   (subsumesp (first environments) e))
          (execute-consumers (first environments))))
      (execute-pending-consumers)))
  (unless (zerop size)
    (execute-consumers e)
    (execute-pending-consumers e)))