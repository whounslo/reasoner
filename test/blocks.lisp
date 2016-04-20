;;; Copyright (C) 2007, 2009, 2011-13 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; Blocks-world planning
;;;
;;; Requires plan.lisp

(in-package :rs-user)

(eval-when (:execute :compile-toplevel :load-toplevel)
  (import '(rs::make-instances
            rs::state
            rs::plan
            rs::describe-plan
            rs::omit-from-state-p
            rs::pooledp)))

(defclass supporting-object ()
  ((supporting :type supported-object)))

(defclass supported-object ()
  ((on :type supporting-object :count number-of-supporting-objects :inverse supporting)
   (number-of-supporting-objects :type zero-or-one)
   (firmly-supported :type true-or-false)
   (held-by :type robot-hand :count number-of-hands-holding)
   (number-of-hands-holding :type zero-or-one)))

(defclass toy-block (supporting-object supported-object)
  ((supporting :type supported-object :count number-of-supported-objects)
   (number-of-supported-objects :type zero-or-one)
   (clear :type true-or-false)))

(defclass table (supporting-object)
  ())

(defclass robot-hand ()
  ((above :type table)
   (holding :type toy-block :count number-of-blocks-held :inverse held-by)
   (number-of-blocks-held :type zero-or-one)))

(defrule block-pickup :assume ((b toy-block)
                               (so supporting-object)
                               (h robot-hand)
                               (t table))
  h above t
  and b on so
  and b clear is true
  -> h holding b)

;;; Governs both picking up and releasing behaviour.
(defrule block-picked ((b1 toy-block)
                       (b2 toy-block)
                       (h robot-hand))
  b1 on b2 and h holding b1 -> b2 clear is true)

;;; Governs both picking up and releasing behaviour.
(defrule block-released ((b toy-block)
                         (h robot-hand)
                         (t table))
  b on t and h holding b -> not t supporting b)

(defmethod omit-from-state-p ((so supporting-object) (slot-name (eql 'supporting)))
  (not nil))

(defrule block-putdown :assume ((b toy-block)
                                (h robot-hand)
                                (t table))
  h above t and h holding b -> b on t)

(defrule block-firm ((b1 toy-block)
                     (b2 toy-block)
                     (t table))
  (b1 on b2 and b2 firmly-supported is true)
  or b1 on t
  -> b1 firmly-supported is true)

(defrule block-stack :assume ((b1 toy-block)
                              (b2 toy-block)
                              (h robot-hand))
  h holding b1
  and b2 firmly-supported is true
  and b2 clear is true
  -> b1 on b2)

(defrule block-stacked ((b toy-block))
  b number-of-supported-objects > 0 -> b clear is false)

(defmethod pooledp ((h1 robot-hand) (h2 robot-hand))
  (not nil))

(defun blocks-operators ()
  (mapcar #'find-instance '(block-pickup block-putdown block-stack)))

(defun blocks (&key (verbose t) (twin-hands nil))
  (let ((table (make-instance 'table :name 'table-1))
        (blocks (make-instances 'toy-block 3 ()))
        (robot-hands (make-instances 'robot-hand (if twin-hands 2 1) ()))
        plan)
    (flet ((blocks-initial-state ()
             (make-instance 'state
               :environment
               (uniquify-environment *atms*
                                     (mapcan #'assume-slot-values
                                             (append blocks robot-hands)
                                             `((on ,table)
                                               (on ,table clear true)
                                               (on ,(first blocks) clear true)
                                               (above ,table)
                                               (above ,table))))))
           (blocks-goal ()
             (uniquify-environment *atms*
                                   (mapcan #'assume-slot-values
                                           blocks
                                           `((on ,(second blocks))
                                             (on ,(third blocks))
                                             (on ,table))))))
      (setq plan (plan (blocks-initial-state) (blocks-goal) (blocks-operators)))
      (if (and plan verbose)
          (describe-plan plan)
        plan))))