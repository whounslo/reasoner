;;; Copyright (C) 2007, 2011 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; Counterfactuals: simple non-monotonic reasoning
;;;
;;; Requires pref.lisp

(in-package :rs-user)

(eval-when (:execute :compile-toplevel :load-toplevel)
  (import 'rs::find-preferred-extension))

(defclass party-attendee ()
  ())

(defclass none-other-than-boris (party-attendee)
  ())

(defclass none-other-than-anna (party-attendee)
  ())

(defrange party-rating dreary lively)

(defclass party ()
  ((attendees :type party-attendee)
   (rating :type party-rating)))

(defrule party-rating-1 :assume ((p party)
                                 (boris none-other-than-boris))
  p attendees includes boris
  -> p rating is lively)

(defrule party-rating-2 :assume ((p party)
                                 (boris none-other-than-boris)
                                 (anna none-other-than-anna))
  p attendees includes boris
  and p attendees includes anna
  -> p rating is dreary)

(defun if-boris ()
  (let ((party (make-instance 'party :name 'party1))
        (boris (make-instance 'none-other-than-boris :name 'boris))
        (anna (make-instance 'none-other-than-anna :name 'anna))
        (boris-attends (make-assumption *atms*))
        (anna-attends (make-assumption *atms*))
        (party-rating-1 (instance-assumption (find-instance 'party-rating-1)))
        (party-rating-2 (instance-assumption (find-instance 'party-rating-2))))

    (flet ((print-counterfactual (e)
             (format t "~&if~{ ~A~^~#[~; and~:;,~]~} had come to the party, ~
                        it would have been~{ ~A~^~#[~; or~:;,~]~}"
                       (mapcar #'instance-name (slot-value-reduce party 'attendees e))
                       (slot-value-reduce party 'rating e))))
  
      (add-slot-value party 'attendees boris boris-attends 'premise)
      (add-slot-value party 'attendees anna anna-attends 'premise)
      (print-counterfactual (find-preferred-extension party
                                                      'rating
                                                      (list boris-attends)
                                                      (list party-rating-1)))
      (print-counterfactual (find-preferred-extension party
                                                      'rating
                                                      (list boris-attends
                                                            anna-attends)
                                                      (list party-rating-1
                                                            party-rating-2))))))