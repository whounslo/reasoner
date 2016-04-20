;;; Copyright (C) 2011, 2012, 2014 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; Events and temporal reasoning
;;;
;;; Requires pref.lisp

(in-package :rs-user)

(eval-when (:execute :compile-toplevel :load-toplevel)
  (import 'rs::find-preferred-extension))

(defclass event ()
  ((time-interval :type time-range :initarg :time-interval :initarg :date)
   (before :type event :count number-of-events-before)
   (number-of-events-before :type zero-or-more)))

(defrange time-range 0 big)

(defclass chronology ()
  ((events :type event)))

(defclass person (compound-object)
  ())

(defclass professional (part)
  ((rank :type symbolic-range)
   (career-history :initarg :career-history :type chronology))
  (:default-initargs
   :career-history (make-instance 'chronology)))

(defclass academic (professional)
  ((rank :type academic-ranks)))

(eval-when (:execute #+lispworks :compile-toplevel :load-toplevel)
(defrange academic-ranks research-student lecturer senior-lecturer professor)
)

(defclass graduation (event)
  ())

(defclass professional-advancement (event)
  ((to :type symbolic-range)))

(defclass professional-appointment (professional-advancement)
  ())

(defclass professional-promotion (professional-advancement)
  ((from :type symbolic-range)))

(defclass academic-advancement (professional-advancement)
  ((to :type academic-ranks :initarg :to)))

(defclass academic-appointment (academic-advancement
                                professional-appointment)
  ())

(defclass academic-promotion (academic-advancement
                              professional-promotion)
  ((from :type academic-ranks :initarg :from)))

(defrule event-precedence ((e1 event)
                           (e2 event))
  e2 time-interval > e1 time-interval
  -> e2 before includes e1)

(defrule appointed :assume ((p professional)
                            (c chronology)
                            (e professional-appointment))
  p career-history is c
  and c events includes e
  -> p rank is e to)

(defrule advancement-precedence-1 ((e1 professional-advancement)
                                   (e2 professional-promotion))
  e2 from is e1 to
  -> e2 before includes e1)

(defrule advancement-precedence-2 ((e1 professional-advancement)
                                   (e2 professional-advancement)
                                   (e3 professional-promotion))
  e3 from is e2 to
  and e2 before includes e1
  -> e3 before includes e1)

(defrule promoted :assume ((p professional)
                           (c chronology)
                           (e1 professional-appointment)
                           (e2 professional-promotion))
  p career-history is c
  and c events includes e2
  and e2 before includes e1
  -> p rank is e2 to)

(defrule advanced :assume ((p professional)
                           (c chronology)
                           (e professional-advancement))
  p career-history is c
  and c events includes e
  and e number-of-events-before > 0
  -> p rank is e to)

(defvar *ruleset1* (mapcar #'find-instance '(appointed promoted)))

(defvar *ruleset2* (mapcar #'find-instance '(advanced)))

(defun date (day month year)
  (encode-universal-time 0 0 0 day month year))

(defmethod date-of ((e event) environment)
  (let ((universal-time (range-min (slot-value-reduce e 'time-interval environment))))
    (if (zerop universal-time)
        nil
      (nthcdr 3 (multiple-value-list (decode-universal-time universal-time))))))

(defun assimilate-events (object slot-name chronology arglists antecedents rules)
  (let (assumption event
        (premises (nconc (mapcar #'instance-assumption rules) antecedents))
        (choices nil))
    (dolist (args arglists)
      (setq assumption (make-assumption *atms*)
            event (apply #'make-instance (first args)
                                         :antecedents (list assumption)
                                         (rest args)))
      (push assumption premises)
      (push (assume-slot-value chronology 'events event) choices)
      (format t "Assimilated ~A event~@[ of ~1{~A/~A/~A~}~] - ~
                 ~A is~{ ~A~^~#[~; or~:;,~]~}~%"
                (first args)
                (date-of event premises)
                slot-name
                (slot-value-reduce object
                                   slot-name
                                   (find-preferred-extension object
                                                             slot-name
                                                             premises
                                                             choices))))))

;;; Example 1: event sequence

(defvar *career1* '((academic-appointment :to lecturer)
                    (academic-promotion :to senior-lecturer :from lecturer)
                    (academic-promotion :to professor :from senior-lecturer)))

;;; Example 2: events are dated, out-of-order

(defvar *career2* `((graduation :date ,(date 29 7 1966))
                                               ; Baseline event.
                    (academic-promotion :to senior-lecturer :date ,(date 27 9 1973))
                    (academic-appointment :to research-student :date ,(date 9 8 1966))
                    (academic-appointment :to lecturer :date ,(date 10 5 1970))
                    (academic-promotion :to professor :date ,(date 1 6 1975))))

(let* ((antecedents (list (make-assumption *atms*)))
       (academic (make-instance 'person
                                :part (make-instance 'academic
                                        :antecedents antecedents))))
  (defun career1 ()
    (assimilate-events academic
                       'rank
                       (first (slot-value-reduce academic 'career-history t))
                       *career1*
                       antecedents
                       *ruleset1*))

  (defun career2 ()
    (assimilate-events academic
                       'rank
                       (first (slot-value-reduce academic 'career-history t))
                       *career2*
                       antecedents
                       *ruleset2*))
) ;end let* antecedents