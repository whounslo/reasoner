;;; Copyright (C) 2009, 2011, 2012 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; Missionaries-and-cannibals problem
;;;
;;; Requires plan.lisp

(in-package :rs-user)

(eval-when (:execute :compile-toplevel :load-toplevel)
  (import '(rs::pooledp
            rs::make-instances
            rs::state
            rs::intermediate-state-p
            rs::plan
            rs::describe-plan)))

(defrange numbers-of-crew 0 2)

(defclass place ()
  ())

(defclass physical-object ()
  ((location :type place :count location-count)
   (location-count :type exactly-one)              ; An object cannot be in two
                                                   ; places at once.
   ))

(defclass river ()
  ((near-bank :type river-bank)
   (far-bank :type river-bank)))

(defclass river-bank (place)
  ((missionary-occupants :type missionary)
   (cannibal-occupants :type cannibal)))

(defclass rowing-boat (place physical-object)
  ((crew :type traveller :count number-of-crew)
   (number-of-crew :type numbers-of-crew)))

(defclass traveller (physical-object)
  ())

(defclass missionary (traveller)
  ())

(defclass cannibal (traveller)
  ())

(defmethod pooledp ((m1 missionary) (m2 missionary))
  (not nil))

(defmethod pooledp ((c1 cannibal) (c2 cannibal))
  (not nil))

(defrule embark :assume ((r river)
                         (b river-bank)
                         (rb rowing-boat)
                         (t traveller))
  r near-bank is b and
  rb location is b and
  t location is b
  -> t location is rb)

(defrule embarked ((rb rowing-boat)
                   (t traveller))
  t location is rb -> rb crew includes t)

(defrule row-outward :assume ((r river)
                              (nb river-bank)
                              (fb river-bank)
                              (rb rowing-boat))
  r near-bank is nb and
  r far-bank is fb and
  rb location is nb and
  rb number-of-crew > 0
  -> rb location is fb)

(defrule row-back :assume ((r river)
                           (nb river-bank)
                           (fb river-bank)
                           (rb rowing-boat))
  r near-bank is nb and
  r far-bank is fb and
  rb location is fb and
  rb number-of-crew > 0
  -> rb location is nb)

(defrule disembark :assume ((r river)
                            (b river-bank)
                            (rb rowing-boat)
                            (t traveller))
  r far-bank is b and
  rb location is b and
  t location is rb
  -> t location is b)

(defrule disembarked-1 ((b river-bank)
                        (m missionary))
  m location is b -> b missionary-occupants includes m)

(defrule disembarked-2 ((b river-bank)
                        (c cannibal))
  c location is b -> b cannibal-occupants includes c)

(defun cannibalism-free-p (number-of-missionaries number-of-cannibals)
  (or (zerop number-of-missionaries)
      (<= number-of-cannibals number-of-missionaries)))
                                                   ; Cannibals must never outnumber
                                                   ; missionaries.

(defun miss-operators ()
  (mapcar #'find-instance '(embark row-outward row-back disembark)))

(defun miss (&key (verbose t))
  (let ((river (make-instance 'river))
        (near-bank (make-instance 'river-bank :name 'near-bank))
        (far-bank (make-instance 'river-bank :name 'far-bank))
        (boat (make-instance 'rowing-boat :name 'rowing-boat-1))
        (missionaries (make-instances 'missionary 3 ()))
        (cannibals (make-instances 'cannibal 3 ()))
        plan)
    (flet ((miss-initial-state ()
             (make-instance 'state
               :environment
               (uniquify-environment *atms*
                                     (nconc (assume-slot-values river
                                                                `(near-bank ,near-bank
                                                                  far-bank ,far-bank)
                                                                (make-assumption *atms*))
                                            (mapcar #'(lambda (object)
                                                        (assume-slot-value object
                                                                           'location
                                                                           near-bank))
                                                    (cons boat (append missionaries
                                                                       cannibals)))))))
           (miss-goal ()
             (uniquify-environment *atms*
                                   (mapcar #'(lambda (object)
                                               (assume-slot-value object
                                                                  'location
                                                                  far-bank))
                                     (append missionaries cannibals))))
           (miss-intermediate-state-p (environment path)
             (declare (ignore path))
             (let ((bank (first (slot-value-reduce boat 'location environment))))
               (cannibalism-free-p (length (slot-value-reduce bank
                                                              'missionary-occupants
                                                              environment))
                                   (length (slot-value-reduce bank
                                                              'cannibal-occupants
                                                              environment))))))
      (setq plan (plan (miss-initial-state) (miss-goal) (miss-operators)
                       :intermediate-test #'miss-intermediate-state-p))
      (if (and plan verbose)
          (describe-plan plan)
        plan))))