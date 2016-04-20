;;; Copyright (C) 2007, 2009-11 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; n-queens problem
;;;
;;; Requires combin.lisp

(in-package :rs-user)
(eval-when (:execute :compile-toplevel :load-toplevel)
  (import '(atms:assumed-datum
            atms:oneof-disjunction
            rs::place-randomly
            rs::find-assumed-value
            rs::min-conflicts)))

(defclass board ()
  ((queens :type queen)))

(defclass queen ()
  ((rank-number :type queen-coord)
   (file-number :type queen-coord)))

(defrange queen-coord 1 big)

(defun attackp (col1 row1 col2 row2)
  (or (= row2 (- row1 (- col2 col1)))
      (= row2 (+ row1 (- col2 col1)))))
      
(defmethod added-assumption ((q queen) (a assumption) (assumptions list))
  (let ((col (find-assumed-value a 'rank-number t))
        (row (find-assumed-value a 'file-number)))
    (dolist (assumption assumptions)
      (unless (conflictp a assumption)         ; Note: local search only.
        (when (attackp (range-min col)
                       (range-min row)
                       (range-min (find-assumed-value assumption 'rank-number t))
                       (range-min (find-assumed-value assumption 'file-number)))
          (add-contradiction (list (assumed-datum a)
                                   (assumed-datum assumption))))))))

(let (board a)
  
  (defun make-board ()
    (setq a (make-assumption *atms*)
        board (make-instance 'board)))

  (defmethod initialize-instance :after ((q queen) &rest initargs)
    (assume-slot-value board 'queens q a)
    (assume-slot-values q initargs a))
  
  (defun print-board (solution)
    (let* ((queens (slot-value-reduce board 'queens t))
           (n (length queens))
           queen
           rank-number)
      (unless queens (return-from print-board nil))
      (dotimes (row n)
        (setq queen (find (1+ row) queens :key #'(lambda (queen)
                                                   (range-min
                                                    (slot-value-reduce queen
                                                                       'file-number
                                                                       solution))))
            rank-number (range-min (slot-value-reduce queen 'rank-number t)))
        (dotimes (column n)
          (princ (if (= (1+ column) rank-number)
                     " X |"
                   "   |")))
        (terpri)
        (dotimes (column n)
          (princ "----"))
        (terpri))
      solution))
  ) ;end let board

;;; n-queens (backtracking search)
  
(defun queens (&optional (n 8) &key (verbose t))
  (let (queen a control-disjunctions
        (rows (make-list n))
        stream)
    (make-board)
    (dotimes (column n)
      (let ((d (make-list n)))
        (setq queen (make-instance 'queen 'rank-number (1+ column)))
        (dotimes (row n)
          (setq a (assume-slot-value queen 'file-number (1+ row)))
          (place-randomly a d n)
          (push a (nth row rows)))
        (push d control-disjunctions)))
    (mapc #'oneof-disjunction rows)
                                               ; Stipulate only one queen per
                                               ; row.
    (setq stream (backtrack (uniquify-environment *atms* nil)
                            (nreverse control-disjunctions)
                                               ; Stipulate only one queen per
                                               ; column.
                            *atms*))
    (if verbose
        (print-board (head stream))
      stream)))

;;; n-queens (local search)
;;;
;;; Initially assign queens randomly one per column, and in different rows.
;;; Repeatedly swap pairs of queens' rows.

(defun queens2 (&optional (n 8) &key (verbose t))
  (flet ((queen-row (assumption)
           (find-assumed-value assumption 'file-number))
         (reassign-queen (queen row)
           (or (fetch-assumption queen 'file-number row)
               (assume-slot-value queen 'file-number row))))
    (let ((assumptions (make-list n))
          (row 0)
          solution)
      (make-board)
      (dotimes (column n)
        (place-randomly (make-instance 'queen 'rank-number (1+ column))
                        assumptions
                        n))
      (map-into assumptions
                #'(lambda (queen)
                    (assume-slot-value queen 'file-number (incf row)))
                assumptions)
      (setq solution (min-conflicts assumptions #'queen-row #'reassign-queen))
      (if (and solution verbose)
          (print-board solution)
        solution))))