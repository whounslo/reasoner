;;; Copyright (C) 2009-11, 2013, 2016-17 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; Sudoku puzzle generator and solver
;;;
;;; Requires combin.lisp

(in-package :rs-user)
(eval-when (:execute :compile-toplevel :load-toplevel)
  (import '(streams:map-stream
            atms:contras
            atms:assumed-datum
            atms:oneof-disjunction
            atms:add-assumption
            rs::combine
            rs::range-set-elements
            rs::place-randomly
            rs::find-assumed-value
            rs::map-elements
            rs::max-steps
            rs::min-conflicts)))

(defrange su-coord 0 8)

(defrange su-values 1 9)

(defclass su-cell ()
  ((row :type su-coord)
   (col :type su-coord)
   (value :type su-values)))

(defclass su-cell-g (su-cell)
  ())

(defclass su-cell-s (su-cell)
  ())

(defclass su-division ()
  ((cells :type su-cell)))

(defclass su-row (su-division)
  ((index :type su-coord)))

(defclass su-column (su-division)
  ())

(defclass su-box (su-division)
  ())

(defclass sudoku-puzzle ()
  ((rows :type su-row)))

(defconstant su-dimension 9)

(defconstant su-box-dimension 3)

(defun box-index (index)
  (truncate index su-box-dimension))

(defun assigned-value-p (cell-value)
  (eql (range-min cell-value) (range-max cell-value)))

(let (puzzle a)
  
  (defun make-rows (&aux su-row rows)
    (setq puzzle (make-instance 'sudoku-puzzle)
        a (make-assumption *atms*))
    (dotimes (i su-dimension)
      (setq su-row (make-instance 'su-row))
      (assume-slot-value su-row 'index i a)
      (assume-slot-value puzzle 'rows su-row a)
      (push su-row rows))
    (nreverse rows))
  
  (defmethod initialize-instance :after
    ((c su-cell) &key col-index row-index rows (columns nil) (boxes nil))
    (when boxes
      (assume-slot-value (nth (box-index col-index)
                              (nth (box-index row-index) boxes))
                         'cells
                         c
                         a))
    (when columns
      (assume-slot-value (nth col-index columns)
                         'cells
                         c
                         a))
    (assume-slot-value (nth row-index rows)
                       'cells
                       c
                       a)
    (assume-slot-values c
                        `(col ,col-index row ,row-index)
                        a))
  
  (defun read-puzzle (pathname rows columns boxes)
    (let ((success nil)
          l assumptions)
      (ignore-errors
       (with-open-file (s pathname)
         (dotimes (row su-dimension)
           (setq l (read-line s))
           (dotimes (col su-dimension)
             (let ((cell (make-instance 'su-cell-s
                           :col-index col
                           :row-index row
                           :rows rows
                           :columns columns
                           :boxes boxes))
                   (value (if (char/= (char l col) #\-)
                              (- (char-code (char l col))
                                 (char-code #\0)))))
               (when value
                 (push (assume-slot-value cell 'value value)
                       assumptions))))))
       (setq success (not nil)))
      (format t "~:[Failed to read~;Read~] ~A.~%" success pathname)
      (when success
        (cons a assumptions))))

  (defun print-puzzle (environment
                       &optional (hide-cells nil) (stream *standard-output* redirect))
    (flet ((inner-edge-p (index)
             (if (< (1+ index) su-dimension)
                 (zerop (rem (1+ index) su-box-dimension))))
           (print-referenced-value (char value)
             (format stream "~C=~:[~{~{~D~:*~v,v^-~:*~D~}~#[~:;,~]~}~;~{~D-~D~}~]~%"
               char
               (numeric-rangep value)
               (if (numeric-rangep value) value (range-set-elements value)))))
      (let ((rows (slot-value-reduce puzzle 'rows t))
            (ref-char (char-code #\A))
            referenced-values
            (i 0))
        (unless rows (return-from print-puzzle nil))
        (dotimes (row-index su-dimension)
          (let* ((su-row (find row-index rows
                               :key #'(lambda (su-row)
                                        (range-min
                                         (slot-value-reduce su-row 'index t)))))
                 (cells (slot-value-reduce su-row 'cells t)))
            (dotimes (col-index su-dimension)
              (let (su-cell value cell-value)
                
                ;; Hide approximately two-thirds of the cells.
                (unless (and hide-cells (plusp (random 3)))
                  (setq su-cell (find col-index cells
                                      :key #'(lambda (su-cell)
                                               (range-min
                                                (slot-value-reduce su-cell 'col t))))
                      value (slot-value-reduce su-cell 'value environment)
                      cell-value (if (assigned-value-p value)
                                     (digit-char (range-min value))))
                  (unless (or cell-value
                              (eq value (slot-value-reduce su-cell 'value nil)))
                    (setq cell-value (code-char (+ ref-char i)))
                    (incf i)
                    (push value referenced-values)))
                (unless cell-value
                  (setq cell-value (if redirect #\- #\ )))
                (format stream "~:[ ~C |~;~C~]" redirect cell-value)))
            (terpri stream)
            (unless redirect
              (dotimes (col-index su-dimension)
                (princ (if (and (inner-edge-p row-index)
                                (inner-edge-p col-index))
                           "---+"
                         "----")))
              (terpri stream))))
        (setq referenced-values (nreverse referenced-values))
        (dotimes (j i)
          (print-referenced-value (code-char (+ ref-char j))
                                  (pop referenced-values)))
        environment)))
  ) ;end let puzzle

(defun cell-clash-p (col-index-1 row-index-1 value-1 col-index-2 row-index-2 value-2)
  (and (eql value-1 value-2)
       (or (and (eql (box-index col-index-1) (box-index col-index-2))
                (eql (box-index row-index-1) (box-index row-index-2)))
           (eql row-index-1 row-index-2))))

(defmethod added-assumption ((c su-cell-g) (a assumption) (assumptions list) (tms core-atms))
  (let ((col-index (find-assumed-value c 'col))
        (row-index (find-assumed-value c 'row))
        (value (find-assumed-value a 'value)))
    (dolist (assumption assumptions)
      (unless (conflictp a assumption)
        (when (cell-clash-p (range-min col-index)
                            (range-min row-index)
                            (range-min value)
                            (range-min (find-assumed-value assumption 'col t))
                            (range-min (find-assumed-value assumption 'row t))
                            (range-min (find-assumed-value assumption 'value)))
          (add-contradiction tms
                             (list (assumed-datum a)
                                   (assumed-datum assumption))))))))

(defmacro su-compile-truename () `',*compile-file-truename*)

(defvar *su-output-pathname*
    (merge-pathnames (make-pathname :directory '(:relative :back "data")
                                    :name "su" :type "dat")
                     (or (su-compile-truename) *load-truename*)))

(defun write-puzzle (solution pathname)
  (let ((success nil))
    (ignore-errors
     (with-open-file (s pathname :direction :output :if-exists :supersede)
       (print-puzzle solution 'hide-cells s))
     (setq success (not nil)))
    (format t "~:[Failed to write~;Wrote~] ~A.~%" success pathname)
    solution))

;;; Sudoku puzzle generator (local search)
;;;
;;; Initially assign the values 1-9 randomly to each column.
;;; Repeatedly swap pairs of values within the same column.

(defun sugen (&key (pathname *su-output-pathname* pathname-supplied) (verbose t))
  (flet ((cell-value (assumption)
           (find-assumed-value assumption 'value))
         (col-index (assumption)
           (range-min (find-assumed-value assumption 'col t)))
         (reassign-cell-value (cell new-value)
           (or (fetch-assumption cell 'value new-value)
               (assume-slot-value cell 'value new-value))))
    (let ((rows (make-rows))
          assumptions
          solution)
      (dotimes (col su-dimension)
        (let ((column (make-list su-dimension)))
          (dotimes (row su-dimension)
            (place-randomly (1+ row) column su-dimension))
          (dotimes (row su-dimension)
            (setf (nth row column) (assume-slot-value (make-instance 'su-cell-g
                                                        :col-index col
                                                        :row-index row
                                                        :rows rows)
                                                      'value
                                                      (nth row column))))
          (setq assumptions (nconc assumptions column))))
      (setq solution (min-conflicts assumptions
                                    #'cell-value
                                    #'reassign-cell-value
                                    :index-key #'col-index
                                    :top-limit 5))
      (when verbose
        (cond (solution
               (print-puzzle solution)
               (terpri))
              (t (format t "No solution found after ~D steps.~%" max-steps))))
      (when solution
        (if (or pathname-supplied
                (y-or-n-p "Write ~A?" pathname))
            (write-puzzle solution pathname)
          (print-puzzle solution 'hide-cells))))))

(defun make-boxes ()
  (mapl #'(lambda (box-rows)
            (setf (first box-rows) (make-list su-box-dimension
                                              :initial-element 'su-box))
            (map-into (first box-rows) #'make-instance (first box-rows)))
        (make-list su-box-dimension)))

(defun make-columns ()
  (let ((columns (make-list su-dimension
                            :initial-element 'su-column)))
    (map-into columns #'make-instance columns)))

(defmethod validate-combination ((new-node su-values) (node su-values) nodes)
  (eq node (first nodes)))

(defun possible-value-p (su-cell value)
  (combine value (first (slot-values su-cell 'value t))))

(defrule su-value-restriction
         ((r su-row) (c su-column) (b su-box) (c1 su-cell-s) (c2 su-cell-s))
  (r cells includes c1
  and lisp (assigned-value-p c1 value)
  and r cells includes c2
  and c1 col /= c2 col
  or
  c cells includes c1
  and lisp (assigned-value-p c1 value)
  and c cells includes c2
  and c1 row /= c2 row
  or
  b cells includes c1
  and lisp (assigned-value-p c1 value)
  and b cells includes c2
  and c1 col /= c2 col
  and c1 row /= c2 row)
  and lisp (possible-value-p (c2 su-cell-s) c1 value)
                                               ; Inhibit redundant inference.
  -> c2 value /= c1 value)

(defun cell-disjunctions (divisions &optional (no-check t))
  
  ;; Stipulate mutual exclusivity of cells with same value within division.
  (dolist (division divisions)
    (let ((cells (slot-value-reduce division 'cells t)))
      (dotimes (i su-dimension)
        (oneof-disjunction (mapcan #'(lambda (cell)
                                       (let ((assumption
                                              (fetch-assumption cell 'value (1+ i))))
                                         (if assumption
                                             (list assumption))))
                             cells)
                           no-check)))))

(defmethod order-control-disjunction ((c su-cell-s) (e environment) (assumptions list))
  
  ;; Least-constraining-value heuristic: allow for maximum flexibility in the
  ;; making of subsequent choices.
  ;; (Source: Artificial Intelligence: A Modern Approach, Stuart Russell and
  ;; Peter Norvig, Prentice-Hall, 1995.)
  (sort assumptions
        #'(lambda (assumption-1 assumption-2)
            (and (not (conflictp assumption-1 e))
                 (not (conflictp assumption-2 e))
                 (< (length (contras assumption-1))
                    (length (contras assumption-2)))))))

;;; Sudoku puzzle solver (backtracking search)

(defun susolve (&key (pathname *su-output-pathname*) (verbose t))
  (let ((rows (make-rows))
        (columns (make-columns))
        (boxes (make-boxes))
        assumptions
        environment
        control-disjunctions
        stream)
    (setq assumptions (read-puzzle pathname rows columns boxes))
    (when assumptions
      (setq environment (uniquify-environment *atms* assumptions))
      (when verbose
        (print-puzzle environment)
        (terpri))
      (nschedule *atms* environment)

      ;; Guessing phase.
      (dolist (division rows)
        (dolist (cell (slot-value-reduce division 'cells t))
          (let ((value (slot-value-reduce cell 'value environment)))
            (unless (assigned-value-p value)
              (let (disjunction)
                (map-elements value
                              #'(lambda (element)
                                  (push (assume-slot-value cell 'value element)
                                        disjunction)))
                (push disjunction control-disjunctions))))))
      (when control-disjunctions
        (when verbose
          (print-puzzle environment)
          (terpri))
        (cell-disjunctions rows)
        (cell-disjunctions columns)
        (dolist (box-row boxes)
          (cell-disjunctions box-row nil)))
      (setq stream (map-stream #'(lambda (e)
                                   (add-assumption *atms* (first assumptions) e))
                               (backtrack (uniquify-environment *atms*
                                                                (rest assumptions))
                                          control-disjunctions
                                          *atms*)))
      (if verbose
          (print-puzzle (head stream))
        stream))))