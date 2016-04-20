;;; Copyright (C) 2007-2009, 2011 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; Graphsearch planning
;;;
;;; Graphsearch adapted from: ANSI Common Lisp by Paul Graham, Prentice Hall, 1996.


(in-package reasoner)

(declaim (special *expansion-count*))

(defclass state ()
  ((environment :accessor environment :initarg :environment)
   (depth :reader depth :initarg :depth :initform 0)
   (cost :accessor cost)
   (all-environments :accessor all-environments
                     :initarg :all-environments
                     :initform nil)
   (environments-fn :reader environments-fn
                    :initarg :environments-fn
                    :initform (constantly nil))))

(defmethod describe-state ((s state))
  (describe-data (environment s)))

(defmethod cost-to-goal ((s state) (goal environment) &optional path)
  (let ((goal-assumptions (assumptions goal))
        (environment (next-environment s))
        (fleshed-out (not nil))
        in-position-count)
    (unless environment
      (setq environment (environment s)
          fleshed-out nil))
    (setq in-position-count (count-if #'(lambda (assumption)
                                          (find assumption
                                                goal-assumptions
                                                :test #'eq))
                                      (assumptions environment)))
    (if (or fleshed-out (null path))
        (- (size goal) in-position-count)
      (- (cost-to-goal (first path) goal) in-position-count))))

(defparameter heuristic-weighting 2)

(defmethod estimated-cost ((s state) (goal environment) &optional path)

  ;; Evaluation function given by
  ;;
  ;; f = g + wh,
  ;;
  ;; where g is the depth of the search tree, h an estimate of the cost of a minimal
  ;; path to the goal, and w a positive number. Smaller values of w tend toward
  ;; breadth-first search; greater values emphasize the heuristic component.
  ;; (Source: Principles of Artificial Intelligence, Nils J. Nilsson, Tioga, 1980.)
  (+ (depth s)
     (* heuristic-weighting (cost-to-goal s goal path))))

(defmethod next-environment ((s state))
  (with-accessors ((environment environment)
                   (environments all-environments))
      s
    (if environments
        (let ((rest-environments (member environment environments :test #'eq)))
          (if rest-environments
              (second rest-environments)
            
            ;; Look-ahead generated the fleshed-out environment(s) but
            ;; the original, partial, version has not yet been replaced.
            (first environments))))))

(defmethod fetch-environment ((s state) &optional tentative)
  (with-accessors ((environment environment)
                   (environments all-environments)
                   (fn environments-fn))
      s
    (unless environments
      (setf environments (funcall fn))
      (unless environments
        (return-from fetch-environment environment)))
    (let ((next-environment (next-environment s)))
      (when next-environment
        (setq next-environment (ensure-environment *atms*
                                                   next-environment
                                                   'ordered))
        (unless tentative
          (setf environment next-environment)))
      next-environment)))

(defun decompose1 (object assumptions)
  (remove object
          assumptions
          :key #'(lambda (assumption)
                   (datum-object (assumed-datum assumption)))
          :test-not #'eq))

;;; decompose partitions assumptions describing a state according to
;;; the object to which their assumed datum refers.

(defun decompose (assumptions)
  (let (objects)
    (dolist (assumption assumptions)
      (pushnew (datum-object (assumed-datum assumption)) objects :test #'eq))
    (mapcar #'(lambda (object)
                (decompose1 object assumptions))
      objects)))

(defun all-solutions-internal (old-component new-component catchall-assumption)
  (solutions (uniquify-environment *atms*
                                   (if catchall-assumption
                                       (cons catchall-assumption
                                             new-component)
                                     new-component))
             old-component
             *atms*
             'dont-create))

;;; all-solutions uses the sets of assumptions produced by decompose
;;; to vivify a similarly-partitioned list of new assumptions that are
;;; the consequents of actions and auxiliary rules, based on the intuition
;;; that the consequences of actions are local to the objects they affect.

(defun all-solutions
    (assumption-sets new-assumptions catchall-assumption &aux extra-new extra-old)
  (setq extra-new
        (set-difference new-assumptions
                        assumption-sets
                        :test #'(lambda (assumption set)
                                  (eq (datum-object
                                       (assumed-datum
                                        assumption))
                                      (datum-object
                                       (assumed-datum
                                        (car set)))))))
  (when (and extra-new catchall-assumption)
    (push catchall-assumption extra-new))
  (nconc (if extra-new
             (list (list extra-new)))              ; New assumptions that have no
                                                   ; corresponding old component
                                                   ; just pass straight through.
         (mapcan #'(lambda (old-component &aux new-component)
                     (setq new-component
                           (decompose1 (datum-object
                                        (assumed-datum
                                         (car old-component)))
                                       new-assumptions))
                     (cond (new-component
                            (list (all-solutions-internal old-component
                                                          new-component
                                                          catchall-assumption)))
                           
                           ;; No corresponding new component; merge with
                           ;; all new assumptions.
                           (t (setq extra-old (nconc extra-old old-component))
                              nil)))
           assumption-sets)
         (let (solutions)
           (setq solutions
                 (mapcar #'(lambda (solution)
                             (nconc (if catchall-assumption
                                        (list catchall-assumption))
                                    (intersection extra-old
                                                  (assumptions solution)
                                                  :test #'eq)))
                   (all-solutions-internal extra-old
                                           new-assumptions
                                           catchall-assumption)))
           (if solutions
               (list solutions)))))

;;; join-solutions reassembles the solution fragments produced by all-solutions
;;; into one or more full descriptions of successor states.

(defun join-solutions (solution-sets)
  (mapcar #'(lambda (environments)
              (union-environments *atms* environments))
    (cross-product solution-sets)))

(defun find-successor-nodes
    (environment antecedents &optional (all-antecedents nil progressed) past-environments)
  (flet ((successorp (consequent antecedents)
           (not (or (contradictoryp consequent)
                    (typep consequent 'temporary-node)
                    (typep (datum-object consequent)
                           'well-formed-formula)
                    (member consequent
                            all-antecedents
                            :test #'eq)
                    (notevery #'(lambda (node)
                                  (or (typep (datum-object node)
                                             'well-formed-formula)
                                      (in-p node environment)
                                      (some #'(lambda (e)
                                                (in-p node e))
                                            past-environments)))
                              antecedents))))
         (operatorp (node &aux (object (datum-object node)))
           (and (typep object 'well-formed-formula)
                (instance-assumption object))))
    (delete-duplicates (mapcan #'(lambda (antecedent)
                                   (mapcan #'(lambda (justification)
                                               (with-slots (consequent antecedents)
                                                   justification
                                                 (cond ((not (successorp consequent
                                                                         antecedents))
                                                        nil)
                                                       ((and progressed
                                                             (find-if #'operatorp
                                                                      antecedents))
                                                   ; Parallel operator applications
                                                   ; only: is consequent the result of
                                                   ; successive applications of a
                                                   ; single operator?
                                                        nil)
                                                       (t
                                                        (list consequent)))))
                                     (consequents antecedent)))
                         antecedents)
                       :test #'eq)))

(defmethod omit-from-state-p ((object t) (slot-name t))
  nil)

(defun make-new-assumptions (environment successor-nodes &optional added-assumptions)
  (mapcan #'(lambda (consequent &aux assumption)
              (cond ((in-p consequent environment)
                     nil)
                    ((omit-from-state-p (datum-object consequent)
                                        (datum-slot consequent))
                     nil)
                    (t
                     (setq assumption (datum-assumption consequent 'oldest))
                     (unless assumption
                       (setq assumption (make-assumption *atms*))
                       (add-justification *atms*
                                          consequent
                                          (list assumption)
                                          'premise))
                     (cond ((member assumption
                                    added-assumptions
                                    :test #'eq)
                            nil)
                           ((add-assumption *atms*
                                            assumption
                                            added-assumptions
                                            'dont-create)
                            (list assumption))))))
    successor-nodes))

(defmethod pooledp ((object-1 t) (object-2 t))
  nil)

(defmethod pooledp ((n1 standard-slot-value) (n2 standard-slot-value))
  (if (eq (datum-slot n1) (datum-slot n2))
      (let ((object-1 (datum-object n1))
            (object-2 (datum-object n2))
            (value-1 (datum-value n1))
            (value-2 (datum-value n2)))
        (or (and (eq value-1 value-2)
                 (pooledp object-1 object-2))
            (and (eq object-1 object-2)
                 (pooledp value-1 value-2))))))

(defmethod pooledp ((a1 assumption) (a2 assumption))
  (pooledp (assumed-datum a1) (assumed-datum a2)))

(defun seed-environments (assumptions new-assumptions &optional (progressed nil))
  (nschedule *atms*
             (uniquify-environment *atms*
                                   (append assumptions
                                           new-assumptions)))
  (if progressed

      ;; Operator ramifications.
      (solutions *empty-environment*
                 new-assumptions
                 *atms*
                 'dont-create)

    ;; Operator. If parallel operator applications are possible, generate
    ;; subsets as well, removing variants indicated by a POOLEDP method.
    (delete-duplicates (schedule *atms*
                                 (uniquify-environment *atms*
                                                       new-assumptions))
                       :test #'(lambda (e1 e2)
                                 (if (eql (size e1) (size e2))
                                     (subsetp (assumptions e1)
                                              (assumptions e2)
                                              :test #'pooledp))))))

(defun vivify (environment past-environment &optional added-assumptions)
  (let* ((assumptions (assumptions past-environment))
         ;; A single assumption may be used to justify all data which
         ;; participates in inferences but is known a priori to be
         ;; unchanging from state to state.
         (catchall-assumption (find-if-not #'singletonp
                                           assumptions
                                           :key #'consequents)))
    (when catchall-assumption
      (setq assumptions (remove catchall-assumption assumptions :test #'eq)))
    (join-solutions (all-solutions (decompose (set-difference assumptions
                                                              added-assumptions
                                                              :test #'eq))
                                   (append (assumptions environment)
                                           added-assumptions)
                                   catchall-assumption))))

(defun progress-all (environments past-environments successor-nodes new-assumptions
                     &optional all-antecedents added-assumptions)
  (or (mapcan #'(lambda (environment)
                  (let ((nodes
                         (remove-if-not #'(lambda (consequent)
                                            (in-p consequent
                                                  environment))
                                        successor-nodes)))
                    (progress environment
                              past-environments
                              nodes
                              (append all-antecedents nodes)
                              (append added-assumptions
                                      (intersection new-assumptions
                                                    (assumptions
                                                     environment)
                                                    :test #'eq)))))
        environments)
      environments))

(defmethod progress ((e environment) past-environments antecedents
                     &optional all-antecedents added-assumptions)
  (let* ((successor-nodes (find-successor-nodes e
                                                antecedents
                                                all-antecedents
                                                past-environments))
         (new-assumptions (make-new-assumptions e
                                                successor-nodes
                                                added-assumptions)))
    (if new-assumptions
        (progress-all (mapcan #'(lambda (environment)
                                  (vivify environment e added-assumptions))
                        (seed-environments (assumptions e)
                                           new-assumptions
                                           'progressed))
                      (cons e past-environments)
                      successor-nodes
                      new-assumptions
                      all-antecedents
                      added-assumptions))))

(defmethod progress-delayed ((initial-state state) antecedents)
  (with-accessors ((environment environment)
                   (depth depth))
      initial-state
    (let* ((successor-nodes (find-successor-nodes environment
                                                  antecedents))
           (new-assumptions (make-new-assumptions environment
                                                  successor-nodes)))
      (mapcar #'(lambda (seed-environment)
                  (make-instance (class-of initial-state)
                    :depth (1+ depth)
                    :environment seed-environment
                    :environments-fn
                    #'(lambda ()
                        (progress-all (vivify seed-environment environment)
                                      (list environment)
                                      successor-nodes
                                      new-assumptions))))
        (seed-environments (assumptions environment) new-assumptions)))))

(defmethod progress-through ((initial-state state) (action forward-rule))
  (nschedule *atms* (add-assumption *atms*
                                    (instance-assumption action)
                                    (environment initial-state)
                                    nil
                                    'no-check))
  (progress-delayed initial-state
                    (slot-values action 'source-form t)))

(defmethod repeated-state-p ((s state) path repetition-test)
  (let ((environment (environment s))
        full-environment)
    (map-plan #'(lambda (previous-state)
                  (with-accessors ((e environment))
                      previous-state
                    (unless full-environment
                      (when (subsumesp environment e)
                        (setq full-environment (fetch-environment s 'tentative))))
                    (when full-environment
                      (when (funcall repetition-test full-environment e)
                        (return-from repeated-state-p (not nil))))))
              path)))

(defun new-paths (path initial-state operators goal repetition-test)
  (incf *expansion-count*)
  (mapcan #'(lambda (operator)
              (mapcar #'(lambda (state)
                          (setf (cost state) (estimated-cost state goal path))
                          (list* state operator path))
                (delete-if #'(lambda (state)
                               (repeated-state-p state path repetition-test))
                           (progress-through initial-state operator))))
    operators))

(defvar *trace-graphsearch* nil)

(defmacro trace-graphsearch (state)
  `(when *trace-graphsearch*
     (format t "~&[~D:~D]" *expansion-count* (depth state))
     (describe-state ,state)
     (when (multiple-value-bind (quotient remainder)
               (truncate *expansion-count* 5)
             (and (plusp quotient) (zerop remainder)))
       (unless (y-or-n-p "Continue?")
         (return-from graphsearch nil)))))

(defmethod intermediate-state-p ((s state) path intermediate-test)
  (unless path
    (return-from intermediate-state-p (not nil)))
  (do ((environment (environment s) (fetch-environment s))
       (previous-environment (environment (car path))))
      ((null environment) nil)
    (when (and (subsetp (assumptions previous-environment)
                        (assumptions environment)
                        :key #'(lambda (a) (datum-object (assumed-datum a))))
                                                   ; No entities clobbered (by
                                                   ; multiple application of an
                                                   ; operator)?
               (funcall intermediate-test environment path))
      (return (not nil)))))

(defun graphsearch (goal queue operators goal-test intermediate-test repetition-test)
  (if (null queue)
      nil
    (let* ((path (car queue))
           (state (car path))
           (environment (fetch-environment state)))
      (if (funcall goal-test goal environment path)
          (reverse path)
        (let ((expandable (intermediate-state-p state
                                                (rest-path path)
                                                intermediate-test)))
          (when expandable
            (trace-graphsearch state))
          (graphsearch goal
                       (if expandable
                           (sort (append (if (next-environment state)
                                             queue
                                           (cdr queue))
                                         (new-paths path
                                                    state
                                                    operators
                                                    goal
                                                    repetition-test))
                                 #'<
                                 :key #'(lambda (path)
                                          (cost (car path))))
                         (cdr queue))
                       operators
                       goal-test
                       intermediate-test
                       repetition-test))))))

(defun plan (initial-state goal operators &key (goal-test
                                                 #'(lambda (goal environment path)
                                                     (declare (ignore path))
                                                     (subsumesp goal environment)))
                                               (intermediate-test (constantly t))
                                               (repetition-test #'eq))
  (setq *expansion-count* 0)
  (graphsearch goal
               (list (list initial-state))
               operators
               goal-test
               intermediate-test
               repetition-test))

(defun rest-path (path)
  (cddr path))

(defun map-plan (fn path)
  (do ((rest-path path (cddr rest-path)))
      ((endp rest-path) nil)
    (funcall fn (car rest-path))))

(defun describe-plan (path)
  (describe-state (car path))                   ; Initial state.
  (do ((rest-path (cdr path) (cddr rest-path)))
      ((endp rest-path))
    (format t "--- Applied operator ~S ---~%" (car rest-path))
    (describe-state (cadr rest-path))))