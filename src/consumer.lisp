;;; Copyright (C) 2007-2011, 2013, 2014 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html


(in-package reasoner)
(eval-when (:execute :compile-toplevel :load-toplevel)
  (import '(atms::cross-product)))

(defclass class-consumer (lockable-object)
    ((rule-source :reader rule-source :initarg rule-source)
     (propositions :reader propositions :initarg propositions)
     (failed-attribute-reference :initform nil
        :documentation "Point of failure during last matching cycle.")))

(defclass conjunctive-class-consumer (class-consumer)
    ())

(defclass constraint-consumer (class-consumer)
    ())

(defmacro first-proposition (propositions)
  `(car ,propositions))

(defmacro rest-propositions (propositions)
  `(cdr ,propositions))

;;; Accessing propositions within conjunctive-class-consumer:
;;; ({Pb}+ [({Ph}* [({Phs}+)])])

(defun remaining-propositions (propositions)
  (do ((rest-propositions propositions (car rest-propositions)))
      ((not (consp (car rest-propositions))) rest-propositions)))

(defun head-propositions (propositions)
  (let ((head (last propositions)))
    (if (consp (car head)) (car head) head)))

(defmethod head-proposition-p ((p proposition) (c class-consumer))
  "Determines if proposition forms the head of the class-consumer."
  (find p (head-propositions (propositions c)) :test #'eq))

;;; Indexing of a class-consumer's constituent propositions

(defmethod initialize-instance :after ((c class-consumer) &rest initargs)
  (do ((propositions (getf initargs 'propositions)
                     (remaining-propositions (cdr propositions))))
      ((endp propositions))
    (add-indexes (if (slot-boundp (car propositions) 'class-consumer)
                     (setf (car propositions)
                           (copy-instance (car propositions)))
                     (car propositions))
                 c)))

(defmethod add-indexes :before ((p proposition) (c class-consumer))
  (setf (class-consumer p) c))

(defmethod add-indexes ((p proposition) (c conjunctive-class-consumer))
  (do ((rest-attribute-references (attribute-references p)
                                  (cdr rest-attribute-references)))
      ((endp rest-attribute-references))
    (funcall (if (and (singletonp rest-attribute-references)
                      (head-proposition-p p c))
                 #'index-head
                 #'index)
             p
             (car rest-attribute-references))))

(defmethod add-indexes ((p proposition) (c constraint-consumer))
  (dolist (attribute-reference (attribute-references p))
    (index p attribute-reference)))

(defmethod add-indexes ((p lisp-proposition) (c conjunctive-class-consumer))

  ;; No distinguished head attribute reference in a Lisp proposition.
  (dolist (attribute-reference (attribute-references p))
    (index p attribute-reference)))

(defmethod add-indexes ((p functional-proposition) (c constraint-consumer))

  ;; A constituent functional proposition of a constraint consumer, if the
  ;; only proposition, has a distinguished head attribute reference which
  ;; should not be indexed.
  (if (rest-propositions (propositions c))
      (call-next-method)
    (do ((rest-attribute-references (attribute-references p)
                                    (cdr rest-attribute-references)))
        ((singletonp rest-attribute-references))
      (index p (car rest-attribute-references)))))

(defmethod add-indexes ((p arithmetic-proposition) (c constraint-consumer))

  ;; A constituent arithmetic proposition of a constraint consumer, if the
  ;; only proposition, has a distinguished head attribute reference which
  ;; should not be indexed.
  (if (rest-propositions (propositions c))
      (call-next-method)
    (do ((rest-attribute-references (attribute-references p)
                                    (cdr rest-attribute-references)))
        ((singletonp rest-attribute-references))
      (index p (car rest-attribute-references)))))

(defmethod remove-indexes ((p lisp-proposition) (c conjunctive-class-consumer))
  (dolist (attribute-reference (attribute-references p))
    (remove-index p attribute-reference)))

(defmethod remove-indexes ((p functional-proposition) (c constraint-consumer))
  (if (rest-propositions (propositions c))
      (call-next-method)
    (do ((rest-attribute-references (attribute-references p)
                                    (cdr rest-attribute-references)))
        ((singletonp rest-attribute-references))
      (remove-index p (car rest-attribute-references)))))

(defmethod remove-indexes ((p arithmetic-proposition) (c constraint-consumer))
  (if (rest-propositions (propositions c))
      (call-next-method)
    (do ((rest-attribute-references (attribute-references p)
                                    (cdr rest-attribute-references)))
        ((singletonp rest-attribute-references))
      (remove-index p (car rest-attribute-references)))))

(defmethod remove-indexes ((p proposition) (c constraint-consumer))
  (dolist (attribute-reference (attribute-references p))
    (remove-index p attribute-reference)))

(defmethod remove-indexes ((p proposition) (c conjunctive-class-consumer))
  (do ((rest-attribute-references (attribute-references p)
                                  (cdr rest-attribute-references)))
      ((endp rest-attribute-references))
    (funcall (if (and (singletonp rest-attribute-references)
                      (head-proposition-p p c))
                 #'remove-head-index
                 #'remove-index)
             p
             (car rest-attribute-references))))

(defmethod remove-indexes ((propositions cons) (c conjunctive-class-consumer))

  ;; Multiple propositions in head.
  (dolist (proposition propositions)
    (remove-indexes proposition c)))

;;; Class-consumer evaluation

(defmethod initially-satisfies-p
    ((node standard-slot-value) (p proposition) attribute-reference
     &optional (frame (make-frame)))
  (declare (ignore attribute-reference))
  (let ((head-proposition-p nil))
    (declare (special head-proposition-p))
    (if (singletonp (attribute-references p))
        
        ;; Proposition has a single attribute reference,
        ;; so determine if it is satisfied by node.
        (satisfiesp node p frame)
      (not nil))))

(defun tail-proposition-relation (proposition)
  (let ((head-proposition-p nil))
    (declare (special head-proposition-p))
    (if (negatedp proposition (class-consumer proposition))
        (invert-relation (relation proposition))
      (relation proposition))))

(defmethod initially-satisfies-p
    ((node standard-slot-value) (p arithmetic-proposition) attribute-reference
     &optional frame)
  (declare (ignore frame))
  
  ;; Inhibit matching of range sets.
  (or (numeric-rangep (elements node))
      (and (eq attribute-reference (head-attribute-reference p))
           (eq (tail-proposition-relation p) '/=))))

(defmethod initially-satisfies-p
    ((node standard-slot-value) (p functional-proposition) attribute-reference
     &optional frame)
  (declare (ignore frame))
  
  ;; Inhibit matching of range sets.
  (or (numeric-rangep (elements node))
      (and (eq attribute-reference (head-attribute-reference p))
           (eq (tail-proposition-relation p) '/=))))

(defmethod initially-satisfies-p
    ((node standard-slot-value) (p lisp-proposition) attribute-reference
     &optional frame)
  (declare (ignore frame))
  (if (and (not (head-proposition-p p (class-consumer p)))
           (notany #'variablep (arguments p)))
      (call-next-method node
                        p
                        attribute-reference
                        (extend-if-consistent p
                                              attribute-reference
                                              node
                                              (make-frame)))
    (not nil)))

(defmethod initially-satisfies-p
    ((node standard-slot-value) (p relational-proposition) attribute-reference
     &optional frame)
  (declare (ignore frame))
  (or (call-next-method node p attribute-reference)
      (subtypep (variable-class-name (proposition-specializer p))
                (class-name (class-of (datum-value node))))
                                               ; Might datum later satisfy proposition,
                                               ; if its class were changed?
      ))

(defmethod generate-consumers ((p proposition) frame-stream)
  (attach-consumers p frame-stream))

(defmethod generate-consumers ((propositions cons) frame-streams)
  (mapc #'(lambda (p frame-stream)
            (attach-consumers p frame-stream))
    propositions
    frame-streams))

(defvar *trace-rule-failure* nil)

(defvar *rule-trace-output* *trace-output*)

(defun trace-failed-match (failed-attribute-reference
                           class-consumer
                           frame-stream)
  (format *rule-trace-output*
          "~S (~D) failed at ~S~%~{~8,1T~S = ~S~%~}"
          (datum-object (rule-source class-consumer))
          (position class-consumer
                    (class-consumers (datum-object
                                      (rule-source class-consumer))
                                     t)
                    :test #'eq)
          failed-attribute-reference
          (mapcan #'(lambda (binding)
                      (if (typep (car binding) 'attribute-reference)
                          nil
                        (list (car binding) (binding-value binding))))
                  (head frame-stream))))

(defmacro node-class-proposition (node-class)
  `(car ,node-class))

(defmacro node-class-attribute-reference (node-class)
  `(cadr ,node-class))

(defmethod node-class-consumer ((node standard-slot-value) node-class)
  (if (find node (apply #'get-all-indexed-assertions node-class) :test #'eq)
                                               ; Has node previously been
                                               ; matched against node-class?
      nil
    (let ((class-consumer (class-consumer (node-class-proposition node-class))))
      (cond ((output-of-rule-p node class-consumer)
                                               ; Check for spurious
                                               ; re-triggering.
             nil)
            ((initially-satisfies-p node
                                    (node-class-proposition node-class)
                                    (node-class-attribute-reference node-class))
             class-consumer)))))

(defmethod match ((c class-consumer) (node standard-slot-value) node-class)
  (flet ((precedesp (attribute-reference-1
                     attribute-reference-2
                     class-consumer)
           (do* ((propositions (propositions class-consumer)
                               (remaining-propositions propositions))
                 (attribute-references (attribute-references (pop propositions))
                                       (or (rest-conjuncts attribute-references)
                                           (attribute-references
                                            (pop propositions)))))
                ((eq (first-conjunct attribute-references) attribute-reference-2)
                 nil)
             (when (eq (first-conjunct attribute-references)
                       attribute-reference-1)
               (return (not nil))))))
    (let (latest-proposition
          failed-attribute-reference
          frame-stream)
      (with-slots ((last-failed-attribute-reference
                    failed-attribute-reference))
          c
        (hold-lock
            c
          (unless (add-to-cache node
                                (node-class-proposition node-class)
                                (node-class-attribute-reference node-class)
                                (if-in-parallel 'tentative))
            
            ;; Suppress duplicate consumer invokation (earlier one hadn't yet run).
            (return-from match nil))
          (unless (and last-failed-attribute-reference
                       (precedesp last-failed-attribute-reference
                                  (node-class-attribute-reference node-class)
                                  c))
            (multiple-value-setq (latest-proposition
                                  failed-attribute-reference
                                  frame-stream)
              (apply #'evaluate
                     c
                     (singleton
                      (extend-if-consistent (node-class-proposition node-class)
                                            (node-class-attribute-reference
                                             node-class)
                                            node
                                            (make-frame)))
                                               ; Establish binding to ensure
                                               ; that class-consumer will not
                                               ; be run on a node tuple that
                                               ; does not include this new
                                               ; node.
                     node-class))
            (unless failed-attribute-reference
              (setf last-failed-attribute-reference nil))))
        (cond ((not latest-proposition) nil)
              ((not failed-attribute-reference)
               (defer (progn (generate-consumers latest-proposition frame-stream)
                        node)))
              ((precedesp (or last-failed-attribute-reference
                              (node-class-attribute-reference node-class))
                          failed-attribute-reference
                          c)
               (setf last-failed-attribute-reference
                 (if (typep latest-proposition 'lisp-proposition)
                     nil
                   failed-attribute-reference))
               (when *trace-rule-failure*
                 (defer (progn (trace-failed-match failed-attribute-reference
                                                   c
                                                   frame-stream)
                          nil)))))))))

(defmethod output-of-rule-p ((n node) (c conjunctive-class-consumer))
  nil)

(defmethod rule-source ((n node))
  (let ((informant (informant (car (justifications n)))))
    (if (typep informant 'class-consumer)
        (rule-source informant))))

(defmethod output-of-rule-p ((n node) (c constraint-consumer))
  "Is node solely the output of another constraint-consumer implementing the same constraint?"
  (and (singletonp (justifications n))
       (eq (rule-source n)
           (rule-source c))))

(defmethod evaluate ((c class-consumer)
                     initial-frame-stream proposition attribute-reference)
  (declare (ignore proposition attribute-reference))
  (conjoin c (propositions c) initial-frame-stream))

(defmethod evaluate ((c constraint-consumer)
                     initial-frame-stream proposition attribute-reference)
  (macrolet ((rotate (propositions)
               `(prog1 (rest-propositions ,propositions)
                  (setf (rest-propositions (head-propositions ,propositions)) ,propositions
                    (rest-propositions ,propositions) nil)))
             (confine-to-tail-p (candidate-proposition)
               `(and (eq ,candidate-proposition proposition)
                     (head-attribute-reference-p attribute-reference
                                                 proposition))))
    (let* ((propositions (copy-list (propositions c)))
           (head (head-propositions propositions))
           latest-proposition
           failed-attribute-reference
           frame-stream)
      (when (confine-to-tail-p (first-proposition head))
        (setq propositions (rotate propositions)))
      (multiple-value-setq (latest-proposition
                            failed-attribute-reference
                            frame-stream)
        (conjoin c propositions initial-frame-stream))
      (cond ((not failed-attribute-reference)
             
             ;; Try with other propositions at head.
             (let (latest-propositions
                   frame-streams)
               (loop 
                 (when (eq propositions head) (return))
                 (setq propositions (rotate propositions))
                 (multiple-value-bind (latest-proposition
                                       failed-attribute-reference
                                       frame-stream)
                     (conjoin c propositions initial-frame-stream)
                   (unless failed-attribute-reference
                     (push latest-proposition latest-propositions)
                     (push frame-stream frame-streams))
                   (when (and failed-attribute-reference
                              (eq latest-proposition (first-proposition head))
                              (return)))))
               (if latest-propositions
                   (values (cons latest-proposition (nreverse latest-propositions))
                           nil
                           (cons frame-stream (nreverse frame-streams)))
                 (values latest-proposition
                         nil
                         frame-stream))))
            ((and (rest-propositions (setq propositions (member latest-proposition
                                                                propositions
                                                                :test #'eq)))
                       
                  (not (confine-to-tail-p latest-proposition)))
             (conjoin c (rotate propositions) frame-stream)
                                               ; Retry with failed proposition
                                               ; as head, re-using accumulated
                                               ; bindings.
             )
            (t
             (values latest-proposition
                     failed-attribute-reference
                     frame-stream))))))

(defmethod conjoin ((c class-consumer)
                    propositions initial-frame-stream)
  "The basic evaluator for a class-consumer."
  (do ((rest-propositions propositions
                          (rest-propositions rest-propositions))
       head-proposition-p
       failed-attribute-reference
       latest-proposition
       (frame-stream initial-frame-stream))
      ((or failed-attribute-reference
           (not (first-proposition rest-propositions)))
       (values latest-proposition failed-attribute-reference frame-stream))
    (declare (special head-proposition-p))
    (setq head-proposition-p (not (rest-propositions rest-propositions)))
    (multiple-value-setq (latest-proposition
                          failed-attribute-reference
                          frame-stream)
                   (conjoin (first-proposition rest-propositions)
                            (attribute-references
                             (first-proposition rest-propositions))
                            frame-stream))))

(defmethod attribute-references ((propositions cons))
  nil)

(defmethod conjoin ((propositions cons) attribute-references initial-frame-stream)
  "Matches a conjunction of head propositions in a class-consumer."
  (declare (ignore attribute-references))
  (do ((rest-propositions propositions
                          (rest-propositions rest-propositions))
       attribute-references
       latest-proposition
       failed-attribute-reference
       frame-stream
       (frame-streams nil (cons frame-stream frame-streams)))
      ((not (first-proposition rest-propositions))
       (values propositions nil (nreverse frame-streams)))
    (setq attribute-references (attribute-references
                                (first-proposition rest-propositions)))
    (when (singletonp attribute-references)
      
      ;; Propositions all have a single (head) attribute reference.
      (return (values propositions nil initial-frame-stream)))
    (multiple-value-setq (latest-proposition
                          failed-attribute-reference
                          frame-stream)
      (conjoin (first-proposition rest-propositions)
               attribute-references
               initial-frame-stream))
    (when failed-attribute-reference
      (return
        (values latest-proposition failed-attribute-reference frame-stream)))))

(defmethod negatedp ((p proposition) (c constraint-consumer))
  (declare (special head-proposition-p))
  (if head-proposition-p
      (slot-value p 'negatedp)
      (not (slot-value p 'negatedp))))

(defmethod negatedp ((p proposition) (c conjunctive-class-consumer))
  (slot-value p 'negatedp))

;;; Basic-consumer creation and execution

(defun map-frames (frame-stream function)
  (do ((frames frame-stream (cdr frames)))
      ((empty-stream-p frames))
    (funcall function (car frames))))

(defmethod class-consumer ((propositions cons))
  (class-consumer (car propositions)))

(defmethod satisfy ((propositions cons) frame antecedents informant)
  (dolist (p propositions)
    (satisfy p frame antecedents informant)))

(defmethod attach-consumers (p frame-stream)
  "Instantiate a class-consumer, by creating a basic consumer of a temporary node, for each frame in frame stream."
  (map-frames frame-stream
              #'(lambda (frame)
                  (add-consumer *atms*
                                (cons (rule-source (class-consumer p))
                                      (mapcan #'(lambda (binding)
                                                  (if (typep (car binding)
                                                             'attribute-reference)
                                                      (list (binding-value binding))))
                                        frame))
                                #'(lambda (antecedents)
                                    (let ((head-proposition-p (not nil)))
                                      (declare (special head-proposition-p))
                                      (satisfy p
                                               frame
                                               antecedents
                                               (class-consumer p)))))))
  p)

(defmethod attach-consumers ((p functional-proposition) frame-stream)
  (with-accessors ((arguments arguments)
                   (attribute-references attribute-references)
                   (function-name function-name))
      p
    (if (aggregate-function-name-p function-name)
        (map-frames frame-stream
                    #'(lambda (frame)
                        (apply #'aggregate-values (attribute-name
                                                   (car (last attribute-references)))
                                                  (fdefinition function-name)
                                                  (mapcar #'(lambda (argument)
                                                              (lookup-in-frame argument
                                                                               frame))
                                                          arguments))))
      (call-next-method)))
  p)

(defun aggregate-min (ranges)
  (make-numeric-range :min '-big
                      :max (reduce #'(lambda (range1 range2)
                                       (unbounded-min (range-min range1)
                                                      (range-min range2)))
                                   ranges
                                   :initial-value 'big)))

(defun aggregate-max (ranges)
  (make-numeric-range :min (reduce #'(lambda (range1 range2)
                                       (unbounded-max (range-max range1)
                                                      (range-max range2)))
                                   ranges
                                   :initial-value '-big)
                      :max 'big))

(defun aggregate-sum (ranges)
  (reduce #'(lambda (range1 range2)
              (range-apply '+ range1 range2))
          ranges
          :initial-value (make-numeric-range :min 0 :max 'big)))

;;; slot-value-combinations

;;; Returns all combinations of picking, for each member of the set of objects
;;; that are the datum-values of the incoming nodes, one subset of the nodes
;;; in its (datum-slot aggregate-datum) slot that, in the case of
;;; (datum-object aggregate-datum), includes aggregate-datum.

(defun slot-value-combinations (nodes aggregate-datum)
  (flet ((remove-initial-value (nodes)
           (remove :initial-value
                   nodes
                   :test #'eq
                   :key #'(lambda (node)
                            (informant (car (justifications node)))))))
    (cross-product
     (mapcar #'(lambda (node)
                 (mapcan #'(lambda (subset &aux (nodes subset))
                             (when (eq (datum-value node)
                                       (datum-object aggregate-datum))
                               
                               ;; Add the new datum back in to get
                               ;; only subsets containing it.
                               (push aggregate-datum nodes))
                             (if (and nodes (reduce #'combine nodes))
                                 (list nodes)))
                   (subsets
                    (remove-initial-value
                     (let ((slot-values (all-slot-values (datum-value node)
                                                         (datum-slot aggregate-datum))))
                       (or (cdr (member aggregate-datum
                                        slot-values
                                        :test #'eq))
                           slot-values)
                                               ; Remove new datum (if it has
                                               ; been added to this slot) and
                                               ; any data that arrived after it
                                               ; (they will be examined during
                                               ; a later matching cycle).
                       )))))
             nodes))))

;;; aggregate-values

;;; Asserts into slot-name aggregate values, including aggregate-datum,
;;; of node subsets in the (datum-slot aggregate-datum) slot of those
;;; subsets of objects, including relational-datum, in the
;;; (datum-slot relational-datum) slot of (datum-object relational-datum).

(defun aggregate-values (slot-name aggregate-fn relational-datum aggregate-datum)
  (with-accessors ((datum-object datum-object)
                   (datum-slot datum-slot))
      relational-datum
    (dolist (nodes (subsets (cdr (member relational-datum
                                         (all-slot-values datum-object
                                                          datum-slot)
                                         :test #'eq))
                                               ; Remove new datum and any data
                                               ; that arrived after it (they
                                               ; will be examined during
                                               ; a later matching cycle).
                            ))
      (let (
            ;; Add the new datum back in to get
            ;; only subsets containing it.
            (subset (cons relational-datum nodes)))
        (do ((combinations (slot-value-combinations subset aggregate-datum)
                           (cdr combinations)))
            ((endp combinations))
          (do ((combination (car combinations) (cdr combination))
               (antecedents subset (if range
                                       (append antecedents (car combination))
                                     antecedents))
               (ranges nil (if range
                               (cons range ranges)
                             ranges))
               range)
              ((endp combination)
               (when ranges
                 (add-consumer *atms*
                               antecedents
                               #'(lambda (antecedents)
                                   (add-slot-value datum-object
                                                   slot-name
                                                   (funcall aggregate-fn ranges)
                                                   antecedents
                                                   :aggregate-values)))))
            (setq range (if (singletonp (car combination))
                            (datum-value (caar combination))
                          (reduce #'combine
                                  (car combination))))))))))