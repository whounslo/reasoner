;;; Copyright (C) 2007-2011, 2013, 2014 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html


(in-package reasoner)

(defclass proposition ()
    ((attribute-references :initform nil :accessor attribute-references
                           :initarg attribute-references)
     (class-consumer :accessor class-consumer)
     (negatedp :initform nil :initarg negatedp)
     (node-cache :initform nil :accessor node-cache
      :documentation "Cache for nodes that have matched proposition.")))

(defclass arithmetic-proposition (proposition)
    ((relation :reader relation :initarg relation)
     (prefix-rhs :reader prefix-rhs :initarg prefix-rhs)
     (source-proposition :reader source-proposition :initarg source-proposition
      :documentation "Proposition corresponding to source expression, if different."))
    (:default-initargs
     source-proposition nil
     ))

(defclass functional-proposition (proposition)
    ((relation :reader relation :initarg relation)
     (function-name :reader function-name :initarg function-name)
     (arguments :reader arguments :initarg arguments))
    (:default-initargs
     arguments nil
     ))

(defclass lisp-proposition (proposition)
    ((function-name :reader function-name :initarg function-name)
     (arguments :reader arguments :initarg arguments)))

(defclass literal-proposition (proposition)
    ((value :reader value :initarg value)))

(defclass numeric-proposition (proposition)
    ((value :reader value :initarg value)))

(defclass relational-proposition (proposition)
    ((specializer :reader proposition-specializer :initarg specializer)))

(defmethod head-attribute-reference ((p arithmetic-proposition))
  (car (last (attribute-references p))))

(defmethod head-attribute-reference ((p functional-proposition))
  (car (last (attribute-references p))))

(defun lastp (item list &key (test #'eq))
  "Determines if item is last in list."
  (endp (cdr (member item list :test test))))

(defun head-attribute-reference-p (attribute-reference proposition)
  "Determines if attribute reference stands to be asserted into if proposition forms the head of a class-consumer."
  (lastp attribute-reference (attribute-references proposition)))

;;; (defstruct (attribute-reference (:conc-name nil) (:type list))
;;;   attribute-reference-variable attribute-name)
(progn
(defmacro make-attribute-reference
       (&key attribute-reference-variable attribute-name)
  `(list ,attribute-reference-variable ,attribute-name))
(defmacro attribute-reference-variable (attribute-reference)
  `(car ,attribute-reference))
(defmacro attribute-name (attribute-reference)
  `(cadr ,attribute-reference))
)

;;; (defstruct (variable (:type list))
;;;   name class-name)
(progn
(defmacro make-variable (&key name class-name) `(list ,name ,class-name))
(defmacro variable-name (variable) `(car ,variable))
(defmacro variable-class-name (variable) `(cadr ,variable))
)

(deftype attribute-reference nil '(satisfies attribute-reference-p))

(deftype variable nil '(satisfies variablep))

(defmethod attribute-reference-p ((x t))
  nil)

(defmethod attribute-reference-p ((x list))
  (and (variablep (attribute-reference-variable x))
       (attribute-name x)
       (symbolp (attribute-name x))))

(defmethod attribute-reference-p ((x null))
  nil)

(defmacro attribute-reference-variable-name (attribute-reference)
  `(variable-name (attribute-reference-variable ,attribute-reference)))

(defun attribute-reference-class (attribute-reference)
  (find-class (variable-class-name
               (attribute-reference-variable attribute-reference))))

(defmethod variablep ((x t))
  nil)

(defmethod variablep ((x list))
  (and (symbolp (variable-class-name x))
       (find-class (variable-class-name x) nil)))

(defmethod variablep ((x null))
  nil)

;;; Proposition initialization

(defmethod initialize-instance :after ((p arithmetic-proposition)
                                       &rest initargs)
  (collect-rhs-attribute-references p (getf initargs 'prefix-rhs)))

(defmethod initialize-instance :after ((p functional-proposition)
                                       &rest initargs)
  (collect-rhs-attribute-references p (getf initargs 'arguments)))

(defmethod initialize-instance :after ((p lisp-proposition)
                                       &rest initargs)
  (collect-rhs-attribute-references p (getf initargs 'arguments)))

(defun collect-rhs-attribute-references (proposition arithmetic-expression)
  "Attribute references found in the prefix arithmetic expression are consed onto the list of attribute references for the proposition."
  (typecase arithmetic-expression
    (attribute-reference (pushnew arithmetic-expression
                                  (attribute-references proposition)
                                  :test #'equal))
    (list (dolist (sub-expression arithmetic-expression)
            (collect-rhs-attribute-references proposition sub-expression)))))

;;; Manipulation of propositions prior to indexing

(defmethod negate ((p proposition))
  (copy-instance p 'negatedp (not nil)))

(defmethod negate ((p numeric-proposition))
  (if (slot-value p 'negatedp)
      (let ((p (copy-instance p)))
        (setf (slot-value p 'negatedp) nil)
        p)
    (call-next-method)))

(defmethod disjoin ((p1 proposition) (p2 proposition))
  nil)

(defmethod disjoin ((p1 numeric-proposition) (p2 numeric-proposition))
  (flet ((value (numeric-proposition)
           (if (slot-value numeric-proposition 'negatedp)
               (satisfy-not-equal (attribute-values
                                   (car
                                    (attribute-references numeric-proposition)))
                                  (value numeric-proposition))
               (value numeric-proposition))))
    (let (new-value)
      (if (and (eq (attribute-name (car (attribute-references p1)))
                   (attribute-name (car (attribute-references p2))))
               (setq new-value (numeric-range-union (value p1) (value p2))))
          (copy-instance p1 'value new-value 'negatedp nil)))))

(defmethod disjoin ((p1 literal-proposition) (p2 literal-proposition))
  (flet ((attribute-reference (literal-proposition)
           (car (last (attribute-references literal-proposition))))
         (value (literal-proposition)
           (let* ((attribute-values
                    (attribute-values
                     (car (attribute-references literal-proposition))))
                  (value (if (slot-boundp literal-proposition 'value)
                             (value literal-proposition)
                             attribute-values
                                               ; Note: disjoined proposition
                                               ; will be tautologous.
                             )))
             (if (slot-value literal-proposition 'negatedp)
                 (set-difference attribute-values value :test #'eq)
                 value))))
    (let (new-value)
      (if (and (eq (attribute-name (attribute-reference p1))
                   (attribute-name (attribute-reference p2)))
               (setq new-value (union (value p1) (value p2))))
          (copy-instance p1 'value new-value 'negatedp nil)))))

(defmethod tautologousp ((p proposition))
  nil)

(defmethod tautologousp ((p literal-proposition))
  (subsetp (attribute-values (car (last (attribute-references p))))
           (value p)))

(defmethod tautologousp ((p numeric-proposition))
  (numeric-subrangep (attribute-values (car (attribute-references p)))
                     (value p)))

(defmethod rewrite ((p proposition))
  (list p))

(defmethod rewrite ((p arithmetic-proposition) &aux flip-count)
  "Return list of propositions representing all possible ways of writing arithmetic expression."
  (labels ((rewrite-expression (rhs target-lhs lhs)
             "Rewrites expression LHS = RHS with target expression (currently part of the RHS) as the LHS; returns RHS."
             (flet ((rewrite (operator argument1 argument2 rhs)
                      "Returns an expression for evaluating an unknown argument (notated by ?) of a binary operator whose result is RHS."
                      (flet ((invert (operator)
                               (ecase operator
                                 (+ '-)
                                 (- '+)
                                 (* '/)
                                 (/ '*))))
                        (cond ((eq argument1 '?)
                               (list (invert operator) rhs argument2))
                              ((member operator '(* +) :test #'eq)
                               (list (invert operator) rhs argument1))
                              (t (list operator argument1 rhs))))))
               (setq flip-count 0)
               (cond ((unary-minus-p rhs)
                      (rewrite-expression (cadr rhs)
                                          target-lhs
                                          (list '- lhs)))
                     ((operatorp (car rhs))
                      (let ((operator (car rhs))
                            (left (cadr rhs))
                            (right (caddr rhs)))
                        (or (rewrite-expression left
                                                target-lhs
                                                (rewrite operator '? right lhs))
                            (let* ((expr (rewrite operator left '? lhs))
                                   (expression (rewrite-expression right
                                                                   target-lhs
                                                                   expr)))
                              (when (and (eq (car expr) operator)
                                         expression)
                                (incf flip-count))
                              expression))))
                     ((equal rhs target-lhs)
                      lhs)))))
    (let ((relation (relation p))
          (prefix-rhs (prefix-rhs p))
          (head-attribute-reference (head-attribute-reference p)))
      (cons p
            (mapcar #'(lambda (attribute-reference)
                        (copy-instance p
                                       'prefix-rhs
                                       (rewrite-expression prefix-rhs
                                                           attribute-reference
                                                           head-attribute-reference)
                                       'relation (if (oddp flip-count)
                                                     relation
                                                   (flip-relation relation))
                                       'source-proposition p
                                       'attribute-references
                                       (list attribute-reference)))
                    (butlast (attribute-references p)))))))

;;; Proposition indexing

(defmethod index ((p proposition) attribute-reference)
  "Index proposition so that its class-consumer will be triggered by incoming assertions corresponding to attribute-reference."
  ;; Index each attribute reference once only per consumer.
  (pushnew (list p attribute-reference)
           (gethash (attribute-name attribute-reference)
                    (class-rule-index (attribute-reference-class attribute-reference)))
           :test #'(lambda (node-class-1 node-class-2)
                     (and (equal (second node-class-1)
                                 (second node-class-2))
                          (eq (class-consumer (first node-class-1))
                              (class-consumer (first node-class-2)))))))

(defmethod index ((p relational-proposition) attribute-reference)
  "Index proposition so that its class-consumer will be triggered by incoming assertions corresponding to attribute-reference."
  ;; Multiple relational propositions within a consumer may have the same
  ;; attribute reference, but their specializers will (should) be
  ;; different.  So index them all.
  (push (list p attribute-reference)
        (gethash (attribute-name attribute-reference)
                 (class-rule-index (attribute-reference-class attribute-reference)))))

(defmethod index-head ((p proposition) attribute-reference)
  "Index proposition as potentially affecting slots corresponding to attribute-reference."
  (push (list p attribute-reference)
        (gethash (attribute-name attribute-reference)
                 (class-rule-head-index (attribute-reference-class attribute-reference)))))

(defmethod remove-head-index ((p proposition) attribute-reference)
  (unless (setf (gethash (attribute-name attribute-reference)
                         (class-rule-head-index
                          (attribute-reference-class attribute-reference)))
            (delete (list p attribute-reference)
                    (gethash (attribute-name attribute-reference)
                             (class-rule-head-index
                              (attribute-reference-class attribute-reference)))
                    :test #'equal))
    (remhash (attribute-name attribute-reference)
             (class-rule-head-index (attribute-reference-class attribute-reference)))))

(defmethod remove-index ((p proposition) attribute-reference)
  (unless (setf (gethash (attribute-name attribute-reference)
                           (class-rule-index (attribute-reference-class
                                              attribute-reference)))
            (delete (list p attribute-reference)
                  (gethash (attribute-name attribute-reference)
                           (class-rule-index (attribute-reference-class
                                              attribute-reference)))
                  :test #'equal))
    (remhash (attribute-name attribute-reference)
             (class-rule-index (attribute-reference-class attribute-reference)))))

;;; Matching propositions

(defmacro first-conjunct (conjuncts)
  `(car ,conjuncts))

(defmacro rest-conjuncts (conjuncts)
  `(cdr ,conjuncts))

(defmethod conjoinedp ((p proposition) rest-conjuncts)
  (declare (special head-proposition-p))
  (or (and head-proposition-p (not (rest-conjuncts rest-conjuncts)))
                                               ; Just the head attribute
                                               ; reference remaining?
      (not (first-conjunct rest-conjuncts))))

(defmethod conjoinedp ((p lisp-proposition) rest-conjuncts)

  ;; Lisp propositions do not have a distinguished head attribute
  ;; reference.
  (not (first-conjunct rest-conjuncts)))

(defmethod conjoin ((p proposition) attribute-references initial-frame-stream)
  "Takes the attribute references (from proposition) and frame-stream and returns the stream of extended frames."
  (declare (special head-proposition-p))
  (do ((rest-conjuncts attribute-references
                       (rest-conjuncts rest-conjuncts))
       (frame-stream initial-frame-stream

                     ;; Filter the stream of frames by finding the stream of all
                     ;; possible extensions to the first conjunct, to use as new
                     ;; frame-stream for rest of conjuncts.
                     (assertedp p
                                (first-conjunct rest-conjuncts)
                                frame-stream))
       (remaining-attribute-references attribute-references
                                       rest-conjuncts)
       (old-frame-stream initial-frame-stream frame-stream))
      ((empty-stream-p frame-stream)

       ;; Failure.
       (values p                               ; Failed proposition.
               (first-conjunct remaining-attribute-references)
                                               ; Attribute reference within
                                               ; proposition not matched.
               old-frame-stream
                                               ; Bindings accumulated up to
                                               ; point of failure.
               ))
    (when (conjoinedp p rest-conjuncts)

      ;; Finished matching a proposition in the tail or head of a
      ;; class-consumer.
      (return (values p nil frame-stream)))))

(defmethod assertedp ((p proposition) attribute-reference frame-stream)
  "Returns the stream formed by extending each frame by all the matches of attribute reference."
  (mapcan #'(lambda (frame)
              (find-assertions p attribute-reference frame))
          frame-stream))

(defmethod find-assertions ((p proposition) attribute-reference frame)
  "Returns stream of frames that extend frame by a match of attribute reference."
  (mapcan #'(lambda (datum)
              (pattern-match p attribute-reference datum frame))
          (fetch-assertions p attribute-reference frame)))

(defmethod pattern-match ((p proposition) attribute-reference datum frame)
  "Takes an attribute reference, a data object and a frame and returns either a one-element stream, or THE-EMPTY-STREAM if the match fails."
  (let ((result (internal-match p attribute-reference datum frame)))
    (if (eq result 'failed)
        the-empty-stream
        (singleton result))))

(defmethod internal-match ((p proposition) attribute-reference datum frame)
  "Returns either the symbol FAILED or an extension of the given frame."
  (if (or (not (head-attribute-reference-p attribute-reference p))
                                               ; Just accumulate binding?
          (satisfiesp datum p frame)
                                               ; Test proposition against
                                               ; datum, using accumulated
                                               ; bindings for any other
                                               ; attribute references in
                                               ; proposition.
          )
      (extend-if-consistent p attribute-reference datum frame)
      'failed))

(defmethod internal-match ((p lisp-proposition) attribute-reference datum frame)
  "Returns either the symbol FAILED or an extension of the given frame."

  ;; Accumulate all the bindings before testing.
  (declare (special head-proposition-p))
  (let ((extended-frame
          (extend-if-consistent p attribute-reference datum frame)))
    (if (or head-proposition-p                 ; If in the head, all attribute
                                               ; references are being matched,
                                               ; so be sure not to test.
            (not (head-attribute-reference-p attribute-reference p))
                                               ; Just accumulate binding?
            (satisfiesp datum p extended-frame)
                                               ; Test proposition against
                                               ; datum, using accumulated
                                               ; bindings for attribute
                                               ; references in proposition.
            )
        extended-frame
        'failed)))

(defmethod extend-if-consistent ((p proposition)
                                 attribute-reference datum frame)
  "Extend frame by adding bindings for attribute reference and single variable within attribute reference, if not bound."
  (if (eq (lookup-in-frame attribute-reference frame)
          datum)
                                               ; Is there a binding for the
                                               ; attribute reference?  We
                                               ; examine the binding because,
                                               ; in the case of multiple
                                               ; relational propositions with
                                               ; the same attribute reference,
                                               ; we must accumulate a binding
                                               ; for each one.
      frame
      (extend attribute-reference
              datum
              (if (binding-in-frame (attribute-reference-variable-name
                                                            attribute-reference)
                                    frame)
                                               ; Is there a binding for the
                                               ; variable?
                  frame
                  (extend (attribute-reference-variable-name
                                                            attribute-reference)
                          (datum-object datum)
                          frame)
                                               ; Extend frame by adding
                                               ; variable binding.
                  ))
                                               ; Extend frame by adding
                                               ; attribute reference binding.
      ))

(defmethod extend-if-consistent ((p relational-proposition)
                                 attribute-reference datum frame)
  "Extend frame by adding binding for variable that specializes proposition, if not bound."
  (declare (ignore attribute-reference))
  (if (binding-in-frame (variable-name (proposition-specializer p))
                        frame)
      (call-next-method)
      (extend (variable-name (proposition-specializer p))
              (datum-value datum)
              (call-next-method))))

(defmethod satisfiesp ((node standard-slot-value) (p literal-proposition) frame)
  (flet ((disjointp (list1 list2)
           (notany #'(lambda (element)
                       (member element list1 :test #'eq))
                   list2)))
        (let ((other-node (if (slot-boundp p 'value)
                              nil
                              (lookup-in-frame (car (attribute-references p))
                                               frame))))
          (if (and other-node
                   (eq node other-node))
              nil
                                               ; The proposition is
                                               ; tautologous if the two
                                               ; attribute references are
                                               ; bound to the same node.
              (let ((value (if other-node
                               (elements other-node)
                               (value p)))
                    (datum-value (elements node)))
                (cond ((negatedp p (class-consumer p))
                       (disjointp datum-value value))
                      ((not other-node)
                       (subsetp datum-value value))
                      ((and (singletonp datum-value)
                            (singletonp value))
                       (equal datum-value value))))))))

(defmethod satisfiesp ((node standard-slot-value) (p numeric-proposition) frame)
  (declare (ignore frame))
  (if (negatedp p (class-consumer p))
      (numeric-range-disjointp (elements node) (value p))
    (numeric-subrangep (elements node) (value p))))

(defmethod satisfiesp ((node standard-slot-value) (p arithmetic-proposition) frame)
  (relation-satisfied-p (elements node)
                        (if (negatedp p (class-consumer p))
                            (invert-relation (relation p))
                            (relation p))
                        (range-eval (instantiate (prefix-rhs p) frame))))

(defmethod satisfiesp ((node standard-slot-value) (p functional-proposition) frame)
  (relation-satisfied-p (elements node)
                        (if (negatedp p (class-consumer p))
                            (invert-relation (relation p))
                            (relation p))
                        (let ((function (ecase (function-name p)
                                          (min #'unbounded-min)
                                          (max #'unbounded-max)))
                              (arguments (instantiate (arguments p) frame)))
                          (make-numeric-range :min (apply function
                                                          (mapcar #'range-min
                                                                  arguments))
                                              :max (apply function
                                                          (mapcar #'range-max
                                                                  arguments))))))

(defmethod satisfiesp ((node standard-slot-value) (p relational-proposition) frame)
  (if (negatedp p (class-consumer p))
      nil
    (let ((specializer-binding (binding-in-frame (variable-name
                                                  (proposition-specializer p))
                                                 frame)))
      (if specializer-binding
          (eq (datum-value node)
              (binding-value specializer-binding))
        (typep (datum-value node)
               (variable-class-name (proposition-specializer p)))))))

(defmethod satisfiesp ((node excluded-slot-value)
                       (p relational-proposition)
                       frame)
  (if (negatedp p (class-consumer p))
      (let ((specializer-binding (binding-in-frame (variable-name
                                                    (proposition-specializer p))
                                                   frame)))
        (if specializer-binding
            (eq (datum-value node)
                (binding-value specializer-binding))
          (typep (datum-value node)
                 (variable-class-name (proposition-specializer p)))))))

(defmethod satisfiesp ((node standard-slot-value) (p lisp-proposition) frame)
  (funcall (if (negatedp p (class-consumer p))
               #'not
               #'identity)
           (apply (function-name p)
                  (mapcar #'(lambda (expression)
                              (instantiate expression frame))
                          (arguments p)))))

(defun fetch-assertions (proposition attribute-reference frame)
  "Return assertions that are potential matches for attribute reference, taking advantage of the information in frame."
  (if (use-index-p attribute-reference frame)
      (get-indexed-assertions proposition attribute-reference)
      (get-all-assertions proposition attribute-reference frame)))

(defun use-index-p (attribute-reference frame)
  "Returns non-nil if variable in attribute reference is not bound in frame."
  (null
   (binding-in-frame (attribute-reference-variable-name attribute-reference)
                     frame)))

(defmethod get-all-indexed-assertions ((p proposition) attribute-reference)
  "Use cache to locate assertions that may match attribute reference."
  (cdr (assoc attribute-reference (node-cache p) :test #'eq)))

(defmethod get-indexed-assertions ((p proposition) attribute-reference)
  "Use cache to locate assertions that may match attribute reference."
  (let ((class (attribute-reference-class attribute-reference))
        (nodes (get-all-indexed-assertions p attribute-reference)))
    (flet ((invalid-datum-p (node)
             (not (typep (datum-object node) class))))
      (if (some #'invalid-datum-p nodes)
          
          ;; If class-changing has been used, nodes that were once potential
          ;; matches may no longer be so; these are removed here.
          (remove-if #'invalid-datum-p nodes)
        nodes))))

(defmethod add-to-cache ((node standard-slot-value)
                         (p proposition)
                         attribute-reference
                         &optional tentative)
  "Add to cache of nodes that have matched proposition."
  (let ((attribute-reference-bucket
         (assoc attribute-reference (node-cache p) :test #'eq)))
    (when (and tentative
               (find node (cdr attribute-reference-bucket)
                     :test #'eq))
      (return-from add-to-cache nil))
    (if attribute-reference-bucket
        (push node (cdr attribute-reference-bucket))
      (push (list attribute-reference node) (node-cache p)))
    node))

(defmethod remove-from-cache ((node standard-slot-value)
                              (p proposition)
                              attribute-reference)
  "Remove from cache of nodes that have matched proposition."
  (let* ((proposition-bucket (node-cache p))
         (attribute-reference-bucket
          (assoc attribute-reference proposition-bucket :test #'eq)))
    (delete node attribute-reference-bucket :test #'eq)
    (or (cdr attribute-reference-bucket)
        (setf (node-cache p)
          (delete attribute-reference-bucket proposition-bucket :test #'eq)))
    node))

(defmethod get-all-assertions ((p proposition)
                               attribute-reference frame)
  "Use bindings in frame to locate assertions that may match attribute reference."
  (let ((value (lookup-in-frame attribute-reference frame)))
    (if value
        (singleton value)
                                          ; Attribute reference itself is
                                          ; bound; just return binding.
      (get-all-assertions-1 p attribute-reference frame))))

(defmethod get-all-assertions ((p relational-proposition)
                               attribute-reference frame)
  "Use bindings in frame to locate assertions that may match attribute reference."

  ;; We cannot simply return the binding of attribute reference, if it is
  ;; bound: the binding for one relational proposition won't satisfy
  ;; another (they will have different specializers).
  (get-all-assertions-1 p attribute-reference frame))

(defun get-all-assertions-1 (proposition attribute-reference frame)
  "Access object that is binding of variable in attribute reference."
  ;; Nodes that have yet to be matched against their class consumers, and so
  ;; are not in the node cache (see GET-INDEXED-ASSERTIONS), must be removed to
  ;; prevent duplicate firing of class-consumers.
  (let ((object (lookup-in-frame (attribute-reference-variable-name
                                                            attribute-reference)
                                 frame))
        (slot-name (attribute-name attribute-reference)))
    (if (slot-exists-p object slot-name)  ; Culprits are relational proposition
                                          ; specializer bindings: see
                                          ; INITIALLY-SATISFIES-P.
        (intersection (all-slot-values object slot-name)
                      (get-indexed-assertions proposition attribute-reference)
                      :test #'eq))))

;;; Asserting propositions

(defmethod satisfy ((p literal-proposition)
                    frame antecedents informant)
  (let ((attribute-reference (car (last (attribute-references p))))
        value object)
    (when (and (if (slot-boundp p 'value)
                   (setq value (value p))
                   (singletonp
                    (setq value
                          (elements
                           (lookup-in-frame (car (attribute-references p))
                                            frame)))))
               (setq object
                     (lookup-in-frame (attribute-reference-variable-name
                                                            attribute-reference)
                                      frame)))
      (add-slot-value object
                      (attribute-name attribute-reference)
                      (if (negatedp p (class-consumer p))
                          (set-difference (attribute-values
                                                          attribute-reference)
                                          value
                                          :test #'eq)
                          value)
                      antecedents
                      informant))))

(defmethod satisfy ((p numeric-proposition)
                    frame antecedents informant &aux object)
  (with-slots (attribute-references value)
              p
    (when (setq object (lookup-in-frame (attribute-reference-variable-name
                                         (car attribute-references))
                                        frame))
      (add-slot-value object
                      (attribute-name (car attribute-references))
                      (if (negatedp p (class-consumer p))
                          (satisfy-not-equal (attribute-values
                                              (car attribute-references))
                                             value)
                          value)
                      antecedents
                      informant))))

(eval-when (:execute :compile-toplevel)

(defmethod make-load-form ((object numeric-range) &optional environment)
  (declare (ignore environment))
  `(make-instance ',(class-of object)))
)

(defmethod satisfy ((p arithmetic-proposition) frame antecedents informant
                    &aux head-attribute-reference head-attribute-values object)
  (flet ((rhs-minusp (attribute-reference)
           (if (eq attribute-reference head-attribute-reference)
               nil
             (unbounded< (range-max
                          (elements
                           (lookup-in-frame attribute-reference frame)))
                         0)))
         (extend (attribute-reference value frame)
           (let ((range #.(make-instance 'numeric-range)))
             (reinitialize-instance range
               :value (if (eql (range-min value)
                               (range-min head-attribute-values))
                          (range-max value)
                        (range-min value)))
             (extend attribute-reference range frame))))
    (setq head-attribute-reference (head-attribute-reference p)
        head-attribute-values (attribute-values head-attribute-reference)
        object
        (lookup-in-frame (attribute-reference-variable-name head-attribute-reference)
                         frame))
    (when object
      (let ((relation (if (negatedp p (class-consumer p))
                          (invert-relation (relation p))
                        (relation p)))
            (source-proposition (source-proposition p))
            (rhs-value (range-eval (instantiate (prefix-rhs p) frame)))
            value)
        
        ;; Ensure that we have the right end of the range.  Unsubtle but guaranteed.
        (when (and (not (member relation '(= /=)))
                   source-proposition
                   (some #'rhs-minusp (attribute-references p)))
          (unless (member relation '(<= >=))
            (setq value (satisfy-relation head-attribute-values
                                          relation
                                          rhs-value)))
          (let ((attribute-reference-value
                 (lookup-in-frame (head-attribute-reference source-proposition)
                                  frame))
                (frame
                 (extend head-attribute-reference
                         (or value
                             (satisfy-relation head-attribute-values
                                               (if (eq relation '<=) '< '>)
                                               rhs-value))
                         frame)))
            (unless (satisfiesp attribute-reference-value
                                source-proposition
                                frame)
              (setq value (satisfy-relation head-attribute-values
                                            (flip-relation relation)
                                            rhs-value)))))
        (add-slot-value object
                        (attribute-name head-attribute-reference)
                        (or value
                            (satisfy-relation head-attribute-values
                                              relation
                                              rhs-value))
                        antecedents
                        informant)))))

(defmethod satisfy ((p functional-proposition)
                    frame antecedents informant &aux head-attribute-reference object)
  (setq head-attribute-reference (head-attribute-reference p)
      object
        (lookup-in-frame (attribute-reference-variable-name head-attribute-reference)
                         frame))
  (when object
    (add-slot-value object
                    (attribute-name head-attribute-reference)
                    (satisfy-relation (attribute-values head-attribute-reference)
                                      (if (negatedp p (class-consumer p))
                                          (invert-relation (relation p))
                                          (relation p))
                                      (let ((function (ecase (function-name p)
                                                        (min #'unbounded-min)
                                                        (max #'unbounded-max)))
                                            (arguments
                                             (instantiate (arguments p) frame)))
                                        (make-numeric-range
                                                 :min (apply function
                                                             (mapcar #'range-min
                                                                     arguments))
                                                 :max (apply function
                                                             (mapcar #'range-max
                                                                  arguments)))))
                    antecedents
                    informant)))

(defmethod satisfy ((p relational-proposition)
                    frame antecedents informant &aux object new-value)
  (let ((attribute-reference (car (attribute-references p))))
    (when (and (setq object
                     (lookup-in-frame (attribute-reference-variable-name
                                                            attribute-reference)
                                      frame))
               (setq new-value (lookup-in-frame (variable-name
                                                 (proposition-specializer p))
                                                frame)))
      (add-slot-value object
                      (attribute-name attribute-reference)
                      new-value
                      antecedents
                      informant
                      :negated (negatedp p (class-consumer p))))))

(defmethod satisfy ((p lisp-proposition)
                    frame antecedents informant)
  (apply (function-name p)
         (nconc (mapcar #'(lambda (expression)
                            (instantiate expression frame))
                        (arguments p))
                (list antecedents informant))))

(defun instantiate (expression frame)
  "Instantiates prefix expression using the bindings in frame."
  (typecase expression
    (attribute-reference (elements (lookup-in-frame expression frame)))
    (variable (lookup-in-frame (variable-name expression) frame))
    (list (mapcar #'(lambda (expression)
                      (instantiate expression frame))
                  expression))
    (t expression)))

;;; Low-level manipulation of bindings

(defun make-frame nil
  (list))

(defun lookup-in-frame (variable frame)
  (binding-value (binding-in-frame variable frame)))

(defun binding-value (binding)
  (cdr binding))

(defun binding-in-frame (variable frame)
  (assoc variable frame :test #'equal))

(defun extend (variable value frame)
  (acons variable value frame))