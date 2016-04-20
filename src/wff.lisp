;;; Copyright (C) 2007, 2008, 2011, 2013 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; Rule compilation

(in-package reasoner)

(defclass well-formed-formula (extended-object)
;    ((source-form :reader source-form :initarg :source-form)
;     (class-consumers :reader class-consumers)
;     (documentation :initarg :documentation))
    ((source-form :initarg :source-form)
     (class-consumers)
     (documentation :initarg :documentation))
  (:metaclass extended-class)
  (:documentation "A well-formed-formula of the rule language."))

(defclass constraint (well-formed-formula)
    ()
  (:metaclass extended-class)
  (:documentation "An arbitrary logical expression from which all possible inferences are derived."
         ))

(defclass forward-rule (well-formed-formula)
    ()
  (:metaclass extended-class)
  (:documentation "A rule that has a distinguished head, the truth of which the rule acts to determine."
         ))

(defmethod documentation ((x well-formed-formula) (doc-type (eql t)))
  (car (slot-value-reduce x 'documentation t)))

;;; In the absence of the ability to customise automatically-generated
;;; methods...

(defmethod source-form ((wff well-formed-formula) &optional environment)
  (car (slot-value-reduce wff 'source-form environment)))

(defmethod class-consumers ((wff well-formed-formula) &optional environment)
  (car (slot-value-reduce wff 'class-consumers environment)))

(defconstant biconditional-token '<->)

(defconstant implication-token '->)

(defparameter rule-neck-tokens (list biconditional-token implication-token))

(defmacro compiler-error (control-string &rest arguments)
  "Signals an error during rule compilation."
  `(format nil ,control-string ,@arguments))

(defmacro errorp (x)
  `(stringp ,x))

(defmacro parse-formula (((sub-expression sub-parse-form)
                          connective
                          (expression parse-form))
                         template)
  "Parses an expression of the form: SUB-EXPRESSION [CONNECTIVE EXPRESSION] ."
  `(let ((,sub-expression ,sub-parse-form))
     (cond ((errorp ,sub-expression) ,sub-expression)
           ((eq (next-token) ',connective)
            (read-token)
            (let ((,expression ,parse-form))
              (if (errorp ,expression)
                  ,expression
                  ,template)))
           (t ,sub-expression))))

(defmethod add-class-consumers ((wff well-formed-formula) consumers antecedents)
  (add-slot-value wff 'class-consumers consumers antecedents :compilation))

(defmethod add-class-consumers :around ((wff well-formed-formula) consumers antecedents)
  (let ((slot-value (call-next-method)))
    (unless antecedents
      (dolist (consumer consumers)
        (setf (slot-value consumer 'rule-source) slot-value)))
    slot-value))

(defmethod rule-compile ((wff well-formed-formula))
  (let* ((antecedents (slot-values wff 'source-form t))
                                               ; Should be a singleton.
         (result (if antecedents (generate-class-consumers wff (car antecedents)))))
    (cond ((errorp result)
           (error "In source of rule ~S: ~A." (instance-name wff) result))
          (result
           (add-class-consumers wff result antecedents)))))

(defmethod parse :around ((wff well-formed-formula))
  (let ((*rule-source* (source-form wff t))
        *declarations*)
    (declare (special *rule-source* *declarations*))
    (call-next-method)))

(defmethod parse ((wff constraint))
  (declare (special *declarations*))
  (setq *declarations* (parse-declarations))
  (if (errorp *declarations*)
      *declarations*
    (parse-expression)))

(defun make-constraint-consumers (body antecedent)
  (do ((disjunctions (do ((initial-set (transform-to-cnf (list
                                                          (reduce-tree body))
                                                         nil)
                                       (cdr initial-set))
                          (enlarged-set nil
                                        (nconc enlarged-set
                                               (cross-product
                                                (mapcar #'rewrite
                                                        (simplify-disjunction
                                                         (car initial-set)))))))
                         ((endp initial-set) enlarged-set))
                     (cdr disjunctions))
       (constraints nil
                    (if (car disjunctions)
                                               ; Not simplified away?
                        (cons (make-instance 'constraint-consumer
                                             'propositions (car disjunctions)
                                             'rule-source antecedent)
                              constraints)
                      constraints)))
      ((endp disjunctions) constraints)))

(defmethod generate-class-consumers ((wff constraint) antecedent)
  (let ((parse-tree (parse wff)))
    (if (errorp parse-tree)
        parse-tree
      (make-constraint-consumers parse-tree antecedent))))

(defun collect-head-propositions (head)
  (let ((disjunction (transform-to-dnf (list (reduce-tree head)) nil)))
    (if (singletonp disjunction) (car disjunction))))

(defmethod parse ((wff forward-rule))
  "Parses rule of form: VARIABLES [DISJUNCTION NECK] HEAD ."
  (let (body neck head head-propositions)
    (declare (special *declarations*))
    (cond ((errorp (setq *declarations* (parse-declarations)))
           *declarations*)
          ((errorp (setq body (parse-disjunction)))
           body)
          ((errorp (setq neck (parse-neck wff)))
           neck)
          ((errorp (setq head (if neck (parse-head wff) body)))
           head)
          ((null (setq head-propositions (collect-head-propositions head)))
           (compiler-error "The head of a rule may only contain a conjunction"))
          ((and (eq neck biconditional-token)
                (not (singletonp head-propositions)))
           (compiler-error
                         "The head of a ~S rule must be a single proposition"
                         biconditional-token))
          ((and (eq neck biconditional-token)
                (typep (car head-propositions) 'lisp-proposition))
           (compiler-error
                         "A lisp proposition may not form the head of a ~S rule"
                         biconditional-token))
          ((some #'(lambda (head)
                     (and (typep head 'lisp-proposition)
                          (slot-value head 'negatedp)))
                 head-propositions)
           (compiler-error
                   "A lisp proposition in the head of a rule may not be negated"
                           ))
          ((and (eq neck biconditional-token)
                (typep (car head-propositions) 'functional-proposition)
                (aggregate-function-name-p (function-name (car head-propositions))))
           (compiler-error
                         "An aggregate function may not appear in a ~S rule"
                         biconditional-token))
          ((some #'(lambda (head)
                     (and (typep head 'functional-proposition)
                          (aggregate-function-name-p (function-name head))
                          (slot-value head 'negatedp)))
                 head-propositions)
           (compiler-error
            "A proposition containing an aggregate function may not be negated"
            ))
          (t (values (if neck body) neck head head-propositions)))))

(defmethod parse-neck ((wff forward-rule))
  (let ((neck (read-token)))
    (cond ((not neck)
                                               ; Tail-less rule?
           nil)
          ((member neck rule-neck-tokens :test #'eq)
           neck)
          (t (compiler-error "Neck should be~{ ~S~^~#[~; or~:;,~]~} and not ~S"
                             rule-neck-tokens neck)))))

(defmethod parse-head ((wff forward-rule))
  "Parses head of rule: [not] PROPOSITION [and HEAD] ."
  (let (head)
    (setq head (parse-conjunction))
    (cond ((errorp head)
           head)
          ((next-token)
           (compiler-error "Unexpected expression in head of rule: ~S..."
                           (next-token)))
          (t head))))

(defmethod make-class-consumers (body head antecedent)
  (mapcar #'(lambda (conjunction)
              (make-instance 'conjunctive-class-consumer
                             'propositions (nconc (reverse conjunction)
                                               ; Reversal preserves
                                               ; source-form ordering - useful
                                               ; when debugging.
                                                  (list head))
                             'rule-source antecedent))
          (transform-to-dnf (if body (list (reduce-tree body))) nil)))

(defmethod make-class-consumers (body (head cons) antecedent)
  (let ((propositions (sort head #'>
                            :key #'(lambda (p)
                                     (length (attribute-references p))))))
    (do ((rest-propositions propositions (cdr rest-propositions))
         (last-propositions nil rest-propositions))
        ((endp rest-propositions))
      (when (singletonp (attribute-references (car rest-propositions)))
                          
        ;; Bring together the single-attribute-reference
        ;; propositions so that they can be satisfied as one.
        (if last-propositions
            (setf (cdr last-propositions) (list rest-propositions))
          (setf propositions (list propositions)))
        (return)))
    (call-next-method body propositions antecedent)))

(defmethod make-class-consumers ((body null) (head cons) antecedent)
  (mapcan #'(lambda (proposition)
              (make-class-consumers nil proposition antecedent))
    head))

(defmethod make-all-class-consumers (body neck head antecedent)
  (nconc (make-class-consumers body head antecedent)
         (if (eq neck biconditional-token)
             (make-class-consumers (list 'not body)
                                   (copy-instance head
                                                  'negatedp
                                                  (not nil))
                                   antecedent))))

(defmethod make-all-class-consumers :around (body neck head antecedent)
  (call-next-method body neck (if (singletonp head) (car head) head) antecedent))

(defmethod generate-class-consumers ((wff forward-rule) antecedent)
  (multiple-value-bind (body neck head head-propositions)
      (parse wff)
    (declare (ignore head))
    (if (errorp body)
        body
      (make-all-class-consumers body neck head-propositions antecedent))))

;;; General parsing routines

(defparameter *rewrite-in-parser* (not nil))

(defun parse-variable nil "Parse a variable of the form VAR-NAME ."
  (let (variable-name)
    (declare (special *declarations*))
    (cond ((not (symbolp (setq variable-name (read-token))))
           (compiler-error "\"~S\" is not a valid variable name" variable-name))
          ((assoc variable-name *declarations* :test #'eq))
          (t (compiler-error "Missing declaration for variable ~S"
                             variable-name)))))

(defun parse-variable-declaration nil
  "Parse a variable declaration of the form (VAR-NAME CLASS-NAME) ."
  (if (listp (next-token))
      (let ((*rule-source* (read-token))
            class-name variable-name)
        (declare (special *rule-source*))
        (cond ((not (symbolp (setq variable-name (read-token))))
               (compiler-error "\"~S\" is not a valid variable name"
                               variable-name))
              ((find-class (setq class-name (read-token)) nil)
               (make-variable :class-name class-name
                              :name variable-name))
              (t (compiler-error "\"~S\" is not a class" class-name))))
      (compiler-error "\"~S\" found instead of a variable declaration"
                      (next-token))))

(defun parse-declarations nil
   (if (listp (next-token))
       (let ((*rule-source* (read-token)))
         (declare (special *rule-source*))
         (do (variable
              (variables nil (cons variable variables)))
             ((null (next-token)) (nreverse variables))
           (when (errorp (setq variable (parse-variable-declaration)))
             (return variable))))
       (compiler-error "List of variable declarations expected")))

(defun parse-attribute-reference nil
  "Parses an attribute reference: VARIABLE SLOT-NAME ."
  (let (variable attribute-name)
    (cond ((errorp (setq variable (parse-variable)))
           variable)
          ((null (setq attribute-name (read-token)))
           (compiler-error "Attribute name expected after variable ~S"
                           variable))
          ((slot-name-p (find-class (variable-class-name variable))
                        attribute-name)
           (make-attribute-reference :attribute-reference-variable variable
                                     :attribute-name attribute-name))
          (t (compiler-error
                           "~S is an invalid attribute name for the variable ~S"
                           attribute-name variable)))))

(defun parse-condition nil "Parses a condition: DISJUNCTION [<-> CONDITION] ."
  (parse-formula ((disjunction (parse-disjunction))
                  <->
                  (condition (parse-condition)))

         (if *rewrite-in-parser*

             ;; A <-> B is re-written as (A or not B) and (not A or B).
             `(and (or ,disjunction (not ,condition))
                   (or ,condition (not ,disjunction)))
           (list biconditional-token disjunction condition))))

(defun parse-conjunction nil
  "Parses a conjunction: PRIMARY [and CONJUNCTION] ."
  (parse-formula ((primary (parse-primary))
                  and
                  (conjunction (parse-conjunction)))
         (list 'and primary conjunction)))

(defun parse-disjunction nil
  "Parses a disjunction: CONJUNCTION [or DISJUNCTION] ."
  (parse-formula ((conjunction (parse-conjunction))
                  or
                  (disjunction (parse-disjunction)))
         (list 'or conjunction disjunction)))

(defun parse-expression nil "Parses an expression: CONDITION [-> EXPRESSION] ."
  (let (expression)
    (setq expression (parse-formula ((condition (parse-condition))
                                     ->
                                     (expression (parse-expression)))

                            (if *rewrite-in-parser*
                                        
                                ;; A -> B is re-written as not A or B.
                                `(or (not ,condition)
                                     ,expression)
                              (list implication-token condition expression))))
    (cond ((errorp expression) expression)
          ((next-token)
           (compiler-error "\"~S\" is an invalid connective" (next-token)))
          (t expression))))

(defun parse-primary nil
  "Parses a primary: PROPOSITION | not PRIMARY | (EXPRESSION) ."
  (cond ((listp (next-token))
         (let ((*rule-source* (read-token)))
           (declare (special *rule-source*))
           (parse-expression)))
        ((eq (next-token) 'not)
         (read-token)
         (let ((expression (parse-primary)))
           (if (errorp expression) expression (list 'not expression))))
        (t (parse-proposition))))

(defun parse-proposition nil
  (cond ((eq (next-token) 'lisp)
         (read-token)
         (if (listp (next-token))
             (let ((*rule-source* (read-token)))
               (declare (special *rule-source*))
               (parse-lisp-proposition))
             (compiler-error "\"~S\" found instead of a lisp form"
                             (next-token))))
        (t (let ((attribute-reference (parse-attribute-reference))
                 type-specifier)
             (cond ((errorp attribute-reference)
                    attribute-reference)
                   ((subtypep (setq type-specifier
                                    (attribute-type attribute-reference))
                              'numeric-range)
                    (parse-numeric-or-arithmetic-proposition
                                                           attribute-reference))
                   ((subtypep type-specifier 'symbolic-range)
                    (parse-literal-proposition attribute-reference))
                   (t (parse-relational-proposition attribute-reference)))))))

(defun parse-lisp-proposition nil
  "Parses a lisp proposition: lisp (FUNCTION-NAME {ARG}+) ."
  (let (function-name)
    (if (symbolp (setq function-name (read-token)))

        ;; Parse the arguments to the function.
        (do (argument
             (arguments nil (cons argument arguments)))
            ((null (next-token))
             (if (notany #'attribute-reference-p arguments)
                 (compiler-error "At least one attribute reference required in a lisp proposition")
               (make-instance 'lisp-proposition
                              'function-name function-name
                              'arguments (nreverse arguments))))
          (setq argument (cond ((listp (next-token))
                                (parse-variable-declaration))
                               ((symbolp (next-token))
                                (parse-attribute-reference))))
          (when (errorp argument)
            (return argument))
          (unless argument
            (setq argument (read-token))))
        (compiler-error "~S is an illegal lisp function name" function-name))))

(defun parse-literal-proposition (attribute-reference)
  "Parses a proposition of the form: ATTRIBUTE-REFERENCE is [in] {{SYMBOL | ({SYMBOL}+)} | ATTRIBUTE-REFERENCE} ."

  ;; The first attribute reference has been used to determine the type of
  ;; proposition and comes in as the argument.
  (let (value)
    (if (eq (read-token) 'is)
        (cond ((eq (next-token) 'in)
               (read-token)
               (cond ((symbolic-rangep (setq value (read-token)))
                      
                      ;; List of symbols.
                      (let ((losers
                             (set-difference value
                                             (attribute-values attribute-reference)
                                             :test #'eq)))
                        (if losers
                            (compiler-error "~S are not valid for ~S"
                                            losers attribute-reference)
                          (make-instance 'literal-proposition
                                         'attribute-references
                                         (list attribute-reference)
                                         'value value))))
                     ((not (symbolp value))
                      (compiler-error "~S is not a range of values for ~S"
                                      value attribute-reference))
                     
                     ;; Symbol denoting a range (a class name).
                     ((subtypep value (attribute-type attribute-reference))
                      (make-instance 'literal-proposition
                                     'attribute-references
                                     (list attribute-reference)
                                     'value (range-elements value)))
                     (t (compiler-error "\"~S\" is not valid for ~S"
                                        value attribute-reference))))
              ((errorp (setq value
                             (if (member (next-token)
                                         (attribute-values attribute-reference)
                                         :test #'eq)
                                 (read-token)
                                 (parse-attribute-reference))))
               value)

              ;; Attribute reference or single symbol.
              ((symbolp value)
               (make-instance 'literal-proposition
                              'attribute-references (list attribute-reference)
                              'value (list value)))

              ;; Attribute reference.
              ((subtypep (attribute-type value)
                         (attribute-type attribute-reference))
               (make-instance 'literal-proposition
                              'attribute-references
                              (list value attribute-reference)))
              (t (compiler-error "\"~S\" is not valid for ~S"
                                 value attribute-reference)))
        (compiler-error "\"~S\" or \"~S ~S\" expected in a literal proposition"
                        'is 'is 'in))))

(defun parse-numeric-or-arithmetic-proposition (attribute-reference)
  "Parses proposition of form: ATTRIBUTE-REFERENCE {is in RANGE | is NUMBER | RELATION ARITHMETIC-RHS} ."

  ;; The first attribute reference has been used to determine the type of
  ;; proposition and comes in as the argument.
  (let ((token (read-token)))
    (cond ((eq token 'is)

           ;; Proposition containing a range or number.
           (let (value)
             (cond ((eq (next-token) 'in)
                    (read-token)
                    (cond ((and (numeric-rangep (setq value (read-token)))
                                (numeric-subrangep value
                                                   (attribute-values
                                                    attribute-reference)))
                           (make-instance 'numeric-proposition
                                          'attribute-references
                                          (list attribute-reference)
                                          'value value))
                          ((not (symbolp value))
                           (compiler-error "~S is not a range of values for ~S"
                                           value attribute-reference))
                          
                          ;; Symbol denoting a range (a class name).
                          ((subtypep value (attribute-type attribute-reference))
                           (make-instance 'numeric-proposition
                                          'attribute-references
                                          (list attribute-reference)
                                          'value (range-elements value)))
                          (t (compiler-error "\"~S\" is not valid for ~S"
                                             value attribute-reference))))
                   ((not (numberp (setq value (read-token))))
                    (compiler-error
                         "Number expected after \"~S\" in a numeric proposition"
                                       'is))
                   ((numeric-subrangep value
                                       (attribute-values attribute-reference))
                    (make-instance 'numeric-proposition
                                   'attribute-references
                                   (list attribute-reference)
                                   'value value))
                   (t (compiler-error "~S is invalid for ~S"
                                      value attribute-reference)))))
          ((not (member token '(= /= <= >= < >) :test #'eq))
           (compiler-error
                     "\"~S\" is invalid for a numeric or arithmetic proposition"
                           token))

          ;; Proposition containing an arithmetic expression.
          ((not (and *rewrite-in-parser*
                     (let ((token (read-token)))
                       (prog1 (and (numberp token)
                                   (not (operatorp (next-token))))
                         (unread-token token)))
                                               ; Is arithmetic expression just
                                               ; a number?
                     ))
           (let ((arithmetic-rhs (parse-arithmetic-rhs)))
             (cond ((errorp arithmetic-rhs)
                    arithmetic-rhs)
                   ((or (numberp arithmetic-rhs)
                        (not (function-name-p (car arithmetic-rhs))))
                    (make-instance 'arithmetic-proposition
                                   'attribute-references
                                   (list attribute-reference)
                                   'relation token
                                   'prefix-rhs arithmetic-rhs))
                   ((and (aggregate-function-name-p (car arithmetic-rhs))
                         (not (eq token '=)))
                    (compiler-error "\"~S\" expected before an aggregate function"
                                    '=))
                   (t (make-instance 'functional-proposition
                                     'attribute-references
                                     (list attribute-reference)
                                     'relation token
                                     'function-name (car arithmetic-rhs)
                                     'arguments (cdr arithmetic-rhs))))))
          (t
             ;; Proposition containing a numeric relation and a number.
           (let ((negated (eq token '/=))
                 (attribute-values (attribute-values attribute-reference))
                 (value (read-token)))
               (if (numeric-subrangep value attribute-values)
                   (make-instance 'numeric-proposition
                                  'attribute-references
                                  (list attribute-reference)
                                  'negatedp negated
                                  'value
                                  (satisfy-relation attribute-values
                                                    (if negated '= token)
                                                    value))
                 (compiler-error "~S is invalid for ~S"
                                 value attribute-reference)))))))

(defun parse-relational-proposition (attribute-reference)
  "Parses a proposition of form: ATTRIBUTE-REFERENCE [is | includes] VARIABLE ."

  ;; The first attribute reference has been used to determine the type of
  ;; proposition and comes in as the argument.
  (let (token count specializer)
    (when (member (next-token) '(is includes) :test #'eq)
      (setq token (read-token)))
    (cond ((or (null (setq count
                          (attribute-count attribute-reference)))
               (and (eq token 'includes)
                    (unbounded> (range-max count) 1))
               (eql (range-max count) 1))
           (setq specializer (parse-variable))
           (if (errorp specializer)
               specializer
               (make-instance 'relational-proposition
                              'specializer specializer
                              'attribute-references
                              (list attribute-reference))))
          ((eq token 'includes)
           (compiler-error
                      "\"~S\" invalid with count declaration of ~S for ~S"
                      token attribute-reference count))
          (t (compiler-error
                     "\"~S\" expected with count declaration of ~S for ~S"
                     'includes attribute-reference count)))))

(defun parse-factor nil
  "Parses a factor of an arithmetic expression: (ARITHMETIC-EXPR) | NUMBER | ATTRIBUTE-REFERENCE | - FACTOR ."
  (let (token factor)
    (cond ((listp (setq token (next-token)))
                                               ; Bracketed expression?
           (let ((*rule-source* (read-token)))
             (declare (special *rule-source*))
             (parse-arithmetic-expression)))
          ((numberp token)
                                               ; Number?
           (read-token))
          ((eq token '-)
                                               ; Negated expression?
           (read-token)
           (setq factor (parse-factor))
           (if (errorp factor) factor (list '- factor)))
          ((errorp (setq factor (parse-attribute-reference)))
           factor)
          ((subtypep (attribute-type factor) 'numeric-range)
                                               ; Numeric attribute reference?
           factor)
          (t (compiler-error
                            "~S should be a numeric attribute reference, not ~S"
                            factor (attribute-type factor))))))

(defun parse-rest-of-expression (factor-stack operator-stack)
  "Parse the remainder of an arithmetic expression following a factor."
  (let (factor (operator (next-token)))
    (cond ((operatorp operator)
           (read-token)

           ;; Now pop operators off the stack until the new operator
           ;; is of higher precedence.
           (do ((top-of-op-stack (car operator-stack)
                                 (car operator-stack)))
               ((not (and top-of-op-stack
                          (higher-precedence-p top-of-op-stack
                                               operator)))
                (if (errorp (setq factor (parse-factor)))
                    factor
                  (parse-rest-of-expression (cons factor factor-stack)
                                            (cons operator operator-stack))))
             (setq factor-stack (cons (list (pop operator-stack)
                                            (cadr factor-stack)
                                            (car factor-stack))
                                      (cddr factor-stack)))))
          (t
             ;; No more operators follow so pop everything from the
             ;; resulting top of the factor stack.
             (do ((top-of-op-stack (pop operator-stack)
                                   (pop operator-stack)))
                 ((not top-of-op-stack) (car factor-stack))
               (setq factor-stack (cons (list top-of-op-stack
                                              (cadr factor-stack)
                                              (car factor-stack))
                                        (cddr factor-stack))))))))

(defun parse-arguments nil
  "Parse the arguments (numeric attribute references or numbers) to a function."
  (do (argument attribute-reference
       (arguments nil (cons argument arguments)))
      ((null (next-token)) (nreverse arguments))
    (setq argument (cond ((numberp (next-token))
                          (read-token))
                         ((errorp (setq attribute-reference
                                        (parse-attribute-reference)))
                          (return attribute-reference))
                         (t attribute-reference)))))

(defun parse-arithmetic-expression nil
  (let ((factor (parse-factor)))
    (if (errorp factor)
        factor
        (parse-rest-of-expression (list factor) nil))))

(defun parse-arithmetic-rhs nil
  (flet ((invalid-argument-p (function-name arguments)
           (if (aggregate-function-name-p function-name)
               (or (/= (length arguments) 2)
                   (notevery #'attribute-reference-p arguments)
                   (not (subtypep (attribute-reference-class (cadr arguments))
                                  (find-class (attribute-type (car arguments)) nil)))
                   (not (subtypep (attribute-type (cadr arguments))
                                  'numeric-range)))
             (notevery #'(lambda (argument)
                           (or (numberp argument)
                               (subtypep (attribute-type argument)
                                     'numeric-range)))
                       arguments))))
    (if (function-name-p (next-token))
        (let ((function-name (read-token)))
          (if (listp (next-token))
              (let (arguments
                    (*rule-source* (read-token)))
                (declare (special *rule-source*))
                (setq arguments (parse-arguments))
                (cond ((errorp arguments)
                       arguments)
                      ((invalid-argument-p function-name arguments)
                       (compiler-error "Illegal number or type of arguments for the function ~S"
                                       function-name))
                      (t (cons function-name arguments))))
            (compiler-error "List of arguments expected after the function ~S"
                            function-name)))
      (parse-arithmetic-expression))))

;;; Auxiliary functions for parser

(defun attribute-count (attribute-reference &aux count-slot-name count-slot-definition)
  (and (setq count-slot-name
             (find-slot-definition (attribute-reference-class attribute-reference)
                                   (attribute-name attribute-reference)))
       (setq count-slot-definition
             (find-slot-definition (attribute-reference-class attribute-reference)
                                   count-slot-name))
       (slot-definition-count-max count-slot-definition)))

(defun attribute-values (attribute-reference)
  (range-elements (attribute-type attribute-reference)))

(defun attribute-type (attribute-reference)
  "Returns type of attribute named by attribute reference."
  (slot-definition-type
   (find-slot-definition (attribute-reference-class attribute-reference)
                         (attribute-name attribute-reference))))

(defun function-name-p (symbol)
  (member symbol '(aggregate-min aggregate-max aggregate-sum min max) :test #'eq))

(defun aggregate-function-name-p (symbol)
  (member symbol '(aggregate-min aggregate-max aggregate-sum) :test #'eq))

(defun higher-precedence-p (op1 op2)
  (macrolet ((memq (item list)
               `(member ,item ,list :test #'eq)))
    (not (and (memq op1 '(- +))
              (memq op2 '(/ *))))))

(defun next-token nil (declare (special *rule-source*))
  (car *rule-source*))

(defun operatorp (token)
  (member token '(+ - * /) :test #'eq))

(defun read-token nil
  (declare (special *rule-source*))
  (pop *rule-source*))

(defun unread-token (token)
  (declare (special *rule-source*))
  (push token *rule-source*))

;;; Auxiliary functions for compiler (consumer generation)

(defun reduce-tree (tree)
  "Moves all the NOTs to the leaves of an and-or-not tree."
  (if (listp tree)
      (ecase (car tree)
        (and (list 'and
                   (reduce-tree (cadr tree))
                   (reduce-tree (caddr tree))))
        (or (list 'or
                  (reduce-tree (cadr tree))
                  (reduce-tree (caddr tree))))
        (not (negate-tree (cadr tree))))
    tree                                       ; A proposition.
    ))

(defun negate-tree (tree)
  "Negates, and moves all the NOTs to the leaves of, an and-or-not tree."
  (if (listp tree)
      (ecase (car tree)
        (and (list 'or
                   (negate-tree (cadr tree))
                   (negate-tree (caddr tree))))
                                               ; De Morgan's law.
        (or (list 'and
                  (negate-tree (cadr tree))
                  (negate-tree (caddr tree))))
                                               ; De Morgan's law.
        (not (reduce-tree (cadr tree))))       ; Two NOTs cancel.
    (negate tree)
                                               ; A proposition.
    ))

(defun transform-to-cnf (and-or-trees disjunction)
  "Transform an implicitly disjoined list of and-or trees to conjunctive normal form."
  (if and-or-trees
      (let ((first-tree (car and-or-trees)))
        (if (listp first-tree)
            (ecase (car first-tree)
              (and (append (transform-to-cnf (cons (cadr first-tree)
                                                   (cdr and-or-trees))
                                             disjunction)
                           (transform-to-cnf (cons (caddr first-tree)
                                                   (cdr and-or-trees))
                                             disjunction)))
                                               ; Get the conjunction over the
                                               ; two sub-trees.
              (or (transform-to-cnf (cons (cadr first-tree)
                                          (cons (caddr first-tree)
                                                (cdr and-or-trees)))
                                    disjunction)))
                                               ; Split an or-tree into its two
                                               ; sub-trees.
          (transform-to-cnf (cdr and-or-trees)
                            (cons first-tree disjunction))))
      (list disjunction)))

(defun transform-to-dnf (and-or-trees conjunction)
  "Transform an implicitly conjoined list of and-or trees to disjunctive normal form."
  (if and-or-trees
      (let ((first-tree (car and-or-trees)))
        (if (listp first-tree)
          (ecase (car first-tree)
            (and (transform-to-dnf (cons (cadr first-tree)
                                         (cons (caddr first-tree)
                                               (cdr and-or-trees)))
                                   conjunction)) ; Split an and-tree into its
                                               ; two sub-trees.
            (or (append (transform-to-dnf (cons (cadr first-tree)
                                                (cdr and-or-trees))
                                          conjunction)
                        (transform-to-dnf (cons (caddr first-tree)
                                                (cdr and-or-trees))
                                          conjunction))))
                                               ; Get the disjunction over the
                                               ; two sub-trees.
          (transform-to-dnf (cdr and-or-trees)
                            (cons first-tree conjunction))))
      (list conjunction)))

(defun simplify-disjunction (propositions)
  "Combine propositions in disjunction mentioning the same single attribute."
  (do ((initial-propositions propositions (cdr initial-propositions))
       (final-propositions nil (absorb (car initial-propositions)
                                       final-propositions
                                       #'disjoin)))
      ((endp initial-propositions)
       (if (some #'tautologousp final-propositions)
           nil
                                               ; Whole disjunction can be
                                               ; discarded.
           final-propositions))))

;;; Querying of rule objects

(defmethod slot-affected ((wff forward-rule))
  "Returns an attribute reference denoting the slot affected by a rule."
  (car (last (attribute-references
              (car (last (propositions
                          (car (class-consumers wff t)))))))))

(defmethod slots-used ((wff well-formed-formula) &aux attribute-references)
  "Returns those attribute references noticed by a rule."
  (dolist (c (class-consumers wff t))
    (do ((rest-propositions (propositions c)
                            (rest-propositions rest-propositions)))
        ((endp rest-propositions))
      (unless (singletonp rest-propositions)
                                               ; Head proposition?
        (do ((rest-attribute-references (attribute-references
                                         (car rest-propositions))
                                        (cdr rest-attribute-references)))
            ((endp rest-attribute-references))
          (pushnew (car rest-attribute-references)
                   attribute-references
                   :test #'(lambda (x y)
                             (and (eq (attribute-reference-class x)
                                      (attribute-reference-class y))
                                  (eq (attribute-name x)
                                      (attribute-name y)))))))))
  attribute-references)
