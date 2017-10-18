;;; Copyright (C) 2007-2014, 2017 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html


(in-package reasoner)

;;; Slot values

(defclass standard-slot-value (node)
    ((object :reader datum-object :initarg :object)
     (slot-name :reader datum-slot :initarg :slot-name)
     (value :reader datum-value :initarg :value)))

(defclass excluded-slot-value (standard-slot-value)
    ())

(defmethod print-object ((instance standard-slot-value) stream)
  (print-unreadable-object (instance stream)
    (format stream "~:(~S~) ~S"
            (class-name (class-of instance))
            (datum-value instance)))
  instance)

(defmethod combine ((n1 standard-slot-value)
                    (n2 standard-slot-value))
  "Combine two slot values to yield a single value."
  (combine1 (datum-value n1) (datum-value n2)))

(defmethod combine ((values t)
                    (n standard-slot-value))
  "Combine an arbitrary combination of values and a STANDARD-SLOT-VALUE object."
  (combine1 values (datum-value n)))

(defmethod combine ((values null)
                    (n standard-slot-value))
  nil)

(defmethod combine ((n1 standard-slot-value)
                    (n2 excluded-slot-value))
  (combine1 (datum-value n1) n2))

(defmethod combine ((n1 excluded-slot-value)
                    (n2 standard-slot-value))
  (combine1 n1 (datum-value n2)))

(defmethod combine ((n1 excluded-slot-value)
                    (n2 excluded-slot-value))
  (combine1 n1 n2))

(defmethod combine ((values t)
                    (n excluded-slot-value))
  "Combine a combination of values and an EXCLUDED-SLOT-VALUE object."
  (combine1 values n))

(defmethod combine1 ((value1 t)
                     (value2 t))
  (if (combinep value1 value2)
      (list value2 value1)))

(defmethod combine1 ((values cons)
                     (value excluded-slot-value))
  (combine2 values value))

(defmethod combine2 ((values cons)
                     (value t))
  (if (every #'(lambda (element)
                 (combinep element value))
             values)
      (cons value values)))

(defmethod combinep ((value t)
                     (n excluded-slot-value))
  (not (slot-value-equal value n t)))

(defmethod combinep ((n excluded-slot-value)
                     (value t))
  (not (slot-value-equal value n t)))

(defmethod combinep ((n1 excluded-slot-value)
                     (n2 excluded-slot-value))
  (not nil))

(defmethod combinep ((value1 t)
                     (value2 t))
  (not nil))

(defmethod slot-value-equal ((value t)
                             (n standard-slot-value)
                             &optional (negatedp nil))
  (if negatedp
      nil
      (slot-value-equal-1 value n)))

(defmethod slot-value-equal ((value t)
                             (n excluded-slot-value)
                             &optional (negatedp nil))
  (if negatedp
      (slot-value-equal-1 value n)))

(defmethod slot-value-equal-1 ((value1 t)
                               (value2 standard-slot-value))
  (equal value1 (datum-value value2)))

(defmethod elements ((node standard-slot-value))
  "Returns a list of the value(s) denoted by a standard-slot-value."
  (list (datum-value node)))

(defmethod elements ((node excluded-slot-value))
  (list node))

(defconstant contradictory-value '?
  "The value returned when slot values cannot be combined.")

(defun contradictory-value-p (value)
  (eq value contradictory-value))

;;; Ranges

(defclass range-class (standard-class)
  ((elements :reader elements :initarg :elements)
   (external-type :reader direct-external-type :initarg :external-type)
   (effective-external-type :accessor external-type))
  (:default-initargs
     :external-type nil
     ))

(defmethod direct-external-type ((class t))
  nil)

(defmethod finalize-inheritance :after ((class range-class))
  (let ((superclass (find nil (class-precedence-list class)
                          :key #'direct-external-type :test-not #'eq)))
    (setf (external-type class) (if superclass
                                    (direct-external-type superclass)))))

(defmacro range-elements (name)
  `(elements (find-class ,name)))

(defmacro range-external-type (name)
  `(or (let ((class (find-class ,name)))
         (unless (class-finalized-p class) (finalize-inheritance class))
         (external-type class))
       ,name))

(eval-when (:execute #+lispworks :compile-toplevel :load-toplevel)
(defmethod validate-superclass ((class range-class)
                                (superclass standard-class))
  "Declare compatibility of RANGE-CLASS and standard-class."
  (not nil))
)

(defclass range (standard-slot-value)
    ((value :reader elements))
  (:metaclass range-class))

;;; (defclass numeric-range (range)
;;;     ()
;;;   (:metaclass range-class)
;;;   (:elements (-big big)))
;;; 
;;; (defclass symbolic-range (range)
;;;     ()
;;;   (:metaclass range-class))

#+(or allegro ecl sbcl)
(defstruct (numeric-range (:type list)) "A set of consecutive integers."
  min max)
#-(or allegro ecl sbcl)
(progn
(defmacro make-numeric-range (&key min max) `(list ,min ,max))
(defmacro numeric-range-min (numeric-range) `(car ,numeric-range))
(defmacro numeric-range-max (numeric-range) `(cadr ,numeric-range))
)

(progn
(defmacro make-range-set (&key elements) `(cons 'range-set ,elements))
(defmacro range-set-elements (range-set) `(cdr ,range-set))
)

(deftype range-set nil
  "A set of numeric ranges, representing an arbitrary set of integers."
  '(satisfies range-set-p))

(defun range-set-p (x) (if (listp x) (eq (car x) 'range-set)))

(deftype symbolic-range* nil '(satisfies symbolic-rangep))

(deftype numeric-range* nil '(satisfies numeric-rangep))

(deftype unbounded-number nil '(satisfies unbounded-number-p))

(defmethod symbolic-rangep ((x t))
  nil)

(defmethod symbolic-rangep ((x list))
  (every #'symbolp x))

(defmethod symbolic-rangep ((x null))
  nil)

(defmethod numeric-rangep ((x t))
  nil)

(defmethod numeric-rangep ((x list))
  (flet ((unbounded-number-p (x)
                  (or (numberp x)
                      (unbounded-number-p x))))
    (and (eql (length x) 2)
         (unbounded-number-p (car x))
         (unbounded-number-p (cadr x))
         (unbounded>= (cadr x) (car x)))))

(defun unbounded-number-p (x)
  (member x '(big -big) :test #'eq))

(defun slot-value-typep (object type
                         &optional (check-bounds (not (eq type 'symbolic-range))))
  "Determines if object is of type, where type may be a range and object a number, symbol, or list thereof."
  (typecase object
    ((or number numeric-range*) (and (subtypep type 'numeric-range)
                                     (or (not check-bounds)
                                         (numeric-subrangep object
                                                            (range-elements type)))))
    (symbol (and (subtypep type 'symbolic-range)
                 (or (not check-bounds)
                     (member object
                             (range-elements type)
                             :test #'eq))))
    (symbolic-range* (and (subtypep type 'symbolic-range)
                          (or (not check-bounds)
                              (subsetp object
                                       (range-elements type)
                                       :test #'eq))))
    (t
     ;; True instance or arbitrary Lisp object.
     (typep object type))))

(defmacro defrange (&rest args)
  (multiple-value-bind (name include external-type documentation body)
      (parse-defrange args)
    `(ensure-range-class ',name
                         :include ',include
                         :external-type ',external-type
                         :documentation ,documentation
                         :elements ',body)))

(defun parse-defrange (args)
  (let* ((options (if (consp (car args))
                      (cdar args)))
         (name (if options
                   (caar args)
                   (car args)))
         (documentation nil)
         (body (cdr args)))
    (when (stringp (car body))
      (setq documentation (pop body)))
    (when (and (numberp (car body))
               (endp (cdr body)))
      (setq body (make-numeric-range :min (car body) :max (car body))))
    (values name
            (cadr (assoc :include options :test #'eq))
            (cadr (assoc :external-type options :test #'eq))
            documentation
            body)))

(defun ensure-range-class-using-class (class class-name
                                       &rest initargs
                                       &key elements
                                       &allow-other-keys)
  (declare (ignorable elements))
  (apply #'ensure-class-using-class
         class
         class-name
         :metaclass 'range-class
         (nconc #+(and mop (not allegro))
                (if elements
                    (list :direct-default-initargs
                      `((:value ',elements ,(constantly elements)))))
                initargs)))

(defun ensure-range-class (name &key include external-type documentation elements
                                &aux (class (find-class name nil)))
  (labels ((find-include (superclass elements)
             (or (dolist (subrange (class-direct-subclasses superclass))
                   (unless (or (eq class subrange)
                               (equal elements (elements subrange)))
                     (when (subsetp elements (elements subrange))
                       (return (find-include subrange elements)))))
                 superclass)))
    (let (superclasses)
      (setq superclasses (list (or (and include (find-class include nil))
                                   (etypecase elements
                                     (numeric-range* (find-class 'numeric-range))
                                     (symbolic-range*
                                      (find-include (find-class 'symbolic-range)
                                                    elements))))))
      (ensure-range-class-using-class class
                                      name
                                      :direct-superclasses superclasses
                                      :external-type external-type
                                      :documentation documentation
                                      :elements elements))))

(defun numeric-subrangep (range1 range2)
  (and (unbounded>= (range-min range1)
                    (range-min range2))
       (unbounded<= (range-max range1)
                    (range-max range2))))

(defun numeric-range-intersection (range1 range2)
  (labels ((numeric-range-intersection-internal (range1 range2)
             (let ((min (unbounded-max (range-min range1)
                                       (range-min range2)))
                   (max (unbounded-min (range-max range1)
                                       (range-max range2))))
               (cond ((unbounded> min max) nil)
                     ((and (eql min (range-min range1))
                           (eql max (range-max range1)))
                      range1)
                     ((and (eql min (range-min range2))
                           (eql max (range-max range2)))
                      range2)
                     (t (make-numeric-range :min min :max max)))))
           (combine-ranges (element-or-set set &aux (result ()))
             "Combines two range sets, or a single range with a range set."
             (do ((element-or-rest-set element-or-set)
                  (is-set (not (numeric-rangep element-or-set)))
                  (rest-set set)
                  element
                  new-element)
                 ((or (and is-set (endp element-or-rest-set))
                      (endp rest-set)))
               (setq element (if is-set
                                 (car element-or-rest-set)
                               element-or-rest-set)
                   new-element (numeric-range-intersection-internal element
                                                                    (car rest-set)))
               (when new-element
                     (push new-element result))
               (cond ((unbounded> (range-max element) (range-max (car rest-set)))
                      (pop rest-set))
                     (is-set
                      (pop element-or-rest-set))
                     (t (return))))
             (nreverse result)))
    (if (or (typep range1 'range-set)
            (typep range2 'range-set))
        (let ((elements (cond ((not (typep range1 'range-set))
                               (combine-ranges range1 (range-set-elements range2)))
                              ((not (typep range2 'range-set))
                               (combine-ranges range2 (range-set-elements range1)))
                              (t (combine-ranges (range-set-elements range1)
                                                 (range-set-elements range2))))))
          (cond ((singletonp elements)
                 (car elements))
                (elements
                 (make-range-set :elements elements))))
        (numeric-range-intersection-internal range1 range2))))

(defun numeric-range-negation (numeric-range)
  (make-numeric-range :min (unbounded- (range-max numeric-range))
                      :max (unbounded- (range-min numeric-range))))

(defun numeric-range-union (range1 range2)
  (let ((min (unbounded-min (range-min range1)
                            (range-min range2)))
        (max (unbounded-max (range-max range1)
                            (range-max range2))))
   (if (unbounded<= min max)
       (make-numeric-range :min min :max max))))

(defun unary-minus-p (arithmetic-expression)
  (and (eq (car arithmetic-expression) '-)
       (endp (cddr arithmetic-expression))))

(defun range-eval (arithmetic-expression)
  "Evaluator for prefix arithmetic expressions containing ranges."
  (flet ((numeric-rangep (arithmetic-expression)
           (or (numberp arithmetic-expression)
               (unbounded-number-p arithmetic-expression)
               (range-set-p arithmetic-expression)
               (numeric-rangep arithmetic-expression))))
    (cond ((numeric-rangep arithmetic-expression)
           arithmetic-expression)
          ((unary-minus-p arithmetic-expression)
           (numeric-range-negation (range-eval (cadr arithmetic-expression))))
          (t (range-apply (car arithmetic-expression)
                          (range-eval (cadr arithmetic-expression))
                          (range-eval (caddr arithmetic-expression)))))))

(defun range-apply (arithmetic-operator range1 range2 &aux fn)
  (flet ((unbounded+ (&rest numbers)
           (macrolet ((memq (item list) `(member ,item ,list :test #'eq)))
             (cond ((memq 'big numbers)
                    (if (memq '-big numbers)
                        (error "Attempt to add ~S and ~S" 'big '-big)
                        'big))
                   ((memq '-big numbers)
                    (if (memq 'big numbers)
                        (error "Attempt to add ~S and ~S" 'big '-big)
                        '-big))
                   (t (apply #'+ numbers)))))
         (unbounded* (&rest numbers)
                                               ; Currently takes exactly two
                                               ; arguments.
           (let ((min (apply #'unbounded-min numbers))
                 (max (apply #'unbounded-max numbers)))
             (cond ((eq min 'big) 'big)
                   ((eq min '-big)
                    (case max
                      (big '-big)
                      (-big 'big)
                      (t (if (plusp max) '-big 'big))))
                   ((eq max 'big) 'big)
                   (t (apply #'* numbers)))))
         (unbounded/ (&rest numbers)
                                               ; Currently takes exactly two
                                               ; arguments.
           (cond ((eq (first numbers) 'big)
                  (case (second numbers)
                    (big 'big)
                    (-big '-big)
                    (t (if (plusp (second numbers)) 'big '-big))))
                 ((eq (first numbers) '-big)
                  (case (second numbers)
                    (big '-big)
                    (-big 'big)
                    (t (if (plusp (second numbers)) '-big 'big))))
                 ((unbounded-number-p (second numbers)) 0)
                 (t (/ (first numbers) (second numbers))))))
    (setq fn (ecase arithmetic-operator
               (+ #'unbounded+)
               (- #'unbounded-)
               (* #'unbounded*)
               (/ #'unbounded/)))
    (funcall #'(lambda (combinations)
                 (make-numeric-range :min (apply #'unbounded-min
                                                 combinations)
                                     :max (apply #'unbounded-max
                                                 combinations)))
             (list (funcall fn (range-min range1)
                               (range-min range2))
                   (funcall fn (range-max range1)
                               (range-max range2))
                   (funcall fn (range-min range1)
                               (range-max range2))
                   (funcall fn (range-max range1)
                               (range-min range2))))))

(defun invert-relation (numeric-relation)
  (ecase numeric-relation
    (= '/=)
    (/= '=)
    (< '>=)
    (> '<=)
    (>= '<)
    (<= '>)))

(defun flip-relation (numeric-relation)
  (case numeric-relation
    (< '>)
    (> '<)
    (>= '<=)
    (<= '>=)
    (t numeric-relation)))

(defun numeric-range-disjointp (range-or-set range)
  (flet ((range-disjointp (range1 range2)
           (or (unbounded> (range-min range1)
                           (range-max range2))
               (unbounded< (range-max range1)
                           (range-min range2)))))
    (if (numeric-rangep range-or-set)
        (range-disjointp range-or-set range)
      (every #'(lambda (element)
                 (range-disjointp element range))
             (range-set-elements range-or-set)))))

(defun relation-satisfied-p (range1 relation range2)
  "Determine if relation holds between the two ranges."
  (ecase relation
    (= (and (unbounded= (range-min range1)
                        (range-max range1))
            (unbounded= (range-min range2)
                        (range-max range2))
            (unbounded= (range-min range1)
                        (range-min range2))))
    (/= (numeric-range-disjointp range1 range2))
    (> (unbounded> (range-min range1)
                   (range-max range2)))
    (< (unbounded< (range-max range1)
                   (range-min range2)))
    (>= (unbounded>= (range-min range1)
                     (range-max range2)))
    (<= (unbounded<= (range-max range1)
                     (range-min range2)))))

(defun unbounded1+ (number)
  (if (unbounded-number-p number) number (1+ (floor number))))

(defun unbounded1- (number)
  (if (unbounded-number-p number) number (1- (ceiling number))))

(defun satisfy-relation (range relation sub-range)
  "Returns that sub-range that satisfies a relation between a range and a sub-range."
  (ecase relation
    (= (make-numeric-range :min (unbounded-max (range-min range)
                                               (range-min sub-range))
                           :max (unbounded-min (range-max range)
                                               (range-max sub-range))))
    (/= (satisfy-not-equal range (if (eql (range-min sub-range)
                                          (range-max sub-range))
                                     (round (range-min sub-range))
                                   sub-range)))
    (> (make-numeric-range :min (unbounded1+ (range-min sub-range))
                           :max (range-max range)))
    (< (make-numeric-range :min (range-min range)
                           :max (unbounded1- (range-max sub-range))))
    (>= (make-numeric-range :min (range-min sub-range)
                            :max (range-max range)))
    (<= (make-numeric-range :min (range-min range)
                            :max (range-max sub-range)))))

(defun satisfy-not-equal (range1 range2)
  "Returns the sub-range of the first range not contained in the second."
  (cond ((numeric-range-disjointp range1 range2)
                                               ; Disjoint ranges?
         range1)
        ((and (unbounded< (range-min range1)
                          (range-min range2))
              (unbounded> (range-max range1)
                          (range-max range2)))
                                               ; Exclusion of middle?
         (make-range-set
                :elements (list
                           (make-numeric-range :min (range-min range1)
                                               :max (unbounded1- (range-min range2)))
                           (make-numeric-range :min (unbounded1+ (range-max range2))
                                               :max (range-max range1))))
                                               ; Return two sub-ranges.
         )
        ((unbounded< (range-min range1)
                     (range-min range2))
                                               ; Top of first range overlaps
                                               ; bottom of second?
         (make-numeric-range :min (range-min range1)
                             :max (unbounded1- (range-min range2))))
        ((unbounded> (range-max range1)
                     (range-max range2))
                                               ; Top of second range overlaps
                                               ; bottom of first?
         (make-numeric-range :min (unbounded1+ (range-max range2))
                             :max (range-max range1)))
        (t (error "Could not determine sub-range of ~S not contained in ~S."
             range1 range2))))

(defun range-max (x)
  (etypecase x
    ((or number unbounded-number) x)
    (range-set (range-set-max x))
    (numeric-range* (numeric-range-max x))))

(defun range-min (x)
  (etypecase x
    ((or number unbounded-number) x)
    (range-set (range-set-min x))
    (numeric-range* (numeric-range-min x))))

(defun range-set-max (range-set)
  "Returns largest of an arbitrary set of integers."
  (range-max (first (last (range-set-elements range-set)))))

(defun range-set-min (range-set)
  "Returns smallest of an arbitrary set of integers."
  (range-min (first (range-set-elements range-set))))

(defun unbounded- (number &rest more-numbers)
                                               ; Currently takes one or two
                                               ; arguments only.
  (cond ((unbounded-number-p number)
         (if (eq number (car more-numbers))
             (error "Attempt to subtract ~S and ~S" number number)
             number))
        ((eq (car more-numbers) 'big)
         '-big)
        ((eq (car more-numbers) '-big)
         'big)
        ((car more-numbers)
         (- number (car more-numbers)))
        (t (- number))))

(defun unbounded-max (number &rest more-numbers)
  (cond ((or (eq number 'big)
             (member 'big more-numbers :test #'eq))
         'big)
        ((not (eq number '-big))
         (apply #'max number (remove '-big more-numbers :test #'eq)))
        ((singletonp more-numbers)
         (car more-numbers))
        (t (apply #'max (remove '-big more-numbers :test #'eq)))))

(defun unbounded-min (number &rest more-numbers)
  (cond ((or (eq number '-big)
             (member '-big more-numbers :test #'eq))
         '-big)
        ((not (eq number 'big))
         (apply #'min number (remove 'big more-numbers :test #'eq)))
        ((singletonp more-numbers)
         (car more-numbers))
        (t (apply #'min (remove 'big more-numbers :test #'eq)))))

(defun unbounded< (number &rest more-numbers)
                                               ; Currently takes exactly two
                                               ; arguments.
  (unbounded> (car more-numbers) number))

(defun unbounded<= (number &rest more-numbers)
                                               ; Currently takes exactly two
                                               ; arguments.
  (not (unbounded> number (car more-numbers))))

(defun unbounded= (number &rest more-numbers)
                                               ; Currently takes exactly two
                                               ; arguments.
  (eql number (car more-numbers)))

(defun unbounded> (number &rest more-numbers)
                                               ; Currently takes exactly two
                                               ; arguments.
  (cond ((eql number (car more-numbers)) nil)
        ((eq number 'big))
        ((eq number '-big) nil)
        ((eq (car more-numbers) 'big) nil)
        ((eq (car more-numbers) '-big))
        (t (> number (car more-numbers)))))

(defun unbounded>= (number &rest more-numbers)
                                               ; Currently takes exactly two
                                               ; arguments.
  (not (unbounded< number (car more-numbers))))

;;; Slot-value combination

(defmethod combine ((value t)
                    (r range))
  (range-intersection value r))

(defmethod combine ((range1 range)
                    (range2 range))
  "Combine two ranges to yield a single range."
  (range-intersection range1 range2))
