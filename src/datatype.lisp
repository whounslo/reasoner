;;; Copyright (C) 2012, 2013 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; XML Schema built-in datatypes

(in-package :reasoner-ext)

(defconstant field-missing-indicator 'field-missing)

(defun parse-integers (string start end predicate &rest flags)
  (do ((rest-flags flags (rest rest-flags))
       (i 1 (1+ i))
       (bound end)
       (end start)
       object
       (integers nil (cons (if (first rest-flags) object 0) integers))
       (start start end))
      ((endp rest-flags) integers)
    (when (first rest-flags)
      (multiple-value-setq (start end)
        (find-token string start bound #'(lambda (ch) (funcall predicate ch i))))
      (setq object (or (parse-integer string
                                      :start start
                                      :end end
                                      :junk-allowed (not nil))
                       field-missing-indicator)))))

;;; Date, time

(defconstant xml-date-separator #\-)

(defconstant xml-time-separator #\:)

(defconstant xml-date-time-separator #\T)

(defconstant xml-time-zone-separator #\+)

(defconstant xml-time-zone-indicator #\Z)

(defparameter *date-time-encoding-fn* #'encode-universal-time)

(defparameter *date-time-decoding-fn* #'decode-universal-time)

(defun leap-year-p (year)
  (and (zerop (mod year 4))
       (or (not (zerop (mod year 100))) (zerop (mod year 400)))))

(defun last-day (month &optional year)
  (case month
    (2 (if (and year (leap-year-p year)) 29 28))
    ((9 4 6 11) 30)
    (t 31)))

(defun negativep (object)
  (declare (type string object))
  (eq (char object 0) #\-))

(defun parse-date-time (string start end &rest flags &aux integers)
  (setq integers
    (apply #'parse-integers
             string
             start
             end
             #'(lambda (ch i)
                 (cond
                   ((eq ch xml-date-separator) (or (< i 5) (> i 5)))
                                               ; Also a time zone separator.
                   ((eq ch xml-date-time-separator) (or (= i 3) (= i 4)))
                   ((eq ch xml-time-separator) (> i 3))
                   ((eq ch xml-time-zone-separator) (or (> i 1) (< i 5) (> i 5)))
                   ((eq ch xml-time-zone-indicator) (= i 6))))
             flags))
  (when (find field-missing-indicator integers :start 1)
    (error "Malformed date or time encountered: ~A." string))
  (cond ((eq (first integers) field-missing-indicator)
         (setf (first integers) 0))
        ((find xml-time-zone-separator string)
         (setf (first integers) (- (first integers)))))
  (when (negativep string)
    (let ((last (last integers)))
      (setf (first last) (- (first last)))))
  (values-list integers))

(defmacro convert-to-universal-time (&rest args)
  `(funcall *date-time-encoding-fn* ,@args))

(defmacro convert-from-universal-time (&rest args)
  `(funcall *date-time-decoding-fn* ,@args))

(defmacro make-time-range (&key min max)
  `(make-numeric-range :min (min ,min ,max) :max (max ,min ,max)))

(defrange date-time -big big)

(defrange xmlxsd::time -big big)

(defrange date -big big)

(defrange g-year-month -big big)

(defrange g-year -big big)

(defrange g-month-day -big big)

(defrange g-day -big big)

(defrange g-month -big big)

(defmethod parse-as-type ((object string) (datatype (eql 'date-time)) start end)
  (multiple-value-bind (zone sec min hour day month year)
      (parse-date-time object start end t t t t t t t)
    (convert-to-universal-time sec min hour day month year zone)))

(defmethod parse-as-type ((object string) (datatype (eql 'xmlxsd::time)) start end)
  (multiple-value-bind (zone sec min hour day month year)
      (parse-date-time object start end nil nil nil t t t t)
    (declare (ignore day month year))
    (convert-to-universal-time sec min hour 1 1 1900 zone)))

(defmethod parse-as-type ((object string) (datatype (eql 'date)) start end)
  (multiple-value-bind (zone sec min hour day month year)
      (parse-date-time object start end t t t nil nil nil t)
    (declare (ignore sec min hour))
    (make-time-range :min (convert-to-universal-time 0 0 0 day month year zone)
                     :max (convert-to-universal-time 59 59 23 day month year zone))))

(defmethod parse-as-type ((object string) (datatype (eql 'g-year-month)) start end)
  (multiple-value-bind (zone sec min hour day month year)
      (parse-date-time object start end t t nil nil nil nil t)
    (declare (ignore sec min hour day))
    (make-time-range :min (convert-to-universal-time 0 0 0 1 month year zone)
                     :max (convert-to-universal-time 59
                                                     59
                                                     23
                                                     (last-day month year)
                                                     month
                                                     year
                                                     zone))))

(defmethod parse-as-type ((object string) (datatype (eql 'g-year)) start end)
  (multiple-value-bind (zone sec min hour day month year)
      (parse-date-time object start end t nil nil nil nil nil t)
    (declare (ignore sec min hour day month))
    (make-time-range :min (convert-to-universal-time 0 0 0 1 1 year zone)
                     :max (convert-to-universal-time 59 59 23 31 12 year zone))))

(defmethod parse-as-type ((object string) (datatype (eql 'g-month-day)) start end)
  (multiple-value-bind (zone sec min hour day month year)
      (parse-date-time object start end nil t t nil nil nil t)
    (declare (ignore sec min hour year))
    (make-time-range :min (convert-to-universal-time 0 0 0 day month 1900 zone)
                     :max (convert-to-universal-time 59 59 23 day month 1900 zone))))

(defmethod parse-as-type ((object string) (datatype (eql 'g-day)) start end)
  (multiple-value-bind (zone sec min hour day month year)
      (parse-date-time object start end nil nil t nil nil nil t)
    (declare (ignore sec min hour month year))
    (make-time-range :min (convert-to-universal-time 0 0 0 day 1 1900 zone)
                     :max (convert-to-universal-time 59 59 23 day 1 1900 zone))))

(defmethod parse-as-type ((object string) (datatype (eql 'g-month)) start end)
  (multiple-value-bind (zone sec min hour day month year)
      (parse-date-time object start end nil t nil nil nil nil t)
    (declare (ignore sec min hour day year))
    (make-time-range :min (convert-to-universal-time 0 0 0 1 month 1900 zone)
                     :max (convert-to-universal-time 59
                                                     59
                                                     23
                                                     (last-day month)
                                                     month
                                                     1900
                                                     zone))))

(defmethod range-to-content (value slot-type (datatype (eql 'date)))
  (declare (ignore slot-type))
  value)

(defmethod range-to-content (value slot-type (datatype (eql 'g-year-month)))
  (declare (ignore slot-type))
  value)

(defmethod range-to-content (value slot-type (datatype (eql 'g-year)))
  (declare (ignore slot-type))
  value)

(defmethod range-to-content (value slot-type (datatype (eql 'g-month-day)))
  (declare (ignore slot-type))
  value)

(defmethod range-to-content (value slot-type (datatype (eql 'g-day)))
  (declare (ignore slot-type))
  value)

(defmethod range-to-content (value slot-type (datatype (eql 'g-month)))
  (declare (ignore slot-type))
  value)

(defun print-date-time (object has-time has-day has-month has-year)
  (let (zone sec min hour day month year)
    (multiple-value-setq (sec min hour day month year)
      (convert-from-universal-time object))
    (unless has-time
      (unless (zerop hour)

        ;; Recoverable timezone.
        (setq zone (multiple-value-bind (quot rem)
                       (round hour 24)
                     (declare (ignore quot))
                     rem))
        (when (minusp zone)
          (multiple-value-setq (sec min hour day month year)
            (convert-from-universal-time object zone)))))
    (format t "~:[~;-~]~@[~4,'0D~]~:[~;-~]~@[~2,'0D~]~:[~;-~]~@[~2,'0D~]~
               ~:[~2*~;~:[-~;+~]~2,'0D:00~]~:[~;T~]~:[~;~2,'0D:~2,'0D:~2,'0DZ~]"
              (or (minusp year) (and (not has-year) (or has-month has-day)))
              (and has-year year)
              (or has-month has-day)
              (and has-month month)
              has-day
              (and has-day day)
              zone
              (and zone (minusp zone))
              (and zone (abs zone))
              (and has-day has-time)
              has-time
              hour
              min
              sec)))

(defmethod print-as-type ((object number) (datatype (eql 'date-time)))
  (print-date-time object t t t t))

(defmethod print-as-type ((object number) (datatype (eql 'xmlxsd::time)))
  (print-date-time object t nil nil nil))

(defmethod print-as-type ((object number) (datatype (eql 'date)))
  (print-date-time object nil t t t))

(defmethod print-as-type ((object number) (datatype (eql 'g-year-month)))
  (print-date-time object nil nil t t))

(defmethod print-as-type ((object number) (datatype (eql 'g-year)))
  (print-date-time object nil nil nil t))

(defmethod print-as-type ((object number) (datatype (eql 'g-month-day)))
  (print-date-time object nil t t nil))

(defmethod print-as-type ((object number) (datatype (eql 'g-day)))
  (print-date-time object nil t nil nil))

(defmethod print-as-type ((object number) (datatype (eql 'g-month)))
  (print-date-time object nil nil t nil))

(defmethod print-as-type ((object cons) (datatype (eql 'date)))
  (print-as-type (range-min object) datatype))

(defmethod print-as-type ((object cons) (datatype (eql 'g-year-month)))
  (print-as-type (range-min object) datatype))

(defmethod print-as-type ((object cons) (datatype (eql 'g-year)))
  (print-as-type (range-min object) datatype))

(defmethod print-as-type ((object cons) (datatype (eql 'g-month-day)))
  (print-as-type (range-min object) datatype))

(defmethod print-as-type ((object cons) (datatype (eql 'g-day)))
  (print-as-type (range-min object) datatype))

(defmethod print-as-type ((object cons) (datatype (eql 'g-month)))
  (print-as-type (range-min object) datatype))

;;; Duration

(defconstant xml-duration-year-indicator #\Y)

(defconstant xml-duration-month-indicator #\M)

(defconstant xml-duration-day-indicator #\D)

(defconstant xml-duration-hour-indicator #\H)

(defconstant xml-duration-min-indicator #\M)

(defconstant xml-duration-sec-indicator #\S)

(let ((min-month-days #(0 28 59 89 120 150 181 212 242 273 303 334))
      (max-month-days #(0 31 62 92 123 153 184 215 245 276 306 337)))

  (defun month-days-table (maximizing)
    (if maximizing max-month-days min-month-days))

  ) ;end let min-month-days

(defmacro months-to-days (months maximizing)
  `(aref (month-days-table ,maximizing) ,months))

(defmacro days-to-months (days maximizing)
  `(position ,days (month-days-table ,maximizing) :test #'>= :from-end (not nil)))

(defun convert-to-seconds (maximizing neg secs mins hours days months years)
  (flet ((leap-years-in (years maximizing)
           (let (leap-years years-over leap-centuries centuries-over)
             (multiple-value-setq (leap-years years-over)
               (truncate years 4))
             (multiple-value-setq (leap-centuries centuries-over)
               (truncate years 400))
             (decf leap-years (- (truncate years 100) leap-centuries))
             (when maximizing
               (when (plusp years-over)
                 (incf leap-years))
               (when (plusp centuries-over)
                 (incf leap-years)))
             leap-years)))
    (multiple-value-bind (year-months months-over)
        (truncate months 12)
      (* (if neg -1 1)
         (+ secs
            (* mins 60)
            (* hours 60 60)
            (* (+ days
                  (months-to-days months-over maximizing)
                  (leap-years-in (+ years year-months) maximizing))
               24 60 60)
            (* years 365 24 60 60))))))

(defrange duration -big big)

(defmethod parse-as-type ((object string) (datatype (eql 'duration)) start end)
  (let (integers
        (neg (negativep object)))
    (setq integers
      (parse-integers object
                      (if neg (1+ start) start)
                      end
                      #'(lambda (ch i) (declare (ignore i)) (alpha-char-p ch))
                      (find xml-duration-year-indicator object)
                      (find xml-duration-month-indicator object
                            :end (or (position xml-date-time-separator object) end))
                      (find xml-duration-day-indicator object)
                      (find xml-duration-hour-indicator object)
                      (find xml-duration-min-indicator object
                            :start (or (position xml-date-time-separator object) end))
                      (find xml-duration-sec-indicator object)))
    (when (find field-missing-indicator integers)
      (error "Malformed duration encountered: ~A." object))
    (make-time-range :min (apply #'convert-to-seconds nil neg integers)
                     :max (apply #'convert-to-seconds 'maximizing neg integers))))

(defmethod range-to-content (value slot-type (datatype (eql 'duration)))
  (declare (ignore slot-type))
  value)

(defun decompose-duration (duration maximizing)
  (flet ((years-in (days maximizing)
           (do ((periods '(400 100 4 1) (rest periods))
                (extra-days '(97 24 1 0) (rest extra-days))
                (days-over days)
                (years 0 (+ years (* n (first periods))))
                n)
               ((endp periods) (values years days-over))
             (multiple-value-setq (n days-over)
               (truncate days-over (+ (* (first periods) 365) (first extra-days))))
             (when maximizing
               (when (case (first periods)
                       (100 (plusp n))
                       (4 (> days-over 365)))
                 (decf days-over))))))
    (let (secs mins hours days months years)
      (multiple-value-setq (mins secs)
        (truncate duration 60))
      (multiple-value-setq (hours mins)
        (truncate mins 60))
      (multiple-value-setq (days hours)
        (truncate hours 24))
      (multiple-value-setq (years days)
        (years-in days maximizing))
      (setq months (days-to-months days maximizing)
            days (- days (months-to-days months maximizing)))
      (values secs mins hours days months years))))

(defmethod print-as-type ((object cons) (datatype (eql 'duration)))
  (let (secs has-secs mins hours days months has-months years)
    (multiple-value-setq (secs mins hours days months years)
      (decompose-duration (min (abs (range-min object)) (abs (range-max object))) nil))
    (setq has-months (and (or (plusp years) (/= (range-min object) (range-max object)))
                          (plusp months))
          has-secs (or (zerop (range-min object)) (plusp secs)))
    (unless has-months
      (setq days (+ days (months-to-days months nil))))
    (format t "~:[~;-~]P~@[~DY~]~@[~DM~]~@[~DD~]~:[~;T~]~@[~DH~]~@[~DM~]~@[~DS~]"
              (minusp (range-min object))
              (and (plusp years) years)
              (and has-months months)
              (and (plusp days) days)
              (or (plusp hours) (plusp mins) has-secs)
              (and (plusp hours) hours)
              (and (plusp mins) mins)
              (and has-secs secs))))