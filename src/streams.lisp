;;; Copyright (C) 2007, 2011, 2014, 2017 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; Adapted from: Structure and Interpretation of Computer Programs
;;; by Harold Abelson and Gerald Jay Sussman with Julie Sussman,
;;; MIT Press, 1985.

(defpackage :streams (:use :cl)
  (:import-from :rparallel #:delay #:force))
(in-package streams)
(eval-when (:execute :compile-toplevel :load-toplevel)
  (export
   '(accumulate-delayed cons-stream delay empty-stream-p
     flatmap flatmap* flatten force head interleave interleave-delayed
     map-stream map-stream* memo-proc singleton tail the-empty-stream
     )))

(defconstant the-empty-stream nil)

(defun empty-stream-p (stream)
  (null stream))

(defun head (stream)
  "Obtain first element in stream."
  (car stream))

(defun tail (stream)
  "Obtain the tail of stream by evaluating delayed expression."
  (force (cdr stream)))

(defmacro cons-stream (a b)
  "Returns a pair comprising A and a delayed object."
  `(cons ,a (delay ,b)))

(defun singleton (s)
  "Generates a single-element stream."
;;;   (cons-stream s the-empty-stream)
  (cons s the-empty-stream)                    ; Handled by generic FORCE.
  )

(defun map-stream (proc stream)
  "Generates the stream formed by applying procedure to each element in input stream."
  (if (empty-stream-p stream)
      the-empty-stream
    (cons-stream (funcall proc (head stream))
                 (map-stream proc (tail stream)))))

(defun flatmap (proc stream)
  "Generate the single stream formed by applying the procedure (which returns a stream) to each item in the input stream and appending the results."
  (flatten (map-stream proc stream)))

(defun map-stream* (proc stream tail-fn)
  "Generates the stream formed by applying procedure to each element in input stream."
  (if (empty-stream-p stream)
      the-empty-stream
    (cons-stream (funcall proc (head stream))
                 (map-stream* proc (funcall tail-fn stream) tail-fn))))

(defun flatmap* (proc stream tail-fn)
  "Generate the single stream formed by applying the procedure (which returns a stream) to each item in the input stream and appending the results."
  (flatten (map-stream* proc stream tail-fn)))

(defun flatten (stream)
  "Appends the elements of a stream of streams to form a single stream."
  (accumulate-delayed #'interleave-delayed the-empty-stream stream))

(defun accumulate-delayed (combiner initial-value stream)
  "Accumulates items in stream using combiner, beginning with initial-value.  Combiner must expect to explicitly force its second argument."
  (if (empty-stream-p stream)
      initial-value
    (funcall combiner (head stream)

                      ;; To handle infinite streams, delay the recursive call.
                      (delay (accumulate-delayed combiner initial-value
                                                          (tail stream))))))

(defun interleave (s1 s2)
  "Append two streams, taking elements alternately from each -- appropriate for infinite streams."
  (if (empty-stream-p s1)
      s2
    (cons-stream (head s1)
                 (interleave s2 (tail s1)))))

(defun interleave-delayed (stream delayed-stream)
  "Append two streams, taking elements alternately from each."
  (if (empty-stream-p stream)
      (force delayed-stream)
    (cons-stream (head stream)
                 (interleave-delayed (force delayed-stream)
                                     (delay (tail stream))))))