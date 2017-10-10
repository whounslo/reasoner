;;; Copyright (C) 2014, 2016-17 by William Hounslow
;;; This is free software, covered by the GNU GPL (v2)
;;; See http://www.gnu.org/copyleft/gpl.html
;;;
;;; Requires Lisp in Parallel (lparallel.org).

(defpackage :pstreams (:use :cl :lparallel)
  (:import-from :streams
                #:the-empty-stream #:empty-stream-p #:head #:singleton #:flatmap*)
  (:export #:the-empty-stream #:empty-stream-p #:head #:singleton
           #:pcons-stream #:gtail #:gflatmap #:pmap-stream #:pflatmap
           #:pmap-stream* #:pflatmap*))
(in-package :pstreams)

(defun tail (stream)
  "Obtain the tail of stream by fulfilling promise."
  (force (cdr stream)))

(defgeneric gforce (object)
  (:method ((delayed-object function))
    "Evaluate delayed-object produced by (non-lparallel) DELAY."
    (funcall delayed-object))
  (:method ((object t))
    "Promise, or anything else."
    (force object)))

(defun gtail (stream)
  "Obtain the tail of stream."
  (gforce (cdr stream)))

(defmacro gflatmap (proc stream)
  `(flatmap* ,proc ,stream #'gtail))

(defmacro cons-stream (a b)
  "Returns a pair comprising A and a delayed object."
  `(cons ,a (delay ,b)))

(defmacro pcons-stream (a b)
  "Returns a pair comprising A and B, evaluated concurrently."
  `(let ((f (future ,b)))
     (cons ,a f)))

(defun pmap-stream-deferred (proc stream)
  "Delay after eagerly obtaining the next element in input stream."
  (chain (delay (pmap-stream proc stream))))

(defun pmap-stream (proc stream)
  "Generates the stream formed by applying procedure to each element in input stream."
  (if (empty-stream-p stream)
      the-empty-stream
    (pcons-stream (funcall proc (head stream))
                  (pmap-stream-deferred proc (tail stream)))))

(defun pflatmap (proc stream)
  "Generate the single stream formed by applying the procedure (which returns a stream) to each item in the input stream and appending the results."
  (flatten (pmap-stream proc stream)))

(defun pmap-stream-deferred* (proc stream tail-fn)
  "Delay after eagerly obtaining the next element in input stream."
  (chain (delay (pmap-stream* proc stream tail-fn))))

(defun pmap-stream* (proc stream tail-fn)
  "Generates the stream formed by applying procedure to each element in input stream."
  (if (empty-stream-p stream)
      the-empty-stream
    (pcons-stream (funcall proc (head stream))
                  (pmap-stream-deferred* proc (funcall tail-fn stream) tail-fn))))

(defun pflatmap* (proc stream tail-fn)
  "Generate the single stream formed by applying the procedure (which returns a stream) to each item in the input stream and appending the results."
  (flatten (pmap-stream* proc stream tail-fn)))

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

(defun interleave-delayed (stream delayed-stream)
  "Append two streams, taking elements alternately from each."
  (if (empty-stream-p stream)
      (force delayed-stream)
    (cons-stream (head stream)
                 (interleave-delayed (force delayed-stream)
                                     (delay (gtail stream))))))