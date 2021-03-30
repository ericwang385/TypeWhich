#lang racket/base
;;; Here we actively choose to not use racket racket/fixnum. Use of
;;; generic numeric ops is disadvantage for racket but there is no
;;; safe version of fixnum operations that avoids the overhead of
;;; contracts, and we are only interested in comparing safe code.  The
;;; racket/fixnum safe operations are generally no faster than using
;;; generic primitives like +. (According to the documentation)

(require "kernel.rkt")

(define (create l1 l2)
  (let ([x (make-vector (* l1 l2) 0)])
    (let loop1 ([i 0])
      (if (< i l1)
	  (let loop2 ([j 0])
	    (begin
	      (if (< j l2)
		  (begin
		    (vector-set! x (+ (* l2 i) j) (+ j i))
		    (loop2 (+ 1 j)))
		  (loop1 (+ 1 i)))))
	  x))))

(define (main)
  (let ([size (read)])
    (let ([ar size]
          [ac size]
          [br size]
          [bc size])
      (let ([a (create ar ac)]
            [b (create br bc)])
        (printf "~a\n" (number->string (vector-ref (mult a ar ac b br bc) (- (* ar bc) 1))))))))

(time (main))
