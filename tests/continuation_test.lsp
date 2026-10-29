;;; -*- mode: Scheme -*-

;;; Copyright 2015 SteelSeries ApS. All rights reserved.
;;; Use of this source code is governed by a BSD-style
;;; license that can be found in the LICENSE file.

(context "first class continuations" ()

  (it "is bound under both names"
    (assert-true (eq? call/cc call-with-current-continuation))
    (assert-true (function? call/cc)))

  (it "returns normally when the procedure returns"
    (assert-eq (call/cc (lambda (k) 7)) 7)
    (assert-eq (call-with-current-continuation (lambda (k) (+ 1 2))) 3))

  (it "jumps with the procedure's argument"
    (assert-eq (call/cc (lambda (k) (k 42) 99)) 42)
    (assert-eq (call/cc (lambda (k) (+ 1 (k 10)) 99)) 10))

  (it "accepts false and the empty list"
    (assert-false (call/cc (lambda (k) (k #f) 1)))
    (assert-nil (call/cc (lambda (k) (k '()))))
    (assert-true (call/cc (lambda (k) (k #t)))))

  (it "escapes from nested calls and argument positions"
    (assert-eq (+ 1 (* 2 (call/cc (lambda (k) (k 10))))) 21)
    (assert-eq ((call/cc (lambda (k) (k car))) '(a b c)) 'a)
    (assert-eq (apply + (list 2 3 (call/cc (lambda (k) (k 4))))) 9))

  (it "abandons expressions following the jump in the receiver"
    (assert-eq (call/cc (lambda (k) (k 'out) 'never)) 'out))

  (it "is usable in every special form evaluation position"
    (assert-eq (if (call/cc (lambda (k) (k #t))) 'yes 'no) 'yes)
    (assert-eq (unless (call/cc (lambda (k) (k #t))) 1) ())
    (assert-eq (begin 0 (call/cc (lambda (k) (k 9))) 10) 10)
    (assert-eq (let ((x (call/cc (lambda (k) (k 3))))) x) 3)
    (assert-eq (let* ((a 1) (b (call/cc (lambda (k) (k 2))))) (+ a b)) 3)
    (assert-eq (call/cc (lambda (k) (and #t (k 's) #f))) 's)
    (assert-eq (call/cc (lambda (k) (or #f (k 'o) #t))) 'o)
    (assert-eq (case (call/cc (lambda (k) (k 'b))) ((a) 1) ((b) 2) (else 3)) 2)
    (assert-eq (cond (#f 1) ((call/cc (lambda (k) (k #t))) 8) (else 3)) 8)
    (assert-eq (begin (define sv2 0) (set! sv2 (call/cc (lambda (k) (k 77)))) sv2) 77))

  (it "breaks out of do and named let"
    (assert-eq (call/cc (lambda (exit)
                  (do ((i 0 (+ i 1)))
                      ((== i 5) 'done)
                    (when (== i 3) (exit 'stopped)))))
               'stopped)
    (assert-eq (call/cc (lambda (exit)
                  (let loop ((i 0))
                    (when (== i 3) (exit 'out))
                    (loop (+ i 1)))))
               'out))

  (it "works through apply"
    (assert-eq (apply call/cc (list (lambda (k) (k 5)))) 5))

  (it "escapes from map and for-each callbacks"
    (assert-eq (map (lambda (x)
                      (call/cc (lambda (c) x)))
                    '(1 2 3))
               '(1 2 3))
    (assert-nil (for-each (lambda (x)
                            (call/cc (lambda (c) x)))
                          '(1 2 3))))

  (it "is a first class value that can be stored and passed"
    (assert-eq ((lambda (f) (f 11))
                (call/cc (lambda (k) (k (lambda (x) (* x 2))))))
               22))

  (it "reports ordinary errors for bad use"
    (assert-error (call/cc))
    (assert-error (call/cc 5))
    (assert-error (call/cc (lambda (k) k) 1))
    (assert-error (1 2)))
)
