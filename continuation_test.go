// Copyright 2014 SteelSeries ApS.  All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// This file tests first-class, multiply invocable escape continuations.

package golisp

import (
	. "gopkg.in/check.v1"
)

type ContinuationSuite struct {
	env *SymbolTableFrame
}

var _ = Suite(&ContinuationSuite{})

var ccTapLog []int64

func ccTapImpl(args *Data, env *SymbolTableFrame) (*Data, error) {
	ccTapLog = append(ccTapLog, IntegerValue(Car(args)))
	return Car(args), nil
}

func (s *ContinuationSuite) SetUpSuite(c *C) {
	InitLisp()
	MakePrimitiveFunction("cc-tap", "1", ccTapImpl)
}

func (s *ContinuationSuite) SetUpTest(c *C) {
	s.env = NewSymbolTableFrameBelow(Global, "continuation-suite")
	ccTapLog = make([]int64, 0)
}

// ev evaluates one source string in the suite environment, as a separate
// host evaluation (public ParseAndEvalInEnvironment).
func (s *ContinuationSuite) ev(c *C, src string) *Data {
	d, err := ParseAndEvalInEnvironment(src, s.env)
	c.Assert(err, IsNil, Commentf("source: %s", src))
	return d
}

func (s *ContinuationSuite) evErr(c *C, src string) error {
	_, err := ParseAndEvalInEnvironment(src, s.env)
	c.Assert(err, NotNil, Commentf("expected an error from: %s", src))
	return err
}

func (s *ContinuationSuite) TestBasicEscapeAndReturn(c *C) {
	c.Assert(IntegerValue(s.ev(c, `(call/cc (lambda (k) (k 42) 99))`)), Equals, int64(42))
	c.Assert(IntegerValue(s.ev(c, `(call-with-current-continuation (lambda (k) 7))`)), Equals, int64(7))
	c.Assert(IntegerValue(s.ev(c, `(call/cc (lambda (k) (+ 1 (k 10)) 20))`)), Equals, int64(10))
	// #f and the empty list are ordinary continuation values.
	v := s.ev(c, `(call/cc (lambda (k) (k #f) 1))`)
	c.Assert(BooleanP(v), Equals, true)
	c.Assert(BooleanValue(v), Equals, false)
	c.Assert(NilP(s.ev(c, `(call/cc (lambda (k) (k '())))`)), Equals, true)
	// the procedure's normal return is the call/cc value
	c.Assert(IntegerValue(s.ev(c, `(call/cc (lambda (k) (if #t 13 14)))`)), Equals, int64(13))
}

func (s *ContinuationSuite) TestSynonymsAreTheSameProcedure(c *C) {
	c.Assert(BooleanValue(s.ev(c, `(eq? call/cc call-with-current-continuation)`)), Equals, true)
	c.Assert(BooleanValue(s.ev(c, `(function? call/cc)`)), Equals, true)
}

func (s *ContinuationSuite) TestEscapeFromEveryArgumentPosition(c *C) {
	c.Assert(IntegerValue(s.ev(c, `(+ 1 (* 2 (call/cc (lambda (k) (k 10)))))`)), Equals, int64(21))
	c.Assert(IntegerValue(s.ev(c, `((call/cc (lambda (k) (k car))) '(1 2 3))`)), Equals, int64(1))
	c.Assert(IntegerValue(s.ev(c, `(apply + (list 2 3 (call/cc (lambda (k) (k 4)))))`)), Equals, int64(9))
	c.Assert(IntegerValue(s.ev(c,
		`(let ((f (lambda (x) (* x 3)))) (f (call/cc (lambda (k) (k 5)))))`)), Equals, int64(15))
}

func (s *ContinuationSuite) TestCallerComputationIsAbandoned(c *C) {
	// After (k ...) the expressions following it inside the receiver are
	// abandoned; the captured continuation itself naturally reruns its
	// suffix against fresh state.
	s.ev(c, `(define cc-counter 0)`)
	v := s.ev(c, `(call/cc (lambda (k) (set! cc-counter 1) (k 'out) (set! cc-counter 99)))`)
	c.Assert(StringValue(v), Equals, "out")
	c.Assert(IntegerValue(s.ev(c, `cc-counter`)), Equals, int64(1))
	// Host primitives after the jump inside the receiver never run.
	v = s.ev(c, `(+ (call/cc (lambda (k) (k 3) (cc-tap 100))) 10)`)
	c.Assert(IntegerValue(v), Equals, int64(13))
	c.Assert(len(ccTapLog), Equals, 0)
}

func (s *ContinuationSuite) TestCrossHostReinvocation(c *C) {
	s.ev(c, `(define resume #f)`)
	s.ev(c, `(define n 0)`)
	v := s.ev(c, `(define out (call/cc (lambda (k) (set! resume k) (set! n (+ n 1)) 'first)))`)
	c.Assert(StringValue(v), Equals, "first")
	c.Assert(IntegerValue(s.ev(c, `n`)), Equals, int64(1))
	// The original top level computation is completed again, for the new
	// host call, each time the saved continuation is invoked.
	c.Assert(StringValue(s.ev(c, `(resume 'second)`)), Equals, "second")
	c.Assert(StringValue(s.ev(c, `(resume 'third)`)), Equals, "third")
	// Side effects completed before the capture are not replayed.
	c.Assert(IntegerValue(s.ev(c, `n`)), Equals, int64(1))
	// out is redefined each time because the suffix re-runs against the
	// shared environment.
	c.Assert(StringValue(s.ev(c, `out`)), Equals, "third")
}

func (s *ContinuationSuite) TestPrefixIsKeptSuffixRerunsWithSharedState(c *C) {
	s.ev(c, `(define kk #f)`)
	v := s.ev(c, `(define r (list (cc-tap 1) (call/cc (lambda (c) (set! kk c) 'b))))`)
	c.Assert(String(v), Equals, "(1 b)")
	c.Assert(len(ccTapLog), Equals, 1)
	// Re-entry reuses the already evaluated prefix (cc-tap not replayed)
	// and re-runs the suffix, which reads current shared state.
	c.Assert(String(s.ev(c, `(kk 'z)`)), Equals, "(1 z)")
	c.Assert(String(s.ev(c, `(kk 'q)`)), Equals, "(1 q)")
	c.Assert(ccTapLog, DeepEquals, []int64{1})

	// Shared mutable state is read fresh by the rerun suffix.
	s.ev(c, `(define box (cons 1 '()))`)
	s.ev(c, `(define k4 #f)`)
	c.Assert(String(s.ev(c,
		`(define res (let ((x (call/cc (lambda (c) (set! k4 c) 'a)))) (cons x (car box))))`)),
		Equals, "(a . 1)")
	s.ev(c, `(set-car! box 2)`)
	c.Assert(String(s.ev(c, `(k4 'b)`)), Equals, "(b . 2)")
}

func (s *ContinuationSuite) TestContinuationIsFirstClassValue(c *C) {
	s.ev(c, `(define saved #f)`)
	s.ev(c, `(call/cc (lambda (k) (set! saved k)))`)
	// stored in a list and selected through ordinary procedures
	v := s.ev(c, `(let ((ks (list saved saved))) ((car ks) 31))`)
	c.Assert(IntegerValue(v), Equals, int64(31))
	// closed over by a user procedure and passed through apply
	s.ev(c, `(define (invoke-later c v) (apply c (list v)))`)
	c.Assert(IntegerValue(s.ev(c, `(invoke-later saved 32)`)), Equals, int64(32))
	// multiple distinct invocations keep producing independent results
	c.Assert(IntegerValue(s.ev(c, `(invoke-later saved 33)`)), Equals, int64(33))
}

func (s *ContinuationSuite) TestNestedCapturesAndSwitching(c *C) {
	s.ev(c, `(define ko #f)`)
	s.ev(c, `(define ki #f)`)
	v := s.ev(c,
		`(define nr (call/cc (lambda (c1)
                            (set! ko c1)
                            (list 'outer (call/cc (lambda (c2) (set! ki c2) 'inner))))))`)
	c.Assert(String(v), Equals, "(outer inner)")
	c.Assert(String(s.ev(c, `(ki 'x)`)), Equals, "(outer x)")
	// jumping to the outer capture discards everything pending
	c.Assert(String(s.ev(c, `(ko 'y)`)), Equals, "y")
	// the inner saved continuation is still independently usable and still
	// completes the original outer computation
	c.Assert(String(s.ev(c, `(ki 'z)`)), Equals, "(outer z)")
}

func (s *ContinuationSuite) TestMapEscapeKeepsPrefixAndSuffix(c *C) {
	s.ev(c, `(define mk #f)`)
	v := s.ev(c,
		`(define mr (map (lambda (x)
                          (call/cc (lambda (c) (when (== x 2) (set! mk c)) x)))
                        '(1 2 3)))`)
	c.Assert(String(v), Equals, "(1 2 3)")
	// Resume inside the second iteration: prefix (1) kept, suffix (3) reruns.
	c.Assert(String(s.ev(c, `(mk 9)`)), Equals, "(1 9 3)")
	c.Assert(String(s.ev(c, `(mk 10)`)), Equals, "(1 10 3)")
	// the third iteration escape: prefix (1 2) kept
	s.ev(c, `(define mk3 #f)`)
	s.ev(c, `(define (cb3 x)
              (call/cc (lambda (c) (when (== x 3) (set! mk3 c))))
              (cc-tap x))`)
	s.ev(c, `(map cb3 '(1 2 3))`)
	c.Assert(ccTapLog, DeepEquals, []int64{1, 2, 3})
	s.ev(c, `(mk3 'z)`)
	// iterations 1 and 2 prefix is not replayed, iteration 3 suffix reruns
	c.Assert(ccTapLog, DeepEquals, []int64{1, 2, 3, 3})
}

func (s *ContinuationSuite) TestForEachEscape(c *C) {
	s.ev(c, `(define fk #f)`)
	s.ev(c, `(define cc-state 0)`)
	v := s.ev(c,
		`(for-each (lambda (x)
                    (call/cc (lambda (c) (when (== x 2) (set! fk c))))
                    (set! cc-state (+ cc-state x)))
                  '(1 2 3))`)
	// for-each returns nil and the full run accumulated 1+2+3
	c.Assert(NilP(v), Equals, true)
	c.Assert(IntegerValue(s.ev(c, `cc-state`)), Equals, int64(6))
	s.ev(c, `(fk 'ignored)`)
	// rerun from iteration 2: iteration 1 prefix is not replayed, the
	// iteration 3 suffix is executed again
	c.Assert(IntegerValue(s.ev(c, `cc-state`)), Equals, int64(11)) // 6 + 2 + 3
}

func (s *ContinuationSuite) TestSpecialFormEvaluationPositions(c *C) {
	var v *Data
	// if / when / unless
	c.Assert(String(s.ev(c, `(if (call/cc (lambda (k) (k #t))) 'yes 'no)`)), Equals, "yes")
	c.Assert(IntegerValue(s.ev(c,
		`(when (call/cc (lambda (k) (k #t))) 1 2)`)), Equals, int64(2))
	c.Assert(NilP(s.ev(c, `(unless (call/cc (lambda (k) (k #t))) 1)`)), Equals, true)

	// cond / case: jumping from a clause test escapes the whole cond
	c.Assert(String(s.ev(c,
		`(if (call/cc (lambda (k) (cond (#f 1) ((k 'escape) 2) (else 3)))) 'yes 'no)`)), Equals, "yes")
	c.Assert(IntegerValue(s.ev(c,
		`(case (call/cc (lambda (k) (k 'b))) ((a) 1) ((b) 2) (else 3))`)), Equals, int64(2))

	// and / or short circuit semantics preserved: to abandon the whole
	// form, the jump goes through a continuation captured outside it.
	c.Assert(String(s.ev(c,
		`(call/cc (lambda (k) (and #t (k 'short) (cc-tap 1))))`)), Equals, "short")
	c.Assert(len(ccTapLog), Equals, 0)
	c.Assert(String(s.ev(c,
		`(call/cc (lambda (k) (or #f (k 'short2) (cc-tap 1))))`)), Equals, "short2")
	c.Assert(len(ccTapLog), Equals, 0)

	// begin / set! / define value positions
	c.Assert(IntegerValue(s.ev(c,
		`(begin 0 (call/cc (lambda (k) (k 41))) 42)`)), Equals, int64(42))
	s.ev(c, `(define sv 0)`)
	c.Assert(IntegerValue(s.ev(c,
		`(set! sv (call/cc (lambda (k) (k 77))))`)), Equals, int64(77))
	s.ev(c, `(set! sv 0)`)
	c.Assert(IntegerValue(s.ev(c,
		`(define dv (call/cc (lambda (k) (k 88))))`)), Equals, int64(88))

	// let / let* / letrec value positions
	c.Assert(IntegerValue(s.ev(c,
		`(let ((a (call/cc (lambda (k) (k 1)))) (b 2)) (+ a b))`)), Equals, int64(3))
	c.Assert(IntegerValue(s.ev(c,
		`(let* ((a 1) (b (call/cc (lambda (k) (k 2))))) (+ a b))`)), Equals, int64(3))
	c.Assert(IntegerValue(s.ev(c,
		`(letrec ((p (lambda (n) (if (== n 0) #t (g (- n 1)))))
                 (g (lambda (n) (call/cc (lambda (k) (k #f))))))
           (if (p 3) 1 2))`)), Equals, int64(2))

	// named let: break out of the loop
	v = s.ev(c,
		`(call/cc (lambda (exit)
                   (let loop ((i 0))
                     (when (== i 3) (exit 'out))
                     (loop (+ i 1)))))`)
	c.Assert(StringValue(v), Equals, "out")

	// do: break out mid loop
	s.ev(c, `(define dk #f)`)
	v = s.ev(c,
		`(call/cc (lambda (exit)
                   (set! dk exit)
                   (do ((i 0 (+ i 1)))
                       ((== i 5) 'done)
                     (when (== i 3) (exit 'stopped))))))`)
	c.Assert(StringValue(v), Equals, "stopped")
	c.Assert(StringValue(s.ev(c, `(dk 'again)`)), Equals, "again")

	// apply with call/cc and with a saved continuation
	c.Assert(IntegerValue(s.ev(c,
		`(apply call/cc (list (lambda (k) (k 7))))`)), Equals, int64(7))
	s.ev(c, `(define ak (call/cc (lambda (c) c)))`)
	c.Assert(IntegerValue(s.ev(c, `(apply ak '(8))`)), Equals, int64(8))
}

func (s *ContinuationSuite) TestLetrecEscape(c *C) {
	v := s.ev(c,
		`(letrec ((run (lambda (i) (if (> i 3) (done i) (run (+ i 1)))))
                 (done (lambda (n) (call/cc (lambda (k) (* n 100))))))
           (run 0))`)
	c.Assert(IntegerValue(v), Equals, int64(400))
}

func (s *ContinuationSuite) TestContinuationCanReturnProcedure(c *C) {
	// call/cc resumes with a procedure which is then applied
	c.Assert(IntegerValue(s.ev(c,
		`((lambda (f) (f 11))
          (call/cc (lambda (k) (k (lambda (x) (* x 2))))))`)), Equals, int64(22))
}

func (s *ContinuationSuite) TestArityAndTypeErrors(c *C) {
	s.evErr(c, `(call/cc)`)
	s.evErr(c, `(call/cc (lambda (k) k) 1)`)
	s.evErr(c, `(call/cc 5)`)
	s.evErr(c, `(call/cc 'not-a-procedure)`)
	s.evErr(c, `(1 2)`)
	s.ev(c, `(define kk2 #f)`)
	c.Assert(StringValue(s.ev(c,
		`(call/cc (lambda (k) (set! kk2 k) 'ready))`)), Equals, "ready")
	s.evErr(c, `(kk2)`)
	s.evErr(c, `(kk2 1 2)`)
	// failed invocations do not consume the continuation
	c.Assert(IntegerValue(s.ev(c, `(kk2 9)`)), Equals, int64(9))
	c.Assert(IntegerValue(s.ev(c, `(kk2 10)`)), Equals, int64(10))
}

func (s *ContinuationSuite) TestErrorsDoNotCrossContaminate(c *C) {
	s.ev(c, `(define good-k #f)`)
	s.ev(c, `(call/cc (lambda (k) (set! good-k k) 'ready))`)
	// an unrelated error in a later evaluation
	s.evErr(c, `(+ 1 'not-a-number-ish)`)
	// the saved continuation still works
	c.Assert(IntegerValue(s.ev(c, `(good-k 123)`)), Equals, int64(123))
	// a failing invocation does not consume the continuation
	s.evErr(c, `(good-k)`)
	s.evErr(c, `(good-k 1 2)`)
	c.Assert(IntegerValue(s.ev(c, `(good-k 124)`)), Equals, int64(124))
}

func (s *ContinuationSuite) TestIndependentEnvironmentsDoNotBleed(c *C) {
	envA := NewSymbolTableFrameBelow(Global, "cc-env-a")
	envB := NewSymbolTableFrameBelow(Global, "cc-env-b")

	// rc is shared through the global environment but the captured
	// computation closes over a binding local to envA.
	_, err := ParseAndEvalInEnvironment(`(define rc #f)`, Global)
	c.Assert(err, IsNil)
	v, err := ParseAndEvalInEnvironment(
		`(define rv ((lambda (local)
                       (let ((x (call/cc (lambda (c) (set! rc c) 'init))))
                         (cons local x))) 'secret))`, envA)
	c.Assert(err, IsNil)
	c.Assert(String(v), Equals, "(secret . init)")
	// invoke it from a completely different host environment
	d, err := ParseAndEvalInEnvironment(`(rc 9)`, envB)
	c.Assert(err, IsNil)
	c.Assert(String(d), Equals, "(secret . 9)")
	// envB never saw envA's local bindings
	d, err = ParseAndEvalInEnvironment(`rv`, envB)
	c.Assert(err, IsNil)
	c.Assert(NilP(d), Equals, true)
}

func (s *ContinuationSuite) TestNestedReentryDoesNotBleedTemporaries(c *C) {
	// Two continuations invoked interleaved repeatedly keep their own
	// captured prefixes and do not share reentry temporaries.
	s.ev(c, `(define ka #f)`)
	s.ev(c, `(define kb #f)`)
	s.ev(c,
		`(define va (+ 10 (call/cc (lambda (c) (set! ka c) 0))))`)
	s.ev(c,
		`(define vb (+ 20 (call/cc (lambda (c) (set! kb c) 0))))`)
	c.Assert(IntegerValue(s.ev(c, `(ka 1)`)), Equals, int64(11))
	c.Assert(IntegerValue(s.ev(c, `(kb 2)`)), Equals, int64(22))
	c.Assert(IntegerValue(s.ev(c, `(ka 3)`)), Equals, int64(13))
	c.Assert(IntegerValue(s.ev(c, `(kb 4)`)), Equals, int64(24))
}

func (s *ContinuationSuite) TestUnsupportedBoundariesRejected(c *C) {
	// eval runs on the same machine, so capture there is complete.
	c.Assert(IntegerValue(s.ev(c, `(eval '(call/cc (lambda (k) (k 1))))`)), Equals, int64(1))
	// Capturing inside a macro transformer is rejected: defining the
	// macro is fine, expanding it raises an ordinary error.
	s.ev(c, `(defmacro (cc-macro-test) (call/cc (lambda (k) 1)))`)
	s.evErr(c, `(cc-macro-test)`)
	// Capturing inside an unquote runs nested evaluation.
	s.evErr(c, `(quasiquote (1 (unquote (call/cc (lambda (k) (k 2))))))`)

	// Invoking a saved continuation from a nested evaluation is rejected
	// and does not consume the continuation.
	s.ev(c, `(define kk-nested #f)`)
	c.Assert(StringValue(s.ev(c,
		`(call/cc (lambda (k) (set! kk-nested k) 'ready))`)), Equals, "ready")
	s.evErr(c, `(quasiquote (1 (unquote (kk-nested 5))))`)
	c.Assert(IntegerValue(s.ev(c, `(kk-nested 6)`)), Equals, int64(6))
}

func (s *ContinuationSuite) TestExtraSemantics(c *C) {
	// strict left-to-right evaluation order of arguments
	v := s.ev(c, `(list (cc-tap 1) (cc-tap 2) (cc-tap 3))`)
	c.Assert(String(v), Equals, "(1 2 3)")
	c.Assert(ccTapLog, DeepEquals, []int64{1, 2, 3})

	// call/cc result splices as the tail argument of apply, with the
	// already evaluated prefix retained across re-invocations.
	s.ev(c, `(define ak2 #f)`)
	v = s.ev(c, `(define ar (apply + 1 (call/cc (lambda (c) (set! ak2 c) (list 2 3)))))`)
	c.Assert(IntegerValue(v), Equals, int64(6))
	c.Assert(IntegerValue(s.ev(c, `(ak2 (list 4 5))`)), Equals, int64(10))
	c.Assert(IntegerValue(s.ev(c, `(ak2 (list 100))`)), Equals, int64(101))

	// map over multiple collections with a continuation prefix
	v = s.ev(c,
		`(map (lambda (a b) (+ a b)) '(1 2 3) '(10 20 30))`)
	c.Assert(String(v), Equals, "(11 22 33)")

	// continuation can deliver a procedure used by the suffix
	s.ev(c, `(define opk2 #f)`)
	v = s.ev(c, `(let ((p (call/cc (lambda (k) (set! opk2 k) car))))
                    (p '(7 8 9)))`)
	c.Assert(IntegerValue(v), Equals, int64(7))
	c.Assert(String(s.ev(c, `(opk2 cdr)`)), Equals, "(8 9)")
	c.Assert(IntegerValue(s.ev(c, `(opk2 cadr)`)), Equals, int64(8))

	// a continuation closed over by a procedure and invoked once
	s.ev(c, `(define done-flag #f)`)
	c.Assert(String(s.ev(c,
		`(let ((kf #f))
           (define (use v) (kf (cons 'got v)))
           (define r (call/cc (lambda (k) (set! kf k))))
           (when (not done-flag)
             (set! done-flag #t)
             (use 5))
           r)`)), Equals, "(got . 5)")
}

func (s *ContinuationSuite) TestForkedProcessUsesContinuation(c *C) {
	// An independently forked process owns its own evaluator and can use
	// call/cc on its own goroutine.
	v := s.ev(c, `(join (fork (lambda (p) (call/cc (lambda (k) (k 77))))))`)
	c.Assert(IntegerValue(v), Equals, int64(77))
}

func (s *ContinuationSuite) TestGeneratorPatternAcrossHostCalls(c *C) {
	// A generator loop parks inside the FIRST host evaluation by escaping
	// through a captured outer continuation; later host evaluations resume
	// the loop via a second, nested saved continuation.
	s.ev(c, `(define yield-k #f)`)
	s.ev(c, `(define resume-k #f)`)
	v := s.ev(c,
		`(define parked (call/cc (lambda (host-k)
                          (set! yield-k host-k)
                          (let loop ((i 0))
                            (cc-tap i)
                            (let ((v (call/cc (lambda (k)
                                                (set! resume-k k)
                                                (yield-k 'parked)))))
                              (loop v))))))`)
	c.Assert(StringValue(v), Equals, "parked")
	c.Assert(ccTapLog, DeepEquals, []int64{0})
	for i := int64(1); i <= 4; i++ {
		v = s.ev(c, `(resume-k `+itoa(i)+`)`)
		c.Assert(StringValue(v), Equals, "parked")
	}
	c.Assert(ccTapLog, DeepEquals, []int64{0, 1, 2, 3, 4})
}

func itoa(i int64) string {
	if i == 0 {
		return "0"
	}
	var buf [20]byte
	pos := len(buf)
	for i > 0 {
		pos--
		buf[pos] = byte('0' + i%10)
		i /= 10
	}
	return string(buf[pos:])
}
