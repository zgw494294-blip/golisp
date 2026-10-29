// Copyright 2014 SteelSeries ApS.  All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// This package implements a basic LISP interpretor for embedding in a go program for scripting.
//
// This file implements Scheme-style first-class, multiply invocable, escape
// continuations (call/cc / call-with-current-continuation).
//
// The evaluator is a CEK-style machine: the rest of a computation is an
// explicit, heap allocated stack of frame values. call/cc copies that stack
// into an ordinary Lisp value; invoking the continuation replaces the current
// stack with a fresh copy of the saved one, so a control point captured in an
// earlier host Eval call can be re-entered any number of times from later
// host Eval calls sharing the same lexical environment. Only control is
// captured -- environments, closures and mutable lists stay shared.

package golisp

import (
	"errors"
	"fmt"
	"runtime"
	"strings"
	"sync/atomic"
	"time"
	"unsafe"
)

// ---------------------------------------------------------------------------
// Continuation data type
// ---------------------------------------------------------------------------

const continuationUnsupportedMessage = "continuations are only supported inside the ordinary synchronous evaluator: call/cc cannot capture, and a saved continuation cannot be invoked, from a nested Eval entered through macro expansion, eval, a host primitive, a frame method, or a custom special form"

// Continuation is a saved machine stack (a first-class escape procedure).
type Continuation struct {
	id     int64
	frames []vmFrame
}

var continuationIdCounter int64 = 0

// ContinuationWithValue boxes a saved continuation as a Data value.
func ContinuationWithValue(c *Continuation) *Data {
	return &Data{Type: ContinuationType, Value: unsafe.Pointer(c)}
}

// ContinuationValue extracts a continuation from a Data value.
func ContinuationValue(d *Data) *Continuation {
	if d == nil || d.Type != ContinuationType {
		return nil
	}
	return (*Continuation)(d.Value)
}

// ContinuationP reports whether d is a saved continuation.
func ContinuationP(d *Data) bool {
	return d != nil && TypeOf(d) == ContinuationType
}

// CallableP reports whether d can be applied as a procedure: user functions,
// host primitives and saved continuations.
func CallableP(d *Data) bool {
	return FunctionP(d) || PrimitiveP(d) || ContinuationP(d)
}

// cloneFrames produces an independent copy of a saved stack. The Data values
// and environments referenced by frames are intentionally shared: only the
// control state is copied, never the user's mutable heap.
func cloneFrames(in []vmFrame) []vmFrame {
	if in == nil {
		return nil
	}
	out := make([]vmFrame, len(in))
	for i, f := range in {
		out[i] = f.vmClone()
	}
	return out
}

// ---------------------------------------------------------------------------
// call/cc registration
// ---------------------------------------------------------------------------

var callCcPrimitive *PrimitiveFunction

// RegisterContinuationPrimitives installs call/cc and its long synonym. Both
// names refer to the same intrinsic primitive value.
func RegisterContinuationPrimitives() {
	f := &PrimitiveFunction{Name: "call/cc", Special: false, IsRestricted: false, Body: callCcUnavailableImpl}
	f.parseNumArgs("1")
	callCcPrimitive = f
	d := PrimitiveWithNameAndFunc("call/cc", f)
	Global.BindToProtected(Intern("call/cc"), d)
	Global.BindToProtected(Intern("call-with-current-continuation"), d)
}

// callCcUnavailableImpl is only reached if the intrinsic is applied outside
// the machine (for example through the public ApplyWithoutEval); the machine
// itself always intercepts the value and performs a real capture.
func callCcUnavailableImpl(args *Data, env *SymbolTableFrame) (result *Data, err error) {
	return nil, ProcessError(continuationUnsupportedMessage, env)
}

// Pointers to built-in primitives that the machine must implement itself so
// that callbacks and evaluation positions remain part of the captured stack.
var (
	mapPrimitive        *PrimitiveFunction
	forEachPrimitive    *PrimitiveFunction
	applyPrimitive      *PrimitiveFunction
	loadPrimitive       *PrimitiveFunction
	timePrimitive       *PrimitiveFunction
	onErrorPrimitive    *PrimitiveFunction
	evalPrimitive       *PrimitiveFunction
	globalEvalPrimitive *PrimitiveFunction
)

func primitiveBoundAs(name string) *PrimitiveFunction {
	v := Global.ValueOf(Intern(name))
	if PrimitiveP(v) {
		return PrimitiveValue(v)
	}
	return nil
}

// resolveIntrinsicPointers must be called after all built-ins are registered.
func resolveIntrinsicPointers() {
	mapPrimitive = primitiveBoundAs("map")
	forEachPrimitive = primitiveBoundAs("for-each")
	applyPrimitive = primitiveBoundAs("apply")
	loadPrimitive = primitiveBoundAs("load")
	timePrimitive = primitiveBoundAs("time")
	onErrorPrimitive = primitiveBoundAs("on-error")
	evalPrimitive = primitiveBoundAs("eval")
	globalEvalPrimitive = primitiveBoundAs("global-eval")
}

// ---------------------------------------------------------------------------
// Nested-evaluation detection
//
// Go code (macro expansion, eval, custom special forms, host primitives,
// frame methods) may call Eval while the machine is already running. Such a
// nested evaluator only owns an empty machine stack, so a continuation
// captured there would silently omit the pending computation; capture and
// invocation are therefore rejected there with an ordinary error.
//
// Detection happens only when a continuation is captured or invoked (a rare
// event) by counting runVM frames on the Go stack, so ordinary evaluation
// pays no per-entry cost. A frameMacroExpand marker additionally rejects
// captures inside a macro transformer that runs on the machine itself.
// ---------------------------------------------------------------------------

// inNestedEvaluation reports whether the current call runs inside another
// (suspended) machine on this goroutine, or inside a machine boundary (such
// as a macro transformer) that cannot represent the rest of the computation.
func (m *vm) inNestedEvaluation() bool {
	var pcs [256]uintptr
	n := runtime.Callers(3, pcs[:])
	frames := runtime.CallersFrames(pcs[:n])
	runVMs := 0
	for {
		frame, more := frames.Next()
		if strings.Contains(frame.Function, "golisp.runVM") {
			runVMs++
		}
		if !more {
			break
		}
	}
	if runVMs >= 2 {
		return true
	}
	for _, fr := range m.stack {
		if _, blocked := fr.(*frameMacroExpand); blocked {
			return true
		}
	}
	return false
}

// ---------------------------------------------------------------------------
// The machine
// ---------------------------------------------------------------------------

// vmFrame is one defunctionalized continuation frame.
type vmFrame interface {
	// vmResume receives the value of the sub-computation pushed on top of
	// this frame and schedules the next step by mutating m. The frame has
	// already been popped from m.stack when vmResume runs; frames that are
	// still waiting must push themselves back.
	vmResume(v *Data, m *vm) error

	// vmAnnotate wraps an error unwinding through this frame, or returns
	// the error unchanged.
	vmAnnotate(err error) error

	// vmClone returns an independent copy for continuation capture.
	vmClone() vmFrame
}

type vm struct {
	expr         *Data
	env          *SymbolTableFrame
	returning    bool
	val          *Data
	stack        []vmFrame
	needFunction bool
}

func (m *vm) push(f vmFrame) {
	m.stack = append(m.stack, f)
}

func (m *vm) evalNext(e *Data, env *SymbolTableFrame, needFunction bool) {
	m.returning = false
	m.expr = e
	m.env = env
	m.needFunction = needFunction
}

func (m *vm) complete(v *Data) {
	m.returning = true
	m.val = v
}

func (m *vm) logEnter(e *Data, env *SymbolTableFrame) {
	if IsInteractive && !DebugEvalInDebugRepl {
		env.CurrentCode.PushFront(fmt.Sprintf("Eval %s", String(e)))
	}
	logEval(e, env)

	if DebugSingleStep {
		DebugSingleStep = false
		DebugRepl(env)
	}

	if DebugCurrentFrame != nil && env == DebugCurrentFrame.Previous {
		DebugCurrentFrame = nil
		DebugRepl(env)
	}
}

func (m *vm) logExit(v *Data, env *SymbolTableFrame) {
	logResult(v, env)
	if IsInteractive && !DebugEvalInDebugRepl && env.CurrentCode.Len() > 0 {
		env.CurrentCode.Remove(env.CurrentCode.Front())
	}
}

// fail unwinds the machine after an error. on-error frames catch; other
// frames may annotate. It reports whether a handler caught the error.
func (m *vm) fail(err error) bool {
	for len(m.stack) > 0 {
		fr := m.stack[len(m.stack)-1]
		m.stack = m.stack[:len(m.stack)-1]
		if oe, ok := fr.(*frameOnError); ok && oe.catches() {
			oe.caught(err, m)
			return true
		}
		err = fr.vmAnnotate(err)
	}
	return false
}

// runVM is the core evaluation loop. Every public Eval enters here.
func runVM(d0 *Data, env0 *SymbolTableFrame) (result *Data, err error) {
	m := &vm{expr: d0, env: env0}
	for {
		if m.returning {
			if len(m.stack) == 0 {
				return m.val, nil
			}
			fr := m.stack[len(m.stack)-1]
			m.stack = m.stack[:len(m.stack)-1]
			if e := fr.vmResume(m.val, m); e != nil {
				if !m.fail(e) {
					return nil, e
				}
			}
			continue
		}

		e := m.expr
		env := m.env
		m.logEnter(e, env)

		if e != nil && e.Type == ConsCellType {
			ee := postProcessShortcuts(e)
			if NilP(ee) {
				m.logExit(EmptyCons(), env)
				m.complete(EmptyCons())
				continue
			}
			fa := &frameApp{orig: ee, env: env}
			m.push(fa)
			m.evalNext(Car(ee), env, true)
		} else {
			var v *Data
			switch {
			case e == nil:
				v = nil
			case e.Type == SymbolType:
				if NakedP(e) {
					v = e
				} else {
					v = env.ValueOfWithFunctionSlotCheck(e, m.needFunction)
				}
			default:
				v = e
			}
			m.logExit(v, env)
			m.complete(v)
		}
	}
}

// ---------------------------------------------------------------------------
// Application frame: operator and arguments, then the callee
// ---------------------------------------------------------------------------

type frameApp struct {
	orig         *Data
	env          *SymbolTableFrame
	fn           *Data
	operatorDone bool
	rest         *Data // unevaluated argument expressions still due
	vals         []*Data
	applying     bool // errors below are wrapped as application errors
	launched     bool // callee/sub-computation running; next resume is final

	profKind string // "", "prim" or "form"
	profName string
	profGuid int64
}

func (f *frameApp) vmClone() vmFrame {
	cp := *f
	if f.vals != nil {
		cp.vals = make([]*Data, len(f.vals))
		copy(cp.vals, f.vals)
	}
	return &cp
}

// failf returns err already annotated as this frame would annotate it while
// unwinding (the frame itself is detached while producing the error).
func (f *frameApp) failf(err error) error {
	f.exitProfile()
	if f.applying {
		return fmt.Errorf("\nEvaling %s. %w", String(f.orig), err)
	}
	return err
}

func (f *frameApp) enterProfile(kind string, name string) {
	guid := atomic.AddInt64(&ProfileGUID, 1) - 1
	f.profKind = kind
	f.profName = name
	f.profGuid = guid
	ProfileEnter(kind, name, guid)
}

func (f *frameApp) exitProfile() {
	if f.profKind != "" {
		ProfileExit(f.profKind, f.profName, f.profGuid)
		f.profKind = ""
	}
}

// finish routes the final value of the application to its continuation,
// reproducing evalHelper's tracing, profile and debug bookkeeping.
func (f *frameApp) finish(m *vm, v *Data) {
	f.exitProfile()
	if DebugReturnValue != nil {
		v = DebugReturnValue
		DebugReturnValue = nil
	}
	m.logExit(v, f.env)
	m.complete(v)
}

func (f *frameApp) vmResume(v *Data, m *vm) error {
	if f.launched {
		f.finish(m, v)
		return nil
	}

	if !f.operatorDone {
		f.operatorDone = true
		f.rest = Cdr(f.orig)

		if NilP(v) {
			return errors.New(fmt.Sprintf("Nil when function or macro expected for %s.", String(Car(f.orig))))
		}
		f.fn = v

		if !DebugSingleStep && TypeOf(v) == FunctionType && DebugOnEntry.Has(FunctionValue(v).Name) {
			DebugRepl(f.env)
		}

		if PrimitiveP(v) {
			f.applying = true
			p := PrimitiveValue(v)
			// Mirror PrimitiveFunction.Apply: restricted and arity errors
			// are raised before arguments are evaluated.
			if p.IsRestricted && f.env.IsRestricted {
				return f.failf(fmt.Errorf("The %s primitive is restricted from execution in this environment\n", p.Name))
			}
			if !p.checkArgumentCount(Length(f.rest)) {
				return f.failf(ProcessError(fmt.Sprintf("Wrong number of args to %s, expected %s but got %d.", p.Name, p.argsString(), Length(f.rest)), f.env))
			}
			if p.Special {
				return m.runSpecial(f, p)
			}
			return m.evalArguments(f)
		}

		if MacroP(v) {
			// Macro expansion runs on the machine itself: the transformer
			// body is evaluated in a fresh expansion environment (raw
			// arguments bound), after which the expanded form is evaluated
			// at the use site. frameMacroExpand marks the transformer
			// extent where continuation capture is unsupported.
			f.applying = true
			f.launched = true
			mc := MacroValue(v)
			localEnv, err := mc.expandEnvironment(f.rest, f.env)
			if err != nil {
				return f.failf(err)
			}
			m.push(f)
			(&frameMacroExpand{argEnv: f.env, body: mc.Body}).start(m, localEnv)
			return nil
		}

		if FunctionP(v) || ContinuationP(v) {
			f.applying = true
			return m.evalArguments(f)
		}

		f.applying = true
		return f.failf(errors.New(fmt.Sprintf("%s when function or macro expected for %s.", TypeName(TypeOf(v)), String(v))))
	}

	// an evaluated argument
	f.vals = append(f.vals, v)
	return m.evalArguments(f)
}

func (f *frameApp) vmAnnotate(err error) error {
	if f.applying {
		f.exitProfile()
		return fmt.Errorf("\nEvaling %s. %w", String(f.orig), err)
	}
	return err
}

// evalArguments continues left-to-right argument evaluation or launches the
// callee once every argument has a value.
func (m *vm) evalArguments(f *frameApp) error {
	if NilP(f.rest) {
		return m.launch(f)
	}
	a := Car(f.rest)
	f.rest = Cdr(f.rest)
	m.push(f)
	m.evalNext(a, f.env, false)
	return nil
}

func (m *vm) launch(f *frameApp) error {
	switch {
	case PrimitiveP(f.fn):
		return m.callPrimitive(PrimitiveValue(f.fn), f.vals, f.env, f)
	case ContinuationP(f.fn):
		return m.jumpToContinuation(ContinuationValue(f.fn), f.vals, f)
	case FunctionP(f.fn):
		fn := FunctionValue(f.fn)
		var fm *FrameMap
		if atomic.LoadInt32(&fn.SlotFunction) == 1 && f.env.HasFrame() {
			fm = f.env.Frame
		}
		localEnv, err := fn.bindForCall(ArrayToList(f.vals), f.env, fm, false)
		if err != nil {
			return f.failf(err)
		}
		f.launched = true
		fb := newFrameBody(fn, localEnv)
		m.push(f)
		fb.start(m)
		return nil
	default:
		return f.failf(errors.New(fmt.Sprintf("%s when function or macro expected for %s.", TypeName(TypeOf(f.fn)), String(f.fn))))
	}
}

// ---------------------------------------------------------------------------
// Function body and generic sequence frames
// ---------------------------------------------------------------------------

type frameBody struct {
	fn     *Function
	env    *SymbolTableFrame
	rest   *Data
	inBody bool
	guid   int64
}

func newFrameBody(fn *Function, env *SymbolTableFrame) *frameBody {
	guid := atomic.AddInt64(&ProfileGUID, 1) - 1
	ProfileEnter("func", fn.Name, guid)
	return &frameBody{fn: fn, env: env, rest: fn.Body, guid: guid}
}

func (f *frameBody) vmClone() vmFrame {
	cp := *f
	return &cp
}

func (f *frameBody) start(m *vm) {
	if NilP(f.rest) {
		ProfileExit("func", f.fn.Name, f.guid)
		m.complete(nil)
		return
	}
	f.inBody = true
	m.push(f)
	m.evalNext(Car(f.rest), f.env, false)
}

func (f *frameBody) vmResume(v *Data, m *vm) error {
	if NotNilP(Cdr(f.rest)) {
		f.rest = Cdr(f.rest)
		m.push(f)
		m.evalNext(Car(f.rest), f.env, false)
		return nil
	}
	ProfileExit("func", f.fn.Name, f.guid)
	f.inBody = false
	m.complete(v)
	return nil
}

func (f *frameBody) vmAnnotate(err error) error {
	if f.inBody {
		ProfileExit("func", f.fn.Name, f.guid)
		f.inBody = false
		return errors.New(fmt.Sprintf("In '%s': %s", f.fn.Name, err))
	}
	return err
}

// frameMacroExpand evaluates a macro transformer body in its expansion
// environment and then evaluates the resulting form at the use site. Its
// presence on the stack marks an extent where call/cc capture and
// continuation invocation are unsupported (macro transformer internals).
type frameMacroExpand struct {
	argEnv *SymbolTableFrame
	body   *Data
}

func (f *frameMacroExpand) vmClone() vmFrame { cp := *f; return &cp }

func (f *frameMacroExpand) start(m *vm, localEnv *SymbolTableFrame) {
	m.push(f)
	m.evalNext(f.body, localEnv, false)
}

func (f *frameMacroExpand) vmResume(v *Data, m *vm) error {
	// The transformer finished with v; evaluate the expanded form in the
	// environment of the use site. The frame is already detached.
	m.evalNext(v, f.argEnv, false)
	return nil
}

func (f *frameMacroExpand) vmAnnotate(err error) error { return err }

// frameSeq evaluates expressions in order within one environment, returning
// the value of the last one (nil when empty). Used by begin, clause bodies,
// let bodies and similar forms.
type frameSeq struct {
	rest *Data
	env  *SymbolTableFrame
}

func (f *frameSeq) vmClone() vmFrame { cp := *f; return &cp }

func (f *frameSeq) start(m *vm) {
	if NilP(f.rest) {
		m.complete(nil)
		return
	}
	m.push(f)
	m.evalNext(Car(f.rest), f.env, false)
}

func (f *frameSeq) vmResume(v *Data, m *vm) error {
	if NotNilP(Cdr(f.rest)) {
		f.rest = Cdr(f.rest)
		m.push(f)
		m.evalNext(Car(f.rest), f.env, false)
		return nil
	}
	m.complete(v)
	return nil
}

func (f *frameSeq) vmAnnotate(err error) error { return err }

// ---------------------------------------------------------------------------
// Primitive invocation from within the machine (argument values ready)
// ---------------------------------------------------------------------------

// invokeValue applies fn to already evaluated argv with whatever frames are
// waiting on the stack (frameMap, frameOnError, a call/cc receiver ...).
func (m *vm) invokeValue(fn *Data, argv []*Data, callEnv *SymbolTableFrame) error {
	switch {
	case FunctionP(fn):
		userFn := FunctionValue(fn)
		var fm *FrameMap
		if atomic.LoadInt32(&userFn.SlotFunction) == 1 && callEnv.HasFrame() {
			fm = callEnv.Frame
		}
		localEnv, err := userFn.bindForCall(ArrayToList(argv), callEnv, fm, false)
		if err != nil {
			return err
		}
		fb := newFrameBody(userFn, localEnv)
		fb.start(m)
		return nil
	case PrimitiveP(fn):
		return m.callPrimitive(PrimitiveValue(fn), argv, callEnv, nil)
	case ContinuationP(fn):
		return m.jumpToContinuation(ContinuationValue(fn), argv, nil)
	default:
		return ProcessError(fmt.Sprintf("%s when function or macro expected for %s.", TypeName(TypeOf(fn)), String(fn)), callEnv)
	}
}

// callPrimitive applies a host primitive (or intrinsic) to evaluated args.
// app is the frameApp for a direct application when present; it receives the
// final result and performs application level bookkeeping.
func (m *vm) callPrimitive(p *PrimitiveFunction, argv []*Data, env *SymbolTableFrame, app *frameApp) error {
	fail := func(err error) error {
		if app != nil {
			return app.failf(err)
		}
		return err
	}

	if p.IsRestricted && env.IsRestricted {
		return fail(fmt.Errorf("The %s primitive is restricted from execution in this environment\n", p.Name))
	}
	if !p.checkArgumentCount(len(argv)) {
		return fail(ProcessError(fmt.Sprintf("Wrong number of args to %s, expected %s but got %d.", p.Name, p.argsString(), len(argv)), env))
	}

	// Intrinsics whose callbacks must stay inside the machine.
	switch p {
	case callCcPrimitive:
		return m.callWithContinuation(argv, env, app)
	case mapPrimitive, forEachPrimitive:
		return m.launchMap(p, argv, env, app)
	case applyPrimitive:
		return m.launchApply(argv, env, app)
	case loadPrimitive:
		return m.launchLoad(argv, env, app)
	case evalPrimitive:
		return m.launchEval(argv, env, app, false)
	case globalEvalPrimitive:
		return m.launchEval(argv, env, app, true)
	}

	kind := "prim"
	if p.Special {
		kind = "form"
	}
	guid := atomic.AddInt64(&ProfileGUID, 1) - 1
	ProfileEnter(kind, p.Name, guid)
	r, err := p.Body(ArrayToList(argv), env)
	ProfileExit(kind, p.Name, guid)
	if err != nil {
		return fail(err)
	}
	if app != nil {
		app.finish(m, r)
	} else {
		m.complete(r)
	}
	return nil
}

// callWithContinuation implements (call/cc proc).
func (m *vm) callWithContinuation(argv []*Data, env *SymbolTableFrame, app *frameApp) error {
	proc := argv[0]
	if !CallableP(proc) || MacroP(proc) {
		err := ProcessError(fmt.Sprintf("call/cc expects a callable procedure as its only argument, but got %s.", String(proc)), env)
		if app != nil {
			return app.failf(err)
		}
		return err
	}
	if m.inNestedEvaluation() {
		err := ProcessError(continuationUnsupportedMessage, env)
		if app != nil {
			return app.failf(err)
		}
		return err
	}

	// The frameApp of the call/cc expression itself is detached right now
	// and must not be part of the captured rest-computation.
	snapshot := cloneFrames(m.stack)
	cont := &Continuation{id: atomic.AddInt64(&continuationIdCounter, 1) + 1, frames: snapshot}
	contData := ContinuationWithValue(cont)

	if app != nil {
		app.launched = true
		m.push(app)
	}
	return m.invokeValue(proc, []*Data{contData}, env)
}

// jumpToContinuation abandons the current pending computation and feeds val
// to a fresh copy of the saved stack.
func (m *vm) jumpToContinuation(cont *Continuation, argv []*Data, app *frameApp) error {
	if len(argv) != 1 {
		err := ProcessError(fmt.Sprintf("a continuation expects exactly one argument, but got %d.", len(argv)), nil)
		if app != nil {
			return app.failf(err)
		}
		return err
	}
	if m.inNestedEvaluation() {
		err := ProcessError(continuationUnsupportedMessage, nil)
		if app != nil {
			return app.failf(err)
		}
		return err
	}
	m.stack = cloneFrames(cont.frames)
	m.complete(argv[0])
	return nil
}

// launchMap implements map and for-each with an explicit frame, so escapes
// inside a callback retain the already produced prefix and pending suffix.
func (m *vm) launchMap(p *PrimitiveFunction, argv []*Data, env *SymbolTableFrame, app *frameApp) error {
	foreach := p == forEachPrimitive
	what := "map"
	if foreach {
		what = "foreach"
	}
	fn := argv[0]
	if !CallableP(fn) || MacroP(fn) {
		err := ProcessError(fmt.Sprintf("%s needs a function as its first argument, but got %s.", what, String(fn)), env)
		if app != nil {
			return app.failf(err)
		}
		return err
	}

	collections := make([]*Data, 0, len(argv)-1)
	loopCount := int64(1<<63 - 1)
	for _, col := range argv[1:] {
		if !ListP(col) {
			err := ProcessError(fmt.Sprintf("%s needs lists as its other arguments, but got %s.", what, String(col)), env)
			if app != nil {
				return app.failf(err)
			}
			return err
		}
		if NilP(col) {
			// Historical quirk: an empty collection ends the iteration
			// immediately with a nil result.
			if app != nil {
				app.finish(m, nil)
			} else {
				m.complete(nil)
			}
			return nil
		}
		collections = append(collections, col)
		if int64(Length(col)) < loopCount {
			loopCount = int64(Length(col))
		}
	}
	if len(collections) == 0 {
		if app != nil {
			app.finish(m, nil)
		} else {
			m.complete(nil)
		}
		return nil
	}

	if app != nil {
		app.launched = true
		m.push(app)
	}
	fm := &frameMap{fn: fn, collections: collections, total: int(loopCount), foreach: foreach, env: env}
	fm.start(m)
	return nil
}

type frameMap struct {
	fn          *Data
	collections []*Data // current remaining list of each collection
	total       int
	index       int
	collected   []*Data
	foreach     bool
	env         *SymbolTableFrame
}

func (f *frameMap) vmClone() vmFrame {
	cp := *f
	cp.collections = make([]*Data, len(f.collections))
	copy(cp.collections, f.collections)
	if f.collected != nil {
		cp.collected = make([]*Data, len(f.collected))
		copy(cp.collected, f.collected)
	}
	return &cp
}

func (f *frameMap) start(m *vm) {
	m.push(f)
	_ = f.next(m)
}

func (f *frameMap) next(m *vm) error {
	mapArgs := make([]*Data, 0, len(f.collections))
	for i, col := range f.collections {
		mapArgs = append(mapArgs, Car(col))
		f.collections[i] = Cdr(col)
	}
	f.index++
	return m.invokeValue(f.fn, mapArgs, f.env)
}

func (f *frameMap) vmResume(v *Data, m *vm) error {
	if !f.foreach {
		f.collected = append(f.collected, v)
	}
	if f.index < f.total {
		m.push(f)
		return f.next(m)
	}
	if f.foreach {
		m.complete(nil)
	} else {
		m.complete(ArrayToList(f.collected))
	}
	return nil
}

func (f *frameMap) vmAnnotate(err error) error { return err }

// launchApply implements apply with already evaluated arguments: the final
// argument is spliced as the argument tail, then the call happens.
func (m *vm) launchApply(argv []*Data, env *SymbolTableFrame, app *frameApp) error {
	fn := argv[0]
	if !CallableP(fn) || MacroP(fn) {
		err := ProcessError(fmt.Sprintf("apply requires a function as it's first argument, but got %s.", String(fn)), env)
		if app != nil {
			return app.failf(err)
		}
		return err
	}
	if len(argv) < 2 {
		err := ProcessError("The last argument to apply must be a list", env)
		if app != nil {
			return app.failf(err)
		}
		return err
	}
	last := argv[len(argv)-1]
	if !ListP(last) {
		err := ProcessError("The last argument to apply must be a list", env)
		if app != nil {
			return app.failf(err)
		}
		return err
	}
	unfolded := make([]*Data, 0, len(argv)-1+Length(last))
	unfolded = append(unfolded, argv[1:len(argv)-1]...)
	for c := last; NotNilP(c); c = Cdr(c) {
		unfolded = append(unfolded, Car(c))
	}
	if app != nil {
		app.launched = true
		m.push(app)
	}
	return m.invokeValue(fn, unfolded, env)
}

// launchLoad implements load in-machine so loaded code can capture
// continuations in the same evaluation.
func (m *vm) launchLoad(argv []*Data, env *SymbolTableFrame, app *frameApp) error {
	filename := argv[0]
	if !StringP(filename) {
		err := ProcessError("Filename must be a string", env)
		if app != nil {
			return app.failf(err)
		}
		return err
	}

	src, err := ReadFile(StringValue(filename))
	if err != nil {
		if app != nil {
			return app.failf(err)
		}
		return err
	}

	forms := make([]*Data, 0)
	tokenizer := NewTokenizerFromString(src)
	for {
		sexpr, eof, perr := parseExpression(tokenizer)
		if perr != nil {
			if app != nil {
				return app.failf(perr)
			}
			return perr
		}
		if eof {
			break
		}
		if NilP(sexpr) {
			break
		}
		forms = append(forms, sexpr)
	}

	if app != nil {
		app.launched = true
		m.push(app)
	}
	fl := &frameLoad{rest: ArrayToList(forms)}
	fl.start(m)
	return nil
}

// frameLoad evaluates parsed file forms in the global environment, matching
// ProcessFile semantics for load.
type frameLoad struct {
	rest *Data
}

func (f *frameLoad) vmClone() vmFrame { cp := *f; return &cp }

func (f *frameLoad) start(m *vm) {
	if NilP(f.rest) {
		m.complete(nil)
		return
	}
	m.push(f)
	m.evalNext(Car(f.rest), Global, false)
}

func (f *frameLoad) vmResume(v *Data, m *vm) error {
	if NotNilP(Cdr(f.rest)) {
		f.rest = Cdr(f.rest)
		m.push(f)
		m.evalNext(Car(f.rest), Global, false)
		return nil
	}
	m.complete(v)
	return nil
}

func (f *frameLoad) vmAnnotate(err error) error { return err }

// launchEval implements eval/global-eval inside the machine, so code run
// through eval shares the pending computation and may capture it.
func (m *vm) launchEval(argv []*Data, env *SymbolTableFrame, app *frameApp, global bool) error {
	target := env
	if global {
		target = Global
	} else if len(argv) == 2 {
		if !EnvironmentP(argv[1]) {
			err := ProcessError(fmt.Sprintf("eval expects an environment as it's second argument, but recieved %s.", String(argv[1])), env)
			if app != nil {
				return app.failf(err)
			}
			return err
		}
		target = EnvironmentValue(argv[1])
	}
	code := argv[0]
	if app != nil {
		app.launched = true
		m.push(app)
	}
	m.push(&frameEval{})
	m.evalNext(code, target, false)
	return nil
}

// frameEval forwards the value of the evaluated code to its caller.
type frameEval struct{}

func (f *frameEval) vmClone() vmFrame              { return &frameEval{} }
func (f *frameEval) vmResume(v *Data, m *vm) error { m.complete(v); return nil }
func (f *frameEval) vmAnnotate(err error) error    { return err }

// ---------------------------------------------------------------------------
// Special forms
// ---------------------------------------------------------------------------

// runSpecial dispatches a special primitive whose (raw) arguments are not
// evaluated yet. Core forms run as machine frames; forms that only need plain
// Go evaluation (quasiquote, expand, ->, =>, definition-of, profile and
// similar) call their existing Go bodies, whose nested Eval calls reject
// continuation capture explicitly.
func (m *vm) runSpecial(f *frameApp, p *PrimitiveFunction) error {
	rawArgs := f.rest
	env := f.env
	goAhead := func() error {
		f.launched = true
		f.enterProfile("form", p.Name)
		m.push(f)
		return nil
	}
	finishNow := func(v *Data) {
		f.enterProfile("form", p.Name)
		f.finish(m, v)
	}
	failNow := func(err error) error {
		f.enterProfile("form", p.Name)
		return f.failf(err)
	}

	switch p {
	case timePrimitive:
		if err := goAhead(); err != nil {
			return err
		}
		ft := &frameTime{rest: rawArgs, env: env, startTime: time.Now()}
		ft.start(m)
		return nil
	case onErrorPrimitive:
		if Length(rawArgs) < 2 {
			return failNow(ProcessError("on-error requires a protected expression and a handler", env))
		}
		if err := goAhead(); err != nil {
			return err
		}
		oe := &frameOnError{
			body:    Car(rawArgs),
			handler: Second(rawArgs),
			noErr:   Third(rawArgs),
			env:     env,
		}
		oe.start(m)
		return nil
	}

	switch p.Name {
	case "quote":
		if Car(rawArgs) == nil {
			finishNow(EmptyCons())
		} else {
			finishNow(Car(rawArgs))
		}
		return nil
	case "lambda":
		if !PairP(Car(rawArgs)) {
			return failNow(ProcessError("A lambda requires a parameter list", env))
		}
		finishNow(FunctionWithNameParamsBodyAndParent("unnamed", Car(rawArgs), Cdr(rawArgs), env))
		return nil
	case "named-lambda":
		if !PairP(Car(rawArgs)) {
			return failNow(ProcessError("A lambda requires a name/parameter list", env))
		}
		name := Caar(rawArgs)
		if !SymbolP(name) {
			return failNow(ProcessError("A named lambda requires a name that is a symbol", env))
		}
		finishNow(FunctionWithNameParamsBodyAndParent(StringValue(name), Cdar(rawArgs), Cdr(rawArgs), env))
		return nil
	case "define":
		return m.runDefine(f, rawArgs, env, false)
	case "defmacro":
		return m.runDefine(f, rawArgs, env, true)
	case "begin":
		if err := goAhead(); err != nil {
			return err
		}
		(&frameSeq{rest: rawArgs, env: env}).start(m)
		return nil
	case "if":
		if err := goAhead(); err != nil {
			return err
		}
		(&frameIf{test: Car(rawArgs), then: Second(rawArgs), els: Third(rawArgs), env: env}).start(m)
		return nil
	case "when":
		if err := goAhead(); err != nil {
			return err
		}
		(&frameBranch{sense: true, test: Car(rawArgs), body: Cdr(rawArgs), env: env}).start(m)
		return nil
	case "unless":
		if err := goAhead(); err != nil {
			return err
		}
		(&frameBranch{sense: false, test: Car(rawArgs), body: Cdr(rawArgs), env: env}).start(m)
		return nil
	case "cond":
		if err := goAhead(); err != nil {
			return err
		}
		return (&frameCond{rest: rawArgs, env: env}).start(m)
	case "case":
		if err := goAhead(); err != nil {
			return err
		}
		(&frameCase{rest: Cdr(rawArgs), env: env, keyExpr: Car(rawArgs)}).start(m)
		return nil
	case "and":
		if err := goAhead(); err != nil {
			return err
		}
		(&frameLogic{isAnd: true, rest: rawArgs, env: env}).start(m)
		return nil
	case "or":
		if err := goAhead(); err != nil {
			return err
		}
		(&frameLogic{isAnd: false, rest: rawArgs, env: env}).start(m)
		return nil
	case "let":
		return m.runLet(f, rawArgs, env)
	case "let*":
		return m.runLetLike(f, rawArgs, env, letModeStar)
	case "letrec":
		return m.runLetLike(f, rawArgs, env, letModeRec)
	case "do":
		return m.runDo(f, rawArgs, env)
	case "set!":
		symbol := Car(rawArgs)
		if !SymbolP(symbol) {
			return failNow(ProcessError("set! requires a raw (unevaluated) symbol as it's first argument.", env))
		}
		if err := goAhead(); err != nil {
			return err
		}
		(&frameSetVar{symbol: symbol, env: env, valueExpr: Cadr(rawArgs)}).start(m)
		return nil
	case "set-car!":
		if err := goAhead(); err != nil {
			return err
		}
		(&frameSetPair{kind: 1, env: env, pairExpr: Car(rawArgs), valueExpr: Cadr(rawArgs), message: "set-car! requires a pair as it's first argument."}).start(m)
		return nil
	case "set-cdr!":
		if err := goAhead(); err != nil {
			return err
		}
		(&frameSetPair{kind: 2, env: env, pairExpr: Car(rawArgs), valueExpr: Cadr(rawArgs), message: "set-cdr! requires a pair as it's first argument."}).start(m)
		return nil
	case "set-nth!":
		if err := goAhead(); err != nil {
			return err
		}
		(&frameSetNth{env: env, listExpr: First(rawArgs), indexExpr: Second(rawArgs), valueExpr: Third(rawArgs)}).start(m)
		return nil
	}

	// Generic special forms: run the existing Go body. Any nested Eval is a
	// nested machine where continuation capture is clearly rejected.
	f.enterProfile("form", p.Name)
	r, err := p.Body(rawArgs, env)
	if err != nil {
		return f.failf(err)
	}
	f.finish(m, r)
	return nil
}

func (m *vm) runDefine(f *frameApp, rawArgs *Data, env *SymbolTableFrame, macro bool) error {
	thing := Car(rawArgs)
	if SymbolP(thing) {
		valueExpr := Cadr(rawArgs)
		f.launched = true
		f.enterProfile("form", "define")
		m.push(f)
		df := &frameDefine1{symbol: thing, env: env, valueExpr: valueExpr}
		df.start(m)
		return nil
	}
	if PairP(thing) {
		name := Car(thing)
		if !SymbolP(name) {
			f.enterProfile("form", "define")
			return f.failf(ProcessError("Function name has to be a symbol", env))
		}
		if !macro {
			existingValueOrNil := env.ValueOf(name)
			if PrimitiveP(existingValueOrNil) {
				f.enterProfile("form", "define")
				return f.failf(ProcessError(fmt.Sprintf("Primitive function %s can not be redefined.", StringValue(name)), env))
			}
		}
		var value *Data
		if macro {
			// A macro body is the single expression that expands the form.
			value = MacroWithNameParamsBodyAndParent(StringValue(name), Cdr(thing), Cadr(rawArgs), env)
		} else {
			value = FunctionWithNameParamsBodyAndParent(StringValue(name), Cdr(thing), Cdr(rawArgs), env)
		}
		if _, err := env.BindLocallyTo(name, value); err != nil {
			f.enterProfile("form", "define")
			return f.failf(err)
		}
		f.enterProfile("form", "define")
		f.finish(m, value)
		return nil
	}
	msg := "Invalid definition"
	if macro {
		msg = "Invalid macro definition"
	}
	f.enterProfile("form", "define")
	return f.failf(ProcessError(msg, env))
}

type frameDefine1 struct {
	symbol    *Data
	env       *SymbolTableFrame
	valueExpr *Data
}

func (f *frameDefine1) vmClone() vmFrame { cp := *f; return &cp }

func (f *frameDefine1) start(m *vm) {
	m.push(f)
	m.evalNext(f.valueExpr, f.env, false)
}

func (f *frameDefine1) vmResume(v *Data, m *vm) error {
	if _, err := f.env.BindLocallyTo(f.symbol, v); err != nil {
		return err
	}
	m.complete(v)
	return nil
}

func (f *frameDefine1) vmAnnotate(err error) error { return err }

type frameSetVar struct {
	symbol    *Data
	env       *SymbolTableFrame
	valueExpr *Data
}

func (f *frameSetVar) vmClone() vmFrame { cp := *f; return &cp }

func (f *frameSetVar) start(m *vm) {
	m.push(f)
	m.evalNext(f.valueExpr, f.env, false)
}

func (f *frameSetVar) vmResume(v *Data, m *vm) error {
	r, err := f.env.SetTo(f.symbol, v)
	if err != nil {
		return err
	}
	m.complete(r)
	return nil
}

func (f *frameSetVar) vmAnnotate(err error) error { return err }

type frameSetPair struct {
	kind      int
	env       *SymbolTableFrame
	pairExpr  *Data
	valueExpr *Data
	pair      *Data
	message   string
}

func (f *frameSetPair) vmClone() vmFrame { cp := *f; return &cp }

func (f *frameSetPair) start(m *vm) {
	m.push(f)
	m.evalNext(f.pairExpr, f.env, false)
}

func (f *frameSetPair) vmResume(v *Data, m *vm) error {
	if f.pair == nil {
		if !PairP(v) {
			return ProcessError(f.message, f.env)
		}
		f.pair = v
		m.push(f)
		m.evalNext(f.valueExpr, f.env, false)
		return nil
	}
	if f.kind == 1 {
		ConsValue(f.pair).Car = v
	} else {
		ConsValue(f.pair).Cdr = v
	}
	m.complete(v)
	return nil
}

func (f *frameSetPair) vmAnnotate(err error) error { return err }

type frameSetNth struct {
	env       *SymbolTableFrame
	listExpr  *Data
	indexExpr *Data
	valueExpr *Data
	phase     int
	list      *Data
	index     *Data
}

func (f *frameSetNth) vmClone() vmFrame { cp := *f; return &cp }

func (f *frameSetNth) start(m *vm) {
	m.push(f)
	m.evalNext(f.listExpr, f.env, false)
}

func (f *frameSetNth) vmResume(v *Data, m *vm) error {
	switch f.phase {
	case 0:
		if !ListP(v) {
			return ProcessError("set-nth! requires a list as it's first argument.", f.env)
		}
		f.list = v
		f.phase = 1
		m.push(f)
		m.evalNext(f.indexExpr, f.env, false)
	case 1:
		f.index = v
		f.phase = 2
		m.push(f)
		m.evalNext(f.valueExpr, f.env, false)
	case 2:
		m.complete(SetNth(f.list, int(IntegerValue(f.index)), v))
	}
	return nil
}

func (f *frameSetNth) vmAnnotate(err error) error { return err }

// if

type frameIf struct {
	test *Data
	then *Data
	els  *Data
	env  *SymbolTableFrame
}

func (f *frameIf) vmClone() vmFrame { cp := *f; return &cp }

func (f *frameIf) start(m *vm) {
	m.push(f)
	m.evalNext(f.test, f.env, false)
}

func (f *frameIf) vmResume(v *Data, m *vm) error {
	var chosen *Data
	if BooleanValue(v) {
		chosen = f.then
	} else {
		chosen = f.els
	}
	if chosen == nil {
		m.complete(nil)
	} else {
		m.evalNext(chosen, f.env, false)
	}
	return nil
}

func (f *frameIf) vmAnnotate(err error) error { return err }

// when / unless

type frameBranch struct {
	sense bool
	test  *Data
	body  *Data
	env   *SymbolTableFrame
}

func (f *frameBranch) vmClone() vmFrame { cp := *f; return &cp }

func (f *frameBranch) start(m *vm) {
	m.push(f)
	m.evalNext(f.test, f.env, false)
}

func (f *frameBranch) vmResume(v *Data, m *vm) error {
	if BooleanValue(v) == f.sense {
		(&frameSeq{rest: f.body, env: f.env}).start(m)
	} else {
		m.complete(nil)
	}
	return nil
}

func (f *frameBranch) vmAnnotate(err error) error { return err }

// and / or

type frameLogic struct {
	isAnd bool
	rest  *Data
	env   *SymbolTableFrame
}

func (f *frameLogic) vmClone() vmFrame { cp := *f; return &cp }

func (f *frameLogic) start(m *vm) {
	if NilP(f.rest) {
		m.complete(nil)
		return
	}
	m.push(f)
	m.evalNext(Car(f.rest), f.env, false)
}

func (f *frameLogic) vmResume(v *Data, m *vm) error {
	if f.isAnd {
		if !BooleanValue(v) {
			m.complete(v)
			return nil
		}
	} else {
		if BooleanValue(v) {
			m.complete(v)
			return nil
		}
	}
	if NotNilP(Cdr(f.rest)) {
		f.rest = Cdr(f.rest)
		m.push(f)
		m.evalNext(Car(f.rest), f.env, false)
		return nil
	}
	m.complete(v)
	return nil
}

func (f *frameLogic) vmAnnotate(err error) error { return err }

// cond

const (
	condTesting = iota
	condSelected
)

type frameCond struct {
	state  int
	rest   *Data
	env    *SymbolTableFrame
	clause *Data
}

func (f *frameCond) vmClone() vmFrame { cp := *f; return &cp }

func (f *frameCond) start(m *vm) error {
	scheduled, err := f.nextClause(m)
	if err != nil {
		return err
	}
	if !scheduled {
		m.complete(nil)
	}
	return nil
}

// nextClause assumes f is detached. It pushes f when a test or selected
// clause body is scheduled and reports scheduled=false when no clauses
// remain.
func (f *frameCond) nextClause(m *vm) (scheduled bool, err error) {
	for NotNilP(f.rest) {
		f.clause = Car(f.rest)
		f.rest = Cdr(f.rest)
		if !PairP(f.clause) {
			return false, ProcessError("Cond expect a sequence of clauses that are lists", f.env)
		}
		if IsEqual(Car(f.clause), Intern("else")) {
			f.state = condSelected
			m.push(f)
			(&frameSeq{rest: Cdr(f.clause), env: f.env}).start(m)
			return true, nil
		}
		f.state = condTesting
		m.push(f)
		m.evalNext(Car(f.clause), f.env, false)
		return true, nil
	}
	return false, nil
}

func (f *frameCond) vmResume(v *Data, m *vm) error {
	if f.state == condSelected {
		m.complete(v)
		return nil
	}
	if BooleanValue(v) {
		f.state = condSelected
		m.push(f)
		(&frameSeq{rest: Cdr(f.clause), env: f.env}).start(m)
		return nil
	}
	scheduled, err := f.nextClause(m)
	if err != nil {
		return err
	}
	if !scheduled {
		m.complete(nil)
	}
	return nil
}

func (f *frameCond) vmAnnotate(err error) error { return err }

// case

const (
	caseKey = iota
	caseMatching
	caseSelected
)

type frameCase struct {
	state   int
	keyExpr *Data
	key     *Data
	rest    *Data
	clause  *Data
	env     *SymbolTableFrame
}

func (f *frameCase) vmClone() vmFrame { cp := *f; return &cp }

func (f *frameCase) start(m *vm) {
	m.push(f)
	f.state = caseKey
	m.evalNext(f.keyExpr, f.env, false)
}

// nextClause assumes f is detached. It pushes f when a clause body is
// scheduled and returns scheduled=false when no clauses remain.
func (f *frameCase) nextClause(m *vm) (scheduled bool, err error) {
	for NotNilP(f.rest) {
		f.clause = Car(f.rest)
		f.rest = Cdr(f.rest)
		if !PairP(f.clause) {
			return false, ProcessError("Case expectes a sequence of clauses that are lists", f.env)
		}
		if IsEqual(Car(f.clause), Intern("else")) {
			f.state = caseSelected
			m.push(f)
			(&frameSeq{rest: Cdr(f.clause), env: f.env}).start(m)
			return true, nil
		}
		if !ListP(Car(f.clause)) {
			return false, ProcessError("Case the condition part of clauses to be lists of 'else", f.env)
		}
		for v := Car(f.clause); NotNilP(v); v = Cdr(v) {
			if IsEqual(Car(v), f.key) {
				f.state = caseSelected
				m.push(f)
				(&frameSeq{rest: Cdr(f.clause), env: f.env}).start(m)
				return true, nil
			}
		}
	}
	return false, nil
}

func (f *frameCase) vmResume(v *Data, m *vm) error {
	switch f.state {
	case caseKey:
		f.key = v
		f.state = caseMatching
		scheduled, err := f.nextClause(m)
		if err != nil {
			return err
		}
		if !scheduled {
			m.complete(nil)
		}
	default:
		// caseSelected, or the final value after clauses were exhausted.
		m.complete(v)
	}
	return nil
}

func (f *frameCase) vmAnnotate(err error) error { return err }

// let, let*, letrec and named let

const (
	letModePlain = iota
	letModeStar
	letModeRec
)

type frameLet struct {
	mode    int
	pending *Data // binding pairs whose init forms remain
	current *Data // pair whose init form is being evaluated
	local   *SymbolTableFrame
	evalEnv *SymbolTableFrame
	body    *Data
}

func (f *frameLet) vmClone() vmFrame { cp := *f; return &cp }

func (m *vm) runLet(f *frameApp, rawArgs *Data, env *SymbolTableFrame) error {
	if SymbolP(Car(rawArgs)) {
		return m.runNamedLet(f, rawArgs, env)
	}
	return m.runLetLike(f, rawArgs, env, letModePlain)
}

func (m *vm) runLetLike(f *frameApp, rawArgs *Data, env *SymbolTableFrame, mode int) error {
	bindings := Car(rawArgs)
	if !PairP(bindings) {
		f.enterProfile("form", "let")
		return f.failf(ProcessError("Let requires a list of bindings as it's first argument", env))
	}
	local := NewSymbolTableFrameBelow(env, "let")
	local.Previous = env
	evalEnv := env
	if mode != letModePlain {
		evalEnv = local
	}
	for cell := bindings; NotNilP(cell); cell = Cdr(cell) {
		pair := Car(cell)
		if !PairP(pair) {
			f.enterProfile("form", "let")
			return f.failf(ProcessError("Let requires a list of bindings (with are pairs) as it's first argument", env))
		}
		if !SymbolP(Car(pair)) {
			f.enterProfile("form", "let")
			return f.failf(ProcessError("First part of a let binding pair must be a symbol", env))
		}
		if mode == letModeRec {
			if _, err := local.BindLocallyTo(Car(pair), nil); err != nil {
				f.enterProfile("form", "let")
				return f.failf(err)
			}
		}
	}

	f.launched = true
	f.enterProfile("form", "let")
	m.push(f)
	lf := &frameLet{mode: mode, pending: bindings, local: local, evalEnv: evalEnv, body: Cdr(rawArgs)}
	lf.start(m)
	return nil
}

func (f *frameLet) start(m *vm) {
	if NilP(f.pending) {
		// No inits: run the body sequence directly, this frame is not needed.
		(&frameSeq{rest: f.body, env: f.local}).start(m)
		return
	}
	m.push(f)
	f.current = Car(f.pending)
	f.pending = Cdr(f.pending)
	m.evalNext(Cadr(f.current), f.evalEnv, false)
}

func (f *frameLet) vmResume(v *Data, m *vm) error {
	if _, err := f.local.BindLocallyTo(Car(f.current), v); err != nil {
		return err
	}
	if NilP(f.pending) {
		// All inits bound: run the body sequence in the local environment.
		(&frameSeq{rest: f.body, env: f.local}).start(m)
		return nil
	}
	f.current = Car(f.pending)
	f.pending = Cdr(f.pending)
	m.push(f)
	m.evalNext(Cadr(f.current), f.evalEnv, false)
	return nil
}

func (f *frameLet) vmAnnotate(err error) error { return err }

// runNamedLet implements (let name ((var init) ...) body ...) by constructing
// the named closure and invoking it with the unevaluated init expressions,
// exactly as a normal application.
func (m *vm) runNamedLet(f *frameApp, rawArgs *Data, env *SymbolTableFrame) error {
	name := Car(rawArgs)
	if !SymbolP(name) {
		f.enterProfile("form", "let")
		return f.failf(ProcessError("A named let requires a symbol name as its first argument", env))
	}
	bindings := Cadr(rawArgs)
	if !PairP(bindings) {
		f.enterProfile("form", "let")
		return f.failf(ProcessError("A named let requires a list of bindings as it's second argument", env))
	}
	vars := make([]*Data, 0, Length(bindings))
	initials := make([]*Data, 0, Length(bindings))
	for remaining := bindings; NotNilP(remaining); remaining = Cdr(remaining) {
		binding := Car(remaining)
		if !SymbolP(Car(binding)) {
			f.enterProfile("form", "let")
			return f.failf(ProcessError("The first element of a binding must be a symbol", env))
		}
		vars = append(vars, Car(binding))
		initials = append(initials, Cadr(binding))
	}
	local := NewSymbolTableFrameBelow(env, StringValue(name))
	local.Previous = env
	if _, err := local.BindLocallyTo(name, nil); err != nil {
		f.enterProfile("form", "let")
		return f.failf(err)
	}
	namedProc := FunctionWithNameParamsBodyAndParent(StringValue(name), ArrayToList(vars), Cddr(rawArgs), local)
	if _, err := local.BindLocallyTo(name, namedProc); err != nil {
		f.enterProfile("form", "let")
		return f.failf(err)
	}

	// Reuse the ordinary application machinery with the init expressions.
	f.applying = true
	f.fn = namedProc
	f.rest = ArrayToList(initials)
	f.vals = nil
	return m.evalArguments(f)
}

// do

const (
	doInit = iota
	doTest
	doBody
	doExit
	doRebind
)

type frameDo struct {
	phase      int
	outer      *SymbolTableFrame
	local      *SymbolTableFrame
	bindings   *Data
	testClause *Data
	body       *Data
	pending    *Data
	current    *Data
	stepValues []*Data
}

func (f *frameDo) vmClone() vmFrame {
	cp := *f
	if f.stepValues != nil {
		cp.stepValues = make([]*Data, len(f.stepValues))
		copy(cp.stepValues, f.stepValues)
	}
	return &cp
}

func (m *vm) runDo(f *frameApp, rawArgs *Data, env *SymbolTableFrame) error {
	bindings := Car(rawArgs)
	if !PairP(bindings) {
		f.enterProfile("form", "do")
		return f.failf(ProcessError("Do requires a list of bindings as it's first argument", env))
	}
	testClause := Cadr(rawArgs)
	if !PairP(testClause) {
		f.enterProfile("form", "do")
		return f.failf(ProcessError("Do requires a list as it's second argument", env))
	}
	for cell := bindings; NotNilP(cell); cell = Cdr(cell) {
		tuple := Car(cell)
		if !PairP(tuple) {
			f.enterProfile("form", "do")
			return f.failf(ProcessError("Let requires a list of bindings (with are pairs) as it's first argument", env))
		}
		if !SymbolP(First(tuple)) {
			f.enterProfile("form", "do")
			return f.failf(ProcessError("First part of a do binding must be a symbol", env))
		}
	}

	local := NewSymbolTableFrameBelow(env, "do")
	local.Previous = env
	f.launched = true
	f.enterProfile("form", "do")
	m.push(f)
	df := &frameDo{phase: doInit, outer: env, local: local, bindings: bindings, testClause: testClause, body: Cddr(rawArgs), pending: bindings}
	df.start(m)
	return nil
}

func (f *frameDo) start(m *vm) {
	m.push(f)
	f.nextInit(m)
}

// nextInit schedules the next init evaluation, or begins the test. The frame
// is already on the stack when called from start/resume.
func (f *frameDo) nextInit(m *vm) {
	if NilP(f.pending) {
		f.phase = doTest
		m.evalNext(Car(f.testClause), f.local, false)
		return
	}
	f.current = Car(f.pending)
	f.pending = Cdr(f.pending)
	m.evalNext(Cadr(f.current), f.outer, false)
}

func (f *frameDo) vmResume(v *Data, m *vm) error {
	switch f.phase {
	case doInit:
		if _, err := f.local.BindLocallyTo(First(f.current), v); err != nil {
			return err
		}
		m.push(f)
		f.nextInit(m)
		return nil
	case doTest:
		m.push(f)
		if BooleanValue(v) {
			f.phase = doExit
			(&frameSeq{rest: Cdr(f.testClause), env: f.local}).start(m)
			return nil
		}
		f.phase = doBody
		(&frameSeq{rest: f.body, env: f.local}).start(m)
		return nil
	case doExit:
		m.complete(v)
		return nil
	case doBody:
		// body sequence finished; recompute step values
		f.phase = doRebind
		f.pending = f.bindings
		f.stepValues = make([]*Data, 0, Length(f.bindings))
		m.push(f)
		f.nextStep(m)
		return nil
	case doRebind:
		f.stepValues = append(f.stepValues, v)
		m.push(f)
		f.nextStep(m)
		return nil
	}
	return nil
}

// nextStep schedules the next step evaluation (in the local environment),
// reusing the current value for bindings without a step form. When all step
// values are computed against the old bindings, every variable is rebound and
// the test runs again -- without pushing any additional frame, so do stays
// iterative as in the original interpreter.
func (f *frameDo) nextStep(m *vm) {
	if NilP(f.pending) {
		i := 0
		for cell := f.bindings; NotNilP(cell); cell = Cdr(cell) {
			f.local.BindLocallyTo(First(Car(cell)), f.stepValues[i])
			i++
		}
		f.phase = doTest
		m.evalNext(Car(f.testClause), f.local, false)
		return
	}
	f.current = Car(f.pending)
	f.pending = Cdr(f.pending)
	if step := Third(f.current); NotNilP(step) {
		m.evalNext(step, f.local, false)
	} else {
		// No evaluation position: preserve the current binding value.
		f.stepValues = append(f.stepValues, f.local.ValueOf(First(f.current)))
		f.nextStep(m)
	}
}

func (f *frameDo) vmAnnotate(err error) error { return err }

// time

type frameTime struct {
	rest      *Data
	env       *SymbolTableFrame
	startTime time.Time
}

func (f *frameTime) vmClone() vmFrame { cp := *f; return &cp }

func (f *frameTime) start(m *vm) {
	if NilP(f.rest) {
		m.complete(IntegerWithValue(int64(time.Since(f.startTime).Nanoseconds() / 1000000)))
		return
	}
	m.push(f)
	m.evalNext(Car(f.rest), f.env, false)
}

func (f *frameTime) vmResume(v *Data, m *vm) error {
	if NotNilP(Cdr(f.rest)) {
		f.rest = Cdr(f.rest)
		m.push(f)
		m.evalNext(Car(f.rest), f.env, false)
		return nil
	}
	m.complete(IntegerWithValue(int64(time.Since(f.startTime).Nanoseconds() / 1000000)))
	return nil
}

func (f *frameTime) vmAnnotate(err error) error { return err }

// on-error

const (
	onErrorBody = iota
	onErrorHandler
	onErrorNoErr
	onErrorDone
)

type frameOnError struct {
	state   int
	body    *Data
	handler *Data
	noErr   *Data
	env     *SymbolTableFrame
	errText string
}

func (f *frameOnError) vmClone() vmFrame { cp := *f; return &cp }

func (f *frameOnError) start(m *vm) {
	m.push(f)
	f.state = onErrorBody
	m.evalNext(f.body, f.env, false)
}

func (f *frameOnError) vmResume(v *Data, m *vm) error {
	switch f.state {
	case onErrorBody:
		if NotNilP(f.noErr) {
			f.state = onErrorNoErr
			m.push(f)
			m.evalNext(f.noErr, f.env, false)
			return nil
		}
		m.complete(v)
		return nil
	case onErrorNoErr:
		if !FunctionP(v) {
			return ProcessError("on-error requires a function as it's third argument", f.env)
		}
		f.state = onErrorDone
		m.push(f)
		return m.invokeValue(v, nil, f.env)
	case onErrorHandler:
		if !FunctionP(v) {
			return ProcessError("on-error requires a function as it's second argument", f.env)
		}
		f.state = onErrorDone
		m.push(f)
		errString := StringWithValue(f.errText)
		return m.invokeValue(v, []*Data{errString}, f.env)
	case onErrorDone:
		m.complete(v)
	}
	return nil
}

func (f *frameOnError) vmAnnotate(err error) error { return err }

// catches reports whether an error unwinding through this frame is handled.
// Only errors raised while the protected body runs are caught; handler
// evaluation errors propagate past the frame.
func (f *frameOnError) catches() bool { return f.state == onErrorBody }

// caught is invoked by the machine while unwinding an error. f has already
// been popped; it pushes itself back while evaluating the handler.
func (f *frameOnError) caught(err error, m *vm) {
	f.errText = err.Error()
	f.state = onErrorHandler
	m.push(f)
	m.evalNext(f.handler, f.env, false)
}
