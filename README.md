golisp
======

GoLisp is a simple Lisp language and runtime implemented in Google’s
Go programming language. It’s main purpose is integration into a Go
application to provide runtime extension and scripting. The core of a
basic Lisp is provided, but with limited special forms and primitive
functions. More of these will be added as required without having to
modify the GoLisp core. Also, a REPL is provided and GoLisp can be
used as-is to enter and evaluate code.

It is heavily inspired and influenced by Scheme (MIT/GNU scheme in
particular). GoLisp 1.0 is much more in line with Scheme, but it is at
it's heart a language for our purposes internally. It's growth and
evolution reflect that.

GoLisp evolves along 4 axis:

* becoming more compatible with MIT/GNU Scheme (GoLisp v1.0 is a huge
  move forward in this regard)
* supporting more capabilities of the underlying Go implementation
  language (e.g. recent work supporting concurrency and channels)
* our particular needs (e.g. byte array support)
* useful additions (e.g. frames)

If GoLisp has a form or function that is also in MIT/GNU scheme, we
strive to make it work the same way.

As much as possible the internals echo those in MIT/GNU Scheme. For
example, the lexical environment structure/handling.

So, while it is intentionally very much like MIT/GNU Scheme, it is not
constrained to conform the specification. That said, unless our
extensions are used, code will usually be indistinguishable.

A complete language reference and other material is available at
[http://techblog.steelseries.com/golisp](http://techblog.steelseries.com/golisp).

A sample application is also available at [https://github.com/SteelSeries/golisp-example-app](https://github.com/SteelSeries/golisp-example-app).

First-class continuations
--------------------------

GoLisp implements Scheme-style escape continuations. `call/cc` (and its
synonym `call-with-current-continuation`) receives one callable procedure
and passes it the current continuation as a first-class value:

```scheme
(call/cc (lambda (k) (k 42) 99))   ; => 42, expressions after (k ...) are abandoned
```

The continuation is an ordinary Lisp value: it can be stored in lexical
bindings and lists, closed over by procedures, passed to `apply`, and
invoked from nested calls, `map`/`for-each` callbacks, `do` loops or named
`let` loops. It accepts exactly one value (`#f` and `()` work like any
other value). Invoking it discards the computation in progress and feeds
the value to a fresh copy of the saved computation, so it can be invoked
any number of times, including from a later public `Eval` /
`ParseAndEvalInEnvironment` call after the evaluation that captured it has
already returned; the result of completing the original computation is
returned to the calling host evaluation.

Only control is captured: lexical bindings, closures and mutable lists
stay shared. Side effects already performed before the capture are not
replayed, while the evaluation positions after the capture re-execute and
observe the current shared state. Already evaluated operator/argument
prefixes (and `map`/`for-each` result prefixes) are retained on
re-entry, and pending suffixes re-execute; left-to-right evaluation order
and short-circuiting are preserved. Distinct saved continuations,
independent environments and evaluations that raised ordinary errors do
not contaminate each other, and failed invocations do not consume a saved
continuation.

The synchronous evaluator itself is unchanged in scope: only serial,
finite, normally-terminating scripts are supported. There is no
`dynamic-wind`, multiple-value return, continuation serialization, or
scheduler integration. Capturing or invoking a continuation is rejected
with an ordinary error (never silently truncated) from boundaries that
enter a nested evaluator through Go: macro transformer internals,
`quasiquote` unquotes, custom special forms, host primitives that call
`Eval`, and frame methods. Continuation objects are not guaranteed to work
across goroutines. `eval`/`global-eval`, `load`, `time` and `on-error` run
on the same evaluator, so code they run may capture continuations
normally.

GoLisp has the following dependencies:

go get github.com/SteelSeries/set.v0
go get github.com/SteelSeries/bufrr
go get gopkg.in/check.v1
