package golisp

import (
	"testing"
)

func BenchmarkFibVM(b *testing.B) {
	src := `
(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
(fib 20)`
	for i := 0; i < b.N; i++ {
		_, err := ParseAndEval(src)
		if err != nil {
			b.Fatal(err)
		}
	}
}
