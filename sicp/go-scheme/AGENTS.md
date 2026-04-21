# Agent Configuration

Get TODO items by `task/list-todo` and mark them as done in the end.

Docs are in `doc/`.

ARD in `docs/adr/`.

Running and testing described in `README.md`.

Follow the TDD process.

## File Organization

- `cmd/gs/main.go` - REPL entry point: parses input, evaluates in default environment, prints results
- `internal/sexp/expr.go` - Expression types and helper functions (e.g., `IsTrue()`, `IsList()`)
- `internal/sexp/env.go` - Environment and evaluator (`Env.Eval()`, `NewEnvDefault()`)
- `internal/sexp/functions.go` - Built-in functions (inc, dec, +, -, *, /, list, cons, car, cdr)
- `internal/sexp/special_forms.go` - Special forms with lazy evaluation (quote, if, etc.)
- `internal/sexp/parser.go` - S-expression parser
- `internal/sexp/rune_stream.go` - Rune stream helper for parsing
