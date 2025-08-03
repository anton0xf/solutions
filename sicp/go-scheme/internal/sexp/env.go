package sexp

type Env struct{}

func (env *Env) Eval(expr Expr) (Expr, error) {
	switch e := expr.(type) {
	case *List:
		return EvalList(e)

	default:
		return e, nil
	}
}

func EvalList(e *List) (Expr, error) {
	// if e == nil {
	return nil, nil
}
