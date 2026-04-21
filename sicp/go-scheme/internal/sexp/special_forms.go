package sexp

import "errors"

var FQuote = &SpecialForm{
	name: "quote",
	f: func(env *Env, args ...Expr) (Expr, error) {
		if len(args) != 1 {
			return nil, errors.New("quote: unexpected number of arguments")
		}
		return env.Eval(Quote(args[0]))
	},
}

var FIf = &SpecialForm{
	name: "if",
	f: func(env *Env, args ...Expr) (Expr, error) {
		if len(args) < 2 || len(args) > 3 {
			return nil, errors.New("if: unexpected number of arguments (expected 2 or 3)")
		}

		cond, err := env.Eval(args[0])
		if err != nil {
			return nil, err
		}

		if IsTrue(cond) {
			return env.Eval(args[1])
		}

		if len(args) == 3 {
			return env.Eval(args[2])
		}
		return FALSE, nil
	},
}
