package sexp

import "errors"

var FAnd = &SpecialForm{
	name: "and",
	f: func(env *Env, args ...Expr) (Expr, error) {
		if len(args) == 0 {
			return TRUE, nil
		}

		var res Expr
		for _, arg := range args {
			var err error
			res, err = env.Eval(arg)
			if err != nil {
				return nil, err
			}
			if !IsTrue(res) {
				return res, nil
			}
		}
		return res, nil
	},
}

var FOr = &SpecialForm{
	name: "or",
	f: func(env *Env, args ...Expr) (Expr, error) {
		if len(args) == 0 {
			return FALSE, nil
		}

		for _, arg := range args {
			res, err := env.Eval(arg)
			if err != nil {
				return nil, err
			}
			if IsTrue(res) {
				return res, nil
			}
		}
		return FALSE, nil
	},
}

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
