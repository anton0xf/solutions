package sexp

import "errors"

var FQuote = &SpecialForm{
	name: "quote",
	f: func(env *Env, args ...Expr) (Expr, error) {
		if len(args) != 1 {
			return nil, errors.New("quote: unexpected number of arguments")
		}
		return Quote(args[0]), nil
	},
}
