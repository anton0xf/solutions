package sexp

import (
	"errors"
	"fmt"
)

var FnInc = &Function{
	name: "inc",
	f: func(args ...Expr) (Expr, error) {
		if len(args) != 1 {
			return nil, errors.New("inc: unexpected number of arguments")
		}
		if n, ok := args[0].(*Int); ok {
			return &Int{n.x + 1}, nil
		}
		return nil, fmt.Errorf("inc: unexpected argument type: %s", args[0])
	},
}

var FnPlus = &Function{
	name: "+",
	f: func(args ...Expr) (Expr, error) {
		res := 0
		for i, arg := range args {
			n, ok := arg.(*Int)
			if !ok {
				return nil, fmt.Errorf("+: unexpected argument type: [%d] %s", i, arg)
			}
			res += n.x
		}
		return &Int{res}, nil
	},
}
