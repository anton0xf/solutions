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

var FnDec = &Function{
	name: "dec",
	f: func(args ...Expr) (Expr, error) {
		if len(args) != 1 {
			return nil, errors.New("dec: unexpected number of arguments")
		}
		if n, ok := args[0].(*Int); ok {
			return &Int{n.x - 1}, nil
		}
		return nil, fmt.Errorf("dec: unexpected argument type: %s", args[0])
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

var FnMinus = &Function{
	name: "-",
	f: func(args ...Expr) (Expr, error) {
		res := 0
		for i, arg := range args {
			n, ok := arg.(*Int)
			if !ok {
				return nil, fmt.Errorf("-: unexpected argument type: [%d] %s", i, arg)
			}
			if i == 0 {
				res += n.x
			} else {
				res -= n.x
			}
		}
		return &Int{res}, nil
	},
}

var FnMult = &Function{
	name: "*",
	f: func(args ...Expr) (Expr, error) {
		res := 1
		for i, arg := range args {
			n, ok := arg.(*Int)
			if !ok {
				return nil, fmt.Errorf("*: unexpected argument type: [%d] %s", i, arg)
			}
			res *= n.x
		}
		return &Int{res}, nil
	},
}

var FnDiv = &Function{
	name: "/",
	f: func(args ...Expr) (Expr, error) {
		if len(args) <= 1 {
			return nil, errors.New("/: unexpected number of arguments")
		}
		res := 1
		for i, arg := range args {
			n, ok := arg.(*Int)
			if !ok {
				return nil, fmt.Errorf("*: unexpected argument type: [%d] %s", i, arg)
			}
			if i == 0 {
				res = n.x
			} else {
				res /= n.x
			}
		}
		return &Int{res}, nil
	},
}
