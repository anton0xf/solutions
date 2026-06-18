package sexp

import (
	"errors"
	"fmt"
)

// numeric operations

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

// numeric predicates

func inequalityFn(name string, cmp func(m, n int) bool) *Function {
	return &Function{
		name: name,
		f: func(args ...Expr) (Expr, error) {
			if len(args) < 2 {
				return nil, fmt.Errorf("%s: expected at least 2 arguments", name)
			}
			nums := make([]int, len(args))
			for i, arg := range args {
				n, ok := arg.(*Int)
				if !ok {
					return nil, fmt.Errorf("%s: unexpected argument type: [%d] %s", name, i, arg)
				}
				if n == nil {
					return nil, fmt.Errorf("%s: nil argument %d", name, i)
				}
				nums[i] = n.x
			}
			res := true
			for i := range len(nums) - 1 {
				res = res && cmp(nums[i], nums[i+1])
			}
			return &Bool{res}, nil
		},
	}
}

var FnLt = inequalityFn("<", func(m int, n int) bool { return m < n })
var FnLe = inequalityFn("<=", func(m int, n int) bool { return m <= n })
var FnGt = inequalityFn(">", func(m int, n int) bool { return m > n })
var FnGe = inequalityFn(">=", func(m int, n int) bool { return m >= n })

// lists

var FnList = &Function{
	name: "list",
	f: func(args ...Expr) (Expr, error) {
		return NewList(args...), nil
	},
}

var FnCons = &Function{
	name: "cons",
	f: func(args ...Expr) (Expr, error) {
		if len(args) != 2 {
			return nil, errors.New("cons: unexpected number of arguments")
		}
		return Cons(args[0], args[1]), nil
	},
}

var FnCar = &Function{
	name: "car",
	f: func(args ...Expr) (Expr, error) {
		if len(args) != 1 {
			return nil, errors.New("car: unexpected number of arguments")
		}
		return Car(args[0])
	},
}

var FnCdr = &Function{
	name: "cdr",
	f: func(args ...Expr) (Expr, error) {
		if len(args) != 1 {
			return nil, errors.New("cdr: unexpected number of arguments")
		}
		return Cdr(args[0])
	},
}
