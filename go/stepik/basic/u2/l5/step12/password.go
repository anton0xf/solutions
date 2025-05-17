/*
Ваша задача сделать проверку подходит ли пароль вводимый пользователем
под заданные требования. Длина пароля должна быть не менее 5 символов,
он может содержать только арабские цифры и буквы латинского алфавита.
На вход подается строка-пароль.
Если пароль соответствует требованиям - вывести "Ok",
иначе вывести "Wrong password"
*/

package main

import (
	"fmt"
	"unicode"
)

func main() {
	var s string
	fmt.Scan(&s)
	if validPassword(s) {
		fmt.Println("Ok")
	} else {
		fmt.Println("Wrong password")
	}
}

func validPassword(s string) bool {
	rs := []rune(s)
	if len(rs) < 5 {
		return false
	}
	for _, r := range rs {
		if !unicode.IsDigit(r) && !unicode.Is(unicode.Latin, r) {
			return false
		}
	}
	return true
}
