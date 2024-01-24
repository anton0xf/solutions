package recfun

import scala.annotation.tailrec

object RecFun extends RecFunInterface:

  def main(args: Array[String]): Unit =
    println("Pascal's Triangle")
    for row <- 0 to 10 do
      for col <- 0 to row do
        print(s"${pascal(col, row)} ")
      println()

  /**
   * Exercise 1
   */
  def pascal(c: Int, r: Int): Int =
    if c < 0 || c > r then 0
    else if c == 0 || c == r then 1
    else pascal(c-1, r-1) + pascal(c, r-1)

  /**
   * Exercise 2
   */
  def balance(chars: List[Char]): Boolean =
    @tailrec
    def iter(stack: List[Char], chars: List[Char]): Boolean =
      if stack.isEmpty && chars.isEmpty then true
      else if chars.isEmpty then false
      else
        val ch = chars.head
        if ch == '(' then iter(ch :: stack, chars.tail)
        else if ch == ')' then (if stack.isEmpty then false
                                else iter(stack.tail, chars.tail))
        else iter(stack, chars.tail)
    iter(List(), chars)

  /**
   * Exercise 3
   */
  def countChange(money: Int, coins: List[Int]): Int =
    if coins.isEmpty || money < 0 then 0
    else if money == 0 then 1
    else countChange(money - coins.head, coins) + countChange(money, coins.tail)
