package u3.l10
package u3.l10

object S04Palindrome {
  @scala.annotation.tailrec
  def isPalindrome(str: String): Boolean = {
    val len = str.length()
    len < 3 || (str.head == str.last &&
      isPalindrome(str.substring(1, len - 1)))
  }
}
