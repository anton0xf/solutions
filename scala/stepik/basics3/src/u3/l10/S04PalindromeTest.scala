//> using target.scope test
package u3.l10

import munit.* 
import u3.l10.S04Palindrome.*

class S04PalindromeTest extends FunSuite {
  test("isPalindrome") {
    assert(isPalindrome("шалаш"))
    assert(!isPalindrome("aaaf"))
  }
}
