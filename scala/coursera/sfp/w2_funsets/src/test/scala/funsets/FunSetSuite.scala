package funsets

/**
 * This class is a test suite for the methods in object FunSets.
 *
 * To run this test suite, start "sbt" then run the "test" command.
 */
class FunSetSuite extends munit.FunSuite:

  import FunSets.*

  test("contains is implemented") {
    assert(contains(x => true, 100))
    assert(!contains(x => false, 100))
    assert(contains(x => x == 0, 0))
    assert(!contains(x => x == 0, 1))
  }

  /**
   * When writing tests, one would often like to re-use certain values for multiple
   * tests. For instance, we would like to create an Int-set and have multiple test
   * about it.
   *
   * Instead of copy-pasting the code for creating the set into every test, we can
   * store it in the test class using a val:
   *
   *   val s1 = singletonSet(1)
   *
   * However, what happens if the method "singletonSet" has a bug and crashes? Then
   * the test methods are not even executed, because creating an instance of the
   * test class fails!
   *
   * Therefore, we put the shared values into a separate trait (traits are like
   * abstract classes), and create an instance inside each test method.
   *
   */

  trait TestSets:
    val s1 = singletonSet(1)
    val s2 = singletonSet(2)
    val s3 = singletonSet(3)

  /**
   * This test is currently disabled (by using .ignore) because the method
   * "singletonSet" is not yet implemented and the test would fail.
   *
   * Once you finish your implementation of "singletonSet", remove the
   * .ignore annotation.
   */

  test("singleton set one contains one") {
    
    /**
     * We create a new instance of the "TestSets" trait, this gives us access
     * to the values "s1" to "s3".
     */
    new TestSets:
      /**
       * The string argument of "assert" is a message that is printed in case
       * the test fails. This helps identifying which assertion failed.
       */
      assert(contains(s1, 1), "Singleton")
  }

  test("union contains all elements of each set") {
    new TestSets:
      val s = union(s1, s2)
      assert(contains(s, 1), "Union 1")
      assert(contains(s, 2), "Union 2")
      assert(!contains(s, 3), "Union 3")
  }

  test("intersect") {
    new TestSets:
      val s1_5 = rangeSet(1, 5)
      val s3_10 = rangeSet(3, 10)
      val s = intersect(s1_5, s3_10)
      assert(!contains(s, 0))
      assert(!contains(s, 1))
      assert(!contains(s, 2))
      assert(contains(s, 3))
      assert(contains(s, 4))
      assert(contains(s, 5))
      assert(!contains(s, 6))
      assert(!contains(s, 10))
      assert(!contains(s, 11))
  }

  test("diff [1..3] and [2..5]") {
    val s1_3 = rangeSet(1, 3)
    val s2_5 = rangeSet(2, 5)
    val s = diff(s1_3, s2_5)
    assert(!s(0))
    assert(s(1))
    assert(!s(2))
    assert(!s(3))
    assert(!s(4))
    assert(!s(5))
    assert(!s(6))
  }

  test("diff") {
    new TestSets:
      assert(isEmpty(diff(s1, s1)))
      assert(isEqual(diff(s1, s2), fromSet(Set(1, 2))))
  }

  test("diff of {1,3,4,5,7,1000} and {1,2,3,4}") {
    val s = diff(fromSet(Set(1, 3, 4, 5, 7, 1000)), fromSet(Set(1, 2, 3, 4)))
    assert(isEqual(s, fromSet(Set(2, 5, 7, 1000))))
  }

  test("filter") {
    val s1_5 = rangeSet(1, 5)
    val s = filter(s1_5, x => x % 2 == 0)
    assert(!s(0))
    assert(!s(1))
    assert(s(2))
    assert(!s(3))
    assert(s(4))
    assert(!s(5))
    assert(!s(6))
  }

  test("forall") {
    new TestSets:
      val s1_5 = rangeSet(1, 5)
      assert(forall(s1, s1))
      assert(forall(s2, s2))
      assert(forall(s3, s3))
      assert(forall(s1_5, s1_5))
  }

  test("exists") {
    assert(!exists(rangeSet(1, 5), x => x > 6))
    assert(exists(rangeSet(1, 5), x => x % 2 == 0))
  }

  test("isNotEmpty") {
    assert(isNotEmpty(singletonSet(1)))
    assert(!isNotEmpty(_ => false))
  }

  test("isEmpty") {
    new TestSets:
      assert(!isEmpty(singletonSet(1)))
      assert(isEmpty(_ => false))
      assert(isEmpty(diff(s1, s1)))
      assert(isEmpty(diff(singletonSet(6), singletonSet(6))))
  }

  test("eq") {
    assert(!isEqual(singletonSet(5), singletonSet(6)))
    assert(isEqual(singletonSet(6), singletonSet(6)))
    assert(!isEqual(rangeSet(1, 6), rangeSet(2, 6)))
    assert(!isEqual(rangeSet(1, 6), rangeSet(1, 5)))
    assert(isEqual(rangeSet(1, 6), rangeSet(1, 6)))
  }

  test("map") {
    val s = map(singletonSet(1), x => x + 5)
    assert(!s(0))
    assert(!s(5))
    assert(s(6))
    assert(!s(7))
    assert(!s(100))
    assert(isEqual(s, singletonSet(6)))
  }

  import scala.concurrent.duration.*
  override val munitTimeout = 10.seconds
