package unit5.lesson2

import munit.FunSuite

class PetSaySpec extends FunSuite {
  test("samples") {
    assertEquals(PetSay.petKind(Pet("cat1", "meow")), "cat")
    assertEquals(PetSay.petKind(Pet("cat2", "nya")), "cat")
    assertEquals(PetSay.petKind(Pet("Rex", "auw")), "dog")
    assertEquals(PetSay.petKind(Pet("robot0", "0")), "robot")
    assertEquals(PetSay.petKind(Pet("robot1", "1")), "robot")
    assertEquals(PetSay.petKind(Pet("robot2", "a01")), "robot")
    assertEquals(PetSay.petKind(Pet("pet", "auw")), "unknown")
  }
}
