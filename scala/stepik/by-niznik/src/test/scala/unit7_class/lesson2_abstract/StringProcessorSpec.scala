package unit7_class.lesson2_abstract

import munit.FunSuite

class StringProcessorSpec extends FunSuite {
  import StringProcessor._

  // tokenDeleter - в методе process обрабатывает строку,
  // удаляя из неё перечисленные знаки препинания: запятая, двоеточие, точка с запятой
  test("tokenDeleter") {
    assertEquals(
      tokenDeleter.process("asdf, qwer: aaa; bbb."),
      "asdf qwer aaa bbb."
    )
  }

  // toLowerConvertor - заменяет все прописные буквы на строчные
  test("toLowerConvertor") {
    assertEquals(toLowerConvertor.process("ASDF qwer"), "asdf qwer")
  }

  // shortener - если строка имеет размер больше 20 символов, он оставляет первые 20 и добавляет к ней "..."
  test("shortener") {
    assertEquals(shortener.process("asdf"), "asdf")
    assertEquals(shortener.process("asdf asdf asdf asdf asdf "), "asdf asdf asdf asdf ...")
  }
}
