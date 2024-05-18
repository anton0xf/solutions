package unit7_class.lesson2_abstract
// https://stepik.org/lesson/106524/step/5?unit=81050

trait StringProcessor {
  def process(input: String): String
}

object StringProcessor {

  /** обрабатывает строку, удаляя из неё перечисленные знаки препинания: запятая, двоеточие, точка с запятой */
  val tokenDeleter: StringProcessor = _.replaceAll("[,:;]", "")

  /** заменяет все прописные буквы на строчные */
  val toLowerConvertor: StringProcessor = _.toLowerCase

  /** если строка имеет размер больше 20 символов, он оставляет первые 20 и добавляет к ней "..." */
  val shortener: StringProcessor = input =>
    if (input.length > 20) input.substring(0, 20) + "..."
    else input

}
