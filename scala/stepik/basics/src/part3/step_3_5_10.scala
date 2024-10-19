package part3

object Step_3_5_10 {
  trait Fruit {
    val code: String
    override def toString: String = s"$code"
  }

  class Apple(val code: String) extends Fruit

  class GalaApple(code: String) extends Apple(code)

  class GreenApple(code: String) extends Apple(code)

  class Store[-T] {
    def sell[U](fruit: U): Unit = println(s"sell $fruit")
  }

  def main(args: Array[String]): Unit = {
    val store: Store[GalaApple] = new Store[Apple]

    store.sell(new Apple("Apple-4135"))
    store.sell(new GalaApple("GalaApple-4133"))
    store.sell(new GreenApple("GreenApple-3344"))
  }
}
