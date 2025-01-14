import zio.*
import zio.test.*
import zio.test.Assertion.*
import HelloZio.*

object HelloZioSpec extends ZIOSpecDefault {
  override def spec =
    suite("HelloZioSpec")(
      test("run say hello") {
        for {
          _ <- TestConsole.feedLines("ZIO")
          _ <- sayHello
          output <- TestConsole.output
        } yield assertTrue(
          output == Vector(
            "What is your name?\n",
            "Hello, ZIO!\n"
          )
        )
      }
    )
}
