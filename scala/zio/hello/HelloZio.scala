import zio.*
import zio.Console.*

import java.io.IOException

object HelloZio extends ZIOAppDefault {
  override def run: ZIO[ZIOAppArgs & Scope, Any, Any] = sayHello
  def sayHello: Task[Unit] = for {
    _ <- printLine("What is your name?")
    name <- readLine
    _ <- printLine(s"Hello, ${name}!")
  } yield ()
}
