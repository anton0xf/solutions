// https://stepik.org/lesson/106517/step/8?unit=81043
List(None, Some(2)).filter(_.isDefined).map(_.get)
List(None, Some(2)).collect{ case Some(x) => x}
List(None, Some(2)).flatten