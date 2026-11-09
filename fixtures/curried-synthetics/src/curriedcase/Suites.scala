package curriedcase

import org.scalactic.Prettifier
import org.scalactic.source.Position
import org.scalatest.Suite
import org.scalatest.wordspec.AnyWordSpec
import org.scalatest.matchers.should.Matchers

class ExternalSuite extends Suite {
  val actual: Int = Library.curried(1)
}

class SourceSuite extends Suite {
  def known(value: Int)(implicit position: Position, prettifier: Prettifier): Int =
    Effects.note(value)
  val actual: Int = known(2)
}

class CallbackSuite extends Suite {
  val actual: Int = Library.returned(4)()
}

class ReusedCallbackSuite extends Suite {
  val callback: () => Int = () => Library.curried(16)
  val first: Int = callback()
  val second: Int = callback()
}

class WordSuite extends AnyWordSpec with Matchers {
  "curried word registration" should {
    "run its effect once" in { Library.curried(8); () }
  }
}
