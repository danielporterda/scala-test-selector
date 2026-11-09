package curriedcase

import org.scalatest.{Args, Reporter}
import org.scalatest.events.Event

object CheckCurried {
  def main(arguments: Array[String]): Unit = {
    Effects.hits = 0
    println(s"external:${new ExternalSuite().actual}:${Effects.hits}")
    Effects.hits = 0
    println(s"source:${new SourceSuite().actual}:${Effects.hits}")
    Effects.hits = 0
    println(s"returned:${new CallbackSuite().actual}:${Effects.hits}")
    Effects.hits = 0
    val reused = new ReusedCallbackSuite()
    println(s"reused:${reused.first}:${reused.second}:${Effects.hits}")
    Effects.hits = 0
    val word = new WordSuite()
    println(s"registered:${word.testNames.size}:${Effects.hits}")
    word.run(None, Args(new Reporter { def apply(event: Event): Unit = () })).waitUntilCompleted()
    println(s"executed:${Effects.hits}")
  }
}
