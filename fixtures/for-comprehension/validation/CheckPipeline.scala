package forcase

import scala.concurrent.Await
import scala.concurrent.duration.Duration

object CheckPipeline {
  def main(arguments: Array[String]): Unit = {
    Effects.events = Vector.empty
    val dormant = new DormantSuite()
    println(s"dormant-before:${Effects.events.size}")
    val active = new ActiveSuite()
    Await.result(active.completed, Duration.Inf)
    println(s"active:${Effects.events.mkString(",")}")
    Effects.events = Vector.empty
    Await.result(dormant.stored(), Duration.Inf)
    println(s"dormant-invoked:${Effects.events.mkString(",")}")
  }
}
