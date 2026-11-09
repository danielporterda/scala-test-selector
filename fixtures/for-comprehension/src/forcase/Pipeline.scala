package forcase

import scala.concurrent.{ExecutionContext, Future}
import org.scalatest.Suite

object Effects {
  var events: Vector[String] = Vector.empty
  def note(value: String): Unit = { events = events :+ value }
}

trait Pipeline {
  implicit val context: ExecutionContext = ExecutionContext.parasitic

  def first(): Future[Int] = { Effects.note("first"); Future.successful(3) }
  def load(value: Int): Future[Int] = { Effects.note(s"load:$value"); Future.successful(value) }
  def check(value: Int): Unit = Effects.note(s"check:$value")
  def save(value: Int): Future[Unit] = { Effects.note(s"save:$value"); Future.successful(()) }
  def after(value: Int): Future[Unit] = { Effects.note(s"after:$value"); Future.successful(()) }
  def finish(): Future[Unit] = { Effects.note("finish"); Future.successful(()) }
  def clueF[A](label: String)(body: => Future[A]): Future[A] = {
    Effects.note(s"clue:$label")
    body
  }

  def execute(): Future[Unit] = for {
    seed <- first()
    _ <- clueF("guard")(for {
      item <- load(seed)
      _ = check(item)
      _ <- save(item)
      _ <- after(item)
    } yield ())
    _ <- finish()
  } yield ()

  def dormant(): Future[Unit] = clueF("dormant")(for {
    item <- load(99)
    _ = check(item)
    _ <- save(item)
    _ <- after(item)
  } yield ())
}

class ActiveSuite extends Suite with Pipeline {
  val completed: Future[Unit] = execute()
}

class DormantSuite extends Suite with Pipeline {
  val stored: () => Future[Unit] = () => dormant()
}
