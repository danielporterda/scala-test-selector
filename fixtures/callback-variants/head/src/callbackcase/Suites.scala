package callbackcase
// JVM validation exercises Suite construction; zero registered test bodies.
final class Lexical1Suite extends org.scalatest.Suite { val observed: Int = Shared.run(() => 1) }
final class Lexical2Suite extends org.scalatest.Suite { val observed: Int = Shared.run(() => 2) }
final class Lexical3Suite extends org.scalatest.Suite { val observed: Int = Shared.run(() => 3) }
final class Lexical4Suite extends org.scalatest.Suite { val observed: Int = Shared.run(() => 4) }
final class Lexical5Suite extends org.scalatest.Suite { val observed: Int = Shared.run(() => 5) }
final class Lexical6Suite extends org.scalatest.Suite { val observed: Int = Shared.run(() => Changed.value()) }
final class Captured1Suite extends org.scalatest.Suite { val observed: Int = Shared.run(Shared.captured(() => 10)) }
final class Captured2Suite extends org.scalatest.Suite { val observed: Int = Shared.run(Shared.captured(() => 20)) }
final class Captured3Suite extends org.scalatest.Suite { val observed: Int = Shared.run(Shared.captured(() => 30)) }
final class Captured4Suite extends org.scalatest.Suite { val observed: Int = Shared.run(Shared.captured(() => 40)) }
final class Captured5Suite extends org.scalatest.Suite { val observed: Int = Shared.run(Shared.captured(() => 50)) }
final class Captured6Suite extends org.scalatest.Suite { val observed: Int = Shared.run(Shared.captured(() => Changed.value())) }
final class UnknownSuite extends org.scalatest.Suite { val observed: Int = Shared.run(Opaque.callback()) }
