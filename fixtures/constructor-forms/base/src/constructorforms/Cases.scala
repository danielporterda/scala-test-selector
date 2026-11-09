package constructorforms
class ApplyDefaultSuite extends org.scalatest.Suite { val observed: Int = Value().value }
class NewDefaultSuite extends org.scalatest.Suite { val observed: Int = new Value().value }
class ApplyExplicitSuite extends org.scalatest.Suite { val observed: Int = Value(7).value }
class CopyDefaultSuite extends org.scalatest.Suite { val observed: Int = Value(7).copy().value }
class CopyExplicitSuite extends org.scalatest.Suite { val observed: Int = Value(7).copy(Effects.changed()).value }
class SecondaryDefaultSuite extends org.scalatest.Suite { val observed: Int = new Secondary().observed }
class SecondaryExplicitSuite extends org.scalatest.Suite { val observed: Int = new Secondary(7).observed }
class NewExplicitSuite extends org.scalatest.Suite { val observed: Int = new Value(7).value }
class MethodDefaultSuite extends org.scalatest.Suite { val observed: Int = Defaults.run() }
class MethodExplicitSuite extends org.scalatest.Suite { val observed: Int = Defaults.run(7) }
class ByNameDefaultUsedSuite extends org.scalatest.Suite { val observed: Int = Defaults.force() }
class ByNameDefaultIgnoredSuite extends org.scalatest.Suite { val observed: Int = Defaults.ignore() }
class DependentDefaultSuite extends org.scalatest.Suite { val observed: Int = Defaults.dependent(Effects.changed())() }
