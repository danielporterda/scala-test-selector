package annotationcase
class AffectedSuite extends org.scalatest.Suite { val observed: Int = new Service().value() }
