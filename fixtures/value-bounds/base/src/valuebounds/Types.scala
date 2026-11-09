package valuebounds
trait Base { def work(): Int }
trait Marker
abstract class Narrow extends Base
final class Allowed extends Narrow with Marker { override def work(): Int = Effects.affected() }
final class Sibling extends Base { override def work(): Int = Effects.outsider() }
final class NoMarker extends Narrow { override def work(): Int = Effects.unmarked() }
