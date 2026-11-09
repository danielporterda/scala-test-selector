package valuebounds
object Cases {
  def exact(): Int = { val value: Base = new Allowed(); value.work() }
  def wider(): Int = Factories.known().work()
  def narrowed(): Int = Factories.narrow().work()
  def alias(): Int = Factories.alias().work()
  def generic(): Int = Factories.generic[Narrow]().work()
  def intersection(): Int = Factories.intersection().work()
  def mixed(flag: Boolean): Int = { val value: Base = if (flag) new Allowed() else Factories.broad(); value.work() }
  def branches(flag: Boolean): Int = { val value: Base = if (flag) new Allowed() else new Sibling(); value.work() }
}
