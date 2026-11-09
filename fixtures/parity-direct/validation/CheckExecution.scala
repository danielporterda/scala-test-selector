package executioncase
object CheckExecution {
  def main(args: Array[String]): Unit = {
    val affected = new AffectedSuite
    val unaffected = new UnaffectedSuite
    val dormant = new DormantSuite
    if (affected.observed != args(0).toInt || unaffected.observed != 7 || dormant.observed != 7)
      throw new AssertionError("independent execution mismatch")
    println("observed:" + affected.observed + "," + unaffected.observed + "," + dormant.observed)
    println("suite:" + affected.getClass.getName)
    println("suite:" + unaffected.getClass.getName)
    println("suite:" + dormant.getClass.getName)
  }
}
