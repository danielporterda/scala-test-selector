package executioncase

object CheckHeldout {
  def main(args: Array[String]): Unit = {
    val affected = new AffectedSuite
    val unrelated = new UnaffectedSuite
    val dormant = new DormantSuite
    val observed = List(affected.observed, unrelated.observed, dormant.observed)
    assert(observed == List(41, 9, 9))
    println("observed:" + observed.mkString(","))
    List(affected, unrelated, dormant).foreach(s => println("suite:" + s.getClass.getName))
  }
}
