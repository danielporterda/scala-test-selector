package repeatedcallbacks

object CheckRepeated {
  def main(args: Array[String]): Unit = {
    val calls = new Calls
    Effects.reset()
    args(0) match {
      case "flat" => val result = calls.flat(); println("flat:" + Effects.trace + ":" + result)
      case "empty" => calls.empty(); println("empty-created:" + Effects.trace)
      case "spread" => val result = calls.spread(); println("spread:" + Effects.trace + ":" + result)
      case "mixed" => val result = calls.mixedCall(); println("mixed:" + Effects.trace + ":" + result)
      case "captured" =>
        val function = calls.captured()
        println("captured-created:" + Effects.trace)
        val result = function()
        println("captured-invoked:" + Effects.trace + ":" + result)
      case "dormant" =>
        val function = calls.dormant()
        println("dormant-created:" + Effects.trace)
        val result = function()
        println("dormant-invoked:" + Effects.trace + ":" + result)
    }
  }
}
