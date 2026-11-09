package directivevalues

object CheckDirective {
  def main(args: Array[String]): Unit = {
    val calls = new Calls
    Effects.reset()
    args(0) match {
      case "active" => val result = calls.active(); println("active:" + Effects.trace + ":" + result)
      case "strict" => val result = calls.strict(); println("strict:" + Effects.trace + ":" + result)
      case "deferred" => val result = calls.deferredGetter(); println("deferred:" + Effects.trace + ":" + result)
      case "constructed" =>
        val function = calls.constructed()
        println("created:" + Effects.trace)
        val result = function { Effects.note("supplied"); 46 }
        println("invoked:" + Effects.trace + ":" + result)
      case "dormant" =>
        val function = calls.dormant()
        println("dormant-created:" + Effects.trace)
        val result = function()
        println("dormant-invoked:" + Effects.trace + ":" + result)
    }
  }
}
