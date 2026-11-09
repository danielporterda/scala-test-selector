package externalprefix

object CheckPrefix {
  def main(args: Array[String]): Unit = {
    val calls = new Calls
    Native.reset()
    args(0) match {
      case "string" => val value = calls.stringConstructor(); println("string:" + Native.trace + ":" + value.value)
      case "int" => val value = calls.intConstructor(); println("int:" + Native.trace + ":" + value.value)
      case "dormant" =>
        val function = calls.dormantConstructor()
        println("dormant-created:" + Native.trace)
        val value = function()
        println("dormant-invoked:" + Native.trace + ":" + value.value)
      case "class" => calls.classLiteral(); println("class:" + Native.trace)
      case "chain" => val value = calls.chain(); println("chain:" + Native.trace + ":" + value)
      case "deferred-chain" =>
        val function = calls.dormantChain()
        println("chain-created:" + Native.trace)
        val value = function()
        println("chain-invoked:" + Native.trace + ":" + value)
      case "eta" =>
        val function = calls.eta()
        println("eta-created:" + Native.trace)
        val value = function(8)
        println("eta-invoked:" + Native.trace + ":" + value)
    }
  }
}
