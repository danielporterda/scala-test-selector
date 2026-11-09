package contextboundcase
object CheckArguments {
  def main(args: Array[String]): Unit = {
    args(0) match {
      case "omitted" | "explicit" | "named" | "evidence" | "never" =>
        val f = args(0) match {
          case "explicit" => Calls.explicitCondition()
          case "named" => Calls.namedArguments()
          case "evidence" => Calls.explicitEvidence()
          case _ => Calls.omitted()
        }
        println("created:" + Effects.defaults + ":" + Effects.renders + ":" + Effects.evidence)
        if (args(0) != "never") {
          val result = f(new Item(5))
          println("invoked:" + result + ":" + Effects.defaults + ":" + Effects.renders + ":" + Effects.evidence)
        }
      case "immediate" =>
        val result = Calls.immediatelyApplied()
        println("immediate:" + result + ":" + Effects.defaults + ":" + Effects.renders + ":" + Effects.evidence)
      case "lambda-named" | "lambda-placeholder" =>
        val result = if (args(0) == "lambda-named") Calls.renderedNamed() else Calls.renderedPlaceholder()
        println(args(0) + ":" + result + ":" + Effects.defaults + ":" + Effects.renders + ":" + Effects.evidence)
    }
  }
}
