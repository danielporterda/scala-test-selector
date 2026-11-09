package selectedexternal

object CheckSelectedApply {
  def main(args: Array[String]): Unit = {
    val calls = new Calls
    Effects.reset()
    args(0) match {
      case "inherited" => val result = calls.inherited(); println("inherited:" + Effects.trace + ":" + result.timeout.value + ":" + result.interval.value)
      case "qualified" => calls.qualified(); println("qualified:" + Effects.trace)
      case "positional" => calls.positional(); println("positional:" + Effects.trace)
      case "overloaded" => calls.overloaded(); println("overloaded:" + Effects.trace)
      case "eta" => val callback = calls.eta(); println("eta-created:" + Effects.trace); callback(); println("eta-invoked:" + Effects.trace)
      case "returned" => val callback = calls.returned(); println("returned-created:" + Effects.trace); callback(new Span(3)); println("returned-invoked:" + Effects.trace)
      case "applied-returned" => calls.appliedReturned(); println("applied-returned:" + Effects.trace)
      case "dormant" => calls.dormant(); println("dormant:" + Effects.trace)
    }
  }
}
