package valuebounds
object Check { def main(args: Array[String]): Unit = {
  val values = Seq(Cases.exact(),Cases.wider(),Cases.narrowed(),Cases.alias(),Cases.generic(),Cases.intersection(),Cases.mixed(true),Cases.mixed(false),Cases.branches(true),Cases.branches(false))
  assert(values == Seq(42,42,42,42,42,42,42,42,42,99))
  assert(Opaque.narrow().isInstanceOf[Allowed])
  assert(Opaque.intersection().isInstanceOf[Marker])
  println("observed:"+values.mkString(","))
} }
