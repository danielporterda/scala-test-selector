package positioncase

import scala.language.experimental.macros
import scala.reflect.macros.blackbox

object UserMacros {
  def effect(): Int = macro implementation
  def implementation(c: blackbox.Context)(): c.Expr[Int] = {
    import c.universe._
    c.Expr[Int](q"{ _root_.positioncase.Effects.hits += 1; 99 }")
  }
}
