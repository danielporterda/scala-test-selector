package directivevalues

final class Calls extends Api {
  def active(): Int = get { Effects.note("inner"); 42 }
  def strict(): Int = strictGet { Effects.note("strict-inner"); 43 }
  def deferredGetter(): Int = deferredGet { Effects.note("deferred-inner"); 44 }
  def constructed(): (=> Int) => Int = convert(get)
  def dormant(): () => Int = () => get { Effects.note("dormant-inner"); 45 }
}
