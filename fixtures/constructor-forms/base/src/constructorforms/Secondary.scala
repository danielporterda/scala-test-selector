package constructorforms
class Secondary(val observed: Int) { def this() = this(Effects.changed()) }
