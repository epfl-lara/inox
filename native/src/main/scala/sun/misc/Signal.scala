package sun.misc

// Scala Native has no sun.misc.Signal. Inox only uses it to turn Ctrl-C into
// a solver interrupt; without it, Ctrl-C terminates the process directly.

final class Signal(val name: String)

trait SignalHandler {
  def handle(sig: Signal): Unit
}

object Signal {
  def handle(sig: Signal, handler: SignalHandler): SignalHandler = null
}
