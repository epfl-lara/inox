/* Copyright 2009-2018 EPFL, Lausanne */

package inox.utils

/** An immutable value that [[push]] saves and [[pop]] restores.
  *
  * Unlike the incremental collections, which copy their contents on each push, it keeps the saved
  * values as they are, since nothing can change them. A state that is one such value is restored
  * by a pop as a whole, whatever changed it since the push. */
final class Snapshots[S](initial: S) extends IncrementalState {
  private var saved: List[S] = Nil
  private var current: S = initial

  def get: S = current
  def update(f: S => S): Unit = current = f(current)

  def push(): Unit = saved ::= current

  def pop(): Unit = {
    current = saved.head
    saved = saved.tail
  }

  def clear(): Unit = {
    current = initial
    saved = Nil
  }

  def reset(): Unit = clear()
}
