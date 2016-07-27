/* Copyright 2009-2016 EPFL, Lausanne */

package inox.utils

trait IncrementalStateWrapper extends IncrementalState {
  val incrementals: Seq[IncrementalState]

  def push(): Unit = incrementals.foreach(_.push())
  def pop(): Unit = incrementals.foreach(_.pop())

  def clear(): Unit = incrementals.foreach(_.clear())
  def reset(): Unit = incrementals.foreach(_.reset())
}
