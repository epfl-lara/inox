/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package utils

trait Cache[A,B] {
  def get(key: A): Option[B]
  def update(key: A, value: B): Unit
  def clear(): Unit

  def cached(key: A, body: => B): B = get(key) match {
    case Some(res) => res
    case None =>
      val res = body
      update(key, res)
      res
  }
}

class LruCache[A,B](val maxSize: Int) extends Cache[A,B] {
  // see java.util.HashMap doc for a discussion about load factors (0.75 here)
  private[this] val cache = new java.util.LinkedHashMap[A,B](maxSize + 1, 0.75f, true) {
    override protected def removeEldestEntry(eldest: java.util.Map.Entry[A,B]): Boolean = super.size() > maxSize
  }

  def get(key: A): Option[B] = Option(cache.get(key))
  def update(key: A, value: B): Unit = cache.put(key, value)
  def clear(): Unit = cache.clear()
}

class PriorityCache[A,B](val maxSize: Int)(implicit val ordering: Ordering[A]) extends Cache[A,B] {
  private[this] val cache = new java.util.HashMap[A,B](maxSize + 1)
  private[this] val queue = new java.util.PriorityQueue(maxSize, ordering)

  def get(key: A): Option[B] = Option(cache.get(key))

  def update(key: A, value: B): Unit = {
    cache.put(key, value)
    queue.add(key)
    if (cache.size > maxSize) {
      cache.remove(queue.poll())
    }
  }

  def clear(): Unit = {
    cache.clear()
    queue.clear()
  }
}
