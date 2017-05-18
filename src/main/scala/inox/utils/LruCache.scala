/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package utils

class LruCache[A,B](val maxSize: Int) {
  private[this] val cache = new java.util.LinkedHashMap[A,B] {
    override protected def removeEldestEntry(eldest: java.util.Map.Entry[A,B]): Boolean = super.size() > maxSize
  }

  def get(key: A): Option[B] = Option(cache.get(key))

  def cached(key: A, body: => B): B = get(key) match {
    case Some(res) => res
    case None =>
      val res = body
      cache.put(key, res)
      res
  }

  def clear(): Unit = cache.clear()
}
