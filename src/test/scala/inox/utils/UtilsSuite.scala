/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package utils

import org.scalatest.funsuite.AnyFunSuite

import java.io.File

class UtilsSuite extends AnyFunSuite {

  test("fixpoint computes correct fixpoint of function that increments up to a max") {
    def f(x: Int): Int = if(x < 10) x + 1 else 10
    assert(f(10) === 10)
    assert(fixpoint(f)(1) === 10)
  }

  test("fixpoint computes correct fixpoint with a large limit") {
    def f(x: Int): Int = if(x < 100) x + 1 else 100
    assert(f(100) === 100)
    assert(fixpoint(f)(-1) === 100)
  }

  test("fixpoint finds the fixpoint in small number of iteration") {
    def f(x: Int): Int = if(x < 10) x + 1 else 10
    assert(f(10) === 10)
    assert(fixpoint(f, 15)(1) === 10)
  }

  test("fixpoint of id is the starting expression") {
    def id(x: Int): Int = x
    assert(fixpoint(id)(1) === 1)
    assert(fixpoint(id)(42) === 42)
  }

  private def counting(n: Int, freed: Array[Boolean]) = new FreeableIterator[Int] {
    private var i = 0
    def computeNext() = if (i < n) { i += 1; Some(i) } else None
    def free() = freed(0) = true
  }

  test("freeable iterators") {
    val freed = Array(false)
    assert(counting(3, freed).toList == List(1, 2, 3))
    assert(freed(0))

    val freed2 = Array(false)
    assert(counting(5, freed2).map(_ * 10).take(2).toList == List(10, 20))
    assert(freed2(0))

    val freed3 = Array(false)
    assert(counting(5, freed3).takeWhile(_ < 3).toList == List(1, 2))
    assert(freed3(0))

    assert(FreeableIterator.empty[Int].toList == Nil)
  }

  test("hexadecimal digits") {
    assert((0 to 15).map(StringUtils.toHex).mkString == "0123456789ABCDEF")
    assert("0123456789ABCDEF".map(StringUtils.fromHex) == (0 to 15))
    assert("abcdef".map(StringUtils.fromHex) == (10 to 15))
  }

  test("string literal escapes") {
    assert(StringUtils.decode("a\\u{}b") == "a\\u{}b".map(_.toInt))
    assert(StringUtils.decode("a\\u{41") == "a\\u{41".map(_.toInt))
    assert(StringUtils.decode("\\u0041\\u{42}") == Seq('A'.toInt, 'B'.toInt))
    assert(StringUtils.decode("\\u00") == "\\u00".map(_.toInt))
    assert(StringUtils.decode(StringUtils.encode(Seq(0x1F600, '\\'.toInt, 'a'.toInt))) == Seq(0x1F600, '\\'.toInt, 'a'.toInt))
  }

  test("positions") {
    val f1 = new File("a.scala")
    val f2 = new File("b.scala")
    val p1 = OffsetPosition(1, 2, 10, f1)
    val p2 = OffsetPosition(1, 5, 13, f1)
    val p3 = OffsetPosition(3, 1, 30, f1)
    val q1 = OffsetPosition(1, 1, 1, f2)

    assert(p1 < p2 && p2 < p3)
    assert(p1 < q1 && q1 > p3)
    assert(NoPosition < p1)
    assert(p1 > NoPosition)
    assert(NoPosition.compare(NoPosition) == 0)

    assert(p1.toString == "1:2")
    assert(p1.fullString == "a.scala:1:2")
    assert(p1.isDefined)
    assert(p1.focusBegin == p1 && p1.focusEnd == p1)
    assert(NoPosition.toString == "?:?")
    assert(NoPosition.fullString == "?:?:?")
    assert(!NoPosition.isDefined)

    val r = Position.between(p3, p1)
    assert(r == RangePosition(1, 2, 10, 3, 1, 30, f1))
    val rp = r.asInstanceOf[RangePosition]
    assert(rp.focusBegin == p1 && rp.focusEnd == p3)
    assert(rp.line == 1 && rp.col == 2)
    assert(Position.between(p1, p1) == p1)
    assert(Position.between(p1, q1) == p1)
    assert(Position.between(r, OffsetPosition(5, 1, 50, f1)) == RangePosition(1, 2, 10, 5, 1, 50, f1))
    assert(Position.between(OffsetPosition(0, 1, 0, f1), r) == RangePosition(0, 1, 0, 3, 1, 30, f1))
    assert(Position.between(r, RangePosition(4, 1, 40, 6, 1, 60, f1)) == RangePosition(1, 2, 10, 6, 1, 60, f1))

    assert(Position.smartPos(NoPosition) == "")
    assert(Position.smartPos(p1).endsWith("a.scala:1:2: "))
  }

  test("bijections") {
    val b = Bijection(1 -> "a", 2 -> "b")
    assert(b.fromA(1) == "a" && b.fromB("b") == 2)
    assert(b.containsA(1) && !b.containsA(3))
    assert(b.containsB("a") && !b.containsB("c"))
    assert(b.aSet == Set(1, 2) && b.bSet == Set("a", "b"))
    val ca = b.composeA(_ * 10)
    assert(ca.toB(10) == "a" && ca.toA("b") == 20)
    val cb = b.composeB(_.toUpperCase)
    assert(cb.toB(1) == "A" && cb.toA("B") == 2)
    assert(Bijection(Seq(1 -> "x")).toB(1) == "x")
  }

  test("search spaces") {
    val succ = (i: Int) => if (i < 5) Set(i + 1, i + 2) else Set.empty[Int]
    assert(SearchSpace.reachable(Set(0), succ) == ((0 to 6).toSet, true))
    val (seen, complete) = SearchSpace.reachable(Set(0), succ, Some(2))
    assert(seen.size == 2 && !complete)
    assert(SearchSpace.reachable(Set.empty[Int], succ, Some(0)) == ((Set.empty[Int], true)))
  }

  test("caches") {
    val lru = new LruCache[Int, String](2)
    lru(1) = "a"
    lru(2) = "b"
    assert(lru.get(1) == Some("a"))
    lru(3) = "c" // evicts 2, the least recently used
    assert(lru.get(2).isEmpty && lru.get(1) == Some("a") && lru.get(3) == Some("c"))
    assert(lru.cached(4, "d") == "d" && lru.cached(4, "e") == "d")
    lru.clear()
    assert(lru.get(4).isEmpty)

    val pc = new PriorityCache[Int, String](2)
    pc(5) = "e"
    pc(3) = "c"
    pc(4) = "d" // evicts the smallest key
    assert(pc.get(3).isEmpty && pc.get(4) == Some("d") && pc.get(5) == Some("e"))
    pc.clear()
    assert(pc.get(5).isEmpty)
  }

  test("interrupt manager") {
    val reporter = new TestSilentReporter
    val im = new InterruptManager(reporter)
    var count = 0
    val i1 = new Interruptible { def interrupt(): Unit = count += 1 }
    im.registerForInterrupts(i1)
    assert(!im.isInterrupted)
    im.interrupt()
    assert(im.isInterrupted && count == 1)
    im.interrupt()
    assert(count == 1)
    assert(reporter.lastErrors.isEmpty)
    val i2 = new Interruptible { def interrupt(): Unit = count += 10 }
    im.registerForInterrupts(i2)
    assert(count == 11)
    im.reset()
    assert(!im.isInterrupted)
    im.reset()
    im.unregisterForInterrupts(i1)
    im.unregisterForInterrupts(i2)
    im.interrupt()
    assert(count == 11)
  }

  test("timers") {
    val t = new Timer
    assert(!t.isRunning && !t.isStopped)
    t.start()
    assert(t.isRunning)
    t.stop()
    assert(t.isStopped)

    val ts = TimerStorage("root")
    assert(ts.run(42) == 42)
    ts.a.run(1)
    ts.a.run(2)
    ts.b.c.run(3)
    assert(ts.get("a") eq ts.a)
    val (_, res) = ts.d.runAndGetTime(throw new Exception("boom"))
    assert(res.isFailure)
    val out = new StringBuilder
    ts.outputTable(out ++= _, asciiOnly = true)
    val table = out.toString
    assert(table.contains("Timers"))
    for (name <- Seq("root", "a", "b", "c", "d")) assert(table.contains(name))
    // Timers that ran once only report their total time
    assert(!table.contains("local"))
  }
}
