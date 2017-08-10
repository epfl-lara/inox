package inox

object Bench {
  val start = System.nanoTime

  object DebugSectionBench extends inox.DebugSection("bench")

  implicit val debugSection = DebugSectionBench

  var times: Map[String,Double] = Map()
  var mintimes: Map[String,Double] = Map()
  var maxtimes: Map[String,Double] = Map()
  var counts: Map[String,Int] = Map()
  
  def time[R](s: String, block: => R): R = {
    val t0 = System.nanoTime
    val result = block    // call-by-name
    val t1 = System.nanoTime
    Bench.synchronized {
      mintimes = mintimes.updated(s,Math.min(mintimes.getOrElse(s,Double.MaxValue),t1 - t0))
      maxtimes = maxtimes.updated(s,Math.max(maxtimes.getOrElse(s,0.0),t1 - t0))
      times = times.updated(s,times.getOrElse(s,0.0) + t1 - t0)
      counts = counts.updated(s,counts.getOrElse(s,0) + 1)
    }
    result
  }
  
  def reportS(ctx: inox.Context) = {
    if (!times.isEmpty) {
      val maxsize = times.map(_._1.size).max
      ctx.reporter.synchronized {
        ctx.reporter.debug("====== REPORT ======")
        for ((s,t) <- times.toList.sortBy(_._2)) {
          ctx.reporter.debug("== %s: %.2fs\t%.2fs\t%.2fs\t%s".format(
            s.padTo(maxsize,' '),
            t/1000000000.0,
            mintimes.getOrElse(s,0.0)/1000000000.0,
            maxtimes.getOrElse(s,0.0)/1000000000.0,
            counts.getOrElse(s,0.0)
          ))
        }
        ctx.reporter.debug("Total time: " + (System.nanoTime - start)/1000000000.0)
        ctx.reporter.debug("====================")
      }
    }
  }
}
