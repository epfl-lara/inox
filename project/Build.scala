import sbt._
import Keys._
import RichURI._

object InoxBuild extends Build {

  override def buildLoaders = BuildLoader.resolve(svnResolver) :: Nil

  // Define the custom resolver which handles the 'svn' scheme with a username/password pair.
  def svnResolver(info: BuildLoader.ResolveInfo): Option[() => File] =
    if (info.uri.getScheme != "svn+credentials") None else {
      val uri = info.uri.withoutMarkerScheme
      val localCopy = Resolvers.uniqueSubdirectoryFor(uri, in = info.staging)
      val from = uri.copy(scheme = "svn").withoutFragment.toASCIIString
      val to = localCopy.getAbsolutePath

      sealed abstract class SVNInfo
      case class Username(user: String) extends SVNInfo
      case class Password(pass: String) extends SVNInfo
      case class Tag(tag: String) extends SVNInfo

      val fragment = uri.getFragment
      val splits = fragment.split("&").toSeq
      val infos = splits.map(s => s.split("=").toSeq match {
        case Seq("username", user) => Username(user)
        case Seq("password", pass) => Password(pass)
        case Seq(tag) => Tag(tag)
        case _ => sys.error("Unexpected fragment: " + fragment)
      })

      val username = infos.collect { case Username(user) => user } match {
        case Seq(user) => user
        case _ => sys.error("Invalid username specification for svn+credentials scheme.")
      }

      val password = infos.collect { case Password(pass) => pass } match {
        case Seq(pass) => pass
        case _ => sys.error("Invalid password specification for svn+credentials scheme.")
      }

      infos.collect { case Tag(tag) => tag } match {
        case Seq(tag) => Some(() => Resolvers.creates(localCopy) {
          Resolvers.run("svn", "checkout", "-q", "-r", tag, "--username", username, "--password", password, from, to)
        })
        case Seq() => Some(() => Resolvers.creates(localCopy) {
          Resolvers.run("svn", "checkout", "-q", "--username", username, "--password", password, from, to)
        })
        case _ => sys.error("Invalid tag specification for svn+credentials scheme.")
      }
    }
}
