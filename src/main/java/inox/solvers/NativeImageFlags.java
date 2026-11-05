/* Copyright 2009-2026 EPFL, Lausanne */

package inox.solvers;

/** Build-time switches for the GraalVM native image (see
  * scripts/build-native-image.sh). The image initializes this class at build
  * time, so these fields are constants there and the solver back ends they
  * turn off are left out of the image entirely. On the JVM they read the
  * same system properties, which are normally unset.
  */
public final class NativeImageFlags {
  private NativeImageFlags() {}

  /** Whether the Princess back end is available (-Dinox.withoutPrincess=true turns it off). */
  public static final boolean WITH_PRINCESS = !Boolean.getBoolean("inox.withoutPrincess");

  /** Whether the Eldarica back end is available (-Dinox.withoutEldarica=true turns it off). */
  public static final boolean WITH_ELDARICA = !Boolean.getBoolean("inox.withoutEldarica");
}
