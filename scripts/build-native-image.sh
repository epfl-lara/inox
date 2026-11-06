#!/usr/bin/env bash
# Builds a GraalVM native image of the inox command line, which starts in
# tens of milliseconds instead of about a second for the JVM. It includes the
# SMT-LIB back ends and the Z3 native interface, but not Princess and
# Eldarica (see native-image.properties).
#
# Usage: scripts/build-native-image.sh [output [native-image options...]]
#   output defaults to ./inox-native-image; e.g. pass -Ob for a quicker,
#   less optimized build.
#
# Needs GraalVM 25 or later: native-image on the PATH, or GRAALVM_HOME set.
# The build uses the configuration in
# src/main/resources/META-INF/native-image/ch.epfl.lara/inox. With
# --exact-reachability-metadata, the image fails with an error when it
# reaches a class, member or resource by name that reachability-metadata.json
# doesn't list, instead of behaving as if it didn't exist, so that
# scripts/check-native-binary.sh catches it in CI.
set -euo pipefail
cd "$(dirname "$0")/.."

out=${1:-inox-native-image}
shift || true
native_image=native-image
if [ -n "${GRAALVM_HOME:-}" ]; then native_image="$GRAALVM_HOME/bin/native-image"; fi

sbt -batch assembly
jar=$(ls -t target/scala-*/inox-assembly-*.jar | head -n 1)
"$native_image" -jar "$jar" -o "$out" -march=compatibility --exact-reachability-metadata "$@"
