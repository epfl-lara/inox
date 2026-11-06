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
# Needs GraalVM 25 or later (native-image and java on the PATH, or
# GRAALVM_HOME set), sbt, and z3 on the PATH.
#
# The build uses the options in
# src/main/resources/META-INF/native-image/ch.epfl.lara/inox and the
# reflection, JNI and resource accesses that
# scripts/record-native-image-metadata.sh records into
# target/native-image-metadata. Set INOX_NATIVE_METADATA to a directory
# holding an earlier recording to skip recording.
set -euo pipefail
cd "$(dirname "$0")/.."

out=${1:-inox-native-image}
shift || true
native_image=native-image
jar_tool=jar
if [ -n "${GRAALVM_HOME:-}" ]; then
  native_image="$GRAALVM_HOME/bin/native-image"
  jar_tool="$GRAALVM_HOME/bin/jar"
fi

if [ -n "${INOX_NATIVE_METADATA:-}" ]; then
  metadata=$INOX_NATIVE_METADATA
  sbt -batch assembly
else
  metadata=target/native-image-metadata
  ./scripts/record-native-image-metadata.sh "$metadata"
fi
jar=$(ls -t target/scala-*/inox-assembly-*.jar | head -n 1)

# native-image reads the metadata from the jar, next to native-image.properties.
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/META-INF/native-image/ch.epfl.lara/inox"
cp "$metadata/reachability-metadata.json" "$work/META-INF/native-image/ch.epfl.lara/inox/"
cp "$jar" "$work/inox.jar"
"$jar_tool" uf "$work/inox.jar" -C "$work" META-INF/native-image/ch.epfl.lara/inox/reachability-metadata.json

"$native_image" -jar "$work/inox.jar" -o "$out" -march=compatibility "$@"
