#!/usr/bin/env bash
# Builds a GraalVM native image of the inox command line, which starts in
# tens of milliseconds instead of about a second for the JVM. All solver back
# ends work, including the Z3 native interface and Princess.
#
# Usage: scripts/build-native-image.sh [output]   (default: ./inox-native-image)
#
# Needs GraalVM 25 or later: native-image on the PATH, or GRAALVM_HOME set.
# The build uses the configuration in
# src/main/resources/META-INF/native-image/ch.epfl.lara/inox. When a change
# makes Inox reach new classes through reflection, JNI or resources, update
# it with scripts/record-native-image-metadata.sh (CI checks that it is
# complete for the TIP regression files).
set -euo pipefail
cd "$(dirname "$0")/.."

out=${1:-inox-native-image}
native_image=native-image
if [ -n "${GRAALVM_HOME:-}" ]; then native_image="$GRAALVM_HOME/bin/native-image"; fi

sbt -batch assembly
jar=$(ls -t target/scala-*/inox-assembly-*.jar | head -n 1)
"$native_image" -jar "$jar" -o "$out" -march=compatibility
