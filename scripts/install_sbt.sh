#!/usr/bin/env sh

SBT_VER="$(grep 'sbt.version' project/build.properties | cut -d= -f2)"
if [ -z "$SBT_VER" ]; then
  echo "sbt.version not found in project/build.properties"
  exit 1
fi
wget -c https://github.com/sbt/sbt/releases/download/v${SBT_VER}/sbt-${SBT_VER}.tgz -q
tar xfz "sbt-${SBT_VER}.tgz"
