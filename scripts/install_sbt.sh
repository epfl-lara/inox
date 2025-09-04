#!/usr/bin/env sh

CURL='curl -L -s -C - -O'

SBT_VER="$(grep 'sbt.version' project/build.properties | cut -d= -f2)"
if [ -z "$SBT_VER" ]; then
  echo "sbt.version not found in project/build.properties"
  exit 1
fi
$CURL https://github.com/sbt/sbt/releases/download/v${SBT_VER}/sbt-${SBT_VER}.tgz
tar xfz "sbt-${SBT_VER}.tgz"
