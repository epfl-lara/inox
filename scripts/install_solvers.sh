#!/usr/bin/env sh

if [ "$INSTALL_SOLVERS" != "1" ]; then
  echo "Skipping solver installation"
  exit 0
fi

INFO_MSG="[INFO]"
WARN_MSG="\033[33m[WARNING]\033[0m"
ERROR_MSG="\033[1;31m[ERROR]\033[0m"

# curl command with default flags
CURL='curl -L -s -C -'

TEMP_DIR="$(pwd)/temp"
SOLVERS_DIR=${1:-"$(pwd)/solvers"}

# check for set version or default to known working (for script) versions
Z3_VER=${2:-"4.15.1"}
CVC4_VER=${3:-"1.8"}
CVC5_VER=${4:-"1.2.1"}
BITWUZLA_VER=${5:-"0.8.2"}

ARCH=$(uname -m)
# short arch name as used by z3 builds
SHORT_ARCH=$(uname -m | sed 's/x86_64/x64/;s/aarch64/arm64/;')

# libc linked against z3
# (glibc for Linux, osx for macOS)
Z3_LIBC_NAME=$(uname -s | tr '[:upper:]' '[:lower:]' | sed 's/darwin/osx/;s/linux/glibc/;')

# os names as used by CVC5 builds
CVC5_OS_NAME=$(uname -s | tr '[:upper:]' '[:lower:]' | sed 's/darwin/macOS/;s/linux/Linux/;')

mkdir -p "$SOLVERS_DIR"
mkdir -p "$TEMP_DIR"

reset_temp_dir() {
  rm -rf "$TEMP_DIR"
  mkdir -p "$TEMP_DIR"
}

echo "$INFO_MSG Installing Solvers to $SOLVERS_DIR"

# cvc5
echo "$INFO_MSG Installing cvc5 (v${CVC5_VER})"

$CURL "https://github.com/cvc5/cvc5/releases/download/cvc5-${CVC5_VER}/cvc5-${CVC5_OS_NAME}-${ARCH}-static.zip" --output "$TEMP_DIR/cvc5.zip"
unzip -q "$TEMP_DIR/cvc5.zip" -d "$TEMP_DIR" 
CVC5_DIR=$(find "$TEMP_DIR" -mindepth 1 -maxdepth 1 -type d -name "*cvc5*")
mv "$CVC5_DIR/bin/cvc5" "$SOLVERS_DIR/cvc5"
chmod +x "$SOLVERS_DIR/cvc5"

reset_temp_dir

# CVC4
echo "$INFO_MSG Installing CVC4 (v${CVC4_VER})"

if [ "$CVC5_OS_NAME" = "macOS" ]; then
  echo "$WARN_MSG CVC4 installation on macOS; defaulting to only build available (x86_64 v1.8)"
  $CURL "https://github.com/CVC4/CVC4-archived/releases/download/1.8/cvc4-1.8-macos-opt" --output "$SOLVERS_DIR/cvc4"
elif [ "$CVC5_OS_NAME" = "Linux" ]; then
  $CURL "https://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-${CVC4_VER}-x86_64-linux-opt" --output "$SOLVERS_DIR/cvc4"
else
  echo "$ERROR_MSG CVC4 installation not supported on unknown OS: $CVC5_OS_NAME"
  exit 1
fi
chmod +x "$SOLVERS_DIR/cvc4"

reset_temp_dir

# z3
echo "$INFO_MSG Installing Z3 (v${Z3_VER})"

# z3 release file names contain libc versions in them, which makes them hard to
# guess. Just get the correct one via the GitHub release API.
Z3_FILE_PREFIX="z3-${Z3_VER}-${SHORT_ARCH}-${Z3_LIBC_NAME}" # followed by -<libcversion>.zip
Z3_URL=$(
  $CURL "https://api.github.com/repos/Z3Prover/z3/releases/tags/z3-${Z3_VER}" | # get release info
  grep "browser_download_url.*${Z3_FILE_PREFIX}" | # find url for the correct build
  sed 's/^.*: //;s/^"//;s/"$//' # strip non-url
)
$CURL "${Z3_URL}" --output "$TEMP_DIR/z3.zip"
unzip -q "$TEMP_DIR/z3.zip" -d "$TEMP_DIR" 
Z3_DIR=$(find "$TEMP_DIR" -mindepth 1 -maxdepth 1 -type d -name "*z3*")
mv "$Z3_DIR/bin/z3" "$SOLVERS_DIR/z3"
chmod +x "$SOLVERS_DIR/z3"
rm -rf "$TEMP_DIR"

# Bitwuzla
echo "$INFO_MSG Installing Bitwuzla (v${BITWUZLA_VER})"

mkdir -p "$TEMP_DIR"
$CURL -L https://github.com/bitwuzla/bitwuzla/releases/download/${BITWUZLA_VER}/Bitwuzla-Linux-x86_64-static.zip --output "$TEMP_DIR/bitwuzla.zip"
unzip -q "$TEMP_DIR/bitwuzla.zip" -d "$TEMP_DIR" 
BITWUZLA_DIR=$(find "$TEMP_DIR" -mindepth 1 -maxdepth 1 -type d -name "*Bitwuzla*")
mv "$BITWUZLA_DIR/bin/bitwuzla" "$SOLVERS_DIR/bitwuzla"
chmod +x "$SOLVERS_DIR/bitwuzla"
rm -rf "$TEMP_DIR"

echo "$INFO_MSG Solvers Installed"
exit 0
