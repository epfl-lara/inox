#!/usr/bin/env sh

if [ "$INSTALL_SOLVERS" != "1" ]; then
  echo "Skipping solver installation"
  exit 0
fi

TEMP_DIR="$(pwd)/temp"
SOLVERS_DIR=${1:-"$(pwd)/solvers"}

# check for set version or default to known working (for script) versions
Z3_VER=${2:-"4.15.1"}
CVC4_VER=${3:-"1.8"}
CVC5_VER=${4:-"1.2.1"}

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
# cvc5
wget -c "https://github.com/cvc5/cvc5/releases/download/cvc5-${CVC5_VER}/cvc5-${CVC5_OS_NAME}-${ARCH}-static.zip" -O "$TEMP_DIR/cvc5.zip" -q
unzip "$TEMP_DIR/cvc5.zip" -d "$TEMP_DIR" 
CVC5_DIR=$(find "$TEMP_DIR" -mindepth 1 -maxdepth 1 -type d -name "*cvc5*")
mv "$CVC5_DIR/bin/cvc5" "$SOLVERS_DIR/cvc5"
chmod +x "$SOLVERS_DIR/cvc5"
rm -rf "$TEMP_DIR"

# CVC4
if [ "$CVC5_OS_NAME" = "macOS" ]; then
  echo "[WARNING] CVC4 installation on macOS; defaulting to only build available (x86_64 v1.9 pre-release 25-09-2020)"
  wget -c "https://cvc4.cs.stanford.edu/downloads/builds/macos/25-09-20/cvc4" -O "$SOLVERS_DIR/cvc4" -q
elif [ "$CVC5_OS_NAME" = "Linux" ]; then
  wget -c "https://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-${CVC4_VER}-x86_64-linux-opt" -O "$SOLVERS_DIR/cvc4" -q
else
  echo "[ERROR] CVC4 installation not supported on unknown OS: $CVC5_OS_NAME"
  exit 1
fi
chmod +x "$SOLVERS_DIR/cvc4"

# z3
mkdir -p "$TEMP_DIR"
Z3_FILE_PREFIX="z3-${Z3_VER}-${SHORT_ARCH}-${Z3_LIBC_NAME}"
Z3_URL=$(
  curl -s "https://api.github.com/repos/Z3Prover/z3/releases/tags/z3-${Z3_VER}" | # get release info
  grep "browser_download_url.*${Z3_FILE_PREFIX}" | #| # find url for the correct build
  sed 's/^.*: //;s/^"//;s/"$//' # strip non-url
)
wget -c "${Z3_URL}" -O "$TEMP_DIR/z3.zip" -q
unzip "$TEMP_DIR/z3.zip" -d "$TEMP_DIR" 
Z3_DIR=$(find "$TEMP_DIR" -mindepth 1 -maxdepth 1 -type d -name "*z3*")
mv "$Z3_DIR/bin/z3" "$SOLVERS_DIR/z3"
chmod +x "$SOLVERS_DIR/z3"
rm -rf "$TEMP_DIR"

echo "************** Solvers Installed **************"
exit 0