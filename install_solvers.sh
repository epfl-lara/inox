TEMP_DIR="temp"
SOLVERS_DIR="$1"

mkdir -p "$SOLVERS_DIR"
mkdir -p "$TEMP_DIR"
# cvc5
wget https://github.com/cvc5/cvc5/releases/download/cvc5-1.1.2/cvc5-Linux-static.zip -O "$TEMP_DIR/downloaded.zip" -q
unzip "$TEMP_DIR/downloaded.zip" -d "$TEMP_DIR" 
CVC5_DIR=$(ls "$TEMP_DIR" | grep cvc5)
mv "$TEMP_DIR/$CVC5_DIR/bin/cvc5" "$SOLVERS_DIR/cvc5"
chmod +x "$SOLVERS_DIR/cvc5"
rm -rf "$TEMP_DIR"

# CVC4
wget https://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.8-x86_64-linux-opt -O "$SOLVERS_DIR/cvc4" -q
chmod +x "$SOLVERS_DIR/cvc4"

# z3
mkdir -p "$TEMP_DIR"
wget https://github.com/Z3Prover/z3/releases/download/z3-4.13.0/z3-4.13.0-x64-glibc-2.35.zip -O "$TEMP_DIR/downloaded.zip" -q
unzip "$TEMP_DIR/downloaded.zip" -d "$TEMP_DIR" 
Z3_DIR=$(ls "$TEMP_DIR" | grep z3)
mv "$TEMP_DIR/$Z3_DIR/bin/z3" "$SOLVERS_DIR/z3"
chmod +x "$SOLVERS_DIR/z3"
rm -rf "$TEMP_DIR"

echo "************** Solvers Installed **************"
exit 0