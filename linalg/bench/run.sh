#!/bin/sh
# Build and run the linalg layout + precision benchmarks.
# Usage: ./run.sh
set -e
cd "$(dirname "$0")"
BEND="${BEND:-bend}"
mkdir -p out

for f in gram_list_f32 gram_array_f32 chol_array_f32 chol_array_f64 chol_list_f32 qr_array_f32; do
  "$BEND" "$f.bend" -o "out/$f"
done

one="+RTS --threads 1 -RTS"
echo "=== Bend benchmarks (N=1000, K=50) ==="
echo "gram list f32 1t   $(out/gram_list_f32 1000 50 0 $one | tail -1)"
echo "gram list f32 8t   $(out/gram_list_f32 1000 50 3 | tail -1)"
echo "gram array f32 1t  $(out/gram_array_f32 1000 50 $one | tail -1)"
echo "chol list f32 1t   $(out/chol_list_f32 50 500 $one | tail -1)"
echo "chol array f32 1t  $(out/chol_array_f32 50 500 6 $one | tail -1)"
echo "chol array f64 1t  $(out/chol_array_f64 50 5 6 $one | tail -1)"
echo "qr array f32 1t    $(out/qr_array_f32 1000 50 $one | tail -1)"
echo ""
python3 precision.py
