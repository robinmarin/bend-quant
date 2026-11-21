#!/bin/sh
# Build every benchmark into out/, then time rank IC on a T x N panel.
# Usage: ./run.sh [T] [N]   (default 5000 1000)
set -e
cd "$(dirname "$0")"
T=${1:-5000}; N=${2:-1000}
mkdir -p out
for f in list_f32 list_f64 list_f32_par list_f64_par array_f32 access; do bend $f.bend -o out/$f; done
clang -O2 -o out/array_f32_c array_f32.c -lm
one="+RTS --threads 1 -RTS"
echo "T=$T N=$N"
echo "numpy f32       $(python3 ref.py $T $N | tail -1)"
echo "numpy f64       $(python3 ref.py $T $N 64 | tail -1)"
echo "C heapsort      $(out/array_f32_c $T $N)"
echo "list f32 1t     $(out/list_f32 $T $N $one | tail -1)"
echo "list f64 1t     $(out/list_f64 $T $N $one | tail -1)"
echo "array f32 1t    $(out/array_f32 $T $N 0 $one | tail -1)"
echo "list f32 par    $(out/list_f32_par $T $N | tail -1)"
echo "list f64 par    $(out/list_f64_par $T $N | tail -1)"
echo "array f32 par   $(out/array_f32 $T $N 5 | tail -1)"
echo "access          $(out/access | tail -1)"
