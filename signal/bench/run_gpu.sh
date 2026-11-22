#!/bin/sh
# Build and run the GPU (!-dispatched) benchmarks, comparing GPU against CPU (+RTS --gpu off -RTS).
# Requires bend 2.0.40 and clang 19+ (Apple clang 17+ on macOS) for GPU builds.
# Usage: ./run_gpu.sh
set -e
cd "$(dirname "$0")"
mkdir -p out
bend array_f32_gpu.bend -o out/array_f32_gpu
bend mc_gpu.bend -o out/mc_gpu

cpu="+RTS --gpu off -RTS"

echo "=== Rank IC (Array<F32> heapsort, N=1000) ==="
for T in 5000 16384; do
  echo "--- T=$T N=1000 ---"
  echo "CPU (D=6)  $(out/array_f32_gpu $T 1000 6 $cpu | tr '\n' ' ')"
  for D in 10 12 13 14; do
    echo "GPU (D=$D) $(out/array_f32_gpu $T 1000 $D | tr '\n' ' ')"
  done
done

echo ""
echo "=== Monte Carlo GBM (252 daily steps) ==="
for P in 16384 131072 1048576; do
  echo "--- PATHS=$P STEPS=252 ---"
  echo "CPU (D=6)  $(out/mc_gpu $P 252 6 $cpu | tr '\n' ' ')"
  for D in 10 12 14; do
    echo "GPU (D=$D) $(out/mc_gpu $P 252 $D | tr '\n' ' ')"
  done
done
