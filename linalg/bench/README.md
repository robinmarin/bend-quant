# linalg layout & precision benchmark

Measures matrix layout (`List` vs `Array`) and precision (`F32` vs soft-float `F64`, normal equations vs thin Householder QR) on the Paleologo quant workloads ($N = 1000$ assets, $K = 50$ factors) before locking `DESIGN.md`.

## Run

```sh
BEND=~/.bend/bin/bend ./run.sh
```

Needs `bend` 2.0.40, `python3` with `numpy` and `scipy`. Binaries go to `out/`, which git ignores.

## Programs

| file | what it measures |
|---|---|
| `gram_list_f32.bend` | $G = B^\top B$ ($1000 \times 50$) on `List<&2, List<&2, F32>>` (1t and 8t fork-join) |
| `gram_array_f32.bend` | $G = B^\top B$ ($1000 \times 50$) on flat `Array<F32>` (1t, upper triangle + mirror) |
| `chol_list_f32.bend` | $50 \times 50$ Cholesky on `List<&2, List<&2, F32>>` (500 reps) |
| `chol_array_f32.bend` | $50 \times 50$ Cholesky (500 reps) and cyclic Jacobi eigen on flat `Array<F32>` |
| `chol_array_f64.bend` | $50 \times 50$ Cholesky (5 reps) and cyclic Jacobi eigen on `Array<F.F64>` (`bend-kit-f64`) |
| `qr_array_f32.bend` | $1000 \times 50$ thin Householder QR on flat `Array<F32>` |
| `precision.py` | NumPy/SciPy timings + accuracy sweep across $\kappa \in [10, 10^6]$ for WLS (normal equations vs QR), Woodbury MVO (weights, SRE, logdet), and spiked-covariance Jacobi eigen |

## Speed results

Apple M-series, macOS, Bend 2.0.40, 2026-11-23. Per-call times in ms (1t = `+RTS --threads 1 -RTS`).

| kernel | Bend `List` F32 | Bend `Array` F32 | Bend `Array` F64 | NumPy/SciPy F32 | NumPy/SciPy F64 |
|---|---:|---:|---:|---:|---:|
| Gram $B^\top B$ ($1000 \times 50$) | 12 ms (1t) / 5 ms (8t) | **1 ms** (1t) | — | 0.008 ms | 0.025 ms |
| Cholesky ($50 \times 50$) | 0.076 ms (1t) | **0.012 ms** (1t) | 3.8 ms (1t) | 0.011 ms | 0.009 ms |
| Thin Householder QR ($1000 \times 50$) | — | **2 ms** (1t) | — | 1.41 ms | 1.38 ms |
| Cyclic Jacobi eigen ($50 \times 50$, 6 sweeps) | — | **< 1 ms** (1t) | 67 ms (1t) | 0.17 ms (`eigh`) | 0.16 ms (`eigh`) |

## Precision results

### 1. Cross-sectional WLS ($N = 1000, K = 50$): relative error $\|f - f_{\text{ref}}\| / \|f_{\text{ref}}\|$

| $\kappa(B)$ | NE `f32` | NE `f32→f64` | Thin QR `f32` | NE `f64` | Thin QR `f64` |
|---:|---:|---:|---:|---:|---:|
| $10^1$ | `8.20e-06` | `1.95e-08` | `5.75e-07` | `7.77e-15` | `2.80e-15` |
| $10^2$ | `3.37e-04` | `8.67e-08` | `1.33e-06` | `8.33e-13` | `4.33e-15` |
| $10^3$ | `2.24e-02` | `4.11e-07` | `3.07e-06` | `5.17e-11` | `9.84e-15` |
| $10^4$ | **FAIL (NPD)** | `8.14e-06` | `2.49e-05` | `1.92e-09` | `8.30e-14` |
| $10^5$ | **FAIL (NPD)** | `3.74e-05` | `3.00e-04` | `4.24e-07` | `8.92e-13` |
| $10^6$ | **FAIL (NPD)** | `4.28e-04` | `2.14e-03` | `3.27e-05` | `6.93e-12` |

### 2. Woodbury MVO $(D + B \Omega_f B^\top)^{-1} \alpha$ ($N = 1000, K = 50$)

| $\kappa(\Omega_f)$ | weight err `f32` | SRE `f32` | weight err mixed `f32→f64` | SRE mixed | `logdet` err `f32` |
|---:|---:|---:|---:|---:|---:|
| $10^1$ | `5.53e-08` | `1.000000` | `4.56e-08` | `1.000000` | `1.00e-08` |
| $10^3$ | `6.21e-08` | `1.000000` | `4.56e-08` | `1.000000` | `8.81e-08` |
| $10^5$ | `1.96e-06` | `1.000000` | `4.56e-08` | `1.000000` | `1.76e-07` |
| $10^6$ | `2.67e-05` | `1.000000` | `4.56e-08` | `1.000000` | `2.66e-06` |

### 3. Cyclic Jacobi on spiked $50 \times 50$ covariance ($\lambda \in [0.01, 100]$)

- `f32`: `max_rel_eig_err = 8.42e-05`, `‖VᵀV - I‖_F = 4.80e-05`, `recon_err = 1.18e-05` (requires `F32.hypot(1.0, tau)` to avoid `tau * tau` overflow on tiny off-diagonals)
- `f64`: `max_rel_eig_err = 3.11e-13`, `‖VᵀV - I‖_F = 6.00e-14`, `recon_err = 1.70e-14`

## What the numbers say

1. **Use thin Householder QR in `F32` for WLS/OLS — never `F32` normal equations.**
   Normal equations square $\kappa(B)$ and break Cholesky outright at $\kappa = 10^4$ (already 2.2% error at $\kappa = 10^3$). Thin Householder QR in `Array<F32>` takes just **2 ms** for $1000 \times 50$ (within 1.4× of NumPy/Accelerate!) and stays at `3e-6` error at $\kappa = 10^3$ and `2.5e-5` at $\kappa = 10^4$.
2. **`F32` is accurate and fast enough as the default scalar type** (until Bend gets native `F64`, bendlang/bend#1120).
   Woodbury MVO in `F32` keeps `SRE = 1.000000` even at $\kappa(\Omega_f) = 10^6$. Jacobi `F32` reaches `~1e-5` reconstruction error in `< 1 ms` vs `67 ms` in soft-float `F64`. Soft-float `F64` Cholesky (`3.8 ms`) is cheap enough to keep as an optional high-precision escape hatch only if a caller actually hits $\kappa > 10^5$ on a small $K \times K$ solve.
3. **Hybrid layout (`Data` row-lists at the API, flat `Array<F32>` inside kernels) is the clear winner.**
   `Array<F32>` is **6–12× faster** than `List` on Cholesky (`0.012 ms` vs `0.076 ms`) and Gram (`1 ms` vs `12 ms` 1t / `5 ms` 8t), and matches Apple Accelerate on $50 \times 50$ Cholesky and comes within 1.4× on $1000 \times 50$ QR. Exposing `Mat` as `Data` (`List<&2, List<&2, F32>>`, matching `signal`'s `Panel`) keeps values reusable and lets `LAWS.bend` / `PROOF.bend` state and prove structural invariants without affine-`Type` friction; copying into a scratch `Array<F32>` at the boundary of `cholesky`, `qr_thin`, `sym_eigen`, and `gram` costs microseconds.

---

## End-to-end `linalg.bend` & GPU benchmarks (Apple M1 Pro, AMD EPYC, Intel Xeon, NVIDIA Tesla T4)

After completing `linalg` v0.1.0.0, we benchmarked the **actual public `linalg.bend` API** (`bench_suite.bend`, including all `Data` list ↔ `Array<F32>` conversions) plus Bend's native GPU (`!`) backend (`bench_gpu.bend`, 4-way fork tree of $4^7 = 16{,}384$ lanes) across four environments:

- **Apple M1 Pro** (8 CPU cores + 16-core Metal GPU, macOS, Apple Accelerate BLAS/LAPACK)
- **Colab High-Mem CPU** (AMD EPYC 7B12, 8 vCPU / 4 cores, 50 GB RAM, OpenBLAS)
- **Colab GPU VM CPU** (Intel Xeon @ 2.00 GHz, 2 vCPU, 12 GB RAM, OpenBLAS)
- **Colab NVIDIA Tesla T4** (15 GB VRAM, CUDA 13.0, compute capability 7.5, `clang-19` for Bend CUDA + PyTorch 2.14.1+cu130)

### 1. Public `linalg.bend` API (per-call ms)

| Operation | M1 Pro Bend 1t | M1 Pro Bend 8t | M1 Pro NumPy f32 | EPYC Bend 1t | EPYC NumPy f32 | Xeon Bend 1t | Xeon NumPy f32 | T4 PyTorch CUDA |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `matvec` ($1000\times 50$) | 0.40 | **0.20** | 0.0056 | 0.35 | 0.0060 | 0.40 | 0.0125 | 0.0146 |
| `matmul` ($1000\times 50 \cdot 50\times 50$) | 13.8 | **3.6** | 0.0189 | 17.0 (5.4 8t) | 0.0562 | 20.6 | 0.0730 | 0.0175 |
| `gram` ($1000\times 50$) | 18.1 | 15.3 | 0.0083 | 37.7 (30.0 8t) | 0.0762 | 38.0 | 0.0951 | 0.0252 |
| `wgram` ($1000\times 50$) | 18.1 | 16.2 | 0.0245 | 38.4 (35.1 8t) | 0.1484 | 34.4 | 0.1484 | — |
| `cholesky` ($50\times 50$) | **0.09** | 0.09 | 0.0114 | 0.13 | 0.0248 | 0.15 | 0.0477 | 0.0879 |
| `cholesky_solve` ($50\times 50$) | **0.01** | 0.01 | 0.0068 | **0.02** | 0.0219 | **0.02** | 0.0280 | — |
| `woodbury_solve` ($1000\times 50$) | 25.2 | 28.8 | 0.0847 | 51.8 | 0.5540 | 48.6 | 0.4237 | — |
| `woodbury_logdet` ($1000\times 50$) | 21.4 | 24.2 | 0.0665 | 45.0 | 0.5930 | 43.6 | 0.3431 | — |
| `qr_thin` ($1000\times 50$) | **5.2** | 5.6 | 1.35 | 8.4 | 5.54 | 9.0 | 2.06 | 0.478 |
| `lstsq` ($1000\times 50$) | **2.0** | 2.0 | 0.96 | **2.6** | 2.49 | 3.0 | 2.03 | 1.12 |
| `wlstsq` ($1000\times 50$) | 5.2 | 6.6 | 1.00 | 8.0 | 2.33 | 9.0 | 2.12 | — |
| `project_orth` ($1000\times 50$) | 6.4 | 13.2 | 0.0130 | 10.8 | 0.0140 | 15.5 | 0.0252 | — |
| `lstsq_constrained` ($500\times 30, p=3$) | **2.6** | 4.2 | 0.25 | 3.0 | 0.48 | 4.8 | 0.75 | — |
| `sym_eigen` ($50\times 50$) | **0.55** | 0.60 | 0.166 | **0.85** | 0.589 | 1.20 | 0.586 | 0.959 |
| `spd_pow` ($50\times 50, p=-0.5$) | **0.90** | 1.70 | 0.177 | 1.40 | 0.619 | 2.20 | 0.567 | — |
| `svd_thin` ($500\times 30$ tall) | **4.2** | 5.0 | 0.444 | 5.4 | 0.809 | 7.8 | 0.934 | 1.35 |
| `svd_thin` ($30\times 500$ wide) | **5.6** | 6.2 | 0.480 | 6.6 | 1.19 | 8.8 | 1.29 | — |
| `pinv` ($200\times 30$) | 4.4 | 6.0 | 0.213 | 5.2 | 0.409 | 8.0 | 0.659 | — |
| `procrustes` ($500\times 30$) | 7.8 | 11.0 | 0.110 | 14.6 | 0.272 | 13.0 | 0.439 | — |

### 2. Bend GPU (`!`) vs CPU Parallel (`bench_gpu.bend`, 16,384 leaves = $4^7$, per-call ms)

| Workload | M1 Pro 1t | M1 Pro 8t | **M1 Pro Metal `!`** | EPYC 1t | EPYC 8t | Xeon 1t | Xeon 2t | **Tesla T4 CUDA `!`** | T4 PyTorch CUDA |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `compute_16384x4096` (134M FLOPs) | 85.3 | 16.6 | 25.7 | 108.0 | 16.1 | 151.9 | 85.9 | **9.1** (**16.7×**) | — |
| `compute_16384x16384` (537M FLOPs) | 449.8 | 72.0 | **15.6** (**28.8×**) | 468.2 | 65.2 | 670.2 | 352.8 | **34.2** (**19.6×**) | — |
| `matvec_tree_16384x64` (2.1M FLOPs) | 4.8 | **1.6** | 3.1 | 11.1 | 2.4 | 5.9 | 4.8 | 5.4 | 0.021 |
| `matmul_tree_16384x64x16` (33.6M FLOPs) | 68.2 | 13.8 | **9.6** (**7.1×**) | 81.7 | 11.7 | 80.1 | 61.1 | **14.8** (**5.4×**) | 0.037 |

### Takeaways from the cross-hardware run

1. **Array-backed factorizations are genuinely competitive with LAPACK.** `cholesky_solve` ($50\times 50$) beats SciPy on EPYC and Xeon (`0.02 ms` vs `0.022–0.028 ms`); `lstsq` ($1000\times 50$) matches NumPy/OpenBLAS on EPYC (`2.6 ms` vs `2.49 ms`) and is within 2× on M1 Pro (`2.0 ms` vs `0.96 ms`); `sym_eigen` ($50\times 50$) is faster on M1 Pro (`0.55 ms`) and EPYC (`0.85 ms`) than PyTorch CUDA on Tesla T4 (`0.96 ms`).
2. **Bend's `!` GPU backend scales strongly once per-lane compute is large enough.** On 16,384-lane compute bangs, M1 Pro Metal reaches **28.8×** over 1t CPU (`15.6 ms` = 34.4 GFLOP/s, unified memory) and Tesla T4 CUDA reaches **16.7–19.6×** over Xeon 1t (`9.1 ms` / `34.2 ms`). Real quadtree cons-list `matmul` ($16{,}384 \times 64 \times 16$) speeds up **7.1×** on Metal (`9.6 ms`) and **5.4×** on T4 CUDA (`14.8 ms`). Small single-matrix $1000\times 50$ factorizations remain faster on CPU because GPU launch and CUDA managed-memory PCIe page faults dominate.
3. **Post-benchmark CPU optimizations applied to `linalg.bend` (verified on M1 Pro with all 37 `--verdict` proofs and 45 `check.py` tests passing):**
   - Moved `gram` and `wgram` to flat column-major `Array<F32>` with provable `arr_upper_tri` + `mirror_upper` symmetry (`gram`: `18.1 → 1.3 ms`, **13.9×**; `wgram`: `18.1 → 1.5 ms`, **12.1×**; `woodbury_solve`: `25.2 → 4.0 ms`, **6.3×**; `woodbury_logdet`: `21.4 → 3.8 ms`, **5.6×**; `spd_pow` 8t: `1.70 → 0.70 ms`, **2.4×**).
   - Replaced transpose-heavy `matvec_t` and `project_orth` with single-pass flat `Array<F32>` loops (`project_orth`: `6.4 ms 1t / 13.2 ms 8t → 0.30 ms 1t / 0.35 ms 8t`, **21–38×**).
   - Loaded weighted rows directly into the column-major QR `Array<F32>` in `wlstsq` (`5.2 ms 1t / 6.6 ms 8t → 2.4 ms 1t / 2.2 ms 8t`, **2.2–3.0×**).
   - Computed $A^\top B$ directly on column-major `Array<F32>` inside `procrustes` (`7.8 ms 1t / 11.0 ms 8t → 1.8 ms 1t / 2.0 ms 8t`, **4.3–5.5×**).
