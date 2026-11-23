# portfolio benchmarks

End-to-end timings of `portfolio.bend` (including `Data` row-list ↔ flat `Array<F32>` boundaries) measured across three CPU architectures against **NumPy (`float32`)** and **OSQP** (the standard C ADMM QP solver, using the sparse factor-model formulation with auxiliary factor vector $f = B^\top w$):

- **Apple M1 Pro** (8 CPU cores, arm64, macOS, Apple Accelerate BLAS/LAPACK)
- **Colab High-Mem CPU** (AMD EPYC 7B12, 8 vCPU / 4 cores, 50 GiB RAM, x86_64 Linux, OpenBLAS)
- **Colab Standard CPU** (Intel Xeon @ 2.20 GHz, 2 vCPU / 1 core, 12 GiB RAM, x86_64 Linux, OpenBLAS)

## Reproduction

```sh
cd portfolio/bench
mkdir -p out
bend bench_portfolio.bend -o out/bench_portfolio
python3 run_bench.py --threads 1
python3 run_bench.py --threads 8 --skip-py
```

`run_bench.py` subtracts process startup and binary file loading by timing `1` repetition vs. `1 + R` repetitions. If `osqp` is installed (`pip install osqp`), it also benchmarks the equivalent sparse factor-model QP+L1+GMV problem in OSQP at matching tolerances (`eps_abs=1e-5`, `eps_rel=1e-4`, `polish=False`).

## Cross-hardware results (per-call ms)

### 1. Risk, analytical MVO, hedging, attribution & parallel `pmap`

| Operation | M1 Pro Bend 1t | M1 Pro Bend 8t | M1 Pro NumPy f32 | EPYC Bend 1t | EPYC Bend 8t | EPYC NumPy f32 | Xeon Bend 1t | Xeon Bend 2t | Xeon NumPy f32 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `risk_decomp` ($1000 \times 30$) | **0.09** | 0.14 | 0.014 | **0.12** | 0.30 | 0.023 | **0.20** | 0.25 | 0.027 |
| `mvo_target_vol` ($1000 \times 30$) | **1.35** | 2.11 | 0.062 | **1.85** | 4.18 | 0.202 | **3.22** | 4.57 | 0.321 |
| `mvo_factor_neutral` ($1000 \times 30$) | 2.76 | **2.73** | 0.683 | **3.70** | 3.78 | 1.515 | **8.76** | 12.19 | 2.364 |
| `fmp` ($1000 \times 30$) | **6.18** | 6.42 | 0.789 | **8.80** | 8.88 | 1.886 | **16.02** | 23.97 | 2.628 |
| `hedge_instruments` ($1000 \times 30, M=10$) | **5.76** | 7.64 | 0.042 | **11.58** | 15.12 | 0.089 | **14.47** | 19.31 | 0.118 |
| `attribute_period` ($1000 \times 30$) | 3.64 | **3.61** | 0.665 | **4.51** | 5.87 | 1.603 | **8.91** | 13.86 | 1.686 |
| `forward_pnl` ($252 \times 1000$, `pmap`) | 1.11 | **0.36** | 0.081 | 1.20 | **0.60** | 0.120 | **1.12** | 2.07 | 0.299 |
| `forward_attribute` ($252 \times 200 \times 15$, `pmap`) | 86.83 | **30.24** | 13.703 | 123.15 | **56.25** | 20.366 | 206.91 | **148.25** | 31.757 |

### 2. Constrained MVO (`mvo_constrained`, Woodbury-ADMM vs OSQP)

Every case solves the full production constraint set simultaneously: position box bounds ($|w_i| \le 0.02$), dollar neutrality ($\mathbf{1}^\top w = 0$), all $K$ factor exposure bounds ($|B^\top w| \le 0.02$), GMV leverage cap ($\|w\|_1 \le 2.0$), L1 linear spread cost ($c_1 = 5\text{ bps}$), and L2 quadratic market impact ($c_2 = 50\text{ bps}$).

| Book size | M1 Pro Bend (1t / 8t) | EPYC Bend (1t / 8t) | EPYC OSQP (total / pure C) | Xeon Bend (1t / 2t) | Xeon OSQP (total) | Bend vs OSQP |
|---|---:|---:|---:|---:|---:|---|
| $200 \times 15, M=16$ | **3.72** / 4.03 | **5.32** / 6.62 | 16.37 / 13.87 (600 it) | **9.85** / 10.08 | 28.78 (600 it) | **2.6–3.1× faster** (115 it) |
| $500 \times 30, M=31$ | 25.38 / **24.45** | **36.37** / 41.59 | 100.98 / 98.78 (1175 it) | 73.87 / **57.66** | 182.98 (1175 it) | **2.5–3.2× faster** (204 it) |
| $1000 \times 30, M=31$ | 84.92 / **81.69** | 125.50 / **122.17** | 719.38 / 714.53 (1825 it) | **213.18** / 229.60 | 1,590.09 (1825 it) | **5.7–7.5× faster** (392 it) |

*(Pure C OSQP time is `res.info.run_time` = C setup + C solve with zero Python sparse-matrix construction overhead; e.g., at $1000 \times 30$ on EPYC, OSQP C setup is `13.40 ms` and C solve is `703.84 ms`.)*

## Takeaways

1. **Bend's Woodbury-ADMM beats pure C OSQP by 2.6×–7.5× on constrained factor-model MVO.**
   General-purpose sparse QP solvers like OSQP have to introduce $2N$ epigraph variables and $4N$ inequality rows to model L1 turnover costs and a GMV leverage cap, then repeatedly solve an $(8N + 2K + M + 1)$-dimensional sparse KKT system. `admm.bend` keeps all $N$ variables in their native space via an exact box $\cap$ $\ell_1$-ball projection and soft-thresholding proximal, factors only a single $(K+M) \times (K+M)$ dense Cholesky ($46\times 46$ or $61\times 61$) via Woodbury, and converges in **4.7–5.8× fewer iterations** (`115` vs `600`, `204` vs `1175`, `392` vs `1825`) at the same `1e-5` / `1e-4` tolerances.
2. **Fork-join `pmap` scales cleanly across cores on multi-period causal evaluation.**
   - `forward_pnl` ($252 \times 1000$): **3.1×** on M1 Pro (`1.11 → 0.36 ms`) and **2.0×** on EPYC (`1.20 → 0.60 ms`, 4 physical cores).
   - `forward_attribute` ($252 \times 200 \times 15$): **2.9×** on M1 Pro (`86.8 → 30.2 ms`, within **2.2×** of NumPy/Accelerate), **2.2×** on EPYC (`123.2 → 56.3 ms`, within **2.8×** of OpenBLAS), and **1.4×** on 1-core / 2-SMT Xeon (`206.9 → 148.3 ms`).
3. **Single-period QR-backed routines stay within 2.4–5.5× of LAPACK.**
   `mvo_factor_neutral` ($1000 \times 30$) is **2.4×** of OpenBLAS on EPYC (`3.70` vs `1.52 ms`) and **4.0×** of Accelerate on M1 Pro (`2.73` vs `0.68 ms`); `attribute_period` ($1000 \times 30$) is **2.8×** of OpenBLAS on EPYC (`4.51` vs `1.60 ms`).

## Optimization notes

### Curvature-matched dual-penalty ADMM ($\mu_w, \mu_c$)

An initial single-$\mu$ ADMM using only the diagonal Hessian mean $\bar{d} = \operatorname{mean}(\rho d_\varepsilon + c_2) \approx 0.015$ converged slowly on large books because factor-subspace eigenvalues of $\rho B \Omega_f B^\top$ scale with $N$ ($\sim 0.8$ at $N=1000$), leaving primal residuals $10^4\times$ larger than dual residuals (`1000` iterations, `203.5 ms`, `rp=1.68e-3`).

Estimating the mean factor-subspace curvature $\lambda_{\text{fac}} = \rho \operatorname{tr}(\Omega_f) \|B\|_F^2 / K^2$ and splitting the ADMM penalties into $\mu_w = \sqrt{\bar{d}(\bar{d} + \lambda_{\text{fac}})}$ (box / L1) and $\mu_c = \max(\mu_w, \bar{d} + \lambda_{\text{fac}})$ (equilibrated linear constraints), while checking unscaled primal residuals, improved both speed and convergence dramatically (measured on M1 Pro):

| book size | before (single $\mu$) | after ($\mu_w, \mu_c$) | speedup |
|---|---:|---:|---:|
| $200 \times 15, M=16$ | 886 iters / `25.15 ms` | **192 iters / `5.74 ms`** | **4.4×** |
| $500 \times 30, M=31$ | 1000 iters (unconv) / `102.73 ms` | **332 iters (conv) / `36.55 ms`** | **2.8×** |
| $1000 \times 30, M=31$ | 1000 iters (unconv) / `203.51 ms` | **463 iters (conv) / `94.90 ms`** | **2.1×** |
