# bend-quant

Formally verified quantitative finance libraries in [Bend](https://bend-lang.com/), built on a shared `float32` row-list representation (`List<&2, List<&2, F32>>`) so signals, factor matrices, and portfolios compose with zero copying.

Every package separates pure math from file IO (`io.bend`), proves its structural, alignment, symmetry, parallel-equivalence, and causality invariants in `LAWS.bend` / `PROOF.bend` with zero `@unsafe` (verified with `bend PROOF.bend --verdict`), and tests numerical accuracy against NumPy, SciPy, pandas, statsmodels, and OSQP.

## Packages

| Package | BendHub | Scope | Key proved laws | Docs & Benchmarks |
|---|---|---|---|---|
| **[signal](signal/)** | `bend-quant-signal@0.1.0.0` | Cross-sectional signal evaluation: Spearman rank IC, Pearson IC, summary stats, Newey–West $t$, causal transforms (`ewma`, `rolling_mean`, `zscore`, `winsorize`, `rank`) | No-lookahead `forward_rank_ic`, strict `scan` causality, exact NaN pair filtering, average-rank merge sort, `pmap` equivalence | [README](signal/README.md) · [DESIGN](signal/DESIGN.md) · [Benchmarks](signal/bench/README.md) |
| **[linalg](linalg/)** | `bend-quant-linalg@0.1.0.0` | Dense `F32` linear algebra: Cholesky, triangular solves, Woodbury & Matrix Determinant Lemma, thin Householder QR, OLS/WLS/constrained least squares, cyclic Jacobi eigen, SPD powers, thin SVD, pseudoinverse, Procrustes | 37 laws: rectangular validation, transpose involution, exact bitwise symmetry (`gram`, `wgram`, `spd_pow`), triangular zero structure (`cholesky`, `qr_thin`), `pmap` equivalence, dimension guards | [README](linalg/README.md) · [DESIGN](linalg/DESIGN.md) · [Benchmarks](linalg/bench/README.md) |
| **[portfolio](portfolio/)** | `bend-quant-portfolio@0.1.0.0` | Portfolio construction, risk & attribution (Paleologo *The Elements of Quantitative Investing*, Ch 4.5, 9–14): factor risk decomposition, analytical MVO, Woodbury-preconditioned ADMM constrained QP + L1/GMV solver, hedging, Kelly & Grossman–Zhou sizing, ex-post & causal multi-period attribution | 33 laws: `FactorModel` validation, no-lookahead `forward_pnl`, strict `grossman_zhou_path` causality, `pmap` equivalence, 24 dimension guards | [README](portfolio/README.md) · [DESIGN](portfolio/DESIGN.md) · [Benchmarks](portfolio/bench/README.md) |

## Quick import (from BendHub)

```bend
import bend-quant-signal@0.1.0.0/signal.bend as S
import bend-quant-linalg@0.1.0.0/linalg.bend as L
import bend-quant-portfolio@0.1.0.0/portfolio.bend as P
```

File loaders live in each package's `io.bend` (wrapping `bend-kit-f32array@0.2.1.0`), kept outside `PROOF.bend` so every proof remains pure and free of foreign effects.

## Design principles

- **Proved invariants, tested numerics:** Bend's type checker verifies structural invariants for *all* inputs—no-lookahead date alignment, strict causality, symmetry, triangular zero structure, and parallel-to-sequential equivalence—while `check.py` in each package cross-checks floating-point values against reference Python libraries.
- **Hybrid data layout:** Public APIs expose immutable `Data` row lists (`Panel`, `Mat`, `Vec`, `FactorModel`) that are freely reusable and proof-friendly, while hot inner loops (`cholesky`, `qr_thin`, `gram`, `sym_eigen`, and `admm.bend`) pack into flat `Array<F32>` buffers for cache-friendly execution.
- **Shared causal return convention:** Across `signal` and `portfolio`, row $j$ of a return matrix holds the one-period return over $(j - 1, j]$. Forward evaluation (`forward_rank_ic`, `forward_pnl`, `forward_attribute`) structurally pairs row $t$ with row $t + 1$, making same-day lookahead unrepresentable.

## Verification

Requires `bend` 2.0.40 and `python3` with `numpy`, `scipy`, `pandas`, and `statsmodels`:

```sh
# Formal proofs (checked twice, including BendTT's Lean-verified kernel)
(cd signal    && bend PROOF.bend --verdict)
(cd linalg    && bend PROOF.bend --verdict)
(cd portfolio && bend PROOF.bend --verdict)

# Numerical verification against Python reference libraries
python3 signal/check.py
python3 linalg/check.py
python3 portfolio/check.py
```

## Benchmark highlights

Measured across Apple M1 Pro, AMD EPYC 7B12 (8 vCPU), Intel Xeon (2 vCPU), and NVIDIA Tesla T4 (see each package's `bench/README.md` for full cross-hardware tables):

- **Constrained factor-model MVO (`portfolio/admm.bend` vs. OSQP):** On the full production constraint set (box bounds, dollar neutrality, $K$ factor bounds, GMV cap, L1 spread + L2 impact costs), Bend's Woodbury-preconditioned ADMM beats pure C OSQP by **2.6×–7.5×** (`5.32` vs `13.87 ms` at $200\times 15$, `36.37` vs `98.78 ms` at $500\times 30$, `122.2` vs `714.5 ms` at $1000\times 30$ on EPYC; `3.72` / `24.45` / `81.69 ms` on M1 Pro).
- **Dense linear algebra (`linalg.bend` vs. BLAS/LAPACK):** `cholesky_solve` ($50\times 50$) matches or beats SciPy on EPYC/Xeon (`0.02 ms`); `lstsq` ($1000\times 50$) matches OpenBLAS on EPYC (`2.6` vs `2.49 ms`); `sym_eigen` ($50\times 50$) runs in `0.55 ms` on M1 Pro and `0.85 ms` on EPYC.
- **Parallel & GPU scaling:** CPU fork-join `pmap` speeds up multi-period `forward_pnl` and `forward_attribute` by **2–3×** across cores; Bend's `!` GPU backend reaches **16–29×** on 16,384-lane compute benchmarks (M1 Pro Metal and Tesla T4 CUDA).

## License

MIT — see [LICENSE](LICENSE).
