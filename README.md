# bend-quant

Formally verified quantitative finance libraries in [Bend](https://bend-lang.com/), built on a shared `float32` row-list representation (`List<&2, List<&2, F32>>`) so signals, factor matrices, and portfolios compose with zero copying.

Every package separates pure math from file IO (`io.bend`), proves its structural, alignment, symmetry, parallel-equivalence, and causality invariants in `LAWS.bend` / `PROOF.bend` with zero `@unsafe` (verified with `bend PROOF.bend --verdict`), and tests numerical accuracy against NumPy, SciPy, pandas, scikit-learn, statsmodels, and OSQP.

## Packages

| Package | BendHub | Scope | Key proved laws | Docs & Benchmarks |
|---|---|---|---|---|
| **[signal](signal/)** | `bend-quant-signal@0.1.0.0` | Cross-sectional signal evaluation: Spearman rank IC, Pearson IC, summary stats, Newey–West $t$, causal transforms (`ewma`, `rolling_mean`, `zscore`, `winsorize`, `rank`) | No-lookahead `forward_rank_ic`, strict `scan` causality, exact NaN pair filtering, average-rank merge sort, `pmap` equivalence | [README](signal/README.md) · [DESIGN](signal/DESIGN.md) · [Benchmarks](signal/bench/README.md) |
| **[linalg](linalg/)** | `bend-quant-linalg@0.1.0.0` | Dense `F32` linear algebra: Cholesky, triangular solves, Woodbury & Matrix Determinant Lemma, thin Householder QR, OLS/WLS/constrained least squares, cyclic Jacobi eigen, SPD powers, thin SVD, pseudoinverse, Procrustes | 37 laws: rectangular validation, transpose involution, exact bitwise symmetry (`gram`, `wgram`, `spd_pow`), triangular zero structure (`cholesky`, `qr_thin`), `pmap` equivalence, dimension guards | [README](linalg/README.md) · [DESIGN](linalg/DESIGN.md) · [Benchmarks](linalg/bench/README.md) |
| **[portfolio](portfolio/)** | `bend-quant-portfolio@0.1.0.0` | Portfolio construction, risk & attribution (Paleologo *The Elements of Quantitative Investing*, Ch 4.5, 9–14): factor risk decomposition, analytical MVO, Woodbury-preconditioned ADMM constrained QP + L1/GMV solver, hedging, Kelly & Grossman–Zhou sizing, ex-post & causal multi-period attribution | 33 laws: `FactorModel` validation, no-lookahead `forward_pnl`, strict `grossman_zhou_path` causality, `pmap` equivalence, 24 dimension guards | [README](portfolio/README.md) · [DESIGN](portfolio/DESIGN.md) · [Benchmarks](portfolio/bench/README.md) |
| **[risk](risk/)** | `bend-quant-risk@0.1.1.0` | Factor & covariance estimation and risk evaluation (Paleologo *The Elements of Quantitative Investing*, Ch 4–7): model rotations/projection/pushout, group risk, QLIKE/QDIST/Mahalanobis/MVP/BETAERR, Ledoit–Wolf/DCC/STVU/Newey–West/Cohen HAC/Cai clusters/causal log-MAD winsorization/IR linking/currency rebasing, WLS & constrained fundamental models, PCA/fast subspace SVD/PPCA/RMT/Bai–Ng/Procrustes statistical models | 47 laws (24 structural, 23 dimension/parameter guards): 11 exact bitwise symmetry laws, 4 strict causality laws (`winsorize_log_mad`, `make_windows`), 7 no-lookahead laws tying `qdist`, `mahalanobis_test`, `mvp_test`, `portfolio_vol_eval` and rolling models (`oos_returns`) to row $t + 1$, `pmap` equivalence | [README](risk/README.md) · [DESIGN](risk/DESIGN.md) · [Benchmarks](risk/bench/README.md) |

## Quick import (from BendHub)

```bend
import bend-quant-signal@0.1.0.0/signal.bend as S
import bend-quant-linalg@0.1.0.0/linalg.bend as L
import bend-quant-portfolio@0.1.0.0/portfolio.bend as P
import bend-quant-risk@0.1.1.0/risk.bend as R
```

File loaders live in each package's `io.bend` (wrapping `bend-kit-f32array@0.2.1.0`), kept outside `PROOF.bend` so every proof remains pure and free of foreign effects.

## Design principles

- **Proved invariants, tested numerics:** Bend's type checker verifies structural invariants for *all* inputs—no-lookahead date alignment, strict causality, symmetry, triangular zero structure, and parallel-to-sequential equivalence—while `check.py` in each package cross-checks floating-point values against reference Python libraries.
- **Hybrid data layout:** Public APIs expose immutable `Data` row lists (`Panel`, `Mat`, `Vec`, `FactorModel`) that are freely reusable and proof-friendly, while hot inner loops (`cholesky`, `qr_thin`, `gram`, `sym_eigen`, `admm.bend`, `cov.bend`, and `subspace_svd.bend`) pack into flat `Array<F32>` buffers for cache-friendly execution.
- **Shared causal return convention:** Across `signal`, `portfolio`, and `risk`, row $j$ of a return matrix holds the one-period return over $(j - 1, j]$. Forward evaluation (`forward_rank_ic`, `forward_pnl`, `forward_attribute`, `qdist`, `mahalanobis_test`, `mvp_test`, `portfolio_vol_eval`) structurally pairs row $t$ with row $t + 1$, making same-day lookahead unrepresentable. Rolling models line up with their evaluation rows through `R.oos_returns`.

## Verification

Requires `bend` 2.0.40 and `python3` with `numpy`, `scipy`, `pandas`, `scikit-learn`, and `statsmodels`:

```sh
# Formal proofs (checked twice, including BendTT's Lean-verified kernel)
(cd signal    && bend PROOF.bend --verdict)
(cd linalg    && bend PROOF.bend --verdict)
(cd portfolio && bend PROOF.bend --verdict)
(cd risk      && bend PROOF.bend --verdict)

# Numerical verification against Python reference libraries
python3 signal/check.py
python3 linalg/check.py
python3 portfolio/check.py
python3 risk/check.py
```

## Benchmark highlights

Measured across Apple M1 Pro, AMD EPYC 7B12 (8 vCPU), Intel Xeon (2 vCPU), and NVIDIA Tesla T4 (see each package's `bench/README.md` for full cross-hardware tables):

- **Constrained factor-model MVO (`portfolio/admm.bend` vs. OSQP):** On the full production constraint set (box bounds, dollar neutrality, $K$ factor bounds, GMV cap, L1 spread + L2 impact costs), Bend's Woodbury-preconditioned ADMM beats pure C OSQP by **2.6×–7.5×** (`5.32` vs `13.87 ms` at $200\times 15$, `36.37` vs `98.78 ms` at $500\times 30$, `122.2` vs `714.5 ms` at $1000\times 30$ on EPYC; `3.72` / `24.45` / `81.69 ms` on M1 Pro).
- **Risk & factor model estimation (`risk.bend` vs. NumPy/SciPy/Accelerate on M1 Pro):** Deterministic flat-array `subspace_svd` speeds up PCA by **19.3×** over exact SVD (`36.7` vs `709.5 ms` on $250\times 500, K=15$, within **3.0×** of Accelerate LAPACK); zero-$N\times N$ Woodbury `qdist` ($252\times 500\times 30$, 8t) beats dense NumPy/Accelerate by **4.2×** (`186.8` vs `788.7 ms`); causal `dcc_cov` ($252\times 30$) beats NumPy (`0.77` vs `0.81 ms`); 127 rolling statistical windows with Procrustes alignment run in `653.8 ms` on 8t (**2.69×** scaling).
- **Dense linear algebra (`linalg.bend` vs. BLAS/LAPACK):** `cholesky_solve` ($50\times 50$) matches or beats SciPy on EPYC/Xeon (`0.02 ms`); `lstsq` ($1000\times 50$) matches OpenBLAS on EPYC (`2.6` vs `2.49 ms`); `sym_eigen` ($50\times 50$) runs in `0.55 ms` on M1 Pro and `0.85 ms` on EPYC.
- **Parallel & GPU scaling:** CPU fork-join `pmap` speeds up multi-period `forward_pnl`, `forward_attribute`, `qdist`, `mvp_test`, `estimate_factor_series`, and `rolling_statistical_models` by **2–3×** across cores; Bend's `!` GPU backend reaches **16–29×** on 16,384-lane compute benchmarks (M1 Pro Metal and Tesla T4 CUDA).

## License

MIT — see [LICENSE](LICENSE).
