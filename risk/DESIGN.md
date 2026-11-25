# risk: design notes

`risk` implements factor model transformations, out-of-sample risk model evaluation, fundamental factor models & covariance estimation, and statistical factor models (PCA / SVD / PPCA / RMT / Procrustes alignment) from Giuseppe Paleologo's *The Elements of Quantitative Investing* (Chapters 4–7), built directly on `bend-quant-linalg@0.1.0.0` and `bend-quant-portfolio@0.1.0.0`.

## Core architectural choices

### 1. Zero-boilerplate ecosystem integration (`P.FactorModel`)
Every estimator (`fit_fundamental_model`, `ppca_fit`, `fit_statistical_model`, `rolling_fundamental_models`, `rolling_statistical_models`) returns `bend-quant-portfolio@0.1.0.0`'s `P.FactorModel{b, cov_f, idio_var}` directly, and every Ch 4–5 transformation and evaluator consumes `P.FactorModel` directly. Return panels follow `signal` and `portfolio`'s convention (`T × N` row-major `L.Mat`, where row `t` is the one-period return over `(t - 1, t]`).

### 2. Zero $N \times N$ dense covariance materialization (Ch 4 & Ch 5)
Across all factor-model transformations and out-of-sample evaluators, the full $N \times N$ return covariance $\Omega_r = B \Omega_f B^\top + \Omega_\varepsilon$ is never formed:
- `qdist`, `mahalanobis_test`, and `mvp_test` evaluate $\Omega_r^{-1} r_{t+1}$, $\log|\Omega_r|$, and $\Omega_r^{-1} b$ in $O(NK^2 + K^3)$ per period via `L.woodbury_solve` and `L.woodbury_logdet`, parallelized across dates via fork-join `pmap`. On $252 \times 500 \times 30$, `qdist` runs **4.2× faster than dense NumPy/Accelerate**.
- `beta_error` (Ch 5.3.2) computes the EWMA realized covariance vector $\hat{\Omega}_{r,t} w_{\text{ref}} = \sum_{s \le t} \alpha_s r_s (r_s^\top w_{\text{ref}})$ via scalar-weighted row updates in $O(TN)$ total work and $O(N)$ memory.
- `pushout_loadings` (Ch 4.4.3 Eq 4.5) orthogonalizes candidate loadings $A$ against $B$ under $\Omega_\varepsilon^{-1}$ via thin QR of $\Omega_\varepsilon^{-1/2} B$ (`L.qr_thin` + `L.project_orth`), avoiding squaring $\kappa(\Omega_\varepsilon^{-1/2} B)$ in `F32`.

### 3. Exact structural symmetry by construction (`cov.bend`)
Every covariance estimator (`sample_cov`, `ewma_cov`, `shrink_to_identity`, `ledoit_wolf_cov`, `psd_project`, `dcc_cov`, `cov_newey_west`, `cov_autocorr_cohen`, `link_models_ir`) passes through `mirror_upper` / `symmetrize_raw`, which constructs only the upper triangle and mirrors it into the full matrix. Because `sym_tri.go` and `hac_tri.i` track ascending `Nat` row lengths (`1n, 2n, ..., n`), `PROOF.bend` proves exact bit-for-bit structural symmetry (`L.Mat.get(M, i, j) == L.Mat.get(M, j, i)`) for all 10 covariance families via linear lexicographic induction without any `F32` arithmetic assumptions.

### 4. Exact numerical formulas & $O(TK + K^2)$ kernels
- **Ledoit–Wolf (2004):** uses the exact identity $\sum_t \|x_t x_t^\top - S\|_F^2 = \sum_t \|x_t\|_2^4 - T \|S\|_F^2$ to compute the analytical shrinkage intensity in $O(TK + K^2)$ without allocating per-date $K \times K$ outer products, matching `sklearn.covariance.LedoitWolf` to `1e-6`.
- **Newey–West & Cohen HAC (§6.3.4):** runs over flat `Array<F32>` buffers in a single upper-triangular pass with Bartlett weights $1 - \ell/(L + 1)$ or Cohen equal weights $1/2$, supporting both equal-weighted and EWMA time decay.
- **Exact STVU (§6.3.3 Eq 6.8 & 6.11):** computes $\mathbb{E}[\log \chi^2_K] = \log 2 + \psi(K/2)$ via a 4-step recurrence + asymptotic digamma expansion (matching `scipy.special.digamma` to full `F32` precision) and also provides the linear vol-ratio approximation (Eq 6.11).
- **Cross-sectional regressions (§6.2):** unconstrained WLS uses thin QR of $W^{1/2} B$ (plus exact $(B^\top W B)^{-1}$ via $R^{-1} R^{-\top}$); Heston–Rouwenhorst constrained WLS solves the exact symmetric KKT saddle-point system via `L.solve` (handling exact rank deficiency such as market + mutually exclusive sectors); Ridge WLS uses augmented thin QR; Ridgeless uses `L.pinv`.
- **Causal log-MAD winsorization (§6.5):** built directly on a generic left `scan` over rows so `PROOF.bend` proves strict causality (`winsorize_log_mad_causal`) — future returns cannot affect past rolling medians or clipped returns.

### 5. Fast deterministic top-$K$ subspace SVD (`subspace_svd.bend`)
Full exact thin SVD (`L.svd_thin`) costs $O(\min(T, N)^2 \max(T, N))$, which is ideal for full-spectrum diagnostics (`ppca_fit`, `select_k_bai_ng`, small panels) but slow on large institutional panels ($T = 250, N = 500\text{–}1000, K = 15$). `subspace_svd.bend` implements deterministic LCG-seeded randomized subspace iteration with twice-iterated Modified Gram–Schmidt over flat `Array<F32>` buffers, followed by an exact thin SVD on the tiny $(K + p) \times N$ projected matrix $B = Q^\top A$:
- Automatically delegates to exact `L.svd_thin` when $\min(m, n) \le \max(k + \text{oversample}, 40)$ or $2k \ge \min(m, n)$.
- On $250 \times 500, K = 15$, achieves a **19.3× speedup** over exact `L.svd_thin` (`36.7 ms` vs `709.5 ms` on 8t, within **3.0×** of Apple Accelerate LAPACK) while matching exact singular values and subspaces to `< 6e-6` on spiked equity return panels.

### 6. Effect isolation & formal guarantees
All binary file IO (`Returns.load`, `LoadingsSeries.load`) lives in `io.bend`, keeping `subspace_svd.bend`, `cov.bend`, `risk.bend`, `LAWS.bend`, and `PROOF.bend` completely pure (zero IO, zero `@unsafe`, 47 Lean-verified BendTT proofs).
