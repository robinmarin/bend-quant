# risk: plan

> **Status:** Active implementation (`v0.1.0.0`).
> Built directly on published `bend-quant-linalg@0.1.0.0` and `bend-quant-portfolio@0.1.0.0` (sharing `P.FactorModel`, `L.Mat`, and `L.Vec` with zero conversion boilerplate), and compatible with `bend-quant-signal@0.1.0.0`'s `T × N` return panel layout.

## Pipeline placement

```
signal (published)     →  Step 1: cross-sectional IC, rank IC, causal signal transforms
linalg (published)     →  Dense linear algebra: Cholesky, Woodbury, QR, sym-eigen, SVD, Procrustes
risk (this pkg)        →  Step 2: factor & covariance estimation, transformations, risk evaluation (Ch 4–7)
portfolio (published)  →  Steps 3–4: risk decomp, MVO, ADMM QP, hedging, Kelly/GZ, attribution (Ch 4.5, 9–14)
```

## Conventions
- **Return panels:** `R` is `T × N` (`L.Mat`), where row `t` is the cross-sectional return vector over `(t - 1, t]` (matching `signal` and `portfolio`).
- **Loadings:** `B` is `N × K` (`L.Mat`), matching `P.FactorModel{b, cov_f, idio_var}`.
- **EWMA half-life:** `half_life > 0` uses exact half-life decay $\lambda = 2^{-1/\text{half\_life}}$, normalized so weights sum to `1.0` with the most recent row (`t = T - 1`) receiving the largest weight.
- **Strict causality:** Every rolling / EWMA estimator at date `t` depends strictly on rows `0 .. t`. Every Ch 5 multi-period risk evaluator pairs `fms[t]` strictly with realized `returns[t + 1]`.

## Public API & Milestones

### Milestone 1 — Core Covariance Estimation & Ch 4 Transformations
- **Factor model transformations (Ch 4.4 & 4.5.2):**
  - `rotate_model(fm, c_mat)` — general covariance-preserving rotation ($\tilde{B} = B C^{-1}, \tilde{\Omega}_f = C \Omega_f C^\top$)
  - `rotate_identity_cov(fm)` — uncorrelated unit-variance factor view ($\tilde{\Omega}_f = I_K$)
  - `rotate_orthonormal_loadings(fm)` — orthonormal loadings view ($\tilde{B}^\top \tilde{B} = I_K$)
  - `rotate_zscore_loadings(fm, a_vec, shifts, scales)` — Eq (4.4) centering & rescaling when $B a = \mathbf{1}$
  - `project_model(fm, a_mat)` — §4.4.2 factor reduction onto $\operatorname{col}(A)$
  - `pushout_loadings(b, a, idio_var)` & `pushout_model(fm, a, cov_g, new_idio_var)` — §4.4.3 Eq (4.5) heteroskedastic factor augmentation
  - `group_risk_decomp(fm, w, groups)` — §4.5.2 partitioned group covariance, variance shares $p_i$, and group MCR $m_i$
- **Covariance, shrinkage, DCC, STVU & autocorrelation (Ch 6.3–6.6):**
  - `ewma_weights(t, half_life)` — normalized exponential weights
  - `sample_cov(x, center)` & `ewma_cov(x, half_life, center)` — structurally symmetric covariance via `L.gram` / `L.wgram`
  - `shrink_to_identity(cov, rho)` — $(1 - \rho) \hat{\Omega} + \rho (\operatorname{tr}(\hat{\Omega})/K) I_K$
  - `ledoit_wolf_cov(x, center)` — analytical Ledoit–Wolf (2004) optimal linear shrinkage intensity $\rho^*$ toward scaled identity
  - `debias_factor_cov(cov_f_raw, b, idio_var, eig_floor)` — Eq (6.5) regression-error bias correction with PSD floor
  - `dcc_cov(f_rets, hl_vol, hl_corr)` — §6.3.2 dual-half-life volatility / correlation separation
  - `stvu_factor_multiplier(f_rets, cov_f, hl_fast, linear_approx)` & `stvu_adjust_cov(...)` — §6.3.3 Eq (6.8, 6.11) Short-Term Volatility Updating
  - `cov_autocorr_cohen(x, l_max, half_life)` & `cov_newey_west(x, l_max, half_life)` — §6.3.4 autocorrelation-consistent covariance
  - `idio_var_ewma(eps, half_life)`, `idio_var_shrink(idio_var, rho)`, `idio_stvu(eps, idio_var, event_weights, hl_fast)` — §6.4.1, §6.4.3, §6.4.5
  - `cai_threshold(n, t, k_const)` & `idio_corr_clusters(eps, threshold)` — §6.4.4 off-diagonal correlation thresholding
  - `link_models_ir(local_covs, joint_cov, rho)` — §6.6.1 Integrated-Rotated-Shrunken multi-block model linking via `L.spd_pow`
  - `rebase_currency(b, c_mat, cov_f_c, target_idx)` — §6.6.2 Eq (6.14–6.16) numeraire rebasing

### Milestone 2 — Fundamental Factor Models & Ch 5 Risk Evaluation
- **Fundamental cross-sectional estimation (Ch 6.2 & 6.5):**
  - `winsorize_log_mad(returns, window, d_max)` — §6.5 causal rolling log-MAD outlier winsorization
  - `cross_sectional_wls(b, r, weights)` — thin-QR WLS returning $(\hat{f}_t, \hat{\varepsilon}_t, (B^\top W B)^{-1})$
  - `cross_sectional_constrained(b, r, weights, c_mat, d_vec)` — §6.2.1 Heston–Rouwenhorst equality-constrained WLS (rank-deficient market + industry/country dummies)
  - `cross_sectional_ridge(b, r, weights, delta)` & `cross_sectional_ridgeless(b, r, weights, tol)`
  - `estimate_factor_series(bs, returns, weights, opt_constraints)` — parallel `pmap` across dates
  - `fit_fundamental_model(returns, bs, opt_constraints, cfg)` — two-pass WLS + DCC/EWMA + Newey–West + shrinkage + STVU → `P.FactorModel`
  - `rolling_fundamental_models(returns, bs_list, window, opt_constraints, cfg)` — causal parallel rolling fundamental models
- **Out-of-sample risk evaluation (Ch 5):**
  - `qlike(var_hat, r)`, `vol_mse(var_hat, r)`, `bias_stat(var_hat, r)` — §5.1.1 Patton (2011) robust volatility losses & Connor–Goldberg–Korajczyk bias stat
  - `qdist(fms, returns)` — §5.1.2 Eq (5.1) multivariate Gaussian NLL via Woodbury + Matrix Determinant Lemma (zero $N \times N$ matrices, parallel `pmap`)
  - `portfolio_vol_eval(fms, weights, returns)` — out-of-sample QLIKE, MSE, bias stat & realized/predicted vol for arbitrary portfolio sequences
  - `mvp_test(fms, returns, b_vec)` — §5.2.1 Eq (5.2) minimum-variance portfolio test via Woodbury (`pmap`)
  - `mahalanobis_test(fms, returns)` — §5.2.2 Mahalanobis distance series $\nu_t$ & `MALV` (`pmap`)
  - `fmp_turnover(fms)` — §5.3.1 quadratic FMP turnover $\|P_t - P_{t-1}\|_F$ (`pmap`)
  - `beta_error(fms, returns, w_ref, half_life)` — §5.3.2 predicted vs EWMA realized asset beta `BETAERR` (zero $N \times N$ matrices)
  - `cross_sectional_r2(bs, returns, idio_vars)` — §5.3.3 weighted cross-sectional $R^2$

### Milestone 3 — Statistical Factor Models & Fast Subspace SVD (Ch 7)
- **Fast top-$K$ SVD kernel (`subspace_svd.bend`):**
  - Deterministic flat-`Array<F32>` subspace-iteration top-$K$ SVD (`svd_top_k`) with QR-stabilized power iterations for $K \ll \min(N, T)$, delegating to exact `L.svd_thin` when small.
- **Statistical estimation, RMT shrinkage & alignment (Ch 7):**
  - `pca_svd(returns, k, half_life, use_subspace)` — §7.1.1 & §7.5.1 time-weighted SVD/PCA
  - `ppca_fit(returns, k)` — §7.1.2 Eq (7.17–7.19) Probabilistic PCA MLE
  - `spiked_shrink_eigenvalues(lambdas, n, t, mode, k1, k2)` — §7.2.3–7.2.4 BBP/Donoho offset Eq (7.33), PPCA bulk-mean, and heavy-tail linear shrinkage
  - `select_k_threshold(lambdas, n, t, bulk_scale)` — §7.2.5 Eq (7.37) Marchenko–Pastur threshold
  - `select_k_gap(lambdas, k_max, use_log)` — §7.2.5 Eq (7.38) Onatski-style max eigenvalue / log gap
  - `select_k_bai_ng(singular_values, n, t, k_max)` — §7.2.5 Eq (7.39–7.40) Bai–Ng $IC_{p1}$ & $PC_{p1}$
  - `eigenfactor_turnover(b_prev, b_curr)` — §7.3.2 Eq (7.42) quadratic turnover $2(1 - |v_t^\top v_{t-1}|)$
  - `align_sign(b_prev, b_curr)`, `align_procrustes(fm_prev, fm_curr)` — §7.3.2 Eq (7.43) & §7.5.2 Procrustes / sign alignment
  - `subspace_distance(b1, b2)` — rotation-invariant subspace distance
  - `fit_statistical_model(returns, cfg)` — §7.5.1 two-stage fast/slow weighted statistical factor model → `P.FactorModel`
  - `impute_loadings_ts(asset_returns, factor_returns)`, `interpret_loadings(b_stat, characteristics)`, `impute_loadings_char(b_known, g_known, g_new, shrink)` — §7.4.2 & §7.5.2
  - `rolling_statistical_models(returns, window, cfg, align_mode)` — causal parallel rolling statistical models + alignment pass

### Milestone 4 — Formal Proofs, Numerical Verification, Benchmarks & Docs
- `LAWS.bend` & `PROOF.bend`: prove structural symmetry of all covariance estimators, strict causality of EWMA / winsorization / rolling estimators, no-lookahead pairing of Ch 5 evaluators (`fms[t]` with `returns[t + 1]`), parallel-sequential equivalence (`pmap_seq`), and dimension/parameter guards (`bend PROOF.bend --verdict` → `ALL PROOFS CHECK`, zero `@unsafe`, zero IO).
- `check.bend` & `check.py`: numerical cross-check against NumPy, SciPy, scikit-learn (`LedoitWolf`), and statsmodels (`cov_hac`).
- `bench/`: benchmark single-date and rolling multi-date workloads (1t & 8t `pmap`) against NumPy / SciPy / scikit-learn.
- `DESIGN.md`, `README.md`, `publish.bend`, `VERSION`, `LICENSE`.

## Dependencies
- `bend-quant-linalg@0.1.0.0`
- `bend-quant-portfolio@0.1.0.0`
- `bend-kit-f32array@0.2.1.0`
