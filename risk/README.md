# risk

Factor model transformations, out-of-sample risk evaluation, fundamental factor models & covariance estimation (Ledoit–Wolf, DCC, STVU, Newey–West/Cohen HAC, Cai clustering, causal log-MAD winsorization, multi-region linking, currency rebasing), and statistical factor models (PCA/SVD, fast subspace SVD, PPCA, RMT shrinkage, Bai–Ng, Procrustes alignment) in Bend, following Giuseppe Paleologo's *The Elements of Quantitative Investing* (Chapters 4–7). [DESIGN.md](DESIGN.md) explains the numerical and architectural choices, and [bench/README.md](bench/README.md) has the timings behind them.

```bend
import bend-quant-risk@0.1.1.0/risk.bend as R
import bend-quant-risk@0.1.1.0/io.bend as RI
```

From a clone, import `./risk/risk.bend` and `./risk/io.bend` instead. All public types are `Data` and operate directly on `bend-quant-linalg@0.1.1.0`'s `Vec`/`Mat` and `bend-quant-portfolio@0.1.1.0`'s `FactorModel` with zero conversion boilerplate. Return panels are `T × N` (`L.Mat`), where row `t` is the one-period return over `(t - 1, t]`.

The types and defs in the API table below are the public ones. Every other def is internal: the laws and proofs name them, and they can change in any version.

## What is proved and what is tested

`LAWS.bend` states 47 laws and `PROOF.bend` proves all of them under `bend PROOF.bend --verdict` (Lean-verified BendTT kernel) with zero `@unsafe` and no IO imports: 24 structural laws over every input and 23 dimension/parameter guards.

Structural laws (every input):

- **Exact symmetry (11 laws):** `mirror_upper_sym`, `symmetrize_sym`, `sample_cov_sym`, `ewma_cov_sym`, `shrink_to_identity_sym`, `ledoit_wolf_sym`, `psd_project_sym`, `dcc_cov_sym`, `cov_newey_west_sym`, `cov_autocorr_cohen_sym` and `link_models_ir_sym` prove bit-for-bit `L.Mat.get(M, i, j) == L.Mat.get(M, j, i)` for every covariance estimator.
- **Strict causality (4 laws):** `scan_causal`, `winsorize_log_mad_causal`, `make_windows_get` and `make_windows_causal`. The first `k` output rows of `winsorize_log_mad` depend only on the first `k` input rows. Window `j` of width `w` is rows `j .. j + w - 1`, so the first `k` windows depend only on the first `k + w - 1` rows.
- **No-lookahead evaluation (7 laws):** `qdist_pairs`, `mahalanobis_pairs`, `mvp_pairs` and `portfolio_vol_pairs` show that each public evaluator runs its per-period metric over exactly the pairs from `pair_oos_fm` / `pair_oos_fmw`. `pair_oos_fm_row` and `pair_oos_fmw_row` show that pair `i` is `fms[i]` (and `weights[i]`) with `returns[i + 1]`. `oos_returns_row` covers rolling models: row `1 + j` of `oos_returns(R, w)` is row `j + w` of `R`, the first row after model `j`'s window.
- **Parallel-sequential equivalence (2 laws):** `pmap_seq` and `pseq_get` prove that fork-join `pmap` (64 tasks at $T \ge 64$) gives the same list as sequential `pseq` for every input.

Dimension & parameter guards (23 laws): `symmetrize`, `qdist`, `mvp_test`, `rotate_model`, `project_model`, `pushout_loadings`, `group_risk_decomp`, `qlike`, `vol_mse`, `bias_stat`, `mahalanobis_test`, `beta_error`, `cross_sectional_wls`, `cross_sectional_constrained`, `cross_sectional_ridge`, `fit_fundamental_model`, `rebase_currency`, `pca_svd`, `eigenfactor_turnover`, `align_sign`, `subspace_distance`, `impute_loadings_ts` and `rolling_statistical_models` return `None` on incompatible headers or invalid parameters. They compare headers only.

To score rolling models out of sample, pair them with `oos_returns`, not the full return matrix:

```bend
match R.rolling_statistical_models(rets, w, cfg, 0) R.oos_returns(rets, w):
  case Some{fms} Some{oos}:
    R.qdist(fms, oos)   # model j (rows j .. j + w - 1) scored on row j + w
```

Bend's checker does not reduce `F32` arithmetic, so numerical accuracy is verified against **NumPy, SciPy (`linalg`, `special.digamma`, `orthogonal_procrustes`), scikit-learn (`LedoitWolf`), and statsmodels (`weights_bartlett`)** in `check.py` (all checks passing to `2.6e-7`–`2.0e-5`).

## Example

Fit a two-stage weighted statistical factor model (`K = 15`) on a `250 × 500` return panel and evaluate out-of-sample QDIST or hand `model` straight to `bend-quant-portfolio`:

```bend
import Base
import bend-quant-linalg@0.1.1.0/linalg.bend as L
import bend-quant-portfolio@0.1.1.0/portfolio.bend as P
import bend-quant-risk@0.1.1.0/risk.bend as R
import bend-quant-risk@0.1.1.0/io.bend as RI

def fit_and_summarize(rr: Result<&1, &1, U32 & String, L.Mat>) -> String:
  match rr:
    case Done{rets}:
      match R.fit_statistical_model(rets, R.StatConfig.default(15)):
        case Some{R.StatModelFit{P.FactorModel{_, _, L.Vec{n, _}}, _, _, L.Vec{k, _}}}:
          "fitted statistical FactorModel: N=" ++ U32.show(n) ++ " K=" ++ U32.show(k) ++ "\n"
        case None{}:
          "fit failed\n"
    case Fail{_}:
      "load failed\n"

def main() -> IO(Unit):
  do IO<Unit>:
    rr : Result<&1, &1, U32 & String, L.Mat> <- RI.Returns.load("returns.f32", 250, 500)
    IO.print(fit_and_summarize(rr))
```

`check.bend` is a complete CLI exercising every public function in the package.

## API

### Types (`Data`)

- `R.GroupRisk{group_cov, group_vars, group_shares, group_mcr, total_factor_var, total_factor_vol}`
- `R.VolEval{qlike, vol_mse, bias_stat, realized_vol, mean_pred_vol, count}`
- `R.QDistResult{mean_qdist, total_qdist, per_period}`
- `R.MahalanobisResult{nu_series, mean_nu, malv}`
- `R.MvpResult{realized_var, realized_vol, mean_pred_vol, qlike, vol_mse, bias_stat, returns, pred_vars}`
- `R.TurnoverResult{mean_turnover, per_period}`
- `R.BetaErrResult{total_err, mean_err, per_period}`
- `R.ShrinkResult{cov, shrinkage, target_diag}`
- `R.CorrPair{i, j, corr}`
- `R.RebaseResult{c_loadings, cov_c}`
- `R.CSConstraint{c_mat, d_vec}`
- `R.CSRegResult{f_ret, resid, est_cov}`
- `R.FactorSeries{f_rets, resid}`
- `R.FundConfig{hl_vol, hl_corr, hl_idio, nw_lags, shrink_f, shrink_idio, hl_stvu, use_stvu, debias, eig_floor}` (`R.FundConfig.default()`)
- `R.FundModelFit{model: P.FactorModel, f_rets, resid}`
- `R.PcaResult{loadings, f_rets, singular_values, eigenvalues}`
- `R.BaiNgResult{k_ic, k_pc, ic_values, pc_values}`
- `R.EigenTurnover{per_factor, mean_turnover}`
- `R.StatConfig{k, stage1_p, hl_fast, hl_slow, shrink_mode, shrink_k1, shrink_k2, shrink_idio, use_subspace, eig_floor}` (`R.StatConfig.default(k)`)
- `R.StatModelFit{model: P.FactorModel, f_rets, resid, singular_values}`

### Ch 4: Factor model transformations & group risk

| def | result |
|---|---|
| `R.rotate_model(fm, c_mat)` | Eq (4.3): exact covariance-preserving rotation $(B C^{-1}, C \Omega_f C^\top, \Omega_\varepsilon)$ |
| `R.rotate_identity_cov(fm)` | Ch 4.4.1: rotate to $\tilde{\Omega}_f = I_K$ via Cholesky |
| `R.rotate_orthonormal_loadings(fm)` | Ch 4.4.1: rotate to $\tilde{B}^\top \tilde{B} = I_K$ via thin QR |
| `R.rotate_zscore_loadings(fm, a_vec, shifts, scales)` | Eq (4.4): covariance-preserving shift/scale z-score standardization when $B a = \mathbf{1}$ |
| `R.project_model(fm, a_mat)` | Ch 4.4.2: project $K$ factors onto $P$ factors $A$, absorbing residual variance into $\Omega_\varepsilon$ |
| `R.pushout_loadings(b, a_mat, idio_var)` | Eq (4.5): orthogonalize $A$ against $B$ under $\Omega_\varepsilon^{-1}$ via thin QR |
| `R.pushout_model(fm, a_mat, cov_g, new_idio)` | augment `fm` with orthogonalized push-out factors $H$ |
| `R.group_risk_decomp(fm, w, groups)` | Ch 4.5.2: partitioned factor-group covariance, variance shares (summing to 1), and group MCR |

### Ch 5: Out-of-sample risk evaluation

| def | result |
|---|---|
| `R.qlike(var_hat, r)`, `R.vol_mse(var_hat, r)`, `R.bias_stat(var_hat, r)` | Patton (2011) QLIKE, volatility MSE, and dimensionless bias statistic |
| `R.qdist(fms, returns)` | Eq (5.1): Gaussian negative log-likelihood $r_{t+1}^\top \Omega_t^{-1} r_{t+1} + \log|\Omega_t| + N \log(2\pi)$ via Woodbury + `pmap` |
| `R.mahalanobis_test(fms, returns)` | Ch 5.2.2: Mahalanobis $\nu_t = \frac{1}{N} r_{t+1}^\top \Omega_t^{-1} r_{t+1}$, mean, and MALV variance via Woodbury + `pmap` |
| `R.mvp_test(fms, returns, b_vec)` | Eq (5.2): constrained minimum-variance portfolio OOS realized/predicted vol, QLIKE, MSE, bias via Woodbury + `pmap` |
| `R.portfolio_vol_eval(fms, weights, returns)` | OOS realized vs. predicted volatility metrics for arbitrary weight panel `weights` (`pmap`) |
| `R.fmp_turnover(fms)` | Ch 5.3.1: FMP Frobenius turnover $\|P_t - P_{t-1}\|_F$ (`pmap`) |
| `R.beta_error(fms, returns, w_ref, half_life)` | Ch 5.3.2: predicted vs. EWMA realized beta error in $O(TN)$ with zero $N \times N$ matrices |
| `R.cross_sectional_r2(bs, returns, idio_vars)` | Ch 5.3.3: $\Omega_\varepsilon^{-1}$-weighted cross-sectional $R^2$ (`pmap`) |

### Ch 6: Covariance estimation, cross-sectional WLS & fundamental models

| def | result |
|---|---|
| `R.symmetrize(m)`, `R.ewma_weights(t, half_life)` | exact upper-triangle mirroring; normalized exponential weights ($\lambda = 2^{-1/\text{hl}}$) |
| `R.sample_cov(x, center)`, `R.ewma_cov(x, half_life, center)` | Bessel- / ESS-corrected (when centered) or uncentered covariance |
| `R.shrink_to_identity(cov, rho)` | linear shrinkage $(1 - \rho)\Sigma + \rho \frac{\operatorname{tr}(\Sigma)}{K} I_K$ |
| `R.ledoit_wolf_cov(x, center)` | Ch 6.3.1: analytical Ledoit–Wolf (2004) shrinkage in $O(TK + K^2)$ |
| `R.psd_project(a, eig_floor)` | spectral projection enforcing $\lambda_{\min} \ge \text{eig\_floor}$ |
| `R.debias_factor_cov(cov_f_raw, b, idio_var, eig_floor)` | Eq (6.5): subtract WLS estimation-error covariance $(B^\top \Omega_\varepsilon^{-1} B)^{-1}$ + PSD project |
| `R.dcc_cov(f_rets, hl_vol, hl_corr)` | Ch 6.3.2: causal EWMA vol standardization + slow EWMA correlation + fast final vol |
| `R.stvu_factor_multiplier(f_rets, cov_f, hl_fast, linear)`, `R.stvu_adjust_cov(...)` | Eq (6.8) exact log-$\chi^2$ digamma STVU and Eq (6.11) linear vol-ratio STVU |
| `R.cov_newey_west(x, l_max, half_life)`, `R.cov_autocorr_cohen(x, l_max, half_life)` | Ch 6.3.4: Bartlett (Newey–West) & Cohen autocorrelation-adjusted covariance (equal or EWMA) |
| `R.idio_var_ewma(eps, half_life)`, `R.idio_var_shrink(idio_var, rho)`, `R.idio_stvu(eps, idio_var, evw, hl_fast)` | Ch 6.4: idiosyncratic variance EWMA, cross-sectional shrinkage, and event-weighted STVU |
| `R.cai_threshold(n, t, k_const)`, `R.idio_corr_clusters(eps, threshold)` | Ch 6.4.4: Cai–Liu universal threshold and thresholded off-diagonal residual correlation pairs |
| `R.winsorize_log_mad(returns, window, d_max)` | Ch 6.5: strictly causal rolling log-MAD outlier winsorization |
| `R.link_models_ir(local_covs, joint_cov, rho)` | Ch 6.6.1: multi-region / asset-class covariance linking preserving local blocks via `L.spd_pow` |
| `R.rebase_currency(c_mat, cov_c, target_idx)` | Eq (6.14–6.16): exact numeraire currency rebasing |
| `R.cross_sectional_wls(b, r, weights)` | thin-QR WLS regression returning $\hat{f}$, $\hat{\varepsilon}$, and $(B^\top W B)^{-1}$ |
| `R.cross_sectional_constrained(b, r, weights, cons)` | Ch 6.2.1: Heston–Rouwenhorst KKT-constrained WLS $C^\top f = d$ (handles rank-deficient $B$) |
| `R.cross_sectional_ridge(b, r, weights, delta)`, `R.cross_sectional_ridgeless(b, r, weights, tol)` | Ch 6.2.1: augmented-QR ridge and minimum-norm pseudoinverse WLS |
| `R.estimate_factor_series(bs, returns, weights_list, opt_cons)` | multi-period cross-sectional WLS factor & residual panels (`pmap`) |
| `R.fit_fundamental_model(returns, bs, opt_cons, cfg)` | end-to-end 2-pass fundamental factor model estimator returning `FundModelFit` |
| `R.rolling_fundamental_models(returns, bs_list, window, opt_cons, cfg)` | causal rolling-window fundamental factor models (`pmap`) |

### Ch 7: Statistical factor models, PCA/SVD, RMT & alignment

| def | result |
|---|---|
| `R.pca_svd(returns, k, half_life, use_subspace)` | equal-weighted or EWMA PCA via exact `L.svd_thin` or fast deterministic `subspace_svd` |
| `R.ppca_fit(returns, k, eig_floor)` | Eq (7.17–7.19): Probabilistic PCA (Tipping & Bishop 1999) returning `P.FactorModel` |
| `R.spiked_shrink_eigenvalues(lambdas, n, t, mode, k1, k2, eig_floor)` | Ch 7.2.3–7.24: none / BBP–Donoho Eq (7.33) / PPCA bulk / heavy-tail linear shrinkage |
| `R.select_k_threshold`, `R.select_k_gap`, `R.select_k_bai_ng` | Eq (7.37–7.40): Marchenko–Pastur bulk edge, max linear/log eigengap, Bai–Ng `IC_p1` & `PC_p1` |
| `R.eigenfactor_turnover(b_prev, b_curr)` | Ch 7.3.2: sign-invariant quadratic eigenfactor turnover $2(1 - |\cos\theta_j|)$ |
| `R.align_sign(b_prev, b_curr)`, `R.align_procrustes(fm_prev, fm_curr)` | Eq (7.43): column sign alignment and covariance-preserving orthogonal Procrustes alignment |
| `R.subspace_distance(b1, b2)` | rotation-invariant subspace distance $\sqrt{\max(0, 1 - \|Q_1^\top Q_2\|_F^2 / K)} \in [0, 1]$ |
| `R.fit_statistical_model(returns, cfg)` | Ch 7.5.1: two-stage EWMA-weighted statistical factor model with RMT shrinkage & optional subspace SVD |
| `R.impute_loadings_ts`, `R.interpret_loadings`, `R.impute_loadings_char` | Ch 7.4.2 & 7.5.2: time-series and characteristic-based loading imputation & factor interpretation |
| `R.rolling_statistical_models(returns, window, cfg, align_mode)` | causal rolling-window statistical models (`pmap`) with optional sign (`1`) or Procrustes (`2`) alignment |
| `R.oos_returns(returns, window)` | `Maybe<&2, Mat>`: `returns` without its first `window - 1` rows, so the evaluators score rolling model `j` on row `j + window` |

### IO (`io.bend`)

| def | result |
|---|---|
| `RI.Returns.load(path, t, n)` | load row-major little-endian float32 `T × N` return panel |
| `RI.LoadingsSeries.load(path, t, n, k)` | load contiguous `(T, N, K)` little-endian float32 loadings series into `List<&2, L.Mat>` |

## Checks & timings

```sh
cd risk
bend PROOF.bend --verdict                  # 47/47 Lean-verified BendTT proofs (0 @unsafe, 0 IO)
python3 check.py                           # numerical cross-check vs NumPy/SciPy/sklearn/statsmodels
cd bench && mkdir -p out
bend bench_risk.bend -o out/bench_risk
python3 run_bench.py --threads 1
python3 run_bench.py --threads 8 --skip-py
```
