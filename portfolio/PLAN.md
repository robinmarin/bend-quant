# portfolio: plan

> **Status:** Active implementation (`v0.1.0.0`).
> Built directly on published `bend-quant-linalg@0.1.0.0` and compatible with `bend-quant-signal@0.1.0.0`.
> Factor/risk model estimation (Paleologo Ch 4–7) is scoped for a separate `risk` package; `portfolio` takes a `FactorModel(B, Ω_f, Ω_ε)` as input and implements Paleologo Ch 4.5 and Ch 9–14.

## Pipeline placement

```
signal (published)     →  Step 1: cross-sectional IC, rank IC, causal signal transforms
linalg (published)     →  Dense linear algebra: Cholesky, Woodbury, QR, sym-eigen, SVD
risk (planned)         →  Step 2: fundamental & statistical factor/risk estimation (Ch 4–7)
portfolio (this pkg)   →  Steps 3–4: risk decomp, MVO, ADMM QP, hedging, Kelly/GZ, attribution (Ch 4.5, 9–14)
```

## Public API & Milestones

### Milestone 1 — Factor Model, Risk Decomposition & Analytical MVO (Ch 4.5, 9, 10.2.3, 10.3)
- **Types (`Data`):**
  - `FactorModel{b: L.Mat, cov_f: L.Mat, idio_var: L.Vec}` with smart constructor `FactorModel.new` (validates `N`, `K`, square `cov_f`, strictly positive `idio_var`)
  - `RiskDecomp{total_var, factor_var, idio_var, total_vol, factor_vol, idio_vol, pct_idio, exposures}`
  - `AlphaDecomp{factor_alpha: L.Vec, spanned: L.Vec, orth: L.Vec}`
- **Risk decomposition (Ch 4.5.2, 10.2.1):**
  - `exposures(fm, w)` — $b = B^\top w$
  - `cov_matvec(fm, w)` — $\Omega_r w = B (\Omega_f (B^\top w)) + \Omega_\varepsilon w$ in $O(NK + K^2)$
  - `risk_decomp(fm, w)` — factor vs. idio variance/vol, `% idio`, exposures
  - `active_risk(fm, w, w_bench)` — tracking error & decomposition of $w - w_{\text{bench}}$
  - `marginal_risk(fm, w)`, `risk_contrib(fm, w)` — Euler risk contributions summing to $\sigma(w)$
  - `herfindahl(w)`, `eff_breadth(w, idio_var)` — concentration $H(w)$ and effective breadth $\|\tilde{w}\|_1 / \|\tilde{w}\|_2$
- **Analytical portfolio construction (Ch 9, 10.2.3, 10.3, 11.3.1):**
  - `mvo_unconstrained(fm, alpha, risk_aversion)` — $\frac{1}{\rho} \Omega_r^{-1} \alpha$ via Woodbury
  - `mvo_target_vol(fm, alpha, target_vol)` — Eq (9.3): $\frac{\sigma}{\sqrt{\alpha^\top \Omega_r^{-1} \alpha}} \Omega_r^{-1} \alpha$
  - `mvo_robust(fm, alpha, risk_aversion, tau_sq)` — Ch 10.2.3 diagonal regularization $(\Omega_r + \tau^2 I)^{-1} \alpha / \rho$ (unifies uncertain alpha, robust factors, robust Frobenius covariance)
  - `fmp(fm)` — Eq (9.12): Factor-Mimicking Portfolios $P = \Omega_\varepsilon^{-1} B (B^\top \Omega_\varepsilon^{-1} B)^{-1}$ via thin QR of $D^{-1/2} B$
  - `alpha_decompose(fm, alpha)` — $\alpha = B \lambda + \hat{\alpha}_\perp$ under $\Omega_\varepsilon^{-1}$ via thin QR + `project_orth`
  - `mvo_factor_neutral(fm, alpha, target_vol)` — Eq (9.18): pure-alpha MVO with exact $B^\top w = 0$
  - `mvo_factor_space(fm, lambda_f, risk_aversion)` — Ch 9.3.1: $w^* = P (\frac{1}{\rho} \Omega_f^{-1} \lambda_f)$
  - `mvo_trade_quad(fm, alpha, w0, cost_quad, risk_aversion)` — Eq (11.7): single-period quadratic impact closed form $(\rho \Omega_r + C)^{-1}(\alpha + C w_0)$ via Woodbury
  - `sre(fm_est, alpha_est, fm_true, alpha_true)` — Ch 10.3: Sharpe Ratio Efficiency
- **IO (`io.bend`, isolated from `PROOF.bend`):** `FactorModel.load`

### Milestone 2 — Constrained & Market-Impact-Aware MVO via Woodbury-ADMM (Ch 10.2, 11)
- **Convex optimization problem:**
  $$\min_{w \in \mathbb{R}^N} \frac{\rho}{2} w^\top \Omega_r w - \alpha^\top w + \frac{1}{2} (w - w_0)^\top \operatorname{diag}(c_2)(w - w_0) + \sum_i c_{1,i} |w_i - w_{0,i}|$$
  subject to box bounds $l_w \le w \le u_w$, linear/factor bounds $l_c \le A w \le u_c$, and optional GMV cap $\|w\|_1 \le G$.
- **Woodbury-preconditioned ADMM (`mvo_constrained`):**
  - Pre-factors $I_{K+M} + U^\top \tilde{D}^{-1} U = L_C L_C^\top$ **once** before the loop where $U = [\sqrt{\rho} B L_f, \sqrt{\mu} A^\top]$.
  - Runs the iteration loop in flat `Array<F32>` with over-relaxation ($\gamma = 1.6$), elementwise box projection, soft-thresholding (L1 trade cost), optional $\ell_1$-ball bisection (GMV), and primal/dual residual termination.
  - Zero $N \times N$ matrices formed; $O(N(K+M))$ per iteration.
- **Transaction cost helpers (Ch 11.1):** `trade_cost_linear`, `trade_cost_quad`, `trade_cost_power` (Almgren–Chriss / Kyle power-law slippage).

### Milestone 3 — Hedging & Dynamic Risk Sizing (Ch 12, 13)
- **Hedging (Ch 12):**
  - `hedge_ratio_model(fm, w_core, w_hedge)` — Eq (12.2, 12.4): optimal single-instrument hedge ratio $-\beta(r_c, r_h)$
  - `hedge_instruments(fm, w_core, h_mat)` — multi-instrument min-variance hedge $-(H^\top \Omega_r H)^{-1} (H^\top \Omega_r w_c)$ accounting for factor & idio risk of hedge instruments
  - `hedge_factor_exact(fm, w_core)` — Ch 12.2.1 Procedure 12.2: $-P b_c$
  - `hedge_beta_shrink(w, beta_hat, se_beta)` & `hedge_beta_shrink_cov(w, beta_hat, cov_eta)` — Eq (12.6–12.7): optimal beta-error shrinkage $y_h^* = \max(0, 1 - w^\top \Omega_\eta w / (w^\top \hat{\beta})^2)$
  - `hedge_track_series(fm, beta_hat, se_beta, mu_h, sigma_h)` — Ch 12.4: regularized tracking portfolio for a non-tradeable time series
- **Dynamic risk sizing (Ch 13):**
  - `kelly_fraction(mu, sigma)`, `kelly_fraction_discrete(mu, sigma)`, `fractional_kelly(mu, sigma, frac)`
  - `grossman_zhou(mu, sigma, max_dd, cur_dd)` — Eq (13.13, 13.15)
  - `grossman_zhou_path(returns, mu, sigma, max_dd)` — strictly causal drawdown-controlled sizing scan

### Milestone 4 — Ex-Post Performance Attribution & Causal Backtest (Ch 14)
- **Holdings-based attribution & uncertainty (Ch 14.1–14.2):**
  - `estimate_factor_returns(fm, r)` — cross-sectional WLS $\hat{f} = (B^\top \Omega_\varepsilon^{-1} B)^{-1} B^\top \Omega_\varepsilon^{-1} r$
  - `attribute_period(fm, w, r, f_ret, realized_pnl)` — trading PnL, total & per-factor PnL, total & per-asset idio PnL, attribution error variance
  - `attrib_error_var(fm, w)` — Ch 14.2.2: $b^\top (B^\top \Omega_\varepsilon^{-1} B)^{-1} b$
- **Maximal & nested attribution (Ch 14.3):**
  - `maximal_attribution(cov_f, b, f_ret, subset)` — Schur complement rotation pushing maximal PnL & variance into factor subset $S$
  - `nested_attribution(cov_f, b, f_ret, groups)` — sequential maximal attribution over a partition of factor groups
- **Selection vs. sizing IR decomposition (Ch 14.4):**
  - `selection_sizing(w, eps, idio_var)` — exact decomposition $\widehat{\text{IR}}_t = \text{selection}_t \cdot \text{diversification}_t + \text{sizing}_t$ plus long/short selection split
- **Causal multi-period backtest & attribution:**
  - `forward_pnl(weights, returns)` — pairs weights at date $t$ with returns at date $t + 1$ (matches `signal`'s convention; parallelized via `pmap`)
  - `forward_attribute(fms, weights, returns, f_rets)` — causal multi-period attribution over dates

### Milestone 5 — Benchmarks, Docs & Publish
- Cross-check all numerical outputs in `check.py` against NumPy / SciPy / convex QP solver.
- Verify all structural & causal laws in `PROOF.bend` with `bend PROOF.bend --verdict` (`ALL PROOFS CHECK`, zero `@unsafe`, zero IO).
- Benchmark CPU performance (including ADMM on $N = 500..2000, K = 30..50$) in `bench/`.
- Write `DESIGN.md`, `README.md`, `publish.bend`, `VERSION`, `LICENSE` and publish `bend-quant-portfolio@0.1.0.0`.

## Provable Laws (`LAWS.bend` & `PROOF.bend`)
1. **FactorModel validation:** `FactorModel.new` rejects dimension mismatches (`b.m != idio_var.n`, `b.n != cov_f.m`, non-square `cov_f`), and whenever it succeeds guarantees `b.m == idio_var.n`, `b.n == cov_f.m == cov_f.n`.
2. **Dimension guards & output shapes:** Every public function returns `None` on incompatible dimensions/bounds, and guarantees exact output vector/matrix dimensions (`N`, `K`, `N x K`, `|S|`, etc.) on success.
3. **No-lookahead / causality:**
   - `forward_pnl_row`: period `t` pairs weights row `t` with return row `t + 1` (same-day pairing is structurally impossible).
   - `forward_attrib_row`: period `t` pairs model/weights at `t` with return row `t + 1`.
   - `gz_path_causal`: first `k` outputs of `grossman_zhou_path` depend only on the first `k` input returns (`scan_causal`).
4. **Parallel-sequential equivalence:** `pmap_seq` proves parallel multi-date batch evaluation equals sequential evaluation for every length.
5. **Attribution partition validity:** `maximal_attribution` rejects out-of-bounds or duplicate subset indices and preserves exact partition sizes (`|S|` and `K - |S|`).

## Dependencies
- `bend-quant-linalg@0.1.0.0` (imported directly from BendHub)
- `bend-kit-f32array@0.2.1.0` (for flat `Array<F32>` ADMM inner loop & `io.bend`)
- Compatible row layout (`List<&2, List<&2, F32>>`) with `bend-quant-signal@0.1.0.0`
