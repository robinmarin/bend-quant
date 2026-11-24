# portfolio

Factor risk decomposition, analytical and constrained mean-variance optimization (Woodbury-preconditioned ADMM), hedging, dynamic risk sizing (Kelly & Grossman–Zhou), and ex-post performance attribution in Bend, following Giuseppe Paleologo's *The Elements of Quantitative Investing* (Ch 4.5, 9–14). [DESIGN.md](DESIGN.md) explains the solver and numerical choices, and [bench/README.md](bench/README.md) has the timings behind them.

```bend
import bend-quant-portfolio@0.1.1.0/portfolio.bend as P
import bend-quant-portfolio@0.1.1.0/io.bend as PI
```

From a clone, import `./portfolio/portfolio.bend` and `./portfolio/io.bend` instead. All public types are `Data` and operate directly on `bend-quant-linalg@0.1.0.0`'s `Vec` and `Mat` (sharing `List<&2, List<&2, F32>>` rows with `bend-quant-signal@0.1.0.0` with zero copying). `io.bend` wraps `bend-quant-linalg@0.1.0.0/io.bend` to load `FactorModel` binary files.

The types and defs in the API table below are the public ones. Every other def is internal: the laws and proofs name them, and they can change in any version.

## What is proved and what is tested

`LAWS.bend` states 36 laws and `PROOF.bend` proves all of them with zero `@unsafe` and no IO imports: 7 structural laws over every input, 28 dimension guards, and 1 fixed example.

Structural laws (every input):

- **FactorModel validation (`fm_new_sound`, `fm_new_rows_ok`):** whenever `FactorModel.new` succeeds, the headers agree (`B` is `N × K`, `cov_f` is `K × K`, `idio_var` has length `N`) and every header matches its rows. Models built with `FactorModel{...}` directly skip this check.
- **No-lookahead forward PnL (`forward_pnl_row`):** whenever the headers match, period `i` of `forward_pnl(W, R)` pairs weight row `i` with return row `i + 1`. Row `j` of `R` is the return over `(j - 1, j]`, matching `signal`'s convention, so same-day pairing cannot be written with this function.
- **No-lookahead forward attribution (`forward_attribute_row`):** whenever the headers match, period `i` of `forward_attribute` attributes model `i` and weight row `i` against return row `i + 1` and factor-return row `i + 1`.
- **Strict causality (`scan_causal`, `gz_path_causal`):** for every `k`, the first `k` states of `grossman_zhou_path(returns, ...)` depend only on the first `k` returns.
- **Parallel-sequential equivalence (`pmap_seq`):** the fork-join `pmap` (64 tasks at $T \ge 64$) gives the same list as the sequential `pseq` for every length.

Dimension guards (28 laws): `FactorModel.new` (`fm_new_mismatch_n`, `fm_new_mismatch_k`, `fm_new_nonsquare_cov`), `forward_pnl`, `exposures`, `cov_matvec`, `risk_decomp`, `active_risk`, `marginal_risk`, `risk_contrib`, `eff_breadth`, `mvo_trade_quad`, `fmp`, `alpha_decompose`, `mvo_factor_neutral`, `mvo_factor_space`, `trade_cost_linear`, `trade_cost_quad`, `trade_cost_power`, `mvo_constrained` (3 laws), `hedge_instruments`, `hedge_beta_shrink`, `hedge_track_series`, `attribute_period`, `maximal_attribution`, and `selection_sizing` return `None` when headers don't fit. They compare headers only.

Fixed example: `fm_new_short_rows` (a `B` whose header claims more rows than it has is rejected).

Bend's checker does not reduce `F32` arithmetic, so numerical accuracy is verified against NumPy and SciPy (`SLSQP`) in `check.py` instead.

## Example

Load a factor model (`B` $N \times K$, `cov_f` $K \times K$, `idio_var` $N$) and expected returns `alpha`, then compute a factor-neutral pure-alpha portfolio and decompose its risk:

```bend
import Base
import bend-quant-linalg@0.1.0.0/linalg.bend as L
import bend-quant-linalg@0.1.0.0/io.bend as LI
import bend-quant-portfolio@0.1.1.0/portfolio.bend as P
import bend-quant-portfolio@0.1.1.0/io.bend as PI

def summarize(rfm: Result<&1, &1, U32 & String, P.FactorModel>, ra: Result<&1, &1, U32 & String, L.Vec>) -> String:
  match rfm ra:
    case Done{+fm} Done{alpha}:
      match P.mvo_factor_neutral(fm, alpha, 0.10):
        case Some{w}:
          match P.risk_decomp(fm, w):
            case Some{P.RiskDecomp{_, _, _, tvol, _, _, pct_idio, _}}:
              "vol=" ++ F32.show(tvol) ++ " pct_idio=" ++ F32.show(pct_idio)
            case None{}:
              "risk failed"
        case None{}:
          "mvo failed"
    case _ _:
      "load failed"

def main() -> IO(Unit):
  do IO<Unit>:
    rfm : Result<&1, &1, U32 & String, P.FactorModel> <- PI.FactorModel.load("b.f32", "cov_f.f32", "idio.f32", 500, 30)
    ra : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load("alpha.f32", 500)
    IO.print(summarize(rfm, ra))
```

`check.bend` is a complete CLI exercising every operation in the library.

## API

### Types (`Data`)

- `P.FactorModel{b: L.Mat, cov_f: L.Mat, idio_var: L.Vec}`
- `P.RiskDecomp{total_var, factor_var, idio_var, total_vol, factor_vol, idio_vol, pct_idio, exposures}`
- `P.AlphaDecomp{factor_alpha, spanned, orth}`
- `P.Constraints{l_w, u_w, a, l_c, u_c, gmv_max}`
- `P.TradeCosts{linear, quad}`
- `P.OptConfig{max_iters, abs_tol, rel_tol, rho_admm, relax}`
- `P.OptResult{weights, iters, primal_res, dual_res, converged}`
- `P.HedgeShrink{raw_exposure, error_var, shrink_factor, hedge_size}`
- `P.DrawdownState{wealth, high_watermark, drawdown, fraction}`
- `P.PeriodAttrib{position_pnl, trading_pnl, factor_pnl, idio_pnl, factor_contrib, idio_contrib, error_var}`
- `P.MaxAttrib{adjusted_betas, subset_pnl, resid_f_ret, resid_pnl, resid_cov}`
- `P.NestedGroup{adjusted_betas, pnl}`
- `P.SelectionSizing{ir, selection, diversification, sizing, sel_long, sel_short, q_long, q_short}`

### Factor model & risk decomposition (Ch 4.5, 10.2.1)

| def | result |
|---|---|
| `P.FactorModel.new(b, cov_f, idio_var)` | `Maybe<&2, FactorModel>`; validates `N`, `K`, square `cov_f`, headers against rows, and `idio_var > 0` |
| `PI.FactorModel.load(b_path, cov_f_path, idio_path, n, k)` | `IO(Result<..., FactorModel>)` from little-endian float32 files |
| `P.exposures(fm, w)` | `Maybe<&2, L.Vec>` $b = B^\top w$ |
| `P.cov_matvec(fm, w)` | `Maybe<&2, L.Vec>` implicit $\Omega_r w = B(\Omega_f(B^\top w)) + \Omega_\varepsilon w$ in $O(NK + K^2)$ |
| `P.risk_decomp(fm, w)` | `Maybe<&2, RiskDecomp>` total/factor/idio variance & vol, `% idio`, exposures |
| `P.active_risk(fm, w, w_bench)` | `Maybe<&2, RiskDecomp>` tracking error & decomposition of $w - w_{\text{bench}}$ |
| `P.marginal_risk(fm, w)`, `P.risk_contrib(fm, w)` | `Maybe<&2, L.Vec>` $(\Omega_r w)/\sigma(w)$ and Euler contributions summing to $\sigma(w)$ |
| `P.herfindahl(w)`, `P.eff_breadth(w, idio_var)` | concentration $\|w\|_2^2 / \|w\|_1^2$ and vol-weighted effective breadth $\|\tilde{w}\|_1 / \|\tilde{w}\|_2$ |

### Analytical & constrained portfolio construction (Ch 9, 10, 11)

| def | result |
|---|---|
| `P.mvo_unconstrained(fm, alpha, risk_aversion)` | $\frac{1}{\rho} \Omega_r^{-1} \alpha$ via Woodbury |
| `P.mvo_target_vol(fm, alpha, target_vol)` | Eq (9.3): $\frac{\sigma}{\sqrt{\alpha^\top \Omega_r^{-1} \alpha}} \Omega_r^{-1} \alpha$ |
| `P.mvo_robust(fm, alpha, risk_aversion, tau_sq)` | Ch 10.2.3: $\frac{1}{\rho} (\Omega_r + \tau^2 I)^{-1} \alpha$ (uncertain alpha / robust factor / Frobenius covariance) |
| `P.mvo_trade_quad(fm, alpha, w0, cost_quad, risk_aversion)` | Eq (11.7): $(\rho \Omega_r + \operatorname{diag}(c_2))^{-1}(\alpha + c_2 \odot w_0)$ |
| `P.fmp(fm)` | Eq (9.12): Factor-Mimicking Portfolios $P = \Omega_\varepsilon^{-1} B (B^\top \Omega_\varepsilon^{-1} B)^{-1}$ via thin QR |
| `P.alpha_decompose(fm, alpha)` | $\alpha = B \lambda + \hat{\alpha}_\perp$ under $\Omega_\varepsilon^{-1}$ |
| `P.mvo_factor_neutral(fm, alpha, target_vol)` | Eq (9.18): pure-alpha MVO with exact $B^\top w = 0$ |
| `P.mvo_factor_space(fm, lambda_f, risk_aversion)` | Ch 9.3.1: $w^* = P (\frac{1}{\rho} \Omega_f^{-1} \lambda_f)$ |
| `P.sre(fm_est, alpha_est, fm_true, alpha_true)` | Ch 10.3: Sharpe Ratio Efficiency |
| `P.mvo_constrained(fm, alpha, w0, cons, costs, risk_aversion, cfg)` | Woodbury-preconditioned ADMM convex QP + L1 solver (box, linear/factor bounds, GMV cap, L1+L2 trade costs) |
| `P.OptConfig.default()`, `P.Constraints.box(lw, uw)`, `P.TradeCosts.zero(n)` | convenience constructors |
| `P.trade_cost_linear(w, w0, c1)`, `P.trade_cost_quad(w, w0, c2)` | linear spread and quadratic market impact costs |
| `P.trade_cost_power(w, w0, kappa, sigma, adv, beta)` | Ch 11.1.1: power-law impact $\sum_i \kappa \sigma_i (|\Delta w_i| / \text{ADV}_i)^\beta |\Delta w_i|$ |

### Hedging & dynamic risk sizing (Ch 12, 13)

| def | result |
|---|---|
| `P.hedge_ratio_model(fm, w_core, w_hedge)` | Eq (12.2, 12.4): optimal single-instrument hedge size $-\beta(r_c, r_h)$ |
| `P.hedge_instruments(fm, w_core, h_mat)` | multi-instrument min-variance hedge $-(H^\top \Omega_r H)^{-1} (H^\top \Omega_r w_c)$ |
| `P.hedge_factor_exact(fm, w_core)` | Ch 12.2.1: exact zero-exposure FMP hedge $-P (B^\top w_c)$ |
| `P.hedge_beta_shrink(w, beta_hat, se_beta)` | Eq (12.6–12.7): optimal beta-error shrinkage with diagonal error variances |
| `P.hedge_beta_shrink_cov(w, beta_hat, cov_eta)` | Ch 12.3 step 4: beta-error shrinkage with general error covariance $\Omega_\eta$ |
| `P.hedge_track_series(fm, beta_hat, se_beta, mu_h, sigma_h)` | Ch 12.4: regularized tracking portfolio for a non-tradeable time series |
| `P.kelly_fraction(mu, sigma)`, `P.kelly_fraction_discrete(mu, sigma)` | $\mu/\sigma^2$ and $\mu/(\mu^2 + \sigma^2)$ |
| `P.fractional_kelly(mu, sigma, frac)` | Eq (13.14): $\text{frac} \cdot \mu/\sigma^2$ |
| `P.grossman_zhou(mu, sigma, max_dd, cur_dd)` | Eq (13.13): drawdown-controlled dynamic Kelly fraction |
| `P.grossman_zhou_path(returns, mu, sigma, max_dd)` | strictly causal wealth, high watermark, drawdown, and sizing path |

### Ex-post performance attribution & causal backtest (Ch 14)

| def | result |
|---|---|
| `P.estimate_factor_returns(fm, r)` | cross-sectional WLS $\hat{f} = (B^\top \Omega_\varepsilon^{-1} B)^{-1} B^\top \Omega_\varepsilon^{-1} r$ |
| `P.attrib_error_var(fm, w)` | Ch 14.2.2: attribution uncertainty variance $b^\top (B^\top \Omega_\varepsilon^{-1} B)^{-1} b$ |
| `P.attribute_period(fm, w, r, f_ret, realized_pnl)` | trading, factor, per-factor, idio, per-asset PnL + attribution error variance |
| `P.maximal_attribution(cov_f, b, f_ret, subset)` | Ch 14.3: Schur-complement rotation pushing maximal PnL & variance into `subset` |
| `P.nested_attribution(cov_f, b, f_ret, groups)` | Ch 14.3 Procedure 14.2: sequential maximal attribution over disjoint factor groups |
| `P.selection_sizing(w, eps, idio_var)` | Ch 14.4: exact IR = selection × diversification + sizing decomposition + long/short split |
| `P.forward_pnl(weights, returns)` | causal parallel forward PnL pairing `weights[t]` with `returns[t + 1]` |
| `P.forward_attribute(fms, weights, returns, f_rets)` | causal parallel multi-period attribution pairing `(fms[t], weights[t])` with `(returns[t + 1], f_rets[t + 1])` |

## Checks & timings

```sh
python3 portfolio/check.py                   # needs bend, numpy, scipy
cd portfolio && bend PROOF.bend --verdict    # verifies all 36 laws twice (including Lean-verified BendTT kernel)
```

`check.py` verifies every public function against NumPy and SciPy (`SLSQP`) across small, zero-factor (`K=0`), parallel (`T >= 64`), ill-conditioned ($\kappa(\Omega_f) = 10^4$), and constrained/turnover-aware cases:

- Risk decomposition & analytical MVO (`N=12..250, K=0..20, cond_f=1e4`): `max_err <= 2.27e-5`, exact `SRE = 1.000000` on matching models, `||B^T w_fn|| <= 1e-6`.
- Woodbury-ADMM constrained MVO (unconstrained equivalence, long-only + budget, factor-neutral + box, GMV + dollar-neutral, L1 + L2 + factor bounds, diagonal `K=0`, and full `200×15` book): matches SciPy `SLSQP` to `w_err <= 3.52e-5`, `obj_err <= 4.62e-6`, `viol <= 5.37e-5`.
- Hedging, Kelly/Grossman–Zhou sizing, attribution, maximal/nested Schur complement, selection/sizing IR decomposition, and parallel `forward_pnl`/`forward_attribute`: `max_err <= 2.24e-6`.

Representative cross-hardware timings (full tables across Apple M1 Pro, AMD EPYC 7B12, and Intel Xeon @ 2.20 GHz in [bench/README.md](bench/README.md)):

| operation | M1 Pro Bend | EPYC Bend | EPYC NumPy / OSQP | Xeon Bend | Xeon NumPy / OSQP |
|---|---:|---:|---:|---:|---:|
| `risk_decomp` ($1000 \times 30$) | `0.09 ms` (1t) | `0.12 ms` (1t) | `0.023 ms` | `0.20 ms` (1t) | `0.027 ms` |
| `mvo_target_vol` ($1000 \times 30$) | `1.35 ms` (1t) | `1.85 ms` (1t) | `0.202 ms` | `3.22 ms` (1t) | `0.321 ms` |
| `mvo_factor_neutral` ($1000 \times 30$) | `2.73 ms` (8t) | `3.70 ms` (1t) | `1.515 ms` | `8.76 ms` (1t) | `2.364 ms` |
| `attribute_period` ($1000 \times 30$) | `3.61 ms` (8t) | `4.51 ms` (1t) | `1.603 ms` | `8.91 ms` (1t) | `1.686 ms` |
| `forward_pnl` ($252 \times 1000$, `pmap`) | `0.36 ms` (8t) | `0.60 ms` (8t) | `0.120 ms` | `1.12 ms` (1t) | `0.299 ms` |
| `forward_attribute` ($252 \times 200 \times 15$, `pmap`) | `30.24 ms` (8t) | `56.25 ms` (8t) | `20.366 ms` | `148.25 ms` (2t) | `31.757 ms` |
| `mvo_constrained` ($200 \times 15, M=16$) | `3.72 ms` | **`5.32 ms`** | `13.87 ms` (OSQP C) | **`9.85 ms`** | `28.78 ms` (OSQP) |
| `mvo_constrained` ($500 \times 30, M=31$) | `24.45 ms` | **`36.37 ms`** | `98.78 ms` (OSQP C) | **`57.66 ms`** | `182.98 ms` (OSQP) |
| `mvo_constrained` ($1000 \times 30, M=31$) | `81.69 ms` | **`122.17 ms`** | `714.53 ms` (OSQP C) | **`213.18 ms`** | `1,590.09 ms` (OSQP) |
