# portfolio: design notes

`portfolio` implements portfolio risk decomposition, analytical and constrained mean-variance optimization, hedging, dynamic risk sizing, and ex-post performance attribution from Giuseppe Paleologo's *The Elements of Quantitative Investing* (Ch 4.5, 9–14) on top of `bend-quant-linalg@0.1.0.0`.

## Core architectural choices

### 1. Strict factor model representation (`FactorModel`)
Every risk, optimization, hedging, and attribution routine operates directly on `(B, Ω_f, diag(Ω_ε))` (`N × K`, `K × K`, `N`) and **never forms the $N \times N$ covariance matrix $\Omega_r = B \Omega_f B^\top + \Omega_\varepsilon$**:
- Implicit matrix-vector products `cov_matvec` run in $O(NK + K^2)$.
- Unconstrained, vol-targeted, robust, quadratic-impact, and tracking-series optimizations use `linalg.woodbury_solve` in $O(NK^2 + K^3)$ via inverse-free $K \times K$ Cholesky.
- Factor-Mimicking Portfolios (`fmp`), alpha orthogonalization (`alpha_decompose`), factor-neutral MVO (`mvo_factor_neutral`), and attribution error variance (`attrib_error_var`) all work via thin QR of $D^{-1/2} B = Q R$ (`linalg.qr_thin` + `linalg.project_orth`), avoiding squaring $\kappa(D^{-1/2} B)$ in `F32` arithmetic.

### 2. Woodbury-preconditioned ADMM (`admm.bend`)
`mvo_constrained` solves the convex portfolio construction problem (Ch 10.2 & 11):
$$\min_w \frac{\rho}{2} w^\top \Omega_r w - \alpha^\top w + \frac{1}{2} (w - w_0)^\top \operatorname{diag}(c_2)(w - w_0) + \sum_{i=1}^N c_{1,i} |w_i - w_{0,i}|$$
subject to $l_w \le w \le u_w$, $l_c \le A w \le u_c$, and optional GMV cap $\|w\|_1 \le G$.

Key design decisions:
- **Exact unified box + GMV projection:** Box bounds and the $\ell_1$ leverage ball are combined into one consensus variable $z_1 = w$. When $\| \operatorname{clip}(v, l_w, u_w) \|_1 > G$, separable KKT optimality gives $z_i(\lambda) = \operatorname{clip}(\operatorname{soft}(v_i, \lambda), l_{w,i}, u_{w,i})$, whose $\ell_1$ norm is continuous and monotonically non-increasing in $\lambda \ge 0$; 30 steps of bisection solve it to $< 10^{-9}$ with zero sorting or variable doubling.
- **Single pre-loop Woodbury factorization:** Combining $U = [\sqrt{\rho} B L_f, \; \sqrt{\mu_c} \tilde{A}^\top] \in \mathbb{R}^{N \times (K + M)}$ makes the $w$-update Hessian $H = \tilde{D} + U U^\top$. We factor $C = I_{K+M} + U^\top \tilde{D}^{-1} U = L_C L_C^\top$ once before the loop and run every iteration in $O(N(K + M))$ over flat `Array<F32>` buffers with over-relaxation ($\gamma = 1.6$).
- **Row equilibration + curvature-matched $(\mu_w, \mu_c)$:** Constraint rows $A_j$ are normalized to unit $\ell_2$ norm for conditioning while primal residuals are unscaled back by $\|A_j\|_2$ before checking `abs_tol`/`rel_tol`. Separate penalties $\mu_w$ (for box/L1) and $\mu_c$ (for factor/linear constraints, scaled to $\bar{d} + \lambda_{\text{fac}}$) prevent slow primal convergence on large $N$.
- **Clean boundary:** `mvo_constrained` returns `z_1`, so hard box and GMV bounds hold to `0.0` at termination.

### 3. Hedging algebra (Ch 12)
- `hedge_instruments` solves $(H^\top \Omega_r H) x^* = - H^\top \Omega_r w_c$ for $M$ tradeable hedge instruments (ETFs, futures, or FMP subsets) without forming $\Omega_r$, automatically accounting for both factor covariance and idiosyncratic variance of the hedge instruments.
- `hedge_track_series` solves $(\Omega_r + \mu_h^2 \Gamma + \mu_h^2 \hat{\beta} \hat{\beta}^\top) w^* = (\mu_h^2 + \sigma_h^2) \hat{\beta}$ in a single Woodbury solve + rank-1 Sherman–Morrison scalar rescale, which also stays nonsingular at $\mu_h = 0$.

### 4. Exact accounting & causality (Ch 13–14)
- `grossman_zhou_path` is built directly on a generic left `scan` so `PROOF.bend` proves strict causality (`gz_path_causal`): future returns cannot influence past wealth, high watermark, drawdown, or sizing.
- `forward_pnl` and `forward_attribute` follow `signal`'s convention (row $j$ of `returns` is the one-period return over $(j - 1, j]$) and pair row $t$ of `weights` with row $t + 1$ of `returns` over a 64-task fork-join `pmap`. `PROOF.bend` proves both parallel-sequential equivalence (`pmap_seq`) and no-lookahead pairing (`forward_pnl_row`).
- All file IO is isolated in `io.bend`, so `PROOF.bend` imports zero effects and zero `@unsafe`.
