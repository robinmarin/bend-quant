# portfolio: factor risk decomposition, portfolio construction (analytical MVO,
# Woodbury-ADMM constrained/turnover-aware MVO), hedging, dynamic risk sizing,
# and ex-post performance attribution over float32 vectors and matrices.
#
# Built on bend-quant-linalg@0.1.0.0 following Paleologo's
# "The Elements of Quantitative Investing" (Ch 4.5, 9-14).
# Every non-public def is internal; LAWS.bend and PROOF.bend name internals and
# they can change in any version.
import Base
import bend-kit-f32array@0.2.1.0/f32array.bend as A
import bend-quant-linalg@0.1.0.0/linalg.bend as L
import ./admm.bend as ADMM

# ---------------------------------------------------------------- types

# Strict factor risk model: Omega_r = B Omega_f B^T + diag(idio_var).
# b: N x K loadings, cov_f: K x K SPD factor covariance, idio_var: N positive variances.
type FactorModel is Data:
  FactorModel{b: L.Mat, cov_f: L.Mat, idio_var: L.Vec}

# Portfolio risk decomposition under a factor model (Paleologo Ch 4.5.2).
type RiskDecomp is Data:
  RiskDecomp{
    total_var: F32,
    factor_var: F32,
    idio_var: F32,
    total_vol: F32,
    factor_vol: F32,
    idio_vol: F32,
    pct_idio: F32,
    exposures: L.Vec
  }

# Alpha decomposition alpha = B * factor_alpha + orth under Omega_eps^{-1} (Ch 4.3, 9.4).
type AlphaDecomp is Data:
  AlphaDecomp{
    factor_alpha: L.Vec,
    spanned: L.Vec,
    orth: L.Vec
  }

# ---------------------------------------------------------------- scalar & list helpers

def fmax(+a: F32, +b: F32) -> F32:
  F32.max(a, b)

def fmin(+a: F32, +b: F32) -> F32:
  Bool.pick(F32, F32.is_le(a, b), a, b)

def all_pos(xs: List<&2, F32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(F32.is_gt(h, 0.0), all_pos(t))

def all_nonneg(xs: List<&2, F32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(F32.is_ge(h, 0.0), all_nonneg(t))

def list_map_f32(~f: F32 -> F32, xs: List<&2, F32>) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      f(h) <> list_map_f32(~f, t)

def inv_f32(x: F32) -> F32:
  (1.0 / x : F32)

def sqrt_f32(x: F32) -> F32:
  F32.sqrt(x)

def inv_sqrt_f32(x: F32) -> F32:
  (1.0 / F32.sqrt(x) : F32)

def list_add_scalar(xs: List<&2, F32>, +s: F32) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      (h + s : F32) <> list_add_scalar(t, s)

def vec_inv(v: L.Vec) -> L.Vec:
  L.Vec{n, xs} = v
  L.Vec{n, list_map_f32(~inv_f32, xs)}

def vec_sqrt(v: L.Vec) -> L.Vec:
  L.Vec{n, xs} = v
  L.Vec{n, list_map_f32(~sqrt_f32, xs)}

def vec_inv_sqrt(v: L.Vec) -> L.Vec:
  L.Vec{n, xs} = v
  L.Vec{n, list_map_f32(~inv_sqrt_f32, xs)}

def vec_add_scalar(v: L.Vec, +s: F32) -> L.Vec:
  L.Vec{n, xs} = v
  L.Vec{n, list_add_scalar(xs, s)}

def list_quad_diag.go(ws: List<&2, F32>, ds: List<&2, F32>, acc: F32) -> F32:
  match ws ds:
    case Nil{} _:
      acc
    case Con{w, wt} Nil{}:
      acc
    case Con{+w, wt} Con{d, dt}:
      list_quad_diag.go(wt, dt, (acc + ((w * w : F32) * d : F32) : F32))

def vec_quad_diag.pick(ok: Bool, ws: List<&2, F32>, ds: List<&2, F32>) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      Some{list_quad_diag.go(ws, ds, 0.0)}
    case False{}:
      None{}

def vec_quad_diag(w: L.Vec, d: L.Vec) -> Maybe<&2, F32>:
  L.Vec{wn, ws} = w
  L.Vec{dn, ds} = d
  vec_quad_diag.pick(U32.is_eq(wn, dn), ws, ds)

# ---------------------------------------------------------------- FactorModel validation

def fm_dims_ok(b: L.Mat, cov_f: L.Mat, idio_var: L.Vec) -> Bool:
  L.Mat{bm, bn, _} = b
  L.Mat{+cm, cn, _} = cov_f
  L.Vec{dn, _} = idio_var
  Bool.and(U32.is_eq(bm, dn), Bool.and(U32.is_eq(bn, cm), U32.is_eq(cm, cn)))

def FactorModel.new.pos(ok: Bool, b: L.Mat, cov_f: L.Mat, idio_var: L.Vec) -> Maybe<&2, FactorModel>:
  match ok:
    case True{}:
      Some{FactorModel{b, cov_f, idio_var}}
    case False{}:
      None{}

# The header matches the rows: m rows, each of length n.
# ponytail: same as L.Mat.ok in linalg 0.1.1.0; switch once that is published.
def mat_ok(a: L.Mat) -> Bool:
  L.Mat{m, n, +rows} = a
  Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, rows), U32.to_nat(m)), L.Mat.rows.ok(rows, U32.to_nat(n)))

def vec_ok(v: L.Vec) -> Bool:
  L.Vec{n, xs} = v
  Nat.is_eq(List.length(&2, F32, xs), U32.to_nat(n))

def fm_rows_ok(b: L.Mat, cov_f: L.Mat, idio_var: L.Vec) -> Bool:
  Bool.and(mat_ok(b), Bool.and(mat_ok(cov_f), vec_ok(idio_var)))

def FactorModel.new.rows(ok: Bool, b: L.Mat, cov_f: L.Mat, +idio_var: L.Vec) -> Maybe<&2, FactorModel>:
  match ok:
    case True{}:
      L.Vec{_, ds} = idio_var
      FactorModel.new.pos(all_pos(ds), b, cov_f, idio_var)
    case False{}:
      None{}

def FactorModel.new.dims(ok: Bool, +b: L.Mat, +cov_f: L.Mat, +idio_var: L.Vec) -> Maybe<&2, FactorModel>:
  match ok:
    case True{}:
      FactorModel.new.rows(fm_rows_ok(b, cov_f, idio_var), b, cov_f, idio_var)
    case False{}:
      None{}

# Validates dimensions (b is N x K, cov_f is K x K, idio_var is N), that every
# header matches its rows, and idio_var > 0.
def FactorModel.new(+b: L.Mat, +cov_f: L.Mat, +idio_var: L.Vec) -> Maybe<&2, FactorModel>:
  FactorModel.new.dims(fm_dims_ok(b, cov_f, idio_var), b, cov_f, idio_var)

# ---------------------------------------------------------------- risk decomposition (Ch 4.5.2)

# Factor exposures b = B^T w (length K).
def exposures(fm: FactorModel, w: L.Vec) -> Maybe<&2, L.Vec>:
  FactorModel{b, _, _} = fm
  L.matvec_t(b, w)

def cov_matvec.step3(fpart: Maybe<&2, L.Vec>, ipart: Maybe<&2, L.Vec>) -> Maybe<&2, L.Vec>:
  match fpart ipart:
    case Some{fp} Some{ip}:
      L.vadd(fp, ip)
    case _ _:
      None{}

def cov_matvec.step2(mbz: Maybe<&2, L.Vec>, b: L.Mat, idio_var: L.Vec, w: L.Vec) -> Maybe<&2, L.Vec>:
  match mbz:
    case Some{bz}:
      cov_matvec.step3(L.matvec(b, bz), L.vmul(idio_var, w))
    case None{}:
      None{}

def cov_matvec.step1(mexp: Maybe<&2, L.Vec>, b: L.Mat, cov_f: L.Mat, idio_var: L.Vec, w: L.Vec) -> Maybe<&2, L.Vec>:
  match mexp:
    case Some{exp}:
      cov_matvec.step2(L.matvec(cov_f, exp), b, idio_var, w)
    case None{}:
      None{}

# Implicit matrix-vector product Omega_r w = B (Omega_f (B^T w)) + diag(idio_var) w in O(N K + K^2).
def cov_matvec(fm: FactorModel, +w: L.Vec) -> Maybe<&2, L.Vec>:
  FactorModel{+b, cov_f, idio_var} = fm
  cov_matvec.step1(L.matvec_t(b, w), b, cov_f, idio_var, w)

def risk_decomp.build(mfvar: Maybe<&2, F32>, mivar: Maybe<&2, F32>, exp: L.Vec) -> Maybe<&2, RiskDecomp>:
  match mfvar mivar:
    case Some{+fvar} Some{+ivar}:
      +tvar = (fvar + ivar : F32)
      +tvol = F32.sqrt(fmax(0.0, tvar))
      +fvol = F32.sqrt(fmax(0.0, fvar))
      +ivol = F32.sqrt(fmax(0.0, ivar))
      +pct = Bool.pick(F32, F32.is_gt(tvar, 0.0), (ivar / tvar : F32), 0.0)
      Some{RiskDecomp{tvar, fvar, ivar, tvol, fvol, ivol, pct, exp}}
    case _ _:
      None{}

def risk_decomp.go(mexp: Maybe<&2, L.Vec>, cov_f: L.Mat, idio_var: L.Vec, w: L.Vec) -> Maybe<&2, RiskDecomp>:
  match mexp:
    case Some{+exp}:
      risk_decomp.build(L.quad_form(exp, cov_f), vec_quad_diag(w, idio_var), exp)
    case None{}:
      None{}

# Total, factor, and idiosyncratic variance/volatility and exposures.
def risk_decomp(fm: FactorModel, +w: L.Vec) -> Maybe<&2, RiskDecomp>:
  FactorModel{b, cov_f, idio_var} = fm
  risk_decomp.go(L.matvec_t(b, w), cov_f, idio_var, w)

def active_risk.go(mwa: Maybe<&2, L.Vec>, fm: FactorModel) -> Maybe<&2, RiskDecomp>:
  match mwa:
    case Some{wa}:
      risk_decomp(fm, wa)
    case None{}:
      None{}

# Tracking error and risk decomposition of active holdings w - w_bench (Ch 10.2.1).
def active_risk(fm: FactorModel, w: L.Vec, w_bench: L.Vec) -> Maybe<&2, RiskDecomp>:
  active_risk.go(L.vsub(w, w_bench), fm)

def marginal_risk.pos(ok: Bool, tvar: F32, om_w: L.Vec) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      Some{L.vscale((1.0 / F32.sqrt(tvar) : F32), om_w)}
    case False{}:
      None{}

def marginal_risk.scale(mtvar: Maybe<&2, F32>, om_w: L.Vec) -> Maybe<&2, L.Vec>:
  match mtvar:
    case Some{+tvar}:
      marginal_risk.pos(F32.is_gt(tvar, 0.0), tvar, om_w)
    case None{}:
      None{}

def marginal_risk.go(momw: Maybe<&2, L.Vec>, w: L.Vec) -> Maybe<&2, L.Vec>:
  match momw:
    case Some{+om_w}:
      marginal_risk.scale(L.dot(w, om_w), om_w)
    case None{}:
      None{}

# Marginal contribution to portfolio volatility: (Omega_r w) / sigma(w).
# Returns None on shape mismatch or zero portfolio variance.
def marginal_risk(fm: FactorModel, +w: L.Vec) -> Maybe<&2, L.Vec>:
  marginal_risk.go(cov_matvec(fm, w), w)

def risk_contrib.pos(ok: Bool, tvar: F32, w: L.Vec, om_w: L.Vec) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      L.vmul(w, L.vscale((1.0 / F32.sqrt(tvar) : F32), om_w))
    case False{}:
      L.Vec{wn, _} = w
      Some{L.Vec.zeros(wn)}

def risk_contrib.scale(mtvar: Maybe<&2, F32>, w: L.Vec, om_w: L.Vec) -> Maybe<&2, L.Vec>:
  match mtvar:
    case Some{+tvar}:
      risk_contrib.pos(F32.is_gt(tvar, 0.0), tvar, w, om_w)
    case None{}:
      None{}

def risk_contrib.go(momw: Maybe<&2, L.Vec>, +w: L.Vec) -> Maybe<&2, L.Vec>:
  match momw:
    case Some{+om_w}:
      risk_contrib.scale(L.dot(w, om_w), w, om_w)
    case None{}:
      None{}

# Euler risk contributions w_i * (Omega_r w)_i / sigma(w); sums to sigma(w).
def risk_contrib(fm: FactorModel, +w: L.Vec) -> Maybe<&2, L.Vec>:
  risk_contrib.go(cov_matvec(fm, w), w)

def herfindahl.pick(ok: Bool, n1: F32, n2: F32) -> F32:
  match ok:
    case True{}:
      +r = (n2 / n1 : F32)
      (r * r : F32)
    case False{}:
      0.0

# Portfolio concentration H(w) = ||w||_2^2 / ||w||_1^2 in [1/N, 1] (Ch 12 note 5).
def herfindahl(+w: L.Vec) -> F32:
  +n1 = L.norm1(w)
  +n2 = L.norm2(w)
  herfindahl.pick(F32.is_gt(n1, 0.0), n1, n2)

def eff_breadth.go(mwtilde: Maybe<&2, L.Vec>) -> Maybe<&2, F32>:
  match mwtilde:
    case Some{+wt}:
      +n1 = L.norm1(wt)
      +n2 = L.norm2(wt)
      Some{Bool.pick(F32, F32.is_gt(n2, 0.0), (n1 / n2 : F32), 0.0)}
    case None{}:
      None{}

def eff_breadth.pos(ok: Bool, w: L.Vec, idio_var: L.Vec) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      eff_breadth.go(L.vmul(vec_sqrt(idio_var), w))
    case False{}:
      None{}

def eff_breadth.pick(ok: Bool, ds: List<&2, F32>, w: L.Vec, idio_var: L.Vec) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      eff_breadth.pos(all_nonneg(ds), w, idio_var)
    case False{}:
      None{}

# Volatility-weighted effective breadth ||sigma .* w||_1 / ||sigma .* w||_2 (Ch 14.4).
def eff_breadth(+w: L.Vec, +idio_var: L.Vec) -> Maybe<&2, F32>:
  L.Vec{wn, _} = w
  L.Vec{dn, ds} = idio_var
  eff_breadth.pick(U32.is_eq(wn, dn), ds, w, idio_var)

# ---------------------------------------------------------------- analytical MVO (Ch 9, 10.2.3, 11.3.1)

def mvo_unconstrained.scale(mz: Maybe<&2, L.Vec>, +risk_aversion: F32) -> Maybe<&2, L.Vec>:
  match mz:
    case Some{z}:
      Some{L.vscale((1.0 / risk_aversion : F32), z)}
    case None{}:
      None{}

def mvo_unconstrained.pos(ok: Bool, idio_var: L.Vec, b: L.Mat, cov_f: L.Mat, alpha: L.Vec, +risk_aversion: F32) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      mvo_unconstrained.scale(L.woodbury_solve(idio_var, b, cov_f, alpha), risk_aversion)
    case False{}:
      None{}

# Unconstrained MVO: max alpha^T w - (rho / 2) w^T Omega_r w => (1 / rho) Omega_r^{-1} alpha (Ch 9.2).
def mvo_unconstrained(fm: FactorModel, alpha: L.Vec, +risk_aversion: F32) -> Maybe<&2, L.Vec>:
  FactorModel{b, cov_f, idio_var} = fm
  mvo_unconstrained.pos(F32.is_gt(risk_aversion, 0.0), idio_var, b, cov_f, alpha, risk_aversion)

def mvo_target_vol.pos(ok: Bool, q: F32, z: L.Vec, +target_vol: F32) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      Some{L.vscale((target_vol / F32.sqrt(q) : F32), z)}
    case False{}:
      None{}

def mvo_target_vol.scale(mq: Maybe<&2, F32>, z: L.Vec, +target_vol: F32) -> Maybe<&2, L.Vec>:
  match mq:
    case Some{+q}:
      mvo_target_vol.pos(F32.is_gt(q, 0.0), q, z, target_vol)
    case None{}:
      None{}

def mvo_target_vol.zero(is_zero: Bool, +z: L.Vec, alpha: L.Vec, +target_vol: F32) -> Maybe<&2, L.Vec>:
  match is_zero:
    case True{}:
      L.Vec{an, _} = alpha
      Some{L.Vec.zeros(an)}
    case False{}:
      mvo_target_vol.scale(L.dot(alpha, z), z, target_vol)

def mvo_target_vol.go(mz: Maybe<&2, L.Vec>, alpha: L.Vec, +target_vol: F32) -> Maybe<&2, L.Vec>:
  match mz:
    case Some{z}:
      mvo_target_vol.zero(F32.is_eq(target_vol, 0.0), z, alpha, target_vol)
    case None{}:
      None{}

def mvo_target_vol.ge(ok: Bool, idio_var: L.Vec, b: L.Mat, cov_f: L.Mat, +alpha: L.Vec, +target_vol: F32) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      mvo_target_vol.go(L.woodbury_solve(idio_var, b, cov_f, alpha), alpha, target_vol)
    case False{}:
      None{}

# Volatility-targeted MVO: w* = (sigma / sqrt(alpha^T Omega_r^{-1} alpha)) Omega_r^{-1} alpha (Eq 9.3).
def mvo_target_vol(fm: FactorModel, alpha: L.Vec, +target_vol: F32) -> Maybe<&2, L.Vec>:
  FactorModel{b, cov_f, idio_var} = fm
  mvo_target_vol.ge(F32.is_ge(target_vol, 0.0), idio_var, b, cov_f, alpha, target_vol)

def mvo_robust.ok(ok: Bool, idio_var: L.Vec, b: L.Mat, cov_f: L.Mat, alpha: L.Vec, +risk_aversion: F32, +tau_sq: F32) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      mvo_unconstrained.scale(L.woodbury_solve(vec_add_scalar(idio_var, tau_sq), b, cov_f, alpha), risk_aversion)
    case False{}:
      None{}

# Robust diagonal-regularized MVO: (1 / rho) (Omega_r + tau_sq * I)^{-1} alpha (Ch 10.2.3).
# Unifies uncertain alpha, robust missing factor, and Frobenius-robust covariance.
def mvo_robust(fm: FactorModel, alpha: L.Vec, +risk_aversion: F32, +tau_sq: F32) -> Maybe<&2, L.Vec>:
  FactorModel{b, cov_f, idio_var} = fm
  mvo_robust.ok(Bool.and(F32.is_gt(risk_aversion, 0.0), F32.is_ge(tau_sq, 0.0)), idio_var, b, cov_f, alpha, risk_aversion, tau_sq)

def mvo_trade_quad.solve(md_eff: Maybe<&2, L.Vec>, mrhs: Maybe<&2, L.Vec>, b: L.Mat, cov_f: L.Mat, +risk_aversion: F32) -> Maybe<&2, L.Vec>:
  match md_eff mrhs:
    case Some{d_eff} Some{rhs}:
      L.woodbury_solve(d_eff, b, L.scale(risk_aversion, cov_f), rhs)
    case _ _:
      None{}

def mvo_trade_quad.rhs(mcw: Maybe<&2, L.Vec>, alpha: L.Vec, idio_var: L.Vec, cost_quad: L.Vec, b: L.Mat, cov_f: L.Mat, +risk_aversion: F32) -> Maybe<&2, L.Vec>:
  match mcw:
    case Some{cw}:
      mvo_trade_quad.solve(L.vadd(L.vscale(risk_aversion, idio_var), cost_quad), L.vadd(alpha, cw), b, cov_f, risk_aversion)
    case None{}:
      None{}

def mvo_trade_quad.nonneg(ok: Bool, b: L.Mat, cov_f: L.Mat, idio_var: L.Vec, alpha: L.Vec, w0: L.Vec, +cost_quad: L.Vec, +risk_aversion: F32) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      mvo_trade_quad.rhs(L.vmul(cost_quad, w0), alpha, idio_var, cost_quad, b, cov_f, risk_aversion)
    case False{}:
      None{}

def mvo_trade_quad.pick(ok: Bool, cs: List<&2, F32>, b: L.Mat, cov_f: L.Mat, idio_var: L.Vec, alpha: L.Vec, w0: L.Vec, cost_quad: L.Vec, +risk_aversion: F32) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      mvo_trade_quad.nonneg(Bool.and(F32.is_gt(risk_aversion, 0.0), all_nonneg(cs)), b, cov_f, idio_var, alpha, w0, cost_quad, risk_aversion)
    case False{}:
      None{}

# Single-period quadratic impact closed form (Ch 11 Eq 11.7):
# max alpha^T w - (rho / 2) w^T Omega_r w - (1/2) (w - w0)^T diag(cost_quad) (w - w0).
def mvo_trade_quad(fm: FactorModel, +alpha: L.Vec, +w0: L.Vec, +cost_quad: L.Vec, +risk_aversion: F32) -> Maybe<&2, L.Vec>:
  FactorModel{+b, cov_f, idio_var} = fm
  L.Mat{+bm, _, _} = b
  L.Vec{an, _} = alpha
  L.Vec{wn, _} = w0
  L.Vec{cn, cs} = cost_quad
  mvo_trade_quad.pick(Bool.and(U32.is_eq(bm, an), Bool.and(U32.is_eq(bm, wn), U32.is_eq(bm, cn))), cs, b, cov_f, idio_var, alpha, w0, cost_quad, risk_aversion)

# ---------------------------------------------------------------- FMPs, alpha decomposition & factor-neutral MVO (Ch 9.3, 9.4)

def fmp.finish(mx: Maybe<&2, L.Mat>, d_isq: L.Vec) -> Maybe<&2, L.Mat>:
  match mx:
    case Some{x}:
      L.diag_mul(d_isq, L.transpose(x))
    case None{}:
      None{}

def fmp.from_qr(mqr: Maybe<&2, L.QR>, d_isq: L.Vec) -> Maybe<&2, L.Mat>:
  match mqr:
    case Some{L.QR{q, r}}:
      fmp.finish(L.solve_upper_mat(r, L.transpose(q)), d_isq)
    case None{}:
      None{}

def fmp.weighted(ma: Maybe<&2, L.Mat>, d_isq: L.Vec) -> Maybe<&2, L.Mat>:
  match ma:
    case Some{a}:
      fmp.from_qr(L.qr_thin(a), d_isq)
    case None{}:
      None{}

def fmp.pos(ok: Bool, b: L.Mat, idio_var: L.Vec) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      +d_isq = vec_inv_sqrt(idio_var)
      fmp.weighted(L.diag_mul(d_isq, b), d_isq)
    case False{}:
      None{}

def fmp.k0(is_k0: Bool, +bm: U32, ds: List<&2, F32>, b: L.Mat, idio_var: L.Vec) -> Maybe<&2, L.Mat>:
  match is_k0:
    case True{}:
      Some{L.Mat{bm, 0, List.replicate(List<&2, F32>, U32.to_nat(bm), Nil{})}}
    case False{}:
      fmp.pos(all_pos(ds), b, idio_var)

def fmp.pick(ok: Bool, bm: U32, bn: U32, ds: List<&2, F32>, b: L.Mat, idio_var: L.Vec) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      fmp.k0(U32.is_eq(bn, 0), bm, ds, b, idio_var)
    case False{}:
      None{}

# Factor-Mimicking Portfolios P = Omega_eps^{-1} B (B^T Omega_eps^{-1} B)^{-1} (N x K, Eq 9.12).
# Computed via thin QR of D^{-1/2} B to avoid squaring the condition number.
def fmp(fm: FactorModel) -> Maybe<&2, L.Mat>:
  FactorModel{+b, _, +idio_var} = fm
  L.Mat{+bm, +bn, _} = b
  L.Vec{+dn, ds} = idio_var
  fmp.pick(U32.is_eq(bm, dn), bm, bn, ds, b, idio_var)

def alpha_decomp.wrap(msp: Maybe<&2, L.Vec>, morth: Maybe<&2, L.Vec>, lam: L.Vec) -> Maybe<&2, AlphaDecomp>:
  match msp morth:
    case Some{sp} Some{orth}:
      Some{AlphaDecomp{lam, sp, orth}}
    case _ _:
      None{}

def alpha_decomp.build(mlam: Maybe<&2, L.Vec>, morth_w: Maybe<&2, L.Vec>, b: L.Mat, d_sq: L.Vec) -> Maybe<&2, AlphaDecomp>:
  match mlam morth_w:
    case Some{+lam} Some{orth_w}:
      alpha_decomp.wrap(L.matvec(b, lam), L.vmul(d_sq, orth_w), lam)
    case _ _:
      None{}

def alpha_decomp.solve_r(mqta: Maybe<&2, L.Vec>, morth_w: Maybe<&2, L.Vec>, r: L.Mat, b: L.Mat, d_sq: L.Vec) -> Maybe<&2, AlphaDecomp>:
  match mqta:
    case Some{qta}:
      alpha_decomp.build(L.solve_upper(r, qta), morth_w, b, d_sq)
    case None{}:
      None{}

def alpha_decomp.from_qr(mqr: Maybe<&2, L.QR>, mta: Maybe<&2, L.Vec>, b: L.Mat, d_sq: L.Vec) -> Maybe<&2, AlphaDecomp>:
  match mqr mta:
    case Some{L.QR{+q, r}} Some{+ta}:
      alpha_decomp.solve_r(L.matvec_t(q, ta), L.project_orth(q, ta), r, b, d_sq)
    case _ _:
      None{}

def alpha_decomp.weighted(ma: Maybe<&2, L.Mat>, b: L.Mat, d_isq: L.Vec, d_sq: L.Vec, alpha: L.Vec) -> Maybe<&2, AlphaDecomp>:
  match ma:
    case Some{a}:
      alpha_decomp.from_qr(L.qr_thin(a), L.vmul(d_isq, alpha), b, d_sq)
    case None{}:
      None{}

def alpha_decomp.pos(ok: Bool, +b: L.Mat, +idio_var: L.Vec, alpha: L.Vec) -> Maybe<&2, AlphaDecomp>:
  match ok:
    case True{}:
      +d_isq = vec_inv_sqrt(idio_var)
      +d_sq = vec_sqrt(idio_var)
      alpha_decomp.weighted(L.diag_mul(d_isq, b), b, d_isq, d_sq, alpha)
    case False{}:
      None{}

def alpha_decomp.k0(is_k0: Bool, bm: U32, ds: List<&2, F32>, b: L.Mat, idio_var: L.Vec, alpha: L.Vec) -> Maybe<&2, AlphaDecomp>:
  match is_k0:
    case True{}:
      Some{AlphaDecomp{L.Vec.zeros(0), L.Vec.zeros(bm), alpha}}
    case False{}:
      alpha_decomp.pos(all_pos(ds), b, idio_var, alpha)

def alpha_decomp.pick(ok: Bool, bm: U32, bn: U32, ds: List<&2, F32>, b: L.Mat, idio_var: L.Vec, alpha: L.Vec) -> Maybe<&2, AlphaDecomp>:
  match ok:
    case True{}:
      alpha_decomp.k0(U32.is_eq(bn, 0), bm, ds, b, idio_var, alpha)
    case False{}:
      None{}

# Decomposes alpha = B * factor_alpha + orth under Omega_eps^{-1} metric (Ch 4.3, 9.4).
def alpha_decompose(fm: FactorModel, +alpha: L.Vec) -> Maybe<&2, AlphaDecomp>:
  FactorModel{+b, _, +idio_var} = fm
  L.Mat{+bm, +bn, _} = b
  L.Vec{+dn, ds} = idio_var
  L.Vec{+an, _} = alpha
  alpha_decomp.pick(Bool.and(U32.is_eq(bm, dn), U32.is_eq(bm, an)), bm, bn, ds, b, idio_var, alpha)

def mvo_fn.nrm(ok: Bool, nrm: F32, ow: L.Vec, d_isq: L.Vec, +target_vol: F32) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      L.vmul(d_isq, L.vscale((target_vol / nrm : F32), ow))
    case False{}:
      None{}

def mvo_fn.zero(is_zero: Bool, +ow: L.Vec, d_isq: L.Vec, +target_vol: F32) -> Maybe<&2, L.Vec>:
  match is_zero:
    case True{}:
      L.Vec{n, _} = ow
      Some{L.Vec.zeros(n)}
    case False{}:
      +nrm = L.norm2(ow)
      mvo_fn.nrm(F32.is_gt(nrm, 0.0), nrm, ow, d_isq, target_vol)

def mvo_fn.scale(mow: Maybe<&2, L.Vec>, d_isq: L.Vec, +target_vol: F32) -> Maybe<&2, L.Vec>:
  match mow:
    case Some{ow}:
      mvo_fn.zero(F32.is_eq(target_vol, 0.0), ow, d_isq, target_vol)
    case None{}:
      None{}

def mvo_fn.from_qr(mqr: Maybe<&2, L.QR>, mta: Maybe<&2, L.Vec>, d_isq: L.Vec, +target_vol: F32) -> Maybe<&2, L.Vec>:
  match mqr mta:
    case Some{L.QR{q, _}} Some{ta}:
      mvo_fn.scale(L.project_orth(q, ta), d_isq, target_vol)
    case _ _:
      None{}

def mvo_fn.weighted(ma: Maybe<&2, L.Mat>, +d_isq: L.Vec, alpha: L.Vec, +target_vol: F32) -> Maybe<&2, L.Vec>:
  match ma:
    case Some{a}:
      mvo_fn.from_qr(L.qr_thin(a), L.vmul(d_isq, alpha), d_isq, target_vol)
    case None{}:
      None{}

def mvo_fn.k0(is_k0: Bool, b: L.Mat, +d_isq: L.Vec, alpha: L.Vec, +target_vol: F32) -> Maybe<&2, L.Vec>:
  match is_k0:
    case True{}:
      mvo_fn.scale(L.vmul(d_isq, alpha), d_isq, target_vol)
    case False{}:
      mvo_fn.weighted(L.diag_mul(d_isq, b), d_isq, alpha, target_vol)

def mvo_fn.pos(ok: Bool, +b: L.Mat, +idio_var: L.Vec, alpha: L.Vec, +target_vol: F32) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      L.Mat{_, +bn, _} = b
      +d_isq = vec_inv_sqrt(idio_var)
      mvo_fn.k0(U32.is_eq(bn, 0), b, d_isq, alpha, target_vol)
    case False{}:
      None{}

def mvo_fn.pick(ok: Bool, ds: List<&2, F32>, b: L.Mat, idio_var: L.Vec, alpha: L.Vec, +target_vol: F32) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      mvo_fn.pos(Bool.and(F32.is_ge(target_vol, 0.0), all_pos(ds)), b, idio_var, alpha, target_vol)
    case False{}:
      None{}

# Pure-alpha / factor-neutral MVO (Ch 9.4 Eq 9.18):
# max alpha^T w  s.t.  B^T w = 0,  w^T Omega_eps w <= target_vol^2.
def mvo_factor_neutral(fm: FactorModel, +alpha: L.Vec, +target_vol: F32) -> Maybe<&2, L.Vec>:
  FactorModel{+b, _, +idio_var} = fm
  L.Mat{+bm, _, _} = b
  L.Vec{+dn, ds} = idio_var
  L.Vec{+an, _} = alpha
  mvo_fn.pick(Bool.and(U32.is_eq(bm, dn), U32.is_eq(bm, an)), ds, b, idio_var, alpha, target_vol)

def mvo_fspace.apply(mp: Maybe<&2, L.Mat>, mu: Maybe<&2, L.Vec>, +risk_aversion: F32) -> Maybe<&2, L.Vec>:
  match mp mu:
    case Some{p} Some{u}:
      L.matvec(p, L.vscale((1.0 / risk_aversion : F32), u))
    case _ _:
      None{}

def mvo_fspace.chol(ml: Maybe<&2, L.Mat>, fm: FactorModel, lambda_f: L.Vec, +risk_aversion: F32) -> Maybe<&2, L.Vec>:
  match ml:
    case Some{l}:
      mvo_fspace.apply(fmp(fm), L.cholesky_solve(l, lambda_f), risk_aversion)
    case None{}:
      None{}

def mvo_fspace.pos(ok: Bool, cov_f: L.Mat, fm: FactorModel, lambda_f: L.Vec, +risk_aversion: F32) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      mvo_fspace.chol(L.cholesky(cov_f), fm, lambda_f, risk_aversion)
    case False{}:
      None{}

def mvo_fspace.pick(ok: Bool, cov_f: L.Mat, fm: FactorModel, lambda_f: L.Vec, +risk_aversion: F32) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      mvo_fspace.pos(F32.is_gt(risk_aversion, 0.0), cov_f, fm, lambda_f, risk_aversion)
    case False{}:
      None{}

# Factor-space MVO: u* = (1 / rho) Omega_f^{-1} lambda_f, w* = P u* (Ch 9.3.1).
def mvo_factor_space(+fm: FactorModel, +lambda_f: L.Vec, +risk_aversion: F32) -> Maybe<&2, L.Vec>:
  FactorModel{b, +cov_f, _} = fm
  L.Mat{_, +bn, _} = b
  L.Mat{+cm, +cn, _} = cov_f
  L.Vec{+ln, _} = lambda_f
  mvo_fspace.pick(Bool.and(U32.is_eq(bn, cm), Bool.and(U32.is_eq(cm, cn), U32.is_eq(cm, ln))), cov_f, fm, lambda_f, risk_aversion)

# ---------------------------------------------------------------- Sharpe Ratio Efficiency (Ch 10.3)

def sre.pos(ok: Bool, ret: F32, rvar: F32, opt2: F32) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      Some{(ret / (F32.sqrt(rvar) * F32.sqrt(opt2) : F32) : F32)}
    case False{}:
      None{}

def sre.finish(mret: Maybe<&2, F32>, mrvar: Maybe<&2, F32>, mopt2: Maybe<&2, F32>) -> Maybe<&2, F32>:
  match mret mrvar mopt2:
    case Some{ret} Some{+rvar} Some{+opt2}:
      sre.pos(Bool.and(F32.is_gt(rvar, 0.0), F32.is_gt(opt2, 0.0)), ret, rvar, opt2)
    case _ _ _:
      None{}

def sre.with_omw(momw: Maybe<&2, L.Vec>, +w: L.Vec, z_true: L.Vec, +alpha_true: L.Vec) -> Maybe<&2, F32>:
  match momw:
    case Some{omw}:
      sre.finish(L.dot(alpha_true, w), L.dot(w, omw), L.dot(alpha_true, z_true))
    case None{}:
      None{}

def sre.go(mw: Maybe<&2, L.Vec>, mz: Maybe<&2, L.Vec>, fm_true: FactorModel, alpha_true: L.Vec) -> Maybe<&2, F32>:
  match mw mz:
    case Some{+w} Some{z_true}:
      sre.with_omw(cov_matvec(fm_true, w), w, z_true, alpha_true)
    case _ _:
      None{}

# Sharpe Ratio Efficiency SR(alpha_est, fm_est) / SR(alpha_true, fm_true) (Ch 10.3).
def sre(fm_est: FactorModel, alpha_est: L.Vec, +fm_true: FactorModel, +alpha_true: L.Vec) -> Maybe<&2, F32>:
  FactorModel{be, cfe, de} = fm_est
  FactorModel{bt, cft, dt} = fm_true
  sre.go(L.woodbury_solve(de, be, cfe, alpha_est), L.woodbury_solve(dt, bt, cft, alpha_true), fm_true, alpha_true)

# ---------------------------------------------------------------- transaction cost models (Ch 11.1)

def tc_lin.go(ws: List<&2, F32>, w0s: List<&2, F32>, cs: List<&2, F32>, acc: F32) -> F32:
  match ws w0s cs:
    case Con{w, wt} Con{w0, w0t} Con{c, ct}:
      tc_lin.go(wt, w0t, ct, (acc + (c * F32.abs((w - w0 : F32)) : F32) : F32))
    case _ _ _:
      acc

def tc_lin.pick(ok: Bool, ws: List<&2, F32>, w0s: List<&2, F32>, cs: List<&2, F32>) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      Some{tc_lin.go(ws, w0s, cs, 0.0)}
    case False{}:
      None{}

# Linear spread / commission cost: sum_i c1_i |w_i - w0_i|.
def trade_cost_linear(w: L.Vec, w0: L.Vec, c1: L.Vec) -> Maybe<&2, F32>:
  L.Vec{+wn, ws} = w
  L.Vec{w0n, w0s} = w0
  L.Vec{cn, cs} = c1
  tc_lin.pick(Bool.and(U32.is_eq(wn, w0n), U32.is_eq(wn, cn)), ws, w0s, cs)

def tc_quad.go(ws: List<&2, F32>, w0s: List<&2, F32>, cs: List<&2, F32>, acc: F32) -> F32:
  match ws w0s cs:
    case Con{w, wt} Con{w0, w0t} Con{c, ct}:
      +dw = (w - w0 : F32)
      tc_quad.go(wt, w0t, ct, (acc + ((0.5 * c : F32) * (dw * dw : F32) : F32) : F32))
    case _ _ _:
      acc

def tc_quad.pick(ok: Bool, ws: List<&2, F32>, w0s: List<&2, F32>, cs: List<&2, F32>) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      Some{tc_quad.go(ws, w0s, cs, 0.0)}
    case False{}:
      None{}

# Quadratic temporary market impact cost: (1/2) sum_i c2_i (w_i - w0_i)^2.
def trade_cost_quad(w: L.Vec, w0: L.Vec, c2: L.Vec) -> Maybe<&2, F32>:
  L.Vec{+wn, ws} = w
  L.Vec{w0n, w0s} = w0
  L.Vec{cn, cs} = c2
  tc_quad.pick(Bool.and(U32.is_eq(wn, w0n), U32.is_eq(wn, cn)), ws, w0s, cs)

def pow_pos(+x: F32, +p: F32) -> F32:
  Bool.pick(F32, F32.is_gt(x, 0.0), F32.exp((p * F32.log(x) : F32)), 0.0)

def tc_pow.go(ws: List<&2, F32>, w0s: List<&2, F32>, sigs: List<&2, F32>, advs: List<&2, F32>, +kappa: F32, +beta: F32, acc: F32) -> F32:
  match ws w0s sigs advs:
    case Con{w, wt} Con{w0, w0t} Con{sig, st} Con{adv, at}:
      +dw = F32.abs((w - w0 : F32))
      +pov = (dw / adv : F32)
      +term = (((kappa * sig : F32) * pow_pos(pov, beta) : F32) * dw : F32)
      tc_pow.go(wt, w0t, st, at, kappa, beta, (acc + term : F32))
    case _ _ _ _:
      acc

def tc_pow.pos(ok: Bool, ws: List<&2, F32>, w0s: List<&2, F32>, sigs: List<&2, F32>, advs: List<&2, F32>, +kappa: F32, +beta: F32) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      Some{tc_pow.go(ws, w0s, sigs, advs, kappa, beta, 0.0)}
    case False{}:
      None{}

def tc_pow.pick(ok: Bool, ws: List<&2, F32>, w0s: List<&2, F32>, +sigs: List<&2, F32>, +advs: List<&2, F32>, +kappa: F32, +beta: F32) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      +params_ok = Bool.and(F32.is_ge(kappa, 0.0), Bool.and(F32.is_ge(beta, 0.0), Bool.and(all_nonneg(sigs), all_pos(advs))))
      tc_pow.pos(params_ok, ws, w0s, sigs, advs, kappa, beta)
    case False{}:
      None{}

# Power-law market impact (Almgren-Chriss / Kyle, Ch 11.1.1):
# sum_i kappa * sigma_i * (|w_i - w0_i| / adv_i)^beta * |w_i - w0_i|.
def trade_cost_power(w: L.Vec, w0: L.Vec, +kappa: F32, sigma: L.Vec, adv: L.Vec, +beta: F32) -> Maybe<&2, F32>:
  L.Vec{+wn, ws} = w
  L.Vec{w0n, w0s} = w0
  L.Vec{sn, sigs} = sigma
  L.Vec{an, advs} = adv
  +dims_ok = Bool.and(U32.is_eq(wn, w0n), Bool.and(U32.is_eq(wn, sn), U32.is_eq(wn, an)))
  tc_pow.pick(dims_ok, ws, w0s, sigs, advs, kappa, beta)

# ---------------------------------------------------------------- constrained & turnover-aware MVO (Ch 10.2, 11)

# Linear + box + optional GMV constraints (Ch 10.2.1).
# Set l_c_j == u_c_j for equality constraints; gmv_max <= 0.0 disables the L1 cap.
type Constraints is Data:
  Constraints{
    l_w: L.Vec,
    u_w: L.Vec,
    a: L.Mat,
    l_c: L.Vec,
    u_c: L.Vec,
    gmv_max: F32
  }

# Transaction / market impact cost vectors (non-negative, length N).
type TradeCosts is Data:
  TradeCosts{
    linear: L.Vec,
    quad: L.Vec
  }

# ADMM solver configuration. rho_admm <= 0.0 selects automatic Hessian scaling.
type OptConfig is Data:
  OptConfig{
    max_iters: U32,
    abs_tol: F32,
    rel_tol: F32,
    rho_admm: F32,
    relax: F32
  }

# Constrained MVO solution and KKT residual diagnostics.
type OptResult is Data:
  OptResult{
    weights: L.Vec,
    iters: U32,
    primal_res: F32,
    dual_res: F32,
    converged: Bool
  }

def OptConfig.default() -> OptConfig:
  OptConfig{1000, 1.0e-5, 1.0e-4, 0.0, 1.6}

def Constraints.box(+l_w: L.Vec, u_w: L.Vec) -> Constraints:
  L.Vec{n, _} = l_w
  Constraints{l_w, u_w, L.Mat{0, n, Nil{}}, L.Vec.zeros(0), L.Vec.zeros(0), 0.0}

def TradeCosts.zero(+n: U32) -> TradeCosts:
  TradeCosts{L.Vec.zeros(n), L.Vec.zeros(n)}

def mvo_con.wrap(mo: Maybe<&2, ADMM.SolveOut>) -> Maybe<&2, OptResult>:
  match mo:
    case Some{ADMM.SolveOut{w, it, rp, rd, conv}}:
      Some{OptResult{w, it, rp, rd, conv}}
    case None{}:
      None{}

def mvo_con.vals(
  ok: Bool,
  b: L.Mat,
  cov_f: L.Mat,
  d_s: List<&2, F32>,
  a_s: List<&2, F32>,
  w0_s: List<&2, F32>,
  lw_s: List<&2, F32>,
  uw_s: List<&2, F32>,
  a_mat: L.Mat,
  lc_v: L.Vec,
  uc_v: L.Vec,
  c1_s: List<&2, F32>,
  c2_s: List<&2, F32>,
  +n: U32,
  +k: U32,
  +m: U32,
  +gmv: F32,
  +rho: F32,
  cfg: OptConfig
) -> Maybe<&2, OptResult>:
  match ok:
    case True{}:
      OptConfig{max_iters, abs_tol, rel_tol, rho_admm, relax} = cfg
      mvo_con.wrap(ADMM.solve_checked(b, cov_f, d_s, a_s, w0_s, lw_s, uw_s, a_mat, lc_v, uc_v, c1_s, c2_s, n, k, m, gmv, rho, max_iters, abs_tol, rel_tol, rho_admm, relax))
    case False{}:
      None{}

def mvo_con.dims_ok(
  +bm: U32, +bn: U32, +cm: U32, +cn: U32, +dn: U32,
  +an: U32, +w0n: U32, +lwn: U32, +uwn: U32,
  +am: U32, +anc: U32, +lcn: U32, +ucn: U32,
  +c1n: U32, +c2n: U32
) -> Bool:
  +ok_fm = Bool.and(U32.is_eq(bm, dn), Bool.and(U32.is_eq(bn, cm), U32.is_eq(cm, cn)))
  +ok_v = Bool.and(U32.is_eq(bm, an), Bool.and(U32.is_eq(bm, w0n), Bool.and(U32.is_eq(bm, lwn), U32.is_eq(bm, uwn))))
  +ok_a = Bool.and(U32.is_eq(bm, anc), Bool.and(U32.is_eq(am, lcn), U32.is_eq(am, ucn)))
  +ok_c = Bool.and(U32.is_eq(bm, c1n), U32.is_eq(bm, c2n))
  Bool.and(ok_fm, Bool.and(ok_v, Bool.and(ok_a, ok_c)))

def mvo_con.pick(
  ok: Bool,
  b: L.Mat,
  cov_f: L.Mat,
  +d_s: List<&2, F32>,
  a_s: List<&2, F32>,
  w0_s: List<&2, F32>,
  lw_s: List<&2, F32>,
  uw_s: List<&2, F32>,
  a_mat: L.Mat,
  lc_v: L.Vec,
  uc_v: L.Vec,
  +c1_s: List<&2, F32>,
  +c2_s: List<&2, F32>,
  +n: U32,
  +k: U32,
  +m: U32,
  +gmv: F32,
  +rho: F32,
  cfg: OptConfig
) -> Maybe<&2, OptResult>:
  match ok:
    case True{}:
      +vok = Bool.and(F32.is_gt(rho, 0.0), Bool.and(all_pos(d_s), Bool.and(all_nonneg(c1_s), all_nonneg(c2_s))))
      mvo_con.vals(vok, b, cov_f, d_s, a_s, w0_s, lw_s, uw_s, a_mat, lc_v, uc_v, c1_s, c2_s, n, k, m, gmv, rho, cfg)
    case False{}:
      None{}

# Constrained, turnover- and market-impact-aware MVO via Woodbury-preconditioned ADMM:
#   min_w  (rho/2) w^T Omega_r w - alpha^T w + (1/2) (w - w0)^T diag(c2) (w - w0) + sum c1_i |w_i - w0_i|
#   s.t.   l_w <= w <= u_w,  l_c <= A w <= u_c,  ||w||_1 <= gmv_max (if > 0).
def mvo_constrained(
  fm: FactorModel,
  alpha: L.Vec,
  w0: L.Vec,
  cons: Constraints,
  costs: TradeCosts,
  +risk_aversion: F32,
  cfg: OptConfig
) -> Maybe<&2, OptResult>:
  FactorModel{+b, +cov_f, idio_var} = fm
  L.Mat{+bm, +bn, _} = b
  L.Mat{+cm, +cn, _} = cov_f
  L.Vec{+dn, d_s} = idio_var
  L.Vec{+an, a_s} = alpha
  L.Vec{+w0n, w0_s} = w0
  Constraints{l_w, u_w, +a_mat, +lc_v, +uc_v, gmv} = cons
  L.Vec{+lwn, lw_s} = l_w
  L.Vec{+uwn, uw_s} = u_w
  L.Mat{+am, +anc, _} = a_mat
  L.Vec{+lcn, _} = lc_v
  L.Vec{+ucn, _} = uc_v
  TradeCosts{c1, c2} = costs
  L.Vec{+c1n, c1_s} = c1
  L.Vec{+c2n, c2_s} = c2
  +dok = mvo_con.dims_ok(bm, bn, cm, cn, dn, an, w0n, lwn, uwn, am, anc, lcn, ucn, c1n, c2n)
  mvo_con.pick(dok, b, cov_f, d_s, a_s, w0_s, lw_s, uw_s, a_mat, lc_v, uc_v, c1_s, c2_s, bm, bn, am, gmv, risk_aversion, cfg)

# ---------------------------------------------------------------- parallel map & causal scan

type Two<-A: Data> is Data:
  Two{l: List<&2, A>, r: List<&2, A>}

def split.cons(-A: Data, h: A, two: Two<A>) -> Two<A>:
  Two{l, r} = two
  Two{h <> l, r}

def split(-A: Data, k: Nat, xs: List<&2, A>) -> Two<A>:
  match k xs:
    case 0n _:
      Two{Nil{}, xs}
    case 1n+p Nil{}:
      Two{Nil{}, Nil{}}
    case 1n+p Con{h, t}:
      split.cons(A, h, split(A, p, t))

def pseq(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, xs: List<&2, A>, +c: C) -> List<&2, B>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      f(c, h) <> pseq(~A, ~B, ~C, ~f, t, c)

def par(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, +depth: Nat, two: Two<A>, +h: U32, +r: U32, +c: C) -> List<&2, B>:
  match depth:
    case 0n:
      Two{xl, xr} = two
      a b = pseq(~A, ~B, ~C, ~f, xl, c) pseq(~A, ~B, ~C, ~f, xr, c)
      List.append(&2, B, a, b)
    case 1n+d:
      Two{xl, xr} = two
      +hl = (h >> 1n : U32)
      +hr = (r >> 1n : U32)
      a b = par(~A, ~B, ~C, ~f, d, split(A, U32.to_nat(hl), xl), hl, (h - hl : U32), c) par(~A, ~B, ~C, ~f, d, split(A, U32.to_nat(hr), xr), hr, (r - hr : U32), c)
      List.append(&2, B, a, b)

# Parallel map over a list of known length t: 2 tasks below 64, 64 tasks at 64+.
def pmap(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, xs: List<&2, A>, +t: U32, +c: C) -> List<&2, B>:
  +h = (t >> 1n : U32)
  +d = Bool.pick(Nat, U32.is_lt(t, 64), 0n, 5n)
  par(~A, ~B, ~C, ~f, d, split(A, U32.to_nat(h), xs), h, (t - h : U32), c)

# Strictly causal left scan: output[i] depends only on input[0..i] and s0.
def scan(~A: Data, ~S: Data, ~step: S -> A -> S, xs: List<&2, A>, s: S) -> List<&2, S>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      +s1 = step(s, h)
      s1 <> scan(~A, ~S, ~step, t, s1)

# ---------------------------------------------------------------- hedging (Ch 12)

# Result of beta-error shrinkage hedging (Paleologo Ch 12.3 Eq 12.6-12.7).
type HedgeShrink is Data:
  HedgeShrink{
    raw_exposure: F32,
    error_var: F32,
    shrink_factor: F32,
    hedge_size: F32
  }

def hedge_ratio.div(ok: Bool, num: F32, den: F32) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      Some{(0.0 - (num / den : F32) : F32)}
    case False{}:
      None{}

def hedge_ratio.dots(mnum: Maybe<&2, F32>, mden: Maybe<&2, F32>) -> Maybe<&2, F32>:
  match mnum mden:
    case Some{num} Some{+den}:
      hedge_ratio.div(F32.is_gt(den, 0.0), num, den)
    case _ _:
      None{}

def hedge_ratio.go(momh: Maybe<&2, L.Vec>, w_core: L.Vec, w_hedge: L.Vec) -> Maybe<&2, F32>:
  match momh:
    case Some{+omh}:
      hedge_ratio.dots(L.dot(w_core, omh), L.dot(w_hedge, omh))
    case None{}:
      None{}

# Optimal single-instrument hedge size x_h^* = -beta(r_c, r_h) (Eq 12.2, 12.4).
# Hedged portfolio is w_core + x_h^* * w_hedge.
def hedge_ratio_model(fm: FactorModel, w_core: L.Vec, +w_hedge: L.Vec) -> Maybe<&2, F32>:
  hedge_ratio.go(cov_matvec(fm, w_hedge), w_core, w_hedge)

def hedge_inst.chol(ml: Maybe<&2, L.Mat>, rhs: L.Vec) -> Maybe<&2, L.Vec>:
  match ml:
    case Some{l}:
      L.cholesky_solve(l, rhs)
    case None{}:
      None{}

def hedge_inst.solve(mgh: Maybe<&2, L.Mat>, mrhs: Maybe<&2, L.Vec>) -> Maybe<&2, L.Vec>:
  match mgh mrhs:
    case Some{gh} Some{rhs}:
      hedge_inst.chol(L.cholesky(gh), rhs)
    case _ _:
      None{}

def hedge_inst.add(mfac: Maybe<&2, L.Mat>, midio: Maybe<&2, L.Mat>, mrhs: Maybe<&2, L.Vec>) -> Maybe<&2, L.Vec>:
  match mfac midio:
    case Some{fac} Some{idio}:
      hedge_inst.solve(L.madd(fac, idio), mrhs)
    case _ _:
      None{}

def hedge_inst.neg(mv: Maybe<&2, L.Vec>) -> Maybe<&2, L.Vec>:
  match mv:
    case Some{v}:
      Some{L.vscale((0.0 - 1.0 : F32), v)}
    case None{}:
      None{}

def hedge_inst.rhs(momc: Maybe<&2, L.Vec>, h_mat: L.Mat) -> Maybe<&2, L.Vec>:
  match momc:
    case Some{omc}:
      hedge_inst.neg(L.matvec_t(h_mat, omc))
    case None{}:
      None{}

def hedge_inst.fbh(mofbh: Maybe<&2, L.Mat>, bh: L.Mat, midio: Maybe<&2, L.Mat>, mrhs: Maybe<&2, L.Vec>) -> Maybe<&2, L.Vec>:
  match mofbh:
    case Some{ofbh}:
      hedge_inst.add(L.matmul(L.transpose(bh), ofbh), midio, mrhs)
    case None{}:
      None{}

def hedge_inst.bh(mbh: Maybe<&2, L.Mat>, cov_f: L.Mat, midio: Maybe<&2, L.Mat>, mrhs: Maybe<&2, L.Vec>) -> Maybe<&2, L.Vec>:
  match mbh:
    case Some{+bh}:
      hedge_inst.fbh(L.matmul(cov_f, bh), bh, midio, mrhs)
    case None{}:
      None{}

def hedge_inst.k0(is_k0: Bool, b: L.Mat, cov_f: L.Mat, idio_var: L.Vec, +h_mat: L.Mat, mrhs: Maybe<&2, L.Vec>) -> Maybe<&2, L.Vec>:
  match is_k0:
    case True{}:
      hedge_inst.solve(L.wgram(h_mat, idio_var), mrhs)
    case False{}:
      hedge_inst.bh(L.matmul(L.transpose(b), h_mat), cov_f, L.wgram(h_mat, idio_var), mrhs)

def hedge_inst.m0(is_m0: Bool, fm: FactorModel, w_core: L.Vec, +h_mat: L.Mat) -> Maybe<&2, L.Vec>:
  match is_m0:
    case True{}:
      Some{L.Vec.zeros(0)}
    case False{}:
      FactorModel{+b, +cov_f, +idio_var} = fm
      L.Mat{_, +bn, _} = b
      hedge_inst.k0(U32.is_eq(bn, 0), b, cov_f, idio_var, h_mat, hedge_inst.rhs(cov_matvec(fm, w_core), h_mat))

def hedge_inst.pick(ok: Bool, hm: U32, fm: FactorModel, w_core: L.Vec, h_mat: L.Mat) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      hedge_inst.m0(U32.is_eq(hm, 0), fm, w_core, h_mat)
    case False{}:
      None{}

# Multi-instrument minimum-variance hedge x^* = -(H^T Omega_r H)^{-1} (H^T Omega_r w_core).
# h_mat is N x M (columns are tradeable hedge baskets/ETFs/FMPs). Returns length-M weights x^*.
def hedge_instruments(+fm: FactorModel, +w_core: L.Vec, +h_mat: L.Mat) -> Maybe<&2, L.Vec>:
  FactorModel{L.Mat{+bm, _, _}, _, _} = fm
  L.Vec{wn, _} = w_core
  L.Mat{hn, +hm, _} = h_mat
  hedge_inst.pick(Bool.and(U32.is_eq(bm, wn), U32.is_eq(bm, hn)), hm, fm, w_core, h_mat)

def hedge_fexact.apply(mp: Maybe<&2, L.Mat>, mbc: Maybe<&2, L.Vec>) -> Maybe<&2, L.Vec>:
  match mp mbc:
    case Some{p} Some{bc}:
      L.matvec(p, L.vscale((0.0 - 1.0 : F32), bc))
    case _ _:
      None{}

# Exact zero-factor-exposure hedge via FMPs: w_h = -P (B^T w_core) (Ch 12.2.1 Procedure 12.2).
def hedge_factor_exact(+fm: FactorModel, w_core: L.Vec) -> Maybe<&2, L.Vec>:
  hedge_fexact.apply(fmp(fm), exposures(fm, w_core))

def list_sq(xs: List<&2, F32>) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      (h * h : F32) <> list_sq(t)

def vec_sq(v: L.Vec) -> L.Vec:
  L.Vec{n, xs} = v
  L.Vec{n, list_sq(xs)}

def hedge_shrink.build(mraw: Maybe<&2, F32>, mev: Maybe<&2, F32>) -> Maybe<&2, HedgeShrink>:
  match mraw mev:
    case Some{+raw} Some{+ev}:
      +raw2 = (raw * raw : F32)
      +yh = Bool.pick(F32, F32.is_gt(raw2, 0.0), fmax(0.0, (1.0 - (ev / raw2 : F32) : F32)), 0.0)
      +xh = (0.0 - (yh * raw : F32) : F32)
      Some{HedgeShrink{raw, ev, yh, xh}}
    case _ _:
      None{}

def hedge_shrink.nonneg(ok: Bool, +w: L.Vec, beta_hat: L.Vec, se_beta: L.Vec) -> Maybe<&2, HedgeShrink>:
  match ok:
    case True{}:
      hedge_shrink.build(L.dot(w, beta_hat), vec_quad_diag(w, vec_sq(se_beta)))
    case False{}:
      None{}

def hedge_shrink.pick(ok: Bool, ses: List<&2, F32>, w: L.Vec, beta_hat: L.Vec, se_beta: L.Vec) -> Maybe<&2, HedgeShrink>:
  match ok:
    case True{}:
      hedge_shrink.nonneg(all_nonneg(ses), w, beta_hat, se_beta)
    case False{}:
      None{}

# Beta-error shrinkage hedge with diagonal error variance diag(se_beta^2) (Eq 12.6-12.7).
def hedge_beta_shrink(+w: L.Vec, +beta_hat: L.Vec, +se_beta: L.Vec) -> Maybe<&2, HedgeShrink>:
  L.Vec{+wn, _} = w
  L.Vec{bn, _} = beta_hat
  L.Vec{sn, ses} = se_beta
  hedge_shrink.pick(Bool.and(U32.is_eq(wn, bn), U32.is_eq(wn, sn)), ses, w, beta_hat, se_beta)

def hedge_shrink_cov.pick(ok: Bool, +w: L.Vec, beta_hat: L.Vec, cov_eta: L.Mat) -> Maybe<&2, HedgeShrink>:
  match ok:
    case True{}:
      hedge_shrink.build(L.dot(w, beta_hat), L.quad_form(w, cov_eta))
    case False{}:
      None{}

# Beta-error shrinkage hedge with general error covariance Omega_eta (Ch 12.3 step 4).
def hedge_beta_shrink_cov(+w: L.Vec, +beta_hat: L.Vec, +cov_eta: L.Mat) -> Maybe<&2, HedgeShrink>:
  L.Vec{+wn, _} = w
  L.Vec{bn, _} = beta_hat
  L.Mat{+cm, cn, _} = cov_eta
  hedge_shrink_cov.pick(Bool.and(U32.is_eq(wn, bn), Bool.and(U32.is_eq(wn, cm), U32.is_eq(cm, cn))), w, beta_hat, cov_eta)

def hedge_track.scale(mbz: Maybe<&2, F32>, z: L.Vec, +mu_h: F32, +sigma_h: F32) -> Maybe<&2, L.Vec>:
  match mbz:
    case Some{bz}:
      +mu2 = (mu_h * mu_h : F32)
      +num = (mu2 + (sigma_h * sigma_h : F32) : F32)
      +den = (1.0 + (mu2 * bz : F32) : F32)
      Some{L.vscale((num / den : F32), z)}
    case None{}:
      None{}

def hedge_track.after_wb(mz: Maybe<&2, L.Vec>, beta_hat: L.Vec, +mu_h: F32, +sigma_h: F32) -> Maybe<&2, L.Vec>:
  match mz:
    case Some{+z}:
      hedge_track.scale(L.dot(beta_hat, z), z, mu_h, sigma_h)
    case None{}:
      None{}

def hedge_track.with_d(md: Maybe<&2, L.Vec>, b: L.Mat, cov_f: L.Mat, +beta_hat: L.Vec, +mu_h: F32, +sigma_h: F32) -> Maybe<&2, L.Vec>:
  match md:
    case Some{d_eff}:
      hedge_track.after_wb(L.woodbury_solve(d_eff, b, cov_f, beta_hat), beta_hat, mu_h, sigma_h)
    case None{}:
      None{}

def hedge_track.pos(ok: Bool, b: L.Mat, cov_f: L.Mat, idio_var: L.Vec, beta_hat: L.Vec, se_beta: L.Vec, +mu_h: F32, +sigma_h: F32) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      +mu2 = (mu_h * mu_h : F32)
      hedge_track.with_d(L.vadd(idio_var, L.vscale(mu2, vec_sq(se_beta))), b, cov_f, beta_hat, mu_h, sigma_h)
    case False{}:
      None{}

def hedge_track.pick(ok: Bool, ses: List<&2, F32>, b: L.Mat, cov_f: L.Mat, idio_var: L.Vec, beta_hat: L.Vec, se_beta: L.Vec, +mu_h: F32, +sigma_h: F32) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      hedge_track.pos(Bool.and(F32.is_gt(sigma_h, 0.0), all_nonneg(ses)), b, cov_f, idio_var, beta_hat, se_beta, mu_h, sigma_h)
    case False{}:
      None{}

# Regularized tracking portfolio for a non-tradeable time series (Ch 12.4):
# solves (Omega_r + mu_h^2 diag(se^2) + mu_h^2 beta beta^T) w* = (mu_h^2 + sigma_h^2) beta.
def hedge_track_series(fm: FactorModel, +beta_hat: L.Vec, +se_beta: L.Vec, +mu_h: F32, +sigma_h: F32) -> Maybe<&2, L.Vec>:
  FactorModel{+b, cov_f, idio_var} = fm
  L.Mat{+bm, _, _} = b
  L.Vec{bn, _} = beta_hat
  L.Vec{sn, ses} = se_beta
  hedge_track.pick(Bool.and(U32.is_eq(bm, bn), U32.is_eq(bm, sn)), ses, b, cov_f, idio_var, beta_hat, se_beta, mu_h, sigma_h)

# ---------------------------------------------------------------- dynamic risk sizing (Ch 13)

type DrawdownState is Data:
  DrawdownState{
    wealth: F32,
    high_watermark: F32,
    drawdown: F32,
    fraction: F32
  }

def kelly_fraction.pos(ok: Bool, mu: F32, +sigma: F32) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      Some{(mu / (sigma * sigma : F32) : F32)}
    case False{}:
      None{}

# Continuous-time / second-order Kelly fraction x* = mu / sigma^2 (Ch 13.1).
def kelly_fraction(mu: F32, +sigma: F32) -> Maybe<&2, F32>:
  kelly_fraction.pos(F32.is_gt(sigma, 0.0), mu, sigma)

def kelly_disc.pos(ok: Bool, +mu: F32, +sigma: F32) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      Some{(mu / ((mu * mu : F32) + (sigma * sigma : F32) : F32) : F32)}
    case False{}:
      None{}

# Discrete-time Gaussian second-order Kelly fraction x_1* = mu / (mu^2 + sigma^2) (Eq 13.9).
def kelly_fraction_discrete(+mu: F32, +sigma: F32) -> Maybe<&2, F32>:
  kelly_disc.pos(F32.is_gt(sigma, 0.0), mu, sigma)

def frac_kelly.pos(ok: Bool, mu: F32, +sigma: F32, frac: F32) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      Some{(frac * (mu / (sigma * sigma : F32) : F32) : F32)}
    case False{}:
      None{}

# Fractional Kelly sizing f = frac * (mu / sigma^2) (Eq 13.14).
def fractional_kelly(mu: F32, +sigma: F32, +frac: F32) -> Maybe<&2, F32>:
  frac_kelly.pos(Bool.and(F32.is_gt(sigma, 0.0), F32.is_ge(frac, 0.0)), mu, sigma, frac)

def gz_formula(+kelly: F32, +max_dd: F32, +cur_dd: F32) -> F32:
  +denom = (1.0 - cur_dd : F32)
  +red = Bool.pick(F32, F32.is_gt(denom, 0.0), fmax(0.0, (1.0 - ((1.0 - max_dd : F32) / denom : F32) : F32)), 0.0)
  (kelly * red : F32)

def gz.ok(ok: Bool, mu: F32, +sigma: F32, max_dd: F32, cur_dd: F32) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      Some{gz_formula((mu / (sigma * sigma : F32) : F32), max_dd, cur_dd)}
    case False{}:
      None{}

# Grossman-Zhou drawdown-controlled dynamic Kelly fraction (Eq 13.13, 13.15):
# f = (mu / sigma^2) * max(0, 1 - (1 - max_dd) / (1 - cur_dd)).
def grossman_zhou(mu: F32, +sigma: F32, +max_dd: F32, +cur_dd: F32) -> Maybe<&2, F32>:
  +d_ok = Bool.and(F32.is_gt(max_dd, 0.0), F32.is_le(max_dd, 1.0))
  +c_ok = Bool.and(F32.is_ge(cur_dd, 0.0), F32.is_gt(1.0, cur_dd))
  gz.ok(Bool.and(F32.is_gt(sigma, 0.0), Bool.and(d_ok, c_ok)), mu, sigma, max_dd, cur_dd)

type GzState is Data:
  GzState{kelly: F32, max_dd: F32, dd: DrawdownState}

def gz_step(st: GzState, r: F32) -> GzState:
  GzState{+kelly, +max_dd, DrawdownState{w, m, _, f}} = st
  +w1 = fmax(0.0, (w * (1.0 + (f * r : F32) : F32) : F32))
  +m1 = fmax(m, w1)
  +d1 = Bool.pick(F32, F32.is_gt(m1, 0.0), (1.0 - (w1 / m1 : F32) : F32), 1.0)
  +f1 = gz_formula(kelly, max_dd, d1)
  GzState{kelly, max_dd, DrawdownState{w1, m1, d1, f1}}

def gz_extract(xs: List<&2, GzState>) -> List<&2, DrawdownState>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{GzState{_, _, dd}, t}:
      dd <> gz_extract(t)

def gz_path.ok(ok: Bool, returns: List<&2, F32>, mu: F32, +sigma: F32, +max_dd: F32) -> Maybe<&2, List<&2, DrawdownState>>:
  match ok:
    case True{}:
      +kelly = (mu / (sigma * sigma : F32) : F32)
      +f0 = (kelly * max_dd : F32)
      s0 = {GzState{kelly, max_dd, DrawdownState{1.0, 1.0, 0.0, f0}} : GzState}
      Some{gz_extract(scan(~F32, ~GzState, ~gz_step, returns, s0))}
    case False{}:
      None{}

# Strictly causal Grossman-Zhou wealth/drawdown/allocation path over a return series (Ch 13.4).
# Proved causal in PROOF.bend via scan_causal.
def grossman_zhou_path(returns: List<&2, F32>, mu: F32, +sigma: F32, +max_dd: F32) -> Maybe<&2, List<&2, DrawdownState>>:
  +d_ok = Bool.and(F32.is_gt(max_dd, 0.0), F32.is_le(max_dd, 1.0))
  gz_path.ok(Bool.and(F32.is_gt(sigma, 0.0), d_ok), returns, mu, sigma, max_dd)

# ---------------------------------------------------------------- ex-post performance attribution (Ch 14)

# Single-period holdings-based attribution and uncertainty (Ch 14.1, 14.2).
type PeriodAttrib is Data:
  PeriodAttrib{
    position_pnl: F32,
    trading_pnl: F32,
    factor_pnl: F32,
    idio_pnl: F32,
    factor_contrib: L.Vec,
    idio_contrib: L.Vec,
    error_var: F32
  }

# Maximal attribution to a factor subset S via Schur complement rotation (Ch 14.3).
type MaxAttrib is Data:
  MaxAttrib{
    adjusted_betas: L.Vec,
    subset_pnl: F32,
    resid_f_ret: L.Vec,
    resid_pnl: F32,
    resid_cov: L.Mat
  }

# One group's result in nested maximal attribution (Ch 14.3 Procedure 14.2).
type NestedGroup is Data:
  NestedGroup{
    adjusted_betas: L.Vec,
    pnl: F32
  }

# Selection vs. sizing IR decomposition (Ch 14.4).
type SelectionSizing is Data:
  SelectionSizing{
    ir: F32,
    selection: F32,
    diversification: F32,
    sizing: F32,
    sel_long: F32,
    sel_short: F32,
    q_long: F32,
    q_short: F32
  }

def list_sum.go(xs: List<&2, F32>, acc: F32) -> F32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      list_sum.go(t, (acc + h : F32))

def vec_sum(v: L.Vec) -> F32:
  L.Vec{_, xs} = v
  list_sum.go(xs, 0.0)

def est_fret.pos(ok: Bool, b: L.Mat, idio_var: L.Vec, r: L.Vec) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      L.wlstsq(b, vec_inv(idio_var), r)
    case False{}:
      None{}

def est_fret.k0(is_k0: Bool, ds: List<&2, F32>, b: L.Mat, idio_var: L.Vec, r: L.Vec) -> Maybe<&2, L.Vec>:
  match is_k0:
    case True{}:
      Some{L.Vec.zeros(0)}
    case False{}:
      est_fret.pos(all_pos(ds), b, idio_var, r)

def est_fret.pick(ok: Bool, bn: U32, ds: List<&2, F32>, b: L.Mat, idio_var: L.Vec, r: L.Vec) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      est_fret.k0(U32.is_eq(bn, 0), ds, b, idio_var, r)
    case False{}:
      None{}

# Cross-sectional WLS factor return estimate f_hat = (B^T Omega_eps^{-1} B)^{-1} B^T Omega_eps^{-1} r.
def estimate_factor_returns(fm: FactorModel, +r: L.Vec) -> Maybe<&2, L.Vec>:
  FactorModel{+b, _, +idio_var} = fm
  L.Mat{+bm, +bn, _} = b
  L.Vec{+dn, ds} = idio_var
  L.Vec{+rn, _} = r
  est_fret.pick(Bool.and(U32.is_eq(bm, dn), U32.is_eq(bm, rn)), bn, ds, b, idio_var, r)

def aev.norm2(my: Maybe<&2, L.Vec>) -> Maybe<&2, F32>:
  match my:
    case Some{y}:
      +nrm = L.norm2(y)
      Some{(nrm * nrm : F32)}
    case None{}:
      None{}

def aev.from_qr(mqr: Maybe<&2, L.QR>, mexp: Maybe<&2, L.Vec>) -> Maybe<&2, F32>:
  match mqr mexp:
    case Some{L.QR{_, r}} Some{exp}:
      aev.norm2(L.solve_lower(L.transpose(r), exp))
    case _ _:
      None{}

def aev.weighted(ma: Maybe<&2, L.Mat>, mexp: Maybe<&2, L.Vec>) -> Maybe<&2, F32>:
  match ma:
    case Some{a}:
      aev.from_qr(L.qr_thin(a), mexp)
    case None{}:
      None{}

def aev.pos(ok: Bool, +b: L.Mat, idio_var: L.Vec, w: L.Vec) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      aev.weighted(L.diag_mul(vec_inv_sqrt(idio_var), b), L.matvec_t(b, w))
    case False{}:
      None{}

def aev.k0(is_k0: Bool, ds: List<&2, F32>, b: L.Mat, idio_var: L.Vec, w: L.Vec) -> Maybe<&2, F32>:
  match is_k0:
    case True{}:
      Some{0.0}
    case False{}:
      aev.pos(all_pos(ds), b, idio_var, w)

def aev.pick(ok: Bool, bn: U32, ds: List<&2, F32>, b: L.Mat, idio_var: L.Vec, w: L.Vec) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      aev.k0(U32.is_eq(bn, 0), ds, b, idio_var, w)
    case False{}:
      None{}

# Attribution error variance b^T (B^T Omega_eps^{-1} B)^{-1} b (Ch 14.2.2).
def attrib_error_var(fm: FactorModel, +w: L.Vec) -> Maybe<&2, F32>:
  FactorModel{+b, _, +idio_var} = fm
  L.Mat{+bm, +bn, _} = b
  L.Vec{+dn, ds} = idio_var
  L.Vec{+wn, _} = w
  aev.pick(Bool.and(U32.is_eq(bm, dn), U32.is_eq(bm, wn)), bn, ds, b, idio_var, w)

def attrib_p.finish(mpos: Maybe<&2, F32>, mfc: Maybe<&2, L.Vec>, mic: Maybe<&2, L.Vec>, mev: Maybe<&2, F32>, +realized_pnl: F32) -> Maybe<&2, PeriodAttrib>:
  match mpos mfc mic mev:
    case Some{+pos} Some{+fc} Some{+ic} Some{ev}:
      Some{PeriodAttrib{pos, (realized_pnl - pos : F32), vec_sum(fc), vec_sum(ic), fc, ic, ev}}
    case _ _ _ _:
      None{}

def attrib_p.with_eps(mexp: Maybe<&2, L.Vec>, meps: Maybe<&2, L.Vec>, +w: L.Vec, r: L.Vec, f_ret: L.Vec, mev: Maybe<&2, F32>, +realized_pnl: F32) -> Maybe<&2, PeriodAttrib>:
  match mexp meps:
    case Some{exp} Some{eps}:
      attrib_p.finish(L.dot(w, r), L.vmul(exp, f_ret), L.vmul(w, eps), mev, realized_pnl)
    case _ _:
      None{}

def attrib_p.with_bf(mbf: Maybe<&2, L.Vec>, +fm: FactorModel, +w: L.Vec, +r: L.Vec, f_ret: L.Vec, +realized_pnl: F32) -> Maybe<&2, PeriodAttrib>:
  match mbf:
    case Some{bf}:
      attrib_p.with_eps(exposures(fm, w), L.vsub(r, bf), w, r, f_ret, attrib_error_var(fm, w), realized_pnl)
    case None{}:
      None{}

def attrib_p.pick(ok: Bool, +fm: FactorModel, w: L.Vec, r: L.Vec, +f_ret: L.Vec, +realized_pnl: F32) -> Maybe<&2, PeriodAttrib>:
  match ok:
    case True{}:
      FactorModel{b, _, _} = fm
      attrib_p.with_bf(L.matvec(b, f_ret), fm, w, r, f_ret, realized_pnl)
    case False{}:
      None{}

# Single-period holdings-based attribution (Ch 14.1, 14.2):
# position_pnl = factor_pnl + idio_pnl; trading_pnl = realized_pnl - position_pnl.
def attribute_period(+fm: FactorModel, +w: L.Vec, +r: L.Vec, +f_ret: L.Vec, +realized_pnl: F32) -> Maybe<&2, PeriodAttrib>:
  FactorModel{L.Mat{+bm, +bn, _}, _, _} = fm
  L.Vec{wn, _} = w
  L.Vec{rn, _} = r
  L.Vec{fn, _} = f_ret
  attrib_p.pick(Bool.and(U32.is_eq(bm, wn), Bool.and(U32.is_eq(bm, rn), U32.is_eq(bn, fn))), fm, w, r, f_ret, realized_pnl)

# ---- Maximal & nested performance attribution (Ch 14.3)

def idx_in(+x: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(U32.is_eq(x, h), idx_in(x, t))

def subset_valid(xs: List<&2, U32>, +k: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      Bool.and(U32.is_lt(h, k), Bool.and(Bool.not(idx_in(h, t)), subset_valid(t, k)))

def build_comp.go(rem: Nat, +i: U32, +sub: List<&2, U32>) -> List<&2, U32>:
  match rem:
    case 0n:
      Nil{}
    case 1n+p:
      +rest = build_comp.go(p, (i + 1 : U32), sub)
      Bool.pick(List<&2, U32>, idx_in(i, sub), rest, i <> rest)

def build_comp(+k: U32, sub: List<&2, U32>) -> List<&2, U32>:
  build_comp.go(U32.to_nat(k), 0, sub)

def get_f32_or(m: Maybe<&2, F32>) -> F32:
  match m:
    case Some{v}:
      v
    case None{}:
      0.0

def gather_vec.go(idxs: List<&2, U32>, +xs: List<&2, F32>) -> List<&2, F32>:
  match idxs:
    case Nil{}:
      Nil{}
    case Con{i, t}:
      get_f32_or(List.get(&2, F32, xs, U32.to_nat(i))) <> gather_vec.go(t, xs)

def gather_vec(+idxs: List<&2, U32>, v: L.Vec) -> L.Vec:
  L.Vec{_, xs} = v
  L.Vec{U32.from_nat(List.length(&2, U32, idxs)), gather_vec.go(idxs, xs)}

def get_row_or(m: Maybe<&2, List<&2, F32>>) -> List<&2, F32>:
  match m:
    case Some{r}:
      r
    case None{}:
      Nil{}

def gather_mat.go(r_idxs: List<&2, U32>, +c_idxs: List<&2, U32>, +rows: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match r_idxs:
    case Nil{}:
      Nil{}
    case Con{ri, t}:
      gather_vec.go(c_idxs, get_row_or(List.get(&2, List<&2, F32>, rows, U32.to_nat(ri)))) <> gather_mat.go(t, c_idxs, rows)

def gather_mat(+r_idxs: List<&2, U32>, +c_idxs: List<&2, U32>, a: L.Mat) -> L.Mat:
  L.Mat{_, _, rows} = a
  L.Mat{U32.from_nat(List.length(&2, U32, r_idxs)), U32.from_nat(List.length(&2, U32, c_idxs)), gather_mat.go(r_idxs, c_idxs, rows)}

def sym_mat.half(ms: Maybe<&2, L.Mat>) -> Maybe<&2, L.Mat>:
  match ms:
    case Some{s}:
      Some{L.scale(0.5, s)}
    case None{}:
      None{}

def sym_mat(+m: L.Mat) -> Maybe<&2, L.Mat>:
  sym_mat.half(L.madd(m, L.transpose(m)))

def max_attr.dots(msp: Maybe<&2, F32>, mrp: Maybe<&2, F32>, adj: L.Vec, rf: L.Vec, rc: L.Mat) -> Maybe<&2, MaxAttrib>:
  match msp mrp:
    case Some{sp} Some{rp}:
      Some{MaxAttrib{adj, sp, rf, rp, rc}}
    case _ _:
      None{}

def max_attr.wrap(madj: Maybe<&2, L.Vec>, mrf: Maybe<&2, L.Vec>, mrc: Maybe<&2, L.Mat>, fs: L.Vec, bbar: L.Vec) -> Maybe<&2, MaxAttrib>:
  match madj mrf mrc:
    case Some{+adj} Some{+rf} Some{rc}:
      max_attr.dots(L.dot(adj, fs), L.dot(bbar, rf), adj, rf, rc)
    case _ _ _:
      None{}

def max_attr.sym_cov(md: Maybe<&2, L.Mat>) -> Maybe<&2, L.Mat>:
  match md:
    case Some{d}:
      sym_mat(d)
    case None{}:
      None{}

def max_attr.sub_cov(mp: Maybe<&2, L.Mat>, o_bb: L.Mat) -> Maybe<&2, L.Mat>:
  match mp:
    case Some{prod}:
      max_attr.sym_cov(L.msub(o_bb, prod))
    case None{}:
      None{}

def max_attr.add_v(mxb: Maybe<&2, L.Vec>, bs: L.Vec) -> Maybe<&2, L.Vec>:
  match mxb:
    case Some{xb}:
      L.vadd(bs, xb)
    case None{}:
      None{}

def max_attr.sub_v(mxtf: Maybe<&2, L.Vec>, fbar: L.Vec) -> Maybe<&2, L.Vec>:
  match mxtf:
    case Some{xtf}:
      L.vsub(fbar, xtf)
    case None{}:
      None{}

def max_attr.with_x(mx: Maybe<&2, L.Mat>, bs: L.Vec, +bbar: L.Vec, +fs: L.Vec, fbar: L.Vec, o_sb: L.Mat, o_bb: L.Mat) -> Maybe<&2, MaxAttrib>:
  match mx:
    case Some{+x}:
      madj = max_attr.add_v(L.matvec(x, bbar), bs)
      mrf = max_attr.sub_v(L.matvec_t(x, fs), fbar)
      mrc = max_attr.sub_cov(L.matmul(L.transpose(o_sb), x), o_bb)
      max_attr.wrap(madj, mrf, mrc, fs, bbar)
    case None{}:
      None{}

def max_attr.chol(ml: Maybe<&2, L.Mat>, bs: L.Vec, bbar: L.Vec, fs: L.Vec, fbar: L.Vec, +o_sb: L.Mat, o_bb: L.Mat) -> Maybe<&2, MaxAttrib>:
  match ml:
    case Some{l}:
      max_attr.with_x(L.cholesky_solve_mat(l, o_sb), bs, bbar, fs, fbar, o_sb, o_bb)
    case None{}:
      None{}

def max_attr.q0(is_q0: Bool, +cov_f: L.Mat, +b: L.Vec, +f_ret: L.Vec, +sub: List<&2, U32>, +comp: List<&2, U32>) -> Maybe<&2, MaxAttrib>:
  match is_q0:
    case True{}:
      +bs = gather_vec(sub, b)
      +fs = gather_vec(sub, f_ret)
      max_attr.dots(L.dot(bs, fs), Some{0.0}, bs, L.Vec.zeros(0), L.Mat{0, 0, Nil{}})
    case False{}:
      o_ss = gather_mat(sub, sub, cov_f)
      o_sb = gather_mat(sub, comp, cov_f)
      o_bb = gather_mat(comp, comp, cov_f)
      bs = gather_vec(sub, b)
      bbar = gather_vec(comp, b)
      fs = gather_vec(sub, f_ret)
      fbar = gather_vec(comp, f_ret)
      max_attr.chol(L.cholesky(o_ss), bs, bbar, fs, fbar, o_sb, o_bb)

def max_attr.p0(is_p0: Bool, +cov_f: L.Mat, +b: L.Vec, +f_ret: L.Vec, +sub: List<&2, U32>, +k: U32) -> Maybe<&2, MaxAttrib>:
  match is_p0:
    case True{}:
      max_attr.dots(Some{0.0}, L.dot(b, f_ret), L.Vec.zeros(0), f_ret, cov_f)
    case False{}:
      +comp = build_comp(k, sub)
      max_attr.q0(Nat.is_eq(List.length(&2, U32, comp), 0n), cov_f, b, f_ret, sub, comp)

def max_attr.valid(ok: Bool, cov_f: L.Mat, b: L.Vec, f_ret: L.Vec, +sub: List<&2, U32>, +k: U32) -> Maybe<&2, MaxAttrib>:
  match ok:
    case True{}:
      max_attr.p0(Nat.is_eq(List.length(&2, U32, sub), 0n), cov_f, b, f_ret, sub, k)
    case False{}:
      None{}

def max_attr.pick(ok: Bool, cov_f: L.Mat, b: L.Vec, f_ret: L.Vec, +sub: List<&2, U32>, +k: U32) -> Maybe<&2, MaxAttrib>:
  match ok:
    case True{}:
      max_attr.valid(subset_valid(sub, k), cov_f, b, f_ret, sub, k)
    case False{}:
      None{}

# Maximal performance attribution for factor subset S (Ch 14.3, Eq 14.6-14.10).
# Returns None on dimension mismatch or invalid/duplicate subset indices.
def maximal_attribution(+cov_f: L.Mat, +b: L.Vec, +f_ret: L.Vec, subset: List<&2, U32>) -> Maybe<&2, MaxAttrib>:
  L.Mat{+cm, cn, _} = cov_f
  L.Vec{bn, _} = b
  L.Vec{fn, _} = f_ret
  max_attr.pick(Bool.and(U32.is_eq(cm, cn), Bool.and(U32.is_eq(cm, bn), U32.is_eq(cm, fn))), cov_f, b, f_ret, subset, cm)

# ---- Nested maximal attribution over a sequence of disjoint factor groups (Ch 14.3 Proc 14.2)

def find_pos.go(+x: U32, xs: List<&2, U32>, +pos: U32) -> Maybe<&2, U32>:
  match xs:
    case Nil{}:
      None{}
    case Con{h, t}:
      Bool.pick(Maybe<&2, U32>, U32.is_eq(x, h), Some{pos}, find_pos.go(x, t, (pos + 1 : U32)))

def map_to_local.cons(mp: Maybe<&2, U32>, mr: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match mp mr:
    case Some{p} Some{r}:
      Some{p <> r}
    case _ _:
      None{}

def map_to_local(grp: List<&2, U32>, +avail: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match grp:
    case Nil{}:
      Some{Nil{}}
    case Con{g, t}:
      map_to_local.cons(find_pos.go(g, avail, 0), map_to_local(t, avail))

def filter_avail(avail: List<&2, U32>, +grp: List<&2, U32>) -> List<&2, U32>:
  match avail:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      +rest = filter_avail(t, grp)
      Bool.pick(List<&2, U32>, idx_in(h, grp), rest, h <> rest)

def range_u32.go(rem: Nat, +i: U32) -> List<&2, U32>:
  match rem:
    case 0n:
      Nil{}
    case 1n+p:
      i <> range_u32.go(p, (i + 1 : U32))

type NestedCur is Data:
  NestedCur{cov_cur: L.Mat, b_cur: L.Vec, f_cur: L.Vec, avail: List<&2, U32>, acc: List<&2, NestedGroup>}

def rev_ng.go(xs: List<&2, NestedGroup>, acc: List<&2, NestedGroup>) -> List<&2, NestedGroup>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      rev_ng.go(t, h <> acc)

def nested.step_one(mma: Maybe<&2, MaxAttrib>, b_cur: L.Vec, comp_loc: List<&2, U32>, avail_next: List<&2, U32>, acc: List<&2, NestedGroup>) -> Maybe<&2, NestedCur>:
  match mma:
    case Some{MaxAttrib{adj, sp, rf, _, rc}}:
      Some{NestedCur{rc, gather_vec(comp_loc, b_cur), rf, avail_next, NestedGroup{adj, sp} <> acc}}
    case None{}:
      None{}

def nested.with_loc(mloc: Maybe<&2, List<&2, U32>>, +cov_cur: L.Mat, +b_cur: L.Vec, f_cur: L.Vec, avail: List<&2, U32>, grp: List<&2, U32>, acc: List<&2, NestedGroup>) -> Maybe<&2, NestedCur>:
  match mloc:
    case Some{+loc}:
      L.Mat{k_cur, _, _} = cov_cur
      comp_loc = build_comp(k_cur, loc)
      avail_next = filter_avail(avail, grp)
      nested.step_one(maximal_attribution(cov_cur, b_cur, f_cur, loc), b_cur, comp_loc, avail_next, acc)
    case None{}:
      None{}

def nested.go(groups: List<&2, List<&2, U32>>, cur: Maybe<&2, NestedCur>) -> Maybe<&2, List<&2, NestedGroup>>:
  match groups cur:
    case _ None{}:
      None{}
    case Nil{} Some{NestedCur{_, _, _, _, acc}}:
      Some{rev_ng.go(acc, Nil{})}
    case Con{+grp, rest} Some{NestedCur{cov_cur, b_cur, f_cur, +avail, acc}}:
      nested.go(rest, nested.with_loc(map_to_local(grp, avail), cov_cur, b_cur, f_cur, avail, grp, acc))

def nested.pick(ok: Bool, cov_f: L.Mat, b: L.Vec, f_ret: L.Vec, groups: List<&2, List<&2, U32>>, +k: U32) -> Maybe<&2, List<&2, NestedGroup>>:
  match ok:
    case True{}:
      nested.go(groups, Some{NestedCur{cov_f, b, f_ret, range_u32.go(U32.to_nat(k), 0), Nil{}}})
    case False{}:
      None{}

# Nested maximal attribution over ordered disjoint factor groups (Ch 14.3 Procedure 14.2).
def nested_attribution(+cov_f: L.Mat, +b: L.Vec, +f_ret: L.Vec, groups: List<&2, List<&2, U32>>) -> Maybe<&2, List<&2, NestedGroup>>:
  L.Mat{+cm, cn, _} = cov_f
  L.Vec{bn, _} = b
  L.Vec{fn, _} = f_ret
  nested.pick(Bool.and(U32.is_eq(cm, cn), Bool.and(U32.is_eq(cm, bn), U32.is_eq(cm, fn))), cov_f, b, f_ret, groups, cm)

# ---- Selection vs. sizing IR decomposition (Ch 14.4)

type SsAcc is Data:
  SsAcc{
    sum_xy: F32,
    sum_x: F32,
    sum_x2: F32,
    sum_y: F32,
    sum_yl: F32,
    sum_ys: F32,
    n_long: F32,
    n_short: F32,
    n_tot: F32
  }

def sgn_f32(+x: F32) -> F32:
  Bool.pick(F32, F32.is_gt(x, 0.0), 1.0, Bool.pick(F32, F32.is_gt(0.0, x), (0.0 - 1.0 : F32), 0.0))

def ss.go(ws: List<&2, F32>, es: List<&2, F32>, ds: List<&2, F32>, acc: SsAcc) -> SsAcc:
  match ws es ds:
    case Con{+w, wt} Con{e, et} Con{d, dt}:
      SsAcc{sxy, sx, sx2, sy, +syl, +sys, +nl, +ns, nt} = acc
      +sig = F32.sqrt(d)
      +x = F32.abs((sig * w : F32))
      +y = ((e / sig : F32) * sgn_f32(w) : F32)
      +is_l = F32.is_gt(w, 0.0)
      +is_s = F32.is_gt(0.0, w)
      +syl2 = Bool.pick(F32, is_l, (syl + y : F32), syl)
      +sys2 = Bool.pick(F32, is_s, (sys + y : F32), sys)
      +nl2 = Bool.pick(F32, is_l, (nl + 1.0 : F32), nl)
      +ns2 = Bool.pick(F32, is_s, (ns + 1.0 : F32), ns)
      ss.go(wt, et, dt, SsAcc{(sxy + (x * y : F32) : F32), (sx + x : F32), (sx2 + (x * x : F32) : F32), (sy + y : F32), syl2, sys2, nl2, ns2, (nt + 1.0 : F32)})
    case _ _ _:
      acc

def ss.finish(acc: SsAcc) -> SelectionSizing:
  SsAcc{+sxy, +sx, +sx2, +sy, +syl, +sys, +nl, +ns, +nt} = acc
  +vol = F32.sqrt(sx2)
  +has_v = F32.is_gt(vol, 0.0)
  +ir = Bool.pick(F32, has_v, (sxy / vol : F32), 0.0)
  +sel = (sy / nt : F32)
  +div = Bool.pick(F32, has_v, (sx / vol : F32), 0.0)
  +cov_xy = ((sxy / nt : F32) - ((sx / nt : F32) * sel : F32) : F32)
  +siz = Bool.pick(F32, has_v, ((nt / vol : F32) * cov_xy : F32), 0.0)
  +sel_l = Bool.pick(F32, F32.is_gt(nl, 0.0), (syl / nl : F32), 0.0)
  +sel_s = Bool.pick(F32, F32.is_gt(ns, 0.0), (sys / ns : F32), 0.0)
  SelectionSizing{ir, sel, div, siz, sel_l, sel_s, (nl / nt : F32), (ns / nt : F32)}

def ss.pos(ok: Bool, ws: List<&2, F32>, es: List<&2, F32>, ds: List<&2, F32>) -> Maybe<&2, SelectionSizing>:
  match ok:
    case True{}:
      Some{ss.finish(ss.go(ws, es, ds, SsAcc{0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0}))}
    case False{}:
      None{}

def ss.pick(ok: Bool, ws: List<&2, F32>, es: List<&2, F32>, +ds: List<&2, F32>) -> Maybe<&2, SelectionSizing>:
  match ok:
    case True{}:
      ss.pos(all_pos(ds), ws, es, ds)
    case False{}:
      None{}

# Selection vs. sizing IR decomposition (Ch 14.4):
# ir == selection * diversification + sizing, and selection == q_long * sel_long + q_short * sel_short.
def selection_sizing(w: L.Vec, eps: L.Vec, idio_var: L.Vec) -> Maybe<&2, SelectionSizing>:
  L.Vec{+wn, ws} = w
  L.Vec{en, es} = eps
  L.Vec{dn, ds} = idio_var
  ss.pick(Bool.and(U32.is_lt(0, wn), Bool.and(U32.is_eq(wn, en), U32.is_eq(wn, dn))), ws, es, ds)

# ---- Causal multi-period forward PnL & attribution (no-lookahead proved in PROOF.bend)

type RowPair is Data:
  RowPair{w: List<&2, F32>, r: List<&2, F32>}

def dot_rows.go(ws: List<&2, F32>, rs: List<&2, F32>, acc: F32) -> F32:
  match ws rs:
    case Con{w, wt} Con{r, rt}:
      dot_rows.go(wt, rt, (acc + (w * r : F32) : F32))
    case _ _:
      acc

def dot_pair(_u: Unit, p: RowPair) -> F32:
  RowPair{w, r} = p
  dot_rows.go(w, r, 0.0)

def zip_rows(ws: List<&2, List<&2, F32>>, rs: List<&2, List<&2, F32>>) -> List<&2, RowPair>:
  match ws rs:
    case Con{w, wt} Con{r, rt}:
      RowPair{w, r} <> zip_rows(wt, rt)
    case _ _:
      Nil{}

def tail_rows(rs: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{_, t}:
      t

def forward_pnl.pick(ok: Bool, +t: U32, ws: List<&2, List<&2, F32>>, rs: List<&2, List<&2, F32>>) -> Maybe<&2, List<&2, F32>>:
  match ok:
    case True{}:
      +cnt = Bool.pick(U32, U32.is_lt(0, t), (t - 1 : U32), 0)
      Some{pmap(~RowPair, ~F32, ~Unit, ~dot_pair, zip_rows(ws, tail_rows(rs)), cnt, Unit{})}
    case False{}:
      None{}

# Causal forward PnL: pairs portfolio row t with next-period return row t + 1 (t = 0 .. T - 2).
# Row j of returns is the return over (j - 1, j], matching signal's convention.
def forward_pnl(weights: L.Mat, returns: L.Mat) -> Maybe<&2, List<&2, F32>>:
  L.Mat{+wt, wn, ws} = weights
  L.Mat{rt, rn, rs} = returns
  forward_pnl.pick(Bool.and(U32.is_eq(wt, rt), U32.is_eq(wn, rn)), wt, ws, rs)

type AttribItem is Data:
  AttribItem{fm: FactorModel, w: List<&2, F32>, r: List<&2, F32>, f: List<&2, F32>}

type AttribDims is Data:
  AttribDims{n: U32, k: U32}

def attrib_item_fn(dims: AttribDims, item: AttribItem) -> Maybe<&2, PeriodAttrib>:
  AttribDims{+n, +k} = dims
  AttribItem{fm, +w, +r, f} = item
  +pos = dot_rows.go(w, r, 0.0)
  attribute_period(fm, L.Vec{n, w}, L.Vec{n, r}, L.Vec{k, f}, pos)

def zip_attrib(fms: List<&2, FactorModel>, ws: List<&2, List<&2, F32>>, rs: List<&2, List<&2, F32>>, fs: List<&2, List<&2, F32>>) -> List<&2, AttribItem>:
  match fms ws rs fs:
    case Con{fm, fmt} Con{w, wt} Con{r, rt} Con{f, ft}:
      AttribItem{fm, w, r, f} <> zip_attrib(fmt, wt, rt, ft)
    case _ _ _ _:
      Nil{}

def forward_attrib.pick(ok: Bool, +t: U32, +n: U32, +k: U32, fms: List<&2, FactorModel>, ws: List<&2, List<&2, F32>>, rs: List<&2, List<&2, F32>>, fs: List<&2, List<&2, F32>>) -> Maybe<&2, List<&2, Maybe<&2, PeriodAttrib>>>:
  match ok:
    case True{}:
      +cnt = Bool.pick(U32, U32.is_lt(0, t), (t - 1 : U32), 0)
      Some{pmap(~AttribItem, ~Maybe<&2, PeriodAttrib>, ~AttribDims, ~attrib_item_fn, zip_attrib(fms, ws, tail_rows(rs), tail_rows(fs)), cnt, AttribDims{n, k})}
    case False{}:
      None{}

# Causal multi-period attribution: pairs (fm[t], weights[t]) with (returns[t+1], f_rets[t+1]).
def forward_attribute(+fms: List<&2, FactorModel>, weights: L.Mat, returns: L.Mat, f_rets: L.Mat) -> Maybe<&2, List<&2, Maybe<&2, PeriodAttrib>>>:
  L.Mat{+wt, +wn, ws} = weights
  L.Mat{rt, rn, rs} = returns
  L.Mat{ft, +fk, fs} = f_rets
  +ok = Bool.and(U32.is_eq(wt, rt), Bool.and(U32.is_eq(wt, ft), Bool.and(U32.is_eq(wn, rn), Nat.is_eq(List.length(&2, FactorModel, fms), U32.to_nat(wt)))))
  forward_attrib.pick(ok, wt, wn, fk, fms, ws, rs, fs)
