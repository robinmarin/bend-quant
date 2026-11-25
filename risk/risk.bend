# risk: factor & covariance estimation, factor model transformations,
# out-of-sample risk evaluation, fundamental & statistical factor models
# following Giuseppe Paleologo's "The Elements of Quantitative Investing" (Ch 4-7).
#
# Built on bend-quant-linalg@0.1.0.0 and bend-quant-portfolio@0.1.0.0 (sharing
# P.FactorModel, L.Mat, and L.Vec directly with zero conversion).
# Every non-public def is internal; LAWS.bend and PROOF.bend name internals and
# they can change in any version.
import Base
import bend-quant-linalg@0.1.0.0/linalg.bend as L
import bend-quant-portfolio@0.1.0.0/portfolio.bend as P
import ./cov.bend as C
import ./subspace_svd.bend as SSVD

# ---------------------------------------------------------------- parallel map (proved == pseq)

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

def pmap(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, xs: List<&2, A>, +t: U32, +c: C) -> List<&2, B>:
  +h = (t >> 1n : U32)
  +d = Bool.pick(Nat, U32.is_lt(t, 64), 0n, 5n)
  par(~A, ~B, ~C, ~f, d, split(A, U32.to_nat(h), xs), h, (t - h : U32), c)

# ---------------------------------------------------------------- public Data types

# Ch 4.5.2: Partitioned group risk decomposition.
type GroupRisk is Data:
  GroupRisk{
    group_cov: L.Mat,
    group_vars: L.Vec,
    group_shares: L.Vec,
    group_mcr: L.Vec,
    total_factor_var: F32,
    total_factor_vol: F32
  }

# Ch 5.1: Volatility forecast evaluation metrics.
type VolEval is Data:
  VolEval{
    qlike: F32,
    vol_mse: F32,
    bias_stat: F32,
    realized_vol: F32,
    mean_pred_vol: F32,
    count: U32
  }

# Ch 5.1.2 Eq (5.1): Multivariate Gaussian negative log-likelihood (QDIST).
type QDistResult is Data:
  QDistResult{
    mean_qdist: F32,
    total_qdist: F32,
    per_period: L.Vec
  }

# Ch 5.2.2: Mahalanobis distance precision matrix test (MALV).
type MahalanobisResult is Data:
  MahalanobisResult{
    nu_series: L.Vec,
    mean_nu: F32,
    malv: F32
  }

# Ch 5.2.1 Eq (5.2): Minimum-variance portfolio out-of-sample test.
type MvpResult is Data:
  MvpResult{
    realized_var: F32,
    realized_vol: F32,
    mean_pred_vol: F32,
    qlike: F32,
    vol_mse: F32,
    bias_stat: F32,
    returns: L.Vec,
    pred_vars: L.Vec
  }

# Ch 5.3.1: Factor-mimicking portfolio quadratic turnover.
type TurnoverResult is Data:
  TurnoverResult{
    mean_turnover: F32,
    per_period: L.Vec
  }

# Ch 5.3.2: Predicted vs EWMA realized asset beta error (BETAERR).
type BetaErrResult is Data:
  BetaErrResult{
    total_err: F32,
    mean_err: F32,
    per_period: L.Vec
  }

# Ch 6.3.1: Ledoit-Wolf shrinkage result.
type ShrinkResult is Data:
  ShrinkResult{
    cov: L.Mat,
    shrinkage: F32,
    target_diag: F32
  }

# Ch 6.4.4: Thresholded off-diagonal idiosyncratic correlation pair.
type CorrPair is Data:
  CorrPair{
    i: U32,
    j: U32,
    corr: F32
  }

# Ch 6.6.2: Numeraire currency rebasing result.
type RebaseResult is Data:
  RebaseResult{
    c_loadings: L.Mat,
    cov_c: L.Mat
  }

# Ch 6.2.1: Heston-Rouwenhorst linear side constraint C^T f = d (C is K x P, d is P).
type CSConstraint is Data:
  CSConstraint{
    c_mat: L.Mat,
    d_vec: L.Vec
  }

# Ch 6.2: Single-period cross-sectional WLS regression result.
type CSRegResult is Data:
  CSRegResult{
    f_ret: L.Vec,
    resid: L.Vec,
    est_cov: L.Mat
  }

# Ch 6.2: Multi-period estimated factor and idiosyncratic return panels.
type FactorSeries is Data:
  FactorSeries{
    f_rets: L.Mat,
    resid: L.Mat
  }

# Ch 6: Fundamental factor model estimation configuration.
type FundConfig is Data:
  FundConfig{
    hl_vol: F32,
    hl_corr: F32,
    hl_idio: F32,
    nw_lags: U32,
    shrink_f: F32,
    shrink_idio: F32,
    hl_stvu: F32,
    use_stvu: Bool,
    debias: Bool,
    eig_floor: F32
  }

def FundConfig.default() -> FundConfig:
  FundConfig{63.0, 126.0, 63.0, 2, 0.1, 0.1, 15.0, False{}, False{}, 1.0e-8}

# Ch 6: End-to-end fundamental factor model fit.
type FundModelFit is Data:
  FundModelFit{
    model: P.FactorModel,
    f_rets: L.Mat,
    resid: L.Mat
  }

# Ch 7.1: PCA / SVD factor decomposition result.
type PcaResult is Data:
  PcaResult{
    loadings: L.Mat,
    f_rets: L.Mat,
    singular_values: L.Vec,
    eigenvalues: L.Vec
  }

# Ch 7.2.5: Bai-Ng (2008) factor-count selection criteria (IC_p1 and PC_p1).
type BaiNgResult is Data:
  BaiNgResult{
    k_ic: U32,
    k_pc: U32,
    ic_values: L.Vec,
    pc_values: L.Vec
  }

# Ch 7.3.2: Eigenfactor quadratic turnover.
type EigenTurnover is Data:
  EigenTurnover{
    per_factor: L.Vec,
    mean_turnover: F32
  }

# Ch 7.5.1: Two-stage weighted statistical factor model configuration.
# shrink_mode: 0 = none, 1 = BBP/Donoho offset Eq (7.33), 2 = PPCA bulk mean, 3 = linear (k1*lam - k2).
type StatConfig is Data:
  StatConfig{
    k: U32,
    stage1_p: U32,
    hl_fast: F32,
    hl_slow: F32,
    shrink_mode: U32,
    shrink_k1: F32,
    shrink_k2: F32,
    shrink_idio: F32,
    use_subspace: Bool,
    eig_floor: F32
  }

def StatConfig.default(+k: U32) -> StatConfig:
  StatConfig{k, 5, 63.0, 126.0, 1, 1.0, 0.0, 0.1, True{}, 1.0e-8}

# Ch 7: End-to-end statistical factor model fit.
type StatModelFit is Data:
  StatModelFit{
    model: P.FactorModel,
    f_rets: L.Mat,
    resid: L.Mat,
    singular_values: L.Vec
  }

# ---------------------------------------------------------------- basic helpers

def fmax(+a: F32, +b: F32) -> F32:
  F32.max(a, b)

def fmin(+a: F32, +b: F32) -> F32:
  Bool.pick(F32, F32.is_le(a, b), a, b)

def all_pos(xs: List<&2, F32>) -> Bool:
  C.all_pos(xs)

def list_inv(xs: List<&2, F32>) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      (1.0 / h : F32) <> list_inv(t)

def list_neg(xs: List<&2, F32>) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      F32.neg(h) <> list_neg(t)

def list_take(-A: Data, k: Nat, xs: List<&2, A>) -> List<&2, A>:
  match k xs:
    case 0n _:
      Nil{}
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{h, t}:
      h <> list_take(A, p, t)

def list_drop(-A: Data, k: Nat, xs: List<&2, A>) -> List<&2, A>:
  match k xs:
    case 0n _:
      xs
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{_, t}:
      list_drop(A, p, t)

def seq_maybe.cons(-A: Data, mx: Maybe<&2, A>, mrest: Maybe<&2, List<&2, A>>) -> Maybe<&2, List<&2, A>>:
  match mx mrest:
    case Some{x} Some{xs}:
      Some{x <> xs}
    case _ _:
      None{}

def seq_maybe(-A: Data, ms: List<&2, Maybe<&2, A>>) -> Maybe<&2, List<&2, A>>:
  match ms:
    case Nil{}:
      Some{Nil{}}
    case Con{mx, rest}:
      seq_maybe.cons(A, mx, seq_maybe(A, rest))

def fm_dims_ok(fm: P.FactorModel) -> Bool:
  P.FactorModel{b, cov_f, idio_var} = fm
  L.Mat{+bm, +bn, _} = b
  L.Mat{+cm, +cn, _} = cov_f
  L.Vec{+dn, +ds} = idio_var
  Bool.and(U32.is_eq(bm, dn), Bool.and(U32.is_eq(bn, cm), Bool.and(U32.is_eq(cm, cn), all_pos(ds))))

# ---------------------------------------------------------------- re-exports from cov.bend (Ch 6.3-6.6)

def symmetrize(m: L.Mat) -> Maybe<&2, L.Mat>:
  C.symmetrize(m)

def ewma_weights(+t: U32, +half_life: F32) -> Maybe<&2, L.Vec>:
  C.ewma_weights(t, half_life)

def sample_cov(x: L.Mat, center: Bool) -> Maybe<&2, L.Mat>:
  C.sample_cov(x, center)

def ewma_cov(x: L.Mat, +half_life: F32, center: Bool) -> Maybe<&2, L.Mat>:
  C.ewma_cov(x, half_life, center)

def shrink_to_identity(cov: L.Mat, +rho: F32) -> Maybe<&2, L.Mat>:
  C.shrink_to_identity(cov, rho)

def wrap_shrink(ms: Maybe<&2, C.ShrinkResult>) -> Maybe<&2, ShrinkResult>:
  match ms:
    case Some{C.ShrinkResult{cov, sh, td}}:
      Some{ShrinkResult{cov, sh, td}}
    case None{}:
      None{}

def ledoit_wolf_cov(x: L.Mat, center: Bool) -> Maybe<&2, ShrinkResult>:
  wrap_shrink(C.ledoit_wolf_cov(x, center))

def psd_project(a: L.Mat, +eig_floor: F32) -> Maybe<&2, L.Mat>:
  C.psd_project(a, eig_floor)

def debias_factor_cov(cov_f_raw: L.Mat, b: L.Mat, idio_var: L.Vec, +eig_floor: F32) -> Maybe<&2, L.Mat>:
  C.debias_factor_cov(cov_f_raw, b, idio_var, eig_floor)

def dcc_cov(f_rets: L.Mat, +hl_vol: F32, +hl_corr: F32) -> Maybe<&2, L.Mat>:
  C.dcc_cov(f_rets, hl_vol, hl_corr)

def stvu_factor_multiplier(f_rets: L.Mat, cov_f: L.Mat, +hl_fast: F32, linear_approx: Bool) -> Maybe<&2, F32>:
  C.stvu_factor_multiplier(f_rets, cov_f, hl_fast, linear_approx)

def stvu_adjust_cov(f_rets: L.Mat, cov_f: L.Mat, +hl_fast: F32, linear_approx: Bool) -> Maybe<&2, L.Mat>:
  C.stvu_adjust_cov(f_rets, cov_f, hl_fast, linear_approx)

def cov_newey_west(x: L.Mat, +l_max: U32, +half_life: F32) -> Maybe<&2, L.Mat>:
  C.cov_newey_west(x, l_max, half_life)

def cov_autocorr_cohen(x: L.Mat, +l_max: U32, +half_life: F32) -> Maybe<&2, L.Mat>:
  C.cov_autocorr_cohen(x, l_max, half_life)

def idio_var_ewma(eps: L.Mat, +half_life: F32) -> Maybe<&2, L.Vec>:
  C.idio_var_ewma(eps, half_life)

def idio_var_shrink(idio_var: L.Vec, +rho: F32) -> Maybe<&2, L.Vec>:
  C.idio_var_shrink(idio_var, rho)

def idio_stvu(eps: L.Mat, idio_var: L.Vec, event_weights: L.Mat, +hl_fast: F32) -> Maybe<&2, L.Vec>:
  C.idio_stvu(eps, idio_var, event_weights, hl_fast)

def cai_threshold(+n: U32, +t: U32, +k_const: F32) -> Maybe<&2, F32>:
  C.cai_threshold(n, t, k_const)

def wrap_pairs.go(ps: List<&2, C.CorrPair>) -> List<&2, CorrPair>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{C.CorrPair{i, j, r}, t}:
      CorrPair{i, j, r} <> wrap_pairs.go(t)

def wrap_pairs(mp: Maybe<&2, List<&2, C.CorrPair>>) -> Maybe<&2, List<&2, CorrPair>>:
  match mp:
    case Some{ps}:
      Some{wrap_pairs.go(ps)}
    case None{}:
      None{}

def idio_corr_clusters(eps: L.Mat, +threshold: F32) -> Maybe<&2, List<&2, CorrPair>>:
  wrap_pairs(C.idio_corr_clusters(eps, threshold))

def winsorize_log_mad(returns: L.Mat, +window: U32, +d_max: F32) -> Maybe<&2, L.Mat>:
  C.winsorize_log_mad(returns, window, d_max)

def link_models_ir(local_covs: List<&2, L.Mat>, joint_cov: L.Mat, +rho: F32) -> Maybe<&2, L.Mat>:
  C.link_models_ir(local_covs, joint_cov, rho)

def wrap_rebase(mr: Maybe<&2, C.RebaseResult>) -> Maybe<&2, RebaseResult>:
  match mr:
    case Some{C.RebaseResult{cl, cc}}:
      Some{RebaseResult{cl, cc}}
    case None{}:
      None{}

def rebase_currency(c_mat: L.Mat, cov_c: L.Mat, +target_idx: U32) -> Maybe<&2, RebaseResult>:
  wrap_rebase(C.rebase_currency(c_mat, cov_c, target_idx))

# ---------------------------------------------------------------- Ch 4: Factor Model Transformations

# §4.4.1 General rotation: B_tilde = B C^{-1}, Omega_f_tilde = C Omega_f C^T.
# Solves C^T X = B^T via lstsq_mat (thin QR) to get B_tilde = X^T without explicit inversion.
def rot_mod.s3(mc2: Maybe<&2, L.Mat>, b_tilde: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match mc2:
    case Some{L.Mat{+k, _, rows}}:
      Some{P.FactorModel{b_tilde, C.symmetrize_raw(k, rows), idio_var}}
    case None{}:
      None{}

def rot_mod.s2(mbt: Maybe<&2, L.Mat>, mc1: Maybe<&2, L.Mat>, c_t: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match mbt mc1:
    case Some{bt} Some{c_cov}:
      rot_mod.s3(L.matmul(c_cov, c_t), L.transpose(bt), idio_var)
    case _ _:
      None{}

def rot_mod.chk(ok: Bool, b: L.Mat, cov_f: L.Mat, idio_var: L.Vec, +c_mat: L.Mat) -> Maybe<&2, P.FactorModel>:
  match ok:
    case True{}:
      +c_t = L.transpose(c_mat)
      rot_mod.s2(L.lstsq_mat(c_t, L.transpose(b)), L.matmul(c_mat, cov_f), c_t, idio_var)
    case False{}:
      None{}

def rotate_model(+fm: P.FactorModel, +c_mat: L.Mat) -> Maybe<&2, P.FactorModel>:
  P.FactorModel{+b, cov_f, idio_var} = fm
  L.Mat{_, +k, _} = b
  L.Mat{+cm, +cn, _} = c_mat
  +ok = Bool.and(fm_dims_ok(fm), Bool.and(U32.is_eq(k, cm), Bool.and(U32.is_eq(cm, cn), U32.is_gt(k, 0))))
  rot_mod.chk(ok, b, cov_f, idio_var, c_mat)

# §4.4.1 Identity factor covariance view: B_tilde = B U S^{1/2}, Omega_f_tilde = I_K.
def rot_id.s2(mbt: Maybe<&2, L.Mat>, +k: U32, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match mbt:
    case Some{bt}:
      Some{P.FactorModel{bt, L.Mat.eye(k), idio_var}}
    case None{}:
      None{}

def rot_id.s1(mbu: Maybe<&2, L.Mat>, sv: L.Vec, +k: U32, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match mbu:
    case Some{bu}:
      rot_id.s2(L.mul_diag(bu, sv), k, idio_var)
    case None{}:
      None{}

def rot_id.pos(ok: Bool, b: L.Mat, vecs: L.Mat, +k: U32, vals: List<&2, F32>, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match ok:
    case True{}:
      rot_id.s1(L.matmul(b, vecs), L.Vec{k, C.list_sqrt(vals)}, k, idio_var)
    case False{}:
      None{}

def rot_id.with_eig(me: Maybe<&2, L.Eigen>, b: L.Mat, +k: U32, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match me:
    case Some{L.Eigen{L.Vec{_, +vals}, vecs}}:
      rot_id.pos(all_pos(vals), b, vecs, k, vals, idio_var)
    case None{}:
      None{}

def rot_id.chk(ok: Bool, b: L.Mat, cov_f: L.Mat, +k: U32, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match ok:
    case True{}:
      rot_id.with_eig(L.sym_eigen(cov_f), b, k, idio_var)
    case False{}:
      None{}

def rotate_identity_cov(+fm: P.FactorModel) -> Maybe<&2, P.FactorModel>:
  P.FactorModel{+b, cov_f, idio_var} = fm
  L.Mat{_, +k, _} = b
  rot_id.chk(Bool.and(fm_dims_ok(fm), U32.is_gt(k, 0)), b, cov_f, k, idio_var)

# §4.4.1 Orthonormal loadings view: B = U S V^T => B_tilde = U, Omega_f_tilde = (S V^T) Omega_f (V S).
def rot_orth.s3(mc2: Maybe<&2, L.Mat>, u: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match mc2:
    case Some{L.Mat{+k, _, rows}}:
      Some{P.FactorModel{u, C.symmetrize_raw(k, rows), idio_var}}
    case None{}:
      None{}

def rot_orth.s2(mc1: Maybe<&2, L.Mat>, svt_t: L.Mat, u: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match mc1:
    case Some{c1}:
      rot_orth.s3(L.matmul(c1, svt_t), u, idio_var)
    case None{}:
      None{}

def rot_orth.s1(msvt: Maybe<&2, L.Mat>, cov_f: L.Mat, u: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match msvt:
    case Some{+svt}:
      rot_orth.s2(L.matmul(svt, cov_f), L.transpose(svt), u, idio_var)
    case None{}:
      None{}

def rot_orth.svd(svd: L.SVD, cov_f: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  L.SVD{u, s, vt} = svd
  rot_orth.s1(L.diag_mul(s, vt), cov_f, u, idio_var)

def rot_orth.chk(ok: Bool, b: L.Mat, cov_f: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match ok:
    case True{}:
      rot_orth.svd(L.svd_thin(b), cov_f, idio_var)
    case False{}:
      None{}

def rotate_orthonormal_loadings(+fm: P.FactorModel) -> Maybe<&2, P.FactorModel>:
  P.FactorModel{+b, cov_f, idio_var} = fm
  L.Mat{+n, +k, _} = b
  rot_orth.chk(Bool.and(fm_dims_ok(fm), Bool.and(U32.is_gt(k, 0), U32.is_ge(n, k))), b, cov_f, idio_var)

# §4.4.1 Eq (4.4) Z-score loadings rotation:
# When B * a = 1, B_tilde = (B + 1 * shifts^T) diag(scales) = B C^{-1}
# where C = diag(scales^{-1}) (I_K - (a * shifts^T) / (1 + shifts^T a)).
def rot_zs.s3(mbt: Maybe<&2, L.Mat>, mc2: Maybe<&2, L.Mat>, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match mbt mc2:
    case Some{bt} Some{L.Mat{+k, _, rows}}:
      Some{P.FactorModel{bt, C.symmetrize_raw(k, rows), idio_var}}
    case _ _:
      None{}

def rot_zs.mul_cov(mtmp: Maybe<&2, L.Mat>, c_t: L.Mat, mbt: Maybe<&2, L.Mat>, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match mtmp:
    case Some{tmp}:
      rot_zs.s3(mbt, L.matmul(tmp, c_t), idio_var)
    case None{}:
      None{}

def rot_zs.with_mats(mc_inv: Maybe<&2, L.Mat>, mc: Maybe<&2, L.Mat>, b: L.Mat, cov_f: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match mc_inv mc:
    case Some{cinv} Some{+c_mat}:
      rot_zs.mul_cov(L.matmul(c_mat, cov_f), L.transpose(c_mat), L.matmul(b, cinv), idio_var)
    case _ _:
      None{}

def rot_zs.with_add(m1: Maybe<&2, L.Mat>, m2: Maybe<&2, L.Mat>, scales: L.Vec, inv_scales: L.Vec, b: L.Mat, cov_f: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match m1 m2:
    case Some{i_plus} Some{i_minus}:
      rot_zs.with_mats(L.mul_diag(i_plus, scales), L.diag_mul(inv_scales, i_minus), b, cov_f, idio_var)
    case _ _:
      None{}

def rot_zs.with_denom(ok_d: Bool, +denom: F32, +k: U32, a_vec: L.Vec, shifts: L.Vec, scales: L.Vec, inv_scales: L.Vec, b: L.Mat, cov_f: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match ok_d:
    case True{}:
      +eye = L.Mat.eye(k)
      +an = L.outer(a_vec, shifts)
      +an_scaled = L.scale((1.0 / denom : F32), an)
      rot_zs.with_add(L.madd(eye, an), L.msub(eye, an_scaled), scales, inv_scales, b, cov_f, idio_var)
    case False{}:
      None{}

def rot_zs.with_dot(md: Maybe<&2, F32>, +k: U32, a_vec: L.Vec, shifts: L.Vec, scales: L.Vec, inv_scales: L.Vec, b: L.Mat, cov_f: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match md:
    case Some{d}:
      +denom = (1.0 + d : F32)
      rot_zs.with_denom(F32.is_gt(F32.abs(denom), 1.0e-12), denom, k, a_vec, shifts, scales, inv_scales, b, cov_f, idio_var)
    case None{}:
      None{}

def rot_zs.chk(ok: Bool, +k: U32, +a_vec: L.Vec, +shifts: L.Vec, scales: L.Vec, sc_list: List<&2, F32>, b: L.Mat, cov_f: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match ok:
    case True{}:
      rot_zs.with_dot(L.dot(shifts, a_vec), k, a_vec, shifts, scales, L.Vec{k, list_inv(sc_list)}, b, cov_f, idio_var)
    case False{}:
      None{}

def rotate_zscore_loadings(+fm: P.FactorModel, +a_vec: L.Vec, +shifts: L.Vec, +scales: L.Vec) -> Maybe<&2, P.FactorModel>:
  P.FactorModel{+b, cov_f, idio_var} = fm
  L.Mat{_, +k, _} = b
  L.Vec{+na, _} = a_vec
  L.Vec{+ns, _} = shifts
  L.Vec{+nk, +sc_list} = scales
  +ok = Bool.and(fm_dims_ok(fm), Bool.and(U32.is_gt(k, 0), Bool.and(U32.is_eq(k, na), Bool.and(U32.is_eq(k, ns), Bool.and(U32.is_eq(k, nk), all_pos(sc_list))))))
  rot_zs.chk(ok, k, a_vec, shifts, scales, sc_list, b, cov_f, idio_var)

# §4.4.2 Projection onto fewer factors A (N x P):
# H = (A^T A)^{-1} A^T B (P x K), Omega_g = H Omega_f H^T,
# residual variance diag((B - A H) Omega_f (B - A H)^T) added to idio_var.
def diag_quad_rows(db_rows: List<&2, List<&2, F32>>, db_cov_rows: List<&2, List<&2, F32>>) -> List<&2, F32>:
  match db_rows db_cov_rows:
    case Con{r1, t1} Con{r2, t2}:
      fmax(0.0, L.dot_raw(r1, r2)) <> diag_quad_rows(t1, t2)
    case _ _:
      Nil{}

def add_f32_lists(xs: List<&2, F32>, ys: List<&2, F32>) -> List<&2, F32>:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      (x + y : F32) <> add_f32_lists(xt, yt)
    case _ _:
      Nil{}

def proj_mod.s4(mcovg: Maybe<&2, L.Mat>, mdbc: Maybe<&2, L.Mat>, db_rows: List<&2, List<&2, F32>>, a_mat: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match mcovg mdbc:
    case Some{L.Mat{+p, _, g_rows}} Some{L.Mat{_, _, dbc_rows}}:
      L.Vec{n, ds} = idio_var
      +extra = diag_quad_rows(db_rows, dbc_rows)
      Some{P.FactorModel{a_mat, C.symmetrize_raw(p, g_rows), L.Vec{n, add_f32_lists(ds, extra)}}}
    case _ _:
      None{}

def proj_mod.s3(mdb: Maybe<&2, L.Mat>, mhc: Maybe<&2, L.Mat>, h_t: L.Mat, cov_f: L.Mat, a_mat: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match mdb mhc:
    case Some{L.Mat{dm, dn, +db_rows}} Some{hc}:
      proj_mod.s4(L.matmul(hc, h_t), L.matmul(L.Mat{dm, dn, db_rows}, cov_f), db_rows, a_mat, idio_var)
    case _ _:
      None{}

def proj_mod.s2(mah: Maybe<&2, L.Mat>, +h: L.Mat, b: L.Mat, +cov_f: L.Mat, a_mat: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match mah:
    case Some{ah}:
      proj_mod.s3(L.msub(b, ah), L.matmul(h, cov_f), L.transpose(h), cov_f, a_mat, idio_var)
    case None{}:
      None{}

def proj_mod.s1(mh: Maybe<&2, L.Mat>, b: L.Mat, cov_f: L.Mat, +a_mat: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match mh:
    case Some{+h}:
      proj_mod.s2(L.matmul(a_mat, h), h, b, cov_f, a_mat, idio_var)
    case None{}:
      None{}

def proj_mod.chk(ok: Bool, +b: L.Mat, cov_f: L.Mat, +a_mat: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match ok:
    case True{}:
      proj_mod.s1(L.lstsq_mat(a_mat, b), b, cov_f, a_mat, idio_var)
    case False{}:
      None{}

def project_model(+fm: P.FactorModel, +a_mat: L.Mat) -> Maybe<&2, P.FactorModel>:
  P.FactorModel{+b, cov_f, idio_var} = fm
  L.Mat{+n, _, _} = b
  L.Mat{+am, +ap, _} = a_mat
  +ok = Bool.and(fm_dims_ok(fm), Bool.and(U32.is_eq(n, am), Bool.and(U32.is_gt(ap, 0), U32.is_ge(n, ap))))
  proj_mod.chk(ok, b, cov_f, a_mat, idio_var)

# §4.4.3 Eq (4.5) Push-out: orthogonalize candidate loadings A (N x P) against B (N x K)
# under Omega_eps^{-1} = diag(idio_var^{-1}), so H^T Omega_eps^{-1} B = 0.
def project_col_one(mv: Maybe<&2, L.Vec>) -> Maybe<&2, List<&2, F32>>:
  match mv:
    case Some{L.Vec{_, xs}}:
      Some{xs}
    case None{}:
      None{}

def project_cols_orth(cols: List<&2, List<&2, F32>>, +q: L.Mat, +n: U32) -> Maybe<&2, List<&2, List<&2, F32>>>:
  match cols:
    case Nil{}:
      Some{Nil{}}
    case Con{c, ct}:
      seq_maybe.cons(List<&2, F32>, project_col_one(L.project_orth(q, L.Vec{n, c})), project_cols_orth(ct, q, n))

def pushout_load.s3(mcols: Maybe<&2, List<&2, List<&2, F32>>>, +n: U32, +p: U32, sqrt_d: L.Vec) -> Maybe<&2, L.Mat>:
  match mcols:
    case Some{h_cols}:
      L.diag_mul(sqrt_d, L.transpose(L.Mat{p, n, h_cols}))
    case None{}:
      None{}

def pushout_load.cols(wat: L.Mat, q: L.Mat, +n: U32, +p: U32, sqrt_d: L.Vec) -> Maybe<&2, L.Mat>:
  L.Mat{_, _, wa_cols} = wat
  pushout_load.s3(project_cols_orth(wa_cols, q, n), n, p, sqrt_d)

def pushout_load.s2(mqr: Maybe<&2, L.QR>, mwa: Maybe<&2, L.Mat>, +n: U32, +p: U32, sqrt_d: L.Vec) -> Maybe<&2, L.Mat>:
  match mqr mwa:
    case Some{L.QR{q, _}} Some{wa}:
      pushout_load.cols(L.transpose(wa), q, n, p, sqrt_d)
    case _ _:
      None{}

def pushout_load.s1(mwb: Maybe<&2, L.Mat>, mwa: Maybe<&2, L.Mat>, +n: U32, +p: U32, sqrt_d: L.Vec) -> Maybe<&2, L.Mat>:
  match mwb:
    case Some{wb}:
      pushout_load.s2(L.qr_thin(wb), mwa, n, p, sqrt_d)
    case None{}:
      None{}

def pushout_load.run(+inv_sd: L.Vec, sd: L.Vec, b: L.Mat, a_mat: L.Mat, +n: U32, +p: U32) -> Maybe<&2, L.Mat>:
  pushout_load.s1(L.diag_mul(inv_sd, b), L.diag_mul(inv_sd, a_mat), n, p, sd)

def pushout_load.chk2(ok: Bool, +n: U32, +p: U32, b: L.Mat, a_mat: L.Mat, +ds: List<&2, F32>) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      pushout_load.run(L.Vec{n, C.list_inv_sqrt(ds)}, L.Vec{n, C.list_sqrt(ds)}, b, a_mat, n, p)
    case False{}:
      None{}

def pushout_loadings(+b: L.Mat, +a_mat: L.Mat, idio_var: L.Vec) -> Maybe<&2, L.Mat>:
  L.Mat{+bm, +bk, _} = b
  L.Mat{+am, +ap, _} = a_mat
  L.Vec{+dn, +ds} = idio_var
  +ok = Bool.and(U32.is_eq(bm, am), Bool.and(U32.is_eq(bm, dn), Bool.and(U32.is_gt(bk, 0), Bool.and(U32.is_gt(ap, 0), Bool.and(U32.is_ge(bm, bk), all_pos(ds))))))
  pushout_load.chk2(ok, bm, ap, b, a_mat, ds)

# Horizontal concatenation [B | H] and block-diagonal diag(cov_f, cov_g).
def hcat_rows(rs1: List<&2, List<&2, F32>>, rs2: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match rs1 rs2:
    case Con{r1, t1} Con{r2, t2}:
      List.append(&2, F32, r1, r2) <> hcat_rows(t1, t2)
    case _ _:
      Nil{}

def block_diag_top(rows: List<&2, List<&2, F32>>, +p: Nat) -> List<&2, List<&2, F32>>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      List.append(&2, F32, r, List.replicate(F32, p, 0.0)) <> block_diag_top(t, p)

def block_diag_bot(rows: List<&2, List<&2, F32>>, +k: Nat) -> List<&2, List<&2, F32>>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      List.append(&2, F32, List.replicate(F32, k, 0.0), r) <> block_diag_bot(t, k)

def pushout_mod.build(n: U32, +k: U32, +p: U32, b_rows: List<&2, List<&2, F32>>, h_rows: List<&2, List<&2, F32>>, cf_rows: List<&2, List<&2, F32>>, cg_rows: List<&2, List<&2, F32>>, new_idio: L.Vec) -> P.FactorModel:
  +kp = (k + p : U32)
  P.FactorModel{
    L.Mat{n, kp, hcat_rows(b_rows, h_rows)},
    C.symmetrize_raw(kp, List.append(&2, List<&2, F32>, block_diag_top(cf_rows, U32.to_nat(p)), block_diag_bot(cg_rows, U32.to_nat(k)))),
    new_idio
  }

def pushout_mod.fin2(mh: Maybe<&2, L.Mat>, b: L.Mat, cov_f: L.Mat, cov_g: L.Mat, new_idio: L.Vec) -> Maybe<&2, P.FactorModel>:
  match mh:
    case Some{L.Mat{_, p, h_rows}}:
      L.Mat{n, k, b_rows} = b
      L.Mat{_, _, cf_rows} = cov_f
      L.Mat{_, _, cg_rows} = cov_g
      Some{pushout_mod.build(n, k, p, b_rows, h_rows, cf_rows, cg_rows, new_idio)}
    case None{}:
      None{}

def pushout_mod.chk(ok: Bool, +b: L.Mat, cov_f: L.Mat, idio_var: L.Vec, a_mat: L.Mat, cov_g: L.Mat, new_idio: L.Vec) -> Maybe<&2, P.FactorModel>:
  match ok:
    case True{}:
      pushout_mod.fin2(pushout_loadings(b, a_mat, idio_var), b, cov_f, cov_g, new_idio)
    case False{}:
      None{}

def pushout_model(+fm: P.FactorModel, +a_mat: L.Mat, +cov_g: L.Mat, +new_idio: L.Vec) -> Maybe<&2, P.FactorModel>:
  P.FactorModel{+b, cov_f, idio_var} = fm
  L.Mat{+n, _, _} = b
  L.Mat{+am, +ap, _} = a_mat
  L.Mat{+gm, +gn, _} = cov_g
  L.Vec{+dn, +nds} = new_idio
  +ok = Bool.and(fm_dims_ok(fm), Bool.and(U32.is_eq(n, am), Bool.and(U32.is_eq(n, dn), Bool.and(U32.is_eq(ap, gm), Bool.and(U32.is_eq(gm, gn), all_pos(nds))))))
  pushout_mod.chk(ok, b, cov_f, idio_var, a_mat, cov_g, new_idio)

# §4.5.2 Partitioned group risk decomposition.
def in_group(+idx: U32, grp: List<&2, U32>) -> Bool:
  match grp:
    case Nil{}:
      False{}
    case Con{g, gt}:
      Bool.or(U32.is_eq(idx, g), in_group(idx, gt))

def group_indices_ok(grp: List<&2, U32>, +k: U32) -> Bool:
  match grp:
    case Nil{}:
      True{}
    case Con{g, gt}:
      Bool.and(U32.is_lt(g, k), group_indices_ok(gt, k))

def all_groups_ok(groups: List<&2, List<&2, U32>>, +k: U32) -> Bool:
  match groups:
    case Nil{}:
      True{}
    case Con{grp, rest}:
      Bool.and(group_indices_ok(grp, k), all_groups_ok(rest, k))

def mask_exposure(xs: List<&2, F32>, +j: U32, +grp: List<&2, U32>) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{v, vt}:
      Bool.pick(F32, in_group(j, grp), v, 0.0) <> mask_exposure(vt, (j + 1 : U32), grp)

def build_group_rows(groups: List<&2, List<&2, U32>>, +b_exp: List<&2, F32>) -> List<&2, List<&2, F32>>:
  match groups:
    case Nil{}:
      Nil{}
    case Con{grp, rest}:
      mask_exposure(b_exp, 0, grp) <> build_group_rows(rest, b_exp)

def row_sums_list(rows: List<&2, List<&2, F32>>) -> List<&2, F32>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, rt}:
      C.list_sum(r) <> row_sums_list(rt)

def div_scalar_safe(xs: List<&2, F32>, +den: F32) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Bool.pick(F32, F32.is_gt(den, 1.0e-30), (h / den : F32), 0.0) <> div_scalar_safe(t, den)

def group_mcr_list(rsums: List<&2, F32>, gvars: List<&2, F32>, +tvol: F32) -> List<&2, F32>:
  match rsums gvars:
    case Con{rs, rt} Con{gv, gt}:
      +gvol = F32.sqrt(fmax(gv, 0.0))
      +den = (tvol * gvol : F32)
      Bool.pick(F32, F32.is_gt(den, 1.0e-30), (rs / den : F32), 0.0) <> group_mcr_list(rt, gt, tvol)
    case _ _:
      Nil{}

def group_risk.build1(gcov: L.Mat, dv: L.Vec, +g: U32) -> GroupRisk:
  L.Mat{+gm, +gn, +grows} = gcov
  L.Vec{_, +gvars} = dv
  +rsums = row_sums_list(grows)
  +tvar = fmax(C.list_sum(rsums), 0.0)
  +tvol = F32.sqrt(tvar)
  GroupRisk{
    L.Mat{gm, gn, grows},
    L.Vec{g, gvars},
    L.Vec{g, div_scalar_safe(rsums, tvar)},
    L.Vec{g, group_mcr_list(rsums, gvars, tvol)},
    tvar,
    tvol
  }

def group_risk.build(+gcov: L.Mat, +g: U32) -> GroupRisk:
  group_risk.build1(gcov, L.Mat.diag_vec(gcov), g)

def group_risk.s2(mgc: Maybe<&2, L.Mat>, +g: U32) -> Maybe<&2, GroupRisk>:
  match mgc:
    case Some{L.Mat{_, _, rows}}:
      Some{group_risk.build(C.symmetrize_raw(g, rows), g)}
    case None{}:
      None{}

def group_risk.s1(mtmp: Maybe<&2, L.Mat>, m_t: L.Mat, +g: U32) -> Maybe<&2, GroupRisk>:
  match mtmp:
    case Some{tmp}:
      group_risk.s2(L.matmul(tmp, m_t), g)
    case None{}:
      None{}

def group_risk.with_mat(+m_mat: L.Mat, cov_f: L.Mat, +g: U32) -> Maybe<&2, GroupRisk>:
  group_risk.s1(L.matmul(m_mat, cov_f), L.transpose(m_mat), g)

def group_risk.with_exp(mexp: Maybe<&2, L.Vec>, cov_f: L.Mat, groups: List<&2, List<&2, U32>>, +g: U32, +k: U32) -> Maybe<&2, GroupRisk>:
  match mexp:
    case Some{L.Vec{_, b_exp}}:
      group_risk.with_mat(L.Mat{g, k, build_group_rows(groups, b_exp)}, cov_f, g)
    case None{}:
      None{}

def group_risk.chk(ok: Bool, fm: P.FactorModel, w: L.Vec, cov_f: L.Mat, groups: List<&2, List<&2, U32>>, +g: U32, +k: U32) -> Maybe<&2, GroupRisk>:
  match ok:
    case True{}:
      group_risk.with_exp(P.exposures(fm, w), cov_f, groups, g, k)
    case False{}:
      None{}

def group_risk_decomp(+fm: P.FactorModel, +w: L.Vec, +groups: List<&2, List<&2, U32>>) -> Maybe<&2, GroupRisk>:
  P.FactorModel{b, cov_f, _} = fm
  L.Mat{+n, +k, _} = b
  L.Vec{+wn, _} = w
  +g = U32.from_nat(List.length(&2, List<&2, U32>, groups))
  +ok = Bool.and(fm_dims_ok(fm), Bool.and(U32.is_eq(n, wn), Bool.and(U32.is_gt(g, 0), all_groups_ok(groups, k))))
  group_risk.chk(ok, fm, w, cov_f, groups, g, k)

# ---------------------------------------------------------------- Ch 5: Evaluating Risk (Out-of-Sample)

# §5.1.1 Univariate robust volatility loss functions (Patton 2011) & Bias stat.
def qlike.go(vs: List<&2, F32>, rs: List<&2, F32>, +acc: F32) -> F32:
  match vs rs:
    case Con{+v, vt} Con{+r, rt}:
      +r2 = fmax((r * r : F32), 1.0e-20)
      +rat = (r2 / v : F32)
      qlike.go(vt, rt, (acc + ((rat - F32.log(rat)) - 1.0) : F32))
    case _ _:
      acc

def qlike.chk(ok: Bool, +n: U32, vs: List<&2, F32>, rs: List<&2, F32>) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      Some{(qlike.go(vs, rs, 0.0) / U32.to_f32(n) : F32)}
    case False{}:
      None{}

def qlike(var_hat: L.Vec, r: L.Vec) -> Maybe<&2, F32>:
  L.Vec{+nv, +vs} = var_hat
  L.Vec{+nr, rs} = r
  +ok = Bool.and(U32.is_eq(nv, nr), Bool.and(U32.is_gt(nv, 0), all_pos(vs)))
  qlike.chk(ok, nv, vs, rs)

def vol_mse.go(vs: List<&2, F32>, rs: List<&2, F32>, +acc: F32) -> F32:
  match vs rs:
    case Con{v, vt} Con{+r, rt}:
      +d = ((r * r) - v : F32)
      vol_mse.go(vt, rt, (acc + (d * d) : F32))
    case _ _:
      acc

def vol_mse.chk(ok: Bool, +n: U32, vs: List<&2, F32>, rs: List<&2, F32>) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      Some{(vol_mse.go(vs, rs, 0.0) / U32.to_f32(n) : F32)}
    case False{}:
      None{}

def vol_mse(var_hat: L.Vec, r: L.Vec) -> Maybe<&2, F32>:
  L.Vec{+nv, +vs} = var_hat
  L.Vec{+nr, rs} = r
  +ok = Bool.and(U32.is_eq(nv, nr), Bool.and(U32.is_gt(nv, 0), all_pos(vs)))
  vol_mse.chk(ok, nv, vs, rs)

def bias_stat.go(vs: List<&2, F32>, rs: List<&2, F32>, +acc: F32) -> F32:
  match vs rs:
    case Con{v, vt} Con{+r, rt}:
      bias_stat.go(vt, rt, (acc + ((r * r) / v) : F32))
    case _ _:
      acc

def bias_stat.chk(ok: Bool, +n: U32, vs: List<&2, F32>, rs: List<&2, F32>) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      Some{F32.sqrt((bias_stat.go(vs, rs, 0.0) / U32.to_f32(n) : F32))}
    case False{}:
      None{}

def bias_stat(var_hat: L.Vec, r: L.Vec) -> Maybe<&2, F32>:
  L.Vec{+nv, +vs} = var_hat
  L.Vec{+nr, rs} = r
  +ok = Bool.and(U32.is_eq(nv, nr), Bool.and(U32.is_gt(nv, 0), all_pos(vs)))
  bias_stat.chk(ok, nv, vs, rs)

# Pair fms[t] strictly with returns[t + 1] (no-lookahead invariant proved in PROOF.bend!).
type FmRetPair is Data:
  FmRetPair{fm: P.FactorModel, ret: List<&2, F32>}

def pair_oos_fm(fms: List<&2, P.FactorModel>, next_rows: List<&2, List<&2, F32>>) -> List<&2, FmRetPair>:
  match fms next_rows:
    case Con{fm, ft} Con{r, rt}:
      FmRetPair{fm, r} <> pair_oos_fm(ft, rt)
    case _ _:
      Nil{}

# §5.1.2 Eq (5.1) QDIST via Woodbury solve & Matrix Determinant Lemma (zero N x N matrices).
def qdist_one.s2(mquad: Maybe<&2, F32>, mld: Maybe<&2, F32>, +n: U32) -> Maybe<&2, F32>:
  match mquad mld:
    case Some{q} Some{ld}:
      Some{((q + ld) + (U32.to_f32(n) * 1.837877) : F32)}
    case _ _:
      None{}

def qdist_one.s1(msol: Maybe<&2, L.Vec>, mld: Maybe<&2, F32>, r_vec: L.Vec, +n: U32) -> Maybe<&2, F32>:
  match msol:
    case Some{inv_r}:
      qdist_one.s2(L.dot(r_vec, inv_r), mld, n)
    case None{}:
      None{}

def qdist_one.go(+n: U32, +b: L.Mat, +cov_f: L.Mat, +idio_var: L.Vec, +r_vec: L.Vec) -> Maybe<&2, F32>:
  qdist_one.s1(L.woodbury_solve(idio_var, b, cov_f, r_vec), L.woodbury_logdet(idio_var, b, cov_f), r_vec, n)

def qdist_period.go(+n: U32, pr: FmRetPair) -> Maybe<&2, F32>:
  FmRetPair{P.FactorModel{b, cov_f, idio_var}, r_list} = pr
  qdist_one.go(n, b, cov_f, idio_var, L.Vec{n, r_list})

def qdist_period(n: U32, pr: FmRetPair) -> Maybe<&2, F32>:
  qdist_period.go(n, pr)

def qdist.fin(mvals: Maybe<&2, List<&2, F32>>, +cnt: U32) -> Maybe<&2, QDistResult>:
  match mvals:
    case Some{+vs}:
      +tot = C.list_sum(vs)
      Some{QDistResult{(tot / U32.to_f32(cnt) : F32), tot, L.Vec{cnt, vs}}}
    case None{}:
      None{}

def qdist.run(fms: List<&2, P.FactorModel>, rows: List<&2, List<&2, F32>>, +cnt: U32, +n: U32) -> Maybe<&2, QDistResult>:
  match rows:
    case Nil{}:
      None{}
    case Con{_, next_rows}:
      +pairs = pair_oos_fm(fms, next_rows)
      qdist.fin(seq_maybe(F32, pmap(~FmRetPair, ~Maybe<&2, F32>, ~U32, ~qdist_period, pairs, cnt, n)), cnt)

def qdist.chk(ok: Bool, fms: List<&2, P.FactorModel>, rows: List<&2, List<&2, F32>>, +t: U32, +n: U32) -> Maybe<&2, QDistResult>:
  match ok:
    case True{}:
      qdist.run(fms, rows, (t - 1 : U32), n)
    case False{}:
      None{}

# Pairs fms[t] with returns[t + 1] for t = 0..T-2 (parallelized via pmap).
def qdist(+fms: List<&2, P.FactorModel>, returns: L.Mat) -> Maybe<&2, QDistResult>:
  L.Mat{+t, +n, rows} = returns
  +nf = U32.from_nat(List.length(&2, P.FactorModel, fms))
  +ok = Bool.and(U32.is_eq(nf, t), Bool.and(U32.is_gt(t, 1), U32.is_gt(n, 0)))
  qdist.chk(ok, fms, rows, t, n)

# §5.2.2 Mahalanobis distance & MALV (zero N x N matrices, parallelized via pmap).
def mahal_one.div(md: Maybe<&2, F32>, +n: U32) -> Maybe<&2, F32>:
  match md:
    case Some{q}:
      Some{(q / U32.to_f32(n) : F32)}
    case None{}:
      None{}

def mahal_one.s1b(msol: Maybe<&2, L.Vec>, r_vec: L.Vec, +n: U32) -> Maybe<&2, F32>:
  match msol:
    case Some{inv_r}:
      mahal_one.div(L.dot(r_vec, inv_r), n)
    case None{}:
      None{}

def mahal_one.go(+n: U32, b: L.Mat, cov_f: L.Mat, idio_var: L.Vec, +r_vec: L.Vec) -> Maybe<&2, F32>:
  mahal_one.s1b(L.woodbury_solve(idio_var, b, cov_f, r_vec), r_vec, n)

def mahal_period.go(+n: U32, pr: FmRetPair) -> Maybe<&2, F32>:
  FmRetPair{P.FactorModel{b, cov_f, idio_var}, r_list} = pr
  mahal_one.go(n, b, cov_f, idio_var, L.Vec{n, r_list})

def mahal_period(n: U32, pr: FmRetPair) -> Maybe<&2, F32>:
  mahal_period.go(n, pr)

def sum_sq_dev(xs: List<&2, F32>, +mu: F32, +acc: F32) -> F32:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      +d = (x - mu : F32)
      sum_sq_dev(t, mu, (acc + (d * d) : F32))

def mahal.fin(mvals: Maybe<&2, List<&2, F32>>, +cnt: U32) -> Maybe<&2, MahalanobisResult>:
  match mvals:
    case Some{+vs}:
      +cf = U32.to_f32(cnt)
      +mu = (C.list_sum(vs) / cf : F32)
      +malv = (sum_sq_dev(vs, mu, 0.0) / cf : F32)
      Some{MahalanobisResult{L.Vec{cnt, vs}, mu, malv}}
    case None{}:
      None{}

def mahal.run(fms: List<&2, P.FactorModel>, rows: List<&2, List<&2, F32>>, +cnt: U32, +n: U32) -> Maybe<&2, MahalanobisResult>:
  match rows:
    case Nil{}:
      None{}
    case Con{_, next_rows}:
      +pairs = pair_oos_fm(fms, next_rows)
      mahal.fin(seq_maybe(F32, pmap(~FmRetPair, ~Maybe<&2, F32>, ~U32, ~mahal_period, pairs, cnt, n)), cnt)

def mahal.chk(ok: Bool, fms: List<&2, P.FactorModel>, rows: List<&2, List<&2, F32>>, +t: U32, +n: U32) -> Maybe<&2, MahalanobisResult>:
  match ok:
    case True{}:
      mahal.run(fms, rows, (t - 1 : U32), n)
    case False{}:
      None{}

def mahalanobis_test(+fms: List<&2, P.FactorModel>, returns: L.Mat) -> Maybe<&2, MahalanobisResult>:
  L.Mat{+t, +n, rows} = returns
  +nf = U32.from_nat(List.length(&2, P.FactorModel, fms))
  +ok = Bool.and(U32.is_eq(nf, t), Bool.and(U32.is_gt(t, 1), U32.is_gt(n, 0)))
  mahal.chk(ok, fms, rows, t, n)

# §5.2.1 Eq (5.2) Minimum-variance portfolio out-of-sample test:
# w_t = (Omega_{r,t}^{-1} b) / (b^T Omega_{r,t}^{-1} b), evaluated on r_{t+1}.
type MvpStep is Data:
  MvpStep{ret: F32, pred_var: F32}

def mvp_one.s2_chk(ok: Bool, +bt_inv_b: F32, +rt_inv_b: F32) -> Maybe<&2, MvpStep>:
  match ok:
    case True{}:
      Some{MvpStep{(rt_inv_b / bt_inv_b : F32), (1.0 / bt_inv_b : F32)}}
    case False{}:
      None{}

def mvp_one.s2b(md_b: Maybe<&2, F32>, md_r: Maybe<&2, F32>) -> Maybe<&2, MvpStep>:
  match md_b md_r:
    case Some{+bt_inv_b} Some{rt_inv_b}:
      mvp_one.s2_chk(F32.is_gt(bt_inv_b, 1.0e-30), bt_inv_b, rt_inv_b)
    case _ _:
      None{}

def mvp_one.s1(msol: Maybe<&2, L.Vec>, b_vec: L.Vec, r_vec: L.Vec) -> Maybe<&2, MvpStep>:
  match msol:
    case Some{+inv_b}:
      mvp_one.s2b(L.dot(b_vec, inv_b), L.dot(r_vec, inv_b))
    case None{}:
      None{}

def mvp_period.go(+b_vec: L.Vec, pr: FmRetPair) -> Maybe<&2, MvpStep>:
  L.Vec{+n, _} = b_vec
  FmRetPair{P.FactorModel{b, cov_f, idio_var}, r_list} = pr
  mvp_one.s1(L.woodbury_solve(idio_var, b, cov_f, b_vec), b_vec, L.Vec{n, r_list})

def mvp_period(b_vec: L.Vec, pr: FmRetPair) -> Maybe<&2, MvpStep>:
  mvp_period.go(b_vec, pr)

def unzip_mvp.cons(r: F32, pv: F32, p: List<&2, F32> & List<&2, F32>) -> List<&2, F32> & List<&2, F32>:
  (rs, pvs) = p
  (r <> rs, pv <> pvs)

def unzip_mvp(xs: List<&2, MvpStep>) -> List<&2, F32> & List<&2, F32>:
  match xs:
    case Nil{}:
      (Nil{}, Nil{})
    case Con{MvpStep{r, pv}, t}:
      unzip_mvp.cons(r, pv, unzip_mvp(t))

def mvp.build(p: List<&2, F32> & List<&2, F32>, +cnt: U32) -> MvpResult:
  (+rs, +pvs) = p
  +cf = U32.to_f32(cnt)
  +rvar = (C.list_sum_sq.go(rs, 0.0) / cf : F32)
  +rvol = F32.sqrt(rvar)
  +mpvol = (C.list_sum(C.list_sqrt(pvs)) / cf : F32)
  +ql = (qlike.go(pvs, rs, 0.0) / cf : F32)
  +mse = (vol_mse.go(pvs, rs, 0.0) / cf : F32)
  +bs = F32.sqrt((bias_stat.go(pvs, rs, 0.0) / cf : F32))
  MvpResult{rvar, rvol, mpvol, ql, mse, bs, L.Vec{cnt, rs}, L.Vec{cnt, pvs}}

def mvp.fin(msteps: Maybe<&2, List<&2, MvpStep>>, +cnt: U32) -> Maybe<&2, MvpResult>:
  match msteps:
    case Some{steps}:
      Some{mvp.build(unzip_mvp(steps), cnt)}
    case None{}:
      None{}

def mvp.run(fms: List<&2, P.FactorModel>, rows: List<&2, List<&2, F32>>, b_vec: L.Vec, +cnt: U32) -> Maybe<&2, MvpResult>:
  match rows:
    case Nil{}:
      None{}
    case Con{_, next_rows}:
      +pairs = pair_oos_fm(fms, next_rows)
      mvp.fin(seq_maybe(MvpStep, pmap(~FmRetPair, ~Maybe<&2, MvpStep>, ~L.Vec, ~mvp_period, pairs, cnt, b_vec)), cnt)

def mvp.chk(ok: Bool, fms: List<&2, P.FactorModel>, rows: List<&2, List<&2, F32>>, b_vec: L.Vec, +t: U32) -> Maybe<&2, MvpResult>:
  match ok:
    case True{}:
      mvp.run(fms, rows, b_vec, (t - 1 : U32))
    case False{}:
      None{}

def mvp_test(+fms: List<&2, P.FactorModel>, returns: L.Mat, +b_vec: L.Vec) -> Maybe<&2, MvpResult>:
  L.Mat{+t, +n, rows} = returns
  L.Vec{+nb, _} = b_vec
  +nf = U32.from_nat(List.length(&2, P.FactorModel, fms))
  +ok = Bool.and(U32.is_eq(nf, t), Bool.and(U32.is_eq(n, nb), Bool.and(U32.is_gt(t, 1), U32.is_gt(n, 0))))
  mvp.chk(ok, fms, rows, b_vec, t)

# §5.1.2 Portfolio volatility evaluation (pairs (fms[t], weights[t]) with returns[t + 1]).
type FmWRet is Data:
  FmWRet{fm: P.FactorModel, w: List<&2, F32>, ret: List<&2, F32>}

def pair_oos_fmw(fms: List<&2, P.FactorModel>, ws: List<&2, List<&2, F32>>, next_rows: List<&2, List<&2, F32>>) -> List<&2, FmWRet>:
  match fms ws next_rows:
    case Con{fm, ft} Con{w, wt} Con{r, rt}:
      FmWRet{fm, w, r} <> pair_oos_fmw(ft, wt, rt)
    case _ _ _:
      Nil{}

def pvol_one.chk(ok: Bool, +pvar: F32, +pret: F32) -> Maybe<&2, MvpStep>:
  match ok:
    case True{}:
      Some{MvpStep{pret, pvar}}
    case False{}:
      None{}

def pvol_one.rd(mrd: Maybe<&2, P.RiskDecomp>, +pret: F32) -> Maybe<&2, MvpStep>:
  match mrd:
    case Some{P.RiskDecomp{+tvar, _, _, _, _, _, _, _}}:
      pvol_one.chk(F32.is_gt(tvar, 0.0), tvar, pret)
    case None{}:
      None{}

def pvol_period(n: U32, item: FmWRet) -> Maybe<&2, MvpStep>:
  FmWRet{fm, +w, r} = item
  pvol_one.rd(P.risk_decomp(fm, L.Vec{n, w}), L.dot_raw(w, r))

def pvol.build(p: List<&2, F32> & List<&2, F32>, +cnt: U32) -> VolEval:
  (+rs, +pvs) = p
  +cf = U32.to_f32(cnt)
  +rvol = F32.sqrt((C.list_sum_sq.go(rs, 0.0) / cf : F32))
  +mpvol = (C.list_sum(C.list_sqrt(pvs)) / cf : F32)
  +ql = (qlike.go(pvs, rs, 0.0) / cf : F32)
  +mse = (vol_mse.go(pvs, rs, 0.0) / cf : F32)
  +bs = F32.sqrt((bias_stat.go(pvs, rs, 0.0) / cf : F32))
  VolEval{ql, mse, bs, rvol, mpvol, cnt}

def pvol.fin(msteps: Maybe<&2, List<&2, MvpStep>>, +cnt: U32) -> Maybe<&2, VolEval>:
  match msteps:
    case Some{steps}:
      Some{pvol.build(unzip_mvp(steps), cnt)}
    case None{}:
      None{}

def pvol.run(fms: List<&2, P.FactorModel>, wrows: List<&2, List<&2, F32>>, rrows: List<&2, List<&2, F32>>, +cnt: U32, +n: U32) -> Maybe<&2, VolEval>:
  match rrows:
    case Nil{}:
      None{}
    case Con{_, next_rows}:
      +items = pair_oos_fmw(fms, wrows, next_rows)
      pvol.fin(seq_maybe(MvpStep, pmap(~FmWRet, ~Maybe<&2, MvpStep>, ~U32, ~pvol_period, items, cnt, n)), cnt)

def pvol.chk(ok: Bool, fms: List<&2, P.FactorModel>, wrows: List<&2, List<&2, F32>>, rrows: List<&2, List<&2, F32>>, +t: U32, +n: U32) -> Maybe<&2, VolEval>:
  match ok:
    case True{}:
      pvol.run(fms, wrows, rrows, (t - 1 : U32), n)
    case False{}:
      None{}

def portfolio_vol_eval(+fms: List<&2, P.FactorModel>, weights: L.Mat, returns: L.Mat) -> Maybe<&2, VolEval>:
  L.Mat{+tw, +nw, wrows} = weights
  L.Mat{+tr, +nr, rrows} = returns
  +nf = U32.from_nat(List.length(&2, P.FactorModel, fms))
  +ok = Bool.and(U32.is_eq(nf, tw), Bool.and(U32.is_eq(tw, tr), Bool.and(U32.is_eq(nw, nr), Bool.and(U32.is_gt(tr, 1), U32.is_gt(nr, 0)))))
  pvol.chk(ok, fms, wrows, rrows, tr, nr)

# §5.3.1 Model FMP turnover: mean_{t=1..T-1} ||P_t - P_{t-1}||_F (FMPs computed via pmap).
def fmp_one(u: Unit, fm: P.FactorModel) -> Maybe<&2, L.Mat>:
  Unit{} = u
  P.fmp(fm)

def diff_frob(md: Maybe<&2, L.Mat>) -> Maybe<&2, F32>:
  match md:
    case Some{d}:
      Some{L.frobenius(d)}
    case None{}:
      None{}

def fmp_diffs(ps: List<&2, L.Mat>) -> Maybe<&2, List<&2, F32>>:
  match ps:
    case Nil{}:
      Some{Nil{}}
    case Con{_, Nil{}}:
      Some{Nil{}}
    case Con{p0, Con{+p1, rest}}:
      seq_maybe.cons(F32, diff_frob(L.msub(p1, p0)), fmp_diffs(p1 <> rest))

def fmp_to.fin2(mds: Maybe<&2, List<&2, F32>>, +cnt: U32) -> Maybe<&2, TurnoverResult>:
  match mds:
    case Some{+ds}:
      Some{TurnoverResult{(C.list_sum(ds) / U32.to_f32(cnt) : F32), L.Vec{cnt, ds}}}
    case None{}:
      None{}

def fmp_to.fin1(mps: Maybe<&2, List<&2, L.Mat>>, +cnt: U32) -> Maybe<&2, TurnoverResult>:
  match mps:
    case Some{ps}:
      fmp_to.fin2(fmp_diffs(ps), cnt)
    case None{}:
      None{}

def fmp_to.chk(ok: Bool, fms: List<&2, P.FactorModel>, +t: U32) -> Maybe<&2, TurnoverResult>:
  match ok:
    case True{}:
      fmp_to.fin1(seq_maybe(L.Mat, pmap(~P.FactorModel, ~Maybe<&2, L.Mat>, ~Unit, ~fmp_one, fms, t, Unit{})), (t - 1 : U32))
    case False{}:
      None{}

def fmp_turnover(+fms: List<&2, P.FactorModel>) -> Maybe<&2, TurnoverResult>:
  +t = U32.from_nat(List.length(&2, P.FactorModel, fms))
  fmp_to.chk(U32.is_gt(t, 1), fms, t)

# §5.3.2 Predicted vs EWMA realized asset beta error (BETAERR, O(TN) with zero N x N matrices).
def model_beta.chk(ok: Bool, ow: List<&2, F32>, +den: F32) -> Maybe<&2, List<&2, F32>>:
  match ok:
    case True{}:
      Some{C.list_scale(ow, (1.0 / den : F32))}
    case False{}:
      None{}

def model_beta.s1(mow: Maybe<&2, L.Vec>, w_ref: L.Vec) -> Maybe<&2, List<&2, F32>>:
  match mow:
    case Some{L.Vec{_, +ow}}:
      L.Vec{_, ws} = w_ref
      +den = L.dot_raw(ws, ow)
      model_beta.chk(F32.is_gt(den, 1.0e-30), ow, den)
    case None{}:
      None{}

def model_beta_one.go(+w_ref: L.Vec, fm: P.FactorModel) -> Maybe<&2, List<&2, F32>>:
  model_beta.s1(P.cov_matvec(fm, w_ref), w_ref)

def model_beta_one(w_ref: L.Vec, fm: P.FactorModel) -> Maybe<&2, List<&2, F32>>:
  model_beta_one.go(w_ref, fm)

def sq_diff_list(xs: List<&2, F32>, ys: List<&2, F32>, +acc: F32) -> F32:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      +d = (x - y : F32)
      sq_diff_list(xt, yt, (acc + (d * d) : F32))
    case _ _:
      acc

def beta_err.scan(
  mbetas: List<&2, List<&2, F32>>,
  rrows: List<&2, List<&2, F32>>,
  +ws: List<&2, F32>,
  +lam: F32,
  cov_rw: List<&2, F32>,
  +var_w: F32
) -> List<&2, F32>:
  match mbetas rrows:
    case Con{mb, mbt} Con{+r, rt}:
      +rw = L.dot_raw(r, ws)
      +cov1 = C.list_axpy(rw, r, C.list_scale(cov_rw, lam))
      +var1 = ((lam * var_w) + (rw * rw) : F32)
      +eb = C.list_scale(cov1, Bool.pick(F32, F32.is_gt(var1, 1.0e-30), (1.0 / var1 : F32), 0.0))
      sq_diff_list(mb, eb, 0.0) <> beta_err.scan(mbt, rt, ws, lam, cov1, var1)
    case _ _:
      Nil{}

def beta_err.fin(mbs: Maybe<&2, List<&2, List<&2, F32>>>, rrows: List<&2, List<&2, F32>>, ws: List<&2, F32>, +t: U32, +n: U32, +half_life: F32) -> Maybe<&2, BetaErrResult>:
  match mbs:
    case Some{bs}:
      +lam = F32.exp((F32.neg(0.69314718) / half_life : F32))
      +z0 = List.replicate(F32, U32.to_nat(n), 0.0)
      +errs = beta_err.scan(bs, rrows, ws, lam, z0, 0.0)
      +tot = C.list_sum(errs)
      Some{BetaErrResult{tot, (tot / U32.to_f32(t) : F32), L.Vec{t, errs}}}
    case None{}:
      None{}

def beta_err.chk(ok: Bool, fms: List<&2, P.FactorModel>, rrows: List<&2, List<&2, F32>>, +w_ref: L.Vec, ws: List<&2, F32>, +t: U32, +n: U32, +half_life: F32) -> Maybe<&2, BetaErrResult>:
  match ok:
    case True{}:
      beta_err.fin(seq_maybe(List<&2, F32>, pmap(~P.FactorModel, ~Maybe<&2, List<&2, F32>>, ~L.Vec, ~model_beta_one, fms, t, w_ref)), rrows, ws, t, n, half_life)
    case False{}:
      None{}

def beta_error(+fms: List<&2, P.FactorModel>, returns: L.Mat, +w_ref: L.Vec, +half_life: F32) -> Maybe<&2, BetaErrResult>:
  L.Mat{+t, +n, rrows} = returns
  L.Vec{+nw, ws} = w_ref
  +nf = U32.from_nat(List.length(&2, P.FactorModel, fms))
  +ok = Bool.and(U32.is_eq(nf, t), Bool.and(U32.is_eq(n, nw), Bool.and(U32.is_gt(t, 0), Bool.and(U32.is_gt(n, 0), F32.is_gt(half_life, 0.0)))))
  beta_err.chk(ok, fms, rrows, w_ref, ws, t, n, half_life)

# §5.3.3 Weighted cross-sectional R^2 (diagnostic; see Paleologo Ch 5.3.3 caveat).
type R2Item is Data:
  R2Item{b: L.Mat, r: List<&2, F32>, iv: L.Vec}

def pair_r2(bs: List<&2, L.Mat>, rrows: List<&2, List<&2, F32>>, ivs: List<&2, L.Vec>) -> List<&2, R2Item>:
  match bs rrows ivs:
    case Con{b, bt} Con{r, rt} Con{iv, it}:
      R2Item{b, r, iv} <> pair_r2(bt, rt, it)
    case _ _ _:
      Nil{}

def w_ss(xs: List<&2, F32>, ws: List<&2, F32>, +acc: F32) -> F32:
  match xs ws:
    case Con{+x, xt} Con{w, wt}:
      w_ss(xt, wt, (acc + ((x * x) * w) : F32))
    case _ _:
      acc

type R2Pair is Data:
  R2Pair{num: F32, den: F32}

def r2_one.s2(mbf: Maybe<&2, L.Vec>, +r_list: List<&2, F32>, +inv_d: List<&2, F32>) -> Maybe<&2, R2Pair>:
  match mbf:
    case Some{L.Vec{_, bf}}:
      +resid = C.list_sub(r_list, bf)
      Some{R2Pair{w_ss(resid, inv_d, 0.0), w_ss(r_list, inv_d, 0.0)}}
    case None{}:
      None{}

def r2_one.s1(mf: Maybe<&2, L.Vec>, b: L.Mat, r_list: List<&2, F32>, inv_d: List<&2, F32>) -> Maybe<&2, R2Pair>:
  match mf:
    case Some{f}:
      r2_one.s2(L.matvec(b, f), r_list, inv_d)
    case None{}:
      None{}

def r2_one.chk(ok: Bool, +b: L.Mat, +n: U32, +r_list: List<&2, F32>, +inv_d: List<&2, F32>) -> Maybe<&2, R2Pair>:
  match ok:
    case True{}:
      r2_one.s1(L.wlstsq(b, L.Vec{n, inv_d}, L.Vec{n, r_list}), b, r_list, inv_d)
    case False{}:
      None{}

def r2_period.go(+n: U32, item: R2Item) -> Maybe<&2, R2Pair>:
  R2Item{+b, r_list, iv} = item
  L.Mat{+bm, _, _} = b
  L.Vec{+dn, +ds} = iv
  +ok = Bool.and(U32.is_eq(bm, n), Bool.and(U32.is_eq(dn, n), all_pos(ds)))
  r2_one.chk(ok, b, n, r_list, list_inv(ds))

def r2_period(n: U32, item: R2Item) -> Maybe<&2, R2Pair>:
  r2_period.go(n, item)

def sum_r2_pairs(ps: List<&2, R2Pair>, +num: F32, +den: F32) -> R2Pair:
  match ps:
    case Nil{}:
      R2Pair{num, den}
    case Con{R2Pair{a, b}, rest}:
      sum_r2_pairs(rest, (num + a : F32), (den + b : F32))

def r2_fin_pair(p: R2Pair) -> F32:
  R2Pair{+num, +den} = p
  Bool.pick(F32, F32.is_gt(den, 1.0e-30), (1.0 - (num / den) : F32), 0.0)

def r2.fin(mps: Maybe<&2, List<&2, R2Pair>>) -> Maybe<&2, F32>:
  match mps:
    case Some{ps}:
      Some{r2_fin_pair(sum_r2_pairs(ps, 0.0, 0.0))}
    case None{}:
      None{}

def r2.chk(ok: Bool, bs: List<&2, L.Mat>, rrows: List<&2, List<&2, F32>>, ivs: List<&2, L.Vec>, +t: U32, +n: U32) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      +items = pair_r2(bs, rrows, ivs)
      r2.fin(seq_maybe(R2Pair, pmap(~R2Item, ~Maybe<&2, R2Pair>, ~U32, ~r2_period, items, t, n)))
    case False{}:
      None{}

def cross_sectional_r2(+bs: List<&2, L.Mat>, returns: L.Mat, +idio_vars: List<&2, L.Vec>) -> Maybe<&2, F32>:
  L.Mat{+t, +n, rrows} = returns
  +nb = U32.from_nat(List.length(&2, L.Mat, bs))
  +ni = U32.from_nat(List.length(&2, L.Vec, idio_vars))
  +ok = Bool.and(U32.is_eq(nb, t), Bool.and(U32.is_eq(ni, t), Bool.and(U32.is_gt(t, 0), U32.is_gt(n, 0))))
  r2.chk(ok, bs, rrows, idio_vars, t, n)

# ---------------------------------------------------------------- Ch 6: Fundamental Factor Models

# §6.2 Single-period WLS: min_f ||W^{1/2}(r - B f)||_2^2, returning (f_hat, resid, (B^T W B)^{-1}).
def cs_wls.s3(mbf: Maybe<&2, L.Vec>, mcov: Maybe<&2, L.Mat>, f: L.Vec, r: L.Vec) -> Maybe<&2, CSRegResult>:
  match mbf mcov:
    case Some{L.Vec{_, bfs}} Some{ecov}:
      L.Vec{n, rs} = r
      Some{CSRegResult{f, L.Vec{n, C.list_sub(rs, bfs)}, ecov}}
    case _ _:
      None{}

def sym_gram_t(ri: L.Mat) -> L.Mat:
  C.inv_bt_winv_b.s4(L.gram(L.transpose(ri)))

def cs_wls.s2b(mf: Maybe<&2, L.Vec>, mri: Maybe<&2, L.Mat>, b: L.Mat, r: L.Vec) -> Maybe<&2, CSRegResult>:
  match mf mri:
    case Some{+f} Some{ri}:
      cs_wls.s3(L.matvec(b, f), Some{sym_gram_t(ri)}, f, r)
    case _ _:
      None{}

def cs_wls.s1(mqr: Maybe<&2, L.QR>, +k: U32, +b: L.Mat, w: L.Vec, +r: L.Vec) -> Maybe<&2, CSRegResult>:
  match mqr:
    case Some{L.QR{_, rmat}}:
      cs_wls.s2b(L.wlstsq(b, w, r), L.solve_upper_mat(rmat, L.Mat.eye(k)), b, r)
    case None{}:
      None{}

def cs_wls.with_wb(mwb: Maybe<&2, L.Mat>, +k: U32, b: L.Mat, w: L.Vec, r: L.Vec) -> Maybe<&2, CSRegResult>:
  match mwb:
    case Some{wb}:
      cs_wls.s1(L.qr_thin(wb), k, b, w, r)
    case None{}:
      None{}

def cs_wls.chk(ok: Bool, +n: U32, +k: U32, +b: L.Mat, +w: L.Vec, ws: List<&2, F32>, r: L.Vec) -> Maybe<&2, CSRegResult>:
  match ok:
    case True{}:
      cs_wls.with_wb(L.diag_mul(L.Vec{n, C.list_sqrt(ws)}, b), k, b, w, r)
    case False{}:
      None{}

def cross_sectional_wls(+b: L.Mat, r: L.Vec, +weights: L.Vec) -> Maybe<&2, CSRegResult>:
  L.Mat{+n, +k, _} = b
  L.Vec{+nr, _} = r
  L.Vec{+nw, +ws} = weights
  +ok = Bool.and(U32.is_eq(n, nr), Bool.and(U32.is_eq(n, nw), Bool.and(U32.is_gt(k, 0), Bool.and(U32.is_ge(n, k), all_pos(ws)))))
  cs_wls.chk(ok, n, k, b, weights, ws, r)

# §6.2.1 Heston-Rouwenhorst equality-constrained WLS: min_f ||W^{1/2}(r - B f)||_2^2 s.t. C^T f = d.
def cs_con.s3(mbf: Maybe<&2, L.Vec>, f: L.Vec, r: L.Vec, +k: U32) -> Maybe<&2, CSRegResult>:
  match mbf:
    case Some{L.Vec{_, bfs}}:
      L.Vec{n, rs} = r
      Some{CSRegResult{f, L.Vec{n, C.list_sub(rs, bfs)}, L.Mat.zeros(k, k)}}
    case None{}:
      None{}

def cs_con.s2(mf: Maybe<&2, L.Vec>, b: L.Mat, r: L.Vec, +k: U32) -> Maybe<&2, CSRegResult>:
  match mf:
    case Some{+f}:
      cs_con.s3(L.matvec(b, f), f, r, k)
    case None{}:
      None{}

def cs_con.s1(mwb: Maybe<&2, L.Mat>, mwr: Maybe<&2, L.Vec>, c_mat: L.Mat, d_vec: L.Vec, b: L.Mat, r: L.Vec, +k: U32) -> Maybe<&2, CSRegResult>:
  match mwb mwr:
    case Some{wb} Some{wr}:
      cs_con.s2(L.lstsq_constrained(wb, wr, c_mat, d_vec), b, r, k)
    case _ _:
      None{}

def cs_con.run(+sw: L.Vec, +b: L.Mat, +r: L.Vec, c_mat: L.Mat, d_vec: L.Vec, +k: U32) -> Maybe<&2, CSRegResult>:
  cs_con.s1(L.diag_mul(sw, b), L.vmul(sw, r), c_mat, d_vec, b, r, k)

def cs_con.chk(ok: Bool, +n: U32, +k: U32, b: L.Mat, r: L.Vec, ws: List<&2, F32>, c_mat: L.Mat, d_vec: L.Vec) -> Maybe<&2, CSRegResult>:
  match ok:
    case True{}:
      cs_con.run(L.Vec{n, C.list_sqrt(ws)}, b, r, c_mat, d_vec, k)
    case False{}:
      None{}

def cross_sectional_constrained(+b: L.Mat, +r: L.Vec, weights: L.Vec, cons: CSConstraint) -> Maybe<&2, CSRegResult>:
  L.Mat{+n, +k, _} = b
  L.Vec{+nr, _} = r
  L.Vec{+nw, +ws} = weights
  CSConstraint{+c_mat, +d_vec} = cons
  L.Mat{+ck, +cp, _} = c_mat
  L.Vec{+dp, _} = d_vec
  +ok = Bool.and(U32.is_eq(n, nr), Bool.and(U32.is_eq(n, nw), Bool.and(U32.is_eq(k, ck), Bool.and(U32.is_eq(cp, dp), Bool.and(U32.is_gt(k, 0), all_pos(ws))))))
  cs_con.chk(ok, n, k, b, r, ws, c_mat, d_vec)

# §6.2.1 Ridge WLS via augmented thin QR: min_f ||W^{1/2}(r - B f)||_2^2 + delta ||f||_2^2.
def cs_ridge.solve(wb_rows: List<&2, List<&2, F32>>, reg_mat: L.Mat, wr_xs: List<&2, F32>, +n: U32, +k: U32, b: L.Mat, r: L.Vec) -> Maybe<&2, CSRegResult>:
  L.Mat{_, _, reg_rows} = reg_mat
  +nk = (n + k : U32)
  cs_con.s2(L.lstsq(L.Mat{nk, k, List.append(&2, List<&2, F32>, wb_rows, reg_rows)}, L.Vec{nk, List.append(&2, F32, wr_xs, List.replicate(F32, U32.to_nat(k), 0.0))}), b, r, k)

def cs_ridge.s1b(mwb: Maybe<&2, L.Mat>, mwr: Maybe<&2, L.Vec>, +n: U32, +k: U32, +delta: F32, b: L.Mat, r: L.Vec) -> Maybe<&2, CSRegResult>:
  match mwb mwr:
    case Some{L.Mat{_, _, wb_rows}} Some{L.Vec{_, wr_xs}}:
      cs_ridge.solve(wb_rows, L.scale(F32.sqrt(delta), L.Mat.eye(k)), wr_xs, n, k, b, r)
    case _ _:
      None{}

def cs_ridge.run(+sw: L.Vec, +n: U32, +k: U32, +delta: F32, +b: L.Mat, +r: L.Vec) -> Maybe<&2, CSRegResult>:
  cs_ridge.s1b(L.diag_mul(sw, b), L.vmul(sw, r), n, k, delta, b, r)

def cs_ridge.chk(ok: Bool, +n: U32, +k: U32, +delta: F32, b: L.Mat, r: L.Vec, ws: List<&2, F32>) -> Maybe<&2, CSRegResult>:
  match ok:
    case True{}:
      cs_ridge.run(L.Vec{n, C.list_sqrt(ws)}, n, k, delta, b, r)
    case False{}:
      None{}

def cross_sectional_ridge(+b: L.Mat, +r: L.Vec, weights: L.Vec, +delta: F32) -> Maybe<&2, CSRegResult>:
  L.Mat{+n, +k, _} = b
  L.Vec{+nr, _} = r
  L.Vec{+nw, +ws} = weights
  +ok = Bool.and(U32.is_eq(n, nr), Bool.and(U32.is_eq(n, nw), Bool.and(U32.is_gt(k, 0), Bool.and(F32.is_ge(delta, 0.0), all_pos(ws)))))
  cs_ridge.chk(ok, n, k, delta, b, r, ws)

# §6.2.1 Ridgeless (minimum-norm Moore-Penrose pseudoinverse) WLS.
def cs_pinv.s1(mwb: Maybe<&2, L.Mat>, mwr: Maybe<&2, L.Vec>, +tol: F32, +k: U32, b: L.Mat, r: L.Vec) -> Maybe<&2, CSRegResult>:
  match mwb mwr:
    case Some{wb} Some{wr}:
      cs_con.s2(L.matvec(L.pinv(wb, tol), wr), b, r, k)
    case _ _:
      None{}

def cs_pinv.run(+sw: L.Vec, +tol: F32, +k: U32, +b: L.Mat, +r: L.Vec) -> Maybe<&2, CSRegResult>:
  cs_pinv.s1(L.diag_mul(sw, b), L.vmul(sw, r), tol, k, b, r)

def cs_pinv.chk(ok: Bool, +n: U32, +k: U32, +tol: F32, b: L.Mat, r: L.Vec, ws: List<&2, F32>) -> Maybe<&2, CSRegResult>:
  match ok:
    case True{}:
      cs_pinv.run(L.Vec{n, C.list_sqrt(ws)}, tol, k, b, r)
    case False{}:
      None{}

def cross_sectional_ridgeless(+b: L.Mat, +r: L.Vec, weights: L.Vec, +tol: F32) -> Maybe<&2, CSRegResult>:
  L.Mat{+n, +k, _} = b
  L.Vec{+nr, _} = r
  L.Vec{+nw, +ws} = weights
  +ok = Bool.and(U32.is_eq(n, nr), Bool.and(U32.is_eq(n, nw), Bool.and(U32.is_gt(k, 0), all_pos(ws))))
  cs_pinv.chk(ok, n, k, tol, b, r, ws)

# Multi-period parallel cross-sectional factor return & residual estimation (pmap over dates).
type CSPeriodIn is Data:
  CSPeriodIn{b: L.Mat, r: List<&2, F32>, w: L.Vec}

def pair_cs_in(bs: List<&2, L.Mat>, rrows: List<&2, List<&2, F32>>, ws: List<&2, L.Vec>) -> List<&2, CSPeriodIn>:
  match bs rrows ws:
    case Con{b, bt} Con{r, rt} Con{w, wt}:
      CSPeriodIn{b, r, w} <> pair_cs_in(bt, rt, wt)
    case _ _ _:
      Nil{}

def cs_period_solve(opt_cons: Maybe<&2, CSConstraint>, item: CSPeriodIn) -> Maybe<&2, CSRegResult>:
  match opt_cons:
    case None{}:
      CSPeriodIn{+b, r_list, w} = item
      L.Mat{n, _, _} = b
      cross_sectional_wls(b, L.Vec{n, r_list}, w)
    case Some{cons}:
      CSPeriodIn{+b, r_list, w} = item
      L.Mat{n, _, _} = b
      cross_sectional_constrained(b, L.Vec{n, r_list}, w, cons)

def unzip_cs.cons(fr: List<&2, F32>, er: List<&2, F32>, p: List<&2, List<&2, F32>> & List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>> & List<&2, List<&2, F32>>:
  (fs, es) = p
  (fr <> fs, er <> es)

def unzip_cs(rs: List<&2, CSRegResult>) -> List<&2, List<&2, F32>> & List<&2, List<&2, F32>>:
  match rs:
    case Nil{}:
      (Nil{}, Nil{})
    case Con{CSRegResult{L.Vec{_, fr}, L.Vec{_, er}, _}, t}:
      unzip_cs.cons(fr, er, unzip_cs(t))

def est_series.build(p: List<&2, List<&2, F32>> & List<&2, List<&2, F32>>, +t: U32, +n: U32, +k: U32) -> FactorSeries:
  (frows, erows) = p
  FactorSeries{L.Mat{t, k, frows}, L.Mat{t, n, erows}}

def est_series.fin(mrs: Maybe<&2, List<&2, CSRegResult>>, +t: U32, +n: U32, +k: U32) -> Maybe<&2, FactorSeries>:
  match mrs:
    case Some{rs}:
      Some{est_series.build(unzip_cs(rs), t, n, k)}
    case None{}:
      None{}

def first_k(bs: List<&2, L.Mat>) -> U32:
  match bs:
    case Nil{}:
      0
    case Con{L.Mat{_, k, _}, _}:
      k

def est_series.chk(ok: Bool, +bs: List<&2, L.Mat>, rrows: List<&2, List<&2, F32>>, ws: List<&2, L.Vec>, opt_cons: Maybe<&2, CSConstraint>, +t: U32, +n: U32) -> Maybe<&2, FactorSeries>:
  match ok:
    case True{}:
      +k = first_k(bs)
      +items = pair_cs_in(bs, rrows, ws)
      est_series.fin(seq_maybe(CSRegResult, pmap(~CSPeriodIn, ~Maybe<&2, CSRegResult>, ~Maybe<&2, CSConstraint>, ~cs_period_solve, items, t, opt_cons)), t, n, k)
    case False{}:
      None{}

def estimate_factor_series(+bs: List<&2, L.Mat>, returns: L.Mat, +weights_list: List<&2, L.Vec>, opt_cons: Maybe<&2, CSConstraint>) -> Maybe<&2, FactorSeries>:
  L.Mat{+t, +n, rrows} = returns
  +nb = U32.from_nat(List.length(&2, L.Mat, bs))
  +nw = U32.from_nat(List.length(&2, L.Vec, weights_list))
  +ok = Bool.and(U32.is_eq(nb, t), Bool.and(U32.is_eq(nw, t), Bool.and(U32.is_gt(t, 0), U32.is_gt(n, 0))))
  est_series.chk(ok, bs, rrows, weights_list, opt_cons, t, n)

# End-to-end two-pass fundamental factor model estimator (Paleologo Ch 6):
# Pass 1: equal-weight cross-sectional regression -> proxy idio variances.
# Pass 2: WLS (1 / idio_var) cross-sectional regression -> F (T x K), E (T x N).
# Factor cov: DCC (if hl_vol != hl_corr) or EWMA/Newey-West + optional debias + shrinkage + optional STVU + PSD floor.
# Idio var: EWMA + shrinkage + eig_floor.
def last_mat(ms: List<&2, L.Mat>, fallback: L.Mat) -> L.Mat:
  match ms:
    case Nil{}:
      fallback
    case Con{m, Nil{}}:
      m
    case Con{_, t}:
      last_mat(t, fallback)

def fund_cov_no_nw(same_hl: Bool, f_rets: L.Mat, +hl_vol: F32, +hl_corr: F32) -> Maybe<&2, L.Mat>:
  match same_hl:
    case True{}:
      ewma_cov(f_rets, hl_vol, False{})
    case False{}:
      dcc_cov(f_rets, hl_vol, hl_corr)

def fund_cov_base2(has_nw: Bool, f_rets: L.Mat, +hl_vol: F32, +hl_corr: F32, +nw_lags: U32) -> Maybe<&2, L.Mat>:
  match has_nw:
    case True{}:
      cov_newey_west(f_rets, nw_lags, hl_corr)
    case False{}:
      fund_cov_no_nw(F32.is_eq(hl_vol, hl_corr), f_rets, hl_vol, hl_corr)

def fund_opt_debias(do_db: Bool, mcov: Maybe<&2, L.Mat>, b_last: L.Mat, idio_v: L.Vec, +eig_floor: F32) -> Maybe<&2, L.Mat>:
  match do_db mcov:
    case True{} Some{cf}:
      debias_factor_cov(cf, b_last, idio_v, eig_floor)
    case False{} Some{cf}:
      Some{cf}
    case _ _:
      None{}

def fund_opt_shrink(mcov: Maybe<&2, L.Mat>, +shrink_f: F32) -> Maybe<&2, L.Mat>:
  match mcov:
    case Some{cf}:
      shrink_to_identity(cf, shrink_f)
    case None{}:
      None{}

def fund_opt_stvu(do_stvu: Bool, mcov: Maybe<&2, L.Mat>, f_rets: L.Mat, +hl_stvu: F32) -> Maybe<&2, L.Mat>:
  match do_stvu mcov:
    case True{} Some{cf}:
      stvu_adjust_cov(f_rets, cf, hl_stvu, False{})
    case False{} Some{cf}:
      Some{cf}
    case _ _:
      None{}

def fund_opt_psd(mcov: Maybe<&2, L.Mat>, +eig_floor: F32) -> Maybe<&2, L.Mat>:
  match mcov:
    case Some{cf}:
      psd_project(cf, eig_floor)
    case None{}:
      None{}

def fund_fit.finish(mcov_f: Maybe<&2, L.Mat>, b_last: L.Mat, idio_v: L.Vec, f_rets: L.Mat, resid: L.Mat) -> Maybe<&2, FundModelFit>:
  match mcov_f:
    case Some{cf}:
      Some{FundModelFit{P.FactorModel{b_last, cf, idio_v}, f_rets, resid}}
    case None{}:
      None{}

def fund_fit.build_cov(+iv: L.Vec, +f_rets: L.Mat, resid: L.Mat, +b_last: L.Mat, cfg: FundConfig) -> Maybe<&2, FundModelFit>:
  FundConfig{hl_vol, hl_corr, _, +nw_lags, shrink_f, _, hl_stvu, use_stvu, debias, +eig_floor} = cfg
  +c0 = fund_cov_base2(U32.is_gt(nw_lags, 0), f_rets, hl_vol, hl_corr, nw_lags)
  +c1 = fund_opt_debias(debias, c0, b_last, iv, eig_floor)
  +c2 = fund_opt_shrink(c1, shrink_f)
  +c3 = fund_opt_stvu(use_stvu, c2, f_rets, hl_stvu)
  +c4 = fund_opt_psd(c3, eig_floor)
  fund_fit.finish(c4, b_last, iv, f_rets, resid)

def fund_fit.with_idio2(miv: Maybe<&2, L.Vec>, f_rets: L.Mat, resid: L.Mat, b_last: L.Mat, +cfg: FundConfig) -> Maybe<&2, FundModelFit>:
  match miv:
    case Some{L.Vec{n, iv_raw}}:
      FundConfig{_, _, _, _, _, _, _, _, _, eig_floor} = cfg
      fund_fit.build_cov(L.Vec{n, C.floor_list(iv_raw, eig_floor)}, f_rets, resid, b_last, cfg)
    case None{}:
      None{}

def fund_fit.shrink_iv(miv: Maybe<&2, L.Vec>, +shrink_idio: F32) -> Maybe<&2, L.Vec>:
  match miv:
    case Some{iv}:
      idio_var_shrink(iv, shrink_idio)
    case None{}:
      None{}

def fund_fit.pass2(mfs2: Maybe<&2, FactorSeries>, b_last: L.Mat, +cfg: FundConfig) -> Maybe<&2, FundModelFit>:
  match mfs2:
    case Some{FactorSeries{f_rets, +resid}}:
      FundConfig{_, _, hl_idio, _, _, shrink_idio, _, _, _, _} = cfg
      fund_fit.with_idio2(fund_fit.shrink_iv(idio_var_ewma(resid, hl_idio), shrink_idio), f_rets, resid, b_last, cfg)
    case None{}:
      None{}

def fund_fit.pass1_iv(miv1: Maybe<&2, L.Vec>, +bs: List<&2, L.Mat>, returns: L.Mat, opt_cons: Maybe<&2, CSConstraint>, +cfg: FundConfig, +t: U32, b_last: L.Mat) -> Maybe<&2, FundModelFit>:
  match miv1:
    case Some{L.Vec{n, iv1}}:
      FundConfig{_, _, _, _, _, _, _, _, _, eig_floor} = cfg
      +w2 = List.replicate(L.Vec, U32.to_nat(t), L.Vec{n, list_inv(C.floor_list(iv1, eig_floor))})
      fund_fit.pass2(estimate_factor_series(bs, returns, w2, opt_cons), b_last, cfg)
    case None{}:
      None{}

def fund_fit.pass1(mfs1: Maybe<&2, FactorSeries>, bs: List<&2, L.Mat>, returns: L.Mat, opt_cons: Maybe<&2, CSConstraint>, +cfg: FundConfig, +t: U32, b_last: L.Mat) -> Maybe<&2, FundModelFit>:
  match mfs1:
    case Some{FactorSeries{_, resid1}}:
      FundConfig{_, _, hl_idio, _, _, _, _, _, _, _} = cfg
      fund_fit.pass1_iv(idio_var_ewma(resid1, hl_idio), bs, returns, opt_cons, cfg, t, b_last)
    case None{}:
      None{}

def fund_fit.chk(ok: Bool, +bs: List<&2, L.Mat>, +returns: L.Mat, +opt_cons: Maybe<&2, CSConstraint>, cfg: FundConfig, +t: U32, +n: U32) -> Maybe<&2, FundModelFit>:
  match ok:
    case True{}:
      +w1 = List.replicate(L.Vec, U32.to_nat(t), L.Vec.ones(n))
      +b_last = last_mat(bs, L.Mat.zeros(n, 0))
      fund_fit.pass1(estimate_factor_series(bs, returns, w1, opt_cons), bs, returns, opt_cons, cfg, t, b_last)
    case False{}:
      None{}

def fit_fundamental_model(+returns: L.Mat, +bs: List<&2, L.Mat>, opt_cons: Maybe<&2, CSConstraint>, cfg: FundConfig) -> Maybe<&2, FundModelFit>:
  L.Mat{+t, +n, _} = returns
  +nb = U32.from_nat(List.length(&2, L.Mat, bs))
  +ok = Bool.and(U32.is_eq(nb, t), Bool.and(U32.is_gt(t, 0), U32.is_gt(n, 0)))
  fund_fit.chk(ok, bs, returns, opt_cons, cfg, t, n)

# ---------------------------------------------------------------- Ch 7: Statistical Factor Models

# §7.1.1 & §7.5.1 Weighted SVD / PCA on T x N returns panel.
# Row t of R_tilde is sqrt(w_t) * r_t (sum w_t = 1).
# Singular values s_j of R_tilde satisfy lambda_j = s_j^2 (eigenvalues of R^T diag(w) R).
# Right singular vectors V_k (N x K) are orthonormal loadings B; F = R * V_k (T x K).
def pca_from_svd.fin(mf: Maybe<&2, L.Mat>, b_mat: L.Mat, +k: U32, +ss: List<&2, F32>) -> Maybe<&2, PcaResult>:
  match mf:
    case Some{f_rets}:
      Some{PcaResult{b_mat, f_rets, L.Vec{k, ss}, L.Vec{k, C.list_sq(ss)}}}
    case None{}:
      None{}

def pca_from_svd2(svd: L.SVD, returns: L.Mat) -> Maybe<&2, PcaResult>:
  L.SVD{_, L.Vec{k, ss}, vt} = svd
  +b_mat = L.transpose(vt)
  pca_from_svd.fin(L.matmul(returns, b_mat), b_mat, k, ss)

def pca_run_svd(use_subspace: Bool, r_w: L.Mat, +k: U32, returns: L.Mat) -> Maybe<&2, PcaResult>:
  match use_subspace:
    case True{}:
      pca_from_svd2(SSVD.svd_top_k(r_w, k, 8, 4), returns)
    case False{}:
      pca_from_svd2(SSVD.slice_svd(L.svd_thin(r_w), k), returns)

def pca_with_rw(mrw: Maybe<&2, L.Mat>, +k: U32, use_subspace: Bool, returns: L.Mat) -> Maybe<&2, PcaResult>:
  match mrw:
    case Some{r_w}:
      pca_run_svd(use_subspace, r_w, k, returns)
    case None{}:
      None{}

def pca_with_w(mw: Maybe<&2, L.Vec>, +k: U32, use_subspace: Bool, +returns: L.Mat) -> Maybe<&2, PcaResult>:
  match mw:
    case Some{L.Vec{t, ws}}:
      pca_with_rw(L.diag_mul(L.Vec{t, C.list_sqrt(ws)}, returns), k, use_subspace, returns)
    case None{}:
      None{}

def pca_mode(use_ewma: Bool, +returns: L.Mat, +t: U32, +k: U32, +half_life: F32, use_subspace: Bool) -> Maybe<&2, PcaResult>:
  match use_ewma:
    case True{}:
      pca_with_w(ewma_weights(t, half_life), k, use_subspace, returns)
    case False{}:
      +sc = (1.0 / F32.sqrt(U32.to_f32(t)) : F32)
      pca_run_svd(use_subspace, L.scale(sc, returns), k, returns)

def pca_svd.chk(ok: Bool, returns: L.Mat, +t: U32, +k: U32, +half_life: F32, use_subspace: Bool) -> Maybe<&2, PcaResult>:
  match ok:
    case True{}:
      pca_mode(F32.is_gt(half_life, 0.0), returns, t, k, half_life, use_subspace)
    case False{}:
      None{}

def pca_svd(+returns: L.Mat, +k: U32, +half_life: F32, use_subspace: Bool) -> Maybe<&2, PcaResult>:
  L.Mat{+t, +n, _} = returns
  +mn = U32.min(t, n)
  +ok = Bool.and(U32.is_gt(k, 0), U32.is_le(k, mn))
  pca_svd.chk(ok, returns, t, k, half_life, use_subspace)

# §7.1.2 Eq (7.17-7.19) Probabilistic PCA (Tipping & Bishop 1999):
# B = V_k (N x K), Omega_f = diag(max(lam_j - lam_bar, floor)), Omega_eps = max(lam_bar, floor) * I_N,
# where lam_bar = (tr(Sigma) - sum_{j=1..k} lam_j) / (N - k).
def sub_floor_list(xs: List<&2, F32>, +sub: F32, +fl: F32) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      fmax((h - sub : F32), fl) <> sub_floor_list(t, sub, fl)

def ppca.build(svd: L.SVD, +t: U32, +n: U32, +k: U32, +frob_sq: F32, +eig_floor: F32) -> P.FactorModel:
  L.SVD{_, L.Vec{_, +ss}, vt} = svd
  +lams = C.list_sq(ss)
  +top_k = list_take(F32, U32.to_nat(k), lams)
  +tr_sig = (frob_sq / U32.to_f32(t) : F32)
  +bulk_sum = fmax((tr_sig - C.list_sum(top_k) : F32), 0.0)
  +lam_bar = fmax((bulk_sum / U32.to_f32((n - k : U32)) : F32), eig_floor)
  +fvars = sub_floor_list(top_k, lam_bar, eig_floor)
  +b_mat = L.transpose(L.slice_rows(vt, 0, k))
  P.FactorModel{b_mat, L.Mat.diag(L.Vec{k, fvars}), L.Vec{n, List.replicate(F32, U32.to_nat(n), lam_bar)}}

def ppca.chk(ok: Bool, +returns: L.Mat, +t: U32, +n: U32, +k: U32, +eig_floor: F32) -> Maybe<&2, P.FactorModel>:
  match ok:
    case True{}:
      +fr = L.frobenius(returns)
      +sc = (1.0 / F32.sqrt(U32.to_f32(t)) : F32)
      Some{ppca.build(L.svd_thin(L.scale(sc, returns)), t, n, k, (fr * fr : F32), eig_floor)}
    case False{}:
      None{}

def ppca_fit(+returns: L.Mat, +k: U32, +eig_floor: F32) -> Maybe<&2, P.FactorModel>:
  L.Mat{+t, +n, _} = returns
  +mn = U32.min(t, n)
  +ok = Bool.and(U32.is_gt(k, 0), Bool.and(U32.is_le(k, mn), Bool.and(U32.is_lt(k, n), F32.is_gt(eig_floor, 0.0))))
  ppca.chk(ok, returns, t, n, k, eig_floor)

# §7.2.3-7.2.4 Spiked eigenvalue shrinkage:
# mode 0: none (identity + floor)
# mode 1: BBP/Donoho offset Eq (7.33): max(lam - gamma, floor) where gamma = N / T
# mode 2: PPCA bulk mean: max(lam - k2, floor) (caller passes lam_bar in k2)
# mode 3: heavy-tail linear §7.2.4: max(k1 * lam - k2, floor)
def spiked_shrink.one(+lam: F32, +mode: U32, +gamma: F32, +k1: F32, +k2: F32, +fl: F32) -> F32:
  +v = Bool.pick(F32, U32.is_eq(mode, 1), (lam - gamma : F32),
         Bool.pick(F32, U32.is_eq(mode, 2), (lam - k2 : F32),
           Bool.pick(F32, U32.is_eq(mode, 3), ((k1 * lam) - k2 : F32), lam)))
  fmax(v, fl)

def spiked_shrink.go(xs: List<&2, F32>, +mode: U32, +gamma: F32, +k1: F32, +k2: F32, +fl: F32) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      spiked_shrink.one(h, mode, gamma, k1, k2, fl) <> spiked_shrink.go(t, mode, gamma, k1, k2, fl)

def spiked_shrink.chk(ok: Bool, +m: U32, xs: List<&2, F32>, +n: U32, +t: U32, +mode: U32, +k1: F32, +k2: F32, +fl: F32) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      +gamma = (U32.to_f32(n) / U32.to_f32(t) : F32)
      Some{L.Vec{m, spiked_shrink.go(xs, mode, gamma, k1, k2, fl)}}
    case False{}:
      None{}

def spiked_shrink_eigenvalues(lambdas: L.Vec, +n: U32, +t: U32, +mode: U32, +k1: F32, +k2: F32, +eig_floor: F32) -> Maybe<&2, L.Vec>:
  L.Vec{+m, xs} = lambdas
  +ok = Bool.and(U32.is_gt(n, 0), Bool.and(U32.is_gt(t, 0), F32.is_ge(eig_floor, 0.0)))
  spiked_shrink.chk(ok, m, xs, n, t, mode, k1, k2, eig_floor)

# §7.2.5 Factor-count selection criteria:

# 1. Marchenko-Pastur / spiked threshold Eq (7.37): count lambdas >= bulk_scale * (1 + sqrt(N/T))^2.
def count_ge(xs: List<&2, F32>, +thr: F32, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      +acc1 = Bool.pick(U32, F32.is_ge(h, thr), (acc + 1 : U32), acc)
      count_ge(t, thr, acc1)

def select_k_thr.chk(ok: Bool, xs: List<&2, F32>, +n: U32, +t: U32, +bulk_scale: F32) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      +sqg = F32.sqrt((U32.to_f32(n) / U32.to_f32(t) : F32))
      +edge = ((1.0 + sqg) * (1.0 + sqg) : F32)
      Some{count_ge(xs, (bulk_scale * edge : F32), 0)}
    case False{}:
      None{}

def select_k_threshold(lambdas: L.Vec, +n: U32, +t: U32, +bulk_scale: F32) -> Maybe<&2, U32>:
  L.Vec{+m, xs} = lambdas
  +ok = Bool.and(U32.is_gt(m, 0), Bool.and(U32.is_gt(n, 0), Bool.and(U32.is_gt(t, 0), F32.is_gt(bulk_scale, 0.0))))
  select_k_thr.chk(ok, xs, n, t, bulk_scale)

# 2. Maximum eigenvalue gap / log-gap Eq (7.38): argmax_{1 <= k <= k_max} (lam_k - lam_{k+1}) or log ratio.
def gap_val(use_log: Bool, +a: F32, +b: F32) -> F32:
  match use_log:
    case True{}:
      (F32.log(fmax(a, 1.0e-20)) - F32.log(fmax(b, 1.0e-20)) : F32)
    case False{}:
      (a - b : F32)

def select_k_gap.go(rem: Nat, xs: List<&2, F32>, +k: U32, +best_k: U32, +best_g: F32, +use_log: Bool) -> U32:
  match rem xs:
    case 0n _:
      best_k
    case 1n+p Con{a, Con{+b, rest}}:
      +g = gap_val(use_log, a, b)
      +better = F32.is_gt(g, best_g)
      select_k_gap.go(p, b <> rest, (k + 1 : U32), Bool.pick(U32, better, k, best_k), Bool.pick(F32, better, g, best_g), use_log)
    case _ _:
      best_k

def select_k_gap.chk(ok: Bool, xs: List<&2, F32>, +m: U32, +k_max: U32, use_log: Bool) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      +lim = U32.min(k_max, (m - 1 : U32))
      Some{select_k_gap.go(U32.to_nat(lim), xs, 1, 1, F32.neg(1.0e30), use_log)}
    case False{}:
      None{}

def select_k_gap(lambdas: L.Vec, +k_max: U32, use_log: Bool) -> Maybe<&2, U32>:
  L.Vec{+m, xs} = lambdas
  +ok = Bool.and(U32.is_gt(m, 1), U32.is_gt(k_max, 0))
  select_k_gap.chk(ok, xs, m, k_max, use_log)

# 3. Bai & Ng (2008) Eq (7.39-7.40):
# Given all singular values s_1 >= ... >= s_r of raw return matrix R (T x N):
#   V(k) = (1 / (N * T)) * sum_{j > k} s_j^2  (for k = 0..k_max)
#   f(N, T) = ((N + T) / (N * T)) * log((N * T) / (N + T))
#   IC_p1(k) = log(V(k)) + k * f(N, T)
#   PC_p1(k) = V(k) + k * V(k_max) * f(N, T)
def head_f32_zero(xs: List<&2, F32>) -> F32:
  match xs:
    case Con{h, _}:
      h
    case Nil{}:
      0.0

def tail_f32(xs: List<&2, F32>) -> List<&2, F32>:
  match xs:
    case Con{_, t}:
      t
    case Nil{}:
      Nil{}

def baing_scan2.go(
  rem: Nat,
  +s2s: List<&2, F32>,
  +k: U32,
  +rem_ss: F32,
  +inv_nt: F32,
  +pen: F32,
  +vkmax: F32,
  +best_k_ic: U32,
  +best_ic: F32,
  +best_k_pc: U32,
  +best_pc: F32,
  +ics: List<&2, F32>,
  +pcs: List<&2, F32>
) -> BaiNgResult:
  match rem:
    case 0n:
      +len = U32.from_nat(List.length(&2, F32, ics))
      BaiNgResult{best_k_ic, best_k_pc, L.Vec{len, List.reverse(&2, F32, ics)}, L.Vec{len, List.reverse(&2, F32, pcs)}}
    case 1n+p:
      +vk = fmax((rem_ss * inv_nt : F32), 1.0e-20)
      +kf = U32.to_f32(k)
      +ic = (F32.log(vk) + (kf * pen) : F32)
      +pc = (vk + ((kf * vkmax) * pen) : F32)
      +bic = F32.is_lt(ic, best_ic)
      +bpc = F32.is_lt(pc, best_pc)
      +next_ss = fmax((rem_ss - head_f32_zero(s2s) : F32), 0.0)
      baing_scan2.go(
        p, tail_f32(s2s), (k + 1 : U32), next_ss, inv_nt, pen, vkmax,
        Bool.pick(U32, bic, k, best_k_ic), Bool.pick(F32, bic, ic, best_ic),
        Bool.pick(U32, bpc, k, best_k_pc), Bool.pick(F32, bpc, pc, best_pc),
        ic <> ics, pc <> pcs
      )

def select_k_baing.chk(ok: Bool, ss: List<&2, F32>, +m: U32, +n: U32, +t: U32, +k_max: U32) -> Maybe<&2, BaiNgResult>:
  match ok:
    case True{}:
      +km = U32.min(k_max, (m - 1 : U32))
      +s2 = C.list_sq(ss)
      +tot_ss = C.list_sum(s2)
      +kmax_ss = C.list_sum(list_drop(F32, U32.to_nat(km), s2))
      +nf = U32.to_f32(n)
      +tf = U32.to_f32(t)
      +nt = (nf * tf : F32)
      +npt = (nf + tf : F32)
      +inv_nt = (1.0 / nt : F32)
      +pen = ((npt / nt) * F32.log((nt / npt : F32)) : F32)
      +vkmax = fmax((kmax_ss * inv_nt : F32), 1.0e-20)
      Some{baing_scan2.go(U32.to_nat((km + 1 : U32)), s2, 0, tot_ss, inv_nt, pen, vkmax, 0, 1.0e30, 0, 1.0e30, Nil{}, Nil{})}
    case False{}:
      None{}

def select_k_bai_ng(singular_values: L.Vec, +n: U32, +t: U32, +k_max: U32) -> Maybe<&2, BaiNgResult>:
  L.Vec{+m, ss} = singular_values
  +ok = Bool.and(U32.is_gt(m, 1), Bool.and(U32.is_gt(n, 0), Bool.and(U32.is_gt(t, 0), U32.is_gt(k_max, 0))))
  select_k_baing.chk(ok, ss, m, n, t, k_max)

# §7.3.2 & §7.5.2 Eigenfactor turnover, sign alignment, Procrustes alignment, subspace distance.

def col_cos_abs(+c1: List<&2, F32>, +c2: List<&2, F32>) -> F32:
  +n1 = F32.sqrt(C.list_sum_sq.go(c1, 0.0))
  +n2 = F32.sqrt(C.list_sum_sq.go(c2, 0.0))
  +den = (n1 * n2 : F32)
  Bool.pick(F32, F32.is_gt(den, 1.0e-30), fmin(1.0, (F32.abs(L.dot_raw(c1, c2)) / den : F32)), 0.0)

def eig_to.cols(cs1: List<&2, List<&2, F32>>, cs2: List<&2, List<&2, F32>>) -> List<&2, F32>:
  match cs1 cs2:
    case Con{+c1, t1} Con{+c2, t2}:
      (2.0 * (1.0 - col_cos_abs(c1, c2)) : F32) <> eig_to.cols(t1, t2)
    case _ _:
      Nil{}

def eig_to.from_t(bt1: L.Mat, bt2: L.Mat, +k: U32) -> EigenTurnover:
  L.Mat{_, _, cs1} = bt1
  L.Mat{_, _, cs2} = bt2
  +tos = eig_to.cols(cs1, cs2)
  EigenTurnover{L.Vec{k, tos}, (C.list_sum(tos) / U32.to_f32(k) : F32)}

def eig_to.chk2(ok: Bool, b_prev: L.Mat, b_curr: L.Mat, +k: U32) -> Maybe<&2, EigenTurnover>:
  match ok:
    case True{}:
      Some{eig_to.from_t(L.transpose(b_prev), L.transpose(b_curr), k)}
    case False{}:
      None{}

def eigenfactor_turnover(+b_prev: L.Mat, +b_curr: L.Mat) -> Maybe<&2, EigenTurnover>:
  L.Mat{+m1, +k1, _} = b_prev
  L.Mat{+m2, +k2, _} = b_curr
  +ok = Bool.and(U32.is_eq(m1, m2), Bool.and(U32.is_eq(k1, k2), U32.is_gt(k1, 0)))
  eig_to.chk2(ok, b_prev, b_curr, k1)

# Column-wise sign alignment so <b_curr[:, j], b_prev[:, j]> >= 0.
def align_sign_cols(cs_prev: List<&2, List<&2, F32>>, cs_curr: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match cs_prev cs_curr:
    case Con{cp, pt} Con{+cc, ct}:
      +d = L.dot_raw(cp, cc)
      +col_out = Bool.pick(List<&2, F32>, F32.is_lt(d, 0.0), list_neg(cc), cc)
      col_out <> align_sign_cols(pt, ct)
    case _ _:
      Nil{}

def align_sign.from_t(bt1: L.Mat, bt2: L.Mat, +k: U32, +n: U32) -> L.Mat:
  L.Mat{_, _, cs1} = bt1
  L.Mat{_, _, cs2} = bt2
  L.transpose(L.Mat{k, n, align_sign_cols(cs1, cs2)})

def align_sign.chk(ok: Bool, b_prev: L.Mat, b_curr: L.Mat, +k: U32, +n: U32) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      Some{align_sign.from_t(L.transpose(b_prev), L.transpose(b_curr), k, n)}
    case False{}:
      None{}

def align_sign(+b_prev: L.Mat, +b_curr: L.Mat) -> Maybe<&2, L.Mat>:
  L.Mat{+m1, +k1, _} = b_prev
  L.Mat{+m2, +k2, _} = b_curr
  +ok = Bool.and(U32.is_eq(m1, m2), Bool.and(U32.is_eq(k1, k2), U32.is_gt(k1, 0)))
  align_sign.chk(ok, b_prev, b_curr, k1, m1)

# §7.3.2 Eq (7.43) Orthogonal Procrustes alignment of a FactorModel against previous loadings:
# Finds orthogonal X = argmin ||B_prev - B_curr X||_F, returns FactorModel{B_curr X, X^T Omega_f X, idio_var}.
def align_proc.s3(mbt: Maybe<&2, L.Mat>, mcf: Maybe<&2, L.Mat>, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match mbt mcf:
    case Some{bt} Some{L.Mat{+k, _, rows}}:
      Some{P.FactorModel{bt, C.symmetrize_raw(k, rows), idio_var}}
    case _ _:
      None{}

def align_proc.s2(mbt: Maybe<&2, L.Mat>, mxtc: Maybe<&2, L.Mat>, x_mat: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match mxtc:
    case Some{xtc}:
      align_proc.s3(mbt, L.matmul(xtc, x_mat), idio_var)
    case None{}:
      None{}

def align_proc.s1(mx: Maybe<&2, L.Mat>, b_curr: L.Mat, cov_f: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match mx:
    case Some{+x}:
      align_proc.s2(L.matmul(b_curr, x), L.matmul(L.transpose(x), cov_f), x, idio_var)
    case None{}:
      None{}

def align_proc.chk(ok: Bool, b_prev: L.Mat, +b_curr: L.Mat, cov_f: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match ok:
    case True{}:
      align_proc.s1(L.procrustes(b_prev, b_curr), b_curr, cov_f, idio_var)
    case False{}:
      None{}

def align_procrustes(fm_prev: P.FactorModel, +fm_curr: P.FactorModel) -> Maybe<&2, P.FactorModel>:
  P.FactorModel{+b_prev, _, _} = fm_prev
  L.Mat{+m1, +k1, _} = b_prev
  P.FactorModel{+b_curr, cov_f, idio_var} = fm_curr
  L.Mat{+m2, +k2, _} = b_curr
  +ok = Bool.and(fm_dims_ok(fm_curr), Bool.and(U32.is_eq(m1, m2), Bool.and(U32.is_eq(k1, k2), U32.is_gt(k1, 0))))
  align_proc.chk(ok, b_prev, b_curr, cov_f, idio_var)

# Rotation-invariant subspace distance between column spaces of B1, B2 (both N x K):
# d(B1, B2) = sqrt(max(0, 1 - ||Q1^T Q2||_F^2 / K)) in [0, 1].
def sub_dist.s2(mq12: Maybe<&2, L.Mat>, +k: U32) -> Maybe<&2, F32>:
  match mq12:
    case Some{m}:
      +f = L.frobenius(m)
      +rat = ((f * f) / U32.to_f32(k) : F32)
      Some{F32.sqrt(fmax(0.0, (1.0 - rat : F32)))}
    case None{}:
      None{}

def sub_dist.s1(mq1: Maybe<&2, L.QR>, mq2: Maybe<&2, L.QR>, +k: U32) -> Maybe<&2, F32>:
  match mq1 mq2:
    case Some{L.QR{q1, _}} Some{L.QR{q2, _}}:
      sub_dist.s2(L.matmul(L.transpose(q1), q2), k)
    case _ _:
      None{}

def sub_dist.chk(ok: Bool, b1: L.Mat, b2: L.Mat, +k: U32) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      sub_dist.s1(L.qr_thin(b1), L.qr_thin(b2), k)
    case False{}:
      None{}

def subspace_distance(+b1: L.Mat, +b2: L.Mat) -> Maybe<&2, F32>:
  L.Mat{+m1, +k1, _} = b1
  L.Mat{+m2, +k2, _} = b2
  +ok = Bool.and(U32.is_eq(m1, m2), Bool.and(U32.is_eq(k1, k2), Bool.and(U32.is_gt(k1, 0), U32.is_ge(m1, k1))))
  sub_dist.chk(ok, b1, b2, k1)

# §7.5.1 Two-stage weighted statistical factor model (Paleologo's flagship statistical estimator).
def col_sum_sq_rows.go(rows: List<&2, List<&2, F32>>, acc: List<&2, F32>) -> List<&2, F32>:
  match rows:
    case Nil{}:
      acc
    case Con{r, rt}:
      col_sum_sq_rows.go(rt, add_f32_lists(acc, C.list_sq(r)))

def col_sum_sq_mat(m: L.Mat) -> L.Vec:
  L.Mat{_, +n, rows} = m
  L.Vec{n, col_sum_sq_rows.go(rows, List.replicate(F32, U32.to_nat(n), 0.0))}

def stat_s1_resid.s3(mr: Maybe<&2, L.Mat>) -> Maybe<&2, L.Vec>:
  match mr:
    case Some{e1}:
      Some{col_sum_sq_mat(e1)}
    case None{}:
      None{}

def stat_s1_resid.s2(mr_hat: Maybe<&2, L.Mat>, r_fast: L.Mat) -> Maybe<&2, L.Vec>:
  match mr_hat:
    case Some{r_hat}:
      stat_s1_resid.s3(L.msub(r_fast, r_hat))
    case None{}:
      None{}

def stat_s1_resid.s1(mus: Maybe<&2, L.Mat>, vt: L.Mat, r_fast: L.Mat) -> Maybe<&2, L.Vec>:
  match mus:
    case Some{us}:
      stat_s1_resid.s2(L.matmul(us, vt), r_fast)
    case None{}:
      None{}

def stat_s1_from_svd(svd: L.SVD, r_fast: L.Mat) -> Maybe<&2, L.Vec>:
  L.SVD{u, s, vt} = svd
  stat_s1_resid.s1(L.mul_diag(u, s), vt, r_fast)

def stat_s1_svd(use_sub: Bool, +r_fast: L.Mat, +p: U32) -> Maybe<&2, L.Vec>:
  match use_sub:
    case True{}:
      stat_s1_from_svd(SSVD.svd_top_k(r_fast, p, 6, 3), r_fast)
    case False{}:
      stat_s1_from_svd(SSVD.slice_svd(L.svd_thin(r_fast), p), r_fast)

def stat_s1_run2(has_p: Bool, use_sub: Bool, r_fast: L.Mat, +p: U32) -> Maybe<&2, L.Vec>:
  match has_p:
    case False{}:
      Some{col_sum_sq_mat(r_fast)}
    case True{}:
      stat_s1_svd(use_sub, r_fast, p)

def weight_time_mat.s1(mw: Maybe<&2, L.Vec>, mat: L.Mat) -> Maybe<&2, L.Mat>:
  match mw:
    case Some{L.Vec{t, ws}}:
      L.diag_mul(L.Vec{t, C.list_sqrt(ws)}, mat)
    case None{}:
      None{}

def weight_time_mat.mode(use_ewma: Bool, mat: L.Mat, +t: U32, +hl: F32) -> Maybe<&2, L.Mat>:
  match use_ewma:
    case True{}:
      weight_time_mat.s1(ewma_weights(t, hl), mat)
    case False{}:
      Some{L.scale((1.0 / F32.sqrt(U32.to_f32(t)) : F32), mat)}

def weight_time_mat(+mat: L.Mat, +hl: F32) -> Maybe<&2, L.Mat>:
  L.Mat{+t, _, _} = mat
  weight_time_mat.mode(F32.is_gt(hl, 0.0), mat, t, hl)

def stat_s2.fin2(miv: Maybe<&2, L.Vec>, b_mat: L.Mat, cov_f: L.Mat, f_rets: L.Mat, resid: L.Mat, s_vec: L.Vec, +eig_floor: F32) -> Maybe<&2, StatModelFit>:
  match miv:
    case Some{L.Vec{n, iv_raw}}:
      Some{StatModelFit{P.FactorModel{b_mat, cov_f, L.Vec{n, C.floor_list(iv_raw, eig_floor)}}, f_rets, resid, s_vec}}
    case None{}:
      None{}

def stat_s2.with_resid(mres: Maybe<&2, L.Mat>, b_mat: L.Mat, cov_f: L.Mat, f_rets: L.Mat, s_vec: L.Vec, cfg: StatConfig) -> Maybe<&2, StatModelFit>:
  match mres:
    case Some{+resid}:
      StatConfig{_, _, hl_fast, _, _, _, _, shrink_idio, _, eig_floor} = cfg
      stat_s2.fin2(fund_fit.shrink_iv(idio_var_ewma(resid, hl_fast), shrink_idio), b_mat, cov_f, f_rets, resid, s_vec, eig_floor)
    case None{}:
      None{}

def stat_s2.with_fbt(mfbt: Maybe<&2, L.Mat>, returns: L.Mat, b_mat: L.Mat, cov_f: L.Mat, f_rets: L.Mat, s_vec: L.Vec, cfg: StatConfig) -> Maybe<&2, StatModelFit>:
  match mfbt:
    case Some{fbt}:
      stat_s2.with_resid(L.msub(returns, fbt), b_mat, cov_f, f_rets, s_vec, cfg)
    case None{}:
      None{}

def stat_s2.with_bf(mb: Maybe<&2, L.Mat>, mf: Maybe<&2, L.Mat>, returns: L.Mat, cov_f: L.Mat, s_vec: L.Vec, cfg: StatConfig) -> Maybe<&2, StatModelFit>:
  match mb mf:
    case Some{+b_mat} Some{+f_rets}:
      stat_s2.with_fbt(L.matmul(f_rets, L.transpose(b_mat)), returns, b_mat, cov_f, f_rets, s_vec, cfg)
    case _ _:
      None{}

def stat_s2.with_sh(msh: Maybe<&2, L.Vec>, returns: L.Mat, r_white: L.Mat, sd_vec: L.Vec, +vk: L.Mat, s_vec: L.Vec, cfg: StatConfig) -> Maybe<&2, StatModelFit>:
  match msh:
    case Some{lam_sh}:
      stat_s2.with_bf(L.diag_mul(sd_vec, vk), L.matmul(r_white, vk), returns, L.Mat.diag(lam_sh), s_vec, cfg)
    case None{}:
      None{}

def stat_s2.from_svd(svd: L.SVD, +returns: L.Mat, r_white: L.Mat, sd_vec: L.Vec, +t: U32, +n: U32, +rw_frob_sq: F32, +cfg: StatConfig) -> Maybe<&2, StatModelFit>:
  L.SVD{_, L.Vec{+k, +ss}, vt} = svd
  StatConfig{_, _, _, _, +shrink_mode, shrink_k1, +shrink_k2, _, _, +eig_floor} = cfg
  +lams = C.list_sq(ss)
  # If shrink_mode == 2 (PPCA bulk mean), compute lam_bar from total whitened variance.
  +bulk_sum = fmax((rw_frob_sq - C.list_sum(lams) : F32), 0.0)
  +den_nm = U32.to_f32(U32.max(1, (n - k : U32)))
  +k2_eff = Bool.pick(F32, U32.is_eq(shrink_mode, 2), (bulk_sum / den_nm : F32), shrink_k2)
  +vk = L.transpose(vt)
  stat_s2.with_sh(spiked_shrink_eigenvalues(L.Vec{k, lams}, n, t, shrink_mode, shrink_k1, k2_eff, eig_floor), returns, r_white, sd_vec, vk, L.Vec{k, ss}, cfg)

def stat_s2.run_svd1(use_sub: Bool, r_ws: L.Mat, +fr2: F32, returns: L.Mat, r_white: L.Mat, sd_vec: L.Vec, +t: U32, +n: U32, +k: U32, cfg: StatConfig) -> Maybe<&2, StatModelFit>:
  match use_sub:
    case True{}:
      stat_s2.from_svd(SSVD.svd_top_k(r_ws, k, 8, 4), returns, r_white, sd_vec, t, n, fr2, cfg)
    case False{}:
      stat_s2.from_svd(SSVD.slice_svd(L.svd_thin(r_ws), k), returns, r_white, sd_vec, t, n, fr2, cfg)

def stat_s2.run_svd(use_sub: Bool, +r_ws: L.Mat, returns: L.Mat, r_white: L.Mat, sd_vec: L.Vec, +t: U32, +n: U32, +k: U32, cfg: StatConfig) -> Maybe<&2, StatModelFit>:
  +fr = L.frobenius(r_ws)
  stat_s2.run_svd1(use_sub, r_ws, (fr * fr : F32), returns, r_white, sd_vec, t, n, k, cfg)

def stat_s2.with_rws(mrws: Maybe<&2, L.Mat>, returns: L.Mat, r_white: L.Mat, sd_vec: L.Vec, +t: U32, +n: U32, +cfg: StatConfig) -> Maybe<&2, StatModelFit>:
  match mrws:
    case Some{r_ws}:
      StatConfig{k, _, _, _, _, _, _, _, use_sub, _} = cfg
      stat_s2.run_svd(use_sub, r_ws, returns, r_white, sd_vec, t, n, k, cfg)
    case None{}:
      None{}

def stat_s2.with_rw(mrw: Maybe<&2, L.Mat>, returns: L.Mat, sd_vec: L.Vec, +t: U32, +n: U32, +cfg: StatConfig) -> Maybe<&2, StatModelFit>:
  match mrw:
    case Some{+r_white}:
      StatConfig{_, _, _, hl_slow, _, _, _, _, _, _} = cfg
      stat_s2.with_rws(weight_time_mat(r_white, hl_slow), returns, r_white, sd_vec, t, n, cfg)
    case None{}:
      None{}

def stat_s2.with_s1(msig: Maybe<&2, L.Vec>, +returns: L.Mat, +t: U32, +n: U32, cfg: StatConfig) -> Maybe<&2, StatModelFit>:
  match msig:
    case Some{L.Vec{_, sig2_raw}}:
      +sig2 = C.floor_list(sig2_raw, 1.0e-12)
      stat_s2.with_rw(L.mul_diag(returns, L.Vec{n, C.list_inv_sqrt(sig2)}), returns, L.Vec{n, C.list_sqrt(sig2)}, t, n, cfg)
    case None{}:
      None{}

def stat_s1.with_rf(mrf: Maybe<&2, L.Mat>, returns: L.Mat, +t: U32, +n: U32, +cfg: StatConfig) -> Maybe<&2, StatModelFit>:
  match mrf:
    case Some{r_fast}:
      StatConfig{_, +stage1_p, _, _, _, _, _, _, use_sub, _} = cfg
      +p_eff = U32.min(stage1_p, U32.min(t, n))
      stat_s2.with_s1(stat_s1_run2(U32.is_gt(p_eff, 0), use_sub, r_fast, p_eff), returns, t, n, cfg)
    case None{}:
      None{}

def stat_fit.chk(ok: Bool, +returns: L.Mat, +t: U32, +n: U32, +cfg: StatConfig) -> Maybe<&2, StatModelFit>:
  match ok:
    case True{}:
      StatConfig{_, _, hl_fast, _, _, _, _, _, _, _} = cfg
      stat_s1.with_rf(weight_time_mat(returns, hl_fast), returns, t, n, cfg)
    case False{}:
      None{}

def fit_statistical_model(+returns: L.Mat, +cfg: StatConfig) -> Maybe<&2, StatModelFit>:
  L.Mat{+t, +n, _} = returns
  StatConfig{+k, _, _, _, _, _, _, +shrink_idio, _, +eig_floor} = cfg
  +mn = U32.min(t, n)
  +ok = Bool.and(U32.is_gt(k, 0), Bool.and(U32.is_le(k, mn), Bool.and(F32.is_ge(shrink_idio, 0.0), Bool.and(F32.is_le(shrink_idio, 1.0), F32.is_gt(eig_floor, 0.0)))))
  stat_fit.chk(ok, returns, t, n, cfg)

# §7.5.2 & §7.4.2 Imputation & Interpretation of Statistical Loadings

# Time-series regression of non-estimation-universe asset returns (T x M) against factor returns F (T x K):
# returns imputed loadings B_new (M x K) = (lstsq_mat(F, R_new))^T.
def imp_ts.fin(mb_t: Maybe<&2, L.Mat>) -> Maybe<&2, L.Mat>:
  match mb_t:
    case Some{bt}:
      Some{L.transpose(bt)}
    case None{}:
      None{}

def imp_ts.chk(ok: Bool, asset_returns: L.Mat, factor_returns: L.Mat) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      imp_ts.fin(L.lstsq_mat(factor_returns, asset_returns))
    case False{}:
      None{}

def impute_loadings_ts(+asset_returns: L.Mat, +factor_returns: L.Mat) -> Maybe<&2, L.Mat>:
  L.Mat{+ta, +ma, _} = asset_returns
  L.Mat{+tf, +kf, _} = factor_returns
  +ok = Bool.and(U32.is_eq(ta, tf), Bool.and(U32.is_gt(ma, 0), Bool.and(U32.is_gt(kf, 0), U32.is_ge(tf, kf))))
  imp_ts.chk(ok, asset_returns, factor_returns)

# §7.4.2 Regress statistical loadings B_stat (N x K) on characteristics G (N x P) -> beta (P x K).
def interpret_loadings.chk(ok: Bool, b_stat: L.Mat, characteristics: L.Mat) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      L.lstsq_mat(characteristics, b_stat)
    case False{}:
      None{}

def interpret_loadings(+b_stat: L.Mat, +characteristics: L.Mat) -> Maybe<&2, L.Mat>:
  L.Mat{+nb, +kb, _} = b_stat
  L.Mat{+ng, +pg, _} = characteristics
  +ok = Bool.and(U32.is_eq(nb, ng), Bool.and(U32.is_gt(kb, 0), Bool.and(U32.is_gt(pg, 0), U32.is_ge(ng, pg))))
  interpret_loadings.chk(ok, b_stat, characteristics)

# §7.5.2 Impute missing/IPO asset loadings from industry/country characteristics with shrinkage toward 0:
# beta = lstsq_mat(g_known, b_known), B_new = (1 - shrink) * (g_new * beta).
def imp_char.s2(mpred: Maybe<&2, L.Mat>, +shrink: F32) -> Maybe<&2, L.Mat>:
  match mpred:
    case Some{pred}:
      Some{L.scale((1.0 - shrink : F32), pred)}
    case None{}:
      None{}

def imp_char.s1(mbeta: Maybe<&2, L.Mat>, g_new: L.Mat, +shrink: F32) -> Maybe<&2, L.Mat>:
  match mbeta:
    case Some{beta}:
      imp_char.s2(L.matmul(g_new, beta), shrink)
    case None{}:
      None{}

def imp_char.chk(ok: Bool, b_known: L.Mat, g_known: L.Mat, g_new: L.Mat, +shrink: F32) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      imp_char.s1(L.lstsq_mat(g_known, b_known), g_new, shrink)
    case False{}:
      None{}

def impute_loadings_char(+b_known: L.Mat, +g_known: L.Mat, +g_new: L.Mat, +shrink: F32) -> Maybe<&2, L.Mat>:
  L.Mat{+nb, +kb, _} = b_known
  L.Mat{+ng, +pg, _} = g_known
  L.Mat{+nn, +pn, _} = g_new
  +ok = Bool.and(U32.is_eq(nb, ng), Bool.and(U32.is_eq(pg, pn), Bool.and(U32.is_gt(kb, 0), Bool.and(U32.is_gt(pg, 0), Bool.and(U32.is_ge(ng, pg), Bool.and(U32.is_gt(nn, 0), Bool.and(F32.is_ge(shrink, 0.0), F32.is_le(shrink, 1.0))))))))
  imp_char.chk(ok, b_known, g_known, g_new, shrink)

# ---------------------------------------------------------------- Causal Parallel Rolling Estimators (Ch 6 & Ch 7.5.2)

# Strictly causal window extractor: builds rolling windows of length `window` ending at
# t = window-1, window, ..., T-1. Window j contains ONLY rows [j .. j + window - 1].
# Proved causal in PROOF.bend: the first k windows depend only on the first k + window - 1 rows.
def make_windows(-A: Data, rem: Nat, xs: List<&2, A>, +w: Nat) -> List<&2, List<&2, A>>:
  match rem xs:
    case 0n _:
      Nil{}
    case 1n+p Con{h, +t}:
      list_take(A, w, h <> t) <> make_windows(A, p, t, w)
    case _ Nil{}:
      Nil{}

# Rolling statistical factor models: parallel pmap over causal windows + optional sequential alignment.
# align_mode: 0 = none, 1 = column sign alignment, 2 = orthogonal Procrustes alignment.
type StatWinCtx is Data:
  StatWinCtx{w: U32, n: U32, cfg: StatConfig}

def stat_win_fit.extract(mf: Maybe<&2, StatModelFit>) -> Maybe<&2, P.FactorModel>:
  match mf:
    case Some{StatModelFit{fm, _, _, _}}:
      Some{fm}
    case None{}:
      None{}

def stat_win_fit(ctx: StatWinCtx, win_rows: List<&2, List<&2, F32>>) -> Maybe<&2, P.FactorModel>:
  StatWinCtx{w, n, cfg} = ctx
  stat_win_fit.extract(fit_statistical_model(L.Mat{w, n, win_rows}, cfg))

def align_fm_sign.fin(mb: Maybe<&2, L.Mat>, cov_f: L.Mat, idio_var: L.Vec) -> Maybe<&2, P.FactorModel>:
  match mb:
    case Some{b_al}:
      Some{P.FactorModel{b_al, cov_f, idio_var}}
    case None{}:
      None{}

def align_fm_step1(is_sign: Bool, prev: P.FactorModel, curr: P.FactorModel) -> Maybe<&2, P.FactorModel>:
  match is_sign:
    case True{}:
      P.FactorModel{bp, _, _} = prev
      P.FactorModel{bc, cf, iv} = curr
      align_fm_sign.fin(align_sign(bp, bc), cf, iv)
    case False{}:
      Some{curr}

def align_fm_step2(is_proc: Bool, +align_mode: U32, prev: P.FactorModel, curr: P.FactorModel) -> Maybe<&2, P.FactorModel>:
  match is_proc:
    case True{}:
      align_procrustes(prev, curr)
    case False{}:
      align_fm_step1(U32.is_eq(align_mode, 1), prev, curr)

def align_fm_push(mal: Maybe<&2, P.FactorModel>, prev: P.FactorModel, pt: List<&2, P.FactorModel>) -> Maybe<&2, List<&2, P.FactorModel>>:
  match mal:
    case Some{al}:
      Some{al <> prev <> pt}
    case None{}:
      None{}

def align_fm_one(macc: Maybe<&2, List<&2, P.FactorModel>>, curr: P.FactorModel, +align_mode: U32) -> Maybe<&2, List<&2, P.FactorModel>>:
  match macc:
    case None{}:
      None{}
    case Some{Nil{}}:
      Some{curr <> Nil{}}
    case Some{Con{+prev, pt}}:
      align_fm_push(align_fm_step2(U32.is_eq(align_mode, 2), align_mode, prev, curr), prev, pt)

def align_fm_rev(macc: Maybe<&2, List<&2, P.FactorModel>>) -> Maybe<&2, List<&2, P.FactorModel>>:
  match macc:
    case Some{acc}:
      Some{List.reverse(&2, P.FactorModel, acc)}
    case None{}:
      None{}

def align_fm_all(fms: List<&2, P.FactorModel>, macc: Maybe<&2, List<&2, P.FactorModel>>, +align_mode: U32) -> Maybe<&2, List<&2, P.FactorModel>>:
  match fms:
    case Nil{}:
      align_fm_rev(macc)
    case Con{curr, rt}:
      align_fm_all(rt, align_fm_one(macc, curr, align_mode), align_mode)

def roll_stat.align(mfms: Maybe<&2, List<&2, P.FactorModel>>, +align_mode: U32) -> Maybe<&2, List<&2, P.FactorModel>>:
  match mfms:
    case Some{fms}:
      align_fm_all(fms, Some{Nil{}}, align_mode)
    case None{}:
      None{}

def roll_stat.chk(ok: Bool, rows: List<&2, List<&2, F32>>, +t: U32, +n: U32, +window: U32, cfg: StatConfig, +align_mode: U32) -> Maybe<&2, List<&2, P.FactorModel>>:
  match ok:
    case True{}:
      +cnt = ((t - window) + 1 : U32)
      +wins = make_windows(List<&2, F32>, U32.to_nat(cnt), rows, U32.to_nat(window))
      +mfms = seq_maybe(P.FactorModel, pmap(~List<&2, List<&2, F32>>, ~Maybe<&2, P.FactorModel>, ~StatWinCtx, ~stat_win_fit, wins, cnt, StatWinCtx{window, n, cfg}))
      roll_stat.align(mfms, align_mode)
    case False{}:
      None{}

def rolling_statistical_models(returns: L.Mat, +window: U32, cfg: StatConfig, +align_mode: U32) -> Maybe<&2, List<&2, P.FactorModel>>:
  L.Mat{+t, +n, rows} = returns
  +ok = Bool.and(U32.is_gt(window, 0), Bool.and(U32.is_ge(t, window), U32.is_gt(n, 0)))
  roll_stat.chk(ok, rows, t, n, window, cfg, align_mode)

def oos_drop(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def oos_returns.chk(ok: Bool, +t: U32, +n: U32, rows: List<&2, List<&2, F32>>, +window: U32) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      Some{L.Mat{((t - window) + 1 : U32), n, list_drop(List<&2, F32>, oos_drop(U32.to_nat(window)), rows)}}
    case False{}:
      None{}

# The return rows that line up with rolling_statistical_models(returns, window, ...):
# drops the first window - 1 rows, so qdist / mahalanobis_test / mvp_test pair
# model j (fit on rows j .. j + window - 1) with row j + window. Proved in PROOF.bend.
def oos_returns(returns: L.Mat, +window: U32) -> Maybe<&2, L.Mat>:
  L.Mat{+t, +n, rows} = returns
  oos_returns.chk(Bool.and(U32.is_gt(window, 0), U32.is_ge(t, window)), t, n, rows, window)

# Rolling fundamental factor models: parallel pmap over strictly causal windows [j .. j + window - 1].
type FundWin is Data:
  FundWin{r_rows: List<&2, List<&2, F32>>, bs: List<&2, L.Mat>}

type FundWinCtx is Data:
  FundWinCtx{w: U32, n: U32, opt_cons: Maybe<&2, CSConstraint>, cfg: FundConfig}

def zip_fund_wins(rwins: List<&2, List<&2, List<&2, F32>>>, bwins: List<&2, List<&2, L.Mat>>) -> List<&2, FundWin>:
  match rwins bwins:
    case Con{rw, rt} Con{bw, bt}:
      FundWin{rw, bw} <> zip_fund_wins(rt, bt)
    case _ _:
      Nil{}

def fund_win_fit.extract(mf: Maybe<&2, FundModelFit>) -> Maybe<&2, P.FactorModel>:
  match mf:
    case Some{FundModelFit{fm, _, _}}:
      Some{fm}
    case None{}:
      None{}

def fund_win_fit(ctx: FundWinCtx, win: FundWin) -> Maybe<&2, P.FactorModel>:
  FundWinCtx{w, n, opt_cons, cfg} = ctx
  FundWin{r_rows, bs} = win
  fund_win_fit.extract(fit_fundamental_model(L.Mat{w, n, r_rows}, bs, opt_cons, cfg))

def roll_fund.chk(ok: Bool, rows: List<&2, List<&2, F32>>, bs_list: List<&2, L.Mat>, +t: U32, +n: U32, +window: U32, opt_cons: Maybe<&2, CSConstraint>, cfg: FundConfig) -> Maybe<&2, List<&2, P.FactorModel>>:
  match ok:
    case True{}:
      +cnt = ((t - window) + 1 : U32)
      +rwins = make_windows(List<&2, F32>, U32.to_nat(cnt), rows, U32.to_nat(window))
      +bwins = make_windows(L.Mat, U32.to_nat(cnt), bs_list, U32.to_nat(window))
      +wins = zip_fund_wins(rwins, bwins)
      seq_maybe(P.FactorModel, pmap(~FundWin, ~Maybe<&2, P.FactorModel>, ~FundWinCtx, ~fund_win_fit, wins, cnt, FundWinCtx{window, n, opt_cons, cfg}))
    case False{}:
      None{}

def rolling_fundamental_models(returns: L.Mat, +bs_list: List<&2, L.Mat>, +window: U32, opt_cons: Maybe<&2, CSConstraint>, cfg: FundConfig) -> Maybe<&2, List<&2, P.FactorModel>>:
  L.Mat{+t, +n, rows} = returns
  +nb = U32.from_nat(List.length(&2, L.Mat, bs_list))
  +ok = Bool.and(U32.is_eq(nb, t), Bool.and(U32.is_gt(window, 0), Bool.and(U32.is_ge(t, window), U32.is_gt(n, 0))))
  roll_fund.chk(ok, rows, bs_list, t, n, window, opt_cons, cfg)
