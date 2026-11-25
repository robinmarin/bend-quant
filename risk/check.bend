# CLI numerical verification driver for bend-quant-risk (Chapters 4-7).
# Invoked by check.py to cross-check every public function against
# NumPy, SciPy, scikit-learn, and statsmodels.
import Base
import bend-quant-linalg@0.1.0.0/linalg.bend as L
import bend-quant-linalg@0.1.0.0/io.bend as LI
import bend-quant-portfolio@0.1.0.0/portfolio.bend as P
import ./risk.bend as R
import ./io.bend as RI

def num(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{n}:
      n
    case None{}:
      0

def tu(s: String) -> U32:
  num(U32.read(s))

def show_list_f32(xs: List<&2, F32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, Nil{}}:
      F32.show(h)
    case Con{h, t}:
      F32.show(h) ++ " " ++ show_list_f32(t)

def show_vec(v: L.Vec) -> String:
  L.Vec{n, xs} = v
  "VEC " ++ U32.show(n) ++ "\n" ++ show_list_f32(xs) ++ "\n"

def show_rows(rs: List<&2, List<&2, F32>>) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{r, t}:
      show_list_f32(r) ++ "\n" ++ show_rows(t)

def show_mat(a: L.Mat) -> String:
  L.Mat{m, n, rs} = a
  "MAT " ++ U32.show(m) ++ " " ++ U32.show(n) ++ "\n" ++ show_rows(rs)

def show_fm(fm: P.FactorModel) -> String:
  P.FactorModel{b, cf, d} = fm
  "FM\n" ++ show_mat(b) ++ show_mat(cf) ++ show_vec(d)

def show_mfm(mfm: Maybe<&2, P.FactorModel>) -> String:
  match mfm:
    case Some{fm}:
      show_fm(fm)
    case None{}:
      "NONE\n"

def show_mvec(mv: Maybe<&2, L.Vec>) -> String:
  match mv:
    case Some{v}:
      show_vec(v)
    case None{}:
      "NONE\n"

def show_mmat(mm: Maybe<&2, L.Mat>) -> String:
  match mm:
    case Some{a}:
      show_mat(a)
    case None{}:
      "NONE\n"

def show_mf32(mx: Maybe<&2, F32>) -> String:
  match mx:
    case Some{x}:
      "F32 " ++ F32.show(x) ++ "\n"
    case None{}:
      "NONE\n"

def show_mu32(mx: Maybe<&2, U32>) -> String:
  match mx:
    case Some{x}:
      "U32 " ++ U32.show(x) ++ "\n"
    case None{}:
      "NONE\n"

def show_group_risk(mg: Maybe<&2, R.GroupRisk>) -> String:
  match mg:
    case Some{R.GroupRisk{gc, gv, gs, gm, tv, tvol}}:
      "GRISK " ++ F32.show(tv) ++ " " ++ F32.show(tvol) ++ "\n" ++ show_mat(gc) ++ show_vec(gv) ++ show_vec(gs) ++ show_vec(gm)
    case None{}:
      "NONE\n"

def show_qdist(mq: Maybe<&2, R.QDistResult>) -> String:
  match mq:
    case Some{R.QDistResult{mn, tot, pp}}:
      "QDIST " ++ F32.show(mn) ++ " " ++ F32.show(tot) ++ "\n" ++ show_vec(pp)
    case None{}:
      "NONE\n"

def show_mahal(mm: Maybe<&2, R.MahalanobisResult>) -> String:
  match mm:
    case Some{R.MahalanobisResult{nu, mn, mv}}:
      "MAHAL " ++ F32.show(mn) ++ " " ++ F32.show(mv) ++ "\n" ++ show_vec(nu)
    case None{}:
      "NONE\n"

def show_mvp(mm: Maybe<&2, R.MvpResult>) -> String:
  match mm:
    case Some{R.MvpResult{rv, rvol, mpv, ql, vm, bs, rets, pvs}}:
      "MVP " ++ F32.show(rv) ++ " " ++ F32.show(rvol) ++ " " ++ F32.show(mpv) ++ " " ++ F32.show(ql) ++ " " ++ F32.show(vm) ++ " " ++ F32.show(bs) ++ "\n" ++ show_vec(rets) ++ show_vec(pvs)
    case None{}:
      "NONE\n"

def show_voleval(mv: Maybe<&2, R.VolEval>) -> String:
  match mv:
    case Some{R.VolEval{ql, vm, bs, rv, mpv, cnt}}:
      "VOLEVAL " ++ F32.show(ql) ++ " " ++ F32.show(vm) ++ " " ++ F32.show(bs) ++ " " ++ F32.show(rv) ++ " " ++ F32.show(mpv) ++ " " ++ U32.show(cnt) ++ "\n"
    case None{}:
      "NONE\n"

def show_turnover(mt: Maybe<&2, R.TurnoverResult>) -> String:
  match mt:
    case Some{R.TurnoverResult{mn, pp}}:
      "TURN " ++ F32.show(mn) ++ "\n" ++ show_vec(pp)
    case None{}:
      "NONE\n"

def show_betaerr(mb: Maybe<&2, R.BetaErrResult>) -> String:
  match mb:
    case Some{R.BetaErrResult{tot, mn, pp}}:
      "BERR " ++ F32.show(tot) ++ " " ++ F32.show(mn) ++ "\n" ++ show_vec(pp)
    case None{}:
      "NONE\n"

def show_shrink(ms: Maybe<&2, R.ShrinkResult>) -> String:
  match ms:
    case Some{R.ShrinkResult{cov, sh, td}}:
      "SHRINK " ++ F32.show(sh) ++ " " ++ F32.show(td) ++ "\n" ++ show_mat(cov)
    case None{}:
      "NONE\n"

def show_pairs.go(ps: List<&2, R.CorrPair>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{R.CorrPair{i, j, c}, t}:
      U32.show(i) ++ " " ++ U32.show(j) ++ " " ++ F32.show(c) ++ "\n" ++ show_pairs.go(t)

def show_pairs(mp: Maybe<&2, List<&2, R.CorrPair>>) -> String:
  match mp:
    case Some{+ps}:
      "PAIRS " ++ U32.show(U32.from_nat(List.length(&2, R.CorrPair, ps))) ++ "\n" ++ show_pairs.go(ps)
    case None{}:
      "NONE\n"

def show_rebase(mr: Maybe<&2, R.RebaseResult>) -> String:
  match mr:
    case Some{R.RebaseResult{cl, cc}}:
      "REBASE\n" ++ show_mat(cl) ++ show_mat(cc)
    case None{}:
      "NONE\n"

def show_csreg(mc: Maybe<&2, R.CSRegResult>) -> String:
  match mc:
    case Some{R.CSRegResult{fr, res, ec}}:
      "CSREG\n" ++ show_vec(fr) ++ show_vec(res) ++ show_mat(ec)
    case None{}:
      "NONE\n"

def show_fseries(mf: Maybe<&2, R.FactorSeries>) -> String:
  match mf:
    case Some{R.FactorSeries{fr, res}}:
      "FSER\n" ++ show_mat(fr) ++ show_mat(res)
    case None{}:
      "NONE\n"

def show_fundfit(mf: Maybe<&2, R.FundModelFit>) -> String:
  match mf:
    case Some{R.FundModelFit{fm, fr, res}}:
      "FUNDFIT\n" ++ show_fm(fm) ++ show_mat(fr) ++ show_mat(res)
    case None{}:
      "NONE\n"

def show_fms.go(fms: List<&2, P.FactorModel>) -> String:
  match fms:
    case Nil{}:
      ""
    case Con{fm, t}:
      show_fm(fm) ++ show_fms.go(t)

def show_mfms(mfms: Maybe<&2, List<&2, P.FactorModel>>) -> String:
  match mfms:
    case Some{+fms}:
      "FMS " ++ U32.show(U32.from_nat(List.length(&2, P.FactorModel, fms))) ++ "\n" ++ show_fms.go(fms)
    case None{}:
      "NONE\n"

def show_pca(mp: Maybe<&2, R.PcaResult>) -> String:
  match mp:
    case Some{R.PcaResult{ld, fr, sv, ev}}:
      "PCA\n" ++ show_mat(ld) ++ show_mat(fr) ++ show_vec(sv) ++ show_vec(ev)
    case None{}:
      "NONE\n"

def show_baing(mb: Maybe<&2, R.BaiNgResult>) -> String:
  match mb:
    case Some{R.BaiNgResult{ki, kp, iv, pv}}:
      "BAING " ++ U32.show(ki) ++ " " ++ U32.show(kp) ++ "\n" ++ show_vec(iv) ++ show_vec(pv)
    case None{}:
      "NONE\n"

def show_eigto(me: Maybe<&2, R.EigenTurnover>) -> String:
  match me:
    case Some{R.EigenTurnover{pf, mn}}:
      "EIGTO " ++ F32.show(mn) ++ "\n" ++ show_vec(pf)
    case None{}:
      "NONE\n"

def show_statfit(ms: Maybe<&2, R.StatModelFit>) -> String:
  match ms:
    case Some{R.StatModelFit{fm, fr, res, sv}}:
      "STATFIT\n" ++ show_fm(fm) ++ show_mat(fr) ++ show_mat(res) ++ show_vec(sv)
    case None{}:
      "NONE\n"

# ---- Helper: unpack packed matrices into FactorModels / Vec lists ----

def rows_to_vecs(rows: List<&2, List<&2, F32>>, +n: U32) -> List<&2, L.Vec>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      L.Vec{n, r} <> rows_to_vecs(t, n)

def zip_fms(bs: List<&2, L.Mat>, cfs: List<&2, L.Mat>, ds: List<&2, L.Vec>) -> List<&2, P.FactorModel>:
  match bs cfs ds:
    case Con{b, bt} Con{cf, cft} Con{d, dt}:
      P.FactorModel{b, cf, d} <> zip_fms(bt, cft, dt)
    case _ _ _:
      Nil{}

def nth_f32(xs: List<&2, F32>, idx: Nat) -> F32:
  match xs idx:
    case Con{h, _} 0n:
      h
    case Con{_, t} 1n+p:
      nth_f32(t, p)
    case _ _:
      0.0

def mk_fm(b: L.Mat, cf: L.Mat, d: L.Vec) -> P.FactorModel:
  P.FactorModel{b, cf, d}

def mk_u32_pair(a: U32, b: U32) -> List<&2, U32>:
  a <> (b <> Nil{})

def mk_grps3() -> List<&2, List<&2, U32>>:
  mk_u32_pair(0, 1) <> (mk_u32_pair(2, 3) <> (mk_u32_pair(4, 5) <> Nil{}))

def mk_mat2(a: L.Mat, b: L.Mat) -> List<&2, L.Mat>:
  a <> (b <> Nil{})

def mk_cons(c: L.Mat, d: L.Vec) -> R.CSConstraint:
  R.CSConstraint{c, d}

def mk_fcfg(hv: F32, hc: F32, hi: F32, nw: U32, sf: F32, si: F32, hs: F32, stvu: Bool, db: Bool, fl: F32) -> R.FundConfig:
  R.FundConfig{hv, hc, hi, nw, sf, si, hs, stvu, db, fl}

def mk_scfg(k: U32, p: U32, hf: F32, hs: F32, sm: U32, k1: F32, k2: F32, si: F32, sub: Bool, fl: F32) -> R.StatConfig:
  R.StatConfig{k, p, hf, hs, sm, k1, k2, si, sub, fl}

def mk_v2() -> L.Vec:
  L.Vec{2, 1.0 <> (2.0 <> Nil{})}

def mk_v3() -> L.Vec:
  L.Vec{3, 1.0 <> (2.0 <> (3.0 <> Nil{}))}

def mk_m22() -> L.Mat:
  L.Mat{2, 2, (1.0 <> (0.0 <> Nil{})) <> ((0.0 <> (1.0 <> Nil{})) <> Nil{})}

def mk_m23() -> L.Mat:
  L.Mat{2, 3, (1.0 <> (0.0 <> (0.0 <> Nil{}))) <> ((0.0 <> (1.0 <> (0.0 <> Nil{}))) <> Nil{})}

# ---- Mode 0: Chapter 4 (Transformations & Group Risk) ----

def run_ch4.go(+b: L.Mat, +cf: L.Mat, +d: L.Vec, cmat: L.Mat, +amat: L.Mat, cg: L.Mat, dnew: L.Vec, avec: L.Vec, sh: L.Vec, sc: L.Vec, w: L.Vec) -> String:
  +fm = mk_fm(b, cf, d)
  s0 = show_mfm(R.rotate_model(fm, cmat))
  s1 = show_mfm(R.rotate_identity_cov(fm))
  s2 = show_mfm(R.rotate_orthonormal_loadings(fm))
  s3 = show_mfm(R.rotate_zscore_loadings(fm, avec, sh, sc))
  s4 = show_mfm(R.project_model(fm, amat))
  s5 = show_mmat(R.pushout_loadings(b, amat, d))
  s6 = show_mfm(R.pushout_model(fm, amat, cg, dnew))
  s7 = show_group_risk(R.group_risk_decomp(fm, w, mk_grps3()))
  s0 ++ s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6 ++ s7

def run_ch4(rb: Result<&1, &1, U32 & String, L.Mat>, rcf: Result<&1, &1, U32 & String, L.Mat>, rd: Result<&1, &1, U32 & String, L.Vec>, rc: Result<&1, &1, U32 & String, L.Mat>, ra: Result<&1, &1, U32 & String, L.Mat>, rcg: Result<&1, &1, U32 & String, L.Mat>, rdn: Result<&1, &1, U32 & String, L.Vec>, rav: Result<&1, &1, U32 & String, L.Vec>, rsh: Result<&1, &1, U32 & String, L.Vec>, rsc: Result<&1, &1, U32 & String, L.Vec>, rw: Result<&1, &1, U32 & String, L.Vec>) -> String:
  match rb rcf rd rc ra rcg rdn rav rsh rsc rw:
    case Done{b} Done{cf} Done{d} Done{c} Done{a} Done{cg} Done{dn} Done{av} Done{sh} Done{sc} Done{w}:
      run_ch4.go(b, cf, d, c, a, cg, dn, av, sh, sc, w)
    case _ _ _ _ _ _ _ _ _ _ _:
      "LOAD_FAIL\n"

# ---- Mode 1: Chapter 5 (Risk Evaluation) ----

def run_ch5.go(+vhat: L.Vec, +r1d: L.Vec, +bs: List<&2, L.Mat>, cfs: List<&2, L.Mat>, dmat: L.Mat, +rets: L.Mat, ws: L.Mat, bvec: L.Vec, wref: L.Vec, ps: L.Vec) -> String:
  L.Mat{_, n, drows} = dmat
  L.Vec{_, pxs} = ps
  +hl_b = nth_f32(pxs, 0n)
  +ds = rows_to_vecs(drows, n)
  +fms = zip_fms(bs, cfs, ds)
  s0 = show_mf32(R.qlike(vhat, r1d))
  s1 = show_mf32(R.vol_mse(vhat, r1d))
  s2 = show_mf32(R.bias_stat(vhat, r1d))
  s3 = show_qdist(R.qdist(fms, rets))
  s4 = show_mahal(R.mahalanobis_test(fms, rets))
  s5 = show_mvp(R.mvp_test(fms, rets, bvec))
  s6 = show_voleval(R.portfolio_vol_eval(fms, ws, rets))
  s7 = show_turnover(R.fmp_turnover(fms))
  s8 = show_betaerr(R.beta_error(fms, rets, wref, hl_b))
  s9 = show_mf32(R.cross_sectional_r2(bs, rets, ds))
  s0 ++ s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6 ++ s7 ++ s8 ++ s9

def run_ch5(rv: Result<&1, &1, U32 & String, L.Vec>, rr1: Result<&1, &1, U32 & String, L.Vec>, rbs: Result<&1, &1, U32 & String, List<&2, L.Mat>>, rcfs: Result<&1, &1, U32 & String, List<&2, L.Mat>>, rdm: Result<&1, &1, U32 & String, L.Mat>, rrets: Result<&1, &1, U32 & String, L.Mat>, rws: Result<&1, &1, U32 & String, L.Mat>, rbv: Result<&1, &1, U32 & String, L.Vec>, rwr: Result<&1, &1, U32 & String, L.Vec>, rps: Result<&1, &1, U32 & String, L.Vec>) -> String:
  match rv rr1 rbs rcfs rdm rrets rws rbv rwr rps:
    case Done{v} Done{r1} Done{bs} Done{cfs} Done{dm} Done{rets} Done{ws} Done{bv} Done{wr} Done{ps}:
      run_ch5.go(v, r1, bs, cfs, dm, rets, ws, bv, wr, ps)
    case _ _ _ _ _ _ _ _ _ _:
      "LOAD_FAIL\n"

# ---- Mode 2: Chapter 6a (Covariance, STVU, HAC, Idio, Winsorize, Linking, Rebasing) ----

def run_ch6a.with_cov(ms: Maybe<&2, L.Mat>, +f: L.Mat, +b: L.Mat, +d: L.Vec, +hl_fast: F32, +rho: F32, +eig_fl: F32) -> String:
  match ms:
    case None{}:
      "NONE\nNONE\nNONE\nNONE\nNONE\n"
    case Some{+cov}:
      s0 = show_mmat(R.shrink_to_identity(cov, rho))
      s1 = show_mmat(R.debias_factor_cov(cov, b, d, eig_fl))
      s2 = show_mf32(R.stvu_factor_multiplier(f, cov, hl_fast, False{}))
      s3 = show_mf32(R.stvu_factor_multiplier(f, cov, hl_fast, True{}))
      s4 = show_mmat(R.stvu_adjust_cov(f, cov, hl_fast, False{}))
      s0 ++ s1 ++ s2 ++ s3 ++ s4

def run_ch6a.go(+f: L.Mat, +eps: L.Mat, +b: L.Mat, +d: L.Vec, evw: L.Mat, indef: L.Mat, loc0: L.Mat, loc1: L.Mat, joint: L.Mat, cmat: L.Mat, covc: L.Mat, ps: L.Vec, +t: U32, +n: U32, +l_max: U32, +win: U32, +target_idx: U32) -> String:
  L.Vec{_, +pxs} = ps
  +hl_vol = nth_f32(pxs, 0n)
  +hl_corr = nth_f32(pxs, 1n)
  +hl_fast = nth_f32(pxs, 2n)
  +rho = nth_f32(pxs, 3n)
  +eig_fl = nth_f32(pxs, 4n)
  +k_cai = nth_f32(pxs, 5n)
  +thr_cl = nth_f32(pxs, 6n)
  +d_max = nth_f32(pxs, 7n)
  +rho_lk = nth_f32(pxs, 8n)
  +mcov_c = R.sample_cov(f, True{})
  locs = mk_mat2(loc0, loc1)
  s0 = show_mvec(R.ewma_weights(t, hl_vol))
  s1 = show_mmat(mcov_c)
  s2 = show_mmat(R.sample_cov(f, False{}))
  s3 = show_mmat(R.ewma_cov(f, hl_vol, True{}))
  s4 = show_mmat(R.ewma_cov(f, hl_vol, False{}))
  s5 = run_ch6a.with_cov(mcov_c, f, b, d, hl_fast, rho, eig_fl)
  s6 = show_shrink(R.ledoit_wolf_cov(f, True{}))
  s7 = show_shrink(R.ledoit_wolf_cov(f, False{}))
  s8 = show_mmat(R.psd_project(indef, eig_fl))
  s9 = show_mmat(R.dcc_cov(f, hl_vol, hl_corr))
  s10 = show_mmat(R.cov_newey_west(f, l_max, 0.0))
  s11 = show_mmat(R.cov_newey_west(f, l_max, hl_vol))
  s12 = show_mmat(R.cov_autocorr_cohen(f, l_max, 0.0))
  s13 = show_mmat(R.cov_autocorr_cohen(f, l_max, hl_vol))
  s14 = show_mvec(R.idio_var_ewma(eps, hl_vol))
  s15 = show_mvec(R.idio_var_shrink(d, rho))
  s16 = show_mvec(R.idio_stvu(eps, d, evw, hl_fast))
  s17 = show_mf32(R.cai_threshold(n, t, k_cai))
  s18 = show_pairs(R.idio_corr_clusters(eps, thr_cl))
  s19 = show_mmat(R.winsorize_log_mad(eps, win, d_max))
  s20 = show_mmat(R.link_models_ir(locs, joint, rho_lk))
  s21 = show_rebase(R.rebase_currency(cmat, covc, target_idx))
  s0 ++ s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6 ++ s7 ++ s8 ++ s9 ++ s10 ++ s11 ++ s12 ++ s13 ++ s14 ++ s15 ++ s16 ++ s17 ++ s18 ++ s19 ++ s20 ++ s21

def run_ch6a(rf: Result<&1, &1, U32 & String, L.Mat>, reps: Result<&1, &1, U32 & String, L.Mat>, rb: Result<&1, &1, U32 & String, L.Mat>, rd: Result<&1, &1, U32 & String, L.Vec>, revw: Result<&1, &1, U32 & String, L.Mat>, rind: Result<&1, &1, U32 & String, L.Mat>, rl0: Result<&1, &1, U32 & String, L.Mat>, rl1: Result<&1, &1, U32 & String, L.Mat>, rj: Result<&1, &1, U32 & String, L.Mat>, rcm: Result<&1, &1, U32 & String, L.Mat>, rcc: Result<&1, &1, U32 & String, L.Mat>, rps: Result<&1, &1, U32 & String, L.Vec>, +t: U32, +n: U32, +l_max: U32, +win: U32, +tidx: U32) -> String:
  match rf reps rb rd revw rind rl0 rl1 rj rcm rcc rps:
    case Done{f} Done{eps} Done{b} Done{d} Done{evw} Done{ind} Done{l0} Done{l1} Done{j} Done{cm} Done{cc} Done{ps}:
      run_ch6a.go(f, eps, b, d, evw, ind, l0, l1, j, cm, cc, ps, t, n, l_max, win, tidx)
    case _ _ _ _ _ _ _ _ _ _ _ _:
      "LOAD_FAIL\n"

# ---- Mode 3: Chapter 6b (Cross-Sectional Regressions & Fundamental Model) ----

def run_ch6b.go(+b: L.Mat, +r: L.Vec, +w: L.Vec, +brd: L.Mat, ccon: L.Mat, dcon: L.Vec, +bs: List<&2, L.Mat>, +rets: L.Mat, wmat: L.Mat, ps: L.Vec, +win: U32) -> String:
  L.Mat{_, n, wrows} = wmat
  L.Vec{_, +pxs} = ps
  +delta = nth_f32(pxs, 0n)
  +tol_rl = nth_f32(pxs, 1n)
  ws = rows_to_vecs(wrows, n)
  cons = mk_cons(ccon, dcon)
  cfg0 = mk_fcfg(20.0, 40.0, 20.0, 2, 0.1, 0.15, 10.0, True{}, True{}, 1.0e-8)
  cfg1 = mk_fcfg(20.0, 20.0, 20.0, 0, 0.0, 0.0, 10.0, False{}, False{}, 1.0e-8)
  s0 = show_csreg(R.cross_sectional_wls(b, r, w))
  s1 = show_csreg(R.cross_sectional_constrained(brd, r, w, cons))
  s2 = show_csreg(R.cross_sectional_ridge(b, r, w, delta))
  s3 = show_csreg(R.cross_sectional_ridgeless(brd, r, w, tol_rl))
  s4 = show_fseries(R.estimate_factor_series(bs, rets, ws, None{}))
  s5 = show_fundfit(R.fit_fundamental_model(rets, bs, None{}, cfg0))
  s6 = show_mfms(R.rolling_fundamental_models(rets, bs, win, None{}, cfg1))
  s0 ++ s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6

def run_ch6b(rb: Result<&1, &1, U32 & String, L.Mat>, rr: Result<&1, &1, U32 & String, L.Vec>, rw: Result<&1, &1, U32 & String, L.Vec>, rbrd: Result<&1, &1, U32 & String, L.Mat>, rcc: Result<&1, &1, U32 & String, L.Mat>, rdc: Result<&1, &1, U32 & String, L.Vec>, rbs: Result<&1, &1, U32 & String, List<&2, L.Mat>>, rrets: Result<&1, &1, U32 & String, L.Mat>, rwm: Result<&1, &1, U32 & String, L.Mat>, rps: Result<&1, &1, U32 & String, L.Vec>, +win: U32) -> String:
  match rb rr rw rbrd rcc rdc rbs rrets rwm rps:
    case Done{b} Done{r} Done{w} Done{brd} Done{cc} Done{dc} Done{bs} Done{rets} Done{wm} Done{ps}:
      run_ch6b.go(b, r, w, brd, cc, dc, bs, rets, wm, ps, win)
    case _ _ _ _ _ _ _ _ _ _:
      "LOAD_FAIL\n"

# ---- Mode 4: Chapter 7 (Statistical Factor Models, PCA, RMT, Alignment, Imputation) ----

def run_ch7.rmt(mp: Maybe<&2, R.PcaResult>, +n: U32, +t: U32, +kmax: U32) -> String:
  match mp:
    case None{}:
      "NONE\nNONE\nNONE\nNONE\nNONE\nNONE\nNONE\nNONE\n"
    case Some{R.PcaResult{_, _, sv, +ev}}:
      s0 = show_mvec(R.spiked_shrink_eigenvalues(ev, n, t, 0, 1.0, 0.0, 1.0e-8))
      s1 = show_mvec(R.spiked_shrink_eigenvalues(ev, n, t, 1, 1.0, 0.0, 1.0e-8))
      s2 = show_mvec(R.spiked_shrink_eigenvalues(ev, n, t, 2, 1.0, 0.0, 1.0e-8))
      s3 = show_mvec(R.spiked_shrink_eigenvalues(ev, n, t, 3, 0.9, 1.0e-5, 1.0e-8))
      s4 = show_mu32(R.select_k_threshold(ev, n, t, 1.0))
      s5 = show_mu32(R.select_k_gap(ev, kmax, False{}))
      s6 = show_mu32(R.select_k_gap(ev, kmax, True{}))
      s7 = show_baing(R.select_k_bai_ng(sv, n, t, kmax))
      s0 ++ s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6 ++ s7

def run_ch7.imp(ms: Maybe<&2, R.StatModelFit>, a_new: L.Mat, +g_known: L.Mat, g_new: L.Mat) -> String:
  match ms:
    case None{}:
      "NONE\nNONE\nNONE\n"
    case Some{R.StatModelFit{P.FactorModel{+bs, _, _}, fr, _, _}}:
      s0 = show_mmat(R.impute_loadings_ts(a_new, fr))
      s1 = show_mmat(R.interpret_loadings(bs, g_known))
      s2 = show_mmat(R.impute_loadings_char(bs, g_known, g_new, 0.05))
      s0 ++ s1 ++ s2

# qdist of the rolling models against the matching out-of-sample rows.
def run_ch7.oos(mfms: Maybe<&2, List<&2, P.FactorModel>>, mret: Maybe<&2, L.Mat>) -> String:
  match mfms mret:
    case Some{fms} Some{r}:
      show_qdist(R.qdist(fms, r))
    case _ _:
      "NONE\n"

def run_ch7.go(+rets: L.Mat, +rets_big: L.Mat, +bp: L.Mat, +bc: L.Mat, cfp: L.Mat, cfc: L.Mat, dp: L.Vec, dc: L.Vec, a_new: L.Mat, g_known: L.Mat, g_new: L.Mat, +t: U32, +n: U32, +k: U32, +kb: U32, +win: U32) -> String:
  +mp_full = R.pca_svd(rets, n, 0.0, False{})
  cfg0 = mk_scfg(k, 0, 20.0, 40.0, 1, 1.0, 0.0, 0.1, False{}, 1.0e-8)
  cfg1 = mk_scfg(k, 3, 20.0, 40.0, 2, 1.0, 0.0, 0.1, False{}, 1.0e-8)
  +cfg_roll = mk_scfg(k, 0, 0.0, 0.0, 0, 1.0, 0.0, 0.0, False{}, 1.0e-8)
  +ms0 = R.fit_statistical_model(rets, cfg0)
  s0 = show_pca(R.pca_svd(rets, k, 0.0, False{}))
  s1 = show_pca(R.pca_svd(rets, k, 25.0, False{}))
  s2 = show_pca(R.pca_svd(rets_big, kb, 0.0, False{}))
  s3 = show_pca(R.pca_svd(rets_big, kb, 0.0, True{}))
  s4 = show_mfm(R.ppca_fit(rets, k, 1.0e-8))
  s5 = run_ch7.rmt(mp_full, n, t, 8)
  s6 = show_eigto(R.eigenfactor_turnover(bp, bc))
  s7 = show_mmat(R.align_sign(bp, bc))
  s8 = show_mfm(R.align_procrustes(P.FactorModel{bp, cfp, dp}, P.FactorModel{bc, cfc, dc}))
  s9 = show_mf32(R.subspace_distance(bp, bc))
  s10 = show_statfit(ms0)
  s11 = show_statfit(R.fit_statistical_model(rets, cfg1))
  s12 = run_ch7.imp(ms0, a_new, g_known, g_new)
  s13 = show_mfms(R.rolling_statistical_models(rets, win, cfg_roll, 1))
  s14 = show_mfms(R.rolling_statistical_models(rets, win, cfg_roll, 2))
  +roll0 = R.rolling_statistical_models(rets, win, cfg_roll, 0)
  s15 = show_mfms(roll0) ++ run_ch7.oos(roll0, R.oos_returns(rets, win))
  s0 ++ s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6 ++ s7 ++ s8 ++ s9 ++ s10 ++ s11 ++ s12 ++ s13 ++ s14 ++ s15

def run_ch7(rr: Result<&1, &1, U32 & String, L.Mat>, rrb: Result<&1, &1, U32 & String, L.Mat>, rbp: Result<&1, &1, U32 & String, L.Mat>, rbc: Result<&1, &1, U32 & String, L.Mat>, rcfp: Result<&1, &1, U32 & String, L.Mat>, rcfc: Result<&1, &1, U32 & String, L.Mat>, rdp: Result<&1, &1, U32 & String, L.Vec>, rdc: Result<&1, &1, U32 & String, L.Vec>, ran: Result<&1, &1, U32 & String, L.Mat>, rgk: Result<&1, &1, U32 & String, L.Mat>, rgn: Result<&1, &1, U32 & String, L.Mat>, +t: U32, +n: U32, +k: U32, +kb: U32, +win: U32) -> String:
  match rr rrb rbp rbc rcfp rcfc rdp rdc ran rgk rgn:
    case Done{r} Done{rb} Done{bp} Done{bc} Done{cfp} Done{cfc} Done{dp} Done{dc} Done{an} Done{gk} Done{gn}:
      run_ch7.go(r, rb, bp, bc, cfp, cfc, dp, dc, an, gk, gn, t, n, k, kb, win)
    case _ _ _ _ _ _ _ _ _ _ _:
      "LOAD_FAIL\n"

# ---- Mode 5: Edge-case / mismatch None{} checks ----

def run_edge() -> String:
  +v2 = mk_v2()
  +v3 = mk_v3()
  +m22 = mk_m22()
  +m23 = mk_m23()
  +fm22 = mk_fm(m22, m22, v2)
  s0 = show_mf32(R.qlike(v2, v3))
  s1 = show_mf32(R.vol_mse(v2, v3))
  s2 = show_mf32(R.bias_stat(v2, v3))
  s3 = show_mmat(R.symmetrize(m23))
  s4 = show_mfm(R.rotate_model(fm22, m23))
  s5 = show_qdist(R.qdist(Nil{}, m22))
  s6 = show_csreg(R.cross_sectional_wls(m22, v3, v2))
  s7 = show_pca(R.pca_svd(m22, 0, 0.0, False{}))
  s8 = show_mfms(R.rolling_statistical_models(m22, 0, R.StatConfig.default(1), 0))
  s9 = show_rebase(R.rebase_currency(m23, m22, 0))
  s0 ++ s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6 ++ s7 ++ s8 ++ s9

# ---- CLI dispatch ----

def go_ch4(args: List<String>) -> IO(Unit):
  match args:
    case bp <> cfp <> dp <> cp <> ap <> cgp <> dnp <> avp <> shp <> scp <> wp <> ns <> ks <> ps <> _:
      +n = tu(ns)
      +k = tu(ks)
      +p = tu(ps)
      do IO<Unit>:
        rb : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(bp, n, k)
        rcf : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(cfp, k, k)
        rd : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(dp, n)
        rc : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(cp, k, k)
        ra : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(ap, n, p)
        rcg : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(cgp, p, p)
        rdn : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(dnp, n)
        rav : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(avp, k)
        rsh : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(shp, k)
        rsc : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(scp, k)
        rw : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(wp, n)
        IO.print(run_ch4(rb, rcf, rd, rc, ra, rcg, rdn, rav, rsh, rsc, rw))
    case _:
      IO.print("BAD_ARGS_0\n")

def go_ch5(args: List<String>) -> IO(Unit):
  match args:
    case vp <> r1p <> bsp <> cfsp <> dsp <> retsp <> wsp <> bvp <> wrp <> psp <> ts <> ns <> ks <> _:
      +t = tu(ts)
      +n = tu(ns)
      +k = tu(ks)
      do IO<Unit>:
        rv : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(vp, t)
        rr1 : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(r1p, t)
        rbs : Result<&1, &1, U32 & String, List<&2, L.Mat>> <- RI.LoadingsSeries.load(bsp, t, n, k)
        rcfs : Result<&1, &1, U32 & String, List<&2, L.Mat>> <- RI.LoadingsSeries.load(cfsp, t, k, k)
        rdm : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(dsp, t, n)
        rrets : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(retsp, t, n)
        rws : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(wsp, t, n)
        rbv : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(bvp, n)
        rwr : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(wrp, n)
        rps : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(psp, 1)
        IO.print(run_ch5(rv, rr1, rbs, rcfs, rdm, rrets, rws, rbv, rwr, rps))
    case _:
      IO.print("BAD_ARGS_1\n")

def go_ch6a(args: List<String>) -> IO(Unit):
  match args:
    case fp <> epsp <> bp <> dp <> evwp <> indp <> l0p <> l1p <> jp <> cmp <> ccp <> psp <> ts <> ks <> ns <> k1s <> k2s <> qs <> lms <> ws <> tis <> _:
      +t = tu(ts)
      +k = tu(ks)
      +n = tu(ns)
      +k1 = tu(k1s)
      +k2 = tu(k2s)
      +q = tu(qs)
      +lmax = tu(lms)
      +win = tu(ws)
      +tidx = tu(tis)
      do IO<Unit>:
        rf : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(fp, t, k)
        reps : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(epsp, t, n)
        rb : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(bp, n, k)
        rd : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(dp, n)
        revw : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(evwp, t, n)
        rind : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(indp, k, k)
        rl0 : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(l0p, k1, k1)
        rl1 : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(l1p, k2, k2)
        rj : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(jp, (k1 + k2 : U32), (k1 + k2 : U32))
        rcm : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(cmp, n, q)
        rcc : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(ccp, q, q)
        rps : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(psp, 9)
        IO.print(run_ch6a(rf, reps, rb, rd, revw, rind, rl0, rl1, rj, rcm, rcc, rps, t, n, lmax, win, tidx))
    case _:
      IO.print("BAD_ARGS_2\n")

def go_ch6b(args: List<String>) -> IO(Unit):
  match args:
    case bp <> rp <> wp <> brdp <> ccp <> dcp <> bsp <> retsp <> wmp <> psp <> ns <> ks <> krds <> pcs <> ts <> ws <> _:
      +n = tu(ns)
      +k = tu(ks)
      +krd = tu(krds)
      +pc = tu(pcs)
      +t = tu(ts)
      +win = tu(ws)
      do IO<Unit>:
        rb : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(bp, n, k)
        rr : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(rp, n)
        rw : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(wp, n)
        rbrd : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(brdp, n, krd)
        rcc : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(ccp, krd, pc)
        rdc : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(dcp, pc)
        rbs : Result<&1, &1, U32 & String, List<&2, L.Mat>> <- RI.LoadingsSeries.load(bsp, t, n, k)
        rrets : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(retsp, t, n)
        rwm : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(wmp, t, n)
        rps : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(psp, 2)
        IO.print(run_ch6b(rb, rr, rw, rbrd, rcc, rdc, rbs, rrets, rwm, rps, win))
    case _:
      IO.print("BAD_ARGS_3\n")

def go_ch7(args: List<String>) -> IO(Unit):
  match args:
    case rp <> rbp <> bpp <> bcp <> cfpp <> cfcp <> dpp <> dcp <> anp <> gkp <> gnp <> ts <> ns <> ks <> tbs <> nbs <> kbs <> mns <> pcs <> ws <> _:
      +t = tu(ts)
      +n = tu(ns)
      +k = tu(ks)
      +tb = tu(tbs)
      +nb = tu(nbs)
      +kb = tu(kbs)
      +mn = tu(mns)
      +pc = tu(pcs)
      +win = tu(ws)
      do IO<Unit>:
        rr : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(rp, t, n)
        rrb : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(rbp, tb, nb)
        rbp : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(bpp, n, k)
        rbc : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(bcp, n, k)
        rcfp : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(cfpp, k, k)
        rcfc : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(cfcp, k, k)
        rdp : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(dpp, n)
        rdc : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(dcp, n)
        ran : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(anp, t, mn)
        rgk : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(gkp, n, pc)
        rgn : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(gnp, mn, pc)
        IO.print(run_ch7(rr, rrb, rbp, rbc, rcfp, rcfc, rdp, rdc, ran, rgk, rgn, t, n, k, kb, win))
    case _:
      IO.print("BAD_ARGS_4\n")

def d5(is5: Bool, rest: List<String>) -> IO(Unit):
  match is5:
    case True{}:
      IO.print(run_edge())
    case False{}:
      IO.print("USAGE\n")

def d4(is4: Bool, is5: Bool, rest: List<String>) -> IO(Unit):
  match is4:
    case True{}:
      go_ch7(rest)
    case False{}:
      d5(is5, rest)

def d3(is3: Bool, is4: Bool, is5: Bool, rest: List<String>) -> IO(Unit):
  match is3:
    case True{}:
      go_ch6b(rest)
    case False{}:
      d4(is4, is5, rest)

def d2(is2: Bool, is3: Bool, is4: Bool, is5: Bool, rest: List<String>) -> IO(Unit):
  match is2:
    case True{}:
      go_ch6a(rest)
    case False{}:
      d3(is3, is4, is5, rest)

def d1(is1: Bool, is2: Bool, is3: Bool, is4: Bool, is5: Bool, rest: List<String>) -> IO(Unit):
  match is1:
    case True{}:
      go_ch5(rest)
    case False{}:
      d2(is2, is3, is4, is5, rest)

def dispatch(is0: Bool, is1: Bool, is2: Bool, is3: Bool, is4: Bool, is5: Bool, rest: List<String>) -> IO(Unit):
  match is0:
    case True{}:
      go_ch4(rest)
    case False{}:
      d1(is1, is2, is3, is4, is5, rest)

def go(args: List<String>) -> IO(Unit):
  match args:
    case _ <> mode <> rest:
      +m = tu(mode)
      dispatch(U32.is_eq(m, 0), U32.is_eq(m, 1), U32.is_eq(m, 2), U32.is_eq(m, 3), U32.is_eq(m, 4), U32.is_eq(m, 5), rest)
    case _:
      IO.print("NO_ARGS\n")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
