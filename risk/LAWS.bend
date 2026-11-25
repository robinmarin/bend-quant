# Laws for risk. The checker does not reduce F32 arithmetic, so numerical
# accuracy is verified against NumPy, SciPy, scikit-learn, and statsmodels in
# check.py. These laws prove exact structural symmetry, strict causality,
# no-lookahead out-of-sample pairing, parallel-sequential equivalence, and
# dimension/parameter guards for every input.
import Base
import bend-quant-linalg@0.1.1.0/linalg.bend as L
import bend-quant-portfolio@0.1.1.0/portfolio.bend as P
import ./cov.bend as C
import ./risk.bend as R

# ---------------------------------------------------------------- helpers for law statements

def upper_ok(up: List<&2, List<&2, F32>>, n: Nat) -> Bool:
  match up n:
    case Nil{} 0n:
      True{}
    case Con{r, sub} 1n+(+p):
      Bool.and(Nat.is_eq(List.length(&2, F32, r), 1n+p), upper_ok(sub, p))
    case _ _:
      False{}

def mm_get(mm: Maybe<&2, L.Mat>, i: Nat, j: Nat) -> Maybe<&2, F32>:
  match mm:
    case None{}:
      None{}
    case Some{m}:
      L.Mat.get(m, i, j)

def ms_cov_get(ms: Maybe<&2, R.ShrinkResult>, i: Nat, j: Nat) -> Maybe<&2, F32>:
  match ms:
    case None{}:
      None{}
    case Some{R.ShrinkResult{cov, _, _}}:
      L.Mat.get(cov, i, j)

def maybe_map_c(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, c: C, m: Maybe<&2, A>) -> Maybe<&2, B>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{f(c, x)}

def maybe_pair_fm(mf: Maybe<&2, P.FactorModel>, mr: Maybe<&2, List<&2, F32>>) -> Maybe<&2, R.FmRetPair>:
  match mf mr:
    case Some{fm} Some{r}:
      Some{R.FmRetPair{fm, r}}
    case _ _:
      None{}

def maybe_pair_fmw(mf: Maybe<&2, P.FactorModel>, mw: Maybe<&2, List<&2, F32>>, mr: Maybe<&2, List<&2, F32>>) -> Maybe<&2, R.FmWRet>:
  match mf mw mr:
    case Some{fm} Some{w} Some{r}:
      Some{R.FmWRet{fm, w, r}}
    case _ _ _:
      None{}

def mm_take_rows(k: Nat, mm: Maybe<&2, L.Mat>) -> Maybe<&2, List<&2, List<&2, F32>>>:
  match mm:
    case None{}:
      None{}
    case Some{L.Mat{_, _, rows}}:
      Some{R.list_take(List<&2, F32>, k, rows)}

# ---------------------------------------------------------------- 1. Exact Structural Symmetry (11 laws + 1 guard)

law mirror_upper_sym:
  for up: List<&2, List<&2, F32>>
  for n: Nat
  for +i: Nat
  for +j: Nat
  for +h: {upper_ok(up, n) == True{} : Bool}
  {L.mat_get(C.mirror_upper(up), i, j) == L.mat_get(C.mirror_upper(up), j, i) : Maybe<&2, F32>}

law symmetrize_nonsquare:
  for +m: U32
  for +n: U32
  for rows: List<&2, List<&2, F32>>
  for h: {U32.is_eq(m, n) == False{} : Bool}
  {R.symmetrize(L.Mat{m, n, rows}) == None{} : Maybe<&2, L.Mat>}

law symmetrize_sym:
  for +a: L.Mat
  for +i: Nat
  for +j: Nat
  {mm_get(R.symmetrize(a), i, j) == mm_get(R.symmetrize(a), j, i) : Maybe<&2, F32>}

law sample_cov_sym:
  for +x: L.Mat
  for +center: Bool
  for +i: Nat
  for +j: Nat
  {mm_get(R.sample_cov(x, center), i, j) == mm_get(R.sample_cov(x, center), j, i) : Maybe<&2, F32>}

law ewma_cov_sym:
  for +x: L.Mat
  for +hl: F32
  for +center: Bool
  for +i: Nat
  for +j: Nat
  {mm_get(R.ewma_cov(x, hl, center), i, j) == mm_get(R.ewma_cov(x, hl, center), j, i) : Maybe<&2, F32>}

law shrink_to_identity_sym:
  for +cov: L.Mat
  for +rho: F32
  for +i: Nat
  for +j: Nat
  {mm_get(R.shrink_to_identity(cov, rho), i, j) == mm_get(R.shrink_to_identity(cov, rho), j, i) : Maybe<&2, F32>}

law ledoit_wolf_sym:
  for +x: L.Mat
  for +center: Bool
  for +i: Nat
  for +j: Nat
  {ms_cov_get(R.ledoit_wolf_cov(x, center), i, j) == ms_cov_get(R.ledoit_wolf_cov(x, center), j, i) : Maybe<&2, F32>}

law psd_project_sym:
  for +a: L.Mat
  for +fl: F32
  for +i: Nat
  for +j: Nat
  {mm_get(R.psd_project(a, fl), i, j) == mm_get(R.psd_project(a, fl), j, i) : Maybe<&2, F32>}

law dcc_cov_sym:
  for +f_rets: L.Mat
  for +hlv: F32
  for +hlc: F32
  for +i: Nat
  for +j: Nat
  {mm_get(R.dcc_cov(f_rets, hlv, hlc), i, j) == mm_get(R.dcc_cov(f_rets, hlv, hlc), j, i) : Maybe<&2, F32>}

law cov_newey_west_sym:
  for +x: L.Mat
  for +lmax: U32
  for +hl: F32
  for +i: Nat
  for +j: Nat
  {mm_get(R.cov_newey_west(x, lmax, hl), i, j) == mm_get(R.cov_newey_west(x, lmax, hl), j, i) : Maybe<&2, F32>}

law cov_autocorr_cohen_sym:
  for +x: L.Mat
  for +lmax: U32
  for +hl: F32
  for +i: Nat
  for +j: Nat
  {mm_get(R.cov_autocorr_cohen(x, lmax, hl), i, j) == mm_get(R.cov_autocorr_cohen(x, lmax, hl), j, i) : Maybe<&2, F32>}

law link_models_ir_sym:
  for +locs: List<&2, L.Mat>
  for +joint: L.Mat
  for +rho: F32
  for +i: Nat
  for +j: Nat
  {mm_get(R.link_models_ir(locs, joint, rho), i, j) == mm_get(R.link_models_ir(locs, joint, rho), j, i) : Maybe<&2, F32>}

# ---------------------------------------------------------------- 2. Strict Causality (4 laws, plus oos_returns_row)

law scan_causal:
  for ~A: Data
  for ~B: Data
  for ~S: Data
  for ~next: S -> A -> S
  for ~out: S -> A -> B
  for +k: Nat
  for +xs: List<&2, A>
  for +s: S
  {R.list_take(B, k, C.scan(~A, ~B, ~S, ~next, ~out, xs, s)) == C.scan(~A, ~B, ~S, ~next, ~out, R.list_take(A, k, xs), s) : List<&2, B>}

law winsorize_log_mad_causal:
  for +t: U32
  for +t2: U32
  for +n: U32
  for +rows: List<&2, List<&2, F32>>
  for +w: U32
  for +dmax: F32
  for +k: Nat
  {mm_take_rows(k, R.winsorize_log_mad(L.Mat{t, n, rows}, w, dmax)) == mm_take_rows(k, R.winsorize_log_mad(L.Mat{t2, n, R.list_take(List<&2, F32>, k, rows)}, w, dmax)) : Maybe<&2, List<&2, List<&2, F32>>>}

law make_windows_get:
  for -A: Data
  for rem: Nat
  for +xs: List<&2, A>
  for +w: Nat
  for +i: Nat
  for h: {Nat.is_lt(i, rem) == True{} : Bool}
  for hlen: {Nat.is_lt(i, List.length(&2, A, xs)) == True{} : Bool}
  {List.get(&2, List<&2, A>, R.make_windows(A, rem, xs, w), i) == Some{R.list_take(A, w, R.list_drop(A, i, xs))} : Maybe<&2, List<&2, A>>}

# The first k windows of size 1 + v depend only on the first k + v rows.
law make_windows_causal:
  for -A: Data
  for +k: Nat
  for +rem: Nat
  for +xs: List<&2, A>
  for +v: Nat
  {R.list_take(List<&2, A>, k, R.make_windows(A, rem, xs, 1n+v)) == R.list_take(List<&2, A>, k, R.make_windows(A, rem, R.list_take(A, Nat.add(k, v), xs), 1n+v)) : List<&2, List<&2, A>>}

def mm_row(mm: Maybe<&2, L.Mat>, i: Nat) -> Maybe<&2, List<&2, F32>>:
  match mm:
    case None{}:
      None{}
    case Some{L.Mat{_, _, rows}}:
      List.get(&2, List<&2, F32>, rows, i)

# Rolling models to evaluation. With window = 1 + v, make_windows_get says model j
# is fit on rows j .. j + v. Row 1 + j of oos_returns(R, window) is row j + v + 1
# of R, and qdist_pairs / pair_oos_fm_row score model j on exactly that row.
law oos_returns_row:
  for +t: U32
  for +n: U32
  for +rows: List<&2, List<&2, F32>>
  for +window: U32
  for +v: Nat
  for +j: Nat
  for hw: {U32.to_nat(window) == 1n+v : Nat}
  for ok: {Bool.and(U32.is_gt(window, 0), U32.is_ge(t, window)) == True{} : Bool}
  {mm_row(R.oos_returns(L.Mat{t, n, rows}, window), 1n+j) == List.get(&2, List<&2, F32>, rows, Nat.add(1n+j, v)) : Maybe<&2, List<&2, F32>>}

# ---------------------------------------------------------------- 3. No-Lookahead Out-of-Sample Evaluation (Ch 5, 6 laws + 2 guards)

law pair_oos_fm_row:
  for +fms: List<&2, P.FactorModel>
  for r0: List<&2, F32>
  for +rs: List<&2, List<&2, F32>>
  for +i: Nat
  {List.get(&2, R.FmRetPair, R.pair_oos_fm(fms, rs), i) == maybe_pair_fm(List.get(&2, P.FactorModel, fms, i), List.get(&2, List<&2, F32>, r0 <> rs, 1n+i)) : Maybe<&2, R.FmRetPair>}

law pair_oos_fmw_row:
  for +fms: List<&2, P.FactorModel>
  for +ws: List<&2, List<&2, F32>>
  for r0: List<&2, F32>
  for +rs: List<&2, List<&2, F32>>
  for +i: Nat
  {List.get(&2, R.FmWRet, R.pair_oos_fmw(fms, ws, rs), i) == maybe_pair_fmw(List.get(&2, P.FactorModel, fms, i), List.get(&2, List<&2, F32>, ws, i), List.get(&2, List<&2, F32>, r0 <> rs, 1n+i)) : Maybe<&2, R.FmWRet>}

# The public evaluators run their per-period metric over exactly pair_oos_fm /
# pair_oos_fmw, so with pair_oos_fm_row: period i scores model i on row i + 1.
law qdist_pairs:
  for +fms: List<&2, P.FactorModel>
  for +t: U32
  for +n: U32
  for +r0: List<&2, F32>
  for +rs: List<&2, List<&2, F32>>
  for h: {Bool.and(U32.is_eq(U32.from_nat(List.length(&2, P.FactorModel, fms)), t), Bool.and(U32.is_gt(t, 1), U32.is_gt(n, 0))) == True{} : Bool}
  {R.qdist(fms, L.Mat{t, n, r0 <> rs}) == R.qdist.fin(R.seq_maybe(F32, R.pseq(~R.FmRetPair, ~Maybe<&2, F32>, ~U32, ~R.qdist_period, R.pair_oos_fm(fms, rs), n)), (t - 1 : U32)) : Maybe<&2, R.QDistResult>}

law mahalanobis_pairs:
  for +fms: List<&2, P.FactorModel>
  for +t: U32
  for +n: U32
  for +r0: List<&2, F32>
  for +rs: List<&2, List<&2, F32>>
  for h: {Bool.and(U32.is_eq(U32.from_nat(List.length(&2, P.FactorModel, fms)), t), Bool.and(U32.is_gt(t, 1), U32.is_gt(n, 0))) == True{} : Bool}
  {R.mahalanobis_test(fms, L.Mat{t, n, r0 <> rs}) == R.mahal.fin(R.seq_maybe(F32, R.pseq(~R.FmRetPair, ~Maybe<&2, F32>, ~U32, ~R.mahal_period, R.pair_oos_fm(fms, rs), n)), (t - 1 : U32)) : Maybe<&2, R.MahalanobisResult>}

law mvp_pairs:
  for +fms: List<&2, P.FactorModel>
  for +t: U32
  for +n: U32
  for +r0: List<&2, F32>
  for +rs: List<&2, List<&2, F32>>
  for +nb: U32
  for +bs: List<&2, F32>
  for h: {Bool.and(U32.is_eq(U32.from_nat(List.length(&2, P.FactorModel, fms)), t), Bool.and(U32.is_eq(n, nb), Bool.and(U32.is_gt(t, 1), U32.is_gt(n, 0)))) == True{} : Bool}
  {R.mvp_test(fms, L.Mat{t, n, r0 <> rs}, L.Vec{nb, bs}) == R.mvp.fin(R.seq_maybe(R.MvpStep, R.pseq(~R.FmRetPair, ~Maybe<&2, R.MvpStep>, ~L.Vec, ~R.mvp_period, R.pair_oos_fm(fms, rs), L.Vec{nb, bs})), (t - 1 : U32)) : Maybe<&2, R.MvpResult>}

law portfolio_vol_pairs:
  for +fms: List<&2, P.FactorModel>
  for +tw: U32
  for +nw: U32
  for +wrows: List<&2, List<&2, F32>>
  for +tr: U32
  for +nr: U32
  for +r0: List<&2, F32>
  for +rs: List<&2, List<&2, F32>>
  for h: {Bool.and(U32.is_eq(U32.from_nat(List.length(&2, P.FactorModel, fms)), tw), Bool.and(U32.is_eq(tw, tr), Bool.and(U32.is_eq(nw, nr), Bool.and(U32.is_gt(tr, 1), U32.is_gt(nr, 0))))) == True{} : Bool}
  {R.portfolio_vol_eval(fms, L.Mat{tw, nw, wrows}, L.Mat{tr, nr, r0 <> rs}) == R.pvol.fin(R.seq_maybe(R.MvpStep, R.pseq(~R.FmWRet, ~Maybe<&2, R.MvpStep>, ~U32, ~R.pvol_period, R.pair_oos_fmw(fms, wrows, rs), nr)), (tr - 1 : U32)) : Maybe<&2, R.VolEval>}

law qdist_mismatch:
  for +fms: List<&2, P.FactorModel>
  for +t: U32
  for +n: U32
  for rows: List<&2, List<&2, F32>>
  for h: {U32.is_eq(U32.from_nat(List.length(&2, P.FactorModel, fms)), t) == False{} : Bool}
  {R.qdist(fms, L.Mat{t, n, rows}) == None{} : Maybe<&2, R.QDistResult>}

law mvp_test_mismatch:
  for +fms: List<&2, P.FactorModel>
  for +t: U32
  for +n: U32
  for rows: List<&2, List<&2, F32>>
  for +nb: U32
  for bs: List<&2, F32>
  for h: {U32.is_eq(n, nb) == False{} : Bool}
  {R.mvp_test(fms, L.Mat{t, n, rows}, L.Vec{nb, bs}) == None{} : Maybe<&2, R.MvpResult>}

# ---------------------------------------------------------------- 4. Parallel Equivalence (2 laws)

law pmap_seq:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: C -> A -> B
  for +xs: List<&2, A>
  for +t: U32
  for +c: C
  {R.pmap(~A, ~B, ~C, ~f, xs, t, c) == R.pseq(~A, ~B, ~C, ~f, xs, c) : List<&2, B>}

law pseq_get:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: C -> A -> B
  for +xs: List<&2, A>
  for +c: C
  for +i: Nat
  {List.get(&2, B, R.pseq(~A, ~B, ~C, ~f, xs, c), i) == maybe_map_c(~A, ~B, ~C, ~f, c, List.get(&2, A, xs, i)) : Maybe<&2, B>}

# ---------------------------------------------------------------- 5. Dimension & Parameter Guards (20 laws)

law rotate_model_mismatch:
  for +n: U32
  for +k: U32
  for brows: List<&2, List<&2, F32>>
  for cf: L.Mat
  for iv: L.Vec
  for +cm: U32
  for +cn: U32
  for crows: List<&2, List<&2, F32>>
  for h: {U32.is_eq(k, cm) == False{} : Bool}
  {R.rotate_model(P.FactorModel{L.Mat{n, k, brows}, cf, iv}, L.Mat{cm, cn, crows}) == None{} : Maybe<&2, P.FactorModel>}

law project_model_mismatch:
  for +n: U32
  for +k: U32
  for brows: List<&2, List<&2, F32>>
  for cf: L.Mat
  for iv: L.Vec
  for +am: U32
  for +ap: U32
  for arows: List<&2, List<&2, F32>>
  for h: {U32.is_eq(n, am) == False{} : Bool}
  {R.project_model(P.FactorModel{L.Mat{n, k, brows}, cf, iv}, L.Mat{am, ap, arows}) == None{} : Maybe<&2, P.FactorModel>}

law pushout_loadings_mismatch:
  for +bm: U32
  for +bk: U32
  for brows: List<&2, List<&2, F32>>
  for +am: U32
  for +ap: U32
  for arows: List<&2, List<&2, F32>>
  for iv: L.Vec
  for h: {U32.is_eq(bm, am) == False{} : Bool}
  {R.pushout_loadings(L.Mat{bm, bk, brows}, L.Mat{am, ap, arows}, iv) == None{} : Maybe<&2, L.Mat>}

law group_risk_mismatch:
  for +n: U32
  for +k: U32
  for brows: List<&2, List<&2, F32>>
  for cf: L.Mat
  for iv: L.Vec
  for +wn: U32
  for ws: List<&2, F32>
  for +groups: List<&2, List<&2, U32>>
  for h: {U32.is_eq(n, wn) == False{} : Bool}
  {R.group_risk_decomp(P.FactorModel{L.Mat{n, k, brows}, cf, iv}, L.Vec{wn, ws}, groups) == None{} : Maybe<&2, R.GroupRisk>}

law qlike_mismatch:
  for +nv: U32
  for vs: List<&2, F32>
  for +nr: U32
  for rs: List<&2, F32>
  for h: {U32.is_eq(nv, nr) == False{} : Bool}
  {R.qlike(L.Vec{nv, vs}, L.Vec{nr, rs}) == None{} : Maybe<&2, F32>}

law vol_mse_mismatch:
  for +nv: U32
  for vs: List<&2, F32>
  for +nr: U32
  for rs: List<&2, F32>
  for h: {U32.is_eq(nv, nr) == False{} : Bool}
  {R.vol_mse(L.Vec{nv, vs}, L.Vec{nr, rs}) == None{} : Maybe<&2, F32>}

law bias_stat_mismatch:
  for +nv: U32
  for vs: List<&2, F32>
  for +nr: U32
  for rs: List<&2, F32>
  for h: {U32.is_eq(nv, nr) == False{} : Bool}
  {R.bias_stat(L.Vec{nv, vs}, L.Vec{nr, rs}) == None{} : Maybe<&2, F32>}

law mahalanobis_mismatch:
  for +fms: List<&2, P.FactorModel>
  for +t: U32
  for +n: U32
  for rows: List<&2, List<&2, F32>>
  for h: {U32.is_eq(U32.from_nat(List.length(&2, P.FactorModel, fms)), t) == False{} : Bool}
  {R.mahalanobis_test(fms, L.Mat{t, n, rows}) == None{} : Maybe<&2, R.MahalanobisResult>}

law beta_error_mismatch:
  for +fms: List<&2, P.FactorModel>
  for +t: U32
  for +n: U32
  for rows: List<&2, List<&2, F32>>
  for +nw: U32
  for ws: List<&2, F32>
  for +hl: F32
  for h: {U32.is_eq(n, nw) == False{} : Bool}
  {R.beta_error(fms, L.Mat{t, n, rows}, L.Vec{nw, ws}, hl) == None{} : Maybe<&2, R.BetaErrResult>}

law cs_wls_mismatch:
  for +n: U32
  for +k: U32
  for brows: List<&2, List<&2, F32>>
  for +nr: U32
  for rs: List<&2, F32>
  for w: L.Vec
  for h: {U32.is_eq(n, nr) == False{} : Bool}
  {R.cross_sectional_wls(L.Mat{n, k, brows}, L.Vec{nr, rs}, w) == None{} : Maybe<&2, R.CSRegResult>}

law cs_constrained_mismatch:
  for +n: U32
  for +k: U32
  for brows: List<&2, List<&2, F32>>
  for +nr: U32
  for rs: List<&2, F32>
  for w: L.Vec
  for cons: R.CSConstraint
  for h: {U32.is_eq(n, nr) == False{} : Bool}
  {R.cross_sectional_constrained(L.Mat{n, k, brows}, L.Vec{nr, rs}, w, cons) == None{} : Maybe<&2, R.CSRegResult>}

law cs_ridge_mismatch:
  for +n: U32
  for +k: U32
  for brows: List<&2, List<&2, F32>>
  for +nr: U32
  for rs: List<&2, F32>
  for w: L.Vec
  for +delta: F32
  for h: {U32.is_eq(n, nr) == False{} : Bool}
  {R.cross_sectional_ridge(L.Mat{n, k, brows}, L.Vec{nr, rs}, w, delta) == None{} : Maybe<&2, R.CSRegResult>}

law fit_fundamental_mismatch:
  for +t: U32
  for +n: U32
  for rows: List<&2, List<&2, F32>>
  for +bs: List<&2, L.Mat>
  for opt_cons: Maybe<&2, R.CSConstraint>
  for cfg: R.FundConfig
  for h: {U32.is_eq(U32.from_nat(List.length(&2, L.Mat, bs)), t) == False{} : Bool}
  {R.fit_fundamental_model(L.Mat{t, n, rows}, bs, opt_cons, cfg) == None{} : Maybe<&2, R.FundModelFit>}

law rebase_currency_mismatch:
  for +n: U32
  for +qc: U32
  for crows: List<&2, List<&2, F32>>
  for +cm: U32
  for +cn: U32
  for cov_rows: List<&2, List<&2, F32>>
  for +target: U32
  for h: {U32.is_eq(qc, cm) == False{} : Bool}
  {R.rebase_currency(L.Mat{n, qc, crows}, L.Mat{cm, cn, cov_rows}, target) == None{} : Maybe<&2, R.RebaseResult>}

law pca_svd_zero_k:
  for +r: L.Mat
  for +hl: F32
  for use_sub: Bool
  {R.pca_svd(r, 0, hl, use_sub) == None{} : Maybe<&2, R.PcaResult>}

law eigenfactor_turnover_mismatch:
  for +m1: U32
  for +k1: U32
  for r1: List<&2, List<&2, F32>>
  for +m2: U32
  for +k2: U32
  for r2: List<&2, List<&2, F32>>
  for h: {U32.is_eq(m1, m2) == False{} : Bool}
  {R.eigenfactor_turnover(L.Mat{m1, k1, r1}, L.Mat{m2, k2, r2}) == None{} : Maybe<&2, R.EigenTurnover>}

law align_sign_mismatch:
  for +m1: U32
  for +k1: U32
  for r1: List<&2, List<&2, F32>>
  for +m2: U32
  for +k2: U32
  for r2: List<&2, List<&2, F32>>
  for h: {U32.is_eq(m1, m2) == False{} : Bool}
  {R.align_sign(L.Mat{m1, k1, r1}, L.Mat{m2, k2, r2}) == None{} : Maybe<&2, L.Mat>}

law subspace_distance_mismatch:
  for +m1: U32
  for +k1: U32
  for r1: List<&2, List<&2, F32>>
  for +m2: U32
  for +k2: U32
  for r2: List<&2, List<&2, F32>>
  for h: {U32.is_eq(m1, m2) == False{} : Bool}
  {R.subspace_distance(L.Mat{m1, k1, r1}, L.Mat{m2, k2, r2}) == None{} : Maybe<&2, F32>}

law impute_ts_mismatch:
  for +ta: U32
  for +ma: U32
  for arows: List<&2, List<&2, F32>>
  for +tf: U32
  for +kf: U32
  for frows: List<&2, List<&2, F32>>
  for h: {U32.is_eq(ta, tf) == False{} : Bool}
  {R.impute_loadings_ts(L.Mat{ta, ma, arows}, L.Mat{tf, kf, frows}) == None{} : Maybe<&2, L.Mat>}

law rolling_stat_zero_window:
  for +r: L.Mat
  for cfg: R.StatConfig
  for +am: U32
  {R.rolling_statistical_models(r, 0, cfg, am) == None{} : Maybe<&2, List<&2, P.FactorModel>>}
