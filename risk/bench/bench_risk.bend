# Benchmark driver for bend-quant-risk (Paleologo Ch 4-7).
# Driven by bench/run_bench.py to measure end-to-end timings (including Data <-> Array boundaries)
# across 1 thread and 8 threads (+RTS --threads N -RTS).
import Base
import bend-quant-linalg@0.1.1.0/linalg.bend as L
import bend-quant-linalg@0.1.1.0/io.bend as LI
import bend-quant-portfolio@0.1.1.0/portfolio.bend as P
import ../risk.bend as R
import ../io.bend as RI

def num(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{n}:
      n
    case None{}:
      0

def tu(s: String) -> U32:
  num(U32.read(s))

def sum_list(xs: List<&2, F32>, acc: F32) -> F32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      sum_list(t, (acc + h : F32))

def mat_chk.rows(rs: List<&2, List<&2, F32>>, acc: F32) -> F32:
  match rs:
    case Nil{}:
      acc
    case Con{r, t}:
      mat_chk.rows(t, sum_list(r, acc))

def mat_chk(mm: Maybe<&2, L.Mat>) -> F32:
  match mm:
    case Some{L.Mat{_, _, rs}}:
      mat_chk.rows(rs, 0.0)
    case None{}:
      0.0

def shrink_chk(ms: Maybe<&2, R.ShrinkResult>) -> F32:
  match ms:
    case Some{R.ShrinkResult{L.Mat{_, _, rs}, sh, _}}:
      (mat_chk.rows(rs, 0.0) + sh : F32)
    case None{}:
      0.0

def qdist_chk(mq: Maybe<&2, R.QDistResult>) -> F32:
  match mq:
    case Some{R.QDistResult{mn, _, _}}:
      mn
    case None{}:
      0.0

def mahal_chk(mm: Maybe<&2, R.MahalanobisResult>) -> F32:
  match mm:
    case Some{R.MahalanobisResult{_, mn, mv}}:
      (mn + mv : F32)
    case None{}:
      0.0

def mvp_chk(mm: Maybe<&2, R.MvpResult>) -> F32:
  match mm:
    case Some{R.MvpResult{rv, _, mpv, ql, _, _, _, _}}:
      ((rv + mpv : F32) + ql : F32)
    case None{}:
      0.0

def fser_chk(mf: Maybe<&2, R.FactorSeries>) -> F32:
  match mf:
    case Some{R.FactorSeries{L.Mat{_, _, fr}, _}}:
      mat_chk.rows(fr, 0.0)
    case None{}:
      0.0

def ffit_chk(mf: Maybe<&2, R.FundModelFit>) -> F32:
  match mf:
    case Some{R.FundModelFit{P.FactorModel{_, L.Mat{_, _, cf}, L.Vec{_, d}}, _, _}}:
      (mat_chk.rows(cf, 0.0) + sum_list(d, 0.0) : F32)
    case None{}:
      0.0

def pca_chk(mp: Maybe<&2, R.PcaResult>) -> F32:
  match mp:
    case Some{R.PcaResult{_, _, L.Vec{_, sv}, _}}:
      sum_list(sv, 0.0)
    case None{}:
      0.0

def sfit_chk(ms: Maybe<&2, R.StatModelFit>) -> F32:
  match ms:
    case Some{R.StatModelFit{P.FactorModel{_, _, L.Vec{_, d}}, _, _, L.Vec{_, sv}}}:
      (sum_list(d, 0.0) + sum_list(sv, 0.0) : F32)
    case None{}:
      0.0

def fms_chk.go(fms: List<&2, P.FactorModel>, acc: F32) -> F32:
  match fms:
    case Nil{}:
      acc
    case Con{P.FactorModel{_, _, L.Vec{_, d}}, t}:
      fms_chk.go(t, sum_list(d, acc))

def fms_chk(mfms: Maybe<&2, List<&2, P.FactorModel>>) -> F32:
  match mfms:
    case Some{fms}:
      fms_chk.go(fms, 0.0)
    case None{}:
      0.0

def mk_fm(b: L.Mat, cf: L.Mat, d: L.Vec) -> P.FactorModel:
  P.FactorModel{b, cf, d}

def mk_scfg(k: U32, p: U32, hf: F32, hs: F32, sm: U32, k1: F32, k2: F32, si: F32, sub: Bool, fl: F32) -> R.StatConfig:
  R.StatConfig{k, p, hf, hs, sm, k1, k2, si, sub, fl}

def mk_fcfg(hv: F32, hc: F32, hi: F32, nw: U32, sf: F32, si: F32, hs: F32, stvu: Bool, db: Bool, fl: F32) -> R.FundConfig:
  R.FundConfig{hv, hc, hi, nw, sf, si, hs, stvu, db, fl}

# ---- Mode 0: Ch 6 Covariance estimators (op 0=LW, 1=NW, 2=DCC) ----

def rep_lw(rem: Nat, +f: L.Mat, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_lw(p, f, (acc + shrink_chk(R.ledoit_wolf_cov(f, True{})) : F32))

def rep_nw(rem: Nat, +f: L.Mat, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_nw(p, f, (acc + mat_chk(R.cov_newey_west(f, 5, 63.0)) : F32))

def rep_dcc(rem: Nat, +f: L.Mat, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_dcc(p, f, (acc + mat_chk(R.dcc_cov(f, 30.0, 90.0)) : F32))

def run_cov2(is1: Bool, f: L.Mat, reps: Nat) -> F32:
  match is1:
    case True{}:
      rep_nw(reps, f, 0.0)
    case False{}:
      rep_dcc(reps, f, 0.0)

def run_cov1(is0: Bool, is1: Bool, f: L.Mat, reps: Nat) -> F32:
  match is0:
    case True{}:
      rep_lw(reps, f, 0.0)
    case False{}:
      run_cov2(is1, f, reps)

def run_cov(rf: Result<&1, &1, U32 & String, L.Mat>, +op: U32, reps: Nat) -> String:
  match rf:
    case Done{f}:
      F32.show(run_cov1(U32.is_eq(op, 0), U32.is_eq(op, 1), f, reps)) ++ "\n"
    case Fail{_}:
      "FAIL\n"

# ---- Mode 1: Ch 5 OOS Woodbury tests (op 0=qdist, 1=mahal, 2=mvp) ----

def rep_qdist(rem: Nat, +fms: List<&2, P.FactorModel>, +rets: L.Mat, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_qdist(p, fms, rets, (acc + qdist_chk(R.qdist(fms, rets)) : F32))

def rep_mahal(rem: Nat, +fms: List<&2, P.FactorModel>, +rets: L.Mat, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_mahal(p, fms, rets, (acc + mahal_chk(R.mahalanobis_test(fms, rets)) : F32))

def rep_mvp(rem: Nat, +fms: List<&2, P.FactorModel>, +rets: L.Mat, +bvec: L.Vec, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_mvp(p, fms, rets, bvec, (acc + mvp_chk(R.mvp_test(fms, rets, bvec)) : F32))

def run_ch5_2(is1: Bool, fms: List<&2, P.FactorModel>, rets: L.Mat, bvec: L.Vec, reps: Nat) -> F32:
  match is1:
    case True{}:
      rep_mahal(reps, fms, rets, 0.0)
    case False{}:
      rep_mvp(reps, fms, rets, bvec, 0.0)

def run_ch5_1(is0: Bool, is1: Bool, fms: List<&2, P.FactorModel>, rets: L.Mat, bvec: L.Vec, reps: Nat) -> F32:
  match is0:
    case True{}:
      rep_qdist(reps, fms, rets, 0.0)
    case False{}:
      run_ch5_2(is1, fms, rets, bvec, reps)

def run_ch5(rb: Result<&1, &1, U32 & String, L.Mat>, rcf: Result<&1, &1, U32 & String, L.Mat>, rd: Result<&1, &1, U32 & String, L.Vec>, rrets: Result<&1, &1, U32 & String, L.Mat>, rbv: Result<&1, &1, U32 & String, L.Vec>, +t: U32, +op: U32, reps: Nat) -> String:
  match rb rcf rd rrets rbv:
    case Done{b} Done{cf} Done{d} Done{rets} Done{bv}:
      +fm = mk_fm(b, cf, d)
      fms = List.replicate(P.FactorModel, U32.to_nat(t), fm)
      F32.show(run_ch5_1(U32.is_eq(op, 0), U32.is_eq(op, 1), fms, rets, bv, reps)) ++ "\n"
    case _ _ _ _ _:
      "FAIL\n"

# ---- Mode 2: Ch 6 Fundamental (op 0=estimate_factor_series, 1=fit_fundamental_model) ----

def rep_fser(rem: Nat, +bs: List<&2, L.Mat>, +rets: L.Mat, +ws: List<&2, L.Vec>, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_fser(p, bs, rets, ws, (acc + fser_chk(R.estimate_factor_series(bs, rets, ws, None{})) : F32))

def rep_ffit(rem: Nat, +rets: L.Mat, +bs: List<&2, L.Mat>, +cfg: R.FundConfig, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_ffit(p, rets, bs, cfg, (acc + ffit_chk(R.fit_fundamental_model(rets, bs, None{}, cfg)) : F32))

def run_fund1(is0: Bool, bs: List<&2, L.Mat>, rets: L.Mat, ws: List<&2, L.Vec>, reps: Nat) -> F32:
  match is0:
    case True{}:
      rep_fser(reps, bs, rets, ws, 0.0)
    case False{}:
      +cfg = mk_fcfg(63.0, 126.0, 63.0, 2, 0.1, 0.1, 15.0, True{}, True{}, 1.0e-8)
      rep_ffit(reps, rets, bs, cfg, 0.0)

def run_fund(rb: Result<&1, &1, U32 & String, L.Mat>, rrets: Result<&1, &1, U32 & String, L.Mat>, +t: U32, +n: U32, +op: U32, reps: Nat) -> String:
  match rb rrets:
    case Done{b} Done{rets}:
      bs = List.replicate(L.Mat, U32.to_nat(t), b)
      ws = List.replicate(L.Vec, U32.to_nat(t), L.Vec.ones(n))
      F32.show(run_fund1(U32.is_eq(op, 0), bs, rets, ws, reps)) ++ "\n"
    case _ _:
      "FAIL\n"

# ---- Mode 3: Ch 7 Statistical & SVD (op 0=pca_exact, 1=pca_subspace, 2=fit_stat_subspace, 3=rolling_stat) ----

def rep_pca(rem: Nat, +rets: L.Mat, +k: U32, +use_sub: Bool, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_pca(p, rets, k, use_sub, (acc + pca_chk(R.pca_svd(rets, k, 0.0, use_sub)) : F32))

def rep_sfit(rem: Nat, +rets: L.Mat, +cfg: R.StatConfig, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_sfit(p, rets, cfg, (acc + sfit_chk(R.fit_statistical_model(rets, cfg)) : F32))

def rep_roll(rem: Nat, +rets: L.Mat, +win: U32, +cfg: R.StatConfig, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_roll(p, rets, win, cfg, (acc + fms_chk(R.rolling_statistical_models(rets, win, cfg, 2)) : F32))

def run_ch7_3(is2: Bool, rets: L.Mat, +k: U32, +win: U32, reps: Nat) -> F32:
  match is2:
    case True{}:
      +cfg = mk_scfg(k, 5, 63.0, 126.0, 1, 1.0, 0.0, 0.1, True{}, 1.0e-8)
      rep_sfit(reps, rets, cfg, 0.0)
    case False{}:
      +cfg = mk_scfg(k, 0, 0.0, 0.0, 1, 1.0, 0.0, 0.1, True{}, 1.0e-8)
      rep_roll(reps, rets, win, cfg, 0.0)

def run_ch7_2(is1: Bool, is2: Bool, rets: L.Mat, +k: U32, +win: U32, reps: Nat) -> F32:
  match is1:
    case True{}:
      rep_pca(reps, rets, k, True{}, 0.0)
    case False{}:
      run_ch7_3(is2, rets, k, win, reps)

def run_ch7_1(is0: Bool, is1: Bool, is2: Bool, rets: L.Mat, +k: U32, +win: U32, reps: Nat) -> F32:
  match is0:
    case True{}:
      rep_pca(reps, rets, k, False{}, 0.0)
    case False{}:
      run_ch7_2(is1, is2, rets, k, win, reps)

def run_ch7(rrets: Result<&1, &1, U32 & String, L.Mat>, +k: U32, +win: U32, +op: U32, reps: Nat) -> String:
  match rrets:
    case Done{rets}:
      F32.show(run_ch7_1(U32.is_eq(op, 0), U32.is_eq(op, 1), U32.is_eq(op, 2), rets, k, win, reps)) ++ "\n"
    case Fail{_}:
      "FAIL\n"

# ---- CLI dispatch ----

def go_cov(args: List<String>) -> IO(Unit):
  match args:
    case ops <> rs <> fp <> ts <> ks <> _:
      +op = tu(ops)
      +reps = U32.to_nat(tu(rs))
      +t = tu(ts)
      +k = tu(ks)
      do IO<Unit>:
        rf : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(fp, t, k)
        IO.print(run_cov(rf, op, reps))
    case _:
      IO.print("BAD_ARGS_0\n")

def go_ch5(args: List<String>) -> IO(Unit):
  match args:
    case ops <> rs <> bp <> cfp <> dp <> retsp <> bvp <> ts <> ns <> ks <> _:
      +op = tu(ops)
      +reps = U32.to_nat(tu(rs))
      +t = tu(ts)
      +n = tu(ns)
      +k = tu(ks)
      do IO<Unit>:
        rb : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(bp, n, k)
        rcf : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(cfp, k, k)
        rd : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(dp, n)
        rrets : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(retsp, t, n)
        rbv : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(bvp, n)
        IO.print(run_ch5(rb, rcf, rd, rrets, rbv, t, op, reps))
    case _:
      IO.print("BAD_ARGS_1\n")

def go_fund(args: List<String>) -> IO(Unit):
  match args:
    case ops <> rs <> bp <> retsp <> ts <> ns <> ks <> _:
      +op = tu(ops)
      +reps = U32.to_nat(tu(rs))
      +t = tu(ts)
      +n = tu(ns)
      +k = tu(ks)
      do IO<Unit>:
        rb : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(bp, n, k)
        rrets : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(retsp, t, n)
        IO.print(run_fund(rb, rrets, t, n, op, reps))
    case _:
      IO.print("BAD_ARGS_2\n")

def go_ch7(args: List<String>) -> IO(Unit):
  match args:
    case ops <> rs <> retsp <> ts <> ns <> ks <> ws <> _:
      +op = tu(ops)
      +reps = U32.to_nat(tu(rs))
      +t = tu(ts)
      +n = tu(ns)
      +k = tu(ks)
      +win = tu(ws)
      do IO<Unit>:
        rrets : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(retsp, t, n)
        IO.print(run_ch7(rrets, k, win, op, reps))
    case _:
      IO.print("BAD_ARGS_3\n")

def d3(is3: Bool, rest: List<String>) -> IO(Unit):
  match is3:
    case True{}:
      go_ch7(rest)
    case False{}:
      IO.print("USAGE\n")

def d2(is2: Bool, is3: Bool, rest: List<String>) -> IO(Unit):
  match is2:
    case True{}:
      go_fund(rest)
    case False{}:
      d3(is3, rest)

def d1(is1: Bool, is2: Bool, is3: Bool, rest: List<String>) -> IO(Unit):
  match is1:
    case True{}:
      go_ch5(rest)
    case False{}:
      d2(is2, is3, rest)

def dispatch(is0: Bool, is1: Bool, is2: Bool, is3: Bool, rest: List<String>) -> IO(Unit):
  match is0:
    case True{}:
      go_cov(rest)
    case False{}:
      d1(is1, is2, is3, rest)

def go(args: List<String>) -> IO(Unit):
  match args:
    case _ <> mode <> rest:
      +m = tu(mode)
      dispatch(U32.is_eq(m, 0), U32.is_eq(m, 1), U32.is_eq(m, 2), U32.is_eq(m, 3), rest)
    case _:
      IO.print("NO_ARGS\n")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
