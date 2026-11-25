# Benchmark suite for bend-quant-portfolio.
# Driven by bench/run_bench.py to measure end-to-end timings (including Data <-> Array boundaries).
import Base
import bend-quant-linalg@0.1.1.0/linalg.bend as L
import bend-quant-linalg@0.1.1.0/io.bend as LI
import ../portfolio.bend as P
import ../io.bend as PI

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

def vec_chk(mv: Maybe<&2, L.Vec>) -> F32:
  match mv:
    case Some{L.Vec{_, xs}}:
      sum_list(xs, 0.0)
    case None{}:
      0.0

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

def risk_chk(mr: Maybe<&2, P.RiskDecomp>) -> F32:
  match mr:
    case Some{P.RiskDecomp{tv, _, _, _, _, _, _, _}}:
      tv
    case None{}:
      0.0

def show_csv(xs: List<&2, F32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, Nil{}}:
      F32.show(h)
    case Con{h, t}:
      F32.show(h) ++ "," ++ show_csv(t)

def opt_chk(mo: Maybe<&2, P.OptResult>) -> String:
  match mo:
    case Some{P.OptResult{L.Vec{_, +xs}, it, rp, rd, _}}:
      "iters=" ++ U32.show(it) ++ " rp=" ++ F32.show(rp) ++ " rd=" ++ F32.show(rd) ++ " sum=" ++ F32.show(sum_list(xs, 0.0)) ++ " w=" ++ show_csv(xs)
    case None{}:
      "none"

def pattr_chk(mp: Maybe<&2, P.PeriodAttrib>) -> F32:
  match mp:
    case Some{P.PeriodAttrib{pos, _, fp, ip, _, _, ev}}:
      (((pos + fp : F32) + ip : F32) + ev : F32)
    case None{}:
      0.0

def repeat_risk(rem: Nat, +fm: P.FactorModel, +w: L.Vec, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      repeat_risk(p, fm, w, (acc + risk_chk(P.risk_decomp(fm, w)) : F32))

def repeat_mvo_tv(rem: Nat, +fm: P.FactorModel, +a: L.Vec, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      repeat_mvo_tv(p, fm, a, (acc + vec_chk(P.mvo_target_vol(fm, a, 0.12)) : F32))

def repeat_mvo_fn(rem: Nat, +fm: P.FactorModel, +a: L.Vec, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      repeat_mvo_fn(p, fm, a, (acc + vec_chk(P.mvo_factor_neutral(fm, a, 0.12)) : F32))

def repeat_fmp(rem: Nat, +fm: P.FactorModel, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      repeat_fmp(p, fm, (acc + mat_chk(P.fmp(fm)) : F32))

def repeat_hedge(rem: Nat, +fm: P.FactorModel, +w: L.Vec, +hmat: L.Mat, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      repeat_hedge(p, fm, w, hmat, (acc + vec_chk(P.hedge_instruments(fm, w, hmat)) : F32))

def repeat_attrib(rem: Nat, +fm: P.FactorModel, +w: L.Vec, +r: L.Vec, +fr: L.Vec, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      repeat_attrib(p, fm, w, r, fr, (acc + pattr_chk(P.attribute_period(fm, w, r, fr, 0.0)) : F32))

def fpnl_sum(mxs: Maybe<&2, List<&2, F32>>) -> F32:
  match mxs:
    case Some{xs}:
      sum_list(xs, 0.0)
    case None{}:
      0.0

def repeat_fpnl(rem: Nat, +wm: L.Mat, +rm: L.Mat, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      repeat_fpnl(p, wm, rm, (acc + fpnl_sum(P.forward_pnl(wm, rm)) : F32))

def rep_fm(rem: Nat, +fm: P.FactorModel) -> List<&2, P.FactorModel>:
  match rem:
    case 0n:
      Nil{}
    case 1n+p:
      fm <> rep_fm(p, fm)

def fattr_sum.go(xs: List<&2, Maybe<&2, P.PeriodAttrib>>, acc: F32) -> F32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      fattr_sum.go(t, (acc + pattr_chk(h) : F32))

def fattr_sum(mxs: Maybe<&2, List<&2, Maybe<&2, P.PeriodAttrib>>>) -> F32:
  match mxs:
    case Some{xs}:
      fattr_sum.go(xs, 0.0)
    case None{}:
      0.0

def repeat_fattr(rem: Nat, +fms: List<&2, P.FactorModel>, +wm: L.Mat, +rm: L.Mat, +frm: L.Mat, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      repeat_fattr(p, fms, wm, rm, frm, (acc + fattr_sum(P.forward_attribute(fms, wm, rm, frm)) : F32))

def run_bench_op.p45(is4: Bool, reps: Nat, fm: P.FactorModel, w: L.Vec, r: L.Vec, fr: L.Vec, hmat: L.Mat) -> String:
  match is4:
    case True{}:
      "chk=" ++ F32.show(repeat_hedge(reps, fm, w, hmat, 0.0)) ++ "\n"
    case False{}:
      "chk=" ++ F32.show(repeat_attrib(reps, fm, w, r, fr, 0.0)) ++ "\n"

def run_bench_op.p3(is3: Bool, is4: Bool, reps: Nat, fm: P.FactorModel, w: L.Vec, r: L.Vec, fr: L.Vec, hmat: L.Mat) -> String:
  match is3:
    case True{}:
      "chk=" ++ F32.show(repeat_fmp(reps, fm, 0.0)) ++ "\n"
    case False{}:
      run_bench_op.p45(is4, reps, fm, w, r, fr, hmat)

def run_bench_op.p2(is2: Bool, is3: Bool, is4: Bool, reps: Nat, fm: P.FactorModel, a: L.Vec, w: L.Vec, r: L.Vec, fr: L.Vec, hmat: L.Mat) -> String:
  match is2:
    case True{}:
      "chk=" ++ F32.show(repeat_mvo_fn(reps, fm, a, 0.0)) ++ "\n"
    case False{}:
      run_bench_op.p3(is3, is4, reps, fm, w, r, fr, hmat)

def run_bench_op.p1(is1: Bool, is2: Bool, is3: Bool, is4: Bool, reps: Nat, fm: P.FactorModel, a: L.Vec, w: L.Vec, r: L.Vec, fr: L.Vec, hmat: L.Mat) -> String:
  match is1:
    case True{}:
      "chk=" ++ F32.show(repeat_mvo_tv(reps, fm, a, 0.0)) ++ "\n"
    case False{}:
      run_bench_op.p2(is2, is3, is4, reps, fm, a, w, r, fr, hmat)

def run_bench_op.pick(is0: Bool, is1: Bool, is2: Bool, is3: Bool, is4: Bool, reps: Nat, fm: P.FactorModel, a: L.Vec, w: L.Vec, r: L.Vec, fr: L.Vec, hmat: L.Mat) -> String:
  match is0:
    case True{}:
      "chk=" ++ F32.show(repeat_risk(reps, fm, w, 0.0)) ++ "\n"
    case False{}:
      run_bench_op.p1(is1, is2, is3, is4, reps, fm, a, w, r, fr, hmat)

def run_bench_op(
  +op: U32,
  +reps: Nat,
  rfm: Result<&1, &1, U32 & String, P.FactorModel>,
  ra: Result<&1, &1, U32 & String, L.Vec>,
  rw: Result<&1, &1, U32 & String, L.Vec>,
  rr: Result<&1, &1, U32 & String, L.Vec>,
  rfr: Result<&1, &1, U32 & String, L.Vec>,
  rh: Result<&1, &1, U32 & String, L.Mat>
) -> String:
  match rfm ra rw rr rfr rh:
    case Done{fm} Done{a} Done{w} Done{r} Done{fr} Done{hmat}:
      run_bench_op.pick(U32.is_eq(op, 0), U32.is_eq(op, 1), U32.is_eq(op, 2), U32.is_eq(op, 3), U32.is_eq(op, 4), reps, fm, a, w, r, fr, hmat)
    case _ _ _ _ _ _:
      "LOAD_FAIL\n"

def repeat_admm(rem: Nat, +fm: P.FactorModel, +a: L.Vec, +w0: L.Vec, +cons: P.Constraints, +costs: P.TradeCosts, +rho: F32, +cfg: P.OptConfig, last: String) -> String:
  match rem:
    case 0n:
      last ++ "\n"
    case 1n+p:
      repeat_admm(p, fm, a, w0, cons, costs, rho, cfg, opt_chk(P.mvo_constrained(fm, a, w0, cons, costs, rho, cfg)))

def run_admm_bench(
  +reps: Nat,
  rfm: Result<&1, &1, U32 & String, P.FactorModel>,
  ra: Result<&1, &1, U32 & String, L.Vec>,
  rw0: Result<&1, &1, U32 & String, L.Vec>,
  rlw: Result<&1, &1, U32 & String, L.Vec>,
  ruw: Result<&1, &1, U32 & String, L.Vec>,
  ram: Result<&1, &1, U32 & String, L.Mat>,
  rlc: Result<&1, &1, U32 & String, L.Vec>,
  ruc: Result<&1, &1, U32 & String, L.Vec>,
  rc1: Result<&1, &1, U32 & String, L.Vec>,
  rc2: Result<&1, &1, U32 & String, L.Vec>,
  rp: Result<&1, &1, U32 & String, L.Vec>,
  +max_it: U32
) -> String:
  match rfm ra rw0 rlw ruw ram:
    case Done{fm} Done{a} Done{w0} Done{lw} Done{uw} Done{am}:
      match rlc ruc rc1 rc2 rp:
        case Done{lc} Done{uc} Done{c1} Done{c2} Done{L.Vec{_, ps}}:
          match ps:
            case Con{rho, Con{gmv, Con{at, Con{rt, Con{ra_p, Con{rel, _}}}}}}:
              cons = {P.Constraints{lw, uw, am, lc, uc, gmv} : P.Constraints}
              costs = {P.TradeCosts{c1, c2} : P.TradeCosts}
              cfg = {P.OptConfig{max_it, at, rt, ra_p, rel} : P.OptConfig}
              repeat_admm(reps, fm, a, w0, cons, costs, rho, cfg, "")
            case _:
              "BAD_PARAMS\n"
        case _ _ _ _ _:
          "LOAD_FAIL\n"
    case _ _ _ _ _ _:
      "LOAD_FAIL\n"

def run_fpnl_bench(+reps: Nat, rw: Result<&1, &1, U32 & String, L.Mat>, rr: Result<&1, &1, U32 & String, L.Mat>) -> String:
  match rw rr:
    case Done{wm} Done{rm}:
      "chk=" ++ F32.show(repeat_fpnl(reps, wm, rm, 0.0)) ++ "\n"
    case _ _:
      "LOAD_FAIL\n"

def run_fattr_bench(
  +reps: Nat,
  +t: U32,
  rfm: Result<&1, &1, U32 & String, P.FactorModel>,
  rw: Result<&1, &1, U32 & String, L.Mat>,
  rr: Result<&1, &1, U32 & String, L.Mat>,
  rfr: Result<&1, &1, U32 & String, L.Mat>
) -> String:
  match rfm rw rr rfr:
    case Done{fm} Done{wm} Done{rm} Done{frm}:
      +fms = rep_fm(U32.to_nat(t), fm)
      "chk=" ++ F32.show(repeat_fattr(reps, fms, wm, rm, frm, 0.0)) ++ "\n"
    case _ _ _ _:
      "LOAD_FAIL\n"

def go_core(rest: List<String>) -> IO(Unit):
  match rest:
    case ops <> reps_s <> bp <> cfp <> dp <> ap <> wp <> rp <> frp <> hp <> ns <> ks <> ms <> _:
      +op = tu(ops)
      +reps = U32.to_nat(tu(reps_s))
      +n = tu(ns)
      +k = tu(ks)
      +m = tu(ms)
      do IO<Unit>:
        rfm : Result<&1, &1, U32 & String, P.FactorModel> <- PI.FactorModel.load(bp, cfp, dp, n, k)
        ra : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(ap, n)
        rw : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(wp, n)
        rr : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(rp, n)
        rfr : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(frp, k)
        rh : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(hp, n, m)
        IO.write(run_bench_op(op, reps, rfm, ra, rw, rr, rfr, rh))
    case _:
      IO.print("BAD_ARGS\n")

def go_admm(rest: List<String>) -> IO(Unit):
  match rest:
    case reps_s <> bp <> cfp <> dp <> ap <> w0p <> lwp <> uwp <> amp <> lcp <> ucp <> c1p <> c2p <> pp <> ns <> ks <> ms <> its <> _:
      +reps = U32.to_nat(tu(reps_s))
      +n = tu(ns)
      +k = tu(ks)
      +m = tu(ms)
      +max_it = tu(its)
      do IO<Unit>:
        rfm : Result<&1, &1, U32 & String, P.FactorModel> <- PI.FactorModel.load(bp, cfp, dp, n, k)
        ra : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(ap, n)
        rw0 : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(w0p, n)
        rlw : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(lwp, n)
        ruw : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(uwp, n)
        ram : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(amp, m, n)
        rlc : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(lcp, m)
        ruc : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(ucp, m)
        rc1 : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(c1p, n)
        rc2 : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(c2p, n)
        rp : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(pp, 6)
        IO.write(run_admm_bench(reps, rfm, ra, rw0, rlw, ruw, ram, rlc, ruc, rc1, rc2, rp, max_it))
    case _:
      IO.print("BAD_ARGS\n")

def go_fpnl(rest: List<String>) -> IO(Unit):
  match rest:
    case reps_s <> wp <> rp <> ts <> ns <> _:
      +reps = U32.to_nat(tu(reps_s))
      +t = tu(ts)
      +n = tu(ns)
      do IO<Unit>:
        rw : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(wp, t, n)
        rr : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(rp, t, n)
        IO.write(run_fpnl_bench(reps, rw, rr))
    case _:
      IO.print("BAD_ARGS\n")

def go_fattr(rest: List<String>) -> IO(Unit):
  match rest:
    case reps_s <> bp <> cfp <> dp <> wp <> rp <> frp <> ts <> ns <> ks <> _:
      +reps = U32.to_nat(tu(reps_s))
      +t = tu(ts)
      +n = tu(ns)
      +k = tu(ks)
      do IO<Unit>:
        rfm : Result<&1, &1, U32 & String, P.FactorModel> <- PI.FactorModel.load(bp, cfp, dp, n, k)
        rw : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(wp, t, n)
        rr : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(rp, t, n)
        rfr : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(frp, t, k)
        IO.write(run_fattr_bench(reps, t, rfm, rw, rr, rfr))
    case _:
      IO.print("BAD_ARGS\n")

def d23(is2: Bool, rest: List<String>) -> IO(Unit):
  match is2:
    case True{}:
      go_fpnl(rest)
    case False{}:
      go_fattr(rest)

def d12(is1: Bool, is2: Bool, rest: List<String>) -> IO(Unit):
  match is1:
    case True{}:
      go_admm(rest)
    case False{}:
      d23(is2, rest)

def d02(is0: Bool, is1: Bool, is2: Bool, rest: List<String>) -> IO(Unit):
  match is0:
    case True{}:
      go_core(rest)
    case False{}:
      d12(is1, is2, rest)

def go(args: List<String>) -> IO(Unit):
  match args:
    case _ <> mode <> rest:
      +m = tu(mode)
      d02(U32.is_eq(m, 0), U32.is_eq(m, 1), U32.is_eq(m, 2), rest)
    case _:
      IO.print("NO_ARGS\n")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
