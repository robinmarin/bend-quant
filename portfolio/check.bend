# CLI test driver for portfolio (Milestones 1-4).
# Invoked by check.py to verify every public function against NumPy / SciPy.
import Base
import bend-quant-linalg@0.1.0.0/linalg.bend as L
import bend-quant-linalg@0.1.0.0/io.bend as LI
import ./portfolio.bend as P
import ./io.bend as PI

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

def show_bool(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def show_risk(mr: Maybe<&2, P.RiskDecomp>) -> String:
  match mr:
    case Some{P.RiskDecomp{tv, fv, iv, tvol, fvol, ivol, pct, exp}}:
      "RISK " ++ F32.show(tv) ++ " " ++ F32.show(fv) ++ " " ++ F32.show(iv) ++ " " ++ F32.show(tvol) ++ " " ++ F32.show(fvol) ++ " " ++ F32.show(ivol) ++ " " ++ F32.show(pct) ++ "\n" ++ show_vec(exp)
    case None{}:
      "NONE\n"

def show_alpha_decomp(ma: Maybe<&2, P.AlphaDecomp>) -> String:
  match ma:
    case Some{P.AlphaDecomp{fa, sp, orth}}:
      show_vec(fa) ++ show_vec(sp) ++ show_vec(orth)
    case None{}:
      "NONE\n"

def show_opt(mo: Maybe<&2, P.OptResult>) -> String:
  match mo:
    case Some{P.OptResult{w, it, rp, rd, conv}}:
      "OPT " ++ U32.show(it) ++ " " ++ F32.show(rp) ++ " " ++ F32.show(rd) ++ " " ++ show_bool(conv) ++ "\n" ++ show_vec(w)
    case None{}:
      "NONE\n"

def show_shrink(ms: Maybe<&2, P.HedgeShrink>) -> String:
  match ms:
    case Some{P.HedgeShrink{raw, ev, yh, xh}}:
      "SHRINK " ++ F32.show(raw) ++ " " ++ F32.show(ev) ++ " " ++ F32.show(yh) ++ " " ++ F32.show(xh) ++ "\n"
    case None{}:
      "NONE\n"

def show_dd_list(xs: List<&2, P.DrawdownState>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{P.DrawdownState{w, m, d, f}, t}:
      F32.show(w) ++ " " ++ F32.show(m) ++ " " ++ F32.show(d) ++ " " ++ F32.show(f) ++ "\n" ++ show_dd_list(t)

def show_mdd(mxs: Maybe<&2, List<&2, P.DrawdownState>>) -> String:
  match mxs:
    case Some{+xs}:
      "DD " ++ U32.show(U32.from_nat(List.length(&2, P.DrawdownState, xs))) ++ "\n" ++ show_dd_list(xs)
    case None{}:
      "NONE\n"

def show_pattr(mp: Maybe<&2, P.PeriodAttrib>) -> String:
  match mp:
    case Some{P.PeriodAttrib{pos, tr, fp, ip, fc, ic, ev}}:
      "PATTR " ++ F32.show(pos) ++ " " ++ F32.show(tr) ++ " " ++ F32.show(fp) ++ " " ++ F32.show(ip) ++ " " ++ F32.show(ev) ++ "\n" ++ show_vec(fc) ++ show_vec(ic)
    case None{}:
      "NONE\n"

def show_mattr(mm: Maybe<&2, P.MaxAttrib>) -> String:
  match mm:
    case Some{P.MaxAttrib{adj, sp, rf, rp, rc}}:
      "MATTR " ++ F32.show(sp) ++ " " ++ F32.show(rp) ++ "\n" ++ show_vec(adj) ++ show_vec(rf) ++ show_mat(rc)
    case None{}:
      "NONE\n"

def show_ng_list(xs: List<&2, P.NestedGroup>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{P.NestedGroup{adj, pnl}, t}:
      "NG " ++ F32.show(pnl) ++ "\n" ++ show_vec(adj) ++ show_ng_list(t)

def show_mng(mxs: Maybe<&2, List<&2, P.NestedGroup>>) -> String:
  match mxs:
    case Some{+xs}:
      "NESTED " ++ U32.show(U32.from_nat(List.length(&2, P.NestedGroup, xs))) ++ "\n" ++ show_ng_list(xs)
    case None{}:
      "NONE\n"

def show_ss(ms: Maybe<&2, P.SelectionSizing>) -> String:
  match ms:
    case Some{P.SelectionSizing{ir, sel, div, siz, sl, ss, ql, qs}}:
      "SS " ++ F32.show(ir) ++ " " ++ F32.show(sel) ++ " " ++ F32.show(div) ++ " " ++ F32.show(siz) ++ " " ++ F32.show(sl) ++ " " ++ F32.show(ss) ++ " " ++ F32.show(ql) ++ " " ++ F32.show(qs) ++ "\n"
    case None{}:
      "NONE\n"

def show_mlist_f32(mxs: Maybe<&2, List<&2, F32>>) -> String:
  match mxs:
    case Some{+xs}:
      "VEC " ++ U32.show(U32.from_nat(List.length(&2, F32, xs))) ++ "\n" ++ show_list_f32(xs) ++ "\n"
    case None{}:
      "NONE\n"

def show_pattr_list(xs: List<&2, Maybe<&2, P.PeriodAttrib>>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      show_pattr(h) ++ show_pattr_list(t)

def show_mpattr_list(mxs: Maybe<&2, List<&2, Maybe<&2, P.PeriodAttrib>>>) -> String:
  match mxs:
    case Some{+xs}:
      "FATTR " ++ U32.show(U32.from_nat(List.length(&2, Maybe<&2, P.PeriodAttrib>, xs))) ++ "\n" ++ show_pattr_list(xs)
    case None{}:
      "NONE\n"

# ---- Mode 0: Risk ----

def run_risk.go(+fm: P.FactorModel, +w: L.Vec, wb: L.Vec) -> String:
  P.FactorModel{_, _, d} = fm
  s0 = show_mvec(P.exposures(fm, w))
  s1 = show_mvec(P.cov_matvec(fm, w))
  s2 = show_risk(P.risk_decomp(fm, w))
  s3 = show_risk(P.active_risk(fm, w, wb))
  s4 = show_mvec(P.marginal_risk(fm, w))
  s5 = show_mvec(P.risk_contrib(fm, w))
  s6 = "F32 " ++ F32.show(P.herfindahl(w)) ++ "\n"
  s7 = show_mf32(P.eff_breadth(w, d))
  s0 ++ s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6 ++ s7

def run_risk(rfm: Result<&1, &1, U32 & String, P.FactorModel>, rw: Result<&1, &1, U32 & String, L.Vec>, rwb: Result<&1, &1, U32 & String, L.Vec>) -> String:
  match rfm rw rwb:
    case Done{fm} Done{w} Done{wb}:
      run_risk.go(fm, w, wb)
    case _ _ _:
      "LOAD_FAIL\n"

# ---- Mode 1: Analytical MVO ----

def run_mvo_params(+fm: P.FactorModel, +a: L.Vec, w0: L.Vec, cq: L.Vec, lf: L.Vec, ps: List<&2, F32>) -> String:
  match ps:
    case Con{+rho, Con{+tvol, Con{tau_sq, _}}}:
      s0 = show_mvec(P.mvo_unconstrained(fm, a, rho))
      s1 = show_mvec(P.mvo_target_vol(fm, a, tvol))
      s2 = show_mvec(P.mvo_robust(fm, a, rho, tau_sq))
      s3 = show_mvec(P.mvo_trade_quad(fm, a, w0, cq, rho))
      s4 = show_mmat(P.fmp(fm))
      s5 = show_alpha_decomp(P.alpha_decompose(fm, a))
      s6 = show_mvec(P.mvo_factor_neutral(fm, a, tvol))
      s7 = show_mvec(P.mvo_factor_space(fm, lf, rho))
      s0 ++ s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6 ++ s7
    case _:
      "BAD_PARAMS\n"

def run_mvo(rfm: Result<&1, &1, U32 & String, P.FactorModel>, ra: Result<&1, &1, U32 & String, L.Vec>, rw0: Result<&1, &1, U32 & String, L.Vec>, rcq: Result<&1, &1, U32 & String, L.Vec>, rlf: Result<&1, &1, U32 & String, L.Vec>, rp: Result<&1, &1, U32 & String, L.Vec>) -> String:
  match rfm ra rw0 rcq rlf rp:
    case Done{fm} Done{a} Done{w0} Done{cq} Done{lf} Done{L.Vec{_, ps}}:
      run_mvo_params(fm, a, w0, cq, lf, ps)
    case _ _ _ _ _ _:
      "LOAD_FAIL\n"

# ---- Mode 2: SRE ----

def run_sre(rfme: Result<&1, &1, U32 & String, P.FactorModel>, rae: Result<&1, &1, U32 & String, L.Vec>, rfmt: Result<&1, &1, U32 & String, P.FactorModel>, rat: Result<&1, &1, U32 & String, L.Vec>) -> String:
  match rfme rae rfmt rat:
    case Done{fme} Done{ae} Done{fmt} Done{at}:
      show_mf32(P.sre(fme, ae, fmt, at))
    case _ _ _ _:
      "LOAD_FAIL\n"

# ---- Mode 3: Constrained MVO (ADMM) ----

def run_con_params(fm: P.FactorModel, a: L.Vec, w0: L.Vec, lw: L.Vec, uw: L.Vec, amat: L.Mat, lc: L.Vec, uc: L.Vec, c1: L.Vec, c2: L.Vec, ps: List<&2, F32>, +max_it: U32) -> String:
  match ps:
    case Con{rho, Con{gmv, Con{abs_t, Con{rel_t, Con{radmm, Con{relax, _}}}}}}:
      cons = {P.Constraints{lw, uw, amat, lc, uc, gmv} : P.Constraints}
      costs = {P.TradeCosts{c1, c2} : P.TradeCosts}
      cfg = {P.OptConfig{max_it, abs_t, rel_t, radmm, relax} : P.OptConfig}
      show_opt(P.mvo_constrained(fm, a, w0, cons, costs, rho, cfg))
    case _:
      "BAD_PARAMS\n"

def run_con2(rfm: Result<&1, &1, U32 & String, P.FactorModel>, ra: Result<&1, &1, U32 & String, L.Vec>, rw0: Result<&1, &1, U32 & String, L.Vec>, rlw: Result<&1, &1, U32 & String, L.Vec>, ruw: Result<&1, &1, U32 & String, L.Vec>, ramat: Result<&1, &1, U32 & String, L.Mat>, rlc: Result<&1, &1, U32 & String, L.Vec>, ruc: Result<&1, &1, U32 & String, L.Vec>, rc1: Result<&1, &1, U32 & String, L.Vec>, rc2: Result<&1, &1, U32 & String, L.Vec>, rp: Result<&1, &1, U32 & String, L.Vec>, +max_it: U32) -> String:
  match rfm ra rw0 rlw ruw ramat:
    case Done{fm} Done{a} Done{w0} Done{lw} Done{uw} Done{amat}:
      match rlc ruc rc1 rc2 rp:
        case Done{lc} Done{uc} Done{c1} Done{c2} Done{L.Vec{_, ps}}:
          run_con_params(fm, a, w0, lw, uw, amat, lc, uc, c1, c2, ps, max_it)
        case _ _ _ _ _:
          "LOAD_FAIL\n"
    case _ _ _ _ _ _:
      "LOAD_FAIL\n"

# ---- Mode 4: Trade Costs ----

def run_tc_params(+w: L.Vec, +w0: L.Vec, c1: L.Vec, c2: L.Vec, sig: L.Vec, adv: L.Vec, ps: List<&2, F32>) -> String:
  match ps:
    case Con{kappa, Con{beta, _}}:
      s0 = show_mf32(P.trade_cost_linear(w, w0, c1))
      s1 = show_mf32(P.trade_cost_quad(w, w0, c2))
      s2 = show_mf32(P.trade_cost_power(w, w0, kappa, sig, adv, beta))
      s0 ++ s1 ++ s2
    case _:
      "BAD_PARAMS\n"

def run_tc(rw: Result<&1, &1, U32 & String, L.Vec>, rw0: Result<&1, &1, U32 & String, L.Vec>, rc1: Result<&1, &1, U32 & String, L.Vec>, rc2: Result<&1, &1, U32 & String, L.Vec>, rsig: Result<&1, &1, U32 & String, L.Vec>, radv: Result<&1, &1, U32 & String, L.Vec>, rp: Result<&1, &1, U32 & String, L.Vec>) -> String:
  match rw rw0 rc1 rc2 rsig radv:
    case Done{w} Done{w0} Done{c1} Done{c2} Done{sig} Done{adv}:
      match rp:
        case Done{L.Vec{_, ps}}:
          run_tc_params(w, w0, c1, c2, sig, adv, ps)
        case Fail{_}:
          "LOAD_FAIL\n"
    case _ _ _ _ _ _:
      "LOAD_FAIL\n"

# ---- Mode 5: Hedging (Ch 12) ----

def run_hedge_params(+fm: P.FactorModel, +wc: L.Vec, wh: L.Vec, hmat: L.Mat, +bh: L.Vec, +se: L.Vec, ceta: L.Mat, ps: List<&2, F32>) -> String:
  match ps:
    case Con{+mu_h, Con{+sig_h, _}}:
      s0 = show_mf32(P.hedge_ratio_model(fm, wc, wh))
      s1 = show_mvec(P.hedge_instruments(fm, wc, hmat))
      s2 = show_mvec(P.hedge_factor_exact(fm, wc))
      s3 = show_shrink(P.hedge_beta_shrink(wc, bh, se))
      s4 = show_shrink(P.hedge_beta_shrink_cov(wc, bh, ceta))
      s5 = show_mvec(P.hedge_track_series(fm, bh, se, mu_h, sig_h))
      s6 = show_mvec(P.hedge_track_series(fm, bh, se, 0.0, sig_h))
      s0 ++ s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6
    case _:
      "BAD_PARAMS\n"

def run_hedge(rfm: Result<&1, &1, U32 & String, P.FactorModel>, rwc: Result<&1, &1, U32 & String, L.Vec>, rwh: Result<&1, &1, U32 & String, L.Vec>, rhmat: Result<&1, &1, U32 & String, L.Mat>, rbh: Result<&1, &1, U32 & String, L.Vec>, rse: Result<&1, &1, U32 & String, L.Vec>, rceta: Result<&1, &1, U32 & String, L.Mat>, rp: Result<&1, &1, U32 & String, L.Vec>) -> String:
  match rfm rwc rwh rhmat rbh rse:
    case Done{fm} Done{wc} Done{wh} Done{hmat} Done{bh} Done{se}:
      match rceta rp:
        case Done{ceta} Done{L.Vec{_, ps}}:
          run_hedge_params(fm, wc, wh, hmat, bh, se, ceta, ps)
        case _ _:
          "LOAD_FAIL\n"
    case _ _ _ _ _ _:
      "LOAD_FAIL\n"

# ---- Mode 6: Dynamic Sizing (Ch 13) ----

def run_sizing_params(rets: List<&2, F32>, ps: List<&2, F32>) -> String:
  match ps:
    case Con{+mu, Con{+sig, Con{+frac, Con{+max_dd, Con{+cur_dd, _}}}}}:
      s0 = show_mf32(P.kelly_fraction(mu, sig))
      s1 = show_mf32(P.kelly_fraction_discrete(mu, sig))
      s2 = show_mf32(P.fractional_kelly(mu, sig, frac))
      s3 = show_mf32(P.grossman_zhou(mu, sig, max_dd, cur_dd))
      s4 = show_mf32(P.grossman_zhou(mu, sig, max_dd, max_dd))
      s5 = show_mdd(P.grossman_zhou_path(rets, mu, sig, max_dd))
      s0 ++ s1 ++ s2 ++ s3 ++ s4 ++ s5
    case _:
      "BAD_PARAMS\n"

def run_sizing(rr: Result<&1, &1, U32 & String, L.Vec>, rp: Result<&1, &1, U32 & String, L.Vec>) -> String:
  match rr rp:
    case Done{L.Vec{_, rets}} Done{L.Vec{_, ps}}:
      run_sizing_params(rets, ps)
    case _ _:
      "LOAD_FAIL\n"

# ---- Mode 7: Attribution (Ch 14) ----

def run_attrib_max(mb: Maybe<&2, L.Vec>, +cf: L.Mat, +fr: L.Vec) -> String:
  match mb:
    case Some{+b}:
      show_mattr(P.maximal_attribution(cf, b, fr, [0, 2])) ++ show_mng(P.nested_attribution(cf, b, fr, [[0, 2], [1, 3], [4, 5]]))
    case None{}:
      "NONE\nNONE\n"

def run_attrib_params(+fm: P.FactorModel, +w: L.Vec, +r: L.Vec, +fr: L.Vec, eps: L.Vec, ps: List<&2, F32>) -> String:
  P.FactorModel{_, +cf, d} = fm
  match ps:
    case Con{+rpnl, _}:
      s0 = show_mvec(P.estimate_factor_returns(fm, r))
      s1 = show_mf32(P.attrib_error_var(fm, w))
      s2 = show_pattr(P.attribute_period(fm, w, r, fr, rpnl))
      mb = P.exposures(fm, w)
      s3 = run_attrib_max(mb, cf, fr)
      s4 = show_ss(P.selection_sizing(w, eps, d))
      s0 ++ s1 ++ s2 ++ s3 ++ s4
    case _:
      "BAD_PARAMS\n"

def run_attrib(rfm: Result<&1, &1, U32 & String, P.FactorModel>, rw: Result<&1, &1, U32 & String, L.Vec>, rr: Result<&1, &1, U32 & String, L.Vec>, rfr: Result<&1, &1, U32 & String, L.Vec>, reps: Result<&1, &1, U32 & String, L.Vec>, rp: Result<&1, &1, U32 & String, L.Vec>) -> String:
  match rfm rw rr rfr reps rp:
    case Done{fm} Done{w} Done{r} Done{fr} Done{eps} Done{L.Vec{_, ps}}:
      run_attrib_params(fm, w, r, fr, eps, ps)
    case _ _ _ _ _ _:
      "LOAD_FAIL\n"

# ---- Mode 8: Forward PnL & Forward Attribution ----

def run_forward(rfm: Result<&1, &1, U32 & String, P.FactorModel>, rw: Result<&1, &1, U32 & String, L.Mat>, rr: Result<&1, &1, U32 & String, L.Mat>, rfr: Result<&1, &1, U32 & String, L.Mat>, +t: U32) -> String:
  match rfm rw rr rfr:
    case Done{fm} Done{+w} Done{+r} Done{fr}:
      fms = List.replicate(P.FactorModel, U32.to_nat(t), fm)
      show_mlist_f32(P.forward_pnl(w, r)) ++ show_mpattr_list(P.forward_attribute(fms, w, r, fr))
    case _ _ _ _:
      "LOAD_FAIL\n"

# ---- CLI dispatch ----

def go_risk(rest: List<String>) -> IO(Unit):
  match rest:
    case bp <> cfp <> dp <> wp <> wbp <> ns <> ks <> _:
      +n = tu(ns)
      +k = tu(ks)
      do IO<Unit>:
        rfm : Result<&1, &1, U32 & String, P.FactorModel> <- PI.FactorModel.load(bp, cfp, dp, n, k)
        rw : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(wp, n)
        rwb : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(wbp, n)
        IO.write(run_risk(rfm, rw, rwb))
    case _:
      IO.print("BAD_ARGS\n")

def go_mvo(rest: List<String>) -> IO(Unit):
  match rest:
    case bp <> cfp <> dp <> ap <> w0p <> cqp <> lfp <> pp <> ns <> ks <> _:
      +n = tu(ns)
      +k = tu(ks)
      do IO<Unit>:
        rfm : Result<&1, &1, U32 & String, P.FactorModel> <- PI.FactorModel.load(bp, cfp, dp, n, k)
        ra : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(ap, n)
        rw0 : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(w0p, n)
        rcq : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(cqp, n)
        rlf : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(lfp, k)
        rp : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(pp, 3)
        IO.write(run_mvo(rfm, ra, rw0, rcq, rlf, rp))
    case _:
      IO.print("BAD_ARGS\n")

def go_sre(rest: List<String>) -> IO(Unit):
  match rest:
    case bep <> cfep <> dep <> aep <> btp <> cftp <> dtp <> atp <> ns <> ks <> _:
      +n = tu(ns)
      +k = tu(ks)
      do IO<Unit>:
        rfme : Result<&1, &1, U32 & String, P.FactorModel> <- PI.FactorModel.load(bep, cfep, dep, n, k)
        rae : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(aep, n)
        rfmt : Result<&1, &1, U32 & String, P.FactorModel> <- PI.FactorModel.load(btp, cftp, dtp, n, k)
        rat : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(atp, n)
        IO.write(run_sre(rfme, rae, rfmt, rat))
    case _:
      IO.print("BAD_ARGS\n")

def go_con(rest: List<String>) -> IO(Unit):
  match rest:
    case bp <> cfp <> dp <> ap <> w0p <> lwp <> uwp <> amatp <> lcp <> ucp <> c1p <> c2p <> pp <> ns <> ks <> ms <> its <> _:
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
        ramat : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(amatp, m, n)
        rlc : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(lcp, m)
        ruc : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(ucp, m)
        rc1 : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(c1p, n)
        rc2 : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(c2p, n)
        rp : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(pp, 6)
        IO.write(run_con2(rfm, ra, rw0, rlw, ruw, ramat, rlc, ruc, rc1, rc2, rp, max_it))
    case _:
      IO.print("BAD_ARGS\n")

def go_tc(rest: List<String>) -> IO(Unit):
  match rest:
    case wp <> w0p <> c1p <> c2p <> sigp <> advp <> pp <> ns <> _:
      +n = tu(ns)
      do IO<Unit>:
        rw : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(wp, n)
        rw0 : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(w0p, n)
        rc1 : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(c1p, n)
        rc2 : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(c2p, n)
        rsig : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(sigp, n)
        radv : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(advp, n)
        rp : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(pp, 2)
        IO.write(run_tc(rw, rw0, rc1, rc2, rsig, radv, rp))
    case _:
      IO.print("BAD_ARGS\n")

def go_hedge(rest: List<String>) -> IO(Unit):
  match rest:
    case bp <> cfp <> dp <> wcp <> whp <> hmatp <> bhp <> sep <> cetap <> pp <> ns <> ks <> ms <> _:
      +n = tu(ns)
      +k = tu(ks)
      +m = tu(ms)
      do IO<Unit>:
        rfm : Result<&1, &1, U32 & String, P.FactorModel> <- PI.FactorModel.load(bp, cfp, dp, n, k)
        rwc : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(wcp, n)
        rwh : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(whp, n)
        rhmat : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(hmatp, n, m)
        rbh : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(bhp, n)
        rse : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(sep, n)
        rceta : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(cetap, n, n)
        rp : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(pp, 2)
        IO.write(run_hedge(rfm, rwc, rwh, rhmat, rbh, rse, rceta, rp))
    case _:
      IO.print("BAD_ARGS\n")

def go_sizing(rest: List<String>) -> IO(Unit):
  match rest:
    case rp_ret <> pp <> ts <> _:
      +t = tu(ts)
      do IO<Unit>:
        rr : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(rp_ret, t)
        rp : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(pp, 5)
        IO.write(run_sizing(rr, rp))
    case _:
      IO.print("BAD_ARGS\n")

def go_attrib(rest: List<String>) -> IO(Unit):
  match rest:
    case bp <> cfp <> dp <> wp <> rp_r <> frp <> epsp <> pp <> ns <> ks <> _:
      +n = tu(ns)
      +k = tu(ks)
      do IO<Unit>:
        rfm : Result<&1, &1, U32 & String, P.FactorModel> <- PI.FactorModel.load(bp, cfp, dp, n, k)
        rw : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(wp, n)
        rr : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(rp_r, n)
        rfr : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(frp, k)
        reps : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(epsp, n)
        rp : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(pp, 1)
        IO.write(run_attrib(rfm, rw, rr, rfr, reps, rp))
    case _:
      IO.print("BAD_ARGS\n")

def go_forward(rest: List<String>) -> IO(Unit):
  match rest:
    case bp <> cfp <> dp <> wp <> rp_r <> frp <> ts <> ns <> ks <> _:
      +t = tu(ts)
      +n = tu(ns)
      +k = tu(ks)
      do IO<Unit>:
        rfm : Result<&1, &1, U32 & String, P.FactorModel> <- PI.FactorModel.load(bp, cfp, dp, n, k)
        rw : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(wp, t, n)
        rr : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(rp_r, t, n)
        rfr : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(frp, t, k)
        IO.write(run_forward(rfm, rw, rr, rfr, t))
    case _:
      IO.print("BAD_ARGS\n")

def d78(is7: Bool, rest: List<String>) -> IO(Unit):
  match is7:
    case True{}:
      go_attrib(rest)
    case False{}:
      go_forward(rest)

def d68(is6: Bool, is7: Bool, rest: List<String>) -> IO(Unit):
  match is6:
    case True{}:
      go_sizing(rest)
    case False{}:
      d78(is7, rest)

def d58(is5: Bool, is6: Bool, is7: Bool, rest: List<String>) -> IO(Unit):
  match is5:
    case True{}:
      go_hedge(rest)
    case False{}:
      d68(is6, is7, rest)

def d48(is4: Bool, is5: Bool, is6: Bool, is7: Bool, rest: List<String>) -> IO(Unit):
  match is4:
    case True{}:
      go_tc(rest)
    case False{}:
      d58(is5, is6, is7, rest)

def d38(is3: Bool, is4: Bool, is5: Bool, is6: Bool, is7: Bool, rest: List<String>) -> IO(Unit):
  match is3:
    case True{}:
      go_con(rest)
    case False{}:
      d48(is4, is5, is6, is7, rest)

def d28(is2: Bool, is3: Bool, is4: Bool, is5: Bool, is6: Bool, is7: Bool, rest: List<String>) -> IO(Unit):
  match is2:
    case True{}:
      go_sre(rest)
    case False{}:
      d38(is3, is4, is5, is6, is7, rest)

def d18(is1: Bool, is2: Bool, is3: Bool, is4: Bool, is5: Bool, is6: Bool, is7: Bool, rest: List<String>) -> IO(Unit):
  match is1:
    case True{}:
      go_mvo(rest)
    case False{}:
      d28(is2, is3, is4, is5, is6, is7, rest)

def dispatch(is0: Bool, is1: Bool, is2: Bool, is3: Bool, is4: Bool, is5: Bool, is6: Bool, is7: Bool, rest: List<String>) -> IO(Unit):
  match is0:
    case True{}:
      go_risk(rest)
    case False{}:
      d18(is1, is2, is3, is4, is5, is6, is7, rest)

def go(args: List<String>) -> IO(Unit):
  match args:
    case _ <> mode <> rest:
      +m = tu(mode)
      dispatch(U32.is_eq(m, 0), U32.is_eq(m, 1), U32.is_eq(m, 2), U32.is_eq(m, 3), U32.is_eq(m, 4), U32.is_eq(m, 5), U32.is_eq(m, 6), U32.is_eq(m, 7), rest)
    case _:
      IO.print("NO_ARGS\n")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
