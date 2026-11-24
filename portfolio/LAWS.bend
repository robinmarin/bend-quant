# Laws for portfolio. The checker doesn't run F32 arithmetic, so numerical
# values are verified against NumPy / SciPy in check.py. These laws prove
# structural, validation, and causal invariants for every input.
import Base
import bend-quant-linalg@0.1.0.0/linalg.bend as L
import ./portfolio.bend as P

# ---------------------------------------------------------------- FactorModel validation

law fm_new_mismatch_n:
  for +bm: U32
  for +bn: U32
  for +brows: List<&2, List<&2, F32>>
  for +cf: L.Mat
  for +dn: U32
  for +ds: List<&2, F32>
  for h: {U32.is_eq(bm, dn) == False{} : Bool}
  {P.FactorModel.new(L.Mat{bm, bn, brows}, cf, L.Vec{dn, ds}) == None{} : Maybe<&2, P.FactorModel>}

law fm_new_mismatch_k:
  for +bm: U32
  for +bn: U32
  for +brows: List<&2, List<&2, F32>>
  for +cm: U32
  for +cn: U32
  for +crows: List<&2, List<&2, F32>>
  for +d: L.Vec
  for h: {U32.is_eq(bn, cm) == False{} : Bool}
  {P.FactorModel.new(L.Mat{bm, bn, brows}, L.Mat{cm, cn, crows}, d) == None{} : Maybe<&2, P.FactorModel>}

law fm_new_nonsquare_cov:
  for +b: L.Mat
  for +cm: U32
  for +cn: U32
  for +crows: List<&2, List<&2, F32>>
  for +d: L.Vec
  for h: {U32.is_eq(cm, cn) == False{} : Bool}
  {P.FactorModel.new(b, L.Mat{cm, cn, crows}, d) == None{} : Maybe<&2, P.FactorModel>}

law fm_new_sound:
  for +b: L.Mat
  for +cf: L.Mat
  for +d: L.Vec
  for +fm: P.FactorModel
  for h: {P.FactorModel.new(b, cf, d) == Some{fm} : Maybe<&2, P.FactorModel>}
  {P.fm_dims_ok(b, cf, d) == True{} : Bool}

# B claims 2 rows but has 1: rejected even though every header agrees.
law fm_new_short_rows:
  {P.FactorModel.new(L.Mat{2, 1, [[1.0]]}, L.Mat{1, 1, [[1.0]]}, L.Vec{2, [1.0, 1.0]}) == None{} : Maybe<&2, P.FactorModel>}

# A FactorModel from FactorModel.new has headers that match its rows.
law fm_new_rows_ok:
  for +b: L.Mat
  for +cf: L.Mat
  for +d: L.Vec
  for +fm: P.FactorModel
  for h: {P.FactorModel.new(b, cf, d) == Some{fm} : Maybe<&2, P.FactorModel>}
  {P.fm_rows_ok(b, cf, d) == True{} : Bool}

# ---------------------------------------------------------------- dimension guards

law exposures_mismatch:
  for +bm: U32
  for +bn: U32
  for +brows: List<&2, List<&2, F32>>
  for +cf: L.Mat
  for +d: L.Vec
  for +wn: U32
  for +ws: List<&2, F32>
  for h: {U32.is_eq(bm, wn) == False{} : Bool}
  {P.exposures(P.FactorModel{L.Mat{bm, bn, brows}, cf, d}, L.Vec{wn, ws}) == None{} : Maybe<&2, L.Vec>}

law cov_matvec_mismatch:
  for +bm: U32
  for +bn: U32
  for +brows: List<&2, List<&2, F32>>
  for +cf: L.Mat
  for +d: L.Vec
  for +wn: U32
  for +ws: List<&2, F32>
  for h: {U32.is_eq(bm, wn) == False{} : Bool}
  {P.cov_matvec(P.FactorModel{L.Mat{bm, bn, brows}, cf, d}, L.Vec{wn, ws}) == None{} : Maybe<&2, L.Vec>}

law risk_decomp_mismatch:
  for +bm: U32
  for +bn: U32
  for +brows: List<&2, List<&2, F32>>
  for +cf: L.Mat
  for +d: L.Vec
  for +wn: U32
  for +ws: List<&2, F32>
  for h: {U32.is_eq(bm, wn) == False{} : Bool}
  {P.risk_decomp(P.FactorModel{L.Mat{bm, bn, brows}, cf, d}, L.Vec{wn, ws}) == None{} : Maybe<&2, P.RiskDecomp>}

law active_risk_mismatch:
  for +fm: P.FactorModel
  for +wn: U32
  for +ws: List<&2, F32>
  for +bn: U32
  for +bs: List<&2, F32>
  for h: {U32.is_eq(wn, bn) == False{} : Bool}
  {P.active_risk(fm, L.Vec{wn, ws}, L.Vec{bn, bs}) == None{} : Maybe<&2, P.RiskDecomp>}

law marginal_risk_mismatch:
  for +bm: U32
  for +bn: U32
  for +brows: List<&2, List<&2, F32>>
  for +cf: L.Mat
  for +d: L.Vec
  for +wn: U32
  for +ws: List<&2, F32>
  for h: {U32.is_eq(bm, wn) == False{} : Bool}
  {P.marginal_risk(P.FactorModel{L.Mat{bm, bn, brows}, cf, d}, L.Vec{wn, ws}) == None{} : Maybe<&2, L.Vec>}

law risk_contrib_mismatch:
  for +bm: U32
  for +bn: U32
  for +brows: List<&2, List<&2, F32>>
  for +cf: L.Mat
  for +d: L.Vec
  for +wn: U32
  for +ws: List<&2, F32>
  for h: {U32.is_eq(bm, wn) == False{} : Bool}
  {P.risk_contrib(P.FactorModel{L.Mat{bm, bn, brows}, cf, d}, L.Vec{wn, ws}) == None{} : Maybe<&2, L.Vec>}

law eff_breadth_mismatch:
  for +wn: U32
  for +ws: List<&2, F32>
  for +dn: U32
  for +ds: List<&2, F32>
  for h: {U32.is_eq(wn, dn) == False{} : Bool}
  {P.eff_breadth(L.Vec{wn, ws}, L.Vec{dn, ds}) == None{} : Maybe<&2, F32>}

law mvo_trade_quad_mismatch:
  for +bm: U32
  for +bn: U32
  for +brows: List<&2, List<&2, F32>>
  for +cf: L.Mat
  for +d: L.Vec
  for +an: U32
  for +as: List<&2, F32>
  for +w0: L.Vec
  for +cq: L.Vec
  for +rho: F32
  for h: {U32.is_eq(bm, an) == False{} : Bool}
  {P.mvo_trade_quad(P.FactorModel{L.Mat{bm, bn, brows}, cf, d}, L.Vec{an, as}, w0, cq, rho) == None{} : Maybe<&2, L.Vec>}

law fmp_mismatch:
  for +bm: U32
  for +bn: U32
  for +brows: List<&2, List<&2, F32>>
  for +cf: L.Mat
  for +dn: U32
  for +ds: List<&2, F32>
  for h: {U32.is_eq(bm, dn) == False{} : Bool}
  {P.fmp(P.FactorModel{L.Mat{bm, bn, brows}, cf, L.Vec{dn, ds}}) == None{} : Maybe<&2, L.Mat>}

law alpha_decomp_mismatch:
  for +bm: U32
  for +bn: U32
  for +brows: List<&2, List<&2, F32>>
  for +cf: L.Mat
  for +dn: U32
  for +ds: List<&2, F32>
  for +an: U32
  for +as: List<&2, F32>
  for h: {U32.is_eq(bm, an) == False{} : Bool}
  {P.alpha_decompose(P.FactorModel{L.Mat{bm, bn, brows}, cf, L.Vec{dn, ds}}, L.Vec{an, as}) == None{} : Maybe<&2, P.AlphaDecomp>}

law mvo_fn_mismatch:
  for +bm: U32
  for +bn: U32
  for +brows: List<&2, List<&2, F32>>
  for +cf: L.Mat
  for +dn: U32
  for +ds: List<&2, F32>
  for +an: U32
  for +as: List<&2, F32>
  for +tv: F32
  for h: {U32.is_eq(bm, an) == False{} : Bool}
  {P.mvo_factor_neutral(P.FactorModel{L.Mat{bm, bn, brows}, cf, L.Vec{dn, ds}}, L.Vec{an, as}, tv) == None{} : Maybe<&2, L.Vec>}

law mvo_fspace_mismatch:
  for +bm: U32
  for +bn: U32
  for +brows: List<&2, List<&2, F32>>
  for +cm: U32
  for +cn: U32
  for +crows: List<&2, List<&2, F32>>
  for +d: L.Vec
  for +ln: U32
  for +ls: List<&2, F32>
  for +rho: F32
  for h: {U32.is_eq(cm, ln) == False{} : Bool}
  {P.mvo_factor_space(P.FactorModel{L.Mat{bm, bn, brows}, L.Mat{cm, cn, crows}, d}, L.Vec{ln, ls}, rho) == None{} : Maybe<&2, L.Vec>}

# ---------------------------------------------------------------- transaction costs & constrained MVO (Ch 10.2, 11)

law trade_cost_linear_mismatch:
  for +wn: U32
  for ws: List<&2, F32>
  for +w0n: U32
  for w0s: List<&2, F32>
  for +cn: U32
  for cs: List<&2, F32>
  for h: {U32.is_eq(wn, w0n) == False{} : Bool}
  {P.trade_cost_linear(L.Vec{wn, ws}, L.Vec{w0n, w0s}, L.Vec{cn, cs}) == None{} : Maybe<&2, F32>}

law trade_cost_quad_mismatch:
  for +wn: U32
  for ws: List<&2, F32>
  for +w0n: U32
  for w0s: List<&2, F32>
  for +cn: U32
  for cs: List<&2, F32>
  for h: {U32.is_eq(wn, w0n) == False{} : Bool}
  {P.trade_cost_quad(L.Vec{wn, ws}, L.Vec{w0n, w0s}, L.Vec{cn, cs}) == None{} : Maybe<&2, F32>}

law trade_cost_power_mismatch:
  for +wn: U32
  for ws: List<&2, F32>
  for +w0n: U32
  for w0s: List<&2, F32>
  for +kappa: F32
  for +sn: U32
  for sigs: List<&2, F32>
  for +an: U32
  for advs: List<&2, F32>
  for +beta: F32
  for h: {U32.is_eq(wn, w0n) == False{} : Bool}
  {P.trade_cost_power(L.Vec{wn, ws}, L.Vec{w0n, w0s}, kappa, L.Vec{sn, sigs}, L.Vec{an, advs}, beta) == None{} : Maybe<&2, F32>}

law mvo_con_mismatch_alpha:
  for +bm: U32
  for +bn: U32
  for +brows: List<&2, List<&2, F32>>
  for +cf: L.Mat
  for +d: L.Vec
  for +an: U32
  for +as: List<&2, F32>
  for +w0: L.Vec
  for +cons: P.Constraints
  for +costs: P.TradeCosts
  for +rho: F32
  for +cfg: P.OptConfig
  for h: {U32.is_eq(bm, an) == False{} : Bool}
  {P.mvo_constrained(P.FactorModel{L.Mat{bm, bn, brows}, cf, d}, L.Vec{an, as}, w0, cons, costs, rho, cfg) == None{} : Maybe<&2, P.OptResult>}

law mvo_con_mismatch_lin:
  for +bm: U32
  for +bn: U32
  for +brows: List<&2, List<&2, F32>>
  for +cf: L.Mat
  for +d: L.Vec
  for +alpha: L.Vec
  for +w0: L.Vec
  for +lw: L.Vec
  for +uw: L.Vec
  for +am: U32
  for +anc: U32
  for +arows: List<&2, List<&2, F32>>
  for +lc: L.Vec
  for +uc: L.Vec
  for +gmv: F32
  for +costs: P.TradeCosts
  for +rho: F32
  for +cfg: P.OptConfig
  for h: {U32.is_eq(bm, anc) == False{} : Bool}
  {P.mvo_constrained(P.FactorModel{L.Mat{bm, bn, brows}, cf, d}, alpha, w0, P.Constraints{lw, uw, L.Mat{am, anc, arows}, lc, uc, gmv}, costs, rho, cfg) == None{} : Maybe<&2, P.OptResult>}

law mvo_con_mismatch_cost:
  for +bm: U32
  for +bn: U32
  for +brows: List<&2, List<&2, F32>>
  for +cf: L.Mat
  for +d: L.Vec
  for +alpha: L.Vec
  for +w0: L.Vec
  for +cons: P.Constraints
  for +c1n: U32
  for +c1s: List<&2, F32>
  for +c2: L.Vec
  for +rho: F32
  for +cfg: P.OptConfig
  for h: {U32.is_eq(bm, c1n) == False{} : Bool}
  {P.mvo_constrained(P.FactorModel{L.Mat{bm, bn, brows}, cf, d}, alpha, w0, cons, P.TradeCosts{L.Vec{c1n, c1s}, c2}, rho, cfg) == None{} : Maybe<&2, P.OptResult>}

# ---------------------------------------------------------------- parallel map & causality (Ch 13, 14)

law pmap_seq:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: C -> A -> B
  for +xs: List<&2, A>
  for +t: U32
  for +c: C
  {P.pmap(~A, ~B, ~C, ~f, xs, t, c) == P.pseq(~A, ~B, ~C, ~f, xs, c) : List<&2, B>}

def take(-A: Data, k: Nat, xs: List<&2, A>) -> List<&2, A>:
  match k xs:
    case 0n _:
      Nil{}
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{h, t}:
      h <> take(A, p, t)

# Every scan is strictly causal: the first k outputs depend only on the first k inputs.
law scan_causal:
  for ~A: Data
  for ~S: Data
  for ~step: S -> A -> S
  for +s0: S
  for +xs: List<&2, A>
  for +ys: List<&2, A>
  for +k: Nat
  for h: {take(A, k, xs) == take(A, k, ys) : List<&2, A>}
  {take(S, k, P.scan(~A, ~S, ~step, xs, s0)) == take(S, k, P.scan(~A, ~S, ~step, ys, s0)) : List<&2, S>}

def take_maybe_dd(k: Nat, m: Maybe<&2, List<&2, P.DrawdownState>>) -> Maybe<&2, List<&2, P.DrawdownState>>:
  match m:
    case None{}:
      None{}
    case Some{xs}:
      Some{take(P.DrawdownState, k, xs)}

# Grossman-Zhou dynamic sizing path is strictly causal: future returns cannot affect past states.
law gz_path_causal:
  for +xs: List<&2, F32>
  for +ys: List<&2, F32>
  for +mu: F32
  for +sigma: F32
  for +max_dd: F32
  for +k: Nat
  for h: {take(F32, k, xs) == take(F32, k, ys) : List<&2, F32>}
  {take_maybe_dd(k, P.grossman_zhou_path(xs, mu, sigma, max_dd)) == take_maybe_dd(k, P.grossman_zhou_path(ys, mu, sigma, max_dd)) : Maybe<&2, List<&2, P.DrawdownState>>}

# --- Hedging & attribution dimension guards ---

law hedge_instruments_mismatch:
  for +bm: U32
  for +bn: U32
  for +brows: List<&2, List<&2, F32>>
  for +cf: L.Mat
  for +d: L.Vec
  for +wn: U32
  for +ws: List<&2, F32>
  for +h_mat: L.Mat
  for h: {U32.is_eq(bm, wn) == False{} : Bool}
  {P.hedge_instruments(P.FactorModel{L.Mat{bm, bn, brows}, cf, d}, L.Vec{wn, ws}, h_mat) == None{} : Maybe<&2, L.Vec>}

law hedge_beta_shrink_mismatch:
  for +wn: U32
  for +ws: List<&2, F32>
  for +bn: U32
  for +bs: List<&2, F32>
  for +se: L.Vec
  for h: {U32.is_eq(wn, bn) == False{} : Bool}
  {P.hedge_beta_shrink(L.Vec{wn, ws}, L.Vec{bn, bs}, se) == None{} : Maybe<&2, P.HedgeShrink>}

law hedge_track_mismatch:
  for +bm: U32
  for +bn: U32
  for +brows: List<&2, List<&2, F32>>
  for +cf: L.Mat
  for +d: L.Vec
  for +betan: U32
  for +betas: List<&2, F32>
  for +se: L.Vec
  for +mu_h: F32
  for +sig_h: F32
  for h: {U32.is_eq(bm, betan) == False{} : Bool}
  {P.hedge_track_series(P.FactorModel{L.Mat{bm, bn, brows}, cf, d}, L.Vec{betan, betas}, se, mu_h, sig_h) == None{} : Maybe<&2, L.Vec>}

law attrib_period_mismatch:
  for +bm: U32
  for +bn: U32
  for +brows: List<&2, List<&2, F32>>
  for +cf: L.Mat
  for +d: L.Vec
  for +wn: U32
  for +ws: List<&2, F32>
  for +r: L.Vec
  for +f_ret: L.Vec
  for +rpnl: F32
  for h: {U32.is_eq(bm, wn) == False{} : Bool}
  {P.attribute_period(P.FactorModel{L.Mat{bm, bn, brows}, cf, d}, L.Vec{wn, ws}, r, f_ret, rpnl) == None{} : Maybe<&2, P.PeriodAttrib>}

law max_attrib_mismatch:
  for +cm: U32
  for +cn: U32
  for +crows: List<&2, List<&2, F32>>
  for +b: L.Vec
  for +f_ret: L.Vec
  for +sub: List<&2, U32>
  for h: {U32.is_eq(cm, cn) == False{} : Bool}
  {P.maximal_attribution(L.Mat{cm, cn, crows}, b, f_ret, sub) == None{} : Maybe<&2, P.MaxAttrib>}

law selection_sizing_mismatch:
  for +wn: U32
  for +ws: List<&2, F32>
  for +en: U32
  for +es: List<&2, F32>
  for +d: L.Vec
  for h: {U32.is_eq(wn, en) == False{} : Bool}
  {P.selection_sizing(L.Vec{wn, ws}, L.Vec{en, es}, d) == None{} : Maybe<&2, P.SelectionSizing>}

# --- No-lookahead forward PnL & attribution laws ---

law forward_pnl_mismatch:
  for +wt: U32
  for +wn: U32
  for +ws: List<&2, List<&2, F32>>
  for +rt: U32
  for +rn: U32
  for +rs: List<&2, List<&2, F32>>
  for h: {U32.is_eq(wt, rt) == False{} : Bool}
  {P.forward_pnl(L.Mat{wt, wn, ws}, L.Mat{rt, rn, rs}) == None{} : Maybe<&2, List<&2, F32>>}

def dot_maybe(mw: Maybe<&2, List<&2, F32>>, mr: Maybe<&2, List<&2, F32>>) -> Maybe<&2, F32>:
  match mw mr:
    case Some{w} Some{r}:
      Some{P.dot_rows.go(w, r, 0.0)}
    case _ _:
      None{}

def get_list_maybe(-A: Data, i: Nat, m: Maybe<&2, List<&2, A>>) -> Maybe<&2, A>:
  match m:
    case None{}:
      None{}
    case Some{xs}:
      List.get(&2, A, xs, i)

# No-lookahead law: whenever the headers match, period i of forward_pnl(W, R)
# pairs weight row i with return row i + 1. Same-day pairing is impossible.
law forward_pnl_row:
  for +wt: U32
  for +wn: U32
  for +ws: List<&2, List<&2, F32>>
  for +rt: U32
  for +rn: U32
  for +rs: List<&2, List<&2, F32>>
  for +i: Nat
  for h: {Bool.and(U32.is_eq(wt, rt), U32.is_eq(wn, rn)) == True{} : Bool}
  {get_list_maybe(F32, i, P.forward_pnl(L.Mat{wt, wn, ws}, L.Mat{rt, rn, rs})) == dot_maybe(List.get(&2, List<&2, F32>, ws, i), List.get(&2, List<&2, F32>, rs, 1n+i)) : Maybe<&2, F32>}

def attrib_at(+n: U32, +k: U32, mfm: Maybe<&2, P.FactorModel>, mw: Maybe<&2, List<&2, F32>>, mr: Maybe<&2, List<&2, F32>>, mf: Maybe<&2, List<&2, F32>>) -> Maybe<&2, Maybe<&2, P.PeriodAttrib>>:
  match mfm mw mr mf:
    case Some{fm} Some{w} Some{r} Some{f}:
      Some{P.attrib_item_fn(P.AttribDims{n, k}, P.AttribItem{fm, w, r, f})}
    case _ _ _ _:
      None{}

# No-lookahead law: whenever the headers match, period i of forward_attribute
# attributes model i and weight row i against return row i + 1 and factor
# return row i + 1.
law forward_attribute_row:
  for +fms: List<&2, P.FactorModel>
  for +wt: U32
  for +wn: U32
  for +ws: List<&2, List<&2, F32>>
  for +rt: U32
  for +rn: U32
  for +rs: List<&2, List<&2, F32>>
  for +ft: U32
  for +fk: U32
  for +fs: List<&2, List<&2, F32>>
  for +i: Nat
  for h: {Bool.and(U32.is_eq(wt, rt), Bool.and(U32.is_eq(wt, ft), Bool.and(U32.is_eq(wn, rn), Nat.is_eq(List.length(&2, P.FactorModel, fms), U32.to_nat(wt))))) == True{} : Bool}
  {get_list_maybe(Maybe<&2, P.PeriodAttrib>, i, P.forward_attribute(fms, L.Mat{wt, wn, ws}, L.Mat{rt, rn, rs}, L.Mat{ft, fk, fs})) == attrib_at(wn, fk, List.get(&2, P.FactorModel, fms, i), List.get(&2, List<&2, F32>, ws, i), List.get(&2, List<&2, F32>, rs, 1n+i), List.get(&2, List<&2, F32>, fs, 1n+i)) : Maybe<&2, Maybe<&2, P.PeriodAttrib>>}
