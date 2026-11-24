# Proofs of every law in LAWS.bend.
# Checked with `bend PROOF.bend --verdict` (zero @unsafe, zero IO).
import Base
import bend-quant-linalg@0.1.0.0/linalg.bend as L
import ./portfolio.bend as P
import ./LAWS.bend as Laws

# --- Bool & Maybe helpers ---

def bool_and_false_r(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def bool_and_false_mid(a: Bool, +b: Bool, c: Bool, h: {b == False{} : Bool}) -> {Bool.and(a, Bool.and(b, c)) == False{} : Bool}:
  match a:
    case True{}:
      %Equal.sym(Bool, b, False{}, h) : {Bool.and(_, c) == False{} : Bool}
      {==}
    case False{}:
      {==}

def bool_and_false_last(a: Bool, b: Bool, +c: Bool, h: {c == False{} : Bool}) -> {Bool.and(a, Bool.and(b, c)) == False{} : Bool}:
  match a:
    case True{}:
      %Equal.sym(Bool, c, False{}, h) : {Bool.and(b, _) == False{} : Bool}
      bool_and_false_r(b)
    case False{}:
      {==}

def is_some_t(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case Some{_}:
      Empty
    case None{}:
      Unit

def none_ne_some(-A: Data, x: A, h: {None{} == Some{x} : Maybe<&2, A>}) -> Empty:
  %h : is_some_t(A, _)
  Unit{}

# --- FactorModel validation proofs ---

def Laws.fm_new_mismatch_n(bm, bn, brows, cf, dn, ds, h):
  L.Mat{+cm, +cn, +crows} = cf
  %Equal.sym(Bool, U32.is_eq(bm, dn), False{}, h) : {P.FactorModel.new.dims(Bool.and(_, Bool.and(U32.is_eq(bn, cm), U32.is_eq(cm, cn))), L.Mat{bm, bn, brows}, L.Mat{cm, cn, crows}, L.Vec{dn, ds}) == None{} : Maybe<&2, P.FactorModel>}
  {==}

def Laws.fm_new_mismatch_k(bm, bn, brows, cm, cn, crows, d, h):
  L.Vec{+dn, +ds} = d
  e = bool_and_false_mid(U32.is_eq(bm, dn), U32.is_eq(bn, cm), U32.is_eq(cm, cn), h)
  %Equal.sym(Bool, Bool.and(U32.is_eq(bm, dn), Bool.and(U32.is_eq(bn, cm), U32.is_eq(cm, cn))), False{}, e) : {P.FactorModel.new.dims(_, L.Mat{bm, bn, brows}, L.Mat{cm, cn, crows}, L.Vec{dn, ds}) == None{} : Maybe<&2, P.FactorModel>}
  {==}

def Laws.fm_new_nonsquare_cov(b, cm, cn, crows, d, h):
  L.Mat{+bm, +bn, +brows} = b
  L.Vec{+dn, +ds} = d
  e = bool_and_false_last(U32.is_eq(bm, dn), U32.is_eq(bn, cm), U32.is_eq(cm, cn), h)
  %Equal.sym(Bool, Bool.and(U32.is_eq(bm, dn), Bool.and(U32.is_eq(bn, cm), U32.is_eq(cm, cn))), False{}, e) : {P.FactorModel.new.dims(_, L.Mat{bm, bn, brows}, L.Mat{cm, cn, crows}, L.Vec{dn, ds}) == None{} : Maybe<&2, P.FactorModel>}
  {==}

def fm_new_sound.go(ok: Bool, b: L.Mat, cf: L.Mat, d: L.Vec, fm: P.FactorModel, h: {P.FactorModel.new.dims(ok, b, cf, d) == Some{fm} : Maybe<&2, P.FactorModel>}) -> {ok == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, none_ne_some(P.FactorModel, fm, h))

def Laws.fm_new_sound(b, cf, d, fm, h):
  fm_new_sound.go(P.fm_dims_ok(b, cf, d), b, cf, d, fm, h)

def Laws.fm_new_short_rows():
  {==}

def fm_new_rows_ok.go(ok: Bool, b: L.Mat, cf: L.Mat, d: L.Vec, fm: P.FactorModel, h: {P.FactorModel.new.rows(ok, b, cf, d) == Some{fm} : Maybe<&2, P.FactorModel>}) -> {ok == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, none_ne_some(P.FactorModel, fm, h))

def fm_new_rows_ok.dims(ok: Bool, +b: L.Mat, +cf: L.Mat, +d: L.Vec, fm: P.FactorModel, h: {P.FactorModel.new.dims(ok, b, cf, d) == Some{fm} : Maybe<&2, P.FactorModel>}) -> {P.fm_rows_ok(b, cf, d) == True{} : Bool}:
  match ok:
    case True{}:
      fm_new_rows_ok.go(P.fm_rows_ok(b, cf, d), b, cf, d, fm, h)
    case False{}:
      Empty.absurd({P.fm_rows_ok(b, cf, d) == True{} : Bool}, none_ne_some(P.FactorModel, fm, h))

def Laws.fm_new_rows_ok(b, cf, d, fm, h):
  fm_new_rows_ok.dims(P.fm_dims_ok(b, cf, d), b, cf, d, fm, h)

# --- Dimension guard proofs ---

def Laws.exposures_mismatch(bm, bn, brows, cf, d, wn, ws, h):
  %Equal.sym(Bool, U32.is_eq(bm, wn), False{}, h) : {L.matvec_t.chk(_, bn, brows, ws) == None{} : Maybe<&2, L.Vec>}
  {==}

def Laws.cov_matvec_mismatch(bm, bn, brows, cf, d, wn, ws, h):
  %Equal.sym(Bool, U32.is_eq(bm, wn), False{}, h) : {P.cov_matvec.step1(L.matvec_t.chk(_, bn, brows, ws), L.Mat{bm, bn, brows}, cf, d, L.Vec{wn, ws}) == None{} : Maybe<&2, L.Vec>}
  {==}

def Laws.risk_decomp_mismatch(bm, bn, brows, cf, d, wn, ws, h):
  %Equal.sym(Bool, U32.is_eq(bm, wn), False{}, h) : {P.risk_decomp.go(L.matvec_t.chk(_, bn, brows, ws), cf, d, L.Vec{wn, ws}) == None{} : Maybe<&2, P.RiskDecomp>}
  {==}

def Laws.active_risk_mismatch(fm, wn, ws, bn, bs, h):
  %Equal.sym(Bool, U32.is_eq(wn, bn), False{}, h) : {P.active_risk.go(L.vsub.chk(_, wn, ws, bs), fm) == None{} : Maybe<&2, P.RiskDecomp>}
  {==}

def Laws.marginal_risk_mismatch(bm, bn, brows, cf, d, wn, ws, h):
  %Equal.sym(Bool, U32.is_eq(bm, wn), False{}, h) : {P.marginal_risk.go(P.cov_matvec.step1(L.matvec_t.chk(_, bn, brows, ws), L.Mat{bm, bn, brows}, cf, d, L.Vec{wn, ws}), L.Vec{wn, ws}) == None{} : Maybe<&2, L.Vec>}
  {==}

def Laws.risk_contrib_mismatch(bm, bn, brows, cf, d, wn, ws, h):
  %Equal.sym(Bool, U32.is_eq(bm, wn), False{}, h) : {P.risk_contrib.go(P.cov_matvec.step1(L.matvec_t.chk(_, bn, brows, ws), L.Mat{bm, bn, brows}, cf, d, L.Vec{wn, ws}), L.Vec{wn, ws}) == None{} : Maybe<&2, L.Vec>}
  {==}

def Laws.eff_breadth_mismatch(wn, ws, dn, ds, h):
  %Equal.sym(Bool, U32.is_eq(wn, dn), False{}, h) : {P.eff_breadth.pick(_, ds, L.Vec{wn, ws}, L.Vec{dn, ds}) == None{} : Maybe<&2, F32>}
  {==}

def Laws.mvo_trade_quad_mismatch(bm, bn, brows, cf, d, an, as, w0, cq, rho, h):
  L.Vec{+wn, +ws} = w0
  L.Vec{+cn, +cs} = cq
  %Equal.sym(Bool, U32.is_eq(bm, an), False{}, h) : {P.mvo_trade_quad.pick(Bool.and(_, Bool.and(U32.is_eq(bm, wn), U32.is_eq(bm, cn))), cs, L.Mat{bm, bn, brows}, cf, d, L.Vec{an, as}, L.Vec{wn, ws}, L.Vec{cn, cs}, rho) == None{} : Maybe<&2, L.Vec>}
  {==}

def Laws.fmp_mismatch(bm, bn, brows, cf, dn, ds, h):
  %Equal.sym(Bool, U32.is_eq(bm, dn), False{}, h) : {P.fmp.pick(_, bm, bn, ds, L.Mat{bm, bn, brows}, L.Vec{dn, ds}) == None{} : Maybe<&2, L.Mat>}
  {==}

def Laws.alpha_decomp_mismatch(bm, bn, brows, cf, dn, ds, an, as, h):
  e = bool_and_false_r(U32.is_eq(bm, dn))
  %Equal.sym(Bool, U32.is_eq(bm, an), False{}, h) : {P.alpha_decomp.pick(Bool.and(U32.is_eq(bm, dn), _), bm, bn, ds, L.Mat{bm, bn, brows}, L.Vec{dn, ds}, L.Vec{an, as}) == None{} : Maybe<&2, P.AlphaDecomp>}
  %Equal.sym(Bool, Bool.and(U32.is_eq(bm, dn), False{}), False{}, e) : {P.alpha_decomp.pick(_, bm, bn, ds, L.Mat{bm, bn, brows}, L.Vec{dn, ds}, L.Vec{an, as}) == None{} : Maybe<&2, P.AlphaDecomp>}
  {==}

def Laws.mvo_fn_mismatch(bm, bn, brows, cf, dn, ds, an, as, tv, h):
  e = bool_and_false_r(U32.is_eq(bm, dn))
  %Equal.sym(Bool, U32.is_eq(bm, an), False{}, h) : {P.mvo_fn.pick(Bool.and(U32.is_eq(bm, dn), _), ds, L.Mat{bm, bn, brows}, L.Vec{dn, ds}, L.Vec{an, as}, tv) == None{} : Maybe<&2, L.Vec>}
  %Equal.sym(Bool, Bool.and(U32.is_eq(bm, dn), False{}), False{}, e) : {P.mvo_fn.pick(_, ds, L.Mat{bm, bn, brows}, L.Vec{dn, ds}, L.Vec{an, as}, tv) == None{} : Maybe<&2, L.Vec>}
  {==}

def Laws.mvo_fspace_mismatch(bm, bn, brows, cm, cn, crows, d, ln, ls, rho, h):
  e = bool_and_false_last(U32.is_eq(bn, cm), U32.is_eq(cm, cn), U32.is_eq(cm, ln), h)
  %Equal.sym(Bool, Bool.and(U32.is_eq(bn, cm), Bool.and(U32.is_eq(cm, cn), U32.is_eq(cm, ln))), False{}, e) : {P.mvo_fspace.pick(_, L.Mat{cm, cn, crows}, P.FactorModel{L.Mat{bm, bn, brows}, L.Mat{cm, cn, crows}, d}, L.Vec{ln, ls}, rho) == None{} : Maybe<&2, L.Vec>}
  {==}

# --- Milestone 2 proofs (transaction costs & constrained MVO) ---

def Laws.trade_cost_linear_mismatch(wn, ws, w0n, w0s, cn, cs, h):
  %Equal.sym(Bool, U32.is_eq(wn, w0n), False{}, h) : {P.tc_lin.pick(Bool.and(_, U32.is_eq(wn, cn)), ws, w0s, cs) == None{} : Maybe<&2, F32>}
  {==}

def Laws.trade_cost_quad_mismatch(wn, ws, w0n, w0s, cn, cs, h):
  %Equal.sym(Bool, U32.is_eq(wn, w0n), False{}, h) : {P.tc_quad.pick(Bool.and(_, U32.is_eq(wn, cn)), ws, w0s, cs) == None{} : Maybe<&2, F32>}
  {==}

def Laws.trade_cost_power_mismatch(wn, ws, w0n, w0s, kappa, sn, sigs, an, advs, beta, h):
  %Equal.sym(Bool, U32.is_eq(wn, w0n), False{}, h) : {P.tc_pow.pick(Bool.and(_, Bool.and(U32.is_eq(wn, sn), U32.is_eq(wn, an))), ws, w0s, sigs, advs, kappa, beta) == None{} : Maybe<&2, F32>}
  {==}

def mvo_con_dims_false_alpha(
  +bm: U32, +bn: U32, +cm: U32, +cn: U32, +dn: U32,
  +an: U32, +w0n: U32, +lwn: U32, +uwn: U32,
  +am: U32, +anc: U32, +lcn: U32, +ucn: U32,
  +c1n: U32, +c2n: U32,
  h: {U32.is_eq(bm, an) == False{} : Bool}
) -> {P.mvo_con.dims_ok(bm, bn, cm, cn, dn, an, w0n, lwn, uwn, am, anc, lcn, ucn, c1n, c2n) == False{} : Bool}:
  +ok_fm = Bool.and(U32.is_eq(bm, dn), Bool.and(U32.is_eq(bn, cm), U32.is_eq(cm, cn)))
  +ok_a = Bool.and(U32.is_eq(bm, anc), Bool.and(U32.is_eq(am, lcn), U32.is_eq(am, ucn)))
  +ok_c = Bool.and(U32.is_eq(bm, c1n), U32.is_eq(bm, c2n))
  %Equal.sym(Bool, U32.is_eq(bm, an), False{}, h) : {Bool.and(ok_fm, Bool.and(Bool.and(_, Bool.and(U32.is_eq(bm, w0n), Bool.and(U32.is_eq(bm, lwn), U32.is_eq(bm, uwn)))), Bool.and(ok_a, ok_c))) == False{} : Bool}
  bool_and_false_r(ok_fm)

def mvo_con_dims_false_lin(
  +bm: U32, +bn: U32, +cm: U32, +cn: U32, +dn: U32,
  +an: U32, +w0n: U32, +lwn: U32, +uwn: U32,
  +am: U32, +anc: U32, +lcn: U32, +ucn: U32,
  +c1n: U32, +c2n: U32,
  h: {U32.is_eq(bm, anc) == False{} : Bool}
) -> {P.mvo_con.dims_ok(bm, bn, cm, cn, dn, an, w0n, lwn, uwn, am, anc, lcn, ucn, c1n, c2n) == False{} : Bool}:
  +ok_fm = Bool.and(U32.is_eq(bm, dn), Bool.and(U32.is_eq(bn, cm), U32.is_eq(cm, cn)))
  +ok_v = Bool.and(U32.is_eq(bm, an), Bool.and(U32.is_eq(bm, w0n), Bool.and(U32.is_eq(bm, lwn), U32.is_eq(bm, uwn))))
  +ok_c = Bool.and(U32.is_eq(bm, c1n), U32.is_eq(bm, c2n))
  %Equal.sym(Bool, U32.is_eq(bm, anc), False{}, h) : {Bool.and(ok_fm, Bool.and(ok_v, Bool.and(Bool.and(_, Bool.and(U32.is_eq(am, lcn), U32.is_eq(am, ucn))), ok_c))) == False{} : Bool}
  e1 = bool_and_false_r(ok_v)
  %Equal.sym(Bool, Bool.and(ok_v, False{}), False{}, e1) : {Bool.and(ok_fm, _) == False{} : Bool}
  bool_and_false_r(ok_fm)

def mvo_con_dims_false_cost(
  +bm: U32, +bn: U32, +cm: U32, +cn: U32, +dn: U32,
  +an: U32, +w0n: U32, +lwn: U32, +uwn: U32,
  +am: U32, +anc: U32, +lcn: U32, +ucn: U32,
  +c1n: U32, +c2n: U32,
  h: {U32.is_eq(bm, c1n) == False{} : Bool}
) -> {P.mvo_con.dims_ok(bm, bn, cm, cn, dn, an, w0n, lwn, uwn, am, anc, lcn, ucn, c1n, c2n) == False{} : Bool}:
  +ok_fm = Bool.and(U32.is_eq(bm, dn), Bool.and(U32.is_eq(bn, cm), U32.is_eq(cm, cn)))
  +ok_v = Bool.and(U32.is_eq(bm, an), Bool.and(U32.is_eq(bm, w0n), Bool.and(U32.is_eq(bm, lwn), U32.is_eq(bm, uwn))))
  +ok_a = Bool.and(U32.is_eq(bm, anc), Bool.and(U32.is_eq(am, lcn), U32.is_eq(am, ucn)))
  %Equal.sym(Bool, U32.is_eq(bm, c1n), False{}, h) : {Bool.and(ok_fm, Bool.and(ok_v, Bool.and(ok_a, Bool.and(_, U32.is_eq(bm, c2n))))) == False{} : Bool}
  e0 = bool_and_false_r(ok_a)
  %Equal.sym(Bool, Bool.and(ok_a, False{}), False{}, e0) : {Bool.and(ok_fm, Bool.and(ok_v, _)) == False{} : Bool}
  e1 = bool_and_false_r(ok_v)
  %Equal.sym(Bool, Bool.and(ok_v, False{}), False{}, e1) : {Bool.and(ok_fm, _) == False{} : Bool}
  bool_and_false_r(ok_fm)

def Laws.mvo_con_mismatch_alpha(bm, bn, brows, cf, d, an, as, w0, cons, costs, rho, cfg, h):
  L.Mat{+cm, +cn, +crows} = cf
  L.Vec{+dn, +d_s} = d
  L.Vec{+w0n, +w0_s} = w0
  P.Constraints{L.Vec{+lwn, +lw_s}, L.Vec{+uwn, +uw_s}, L.Mat{+am, +anc, +arows}, L.Vec{+lcn, +lcs}, L.Vec{+ucn, +ucs}, +gmv} = cons
  P.TradeCosts{L.Vec{+c1n, +c1_s}, L.Vec{+c2n, +c2_s}} = costs
  e = mvo_con_dims_false_alpha(bm, bn, cm, cn, dn, an, w0n, lwn, uwn, am, anc, lcn, ucn, c1n, c2n, h)
  %Equal.sym(Bool, P.mvo_con.dims_ok(bm, bn, cm, cn, dn, an, w0n, lwn, uwn, am, anc, lcn, ucn, c1n, c2n), False{}, e) : {P.mvo_con.pick(_, L.Mat{bm, bn, brows}, L.Mat{cm, cn, crows}, d_s, as, w0_s, lw_s, uw_s, L.Mat{am, anc, arows}, L.Vec{lcn, lcs}, L.Vec{ucn, ucs}, c1_s, c2_s, bm, bn, am, gmv, rho, cfg) == None{} : Maybe<&2, P.OptResult>}
  {==}

def Laws.mvo_con_mismatch_lin(bm, bn, brows, cf, d, alpha, w0, lw, uw, am, anc, arows, lc, uc, gmv, costs, rho, cfg, h):
  L.Mat{+cm, +cn, +crows} = cf
  L.Vec{+dn, +d_s} = d
  L.Vec{+an, +a_s} = alpha
  L.Vec{+w0n, +w0_s} = w0
  L.Vec{+lwn, +lw_s} = lw
  L.Vec{+uwn, +uw_s} = uw
  L.Vec{+lcn, +lcs} = lc
  L.Vec{+ucn, +ucs} = uc
  P.TradeCosts{L.Vec{+c1n, +c1_s}, L.Vec{+c2n, +c2_s}} = costs
  e = mvo_con_dims_false_lin(bm, bn, cm, cn, dn, an, w0n, lwn, uwn, am, anc, lcn, ucn, c1n, c2n, h)
  %Equal.sym(Bool, P.mvo_con.dims_ok(bm, bn, cm, cn, dn, an, w0n, lwn, uwn, am, anc, lcn, ucn, c1n, c2n), False{}, e) : {P.mvo_con.pick(_, L.Mat{bm, bn, brows}, L.Mat{cm, cn, crows}, d_s, a_s, w0_s, lw_s, uw_s, L.Mat{am, anc, arows}, L.Vec{lcn, lcs}, L.Vec{ucn, ucs}, c1_s, c2_s, bm, bn, am, gmv, rho, cfg) == None{} : Maybe<&2, P.OptResult>}
  {==}

def Laws.mvo_con_mismatch_cost(bm, bn, brows, cf, d, alpha, w0, cons, c1n, c1s, c2, rho, cfg, h):
  L.Mat{+cm, +cn, +crows} = cf
  L.Vec{+dn, +d_s} = d
  L.Vec{+an, +a_s} = alpha
  L.Vec{+w0n, +w0_s} = w0
  P.Constraints{L.Vec{+lwn, +lw_s}, L.Vec{+uwn, +uw_s}, L.Mat{+am, +anc, +arows}, L.Vec{+lcn, +lcs}, L.Vec{+ucn, +ucs}, +gmv} = cons
  L.Vec{+c2n, +c2_s} = c2
  e = mvo_con_dims_false_cost(bm, bn, cm, cn, dn, an, w0n, lwn, uwn, am, anc, lcn, ucn, c1n, c2n, h)
  %Equal.sym(Bool, P.mvo_con.dims_ok(bm, bn, cm, cn, dn, an, w0n, lwn, uwn, am, anc, lcn, ucn, c1n, c2n), False{}, e) : {P.mvo_con.pick(_, L.Mat{bm, bn, brows}, L.Mat{cm, cn, crows}, d_s, a_s, w0_s, lw_s, uw_s, L.Mat{am, anc, arows}, L.Vec{lcn, lcs}, L.Vec{ucn, ucs}, c1s, c2_s, bm, bn, am, gmv, rho, cfg) == None{} : Maybe<&2, P.OptResult>}
  {==}

# --- Milestone 3 & 4 proofs (pmap_seq, scan_causal, gz_path_causal, guards, forward_pnl_row) ---

def seq2(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, two: P.Two<A>, +c: C) -> List<&2, B>:
  P.Two{l, r} = two
  List.append(&2, B, P.pseq(~A, ~B, ~C, ~f, l, c), P.pseq(~A, ~B, ~C, ~f, r, c))

def cons_seq2(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, +h: A, +two: P.Two<A>, +c: C) -> {seq2(~A, ~B, ~C, ~f, P.split.cons(A, h, two), c) == f(c, h) <> seq2(~A, ~B, ~C, ~f, two, c) : List<&2, B>}:
  match two:
    case P.Two{l, r}:
      {==}

def split_seq(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, +k: Nat, +xs: List<&2, A>, +c: C) -> {seq2(~A, ~B, ~C, ~f, P.split(A, k, xs), c) == P.pseq(~A, ~B, ~C, ~f, xs, c) : List<&2, B>}:
  match k xs:
    case 0n Nil{}:
      {==}
    case 0n Con{h, t}:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{+h, +t}:
      %split_seq(~A, ~B, ~C, ~f, p, t, c) : {seq2(~A, ~B, ~C, ~f, P.split.cons(A, h, P.split(A, p, t)), c) == f(c, h) <> _ : List<&2, B>}
      cons_seq2(~A, ~B, ~C, ~f, h, P.split(A, p, t), c)

def par_seq(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, +d: Nat, +two: P.Two<A>, +h: U32, +r: U32, +c: C) -> {P.par(~A, ~B, ~C, ~f, d, two, h, r, c) == seq2(~A, ~B, ~C, ~f, two, c) : List<&2, B>}:
  match d:
    case 0n:
      match two:
        case P.Two{l, q}:
          {==}
    case 1n+e:
      match two:
        case P.Two{+l, +q}:
          +hl = (h >> 1n : U32)
          +hr = (r >> 1n : U32)
          +pl = P.par(~A, ~B, ~C, ~f, e, P.split(A, U32.to_nat(hl), l), hl, (h - hl : U32), c)
          +pr = P.par(~A, ~B, ~C, ~f, e, P.split(A, U32.to_nat(hr), q), hr, (r - hr : U32), c)
          el = Equal.trans(List<&2, B>, pl, seq2(~A, ~B, ~C, ~f, P.split(A, U32.to_nat(hl), l), c), P.pseq(~A, ~B, ~C, ~f, l, c), par_seq(~A, ~B, ~C, ~f, e, P.split(A, U32.to_nat(hl), l), hl, (h - hl : U32), c), split_seq(~A, ~B, ~C, ~f, U32.to_nat(hl), l, c))
          er = Equal.trans(List<&2, B>, pr, seq2(~A, ~B, ~C, ~f, P.split(A, U32.to_nat(hr), q), c), P.pseq(~A, ~B, ~C, ~f, q, c), par_seq(~A, ~B, ~C, ~f, e, P.split(A, U32.to_nat(hr), q), hr, (r - hr : U32), c), split_seq(~A, ~B, ~C, ~f, U32.to_nat(hr), q, c))
          %el : {List.append(&2, B, pl, pr) == List.append(&2, B, _, P.pseq(~A, ~B, ~C, ~f, q, c)) : List<&2, B>}
          %er : {List.append(&2, B, pl, pr) == List.append(&2, B, pl, _) : List<&2, B>}
          {==}

def Laws.pmap_seq(A, B, C, f, xs, t, c):
  +k = U32.to_nat((t >> 1n : U32))
  +d = Bool.pick(Nat, U32.is_lt(t, 64), 0n, 5n)
  +sp = P.split(A, k, xs)
  Equal.trans(List<&2, B>, P.par(~A, ~B, ~C, ~f, d, sp, (t >> 1n : U32), (t - (t >> 1n : U32) : U32), c), seq2(~A, ~B, ~C, ~f, sp, c), P.pseq(~A, ~B, ~C, ~f, xs, c), par_seq(~A, ~B, ~C, ~f, d, sp, (t >> 1n : U32), (t - (t >> 1n : U32) : U32), c), split_seq(~A, ~B, ~C, ~f, k, xs, c))

# --- Causal scan proofs ---

def is_nil_t(-A: Data, xs: List<&2, A>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{_, _}:
      Empty

def nil_ne_cons(-A: Data, h: A, t: List<&2, A>, e: {Nil{} == Con{h, t} : List<&2, A>}) -> Empty:
  %e : is_nil_t(A, _)
  Unit{}

def head_or(-A: Data, d: A, xs: List<&2, A>) -> A:
  match xs:
    case Nil{}:
      d
    case Con{h, _}:
      h

def tail_or(-A: Data, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{_, t}:
      t

def cons_head_eq(-A: Data, +x: A, +xs: List<&2, A>, +y: A, +ys: List<&2, A>, e: {Con{x, xs} == Con{y, ys} : List<&2, A>}) -> {x == y : A}:
  Equal.cong(List<&2, A>, A, head_or(A, x), Con{x, xs}, Con{y, ys}, e)

def cons_tail_eq(-A: Data, +x: A, +xs: List<&2, A>, +y: A, +ys: List<&2, A>, e: {Con{x, xs} == Con{y, ys} : List<&2, A>}) -> {xs == ys : List<&2, A>}:
  Equal.cong(List<&2, A>, List<&2, A>, tail_or(A), Con{x, xs}, Con{y, ys}, e)

def scan_causal.go(~A: Data, ~S: Data, ~step: S -> A -> S, +k: Nat, +xs: List<&2, A>, +ys: List<&2, A>, +s0: S, +h: {Laws.take(A, k, xs) == Laws.take(A, k, ys) : List<&2, A>}) -> {Laws.take(S, k, P.scan(~A, ~S, ~step, xs, s0)) == Laws.take(S, k, P.scan(~A, ~S, ~step, ys, s0)) : List<&2, S>}:
  match k xs ys:
    case 0n _ _:
      {==}
    case 1n+p Nil{} Nil{}:
      {==}
    case 1n+p Nil{} Con{yh, yt}:
      Empty.absurd({Nil{} == step(s0, yh) <> Laws.take(S, p, P.scan(~A, ~S, ~step, yt, step(s0, yh))) : List<&2, S>}, nil_ne_cons(A, yh, Laws.take(A, p, yt), h))
    case 1n+p Con{xh, xt} Nil{}:
      Empty.absurd({step(s0, xh) <> Laws.take(S, p, P.scan(~A, ~S, ~step, xt, step(s0, xh))) == Nil{} : List<&2, S>}, nil_ne_cons(A, xh, Laws.take(A, p, xt), Equal.sym(List<&2, A>, Con{xh, Laws.take(A, p, xt)}, Nil{}, h)))
    case 1n+p Con{+xh, +xt} Con{+yh, +yt}:
      eh = cons_head_eq(A, xh, Laws.take(A, p, xt), yh, Laws.take(A, p, yt), h)
      et = cons_tail_eq(A, xh, Laws.take(A, p, xt), yh, Laws.take(A, p, yt), h)
      %eh : {step(s0, xh) <> Laws.take(S, p, P.scan(~A, ~S, ~step, xt, step(s0, xh))) == step(s0, _) <> Laws.take(S, p, P.scan(~A, ~S, ~step, yt, step(s0, _))) : List<&2, S>}
      ih = scan_causal.go(~A, ~S, ~step, p, xt, yt, step(s0, xh), et)
      %ih : {step(s0, xh) <> Laws.take(S, p, P.scan(~A, ~S, ~step, xt, step(s0, xh))) == step(s0, xh) <> _ : List<&2, S>}
      {==}

def Laws.scan_causal(A, S, step, s0, xs, ys, k, h):
  scan_causal.go(~A, ~S, ~step, k, xs, ys, s0, h)

def take_gz_extract(+k: Nat, +xs: List<&2, P.GzState>) -> {Laws.take(P.DrawdownState, k, P.gz_extract(xs)) == P.gz_extract(Laws.take(P.GzState, k, xs)) : List<&2, P.DrawdownState>}:
  match k xs:
    case 0n _:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{P.GzState{_, _, +dd}, t}:
      %take_gz_extract(p, t) : {dd <> Laws.take(P.DrawdownState, p, P.gz_extract(t)) == dd <> _ : List<&2, P.DrawdownState>}
      {==}

def gz_path_causal.go(ok: Bool, +xs: List<&2, F32>, +ys: List<&2, F32>, +mu: F32, +sigma: F32, +max_dd: F32, +k: Nat, h: {Laws.take(F32, k, xs) == Laws.take(F32, k, ys) : List<&2, F32>}) -> {Laws.take_maybe_dd(k, P.gz_path.ok(ok, xs, mu, sigma, max_dd)) == Laws.take_maybe_dd(k, P.gz_path.ok(ok, ys, mu, sigma, max_dd)) : Maybe<&2, List<&2, P.DrawdownState>>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      +kelly = (mu / (sigma * sigma : F32) : F32)
      +f0 = (kelly * max_dd : F32)
      +s0 = {P.GzState{kelly, max_dd, P.DrawdownState{1.0, 1.0, 0.0, f0}} : P.GzState}
      +sx = P.scan(~F32, ~P.GzState, ~P.gz_step, xs, s0)
      +sy = P.scan(~F32, ~P.GzState, ~P.gz_step, ys, s0)
      ex = take_gz_extract(k, sx)
      ey = take_gz_extract(k, sy)
      es = scan_causal.go(~F32, ~P.GzState, ~P.gz_step, k, xs, ys, s0, h)
      e1 = Equal.trans(List<&2, P.DrawdownState>, Laws.take(P.DrawdownState, k, P.gz_extract(sx)), P.gz_extract(Laws.take(P.GzState, k, sx)), P.gz_extract(Laws.take(P.GzState, k, sy)), ex, Equal.cong(List<&2, P.GzState>, List<&2, P.DrawdownState>, P.gz_extract, Laws.take(P.GzState, k, sx), Laws.take(P.GzState, k, sy), es))
      e2 = Equal.trans(List<&2, P.DrawdownState>, Laws.take(P.DrawdownState, k, P.gz_extract(sx)), P.gz_extract(Laws.take(P.GzState, k, sy)), Laws.take(P.DrawdownState, k, P.gz_extract(sy)), e1, Equal.sym(List<&2, P.DrawdownState>, Laws.take(P.DrawdownState, k, P.gz_extract(sy)), P.gz_extract(Laws.take(P.GzState, k, sy)), ey))
      %e2 : {Some{Laws.take(P.DrawdownState, k, P.gz_extract(sx))} == Some{_} : Maybe<&2, List<&2, P.DrawdownState>>}
      {==}

def Laws.gz_path_causal(xs, ys, mu, sigma, max_dd, k, h):
  +d_ok = Bool.and(F32.is_gt(max_dd, 0.0), F32.is_le(max_dd, 1.0))
  gz_path_causal.go(Bool.and(F32.is_gt(sigma, 0.0), d_ok), xs, ys, mu, sigma, max_dd, k, h)

# --- Hedging & attribution dimension guard proofs ---

def Laws.hedge_instruments_mismatch(bm, bn, brows, cf, d, wn, ws, h_mat, h):
  L.Mat{+hn, +hm, +hrows} = h_mat
  %Equal.sym(Bool, U32.is_eq(bm, wn), False{}, h) : {P.hedge_inst.pick(Bool.and(_, U32.is_eq(bm, hn)), hm, P.FactorModel{L.Mat{bm, bn, brows}, cf, d}, L.Vec{wn, ws}, L.Mat{hn, hm, hrows}) == None{} : Maybe<&2, L.Vec>}
  {==}

def Laws.hedge_beta_shrink_mismatch(wn, ws, bn, bs, se, h):
  L.Vec{+sn, +ses} = se
  %Equal.sym(Bool, U32.is_eq(wn, bn), False{}, h) : {P.hedge_shrink.pick(Bool.and(_, U32.is_eq(wn, sn)), ses, L.Vec{wn, ws}, L.Vec{bn, bs}, L.Vec{sn, ses}) == None{} : Maybe<&2, P.HedgeShrink>}
  {==}

def Laws.hedge_track_mismatch(bm, bn, brows, cf, d, betan, betas, se, mu_h, sig_h, h):
  L.Vec{+sn, +ses} = se
  %Equal.sym(Bool, U32.is_eq(bm, betan), False{}, h) : {P.hedge_track.pick(Bool.and(_, U32.is_eq(bm, sn)), ses, L.Mat{bm, bn, brows}, cf, d, L.Vec{betan, betas}, L.Vec{sn, ses}, mu_h, sig_h) == None{} : Maybe<&2, L.Vec>}
  {==}

def Laws.attrib_period_mismatch(bm, bn, brows, cf, d, wn, ws, r, f_ret, rpnl, h):
  L.Vec{+rn, +rs} = r
  L.Vec{+fn, +fs} = f_ret
  %Equal.sym(Bool, U32.is_eq(bm, wn), False{}, h) : {P.attrib_p.pick(Bool.and(_, Bool.and(U32.is_eq(bm, rn), U32.is_eq(bn, fn))), P.FactorModel{L.Mat{bm, bn, brows}, cf, d}, L.Vec{wn, ws}, L.Vec{rn, rs}, L.Vec{fn, fs}, rpnl) == None{} : Maybe<&2, P.PeriodAttrib>}
  {==}

def Laws.max_attrib_mismatch(cm, cn, crows, b, f_ret, sub, h):
  L.Vec{+bn, +bs} = b
  L.Vec{+fn, +fs} = f_ret
  %Equal.sym(Bool, U32.is_eq(cm, cn), False{}, h) : {P.max_attr.pick(Bool.and(_, Bool.and(U32.is_eq(cm, bn), U32.is_eq(cm, fn))), L.Mat{cm, cn, crows}, L.Vec{bn, bs}, L.Vec{fn, fs}, sub, cm) == None{} : Maybe<&2, P.MaxAttrib>}
  {==}

def Laws.selection_sizing_mismatch(wn, ws, en, es, d, h):
  L.Vec{+dn, +ds} = d
  e = bool_and_false_mid(U32.is_lt(0, wn), U32.is_eq(wn, en), U32.is_eq(wn, dn), h)
  %Equal.sym(Bool, Bool.and(U32.is_lt(0, wn), Bool.and(U32.is_eq(wn, en), U32.is_eq(wn, dn))), False{}, e) : {P.ss.pick(_, ws, es, ds) == None{} : Maybe<&2, P.SelectionSizing>}
  {==}

# --- No-lookahead forward PnL proofs ---

def Laws.forward_pnl_mismatch(wt, wn, ws, rt, rn, rs, h):
  %Equal.sym(Bool, U32.is_eq(wt, rt), False{}, h) : {P.forward_pnl.pick(Bool.and(_, U32.is_eq(wn, rn)), wt, ws, rs) == None{} : Maybe<&2, List<&2, F32>>}
  {==}

def dot_maybe_none_r(m: Maybe<&2, List<&2, F32>>) -> {None{} == Laws.dot_maybe(m, None{}) : Maybe<&2, F32>}:
  match m:
    case None{}:
      {==}
    case Some{_}:
      {==}

def get_pseq_dot(+ws: List<&2, List<&2, F32>>, +rs: List<&2, List<&2, F32>>, +i: Nat) -> {List.get(&2, F32, P.pseq(~P.RowPair, ~F32, ~Unit, ~P.dot_pair, P.zip_rows(ws, rs), Unit{}), i) == Laws.dot_maybe(List.get(&2, List<&2, F32>, ws, i), List.get(&2, List<&2, F32>, rs, i)) : Maybe<&2, F32>}:
  match ws rs i:
    case Nil{} Nil{} _:
      {==}
    case Nil{} Con{_, _} _:
      {==}
    case Con{_, _} Nil{} 0n:
      {==}
    case Con{_, wt} Nil{} 1n+p:
      dot_maybe_none_r(List.get(&2, List<&2, F32>, wt, p))
    case Con{w, wt} Con{r, rt} 0n:
      {==}
    case Con{w, wt} Con{r, rt} 1n+p:
      get_pseq_dot(wt, rt, p)

def get_tail_rows(+rs: List<&2, List<&2, F32>>, +i: Nat) -> {List.get(&2, List<&2, F32>, P.tail_rows(rs), i) == List.get(&2, List<&2, F32>, rs, 1n+i) : Maybe<&2, List<&2, F32>>}:
  match rs:
    case Nil{}:
      {==}
    case Con{_, t}:
      {==}

def Laws.forward_pnl_row(wt, wn, ws, rt, rn, rs, i, h):
  +cnt = Bool.pick(U32, U32.is_lt(0, wt), (wt - 1 : U32), 0)
  %Equal.sym(Bool, Bool.and(U32.is_eq(wt, rt), U32.is_eq(wn, rn)), True{}, h) : {Laws.get_list_maybe(F32, i, P.forward_pnl.pick(_, wt, ws, rs)) == Laws.dot_maybe(List.get(&2, List<&2, F32>, ws, i), List.get(&2, List<&2, F32>, rs, 1n+i)) : Maybe<&2, F32>}
  ep = Laws.pmap_seq(P.RowPair, F32, Unit, P.dot_pair, P.zip_rows(ws, P.tail_rows(rs)), cnt, Unit{})
  %Equal.sym(List<&2, F32>, P.pmap(~P.RowPair, ~F32, ~Unit, ~P.dot_pair, P.zip_rows(ws, P.tail_rows(rs)), cnt, Unit{}), P.pseq(~P.RowPair, ~F32, ~Unit, ~P.dot_pair, P.zip_rows(ws, P.tail_rows(rs)), Unit{}), ep) : {List.get(&2, F32, _, i) == Laws.dot_maybe(List.get(&2, List<&2, F32>, ws, i), List.get(&2, List<&2, F32>, rs, 1n+i)) : Maybe<&2, F32>}
  et = get_tail_rows(rs, i)
  %et : {List.get(&2, F32, P.pseq(~P.RowPair, ~F32, ~Unit, ~P.dot_pair, P.zip_rows(ws, P.tail_rows(rs)), Unit{}), i) == Laws.dot_maybe(List.get(&2, List<&2, F32>, ws, i), _) : Maybe<&2, F32>}
  get_pseq_dot(ws, P.tail_rows(rs), i)

# --- No-lookahead forward attribution ---

def at_none_2(+n: U32, +k: U32, mfm: Maybe<&2, P.FactorModel>, mr: Maybe<&2, List<&2, F32>>, mf: Maybe<&2, List<&2, F32>>) -> {None{} == Laws.attrib_at(n, k, mfm, None{}, mr, mf) : Maybe<&2, Maybe<&2, P.PeriodAttrib>>}:
  match mfm:
    case None{}:
      {==}
    case Some{_}:
      {==}

def at_none_3(+n: U32, +k: U32, mfm: Maybe<&2, P.FactorModel>, mw: Maybe<&2, List<&2, F32>>, mf: Maybe<&2, List<&2, F32>>) -> {None{} == Laws.attrib_at(n, k, mfm, mw, None{}, mf) : Maybe<&2, Maybe<&2, P.PeriodAttrib>>}:
  match mfm mw:
    case None{} _:
      {==}
    case Some{_} None{}:
      {==}
    case Some{_} Some{_}:
      {==}

def at_none_4(+n: U32, +k: U32, mfm: Maybe<&2, P.FactorModel>, mw: Maybe<&2, List<&2, F32>>, mr: Maybe<&2, List<&2, F32>>) -> {None{} == Laws.attrib_at(n, k, mfm, mw, mr, None{}) : Maybe<&2, Maybe<&2, P.PeriodAttrib>>}:
  match mfm mw mr:
    case None{} _ _:
      {==}
    case Some{_} None{} _:
      {==}
    case Some{_} Some{_} None{}:
      {==}
    case Some{_} Some{_} Some{_}:
      {==}

def get_pseq_attrib(+n: U32, +k: U32, +fms: List<&2, P.FactorModel>, +ws: List<&2, List<&2, F32>>, +rs: List<&2, List<&2, F32>>, +fs: List<&2, List<&2, F32>>, +i: Nat) -> {List.get(&2, Maybe<&2, P.PeriodAttrib>, P.pseq(~P.AttribItem, ~Maybe<&2, P.PeriodAttrib>, ~P.AttribDims, ~P.attrib_item_fn, P.zip_attrib(fms, ws, rs, fs), P.AttribDims{n, k}), i) == Laws.attrib_at(n, k, List.get(&2, P.FactorModel, fms, i), List.get(&2, List<&2, F32>, ws, i), List.get(&2, List<&2, F32>, rs, i), List.get(&2, List<&2, F32>, fs, i)) : Maybe<&2, Maybe<&2, P.PeriodAttrib>>}:
  match fms ws rs fs i:
    case Nil{} _ _ _ _:
      {==}
    case Con{_, _} Nil{} _ _ 0n:
      {==}
    case Con{_, fmt} Nil{} _ _ 1n+p:
      at_none_2(n, k, List.get(&2, P.FactorModel, fmt, p), List.get(&2, List<&2, F32>, rs, 1n+p), List.get(&2, List<&2, F32>, fs, 1n+p))
    case Con{_, _} Con{_, _} Nil{} _ 0n:
      {==}
    case Con{_, fmt} Con{_, wt} Nil{} _ 1n+p:
      at_none_3(n, k, List.get(&2, P.FactorModel, fmt, p), List.get(&2, List<&2, F32>, wt, p), List.get(&2, List<&2, F32>, fs, 1n+p))
    case Con{_, _} Con{_, _} Con{_, _} Nil{} 0n:
      {==}
    case Con{_, fmt} Con{_, wt} Con{_, rt} Nil{} 1n+p:
      at_none_4(n, k, List.get(&2, P.FactorModel, fmt, p), List.get(&2, List<&2, F32>, wt, p), List.get(&2, List<&2, F32>, rt, p))
    case Con{_, _} Con{_, _} Con{_, _} Con{_, _} 0n:
      {==}
    case Con{_, fmt} Con{_, wt} Con{_, rt} Con{_, ft} 1n+p:
      get_pseq_attrib(n, k, fmt, wt, rt, ft, p)

def Laws.forward_attribute_row(fms, wt, wn, ws, rt, rn, rs, ft, fk, fs, i, h):
  +cnt = Bool.pick(U32, U32.is_lt(0, wt), (wt - 1 : U32), 0)
  +dims = {P.AttribDims{wn, fk} : P.AttribDims}
  +items = P.zip_attrib(fms, ws, P.tail_rows(rs), P.tail_rows(fs))
  +rhs = Laws.attrib_at(wn, fk, List.get(&2, P.FactorModel, fms, i), List.get(&2, List<&2, F32>, ws, i), List.get(&2, List<&2, F32>, rs, 1n+i), List.get(&2, List<&2, F32>, fs, 1n+i))
  %Equal.sym(Bool, Bool.and(U32.is_eq(wt, rt), Bool.and(U32.is_eq(wt, ft), Bool.and(U32.is_eq(wn, rn), Nat.is_eq(List.length(&2, P.FactorModel, fms), U32.to_nat(wt))))), True{}, h) : {Laws.get_list_maybe(Maybe<&2, P.PeriodAttrib>, i, P.forward_attrib.pick(_, wt, wn, fk, fms, ws, rs, fs)) == rhs : Maybe<&2, Maybe<&2, P.PeriodAttrib>>}
  ep = Laws.pmap_seq(P.AttribItem, Maybe<&2, P.PeriodAttrib>, P.AttribDims, P.attrib_item_fn, items, cnt, dims)
  %Equal.sym(List<&2, Maybe<&2, P.PeriodAttrib>>, P.pmap(~P.AttribItem, ~Maybe<&2, P.PeriodAttrib>, ~P.AttribDims, ~P.attrib_item_fn, items, cnt, dims), P.pseq(~P.AttribItem, ~Maybe<&2, P.PeriodAttrib>, ~P.AttribDims, ~P.attrib_item_fn, items, dims), ep) : {List.get(&2, Maybe<&2, P.PeriodAttrib>, _, i) == rhs : Maybe<&2, Maybe<&2, P.PeriodAttrib>>}
  %get_tail_rows(rs, i) : {List.get(&2, Maybe<&2, P.PeriodAttrib>, P.pseq(~P.AttribItem, ~Maybe<&2, P.PeriodAttrib>, ~P.AttribDims, ~P.attrib_item_fn, items, dims), i) == Laws.attrib_at(wn, fk, List.get(&2, P.FactorModel, fms, i), List.get(&2, List<&2, F32>, ws, i), _, List.get(&2, List<&2, F32>, fs, 1n+i)) : Maybe<&2, Maybe<&2, P.PeriodAttrib>>}
  %get_tail_rows(fs, i) : {List.get(&2, Maybe<&2, P.PeriodAttrib>, P.pseq(~P.AttribItem, ~Maybe<&2, P.PeriodAttrib>, ~P.AttribDims, ~P.attrib_item_fn, items, dims), i) == Laws.attrib_at(wn, fk, List.get(&2, P.FactorModel, fms, i), List.get(&2, List<&2, F32>, ws, i), List.get(&2, List<&2, F32>, P.tail_rows(rs), i), _) : Maybe<&2, Maybe<&2, P.PeriodAttrib>>}
  get_pseq_attrib(wn, fk, fms, ws, P.tail_rows(rs), P.tail_rows(fs), i)
