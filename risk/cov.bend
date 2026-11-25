# Covariance estimation, shrinkage, DCC, STVU, autocorrelation correction,
# idiosyncratic risk, correlation clustering, multi-block model linking,
# currency rebasing, and causal log-MAD winsorization (Paleologo Ch 6.3-6.6).
#
# Every covariance estimator returns a structurally symmetric matrix built
# through mirror_upper, enabling formal bitwise symmetry proofs in PROOF.bend.
import Base
import bend-kit-f32array@0.2.1.0/f32array.bend as A
import bend-quant-linalg@0.1.1.0/linalg.bend as L

# ---------------------------------------------------------------- types

# Ledoit-Wolf linear shrinkage result.
type ShrinkResult is Data:
  ShrinkResult{cov: L.Mat, shrinkage: F32, target_diag: F32}

# Thresholded off-diagonal idiosyncratic correlation pair (i < j, |corr| > threshold).
type CorrPair is Data:
  CorrPair{i: U32, j: U32, corr: F32}

# Currency rebasing result.
type RebaseResult is Data:
  RebaseResult{c_loadings: L.Mat, cov_c: L.Mat}

# ---------------------------------------------------------------- scalar & list helpers

def fmax(+a: F32, +b: F32) -> F32:
  F32.max(a, b)

def fmin(+a: F32, +b: F32) -> F32:
  Bool.pick(F32, F32.is_le(a, b), a, b)

def clip(+x: F32, +lo: F32, +hi: F32) -> F32:
  fmin(fmax(x, lo), hi)

def all_pos(xs: List<&2, F32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(F32.is_gt(h, 0.0), all_pos(t))

def list_sum.go(xs: List<&2, F32>, +acc: F32) -> F32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      list_sum.go(t, (acc + h : F32))

def list_sum(xs: List<&2, F32>) -> F32:
  list_sum.go(xs, 0.0)

def list_scale(xs: List<&2, F32>, +s: F32) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      (h * s : F32) <> list_scale(t, s)

def list_sub(xs: List<&2, F32>, ys: List<&2, F32>) -> List<&2, F32>:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      (x - y : F32) <> list_sub(xt, yt)
    case _ _:
      Nil{}

def list_sq(xs: List<&2, F32>) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      (x * x : F32) <> list_sq(t)

def list_sqrt(xs: List<&2, F32>) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      F32.sqrt(x) <> list_sqrt(t)

def list_inv_sqrt(xs: List<&2, F32>) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      (1.0 / F32.sqrt(x) : F32) <> list_inv_sqrt(t)

def list_axpy(+a: F32, xs: List<&2, F32>, ys: List<&2, F32>) -> List<&2, F32>:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      ((a * x) + y : F32) <> list_axpy(a, xt, yt)
    case _ _:
      Nil{}

def list_sum_sq.go(xs: List<&2, F32>, +acc: F32) -> F32:
  match xs:
    case Nil{}:
      acc
    case Con{+x, t}:
      list_sum_sq.go(t, (acc + (x * x) : F32))

def floor_list(xs: List<&2, F32>, +fl: F32) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      fmax(h, fl) <> floor_list(t, fl)

def map_rows_sq(rows: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      list_sq(r) <> map_rows_sq(t)

# ---------------------------------------------------------------- structural symmetry (mirror_upper)

def prepend_col(col: List<&2, F32>, rows: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match col rows:
    case Con{c, ct} Con{r, rt}:
      (c <> r) <> prepend_col(ct, rt)
    case _ _:
      Nil{}

def mirror_upper(upper: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match upper:
    case Nil{}:
      Nil{}
    case Con{Nil{}, sub}:
      Nil{} <> mirror_upper(sub)
    case Con{Con{d, +off}, sub}:
      (d <> off) <> prepend_col(off, mirror_upper(sub))

def arr_depth.go(rem: Nat, +d: Nat, +cap: U32, +n: U32) -> Nat:
  match rem:
    case 0n:
      d
    case 1n+p:
      +lt = U32.is_lt(cap, n)
      arr_depth.go(p, Bool.pick(Nat, lt, 1n+d, d), Bool.pick(U32, lt, (cap << 1n : U32), cap), n)

def arr_depth(+n: U32) -> Nat:
  arr_depth.go(30n, 0n, 1, n)

def fill_rm_row(r: List<&2, F32>, a: Array<F32>, +idx: U32) -> Array<F32>:
  match r:
    case Nil{}:
      a
    case Con{x, t}:
      fill_rm_row(t, Array.set(F32, a, idx, x), (idx + 1 : U32))

def fill_rm(rows: List<&2, List<&2, F32>>, a: Array<F32>, +off: U32, +nc: U32) -> Array<F32>:
  match rows:
    case Nil{}:
      a
    case Con{r, t}:
      fill_rm(t, fill_rm_row(r, a, off), (off + nc : U32), nc)

def mat_to_arr(rows: List<&2, List<&2, F32>>, +m: U32, +n: U32) -> Array<F32>:
  fill_rm(rows, Array.new(F32, arr_depth((m * n : U32)), 0.0), 0, n)

type SymRow is Type:
  SymRow{a: Array<F32>, row: List<&2, F32>}

def sym_cell.s2(p: Array<F32> & F32, +aij: F32) -> Array<F32> & F32:
  (a, aji) = p
  (a, (0.5 * (aij + aji) : F32))

def sym_cell.s1(p: Array<F32> & F32, +idx_ji: U32) -> Array<F32> & F32:
  (a, aij) = p
  sym_cell.s2(Array.get(F32, a, idx_ji), aij)

def sym_cell(a: Array<F32>, +idx_ij: U32, +idx_ji: U32) -> Array<F32> & F32:
  sym_cell.s1(Array.get(F32, a, idx_ij), idx_ji)

def sym_row.push(p: Array<F32> & F32, row: List<&2, F32>) -> SymRow:
  (a, val) = p
  SymRow{a, val <> row}

def sym_row.go(rem: Nat, st: SymRow, +i: U32, +j: U32, +n: U32) -> SymRow:
  match rem:
    case 0n:
      st
    case 1n+p:
      SymRow{a, row} = st
      st1 = sym_row.push(sym_cell(a, ((i * n) + j : U32), ((j * n) + i : U32)), row)
      sym_row.go(p, st1, i, (j - 1 : U32), n)

type SymTri is Type:
  SymTri{a: Array<F32>, upper: List<&2, List<&2, F32>>}

def sym_tri.push(st: SymRow, upper: List<&2, List<&2, F32>>) -> SymTri:
  SymRow{a, row} = st
  SymTri{a, row <> upper}

def sym_tri.go(rem: Nat, st: SymTri, +row_len: Nat, +i: U32, +n: U32) -> List<&2, List<&2, F32>>:
  match rem:
    case 0n:
      SymTri{_, upper} = st
      upper
    case 1n+p:
      SymTri{a, upper} = st
      st1 = sym_tri.push(sym_row.go(row_len, SymRow{a, Nil{}}, i, (n - 1 : U32), n), upper)
      sym_tri.go(p, st1, 1n+row_len, (i - 1 : U32), n)

def upper_sym_from_arr.chk(is_z: Bool, a: Array<F32>, +n: U32) -> List<&2, List<&2, F32>>:
  match is_z:
    case True{}:
      Nil{}
    case False{}:
      sym_tri.go(U32.to_nat(n), SymTri{a, Nil{}}, 1n, (n - 1 : U32), n)

def upper_sym_from_arr(a: Array<F32>, +n: U32) -> List<&2, List<&2, F32>>:
  upper_sym_from_arr.chk(U32.is_eq(n, 0), a, n)

def symmetrize_raw(+n: U32, rows: List<&2, List<&2, F32>>) -> L.Mat:
  L.Mat{n, n, mirror_upper(upper_sym_from_arr(mat_to_arr(rows, n, n), n))}

def symmetrize.chk(ok: Bool, +n: U32, rows: List<&2, List<&2, F32>>) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      Some{symmetrize_raw(n, rows)}
    case False{}:
      None{}

def symmetrize(m: L.Mat) -> Maybe<&2, L.Mat>:
  L.Mat{r, +c, rows} = m
  symmetrize.chk(U32.is_eq(r, c), c, rows)

# ---------------------------------------------------------------- EWMA weights (Ch 6.3, 6.4, 7.5)

def ewma_raw.go(rem: Nat, +lam: F32, +cur: F32, acc: List<&2, F32>, +sum: F32) -> List<&2, F32> & F32:
  match rem:
    case 0n:
      (acc, sum)
    case 1n+p:
      ewma_raw.go(p, lam, (cur * lam : F32), cur <> acc, (sum + cur : F32))

def ewma_weights.fin(p: List<&2, F32> & F32, +t: U32) -> L.Vec:
  (ws, s) = p
  L.Vec{t, list_scale(ws, (1.0 / s : F32))}

def ewma_weights.chk(ok: Bool, +t: U32, +half_life: F32) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      +lam = F32.exp((F32.neg(0.69314718) / half_life : F32))
      Some{ewma_weights.fin(ewma_raw.go(U32.to_nat(t), lam, 1.0, Nil{}, 0.0), t)}
    case False{}:
      None{}

def ewma_weights(+t: U32, +half_life: F32) -> Maybe<&2, L.Vec>:
  ewma_weights.chk(Bool.and(U32.is_gt(t, 0), F32.is_gt(half_life, 0.0)), t, half_life)

# ---------------------------------------------------------------- column centering helpers

def col_wsum.go(rows: List<&2, List<&2, F32>>, ws: List<&2, F32>, acc: List<&2, F32>) -> List<&2, F32>:
  match rows ws:
    case Con{r, rt} Con{w, wt}:
      col_wsum.go(rt, wt, list_axpy(w, r, acc))
    case _ _:
      acc

def col_mean_weighted(rows: List<&2, List<&2, F32>>, ws: List<&2, F32>, +k: U32) -> List<&2, F32>:
  col_wsum.go(rows, ws, List.replicate(F32, U32.to_nat(k), 0.0))

def sub_row_mean(rows: List<&2, List<&2, F32>>, +mu: List<&2, F32>) -> List<&2, List<&2, F32>>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      list_sub(r, mu) <> sub_row_mean(t, mu)

def center_rows(+rows: List<&2, List<&2, F32>>, ws: List<&2, F32>, +k: U32) -> List<&2, List<&2, F32>>:
  +mu = col_mean_weighted(rows, ws, k)
  sub_row_mean(rows, mu)

# ---------------------------------------------------------------- sample_cov & ewma_cov

def sym_scale.fin(m: L.Mat) -> L.Mat:
  L.Mat{+n, _, rows} = m
  symmetrize_raw(n, rows)

def sym_scale(+s: F32, m: L.Mat) -> L.Mat:
  sym_scale.fin(L.scale(s, m))

def sample_cov.centered(ok: Bool, +t: U32, +k: U32, +rows: List<&2, List<&2, F32>>) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      +ws = List.replicate(F32, U32.to_nat(t), (1.0 / U32.to_f32(t) : F32))
      +crows = center_rows(rows, ws, k)
      +inv = (1.0 / U32.to_f32((t - 1 : U32)) : F32)
      Some{sym_scale(inv, L.gram(L.Mat{t, k, crows}))}
    case False{}:
      None{}

def sample_cov.run(center: Bool, +t: U32, +k: U32, +rows: List<&2, List<&2, F32>>) -> Maybe<&2, L.Mat>:
  match center:
    case False{}:
      +inv = (1.0 / U32.to_f32(t) : F32)
      Some{sym_scale(inv, L.gram(L.Mat{t, k, rows}))}
    case True{}:
      sample_cov.centered(U32.is_gt(t, 1), t, k, rows)

def sample_cov.chk(ok: Bool, center: Bool, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      sample_cov.run(center, t, k, rows)
    case False{}:
      None{}

def sample_cov(x: L.Mat, center: Bool) -> Maybe<&2, L.Mat>:
  L.Mat{+t, +k, rows} = x
  sample_cov.chk(Bool.and(U32.is_gt(t, 0), U32.is_gt(k, 0)), center, t, k, rows)

def ewma_cov.wgram_wrap(mg: Maybe<&2, L.Mat>, +sc: F32) -> Maybe<&2, L.Mat>:
  match mg:
    case Some{g}:
      Some{sym_scale(sc, g)}
    case None{}:
      None{}

def ewma_cov.centered(ok: Bool, +den: F32, +t: U32, +k: U32, +rows: List<&2, List<&2, F32>>, +ws: List<&2, F32>) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      +crows = center_rows(rows, ws, k)
      ewma_cov.wgram_wrap(L.wgram(L.Mat{t, k, crows}, L.Vec{t, ws}), (1.0 / den : F32))
    case False{}:
      None{}

def ewma_cov.run(center: Bool, +t: U32, +k: U32, +rows: List<&2, List<&2, F32>>, +ws: List<&2, F32>) -> Maybe<&2, L.Mat>:
  match center:
    case False{}:
      ewma_cov.wgram_wrap(L.wgram(L.Mat{t, k, rows}, L.Vec{t, ws}), 1.0)
    case True{}:
      +den = (1.0 - list_sum_sq.go(ws, 0.0) : F32)
      ewma_cov.centered(F32.is_gt(den, 1.0e-12), den, t, k, rows, ws)

def ewma_cov.with_w(mw: Maybe<&2, L.Vec>, center: Bool, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>) -> Maybe<&2, L.Mat>:
  match mw:
    case Some{L.Vec{_, ws}}:
      ewma_cov.run(center, t, k, rows, ws)
    case None{}:
      None{}

def ewma_cov.chk(ok: Bool, center: Bool, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>, +half_life: F32) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      ewma_cov.with_w(ewma_weights(t, half_life), center, t, k, rows)
    case False{}:
      None{}

def ewma_cov(x: L.Mat, +half_life: F32, center: Bool) -> Maybe<&2, L.Mat>:
  L.Mat{+t, +k, rows} = x
  ewma_cov.chk(Bool.and(U32.is_gt(t, 0), U32.is_gt(k, 0)), center, t, k, rows, half_life)

# ---------------------------------------------------------------- Shrinkage & Ledoit-Wolf (Ch 6.3.1)

def shrink_id.row(rem: Nat, r: List<&2, F32>, +i: Nat, +j: Nat, +omr: F32, +add_d: F32) -> List<&2, F32>:
  match rem r:
    case 0n _:
      Nil{}
    case 1n+p Con{v, rt}:
      +sv = (omr * v : F32)
      Bool.pick(F32, Nat.is_eq(i, j), (sv + add_d : F32), sv) <> shrink_id.row(p, rt, i, 1n+j, omr, add_d)
    case _ _:
      Nil{}

def shrink_id.rows(rows: List<&2, List<&2, F32>>, +i: Nat, +n: Nat, +omr: F32, +add_d: F32) -> List<&2, List<&2, F32>>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, rt}:
      shrink_id.row(n, r, i, 0n, omr, add_d) <> shrink_id.rows(rt, 1n+i, n, omr, add_d)

def shrink_id.with_tr(mtr: Maybe<&2, F32>, +n: U32, rows: List<&2, List<&2, F32>>, +rho: F32) -> Maybe<&2, L.Mat>:
  match mtr:
    case Some{tr}:
      +mu = (tr / U32.to_f32(n) : F32)
      +raw = shrink_id.rows(rows, 0n, U32.to_nat(n), (1.0 - rho : F32), (rho * mu : F32))
      Some{symmetrize_raw(n, raw)}
    case None{}:
      None{}

def shrink_id.chk(ok: Bool, +n: U32, +rows: List<&2, List<&2, F32>>, +rho: F32) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      shrink_id.with_tr(L.trace(L.Mat{n, n, rows}), n, rows, rho)
    case False{}:
      None{}

def shrink_to_identity(cov: L.Mat, +rho: F32) -> Maybe<&2, L.Mat>:
  L.Mat{m, +n, rows} = cov
  +ok = Bool.and(U32.is_eq(m, n), Bool.and(U32.is_gt(n, 0), Bool.and(F32.is_ge(rho, 0.0), F32.is_le(rho, 1.0))))
  shrink_id.chk(ok, n, rows, rho)

def sum_row_norm4.go(rows: List<&2, List<&2, F32>>, +acc: F32) -> F32:
  match rows:
    case Nil{}:
      acc
    case Con{r, rt}:
      +ss = list_sum_sq.go(r, 0.0)
      sum_row_norm4.go(rt, (acc + (ss * ss) : F32))

def diag_sub_sq.row(r: List<&2, F32>, +i: Nat, +j: Nat, +mu: F32, +acc: F32) -> F32:
  match r:
    case Nil{}:
      acc
    case Con{+v, rt}:
      +d = Bool.pick(F32, Nat.is_eq(i, j), (v - mu : F32), v)
      diag_sub_sq.row(rt, i, 1n+j, mu, (acc + (d * d) : F32))

def frob_sub_mu_sq(rows: List<&2, List<&2, F32>>, +i: Nat, +mu: F32, +acc: F32) -> F32:
  match rows:
    case Nil{}:
      acc
    case Con{r, rt}:
      frob_sub_mu_sq(rt, 1n+i, mu, diag_sub_sq.row(r, i, 0n, mu, acc))

def maybe_f32(mv: Maybe<&2, F32>, +defv: F32) -> F32:
  match mv:
    case Some{v}:
      v
    case None{}:
      defv

def ledoit_wolf.with_s(+s_mat: L.Mat, +t: U32, +k: U32, xrows: List<&2, List<&2, F32>>) -> ShrinkResult:
  L.Mat{_, _, +srows} = s_mat
  +tf = U32.to_f32(t)
  +kf = U32.to_f32(k)
  +tr = maybe_f32(L.trace(s_mat), 0.0)
  +mu = (tr / kf : F32)
  +fr = L.frobenius(s_mat)
  +s_frob_sq = (fr * fr : F32)
  +delta_sq = frob_sub_mu_sq(srows, 0n, mu, 0.0)
  +s4 = sum_row_norm4.go(xrows, 0.0)
  +beta_bar = fmax(0.0, ((s4 - (tf * s_frob_sq)) / (tf * tf) : F32))
  +rho = Bool.pick(F32, F32.is_gt(delta_sq, 1.0e-30), fmin(1.0, (beta_bar / delta_sq : F32)), 0.0)
  +raw = shrink_id.rows(srows, 0n, U32.to_nat(k), (1.0 - rho : F32), (rho * mu : F32))
  ShrinkResult{symmetrize_raw(k, raw), rho, mu}

def ledoit_wolf.run(+t: U32, +k: U32, +xrows: List<&2, List<&2, F32>>) -> ShrinkResult:
  +s_mat = sym_scale((1.0 / U32.to_f32(t) : F32), L.gram(L.Mat{t, k, xrows}))
  ledoit_wolf.with_s(s_mat, t, k, xrows)

def ledoit_wolf.prep(center: Bool, +t: U32, +k: U32, +rows: List<&2, List<&2, F32>>) -> ShrinkResult:
  match center:
    case True{}:
      +ws = List.replicate(F32, U32.to_nat(t), (1.0 / U32.to_f32(t) : F32))
      ledoit_wolf.run(t, k, center_rows(rows, ws, k))
    case False{}:
      ledoit_wolf.run(t, k, rows)

def ledoit_wolf.chk(ok: Bool, center: Bool, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>) -> Maybe<&2, ShrinkResult>:
  match ok:
    case True{}:
      Some{ledoit_wolf.prep(center, t, k, rows)}
    case False{}:
      None{}

def ledoit_wolf_cov(x: L.Mat, center: Bool) -> Maybe<&2, ShrinkResult>:
  L.Mat{+t, +k, rows} = x
  ledoit_wolf.chk(Bool.and(U32.is_gt(t, 0), U32.is_gt(k, 0)), center, t, k, rows)

# ---------------------------------------------------------------- PSD floor & factor cov debiasing (Ch 6.3.1 Eq 6.5)

def psd_project.fin(mg: Maybe<&2, L.Mat>) -> Maybe<&2, L.Mat>:
  match mg:
    case Some{L.Mat{+n, _, rows}}:
      Some{symmetrize_raw(n, rows)}
    case None{}:
      None{}

def psd_project.with_eig(me: Maybe<&2, L.Eigen>, +eig_floor: F32) -> Maybe<&2, L.Mat>:
  match me:
    case Some{L.Eigen{L.Vec{n, vals}, vecs}}:
      psd_project.fin(L.wgram(L.transpose(vecs), L.Vec{n, floor_list(vals, eig_floor)}))
    case None{}:
      None{}

def psd_project(a: L.Mat, +eig_floor: F32) -> Maybe<&2, L.Mat>:
  psd_project.with_eig(L.sym_eigen(a), eig_floor)

def inv_bt_winv_b.s4(g: L.Mat) -> L.Mat:
  L.Mat{+k, _, rows} = g
  symmetrize_raw(k, rows)

def inv_bt_winv_b.s3(mri: Maybe<&2, L.Mat>) -> Maybe<&2, L.Mat>:
  match mri:
    case Some{ri}:
      Some{inv_bt_winv_b.s4(L.gram(L.transpose(ri)))}
    case None{}:
      None{}

def inv_bt_winv_b.s2(mqr: Maybe<&2, L.QR>, +k: U32) -> Maybe<&2, L.Mat>:
  match mqr:
    case Some{L.QR{_, r}}:
      inv_bt_winv_b.s3(L.solve_upper_mat(r, L.Mat.eye(k)))
    case None{}:
      None{}

def inv_bt_winv_b.s1(mwb: Maybe<&2, L.Mat>, +k: U32) -> Maybe<&2, L.Mat>:
  match mwb:
    case Some{wb}:
      inv_bt_winv_b.s2(L.qr_thin(wb), k)
    case None{}:
      None{}

def inv_bt_winv_b.chk(ok: Bool, b: L.Mat, +nd: U32, ds: List<&2, F32>, +k: U32) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      inv_bt_winv_b.s1(L.diag_mul(L.Vec{nd, list_inv_sqrt(ds)}, b), k)
    case False{}:
      None{}

def inv_bt_winv_b(+b: L.Mat, idio_var: L.Vec) -> Maybe<&2, L.Mat>:
  L.Mat{n, +k, _} = b
  L.Vec{+nd, +ds} = idio_var
  inv_bt_winv_b.chk(Bool.and(U32.is_eq(n, nd), Bool.and(U32.is_gt(k, 0), all_pos(ds))), b, nd, ds, k)

def debias.proj(md: Maybe<&2, L.Mat>, +eig_floor: F32) -> Maybe<&2, L.Mat>:
  match md:
    case Some{diff}:
      psd_project(diff, eig_floor)
    case None{}:
      None{}

def debias.sub(merr: Maybe<&2, L.Mat>, cov_f: L.Mat, +eig_floor: F32) -> Maybe<&2, L.Mat>:
  match merr:
    case Some{err}:
      debias.proj(L.msub(cov_f, err), eig_floor)
    case None{}:
      None{}

def debias.chk(ok: Bool, cov_f: L.Mat, b: L.Mat, idio_var: L.Vec, +eig_floor: F32) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      debias.sub(inv_bt_winv_b(b, idio_var), cov_f, eig_floor)
    case False{}:
      None{}

def debias_factor_cov(+cov_f_raw: L.Mat, +b: L.Mat, +idio_var: L.Vec, +eig_floor: F32) -> Maybe<&2, L.Mat>:
  L.Mat{+cm, +cn, _} = cov_f_raw
  L.Mat{+bm, +bn, _} = b
  L.Vec{+dn, _} = idio_var
  +ok = Bool.and(U32.is_eq(cm, cn), Bool.and(U32.is_eq(cm, bn), Bool.and(U32.is_eq(bm, dn), F32.is_ge(eig_floor, 0.0))))
  debias.chk(ok, cov_f_raw, b, idio_var, eig_floor)

# ---------------------------------------------------------------- DCC: Dual-Half-Life Vol/Corr Separation (Ch 6.3.2)

def ewma_var_step(v_prev: List<&2, F32>, r: List<&2, F32>, +a: F32, +oma: F32) -> List<&2, F32>:
  match v_prev r:
    case Con{vp, vt} Con{+x, xt}:
      ((oma * vp) + (a * (x * x)) : F32) <> ewma_var_step(vt, xt, a, oma)
    case _ _:
      Nil{}

def safe_div_vol(r: List<&2, F32>, vs: List<&2, F32>) -> List<&2, F32>:
  match r vs:
    case Con{x, xt} Con{+v, vt}:
      +sd = F32.sqrt(fmax(v, 1.0e-12))
      (x / sd : F32) <> safe_div_vol(xt, vt)
    case _ _:
      Nil{}

type DccScan is Data:
  DccScan{std_rows: List<&2, List<&2, F32>>, last_var: List<&2, F32>}

def dcc_scan.go(rows: List<&2, List<&2, F32>>, v_cur: List<&2, F32>, +a: F32, +oma: F32, acc: List<&2, List<&2, F32>>) -> DccScan:
  match rows:
    case Nil{}:
      DccScan{List.reverse(&2, List<&2, F32>, acc), v_cur}
    case Con{+r, rt}:
      +v_next = ewma_var_step(v_cur, r, a, oma)
      +z_row = safe_div_vol(r, v_next)
      dcc_scan.go(rt, v_next, a, oma, z_row <> acc)

def dcc_norm.s4(m: Maybe<&2, L.Mat>) -> Maybe<&2, L.Mat>:
  match m:
    case Some{L.Mat{+n, _, rows}}:
      Some{symmetrize_raw(n, rows)}
    case None{}:
      None{}

def dcc_norm.s3(m: Maybe<&2, L.Mat>, last_vol: L.Vec) -> Maybe<&2, L.Mat>:
  match m:
    case Some{tmp2}:
      dcc_norm.s4(L.mul_diag(tmp2, last_vol))
    case None{}:
      None{}

def dcc_norm.s2(m: Maybe<&2, L.Mat>, +last_vol: L.Vec) -> Maybe<&2, L.Mat>:
  match m:
    case Some{c_norm}:
      dcc_norm.s3(L.diag_mul(last_vol, c_norm), last_vol)
    case None{}:
      None{}

def dcc_norm.s1(m: Maybe<&2, L.Mat>, inv_d: L.Vec, last_vol: L.Vec) -> Maybe<&2, L.Mat>:
  match m:
    case Some{tmp1}:
      dcc_norm.s2(L.mul_diag(tmp1, inv_d), last_vol)
    case None{}:
      None{}

def dcc_norm.diag1(+inv_d: L.Vec, corr_raw: L.Mat, last_vol: L.Vec) -> Maybe<&2, L.Mat>:
  dcc_norm.s1(L.diag_mul(inv_d, corr_raw), inv_d, last_vol)

def dcc_norm.diag(dv: L.Vec, corr_raw: L.Mat, last_vol: L.Vec) -> Maybe<&2, L.Mat>:
  L.Vec{k, ds} = dv
  dcc_norm.diag1(L.Vec{k, list_inv_sqrt(floor_list(ds, 1.0e-12))}, corr_raw, last_vol)

def dcc_norm_corr.finish(+corr_raw: L.Mat, last_vol: L.Vec) -> Maybe<&2, L.Mat>:
  dcc_norm.diag(L.Mat.diag_vec(corr_raw), corr_raw, last_vol)

def dcc_init_var(rows: List<&2, List<&2, F32>>, +k: U32) -> List<&2, F32>:
  match rows:
    case Con{r0, _}:
      floor_list(list_sq(r0), 1.0e-12)
    case Nil{}:
      List.replicate(F32, U32.to_nat(k), 1.0e-12)

def dcc_cov.with_craw(mc: Maybe<&2, L.Mat>, last_vol: L.Vec) -> Maybe<&2, L.Mat>:
  match mc:
    case Some{c_raw}:
      dcc_norm_corr.finish(c_raw, last_vol)
    case None{}:
      None{}

def dcc_cov.with_wv(mwv: Maybe<&2, L.Vec>, scan_res: DccScan, wc: L.Vec, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>) -> Maybe<&2, L.Mat>:
  match mwv:
    case Some{L.Vec{_, wv}}:
      DccScan{std_rows, _} = scan_res
      +final_var = col_wsum.go(map_rows_sq(rows), wv, List.replicate(F32, U32.to_nat(k), 0.0))
      dcc_cov.with_craw(L.wgram(L.Mat{t, k, std_rows}, wc), L.Vec{k, list_sqrt(floor_list(final_var, 1.0e-12))})
    case None{}:
      None{}

def dcc_cov.with_wc(mwc: Maybe<&2, L.Vec>, +t: U32, +k: U32, +rows: List<&2, List<&2, F32>>, +hl_vol: F32) -> Maybe<&2, L.Mat>:
  match mwc:
    case Some{wc}:
      +lam_v = F32.exp((F32.neg(0.69314718) / hl_vol : F32))
      +a = (1.0 - lam_v : F32)
      +v0 = dcc_init_var(rows, k)
      +scan_res = dcc_scan.go(rows, v0, a, lam_v, Nil{})
      dcc_cov.with_wv(ewma_weights(t, hl_vol), scan_res, wc, t, k, rows)
    case None{}:
      None{}

def dcc_cov.chk(ok: Bool, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>, +hl_vol: F32, +hl_corr: F32) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      dcc_cov.with_wc(ewma_weights(t, hl_corr), t, k, rows, hl_vol)
    case False{}:
      None{}

def dcc_cov(f_rets: L.Mat, +hl_vol: F32, +hl_corr: F32) -> Maybe<&2, L.Mat>:
  L.Mat{+t, +k, rows} = f_rets
  +ok = Bool.and(U32.is_gt(t, 0), Bool.and(U32.is_gt(k, 0), Bool.and(F32.is_gt(hl_vol, 0.0), F32.is_gt(hl_corr, 0.0))))
  dcc_cov.chk(ok, t, k, rows, hl_vol, hl_corr)

# ---------------------------------------------------------------- Short-Term Volatility Updating (STVU, Ch 6.3.3)

def digamma_large(+x: F32) -> F32:
  +inv = (1.0 / x : F32)
  +inv2 = (inv * inv : F32)
  (((F32.log(x) - (0.5 * inv)) - (inv2 * (0.083333336 - (0.008333334 * inv2)))) : F32)

def digamma_pos(+x: F32) -> F32:
  +d = digamma_large((x + 4.0 : F32))
  +s = (((1.0 / x) + (1.0 / (x + 1.0))) + ((1.0 / (x + 2.0)) + (1.0 / (x + 3.0))) : F32)
  (d - s : F32)

def chi2_log_mean(+k: U32) -> F32:
  (digamma_pos((0.5 * U32.to_f32(k) : F32)) + 0.69314718 : F32)

def stvu_term(linear: Bool, +u2: F32, +kf: F32, +kappa: F32) -> F32:
  match linear:
    case True{}:
      F32.sqrt((u2 / kf : F32))
    case False{}:
      (F32.log(u2) - kappa : F32)

def stvu_fin(linear: Bool, +val: F32) -> F32:
  match linear:
    case True{}:
      (val * val : F32)
    case False{}:
      F32.exp(val)

def stvu_accum.go(u_rows: List<&2, List<&2, F32>>, ws: List<&2, F32>, +linear: Bool, +kf: F32, +kappa: F32, +acc: F32) -> F32:
  match u_rows ws:
    case Con{r, rt} Con{w, wt}:
      +u2 = fmax(list_sum_sq.go(r, 0.0), 1.0e-12)
      +term = stvu_term(linear, u2, kf, kappa)
      stvu_accum.go(rt, wt, linear, kf, kappa, (acc + (w * term) : F32))
    case _ _:
      acc

def stvu_mult.with_u(mu: Maybe<&2, L.Mat>, ws: List<&2, F32>, +k: U32, +linear: Bool) -> Maybe<&2, F32>:
  match mu:
    case Some{L.Mat{_, _, u_rows}}:
      +kf = U32.to_f32(k)
      +kappa = chi2_log_mean(k)
      +val = stvu_accum.go(u_rows, ws, linear, kf, kappa, 0.0)
      Some{stvu_fin(linear, val)}
    case None{}:
      None{}

def stvu_mult.with_inv(minv: Maybe<&2, L.Mat>, f_rets: L.Mat, ws: List<&2, F32>, +k: U32, linear: Bool) -> Maybe<&2, F32>:
  match minv:
    case Some{inv_sqrt}:
      stvu_mult.with_u(L.matmul(f_rets, inv_sqrt), ws, k, linear)
    case None{}:
      None{}

def stvu_mult.with_w(mw: Maybe<&2, L.Vec>, f_rets: L.Mat, cov_f: L.Mat, +k: U32, linear: Bool) -> Maybe<&2, F32>:
  match mw:
    case Some{L.Vec{_, ws}}:
      stvu_mult.with_inv(L.spd_pow(cov_f, F32.neg(0.5)), f_rets, ws, k, linear)
    case None{}:
      None{}

def stvu_mult.chk(ok: Bool, f_rets: L.Mat, cov_f: L.Mat, +t: U32, +k: U32, +hl_fast: F32, linear: Bool) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      stvu_mult.with_w(ewma_weights(t, hl_fast), f_rets, cov_f, k, linear)
    case False{}:
      None{}

def stvu_factor_multiplier(+f_rets: L.Mat, +cov_f: L.Mat, +hl_fast: F32, linear_approx: Bool) -> Maybe<&2, F32>:
  L.Mat{+t, +k, _} = f_rets
  L.Mat{+cm, +cn, _} = cov_f
  +ok = Bool.and(U32.is_gt(t, 0), Bool.and(U32.is_gt(k, 0), Bool.and(U32.is_eq(k, cm), Bool.and(U32.is_eq(cm, cn), F32.is_gt(hl_fast, 0.0)))))
  stvu_mult.chk(ok, f_rets, cov_f, t, k, hl_fast, linear_approx)

def stvu_adjust.fin(mm: Maybe<&2, F32>, cov_f: L.Mat) -> Maybe<&2, L.Mat>:
  match mm:
    case Some{mult}:
      Some{sym_scale(mult, cov_f)}
    case None{}:
      None{}

def stvu_adjust_cov(f_rets: L.Mat, +cov_f: L.Mat, +hl_fast: F32, linear_approx: Bool) -> Maybe<&2, L.Mat>:
  stvu_adjust.fin(stvu_factor_multiplier(f_rets, cov_f, hl_fast, linear_approx), cov_f)

# ---------------------------------------------------------------- Autocorrelation Adjustment: Cohen & Newey-West (Ch 6.3.4)

type LagAcc is Type:
  LagAcc{x: Array<F32>, w: Array<F32>, acc: F32}

def lag_dot.s3(pw: Array<F32> & F32, x: Array<F32>, +term: F32, +acc: F32) -> LagAcc:
  (w, wt) = pw
  LagAcc{x, w, (acc + (wt * term) : F32)}

def lag_dot.s2b(p: Array<F32> & F32, w: Array<F32>, +xti: F32, +xtj: F32, +xtli: F32, +t: U32, +acc: F32) -> LagAcc:
  (x, xtlj) = p
  lag_dot.s3(Array.get(F32, w, t), x, ((xti * xtlj) + (xtj * xtli) : F32), acc)

def lag_dot.s2a(p: Array<F32> & F32, w: Array<F32>, +xti: F32, +xtj: F32, +idx_tlj: U32, +t: U32, +acc: F32) -> LagAcc:
  (x, xtli) = p
  lag_dot.s2b(Array.get(F32, x, idx_tlj), w, xti, xtj, xtli, t, acc)

def lag_dot.s1b(p: Array<F32> & F32, w: Array<F32>, +xti: F32, +idx_tli: U32, +idx_tlj: U32, +t: U32, +acc: F32) -> LagAcc:
  (x, xtj) = p
  lag_dot.s2a(Array.get(F32, x, idx_tli), w, xti, xtj, idx_tlj, t, acc)

def lag_dot.s1a(p: Array<F32> & F32, w: Array<F32>, +idx_tj: U32, +idx_tli: U32, +idx_tlj: U32, +t: U32, +acc: F32) -> LagAcc:
  (x, xti) = p
  lag_dot.s1b(Array.get(F32, x, idx_tj), w, xti, idx_tli, idx_tlj, t, acc)

def lag_dot.go(rem: Nat, st: LagAcc, +t: U32, +lag: U32, +i: U32, +j: U32, +k: U32) -> LagAcc:
  match rem:
    case 0n:
      st
    case 1n+p:
      LagAcc{x, w, acc} = st
      +tl = (t - lag : U32)
      st1 = lag_dot.s1a(Array.get(F32, x, ((t * k) + i : U32)), w, ((t * k) + j : U32), ((tl * k) + i : U32), ((tl * k) + j : U32), t, acc)
      lag_dot.go(p, st1, (t + 1 : U32), lag, i, j, k)

def lag0_dot.s2(p: Array<F32> & F32, w: Array<F32>, +xti: F32, +t: U32, +acc: F32) -> LagAcc:
  (x, xtj) = p
  lag_dot.s3(Array.get(F32, w, t), x, (xti * xtj : F32), acc)

def lag0_dot.s1(p: Array<F32> & F32, w: Array<F32>, +idx_tj: U32, +t: U32, +acc: F32) -> LagAcc:
  (x, xti) = p
  lag0_dot.s2(Array.get(F32, x, idx_tj), w, xti, t, acc)

def lag0_dot.go(rem: Nat, st: LagAcc, +t: U32, +i: U32, +j: U32, +k: U32) -> LagAcc:
  match rem:
    case 0n:
      st
    case 1n+p:
      LagAcc{x, w, acc} = st
      st1 = lag0_dot.s1(Array.get(F32, x, ((t * k) + i : U32)), w, ((t * k) + j : U32), t, acc)
      lag0_dot.go(p, st1, (t + 1 : U32), i, j, k)

def lag_kernel(is_nw: Bool, +lag: U32, +l_max: U32) -> F32:
  match is_nw:
    case True{}:
      (1.0 - (U32.to_f32(lag) / U32.to_f32((l_max + 1 : U32))) : F32)
    case False{}:
      0.5

def hac_cell.add(st1: LagAcc, +total: F32, +kw: F32) -> LagAcc:
  LagAcc{x1, w1, c_sym} = st1
  LagAcc{x1, w1, (total + (kw * c_sym) : F32)}

def hac_cell.lags(rem: Nat, st: LagAcc, +lag: U32, +l_max: U32, +is_nw: Bool, +t: U32, +i: U32, +j: U32, +k: U32) -> LagAcc:
  match rem:
    case 0n:
      st
    case 1n+p:
      LagAcc{x, w, total} = st
      +cnt = (t - lag : U32)
      +kw = lag_kernel(is_nw, lag, l_max)
      st2 = hac_cell.add(lag_dot.go(U32.to_nat(cnt), LagAcc{x, w, 0.0}, lag, lag, i, j, k), total, kw)
      hac_cell.lags(p, st2, (lag + 1 : U32), l_max, is_nw, t, i, j, k)

type HacRow is Type:
  HacRow{x: Array<F32>, w: Array<F32>, row: List<&2, F32>}

def hac_row.push(st: LagAcc, row: List<&2, F32>) -> HacRow:
  LagAcc{x, w, val} = st
  HacRow{x, w, val <> row}

def hac_row.j(rem: Nat, st: HacRow, +i: U32, +j: U32, +t: U32, +k: U32, +l_eff: U32, +l_max: U32, +is_nw: Bool) -> HacRow:
  match rem:
    case 0n:
      st
    case 1n+p:
      HacRow{x, w, row} = st
      st0 = lag0_dot.go(U32.to_nat(t), LagAcc{x, w, 0.0}, 0, i, j, k)
      st1 = hac_cell.lags(U32.to_nat(l_eff), st0, 1, l_max, is_nw, t, i, j, k)
      hac_row.j(p, hac_row.push(st1, row), i, (j - 1 : U32), t, k, l_eff, l_max, is_nw)

type HacTri is Type:
  HacTri{x: Array<F32>, w: Array<F32>, upper: List<&2, List<&2, F32>>}

def hac_tri.push(st: HacRow, upper: List<&2, List<&2, F32>>) -> HacTri:
  HacRow{x, w, row} = st
  HacTri{x, w, row <> upper}

def hac_tri.i(rem: Nat, st: HacTri, +row_len: Nat, +i: U32, +t: U32, +k: U32, +l_eff: U32, +l_max: U32, +is_nw: Bool) -> List<&2, List<&2, F32>>:
  match rem:
    case 0n:
      HacTri{_, _, upper} = st
      upper
    case 1n+p:
      HacTri{x, w, upper} = st
      st1 = hac_tri.push(hac_row.j(row_len, HacRow{x, w, Nil{}}, i, (k - 1 : U32), t, k, l_eff, l_max, is_nw), upper)
      hac_tri.i(p, st1, 1n+row_len, (i - 1 : U32), t, k, l_eff, l_max, is_nw)

def fill_vec_arr(xs: List<&2, F32>, a: Array<F32>, +idx: U32) -> Array<F32>:
  match xs:
    case Nil{}:
      a
    case Con{v, t}:
      fill_vec_arr(t, Array.set(F32, a, idx, v), (idx + 1 : U32))

def vec_to_arr(xs: List<&2, F32>, +n: U32) -> Array<F32>:
  fill_vec_arr(xs, Array.new(F32, arr_depth(n), 0.0), 0)

def hac_cov.with_w(ws: List<&2, F32>, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>, +l_max: U32, is_nw: Bool) -> L.Mat:
  +l_eff = U32.min(l_max, (t - 1 : U32))
  xa = mat_to_arr(rows, t, k)
  wa = vec_to_arr(ws, t)
  +upper = hac_tri.i(U32.to_nat(k), HacTri{xa, wa, Nil{}}, 1n, (k - 1 : U32), t, k, l_eff, l_max, is_nw)
  L.Mat{k, k, mirror_upper(upper)}

def hac_cov.from_mw(mw: Maybe<&2, L.Vec>, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>, +l_max: U32, is_nw: Bool) -> Maybe<&2, L.Mat>:
  match mw:
    case Some{L.Vec{_, ws}}:
      Some{hac_cov.with_w(ws, t, k, rows, l_max, is_nw)}
    case None{}:
      None{}

def hac_cov.resolve_w(use_ewma: Bool, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>, +l_max: U32, +half_life: F32, is_nw: Bool) -> Maybe<&2, L.Mat>:
  match use_ewma:
    case True{}:
      hac_cov.from_mw(ewma_weights(t, half_life), t, k, rows, l_max, is_nw)
    case False{}:
      +ws = List.replicate(F32, U32.to_nat(t), (1.0 / U32.to_f32(t) : F32))
      Some{hac_cov.with_w(ws, t, k, rows, l_max, is_nw)}

def hac_cov.chk(ok: Bool, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>, +l_max: U32, +half_life: F32, is_nw: Bool) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      hac_cov.resolve_w(F32.is_gt(half_life, 0.0), t, k, rows, l_max, half_life, is_nw)
    case False{}:
      None{}

def cov_newey_west(x: L.Mat, +l_max: U32, +half_life: F32) -> Maybe<&2, L.Mat>:
  L.Mat{+t, +k, rows} = x
  hac_cov.chk(Bool.and(U32.is_gt(t, 0), U32.is_gt(k, 0)), t, k, rows, l_max, half_life, True{})

def cov_autocorr_cohen(x: L.Mat, +l_max: U32, +half_life: F32) -> Maybe<&2, L.Mat>:
  L.Mat{+t, +k, rows} = x
  hac_cov.chk(Bool.and(U32.is_gt(t, 0), U32.is_gt(k, 0)), t, k, rows, l_max, half_life, False{})

# ---------------------------------------------------------------- Idiosyncratic Variance Estimation (Ch 6.4)

def idio_var_acc.go(rows: List<&2, List<&2, F32>>, ws: List<&2, F32>, acc: List<&2, F32>) -> List<&2, F32>:
  match rows ws:
    case Con{r, rt} Con{w, wt}:
      idio_var_acc.go(rt, wt, list_axpy(w, list_sq(r), acc))
    case _ _:
      acc

def idio_var_ewma.with_w(mw: Maybe<&2, L.Vec>, +n: U32, rows: List<&2, List<&2, F32>>) -> Maybe<&2, L.Vec>:
  match mw:
    case Some{L.Vec{_, ws}}:
      Some{L.Vec{n, idio_var_acc.go(rows, ws, List.replicate(F32, U32.to_nat(n), 0.0))}}
    case None{}:
      None{}

def idio_var_ewma.mode(use_ewma: Bool, +t: U32, +n: U32, rows: List<&2, List<&2, F32>>, +half_life: F32) -> Maybe<&2, L.Vec>:
  match use_ewma:
    case True{}:
      idio_var_ewma.with_w(ewma_weights(t, half_life), n, rows)
    case False{}:
      +ws = List.replicate(F32, U32.to_nat(t), (1.0 / U32.to_f32(t) : F32))
      Some{L.Vec{n, idio_var_acc.go(rows, ws, List.replicate(F32, U32.to_nat(n), 0.0))}}

def idio_var_ewma.chk(ok: Bool, +t: U32, +n: U32, rows: List<&2, List<&2, F32>>, +half_life: F32) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      idio_var_ewma.mode(F32.is_gt(half_life, 0.0), t, n, rows, half_life)
    case False{}:
      None{}

def idio_var_ewma(eps: L.Mat, +half_life: F32) -> Maybe<&2, L.Vec>:
  L.Mat{+t, +n, rows} = eps
  idio_var_ewma.chk(Bool.and(U32.is_gt(t, 0), U32.is_gt(n, 0)), t, n, rows, half_life)

def idio_shrink.go(xs: List<&2, F32>, +omr: F32, +add: F32) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      ((omr * h) + add : F32) <> idio_shrink.go(t, omr, add)

def idio_var_shrink.chk(ok: Bool, +n: U32, +xs: List<&2, F32>, +rho: F32) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      +mean = (list_sum(xs) / U32.to_f32(n) : F32)
      Some{L.Vec{n, idio_shrink.go(xs, (1.0 - rho : F32), (rho * mean : F32))}}
    case False{}:
      None{}

def idio_var_shrink(idio_var: L.Vec, +rho: F32) -> Maybe<&2, L.Vec>:
  L.Vec{+n, xs} = idio_var
  +ok = Bool.and(U32.is_gt(n, 0), Bool.and(F32.is_ge(rho, 0.0), F32.is_le(rho, 1.0)))
  idio_var_shrink.chk(ok, n, xs, rho)

# Short-Term Idio Volatility Update (Ch 6.4.3)
def idio_stvu_row_stat(erow: List<&2, F32>, arow: List<&2, F32>, ivar: List<&2, F32>, +num: F32, +den: F32) -> F32 & F32:
  match erow arow ivar:
    case Con{+e, et} Con{+a, at} Con{v, vt}:
      +z2 = ((e * e) / fmax(v, 1.0e-12) : F32)
      idio_stvu_row_stat(et, at, vt, (num + (a * z2) : F32), (den + a : F32))
    case _ _ _:
      (num, den)

def idio_stvu_mult.step(p: F32 & F32, st: F32 & F32, +w: F32) -> F32 & F32:
  (+num, +den) = p
  (+acc, +wsum) = st
  +has = F32.is_gt(den, 1.0e-12)
  +ratio = Bool.pick(F32, has, F32.sqrt((num / den : F32)), 0.0)
  +w_add = Bool.pick(F32, has, w, 0.0)
  ((acc + (w_add * ratio) : F32), (wsum + w_add : F32))

def idio_stvu_mult.fin(st: F32 & F32) -> F32:
  (+acc, +wsum) = st
  +v = Bool.pick(F32, F32.is_gt(wsum, 1.0e-12), (acc / wsum : F32), 1.0)
  (v * v : F32)

def idio_stvu_mult.go(erows: List<&2, List<&2, F32>>, arows: List<&2, List<&2, F32>>, +ivar: List<&2, F32>, ws: List<&2, F32>, st: F32 & F32) -> F32:
  match erows arows ws:
    case Con{er, ert} Con{ar, art} Con{w, wt}:
      idio_stvu_mult.go(ert, art, ivar, wt, idio_stvu_mult.step(idio_stvu_row_stat(er, ar, ivar, 0.0, 0.0), st, w))
    case _ _ _:
      idio_stvu_mult.fin(st)

def last_row(rows: List<&2, List<&2, F32>>) -> List<&2, F32>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, Nil{}}:
      r
    case Con{_, rt}:
      last_row(rt)

def idio_stvu_apply(ivar: List<&2, F32>, a_last: List<&2, F32>, +mult: F32) -> List<&2, F32>:
  match ivar a_last:
    case Con{v, vt} Con{+a, at}:
      +scale = ((1.0 - a) + (a * mult) : F32)
      (scale * v : F32) <> idio_stvu_apply(vt, at, mult)
    case _ _:
      Nil{}

def idio_stvu.with_w(mw: Maybe<&2, L.Vec>, erows: List<&2, List<&2, F32>>, +arows: List<&2, List<&2, F32>>, +n: U32, +ivar: List<&2, F32>) -> Maybe<&2, L.Vec>:
  match mw:
    case Some{L.Vec{_, ws}}:
      +mult = idio_stvu_mult.go(erows, arows, ivar, ws, (0.0, 0.0))
      Some{L.Vec{n, idio_stvu_apply(ivar, last_row(arows), mult)}}
    case None{}:
      None{}

def idio_stvu.chk(ok: Bool, +t: U32, +n: U32, erows: List<&2, List<&2, F32>>, arows: List<&2, List<&2, F32>>, ivar: List<&2, F32>, +hl_fast: F32) -> Maybe<&2, L.Vec>:
  match ok:
    case True{}:
      idio_stvu.with_w(ewma_weights(t, hl_fast), erows, arows, n, ivar)
    case False{}:
      None{}

def idio_stvu(eps: L.Mat, idio_var: L.Vec, event_weights: L.Mat, +hl_fast: F32) -> Maybe<&2, L.Vec>:
  L.Mat{+t, +n, erows} = eps
  L.Vec{+dn, +ivar} = idio_var
  L.Mat{+at, +an, arows} = event_weights
  +ok = Bool.and(U32.is_gt(t, 0), Bool.and(U32.is_gt(n, 0), Bool.and(U32.is_eq(n, dn), Bool.and(U32.is_eq(t, at), Bool.and(U32.is_eq(n, an), Bool.and(F32.is_gt(hl_fast, 0.0), all_pos(ivar)))))))
  idio_stvu.chk(ok, t, n, erows, arows, ivar, hl_fast)

# ---------------------------------------------------------------- Idiosyncratic Correlation Clustering (Ch 6.4.4)

def cai_threshold.chk(ok: Bool, +n: U32, +t: U32, +k_const: F32) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      Some{(k_const * F32.sqrt((F32.log(U32.to_f32(n)) / U32.to_f32(t) : F32)) : F32)}
    case False{}:
      None{}

def cai_threshold(+n: U32, +t: U32, +k_const: F32) -> Maybe<&2, F32>:
  cai_threshold.chk(Bool.and(U32.is_gt(n, 1), Bool.and(U32.is_gt(t, 0), F32.is_gt(k_const, 0.0))), n, t, k_const)

def fill_cm_row(r: List<&2, F32>, a: Array<F32>, +idx: U32, +stride: U32) -> Array<F32>:
  match r:
    case Nil{}:
      a
    case Con{x, t}:
      fill_cm_row(t, Array.set(F32, a, idx, x), (idx + stride : U32), stride)

def fill_cm_mat(rows: List<&2, List<&2, F32>>, a: Array<F32>, +row_i: U32, +m: U32) -> Array<F32>:
  match rows:
    case Nil{}:
      a
    case Con{r, t}:
      fill_cm_mat(t, fill_cm_row(r, a, row_i, m), (row_i + 1 : U32), m)

def mat_to_cm(rows: List<&2, List<&2, F32>>, +m: U32, +n: U32) -> Array<F32>:
  fill_cm_mat(rows, Array.new(F32, arr_depth((m * n : U32)), 0.0), 0, m)

def col_sum_sq.step(p: Array<F32> & F32, +acc: F32) -> Array<F32> & F32:
  (a, +v) = p
  (a, (acc + (v * v) : F32))

def col_sum_sq(rem: Nat, st: Array<F32> & F32, +idx: U32) -> Array<F32> & F32:
  match rem:
    case 0n:
      st
    case 1n+p:
      (a, acc) = st
      col_sum_sq(p, col_sum_sq.step(Array.get(F32, a, idx), acc), (idx + 1 : U32))

def col_dot_cm.s2(p: Array<F32> & F32, +v1: F32, +acc: F32) -> Array<F32> & F32:
  (a, v2) = p
  (a, (acc + (v1 * v2) : F32))

def col_dot_cm.s1(p: Array<F32> & F32, +i2: U32, +acc: F32) -> Array<F32> & F32:
  (a, v1) = p
  col_dot_cm.s2(Array.get(F32, a, i2), v1, acc)

def col_dot_cm(rem: Nat, st: Array<F32> & F32, +i1: U32, +i2: U32) -> Array<F32> & F32:
  match rem:
    case 0n:
      st
    case 1n+p:
      (a, acc) = st
      col_dot_cm(p, col_dot_cm.s1(Array.get(F32, a, i1), i2, acc), (i1 + 1 : U32), (i2 + 1 : U32))

def col_scale_cm.step(p: Array<F32> & F32, +idx: U32, +sc: F32) -> Array<F32>:
  (a, v) = p
  Array.set(F32, a, idx, (v * sc : F32))

def col_scale_cm(rem: Nat, a: Array<F32>, +idx: U32, +sc: F32) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+p:
      col_scale_cm(p, col_scale_cm.step(Array.get(F32, a, idx), idx, sc), (idx + 1 : U32), sc)

def norm_cols.one(p: Array<F32> & F32, +off: U32, +tt: Nat) -> Array<F32>:
  (a, ss) = p
  +nrm = F32.sqrt(ss)
  +sc = Bool.pick(F32, F32.is_gt(nrm, 1.0e-12), (1.0 / nrm : F32), 0.0)
  col_scale_cm(tt, a, off, sc)

def norm_cols.go(rem: Nat, a: Array<F32>, +j: U32, +t: U32, +tt: Nat) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+p:
      +off = (j * t : U32)
      norm_cols.go(p, norm_cols.one(col_sum_sq(tt, (a, 0.0), off), off, tt), (j + 1 : U32), t, tt)

type ClustSt is Type:
  ClustSt{a: Array<F32>, pairs: List<&2, CorrPair>}

def clust.push_chk(keep: Bool, a: Array<F32>, pairs: List<&2, CorrPair>, +i: U32, +j: U32, +rho: F32) -> ClustSt:
  match keep:
    case True{}:
      ClustSt{a, CorrPair{i, j, rho} <> pairs}
    case False{}:
      ClustSt{a, pairs}

def clust.push(p: Array<F32> & F32, pairs: List<&2, CorrPair>, +i: U32, +j: U32, +thresh: F32) -> ClustSt:
  (a, +rho) = p
  clust.push_chk(F32.is_gt(F32.abs(rho), thresh), a, pairs, i, j, rho)

def clust.j(rem: Nat, st: ClustSt, +i: U32, +j: U32, +t: U32, +tt: Nat, +thresh: F32) -> ClustSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      ClustSt{a, pairs} = st
      st1 = clust.push(col_dot_cm(tt, (a, 0.0), (i * t : U32), (j * t : U32)), pairs, i, j, thresh)
      clust.j(p, st1, i, (j + 1 : U32), t, tt, thresh)

def clust.i(rem: Nat, st: ClustSt, +i: U32, +n: U32, +t: U32, +tt: Nat, +thresh: F32) -> List<&2, CorrPair>:
  match rem:
    case 0n:
      ClustSt{_, pairs} = st
      List.reverse(&2, CorrPair, pairs)
    case 1n+p:
      +j0 = (i + 1 : U32)
      +cnt = (n - j0 : U32)
      clust.i(p, clust.j(U32.to_nat(cnt), st, i, j0, t, tt, thresh), (i + 1 : U32), n, t, tt, thresh)

def idio_corr_clusters.chk(ok: Bool, +t: U32, +n: U32, +rows: List<&2, List<&2, F32>>, +threshold: F32) -> Maybe<&2, List<&2, CorrPair>>:
  match ok:
    case True{}:
      +ws = List.replicate(F32, U32.to_nat(t), (1.0 / U32.to_f32(t) : F32))
      +crows = center_rows(rows, ws, n)
      a0 = mat_to_cm(crows, t, n)
      +tt = U32.to_nat(t)
      a1 = norm_cols.go(U32.to_nat(n), a0, 0, t, tt)
      Some{clust.i(U32.to_nat(n), ClustSt{a1, Nil{}}, 0, n, t, tt, threshold)}
    case False{}:
      None{}

def idio_corr_clusters(eps: L.Mat, +threshold: F32) -> Maybe<&2, List<&2, CorrPair>>:
  L.Mat{+t, +n, rows} = eps
  +ok = Bool.and(U32.is_gt(t, 1), Bool.and(U32.is_gt(n, 0), Bool.and(F32.is_ge(threshold, 0.0), F32.is_le(threshold, 1.0))))
  idio_corr_clusters.chk(ok, t, n, rows, threshold)

# ---------------------------------------------------------------- Causal Log-MAD Winsorization (Ch 6.5)

type TwoF32 is Data:
  TwoF32{l: List<&2, F32>, r: List<&2, F32>}

def msort_split.cons(x: F32, y: F32, two: TwoF32) -> TwoF32:
  TwoF32{ls, rs} = two
  TwoF32{x <> ls, y <> rs}

def msort_split(xs: List<&2, F32>) -> TwoF32:
  match xs:
    case Nil{}:
      TwoF32{Nil{}, Nil{}}
    case Con{x, Nil{}}:
      TwoF32{x <> Nil{}, Nil{}}
    case Con{x, Con{y, rest}}:
      msort_split.cons(x, y, msort_split(rest))

def msort_mrg(xs: List<&2, F32>, ys: List<&2, F32>, +x: F32, +y: F32, le: Bool) -> List<&2, F32>:
  match xs ys le:
    case Nil{} _ True{}:
      x <> y <> ys
    case Con{+x1, xt} _ True{}:
      x <> msort_mrg(xt, ys, x1, y, F32.is_le(x1, y))
    case _ Nil{} False{}:
      y <> x <> xs
    case _ Con{+y1, yt} False{}:
      y <> msort_mrg(xs, yt, x, y1, F32.is_le(x, y1))

def msort_merge(xs: List<&2, F32>, ys: List<&2, F32>) -> List<&2, F32>:
  match xs ys:
    case Nil{} _:
      ys
    case _ Nil{}:
      xs
    case Con{+x, xt} Con{+y, yt}:
      msort_mrg(xt, yt, x, y, F32.is_le(x, y))

def msort_isort(xs: List<&2, F32>) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      msort_merge(x <> Nil{}, msort_isort(t))

def msort_f32.go(fuel: Nat, two: TwoF32) -> List<&2, F32>:
  match fuel:
    case 0n:
      TwoF32{l, r} = two
      msort_merge(msort_isort(l), msort_isort(r))
    case 1n+(+p):
      TwoF32{l, r} = two
      msort_merge(msort_f32.go(p, msort_split(l)), msort_f32.go(p, msort_split(r)))

def msort_f32(xs: List<&2, F32>) -> List<&2, F32>:
  msort_f32.go(16n, msort_split(xs))

def median_pick(is_odd: Bool, +xs: List<&2, F32>, +half: Nat) -> F32:
  match is_odd:
    case True{}:
      maybe_f32(List.get(&2, F32, xs, half), 0.0)
    case False{}:
      +v1 = maybe_f32(List.get(&2, F32, xs, Nat.sub(half, 1n)), 0.0)
      +v2 = maybe_f32(List.get(&2, F32, xs, half), 0.0)
      (0.5 * (v1 + v2) : F32)

def median_sorted.len(len: Nat, +xs: List<&2, F32>) -> F32:
  match len:
    case 0n:
      0.0
    case 1n+(+p):
      median_pick(Nat.is_eq(Nat.mod(1n+p, 2n), 1n), xs, Nat.div(1n+p, 2n))

def median_sorted(+xs: List<&2, F32>) -> F32:
  median_sorted.len(List.length(&2, F32, xs), xs)

def median_f32(xs: List<&2, F32>) -> F32:
  median_sorted(msort_f32(xs))

# Generic strictly causal left scan over rows (for scan_causal proof!).
def scan(~A: Data, ~B: Data, ~S: Data, ~next: S -> A -> S, ~out: S -> A -> B, xs: List<&2, A>, +s: S) -> List<&2, B>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      out(s, x) <> scan(~A, ~B, ~S, ~next, ~out, t, next(s, x))

def take_n(-A: Data, k: Nat, xs: List<&2, A>) -> List<&2, A>:
  match k xs:
    case 0n _:
      Nil{}
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{h, t}:
      h <> take_n(A, p, t)

type WinState is Data:
  WinState{w: Nat, d_max: F32, hist: List<&2, List<&2, F32>>}

def winsor_clip_chk(do_clip: Bool, +r: F32, +lr: F32, +lim: F32) -> F32:
  match do_clip:
    case True{}:
      (F32.exp(clip(lr, F32.neg(lim), lim)) - 1.0 : F32)
    case False{}:
      r

def winsor_out_asset(+r: F32, +h: List<&2, F32>, +d_max: F32) -> F32:
  +lr = F32.log(fmax((1.0 + r : F32), 1.0e-6))
  +alr = F32.abs(lr)
  +med = median_f32(h)
  +lim = (d_max * med : F32)
  winsor_clip_chk(Bool.and(F32.is_gt(med, 1.0e-12), F32.is_gt(alr, lim)), r, lr, lim)

def winsor_out_row(row: List<&2, F32>, hist: List<&2, List<&2, F32>>, +d_max: F32) -> List<&2, F32>:
  match row hist:
    case Con{r, rt} Con{h, ht}:
      winsor_out_asset(r, h, d_max) <> winsor_out_row(rt, ht, d_max)
    case _ _:
      Nil{}

def winsor_next_hist(row: List<&2, F32>, hist: List<&2, List<&2, F32>>, +w: Nat) -> List<&2, List<&2, F32>>:
  match row hist:
    case Con{r, rt} Con{h, ht}:
      +alr = F32.abs(F32.log(fmax((1.0 + r : F32), 1.0e-6)))
      take_n(F32, w, alr <> h) <> winsor_next_hist(rt, ht, w)
    case _ _:
      Nil{}

def winsor_out(st: WinState, row: List<&2, F32>) -> List<&2, F32>:
  WinState{_, d_max, hist} = st
  winsor_out_row(row, hist, d_max)

def winsor_next(st: WinState, row: List<&2, F32>) -> WinState:
  WinState{+w, d_max, hist} = st
  WinState{w, d_max, winsor_next_hist(row, hist, w)}

def winsorize_log_mad.chk(ok: Bool, +t: U32, +n: U32, rows: List<&2, List<&2, F32>>, +window: U32, +d_max: F32) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      +init_hist = List.replicate(List<&2, F32>, U32.to_nat(n), Nil{})
      +out_rows = scan(~List<&2, F32>, ~List<&2, F32>, ~WinState, ~winsor_next, ~winsor_out, rows, WinState{U32.to_nat(window), d_max, init_hist})
      Some{L.Mat{t, n, out_rows}}
    case False{}:
      None{}

def winsorize_log_mad(returns: L.Mat, +window: U32, +d_max: F32) -> Maybe<&2, L.Mat>:
  L.Mat{+t, +n, rows} = returns
  +ok = Bool.and(U32.is_gt(window, 0), F32.is_gt(d_max, 0.0))
  winsorize_log_mad.chk(ok, t, n, rows, window, d_max)

# ---------------------------------------------------------------- Multi-Region / Asset-Class Linking (Ch 6.6.1)

def sum_block_sizes.add(ok: Bool, +m: U32, rest: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match ok rest:
    case True{} Some{s}:
      Some{(m + s : U32)}
    case _ _:
      None{}

def sum_block_sizes(blocks: List<&2, L.Mat>) -> Maybe<&2, U32>:
  match blocks:
    case Nil{}:
      Some{0}
    case Con{L.Mat{+m, +n, _}, rest}:
      sum_block_sizes.add(Bool.and(U32.is_eq(m, n), U32.is_gt(m, 0)), m, sum_block_sizes(rest))

def compute_c_one.pows(mv: Maybe<&2, L.Mat>, ml: Maybe<&2, L.Mat>) -> Maybe<&2, L.Mat>:
  match mv ml:
    case Some{vii_mhalf} Some{loc_half}:
      L.matmul(vii_mhalf, loc_half)
    case _ _:
      None{}

def compute_c_one(loc: L.Mat, joint: L.Mat, +off: U32, +ki: U32) -> Maybe<&2, L.Mat>:
  +vii = L.submatrix(joint, off, ki, off, ki)
  compute_c_one.pows(L.spd_pow(vii, F32.neg(0.5)), L.spd_pow(loc, 0.5))

def compute_c.cons(mci: Maybe<&2, L.Mat>, mcs: Maybe<&2, List<&2, L.Mat>>) -> Maybe<&2, List<&2, L.Mat>>:
  match mci mcs:
    case Some{ci} Some{cs}:
      Some{ci <> cs}
    case _ _:
      None{}

def compute_c_blocks(blocks: List<&2, L.Mat>, +joint: L.Mat, +off: U32) -> Maybe<&2, List<&2, L.Mat>>:
  match blocks:
    case Nil{}:
      Some{Nil{}}
    case Con{+loc, rest}:
      L.Mat{+ki, _, _} = loc
      compute_c.cons(compute_c_one(loc, joint, off, ki), compute_c_blocks(rest, joint, (off + ki : U32)))

def place_block_row(r: List<&2, F32>, a: Array<F32>, +idx: U32, +sc: F32) -> Array<F32>:
  match r:
    case Nil{}:
      a
    case Con{v, rt}:
      place_block_row(rt, Array.set(F32, a, idx, (sc * v : F32)), (idx + 1 : U32), sc)

def place_block_rows(rows: List<&2, List<&2, F32>>, a: Array<F32>, +r_idx: U32, +c0: U32, +k_tot: U32, +sc: F32) -> Array<F32>:
  match rows:
    case Nil{}:
      a
    case Con{r, rt}:
      place_block_rows(rt, place_block_row(r, a, ((r_idx * k_tot) + c0 : U32), sc), (r_idx + 1 : U32), c0, k_tot, sc)

def place_diag_blocks(blocks: List<&2, L.Mat>, a: Array<F32>, +off: U32, +k_tot: U32) -> Array<F32>:
  match blocks:
    case Nil{}:
      a
    case Con{L.Mat{+ki, _, rows}, rest}:
      place_diag_blocks(rest, place_block_rows(rows, a, off, off, k_tot, 1.0), (off + ki : U32), k_tot)

def link_place_vt(mvt: Maybe<&2, L.Mat>, a: Array<F32>, +off_i: U32, +off_j: U32, +k_tot: U32, +rho: F32) -> Array<F32>:
  match mvt:
    case Some{L.Mat{_, _, vtilde}}:
      place_block_rows(vtilde, a, off_i, off_j, k_tot, rho)
    case None{}:
      a

def link_place_tmp(mtmp: Maybe<&2, L.Mat>, cj: L.Mat, a: Array<F32>, +off_i: U32, +off_j: U32, +k_tot: U32, +rho: F32) -> Array<F32>:
  match mtmp:
    case Some{tmp}:
      link_place_vt(L.matmul(tmp, cj), a, off_i, off_j, k_tot, rho)
    case None{}:
      a

def link_place_off(same: Bool, ci_t: L.Mat, cj: L.Mat, joint: L.Mat, a: Array<F32>, +off_i: U32, +off_j: U32, +ki: U32, +kj: U32, +k_tot: U32, +rho: F32) -> Array<F32>:
  match same:
    case True{}:
      a
    case False{}:
      +vij = L.submatrix(joint, off_i, ki, off_j, kj)
      link_place_tmp(L.matmul(ci_t, vij), cj, a, off_i, off_j, k_tot, rho)

def link_shrink_off.j(blocks_j: List<&2, L.Mat>, +ci_t: L.Mat, +joint: L.Mat, a: Array<F32>, +off_i: U32, +off_j: U32, +ki: U32, +k_tot: U32, +rho: F32) -> Array<F32>:
  match blocks_j:
    case Nil{}:
      a
    case Con{+cj, rest_j}:
      L.Mat{+kj, _, _} = cj
      a1 = link_place_off(U32.is_eq(off_i, off_j), ci_t, cj, joint, a, off_i, off_j, ki, kj, k_tot, rho)
      link_shrink_off.j(rest_j, ci_t, joint, a1, off_i, (off_j + kj : U32), ki, k_tot, rho)

def link_shrink_off.i(blocks_i: List<&2, L.Mat>, +all_c: List<&2, L.Mat>, +joint: L.Mat, a: Array<F32>, +off_i: U32, +k_tot: U32, +rho: F32) -> Array<F32>:
  match blocks_i:
    case Nil{}:
      a
    case Con{+ci, rest_i}:
      L.Mat{+ki, _, _} = ci
      a1 = link_shrink_off.j(all_c, L.transpose(ci), joint, a, off_i, 0, ki, k_tot, rho)
      link_shrink_off.i(rest_i, all_c, joint, a1, (off_i + ki : U32), k_tot, rho)

def link_models_ir.build(mcs: Maybe<&2, List<&2, L.Mat>>, local_covs: List<&2, L.Mat>, joint_cov: L.Mat, +k_tot: U32, +rho: F32) -> Maybe<&2, L.Mat>:
  match mcs:
    case Some{+cs}:
      a0 = Array.new(F32, arr_depth((k_tot * k_tot : U32)), 0.0)
      a1 = place_diag_blocks(local_covs, a0, 0, k_tot)
      a2 = link_shrink_off.i(cs, cs, joint_cov, a1, 0, k_tot, rho)
      Some{L.Mat{k_tot, k_tot, mirror_upper(upper_sym_from_arr(a2, k_tot))}}
    case None{}:
      None{}

def link_models_ir.chk_ok(ok: Bool, +local_covs: List<&2, L.Mat>, +joint_cov: L.Mat, +k_tot: U32, +rho: F32) -> Maybe<&2, L.Mat>:
  match ok:
    case True{}:
      link_models_ir.build(compute_c_blocks(local_covs, joint_cov, 0), local_covs, joint_cov, k_tot, rho)
    case False{}:
      None{}

def link_models_ir.chk_sum(ms: Maybe<&2, U32>, local_covs: List<&2, L.Mat>, +joint_cov: L.Mat, +rho: F32) -> Maybe<&2, L.Mat>:
  match ms:
    case Some{+k_tot}:
      L.Mat{+jm, +jn, _} = joint_cov
      +ok = Bool.and(U32.is_eq(jm, k_tot), Bool.and(U32.is_eq(jn, k_tot), Bool.and(U32.is_gt(k_tot, 0), Bool.and(F32.is_ge(rho, 0.0), F32.is_le(rho, 1.0)))))
      link_models_ir.chk_ok(ok, local_covs, joint_cov, k_tot, rho)
    case None{}:
      None{}

def link_models_ir(+local_covs: List<&2, L.Mat>, joint_cov: L.Mat, +rho: F32) -> Maybe<&2, L.Mat>:
  link_models_ir.chk_sum(sum_block_sizes(local_covs), local_covs, joint_cov, rho)

# ---------------------------------------------------------------- Currency Rebasing (Ch 6.6.2 Eq 6.14-6.16)

def rebase_row(rem: Nat, +i: U32, +j: U32, +target: U32) -> List<&2, F32>:
  match rem:
    case 0n:
      Nil{}
    case 1n+p:
      +d = Bool.pick(F32, U32.is_eq(i, j), 1.0, 0.0)
      +a = Bool.pick(F32, U32.is_eq(j, target), 1.0, 0.0)
      (d - a : F32) <> rebase_row(p, i, (j + 1 : U32), target)

def rebase_rows(rem: Nat, +i: U32, +q: Nat, +target: U32) -> List<&2, List<&2, F32>>:
  match rem:
    case 0n:
      Nil{}
    case 1n+p:
      rebase_row(q, i, 0, target) <> rebase_rows(p, (i + 1 : U32), q, target)

def rebase_currency.s2(mcov: Maybe<&2, L.Mat>, c_new: L.Mat, +q: U32) -> Maybe<&2, RebaseResult>:
  match mcov:
    case Some{L.Mat{_, _, cov_rows}}:
      Some{RebaseResult{c_new, symmetrize_raw(q, cov_rows)}}
    case None{}:
      None{}

def rebase_currency.s1(mc: Maybe<&2, L.Mat>, mtc: Maybe<&2, L.Mat>, t_mat: L.Mat, +q: U32) -> Maybe<&2, RebaseResult>:
  match mc mtc:
    case Some{c_new} Some{tc}:
      rebase_currency.s2(L.matmul(tc, L.transpose(t_mat)), c_new, q)
    case _ _:
      None{}

def rebase_currency.with_t(+t_mat: L.Mat, c_mat: L.Mat, cov_c: L.Mat, +q: U32) -> Maybe<&2, RebaseResult>:
  rebase_currency.s1(L.matmul(c_mat, t_mat), L.matmul(t_mat, cov_c), t_mat, q)

def rebase_currency.chk(ok: Bool, c_mat: L.Mat, cov_c: L.Mat, +q: U32, +target_idx: U32) -> Maybe<&2, RebaseResult>:
  match ok:
    case True{}:
      +qn = U32.to_nat(q)
      rebase_currency.with_t(L.Mat{q, q, rebase_rows(qn, 0, qn, target_idx)}, c_mat, cov_c, q)
    case False{}:
      None{}

def rebase_currency(+c_mat: L.Mat, +cov_c: L.Mat, +target_idx: U32) -> Maybe<&2, RebaseResult>:
  L.Mat{_, +qc, _} = c_mat
  L.Mat{+cm, +cn, _} = cov_c
  +ok = Bool.and(U32.is_eq(qc, cm), Bool.and(U32.is_eq(cm, cn), U32.is_lt(target_idx, qc)))
  rebase_currency.chk(ok, c_mat, cov_c, qc, target_idx)
