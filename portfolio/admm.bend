# Woodbury-preconditioned ADMM convex QP + L1 solver for portfolio construction.
# Solves:
#   min_w  (rho/2) w^T (B Omega_f B^T + diag(d)) w - alpha^T w
#          + (1/2) (w - w0)^T diag(c2) (w - w0) + sum_i c1_i |w_i - w0_i|
#   s.t.   l_w <= w <= u_w
#          l_c <= A w <= u_c
#          ||w||_1 <= gmv_max   (when gmv_max > 0.0)
#
# Pre-factors C = I_{K+M} + U^T D_tilde^{-1} U = L_C L_C^T ONCE before the loop,
# then runs O(N (K + M)) flat-array iterations with over-relaxation.
# Internal to portfolio; public entry point is portfolio.mvo_constrained.
import Base
import bend-kit-f32array@0.2.1.0/f32array.bend as A
import bend-quant-linalg@0.1.0.0/linalg.bend as L

# ---------------------------------------------------------------- scalar helpers

def fmin(+a: F32, +b: F32) -> F32:
  Bool.pick(F32, F32.is_le(a, b), a, b)

def fmax(+a: F32, +b: F32) -> F32:
  F32.max(a, b)

def clip(+x: F32, +lo: F32, +hi: F32) -> F32:
  fmin(fmax(x, lo), hi)

def soft(+x: F32, +t: F32) -> F32:
  +pos = fmax((x - t : F32), 0.0)
  +neg = fmax(((0.0 - x : F32) - t : F32), 0.0)
  (pos - neg : F32)

# ---------------------------------------------------------------- flat Array<F32> helpers

def arr_depth.go(rem: Nat, +d: Nat, +cap: U32, +n: U32) -> Nat:
  match rem:
    case 0n:
      d
    case 1n+p:
      +lt = U32.is_lt(cap, n)
      arr_depth.go(p, Bool.pick(Nat, lt, 1n+d, d), Bool.pick(U32, lt, (cap << 1n : U32), cap), n)

def arr_depth(+n: U32) -> Nat:
  arr_depth.go(30n, 0n, 1, n)

def fill_list(xs: List<&2, F32>, a: Array<F32>, +idx: U32) -> Array<F32>:
  match xs:
    case Nil{}:
      a
    case Con{x, t}:
      fill_list(t, Array.set(F32, a, idx, x), (idx + 1 : U32))

def vec_to_arr(xs: List<&2, F32>, +n: U32) -> Array<F32>:
  fill_list(xs, Array.new(F32, arr_depth(n), 0.0), 0)

def fill_mat_row(r: List<&2, F32>, a: Array<F32>, +idx: U32) -> Array<F32>:
  match r:
    case Nil{}:
      a
    case Con{x, t}:
      fill_mat_row(t, Array.set(F32, a, idx, x), (idx + 1 : U32))

def fill_mat(rows: List<&2, List<&2, F32>>, a: Array<F32>, +off: U32, +nc: U32) -> Array<F32>:
  match rows:
    case Nil{}:
      a
    case Con{r, t}:
      fill_mat(t, fill_mat_row(r, a, off), (off + nc : U32), nc)

def mat_to_arr(rows: List<&2, List<&2, F32>>, +m: U32, +n: U32) -> Array<F32>:
  fill_mat(rows, Array.new(F32, arr_depth((m * n : U32)), 0.0), 0, n)

type ArrList is Type:
  ArrList{a: Array<F32>, acc: List<&2, F32>}

def arr_to_list.push(p: Array<F32> & F32, acc: List<&2, F32>) -> ArrList:
  (a, v) = p
  ArrList{a, v <> acc}

def arr_to_list.loop(rem: Nat, st: ArrList, +i: U32) -> List<&2, F32>:
  match rem:
    case 0n:
      ArrList{_, acc} = st
      acc
    case 1n+p:
      ArrList{a, acc} = st
      arr_to_list.loop(p, arr_to_list.push(Array.get(F32, a, i), acc), (i - 1 : U32))

def arr_to_list(a: Array<F32>, +n: U32) -> List<&2, F32>:
  arr_to_list.loop(U32.to_nat(n), ArrList{a, Nil{}}, (n - 1 : U32))

# ---------------------------------------------------------------- preprocessing helpers (Data)

def bounds_ok(ls: List<&2, F32>, us: List<&2, F32>) -> Bool:
  match ls us:
    case Nil{} Nil{}:
      True{}
    case Con{l, lt} Con{u, ut}:
      Bool.and(F32.is_le(l, u), bounds_ok(lt, ut))
    case _ _:
      False{}

def any_pos(xs: List<&2, F32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(F32.is_gt(h, 0.0), any_pos(t))

def min_box_l1.go(ls: List<&2, F32>, us: List<&2, F32>, acc: F32) -> F32:
  match ls us:
    case Con{l, lt} Con{u, ut}:
      min_box_l1.go(lt, ut, (acc + F32.abs(clip(0.0, l, u)) : F32))
    case _ _:
      acc

def list_mean.go(xs: List<&2, F32>, acc: F32, +cnt: F32) -> F32:
  match xs:
    case Nil{}:
      Bool.pick(F32, F32.is_gt(cnt, 0.0), (acc / cnt : F32), 1.0)
    case Con{h, t}:
      list_mean.go(t, (acc + h : F32), (cnt + 1.0 : F32))

def scale_list(xs: List<&2, F32>, +s: F32) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      (h * s : F32) <> scale_list(t, s)

def row_norm2.go(r: List<&2, F32>, acc: F32) -> F32:
  match r:
    case Nil{}:
      F32.sqrt(acc)
    case Con{+x, t}:
      row_norm2.go(t, (acc + (x * x : F32) : F32))

type Equil is Data:
  Equil{a_norm: L.Mat, lc_norm: L.Vec, uc_norm: L.Vec, scales: L.Vec}

def equil.cons(r: List<&2, F32>, l: F32, u: F32, s: F32, eq: Equil) -> Equil:
  Equil{L.Mat{m, n, rs}, L.Vec{ml, ls}, L.Vec{mu, us}, L.Vec{ms, ss}} = eq
  Equil{L.Mat{(m + 1 : U32), n, r <> rs}, L.Vec{(ml + 1 : U32), l <> ls}, L.Vec{(mu + 1 : U32), u <> us}, L.Vec{(ms + 1 : U32), s <> ss}}

def equil.go(rows: List<&2, List<&2, F32>>, ls: List<&2, F32>, us: List<&2, F32>, +nc: U32) -> Equil:
  match rows ls us:
    case Con{+r, rt} Con{+l, lt} Con{+u, ut}:
      +nrm = row_norm2.go(r, 0.0)
      +ok = F32.is_gt(nrm, 1.0e-6)
      +sc = Bool.pick(F32, ok, nrm, 1.0)
      +inv = Bool.pick(F32, ok, (1.0 / nrm : F32), 1.0)
      equil.cons(scale_list(r, inv), (l * inv : F32), (u * inv : F32), sc, equil.go(rt, lt, ut, nc))
    case _ _ _:
      Equil{L.Mat{0, nc, Nil{}}, L.Vec{0, Nil{}}, L.Vec{0, Nil{}}, L.Vec{0, Nil{}}}

def equilibrate(a: L.Mat, lc: L.Vec, uc: L.Vec) -> Equil:
  L.Mat{_, n, rows} = a
  L.Vec{_, ls} = lc
  L.Vec{_, us} = uc
  equil.go(rows, ls, us, n)

def hcat_rows(rs1: List<&2, List<&2, F32>>, rs2: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match rs1 rs2:
    case Con{r1, t1} Con{r2, t2}:
      List.append(&2, F32, r1, r2) <> hcat_rows(t1, t2)
    case Nil{} _:
      rs2
    case _ Nil{}:
      rs1

def hcat_mat(a: L.Mat, b: L.Mat) -> L.Mat:
  L.Mat{ma, na, rsa} = a
  L.Mat{_, nb, rsb} = b
  L.Mat{ma, (na + nb : U32), hcat_rows(rsa, rsb)}

def list_dinv(ds: List<&2, F32>, c2s: List<&2, F32>, +rho: F32, +shift: F32) -> List<&2, F32>:
  match ds c2s:
    case Con{d, dt} Con{c2, ct}:
      (1.0 / (((rho * d : F32) + c2 : F32) + shift : F32) : F32) <> list_dinv(dt, ct, rho, shift)
    case _ _:
      Nil{}

def list_diag_scale(ds: List<&2, F32>, c2s: List<&2, F32>, +rho: F32) -> List<&2, F32>:
  match ds c2s:
    case Con{d, dt} Con{c2, ct}:
      ((rho * d : F32) + c2 : F32) <> list_diag_scale(dt, ct, rho)
    case _ _:
      Nil{}

def list_base_rhs(as: List<&2, F32>, c2s: List<&2, F32>, w0s: List<&2, F32>) -> List<&2, F32>:
  match as c2s w0s:
    case Con{a, at} Con{c2, ct} Con{w0, wt}:
      (a + (c2 * w0 : F32) : F32) <> list_base_rhs(at, ct, wt)
    case _ _ _:
      Nil{}

# ---------------------------------------------------------------- flat-array linear algebra kernels

type RhsPack is Type:
  RhsPack{
    base: Array<F32>,
    w0: Array<F32>,
    z1: Array<F32>,
    u1: Array<F32>,
    z2: Array<F32>,
    u2: Array<F32>,
    out: Array<F32>
  }

def rhs.s6(p: Array<F32> & F32, base: Array<F32>, w0: Array<F32>, z1: Array<F32>, u1: Array<F32>, z2: Array<F32>, out: Array<F32>, +i: U32, +vb: F32, +vw0: F32, +vz1: F32, +vu1: F32, +vz2: F32, +mu: F32, +sig2: F32) -> RhsPack:
  (u2, vu2) = p
  +v = ((vb + (mu * (vz1 - vu1 : F32) : F32) : F32) + (sig2 * ((vw0 + vz2 : F32) - vu2 : F32) : F32) : F32)
  RhsPack{base, w0, z1, u1, z2, u2, Array.set(F32, out, i, v)}

def rhs.s5(p: Array<F32> & F32, base: Array<F32>, w0: Array<F32>, z1: Array<F32>, u1: Array<F32>, u2: Array<F32>, out: Array<F32>, +i: U32, +vb: F32, +vw0: F32, +vz1: F32, +vu1: F32, +mu: F32, +sig2: F32) -> RhsPack:
  (z2, vz2) = p
  rhs.s6(Array.get(F32, u2, i), base, w0, z1, u1, z2, out, i, vb, vw0, vz1, vu1, vz2, mu, sig2)

def rhs.s4(p: Array<F32> & F32, base: Array<F32>, w0: Array<F32>, z1: Array<F32>, z2: Array<F32>, u2: Array<F32>, out: Array<F32>, +i: U32, +vb: F32, +vw0: F32, +vz1: F32, +mu: F32, +sig2: F32) -> RhsPack:
  (u1, vu1) = p
  rhs.s5(Array.get(F32, z2, i), base, w0, z1, u1, u2, out, i, vb, vw0, vz1, vu1, mu, sig2)

def rhs.s3(p: Array<F32> & F32, base: Array<F32>, w0: Array<F32>, u1: Array<F32>, z2: Array<F32>, u2: Array<F32>, out: Array<F32>, +i: U32, +vb: F32, +vw0: F32, +mu: F32, +sig2: F32) -> RhsPack:
  (z1, vz1) = p
  rhs.s4(Array.get(F32, u1, i), base, w0, z1, z2, u2, out, i, vb, vw0, vz1, mu, sig2)

def rhs.s2(p: Array<F32> & F32, base: Array<F32>, z1: Array<F32>, u1: Array<F32>, z2: Array<F32>, u2: Array<F32>, out: Array<F32>, +i: U32, +vb: F32, +mu: F32, +sig2: F32) -> RhsPack:
  (w0, vw0) = p
  rhs.s3(Array.get(F32, z1, i), base, w0, u1, z2, u2, out, i, vb, vw0, mu, sig2)

def rhs.s1(p: Array<F32> & F32, w0: Array<F32>, z1: Array<F32>, u1: Array<F32>, z2: Array<F32>, u2: Array<F32>, out: Array<F32>, +i: U32, +mu: F32, +sig2: F32) -> RhsPack:
  (base, vb) = p
  rhs.s2(Array.get(F32, w0, i), base, z1, u1, z2, u2, out, i, vb, mu, sig2)

def build_rhs.go(rem: Nat, pk: RhsPack, +i: U32, +mu: F32, +sig2: F32) -> RhsPack:
  match rem:
    case 0n:
      pk
    case 1n+p:
      RhsPack{base, w0, z1, u1, z2, u2, out} = pk
      build_rhs.go(p, rhs.s1(Array.get(F32, base, i), w0, z1, u1, z2, u2, out, i, mu, sig2), (i + 1 : U32), mu, sig2)

type MatTVec is Type:
  MatTVec{mat: Array<F32>, y: Array<F32>}

def mtv_row.s2(py: Array<F32> & F32, mat: Array<F32>, +mv: F32, +c: F32, +i: U32) -> MatTVec:
  (y, yv) = py
  MatTVec{mat, Array.set(F32, y, i, (yv + (c * mv : F32) : F32))}

def mtv_row.s1(pm: Array<F32> & F32, y: Array<F32>, +c: F32, +i: U32) -> MatTVec:
  (mat, mv) = pm
  mtv_row.s2(Array.get(F32, y, i), mat, mv, c, i)

def mtv_row(rem: Nat, st: MatTVec, +row_off: U32, +i: U32, +c: F32) -> MatTVec:
  match rem:
    case 0n:
      st
    case 1n+p:
      MatTVec{mat, y} = st
      mtv_row(p, mtv_row.s1(Array.get(F32, mat, (row_off + i : U32)), y, c, i), row_off, (i + 1 : U32), c)

type AddAT2 is Type:
  AddAT2{a: Array<F32>, z3: Array<F32>, u3: Array<F32>, y: Array<F32>}

def add_at_diff.wrap(mtv: MatTVec, z3: Array<F32>, u3: Array<F32>) -> AddAT2:
  MatTVec{a2, y2} = mtv
  AddAT2{a2, z3, u3, y2}

def add_at_diff.step2(pu: Array<F32> & F32, a: Array<F32>, z3: Array<F32>, y: Array<F32>, +vz: F32, +j: U32, +n: U32, +mu: F32) -> AddAT2:
  (u3, vu) = pu
  add_at_diff.wrap(mtv_row(U32.to_nat(n), MatTVec{a, y}, (j * n : U32), 0, (mu * (vz - vu : F32) : F32)), z3, u3)

def add_at_diff.step1(pz: Array<F32> & F32, a: Array<F32>, u3: Array<F32>, y: Array<F32>, +j: U32, +n: U32, +mu: F32) -> AddAT2:
  (z3, vz) = pz
  add_at_diff.step2(Array.get(F32, u3, j), a, z3, y, vz, j, n, mu)

def add_at_diff.go(rem: Nat, st: AddAT2, +j: U32, +n: U32, +mu: F32) -> AddAT2:
  match rem:
    case 0n:
      st
    case 1n+p:
      AddAT2{a, z3, u3, y} = st
      add_at_diff.go(p, add_at_diff.step1(Array.get(F32, z3, j), a, u3, y, j, n, mu), (j + 1 : U32), n, mu)

type MatTSt is Type:
  MatTSt{mat: Array<F32>, x: Array<F32>, y: Array<F32>}

def mat_t_mul.wrap(mtv: MatTVec, x: Array<F32>) -> MatTSt:
  MatTVec{mat2, y2} = mtv
  MatTSt{mat2, x, y2}

def mat_t_mul.step(px: Array<F32> & F32, mat: Array<F32>, y: Array<F32>, +j: U32, +nc: U32) -> MatTSt:
  (x, xv) = px
  mat_t_mul.wrap(mtv_row(U32.to_nat(nc), MatTVec{mat, y}, (j * nc : U32), 0, xv), x)

def mat_t_mul.go(rem: Nat, st: MatTSt, +j: U32, +nc: U32) -> MatTSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      MatTSt{mat, x, y} = st
      mat_t_mul.go(p, mat_t_mul.step(Array.get(F32, x, j), mat, y, j, nc), (j + 1 : U32), nc)

type DotSt is Type:
  DotSt{mat: Array<F32>, x: Array<F32>, acc: F32}

def dot_row.s2(px: Array<F32> & F32, mat: Array<F32>, +mv: F32, +acc: F32) -> DotSt:
  (x, xv) = px
  DotSt{mat, x, (acc + (mv * xv : F32) : F32)}

def dot_row.s1(pm: Array<F32> & F32, x: Array<F32>, +c: U32, +acc: F32) -> DotSt:
  (mat, mv) = pm
  dot_row.s2(Array.get(F32, x, c), mat, mv, acc)

def dot_row(rem: Nat, st: DotSt, +row_off: U32, +c: U32) -> DotSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      DotSt{mat, x, acc} = st
      dot_row(p, dot_row.s1(Array.get(F32, mat, (row_off + c : U32)), x, c, acc), row_off, (c + 1 : U32))

type TriInPlace is Type:
  TriInPlace{l: Array<F32>, t: Array<F32>}

def fwd.s2(pt: Array<F32> & F32, l: Array<F32>, +diag: F32, +s: F32, +i: U32) -> TriInPlace:
  (t, ti) = pt
  TriInPlace{l, Array.set(F32, t, i, ((ti - s : F32) / diag : F32))}

def fwd.s1(pl: Array<F32> & F32, t: Array<F32>, +s: F32, +i: U32) -> TriInPlace:
  (l, diag) = pl
  fwd.s2(Array.get(F32, t, i), l, diag, s, i)

def fwd_solve.step(ds: DotSt, +i: U32, +r: U32) -> TriInPlace:
  DotSt{l2, t2, s} = ds
  fwd.s1(Array.get(F32, l2, ((i * r : U32) + i : U32)), t2, s, i)

def fwd_solve.go(rem: Nat, st: TriInPlace, +i: U32, +r: U32) -> TriInPlace:
  match rem:
    case 0n:
      st
    case 1n+p:
      TriInPlace{l, t} = st
      fwd_solve.go(p, fwd_solve.step(dot_row(U32.to_nat(i), DotSt{l, t, 0.0}, (i * r : U32), 0), i, r), (i + 1 : U32), r)

def dot_lt.s2(pt: Array<F32> & F32, l: Array<F32>, +lv: F32, +acc: F32) -> DotSt:
  (t, tv) = pt
  DotSt{l, t, (acc + (lv * tv : F32) : F32)}

def dot_lt.s1(pl: Array<F32> & F32, t: Array<F32>, +k: U32, +acc: F32) -> DotSt:
  (l, lv) = pl
  dot_lt.s2(Array.get(F32, t, k), l, lv, acc)

def dot_lt(rem: Nat, st: DotSt, +k: U32, +i: U32, +r: U32) -> DotSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      DotSt{l, t, acc} = st
      dot_lt(p, dot_lt.s1(Array.get(F32, l, ((k * r : U32) + i : U32)), t, k, acc), (k + 1 : U32), i, r)

def bwd_solve.go(rem: Nat, st: TriInPlace, +i: U32, +r: U32) -> TriInPlace:
  match rem:
    case 0n:
      st
    case 1n+p:
      TriInPlace{l, t} = st
      +cnt = ((r - 1 : U32) - i : U32)
      bwd_solve.go(p, fwd_solve.step(dot_lt(U32.to_nat(cnt), DotSt{l, t, 0.0}, (i + 1 : U32), i, r), i, r), (i - 1 : U32), r)

type MulDinv is Type:
  MulDinv{d_inv: Array<F32>, y: Array<F32>}

def mul_dinv.s2(py: Array<F32> & F32, d_inv: Array<F32>, +dv: F32, +i: U32) -> MulDinv:
  (y, yv) = py
  MulDinv{d_inv, Array.set(F32, y, i, (dv * yv : F32))}

def mul_dinv.s1(pd: Array<F32> & F32, y: Array<F32>, +i: U32) -> MulDinv:
  (d_inv, dv) = pd
  mul_dinv.s2(Array.get(F32, y, i), d_inv, dv, i)

def mul_dinv.go(rem: Nat, st: MulDinv, +i: U32) -> MulDinv:
  match rem:
    case 0n:
      st
    case 1n+p:
      MulDinv{d_inv, y} = st
      mul_dinv.go(p, mul_dinv.s1(Array.get(F32, d_inv, i), y, i), (i + 1 : U32))

type SubUq is Type:
  SubUq{d_inv: Array<F32>, u_arr: Array<F32>, q: Array<F32>, y0: Array<F32>}

def sub_uq.s2(py: Array<F32> & F32, d_inv: Array<F32>, u_arr: Array<F32>, q: Array<F32>, +dv: F32, +uq: F32, +i: U32) -> SubUq:
  (y0, yv) = py
  SubUq{d_inv, u_arr, q, Array.set(F32, y0, i, (yv - (dv * uq : F32) : F32))}

def sub_uq.s1(pd: Array<F32> & F32, u_arr: Array<F32>, q: Array<F32>, y0: Array<F32>, +uq: F32, +i: U32) -> SubUq:
  (d_inv, dv) = pd
  sub_uq.s2(Array.get(F32, y0, i), d_inv, u_arr, q, dv, uq, i)

def sub_uq.after_dot(ds: DotSt, d_inv: Array<F32>, y0: Array<F32>, +i: U32) -> SubUq:
  DotSt{u2, q2, uq} = ds
  sub_uq.s1(Array.get(F32, d_inv, i), u2, q2, y0, uq, i)

def sub_uq.go(rem: Nat, st: SubUq, +i: U32, +r: U32) -> SubUq:
  match rem:
    case 0n:
      st
    case 1n+p:
      SubUq{d_inv, u_arr, q, y0} = st
      sub_uq.go(p, sub_uq.after_dot(dot_row(U32.to_nat(r), DotSt{u_arr, q, 0.0}, (i * r : U32), 0), d_inv, y0, i), (i + 1 : U32), r)

# ---------------------------------------------------------------- box + L1-ball projection & z1/u1 update

type Z1Prep is Type:
  Z1Prep{
    w: Array<F32>,
    z1_old: Array<F32>,
    u1: Array<F32>,
    lw: Array<F32>,
    uw: Array<F32>,
    v1: Array<F32>,
    z1_new: Array<F32>,
    l1_sum: F32,
    vmax: F32
  }

def z1p.s5(puw: Array<F32> & F32, w: Array<F32>, z1_old: Array<F32>, u1: Array<F32>, lw: Array<F32>, v1: Array<F32>, z1_new: Array<F32>, +i: U32, +vw: F32, +vz: F32, +vu: F32, +vl: F32, +l1: F32, +vm: F32, +gamma: F32) -> Z1Prep:
  (uw, vhi) = puw
  +w_hat = ((gamma * vw : F32) + ((1.0 - gamma : F32) * vz : F32) : F32)
  +vv = (w_hat + vu : F32)
  +zc = clip(vv, vl, vhi)
  Z1Prep{w, z1_old, u1, lw, uw, Array.set(F32, v1, i, vv), Array.set(F32, z1_new, i, zc), (l1 + F32.abs(zc) : F32), fmax(vm, F32.abs(vv))}

def z1p.s4(plw: Array<F32> & F32, w: Array<F32>, z1_old: Array<F32>, u1: Array<F32>, uw: Array<F32>, v1: Array<F32>, z1_new: Array<F32>, +i: U32, +vw: F32, +vz: F32, +vu: F32, +l1: F32, +vm: F32, +gamma: F32) -> Z1Prep:
  (lw, vl) = plw
  z1p.s5(Array.get(F32, uw, i), w, z1_old, u1, lw, v1, z1_new, i, vw, vz, vu, vl, l1, vm, gamma)

def z1p.s3(pu: Array<F32> & F32, w: Array<F32>, z1_old: Array<F32>, lw: Array<F32>, uw: Array<F32>, v1: Array<F32>, z1_new: Array<F32>, +i: U32, +vw: F32, +vz: F32, +l1: F32, +vm: F32, +gamma: F32) -> Z1Prep:
  (u1, vu) = pu
  z1p.s4(Array.get(F32, lw, i), w, z1_old, u1, uw, v1, z1_new, i, vw, vz, vu, l1, vm, gamma)

def z1p.s2(pz: Array<F32> & F32, w: Array<F32>, u1: Array<F32>, lw: Array<F32>, uw: Array<F32>, v1: Array<F32>, z1_new: Array<F32>, +i: U32, +vw: F32, +l1: F32, +vm: F32, +gamma: F32) -> Z1Prep:
  (z1_old, vz) = pz
  z1p.s3(Array.get(F32, u1, i), w, z1_old, lw, uw, v1, z1_new, i, vw, vz, l1, vm, gamma)

def z1p.s1(pw: Array<F32> & F32, z1_old: Array<F32>, u1: Array<F32>, lw: Array<F32>, uw: Array<F32>, v1: Array<F32>, z1_new: Array<F32>, +i: U32, +l1: F32, +vm: F32, +gamma: F32) -> Z1Prep:
  (w, vw) = pw
  z1p.s2(Array.get(F32, z1_old, i), w, u1, lw, uw, v1, z1_new, i, vw, l1, vm, gamma)

def z1_prep.go(rem: Nat, st: Z1Prep, +i: U32, +gamma: F32) -> Z1Prep:
  match rem:
    case 0n:
      st
    case 1n+p:
      Z1Prep{w, z1_old, u1, lw, uw, v1, z1_new, l1, vm} = st
      z1_prep.go(p, z1p.s1(Array.get(F32, w, i), z1_old, u1, lw, uw, v1, z1_new, i, l1, vm, gamma), (i + 1 : U32), gamma)

type L1Eval is Type:
  L1Eval{v1: Array<F32>, lw: Array<F32>, uw: Array<F32>, acc: F32}

def l1e.s3(puw: Array<F32> & F32, v1: Array<F32>, lw: Array<F32>, +vv: F32, +vl: F32, +acc: F32, +lam: F32) -> L1Eval:
  (uw, vhi) = puw
  L1Eval{v1, lw, uw, (acc + F32.abs(clip(soft(vv, lam), vl, vhi)) : F32)}

def l1e.s2(plw: Array<F32> & F32, v1: Array<F32>, uw: Array<F32>, +vv: F32, +acc: F32, +i: U32, +lam: F32) -> L1Eval:
  (lw, vl) = plw
  l1e.s3(Array.get(F32, uw, i), v1, lw, vv, vl, acc, lam)

def l1e.s1(pv: Array<F32> & F32, lw: Array<F32>, uw: Array<F32>, +acc: F32, +i: U32, +lam: F32) -> L1Eval:
  (v1, vv) = pv
  l1e.s2(Array.get(F32, lw, i), v1, uw, vv, acc, i, lam)

def l1_eval.go(rem: Nat, st: L1Eval, +i: U32, +lam: F32) -> L1Eval:
  match rem:
    case 0n:
      st
    case 1n+p:
      L1Eval{v1, lw, uw, acc} = st
      l1_eval.go(p, l1e.s1(Array.get(F32, v1, i), lw, uw, acc, i, lam), (i + 1 : U32), lam)

type BisectSt is Type:
  BisectSt{v1: Array<F32>, lw: Array<F32>, uw: Array<F32>, lo: F32, hi: F32}

def bisect_l1.step(ev: L1Eval, +lo: F32, +hi: F32, +mid: F32, +gmv: F32) -> BisectSt:
  L1Eval{v2, lw2, uw2, +s} = ev
  +nlo = Bool.pick(F32, F32.is_gt(s, gmv), mid, lo)
  +nhi = Bool.pick(F32, F32.is_gt(s, gmv), hi, mid)
  BisectSt{v2, lw2, uw2, nlo, nhi}

def bisect_l1.go(rem: Nat, st: BisectSt, +n: U32, +gmv: F32) -> BisectSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      BisectSt{v1, lw, uw, +lo, +hi} = st
      +mid = (0.5 * (lo + hi : F32) : F32)
      bisect_l1.go(p, bisect_l1.step(l1_eval.go(U32.to_nat(n), L1Eval{v1, lw, uw, 0.0}, 0, mid), lo, hi, mid, gmv), n, gmv)

type WriteZ1 is Type:
  WriteZ1{v1: Array<F32>, lw: Array<F32>, uw: Array<F32>, z1_new: Array<F32>}

def wz1.s3(puw: Array<F32> & F32, v1: Array<F32>, lw: Array<F32>, z1_new: Array<F32>, +vv: F32, +vl: F32, +i: U32, +lam: F32) -> WriteZ1:
  (uw, vhi) = puw
  WriteZ1{v1, lw, uw, Array.set(F32, z1_new, i, clip(soft(vv, lam), vl, vhi))}

def wz1.s2(plw: Array<F32> & F32, v1: Array<F32>, uw: Array<F32>, z1_new: Array<F32>, +vv: F32, +i: U32, +lam: F32) -> WriteZ1:
  (lw, vl) = plw
  wz1.s3(Array.get(F32, uw, i), v1, lw, z1_new, vv, vl, i, lam)

def wz1.s1(pv: Array<F32> & F32, lw: Array<F32>, uw: Array<F32>, z1_new: Array<F32>, +i: U32, +lam: F32) -> WriteZ1:
  (v1, vv) = pv
  wz1.s2(Array.get(F32, lw, i), v1, uw, z1_new, vv, i, lam)

def write_z1.go(rem: Nat, st: WriteZ1, +i: U32, +lam: F32) -> WriteZ1:
  match rem:
    case 0n:
      st
    case 1n+p:
      WriteZ1{v1, lw, uw, z1_new} = st
      write_z1.go(p, wz1.s1(Array.get(F32, v1, i), lw, uw, z1_new, i, lam), (i + 1 : U32), lam)

def maybe_bisect.fin(bs: BisectSt, z1_new: Array<F32>, +n: U32) -> WriteZ1:
  BisectSt{v2, lw2, uw2, _, hi} = bs
  write_z1.go(U32.to_nat(n), WriteZ1{v2, lw2, uw2, z1_new}, 0, hi)

def maybe_bisect(need: Bool, v1: Array<F32>, lw: Array<F32>, uw: Array<F32>, z1_new: Array<F32>, +vmax: F32, +n: U32, +gmv: F32) -> WriteZ1:
  match need:
    case True{}:
      maybe_bisect.fin(bisect_l1.go(30n, BisectSt{v1, lw, uw, 0.0, vmax}, n, gmv), z1_new, n)
    case False{}:
      WriteZ1{v1, lw, uw, z1_new}

type Z1Fin is Type:
  Z1Fin{
    w: Array<F32>,
    z1_old: Array<F32>,
    z1_new: Array<F32>,
    v1: Array<F32>,
    u1: Array<F32>,
    r_pri: F32,
    r_dual: F32,
    p_scale: F32,
    d_scale: F32
  }

def z1f.s4(pv: Array<F32> & F32, w: Array<F32>, z1_old: Array<F32>, z1_new: Array<F32>, u1: Array<F32>, +i: U32, +vw: F32, +vzo: F32, +vzn: F32, +rp: F32, +rd: F32, +ps: F32, +ds: F32) -> Z1Fin:
  (v1, vv) = pv
  +un = (vv - vzn : F32)
  +rp2 = fmax(rp, F32.abs((vw - vzn : F32)))
  +rd2 = fmax(rd, F32.abs((vzn - vzo : F32)))
  +ps2 = fmax(ps, fmax(F32.abs(vw), F32.abs(vzn)))
  +ds2 = fmax(ds, F32.abs(un))
  Z1Fin{w, z1_old, z1_new, v1, Array.set(F32, u1, i, un), rp2, rd2, ps2, ds2}

def z1f.s3(pzn: Array<F32> & F32, w: Array<F32>, z1_old: Array<F32>, v1: Array<F32>, u1: Array<F32>, +i: U32, +vw: F32, +vzo: F32, +rp: F32, +rd: F32, +ps: F32, +ds: F32) -> Z1Fin:
  (z1_new, vzn) = pzn
  z1f.s4(Array.get(F32, v1, i), w, z1_old, z1_new, u1, i, vw, vzo, vzn, rp, rd, ps, ds)

def z1f.s2(pzo: Array<F32> & F32, w: Array<F32>, z1_new: Array<F32>, v1: Array<F32>, u1: Array<F32>, +i: U32, +vw: F32, +rp: F32, +rd: F32, +ps: F32, +ds: F32) -> Z1Fin:
  (z1_old, vzo) = pzo
  z1f.s3(Array.get(F32, z1_new, i), w, z1_old, v1, u1, i, vw, vzo, rp, rd, ps, ds)

def z1f.s1(pw: Array<F32> & F32, z1_old: Array<F32>, z1_new: Array<F32>, v1: Array<F32>, u1: Array<F32>, +i: U32, +rp: F32, +rd: F32, +ps: F32, +ds: F32) -> Z1Fin:
  (w, vw) = pw
  z1f.s2(Array.get(F32, z1_old, i), w, z1_new, v1, u1, i, vw, rp, rd, ps, ds)

def z1_fin.go(rem: Nat, st: Z1Fin, +i: U32) -> Z1Fin:
  match rem:
    case 0n:
      st
    case 1n+p:
      Z1Fin{w, z1_old, z1_new, v1, u1, rp, rd, ps, ds} = st
      z1_fin.go(p, z1f.s1(Array.get(F32, w, i), z1_old, z1_new, v1, u1, i, rp, rd, ps, ds), (i + 1 : U32))

# ---------------------------------------------------------------- z2 / u2 update (L1 trade cost)

type Z2St is Type:
  Z2St{
    w: Array<F32>,
    w0: Array<F32>,
    c1m: Array<F32>,
    z2: Array<F32>,
    u2: Array<F32>,
    r_pri: F32,
    r_dual: F32,
    p_scale: F32,
    d_scale: F32
  }

def z2.s5(pu: Array<F32> & F32, w: Array<F32>, w0: Array<F32>, c1m: Array<F32>, z2: Array<F32>, +i: U32, +vw: F32, +vw0: F32, +vc: F32, +vzo: F32, +rp: F32, +rd: F32, +ps: F32, +ds: F32, +gamma: F32) -> Z2St:
  (u2, vu) = pu
  +dw = (vw - vw0 : F32)
  +dw_hat = ((gamma * dw : F32) + ((1.0 - gamma : F32) * vzo : F32) : F32)
  +vv = (dw_hat + vu : F32)
  +vzn = soft(vv, vc)
  +un = (vv - vzn : F32)
  +rp2 = fmax(rp, F32.abs((dw - vzn : F32)))
  +rd2 = fmax(rd, F32.abs((vzn - vzo : F32)))
  +ps2 = fmax(ps, fmax(F32.abs(dw), F32.abs(vzn)))
  +ds2 = fmax(ds, F32.abs(un))
  Z2St{w, w0, c1m, Array.set(F32, z2, i, vzn), Array.set(F32, u2, i, un), rp2, rd2, ps2, ds2}

def z2.s4(pz: Array<F32> & F32, w: Array<F32>, w0: Array<F32>, c1m: Array<F32>, u2: Array<F32>, +i: U32, +vw: F32, +vw0: F32, +vc: F32, +rp: F32, +rd: F32, +ps: F32, +ds: F32, +gamma: F32) -> Z2St:
  (z2, vzo) = pz
  z2.s5(Array.get(F32, u2, i), w, w0, c1m, z2, i, vw, vw0, vc, vzo, rp, rd, ps, ds, gamma)

def z2.s3(pc: Array<F32> & F32, w: Array<F32>, w0: Array<F32>, z2: Array<F32>, u2: Array<F32>, +i: U32, +vw: F32, +vw0: F32, +rp: F32, +rd: F32, +ps: F32, +ds: F32, +gamma: F32) -> Z2St:
  (c1m, vc) = pc
  z2.s4(Array.get(F32, z2, i), w, w0, c1m, u2, i, vw, vw0, vc, rp, rd, ps, ds, gamma)

def z2.s2(pw0: Array<F32> & F32, w: Array<F32>, c1m: Array<F32>, z2: Array<F32>, u2: Array<F32>, +i: U32, +vw: F32, +rp: F32, +rd: F32, +ps: F32, +ds: F32, +gamma: F32) -> Z2St:
  (w0, vw0) = pw0
  z2.s3(Array.get(F32, c1m, i), w, w0, z2, u2, i, vw, vw0, rp, rd, ps, ds, gamma)

def z2.s1(pw: Array<F32> & F32, w0: Array<F32>, c1m: Array<F32>, z2: Array<F32>, u2: Array<F32>, +i: U32, +rp: F32, +rd: F32, +ps: F32, +ds: F32, +gamma: F32) -> Z2St:
  (w, vw) = pw
  z2.s2(Array.get(F32, w0, i), w, c1m, z2, u2, i, vw, rp, rd, ps, ds, gamma)

def z2_upd.go(rem: Nat, st: Z2St, +i: U32, +gamma: F32) -> Z2St:
  match rem:
    case 0n:
      st
    case 1n+p:
      Z2St{w, w0, c1m, z2, u2, rp, rd, ps, ds} = st
      z2_upd.go(p, z2.s1(Array.get(F32, w, i), w0, c1m, z2, u2, i, rp, rd, ps, ds, gamma), (i + 1 : U32), gamma)

# ---------------------------------------------------------------- z3 / u3 update (linear constraints)

type Z3St is Type:
  Z3St{
    a_arr: Array<F32>,
    a_sc: Array<F32>,
    w: Array<F32>,
    lc: Array<F32>,
    uc: Array<F32>,
    z3: Array<F32>,
    u3: Array<F32>,
    dz3: Array<F32>,
    r_pri: F32,
    p_scale: F32
  }

def z3.s5(psc: Array<F32> & F32, a_arr: Array<F32>, w: Array<F32>, lc: Array<F32>, uc: Array<F32>, z3: Array<F32>, u3: Array<F32>, dz3: Array<F32>, +j: U32, +awj: F32, +vl: F32, +vh: F32, +vzo: F32, +vu: F32, +rp: F32, +ps: F32, +gamma: F32) -> Z3St:
  (a_sc, +sc) = psc
  +aw_hat = ((gamma * awj : F32) + ((1.0 - gamma : F32) * vzo : F32) : F32)
  +vv = (aw_hat + vu : F32)
  +vzn = clip(vv, vl, vh)
  +un = (vv - vzn : F32)
  +rp2 = fmax(rp, (sc * F32.abs((awj - vzn : F32)) : F32))
  +ps2 = fmax(ps, (sc * fmax(F32.abs(awj), F32.abs(vzn)) : F32))
  Z3St{a_arr, a_sc, w, lc, uc, Array.set(F32, z3, j, vzn), Array.set(F32, u3, j, un), Array.set(F32, dz3, j, (vzn - vzo : F32)), rp2, ps2}

def z3.s4(pu: Array<F32> & F32, a_arr: Array<F32>, a_sc: Array<F32>, w: Array<F32>, lc: Array<F32>, uc: Array<F32>, z3: Array<F32>, dz3: Array<F32>, +j: U32, +awj: F32, +vl: F32, +vh: F32, +vzo: F32, +rp: F32, +ps: F32, +gamma: F32) -> Z3St:
  (u3, vu) = pu
  z3.s5(Array.get(F32, a_sc, j), a_arr, w, lc, uc, z3, u3, dz3, j, awj, vl, vh, vzo, vu, rp, ps, gamma)

def z3.s3(pz: Array<F32> & F32, a_arr: Array<F32>, a_sc: Array<F32>, w: Array<F32>, lc: Array<F32>, uc: Array<F32>, u3: Array<F32>, dz3: Array<F32>, +j: U32, +awj: F32, +vl: F32, +vh: F32, +rp: F32, +ps: F32, +gamma: F32) -> Z3St:
  (z3, vzo) = pz
  z3.s4(Array.get(F32, u3, j), a_arr, a_sc, w, lc, uc, z3, dz3, j, awj, vl, vh, vzo, rp, ps, gamma)

def z3.s2(puc: Array<F32> & F32, a_arr: Array<F32>, a_sc: Array<F32>, w: Array<F32>, lc: Array<F32>, z3: Array<F32>, u3: Array<F32>, dz3: Array<F32>, +j: U32, +awj: F32, +vl: F32, +rp: F32, +ps: F32, +gamma: F32) -> Z3St:
  (uc, vh) = puc
  z3.s3(Array.get(F32, z3, j), a_arr, a_sc, w, lc, uc, u3, dz3, j, awj, vl, vh, rp, ps, gamma)

def z3.s1(plc: Array<F32> & F32, a_arr: Array<F32>, a_sc: Array<F32>, w: Array<F32>, uc: Array<F32>, z3: Array<F32>, u3: Array<F32>, dz3: Array<F32>, +j: U32, +awj: F32, +rp: F32, +ps: F32, +gamma: F32) -> Z3St:
  (lc, vl) = plc
  z3.s2(Array.get(F32, uc, j), a_arr, a_sc, w, lc, z3, u3, dz3, j, awj, vl, rp, ps, gamma)

def z3_upd.after_dot(ds: DotSt, a_sc: Array<F32>, lc: Array<F32>, uc: Array<F32>, z3: Array<F32>, u3: Array<F32>, dz3: Array<F32>, +rp: F32, +ps: F32, +j: U32, +gamma: F32) -> Z3St:
  DotSt{a2, w2, awj} = ds
  z3.s1(Array.get(F32, lc, j), a2, a_sc, w2, uc, z3, u3, dz3, j, awj, rp, ps, gamma)

def z3_upd.go(rem: Nat, st: Z3St, +j: U32, +n: U32, +gamma: F32) -> Z3St:
  match rem:
    case 0n:
      st
    case 1n+p:
      Z3St{a_arr, a_sc, w, lc, uc, z3, u3, dz3, rp, ps} = st
      z3_upd.go(p, z3_upd.after_dot(dot_row(U32.to_nat(n), DotSt{a_arr, w, 0.0}, (j * n : U32), 0), a_sc, lc, uc, z3, u3, dz3, rp, ps, j, gamma), (j + 1 : U32), n, gamma)

type InfSt is Type:
  InfSt{a: Array<F32>, mx: F32}

def inf_norm.step(p: Array<F32> & F32, +mx: F32) -> InfSt:
  (a, v) = p
  InfSt{a, fmax(mx, F32.abs(v))}

def inf_norm.go(rem: Nat, st: InfSt, +i: U32) -> InfSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      InfSt{a, mx} = st
      inf_norm.go(p, inf_norm.step(Array.get(F32, a, i), mx), (i + 1 : U32))

# ---------------------------------------------------------------- ADMM main loop state & step

type AdmmParams is Data:
  AdmmParams{
    n: U32,
    m: U32,
    r: U32,
    has_l1: Bool,
    gmv_max: F32,
    mu: F32,
    mu_c: F32,
    sig2: F32,
    gamma: F32,
    abs_tol: F32,
    rel_tol: F32
  }

type AdmmState is Type:
  AdmmState{
    d_inv: Array<F32>,
    base_rhs: Array<F32>,
    w0: Array<F32>,
    lw: Array<F32>,
    uw: Array<F32>,
    c1m: Array<F32>,
    lc: Array<F32>,
    uc: Array<F32>,
    a_sc: Array<F32>,
    u_arr: Array<F32>,
    lc_arr: Array<F32>,
    a_arr: Array<F32>,
    w: Array<F32>,
    z1: Array<F32>,
    u1: Array<F32>,
    z2: Array<F32>,
    u2: Array<F32>,
    z3: Array<F32>,
    u3: Array<F32>,
    primal_res: F32,
    dual_res: F32,
    iters: U32,
    converged: Bool
  }

type WbOut is Type:
  WbOut{d_inv: Array<F32>, u_arr: Array<F32>, lc_arr: Array<F32>, w: Array<F32>}

def wb_solve.s4(sq: SubUq, lc2: Array<F32>) -> WbOut:
  SubUq{d2, u3, _, w_out} = sq
  WbOut{d2, u3, lc2, w_out}

def wb_solve.s3(tr: TriInPlace, d_inv: Array<F32>, u2: Array<F32>, y1: Array<F32>, +n: U32, +r: U32) -> WbOut:
  TriInPlace{lc2, q} = tr
  wb_solve.s4(sub_uq.go(U32.to_nat(n), SubUq{d_inv, u2, q, y1}, 0, r), lc2)

def wb_solve.s2(tr: TriInPlace, d_inv: Array<F32>, u2: Array<F32>, y1: Array<F32>, +n: U32, +r: U32) -> WbOut:
  TriInPlace{lc1, t1} = tr
  wb_solve.s3(bwd_solve.go(U32.to_nat(r), TriInPlace{lc1, t1}, (r - 1 : U32), r), d_inv, u2, y1, n, r)

def wb_solve.s1(mt: MatTSt, d_inv: Array<F32>, lc_arr: Array<F32>, +n: U32, +r: U32) -> WbOut:
  MatTSt{u2, y1, t0} = mt
  wb_solve.s2(fwd_solve.go(U32.to_nat(r), TriInPlace{lc_arr, t0}, 0, r), d_inv, u2, y1, n, r)

def wb_solve.pick(has_r: Bool, d_inv: Array<F32>, u_arr: Array<F32>, lc_arr: Array<F32>, y0: Array<F32>, +n: U32, +r: U32) -> WbOut:
  match has_r:
    case True{}:
      wb_solve.s1(mat_t_mul.go(U32.to_nat(n), MatTSt{u_arr, y0, Array.new(F32, arr_depth(r), 0.0)}, 0, r), d_inv, lc_arr, n, r)
    case False{}:
      WbOut{d_inv, u_arr, lc_arr, y0}

def maybe_add_at(has_m: Bool, a_arr: Array<F32>, z3: Array<F32>, u3: Array<F32>, y: Array<F32>, +m: U32, +n: U32, +mu: F32) -> AddAT2:
  match has_m:
    case True{}:
      add_at_diff.go(U32.to_nat(m), AddAT2{a_arr, z3, u3, y}, 0, n, mu)
    case False{}:
      AddAT2{a_arr, z3, u3, y}

def maybe_z2(has_l1: Bool, w: Array<F32>, w0: Array<F32>, c1m: Array<F32>, z2: Array<F32>, u2: Array<F32>, +rp: F32, +rd: F32, +ps: F32, +ds: F32, +n: U32, +gamma: F32) -> Z2St:
  match has_l1:
    case True{}:
      z2_upd.go(U32.to_nat(n), Z2St{w, w0, c1m, z2, u2, rp, rd, ps, ds}, 0, gamma)
    case False{}:
      Z2St{w, w0, c1m, z2, u2, rp, rd, ps, ds}

type Z3Res is Type:
  Z3Res{
    a_arr: Array<F32>,
    a_sc: Array<F32>,
    w: Array<F32>,
    lc: Array<F32>,
    uc: Array<F32>,
    z3: Array<F32>,
    u3: Array<F32>,
    r_pri: F32,
    r_dual: F32,
    p_scale: F32,
    d_scale: F32
  }

def mz3.s5(inf2: InfSt, a3: Array<F32>, a_sc: Array<F32>, w1: Array<F32>, lc1: Array<F32>, uc1: Array<F32>, z3n: Array<F32>, u3f: Array<F32>, +rp1: F32, +rd2: F32, +ps1: F32, +ds: F32, +mu_c: F32) -> Z3Res:
  InfSt{_, ds3} = inf2
  Z3Res{a3, a_sc, w1, lc1, uc1, z3n, u3f, rp1, rd2, ps1, fmax(ds, (mu_c * ds3 : F32))}

def mz3.s4(mt2: MatTSt, a_sc: Array<F32>, w1: Array<F32>, lc1: Array<F32>, uc1: Array<F32>, z3n: Array<F32>, +rp1: F32, +rd2: F32, +ps1: F32, +ds: F32, +n: U32, +mu_c: F32) -> Z3Res:
  MatTSt{a3, u3f, atu3} = mt2
  mz3.s5(inf_norm.go(U32.to_nat(n), InfSt{atu3, 0.0}, 0), a3, a_sc, w1, lc1, uc1, z3n, u3f, rp1, rd2, ps1, ds, mu_c)

def mz3.s3(inf1: InfSt, a2: Array<F32>, a_sc: Array<F32>, w1: Array<F32>, lc1: Array<F32>, uc1: Array<F32>, z3n: Array<F32>, u3n: Array<F32>, +rp1: F32, +rd: F32, +ps1: F32, +ds: F32, +m: U32, +n: U32, +mu_c: F32) -> Z3Res:
  InfSt{_, rd3} = inf1
  mz3.s4(mat_t_mul.go(U32.to_nat(m), MatTSt{a2, u3n, Array.new(F32, arr_depth(n), 0.0)}, 0, n), a_sc, w1, lc1, uc1, z3n, rp1, fmax(rd, (mu_c * rd3 : F32)), ps1, ds, n, mu_c)

def mz3.s2(mt1: MatTSt, a_sc: Array<F32>, w1: Array<F32>, lc1: Array<F32>, uc1: Array<F32>, z3n: Array<F32>, u3n: Array<F32>, +rp1: F32, +rd: F32, +ps1: F32, +ds: F32, +m: U32, +n: U32, +mu_c: F32) -> Z3Res:
  MatTSt{a2, _, atdz} = mt1
  mz3.s3(inf_norm.go(U32.to_nat(n), InfSt{atdz, 0.0}, 0), a2, a_sc, w1, lc1, uc1, z3n, u3n, rp1, rd, ps1, ds, m, n, mu_c)

def mz3.s1(zs: Z3St, +rd: F32, +ds: F32, +m: U32, +n: U32, +mu_c: F32) -> Z3Res:
  Z3St{a1, a_sc, w1, lc1, uc1, z3n, u3n, dz3, rp1, ps1} = zs
  mz3.s2(mat_t_mul.go(U32.to_nat(m), MatTSt{a1, dz3, Array.new(F32, arr_depth(n), 0.0)}, 0, n), a_sc, w1, lc1, uc1, z3n, u3n, rp1, rd, ps1, ds, m, n, mu_c)

def maybe_z3(has_m: Bool, a_arr: Array<F32>, a_sc: Array<F32>, w: Array<F32>, lc: Array<F32>, uc: Array<F32>, z3: Array<F32>, u3: Array<F32>, +rp: F32, +rd: F32, +ps: F32, +ds: F32, +m: U32, +n: U32, +gamma: F32, +mu_c: F32) -> Z3Res:
  match has_m:
    case True{}:
      mz3.s1(z3_upd.go(U32.to_nat(m), Z3St{a_arr, a_sc, w, lc, uc, z3, u3, Array.new(F32, arr_depth(m), 0.0), rp, ps}, 0, n, gamma), rd, ds, m, n, mu_c)
    case False{}:
      Z3Res{a_arr, a_sc, w, lc, uc, z3, u3, rp, rd, ps, ds}

# Chained ADMM step helpers (no computed-expression destructures)
def step.s9(zr: Z3Res, d2: Array<F32>, base1: Array<F32>, w02: Array<F32>, lw2: Array<F32>, uw2: Array<F32>, c1m2: Array<F32>, u_arr2: Array<F32>, lc_arr2: Array<F32>, z1_out: Array<F32>, u1_out: Array<F32>, z2_out: Array<F32>, u2_out: Array<F32>, +iters: U32, +abs_tol: F32, +rel_tol: F32) -> AdmmState:
  Z3Res{a2, a_sc2, w4, lc2, uc2, z3_out, u3_out, +rp3, +rd3, +ps3, +ds3} = zr
  +r_pri = rp3
  +r_dual = rd3
  +eps_pri = (abs_tol + (rel_tol * ps3 : F32) : F32)
  +eps_dual = (abs_tol + (rel_tol * ds3 : F32) : F32)
  +conv = Bool.and(F32.is_le(r_pri, eps_pri), F32.is_le(r_dual, eps_dual))
  AdmmState{d2, base1, w02, lw2, uw2, c1m2, lc2, uc2, a_sc2, u_arr2, lc_arr2, a2, w4, z1_out, u1_out, z2_out, u2_out, z3_out, u3_out, r_pri, r_dual, (iters + 1 : U32), conv}

def step.s8(z2s: Z2St, d2: Array<F32>, base1: Array<F32>, lw2: Array<F32>, uw2: Array<F32>, lc: Array<F32>, uc: Array<F32>, a_sc: Array<F32>, u_arr2: Array<F32>, lc_arr2: Array<F32>, a1: Array<F32>, z1_out: Array<F32>, u1_out: Array<F32>, z31: Array<F32>, u31: Array<F32>, +iters: U32, +pr: AdmmParams) -> AdmmState:
  Z2St{w3, w02, c1m2, z2_out, u2_out, rp2, rd2, ps2, ds2} = z2s
  AdmmParams{+n, +m, _, _, _, +mu, +mu_c, _, +gamma, +abs_tol, +rel_tol} = pr
  step.s9(maybe_z3(U32.is_lt(0, m), a1, a_sc, w3, lc, uc, z31, u31, rp2, (mu * rd2 : F32), ps2, (mu * ds2 : F32), m, n, gamma, mu_c), d2, base1, w02, lw2, uw2, c1m2, u_arr2, lc_arr2, z1_out, u1_out, z2_out, u2_out, iters, abs_tol, rel_tol)

def step.s7(zf: Z1Fin, d2: Array<F32>, base1: Array<F32>, w01: Array<F32>, lw2: Array<F32>, uw2: Array<F32>, c1m: Array<F32>, lc: Array<F32>, uc: Array<F32>, a_sc: Array<F32>, u_arr2: Array<F32>, lc_arr2: Array<F32>, a1: Array<F32>, z21: Array<F32>, u21: Array<F32>, z31: Array<F32>, u31: Array<F32>, +iters: U32, +pr: AdmmParams) -> AdmmState:
  Z1Fin{w2, _, z1_out, _, u1_out, rp1, rd1, ps1, ds1} = zf
  AdmmParams{+n, _, _, +has_l1, _, _, _, _, +gamma, _, _} = pr
  step.s8(maybe_z2(has_l1, w2, w01, c1m, z21, u21, rp1, rd1, ps1, ds1, n, gamma), d2, base1, lw2, uw2, lc, uc, a_sc, u_arr2, lc_arr2, a1, z1_out, u1_out, z31, u31, iters, pr)

def step.s6(wz: WriteZ1, w1: Array<F32>, z12: Array<F32>, u12: Array<F32>, d2: Array<F32>, base1: Array<F32>, w01: Array<F32>, c1m: Array<F32>, lc: Array<F32>, uc: Array<F32>, a_sc: Array<F32>, u_arr2: Array<F32>, lc_arr2: Array<F32>, a1: Array<F32>, z21: Array<F32>, u21: Array<F32>, z31: Array<F32>, u31: Array<F32>, +iters: U32, +pr: AdmmParams) -> AdmmState:
  WriteZ1{v11, lw2, uw2, z1n1} = wz
  AdmmParams{+n, _, _, _, _, _, _, _, _, _, _} = pr
  step.s7(z1_fin.go(U32.to_nat(n), Z1Fin{w1, z12, z1n1, v11, u12, 0.0, 0.0, 0.0, 0.0}, 0), d2, base1, w01, lw2, uw2, c1m, lc, uc, a_sc, u_arr2, lc_arr2, a1, z21, u21, z31, u31, iters, pr)

def step.s5(zp: Z1Prep, d2: Array<F32>, base1: Array<F32>, w01: Array<F32>, c1m: Array<F32>, lc: Array<F32>, uc: Array<F32>, a_sc: Array<F32>, u_arr2: Array<F32>, lc_arr2: Array<F32>, a1: Array<F32>, z21: Array<F32>, u21: Array<F32>, z31: Array<F32>, u31: Array<F32>, +iters: U32, +pr: AdmmParams) -> AdmmState:
  Z1Prep{w1, z12, u12, lw1, uw1, v10, z1n0, l1s, vmax} = zp
  AdmmParams{+n, _, _, _, +gmv, _, _, _, _, _, _} = pr
  +need_gmv = Bool.and(F32.is_gt(gmv, 0.0), F32.is_gt(l1s, gmv))
  step.s6(maybe_bisect(need_gmv, v10, lw1, uw1, z1n0, vmax, n, gmv), w1, z12, u12, d2, base1, w01, c1m, lc, uc, a_sc, u_arr2, lc_arr2, a1, z21, u21, z31, u31, iters, pr)

def step.s4(wb: WbOut, base1: Array<F32>, w01: Array<F32>, lw: Array<F32>, uw: Array<F32>, c1m: Array<F32>, lc: Array<F32>, uc: Array<F32>, a_sc: Array<F32>, a1: Array<F32>, z11: Array<F32>, u11: Array<F32>, z21: Array<F32>, u21: Array<F32>, z31: Array<F32>, u31: Array<F32>, +iters: U32, +pr: AdmmParams) -> AdmmState:
  WbOut{d2, u_arr2, lc_arr2, w_new} = wb
  AdmmParams{+n, _, _, _, _, _, _, _, +gamma, _, _} = pr
  +dn = arr_depth(n)
  step.s5(z1_prep.go(U32.to_nat(n), Z1Prep{w_new, z11, u11, lw, uw, Array.new(F32, dn, 0.0), Array.new(F32, dn, 0.0), 0.0, 0.0}, 0, gamma), d2, base1, w01, c1m, lc, uc, a_sc, u_arr2, lc_arr2, a1, z21, u21, z31, u31, iters, pr)

def step.s3(md: MulDinv, base1: Array<F32>, w01: Array<F32>, lw: Array<F32>, uw: Array<F32>, c1m: Array<F32>, lc: Array<F32>, uc: Array<F32>, a_sc: Array<F32>, u_arr: Array<F32>, lc_arr: Array<F32>, a1: Array<F32>, z11: Array<F32>, u11: Array<F32>, z21: Array<F32>, u21: Array<F32>, z31: Array<F32>, u31: Array<F32>, +iters: U32, +pr: AdmmParams) -> AdmmState:
  MulDinv{d1, y0} = md
  AdmmParams{+n, _, +r, _, _, _, _, _, _, _, _} = pr
  step.s4(wb_solve.pick(U32.is_lt(0, r), d1, u_arr, lc_arr, y0, n, r), base1, w01, lw, uw, c1m, lc, uc, a_sc, a1, z11, u11, z21, u21, z31, u31, iters, pr)

def step.s2(at: AddAT2, d_inv: Array<F32>, base1: Array<F32>, w01: Array<F32>, lw: Array<F32>, uw: Array<F32>, c1m: Array<F32>, lc: Array<F32>, uc: Array<F32>, a_sc: Array<F32>, u_arr: Array<F32>, lc_arr: Array<F32>, z11: Array<F32>, u11: Array<F32>, z21: Array<F32>, u21: Array<F32>, +iters: U32, +pr: AdmmParams) -> AdmmState:
  AddAT2{a1, z31, u31, rhs1} = at
  AdmmParams{+n, _, _, _, _, _, _, _, _, _, _} = pr
  step.s3(mul_dinv.go(U32.to_nat(n), MulDinv{d_inv, rhs1}, 0), base1, w01, lw, uw, c1m, lc, uc, a_sc, u_arr, lc_arr, a1, z11, u11, z21, u21, z31, u31, iters, pr)

def step.s1(rp: RhsPack, d_inv: Array<F32>, lw: Array<F32>, uw: Array<F32>, c1m: Array<F32>, lc: Array<F32>, uc: Array<F32>, a_sc: Array<F32>, u_arr: Array<F32>, lc_arr: Array<F32>, a_arr: Array<F32>, z3: Array<F32>, u3: Array<F32>, +iters: U32, +pr: AdmmParams) -> AdmmState:
  RhsPack{base1, w01, z11, u11, z21, u21, rhs0} = rp
  AdmmParams{+n, +m, _, _, _, _, +mu_c, _, _, _, _} = pr
  step.s2(maybe_add_at(U32.is_lt(0, m), a_arr, z3, u3, rhs0, m, n, mu_c), d_inv, base1, w01, lw, uw, c1m, lc, uc, a_sc, u_arr, lc_arr, z11, u11, z21, u21, iters, pr)

def admm_step(st: AdmmState, +pr: AdmmParams) -> AdmmState:
  AdmmState{d_inv, base_rhs, w0, lw, uw, c1m, lc, uc, a_sc, u_arr, lc_arr, a_arr, _, z1, u1, z2, u2, z3, u3, _, _, iters, _} = st
  AdmmParams{+n, _, _, _, _, +mu, _, +sig2, _, _, _} = pr
  step.s1(build_rhs.go(U32.to_nat(n), RhsPack{base_rhs, w0, z1, u1, z2, u2, Array.new(F32, arr_depth(n), 0.0)}, 0, mu, sig2), d_inv, lw, uw, c1m, lc, uc, a_sc, u_arr, lc_arr, a_arr, z3, u3, iters, pr)

def admm_loop(rem: Nat, st: AdmmState, +pr: AdmmParams) -> AdmmState:
  match rem:
    case 0n:
      st
    case 1n+p:
      match st:
        case AdmmState{d_inv, base_rhs, w0, lw, uw, c1m, lc, uc, a_sc, u_arr, lc_arr, a_arr, w, z1, u1, z2, u2, z3, u3, rp, rd, it, True{}}:
          AdmmState{d_inv, base_rhs, w0, lw, uw, c1m, lc, uc, a_sc, u_arr, lc_arr, a_arr, w, z1, u1, z2, u2, z3, u3, rp, rd, it, True{}}
        case AdmmState{d_inv, base_rhs, w0, lw, uw, c1m, lc, uc, a_sc, u_arr, lc_arr, a_arr, w, z1, u1, z2, u2, z3, u3, rp, rd, it, False{}}:
          admm_loop(p, admm_step(AdmmState{d_inv, base_rhs, w0, lw, uw, c1m, lc, uc, a_sc, u_arr, lc_arr, a_arr, w, z1, u1, z2, u2, z3, u3, rp, rd, it, False{}}, pr), pr)

# ---------------------------------------------------------------- setup & entry point

type SolveOut is Data:
  SolveOut{weights: L.Vec, iters: U32, primal_res: F32, dual_res: F32, converged: Bool}

def extract_out(st: AdmmState, +n: U32) -> SolveOut:
  AdmmState{_, _, _, _, _, _, _, _, _, _, _, _, _, z1, _, _, _, _, _, rp, rd, it, conv} = st
  SolveOut{L.Vec{n, arr_to_list(z1, n)}, it, rp, rd, conv}

def run_with_factors(
  +n: U32,
  +m: U32,
  +r: U32,
  +has_l1: Bool,
  +gmv: F32,
  +mu: F32,
  +mu_c: F32,
  +sig2: F32,
  +gamma: F32,
  +max_iters: U32,
  +abs_tol: F32,
  +rel_tol: F32,
  dinv_s: List<&2, F32>,
  base_s: List<&2, F32>,
  w0_s: List<&2, F32>,
  lw_s: List<&2, F32>,
  uw_s: List<&2, F32>,
  c1m_s: List<&2, F32>,
  lc_s: List<&2, F32>,
  uc_s: List<&2, F32>,
  sc_s: List<&2, F32>,
  u_rows: List<&2, List<&2, F32>>,
  lc_rows: List<&2, List<&2, F32>>,
  a_rows: List<&2, List<&2, F32>>
) -> SolveOut:
  +dn = arr_depth(n)
  +dm = arr_depth(m)
  +pr = {AdmmParams{n, m, r, has_l1, gmv, mu, mu_c, sig2, gamma, abs_tol, rel_tol} : AdmmParams}
  st0 = {AdmmState{
    vec_to_arr(dinv_s, n),
    vec_to_arr(base_s, n),
    vec_to_arr(w0_s, n),
    vec_to_arr(lw_s, n),
    vec_to_arr(uw_s, n),
    vec_to_arr(c1m_s, n),
    vec_to_arr(lc_s, m),
    vec_to_arr(uc_s, m),
    vec_to_arr(sc_s, m),
    mat_to_arr(u_rows, n, r),
    mat_to_arr(lc_rows, r, r),
    mat_to_arr(a_rows, m, n),
    Array.new(F32, dn, 0.0),
    Array.new(F32, dn, 0.0),
    Array.new(F32, dn, 0.0),
    Array.new(F32, dn, 0.0),
    Array.new(F32, dn, 0.0),
    Array.new(F32, dm, 0.0),
    Array.new(F32, dm, 0.0),
    0.0,
    0.0,
    0,
    False{}
  } : AdmmState}
  extract_out(admm_loop(U32.to_nat(max_iters), st0, pr), n)

def solve.with_lc(
  mlc: Maybe<&2, L.Mat>,
  u_mat: L.Mat,
  a_norm: L.Mat,
  +n: U32,
  +m: U32,
  +has_l1: Bool,
  +gmv: F32,
  +mu: F32,
  +mu_c: F32,
  +sig2: F32,
  +gamma: F32,
  +max_iters: U32,
  +abs_tol: F32,
  +rel_tol: F32,
  dinv_s: List<&2, F32>,
  base_s: List<&2, F32>,
  w0_s: List<&2, F32>,
  lw_s: List<&2, F32>,
  uw_s: List<&2, F32>,
  c1m_s: List<&2, F32>,
  lc_s: List<&2, F32>,
  uc_s: List<&2, F32>,
  sc_s: List<&2, F32>
) -> Maybe<&2, SolveOut>:
  match mlc:
    case Some{L.Mat{_, _, lc_rows}}:
      L.Mat{_, +r, u_rows} = u_mat
      L.Mat{_, _, a_rows} = a_norm
      Some{run_with_factors(n, m, r, has_l1, gmv, mu, mu_c, sig2, gamma, max_iters, abs_tol, rel_tol, dinv_s, base_s, w0_s, lw_s, uw_s, c1m_s, lc_s, uc_s, sc_s, u_rows, lc_rows, a_rows)}
    case None{}:
      None{}

def solve.with_c(
  mc: Maybe<&2, L.Mat>,
  u_mat: L.Mat,
  a_norm: L.Mat,
  +n: U32,
  +m: U32,
  +has_l1: Bool,
  +gmv: F32,
  +mu: F32,
  +mu_c: F32,
  +sig2: F32,
  +gamma: F32,
  +max_iters: U32,
  +abs_tol: F32,
  +rel_tol: F32,
  dinv_s: List<&2, F32>,
  base_s: List<&2, F32>,
  w0_s: List<&2, F32>,
  lw_s: List<&2, F32>,
  uw_s: List<&2, F32>,
  c1m_s: List<&2, F32>,
  lc_s: List<&2, F32>,
  uc_s: List<&2, F32>,
  sc_s: List<&2, F32>
) -> Maybe<&2, SolveOut>:
  match mc:
    case Some{c_mat}:
      solve.with_lc(L.cholesky(c_mat), u_mat, a_norm, n, m, has_l1, gmv, mu, mu_c, sig2, gamma, max_iters, abs_tol, rel_tol, dinv_s, base_s, w0_s, lw_s, uw_s, c1m_s, lc_s, uc_s, sc_s)
    case None{}:
      None{}

def solve.with_gu(
  mgu: Maybe<&2, L.Mat>,
  +u_mat: L.Mat,
  a_norm: L.Mat,
  +n: U32,
  +m: U32,
  +has_l1: Bool,
  +gmv: F32,
  +mu: F32,
  +mu_c: F32,
  +sig2: F32,
  +gamma: F32,
  +max_iters: U32,
  +abs_tol: F32,
  +rel_tol: F32,
  dinv_s: List<&2, F32>,
  base_s: List<&2, F32>,
  w0_s: List<&2, F32>,
  lw_s: List<&2, F32>,
  uw_s: List<&2, F32>,
  c1m_s: List<&2, F32>,
  lc_s: List<&2, F32>,
  uc_s: List<&2, F32>,
  sc_s: List<&2, F32>
) -> Maybe<&2, SolveOut>:
  match mgu:
    case Some{gu}:
      L.Mat{_, +r, _} = u_mat
      solve.with_c(L.madd(L.Mat.eye(r), gu), u_mat, a_norm, n, m, has_l1, gmv, mu, mu_c, sig2, gamma, max_iters, abs_tol, rel_tol, dinv_s, base_s, w0_s, lw_s, uw_s, c1m_s, lc_s, uc_s, sc_s)
    case None{}:
      None{}

def solve.factor_u(
  has_r: Bool,
  +u_mat: L.Mat,
  a_norm: L.Mat,
  +n: U32,
  +m: U32,
  +has_l1: Bool,
  +gmv: F32,
  +mu: F32,
  +mu_c: F32,
  +sig2: F32,
  +gamma: F32,
  +max_iters: U32,
  +abs_tol: F32,
  +rel_tol: F32,
  +dinv_s: List<&2, F32>,
  base_s: List<&2, F32>,
  w0_s: List<&2, F32>,
  lw_s: List<&2, F32>,
  uw_s: List<&2, F32>,
  c1m_s: List<&2, F32>,
  lc_s: List<&2, F32>,
  uc_s: List<&2, F32>,
  sc_s: List<&2, F32>
) -> Maybe<&2, SolveOut>:
  match has_r:
    case True{}:
      solve.with_gu(L.wgram(u_mat, L.Vec{n, dinv_s}), u_mat, a_norm, n, m, has_l1, gmv, mu, mu_c, sig2, gamma, max_iters, abs_tol, rel_tol, dinv_s, base_s, w0_s, lw_s, uw_s, c1m_s, lc_s, uc_s, sc_s)
    case False{}:
      L.Mat{_, _, a_rows} = a_norm
      Some{run_with_factors(n, m, 0, has_l1, gmv, mu, mu_c, sig2, gamma, max_iters, abs_tol, rel_tol, dinv_s, base_s, w0_s, lw_s, uw_s, c1m_s, lc_s, uc_s, sc_s, Nil{}, Nil{}, a_rows)}

def solve.with_u(
  +u_mat: L.Mat,
  a_norm: L.Mat,
  +n: U32,
  +m: U32,
  +has_l1: Bool,
  +gmv: F32,
  +mu: F32,
  +mu_c: F32,
  +sig2: F32,
  +gamma: F32,
  +max_iters: U32,
  +abs_tol: F32,
  +rel_tol: F32,
  dinv_s: List<&2, F32>,
  base_s: List<&2, F32>,
  w0_s: List<&2, F32>,
  lw_s: List<&2, F32>,
  uw_s: List<&2, F32>,
  c1m_s: List<&2, F32>,
  lc_s: List<&2, F32>,
  uc_s: List<&2, F32>,
  sc_s: List<&2, F32>
) -> Maybe<&2, SolveOut>:
  L.Mat{_, +r, _} = u_mat
  solve.factor_u(U32.is_lt(0, r), u_mat, a_norm, n, m, has_l1, gmv, mu, mu_c, sig2, gamma, max_iters, abs_tol, rel_tol, dinv_s, base_s, w0_s, lw_s, uw_s, c1m_s, lc_s, uc_s, sc_s)

def build_u_combine(has_m: Bool, u_f: L.Mat, a_norm: L.Mat, +mu_c: F32) -> L.Mat:
  match has_m:
    case True{}:
      u_a = L.scale(F32.sqrt(mu_c), L.transpose(a_norm))
      hcat_mat(u_f, u_a)
    case False{}:
      u_f

def solve.with_uf(
  muf: Maybe<&2, L.Mat>,
  +a_norm: L.Mat,
  +n: U32,
  +m: U32,
  +has_l1: Bool,
  +gmv: F32,
  +mu: F32,
  +mu_c: F32,
  +sig2: F32,
  +gamma: F32,
  +max_iters: U32,
  +abs_tol: F32,
  +rel_tol: F32,
  dinv_s: List<&2, F32>,
  base_s: List<&2, F32>,
  w0_s: List<&2, F32>,
  lw_s: List<&2, F32>,
  uw_s: List<&2, F32>,
  c1m_s: List<&2, F32>,
  lc_s: List<&2, F32>,
  uc_s: List<&2, F32>,
  sc_s: List<&2, F32>
) -> Maybe<&2, SolveOut>:
  match muf:
    case Some{uf}:
      solve.with_u(build_u_combine(U32.is_lt(0, m), uf, a_norm, mu_c), a_norm, n, m, has_l1, gmv, mu, mu_c, sig2, gamma, max_iters, abs_tol, rel_tol, dinv_s, base_s, w0_s, lw_s, uw_s, c1m_s, lc_s, uc_s, sc_s)
    case None{}:
      None{}

def solve.with_blf(mblf: Maybe<&2, L.Mat>, +rho: F32) -> Maybe<&2, L.Mat>:
  match mblf:
    case Some{blf}:
      Some{L.scale(F32.sqrt(rho), blf)}
    case None{}:
      None{}

def solve.with_lf(mlf: Maybe<&2, L.Mat>, b: L.Mat, +rho: F32) -> Maybe<&2, L.Mat>:
  match mlf:
    case Some{lf}:
      solve.with_blf(L.matmul(b, lf), rho)
    case None{}:
      None{}

def build_uf(has_k: Bool, b: L.Mat, cov_f: L.Mat, +n: U32, +rho: F32) -> Maybe<&2, L.Mat>:
  match has_k:
    case True{}:
      solve.with_lf(L.cholesky(cov_f), b, rho)
    case False{}:
      Some{L.Mat{n, 0, List.replicate(List<&2, F32>, U32.to_nat(n), Nil{})}}

def trace_or(mt: Maybe<&2, F32>) -> F32:
  match mt:
    case Some{t}:
      fmax(0.0, t)
    case None{}:
      0.0

def u32_to_f32.go(rem: Nat, acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      u32_to_f32.go(p, (acc + 1.0 : F32))

def lam_fac_est.pick(has_k: Bool, b: L.Mat, cov_f: L.Mat, +k: U32, +rho: F32) -> F32:
  match has_k:
    case True{}:
      +kf = u32_to_f32.go(U32.to_nat(k), 0.0)
      +fb = L.frobenius(b)
      +tr = trace_or(L.trace(cov_f))
      (((rho * tr : F32) * (fb * fb : F32) : F32) / (kf * kf : F32) : F32)
    case False{}:
      0.0

def lam_fac_est(b: L.Mat, cov_f: L.Mat, +k: U32, +rho: F32) -> F32:
  lam_fac_est.pick(U32.is_lt(0, k), b, cov_f, k, rho)

def solve.with_equil(
  eq: Equil,
  b: L.Mat,
  cov_f: L.Mat,
  +n: U32,
  +k: U32,
  +m: U32,
  +has_l1: Bool,
  +gmv: F32,
  +rho: F32,
  +mu: F32,
  +mu_c: F32,
  +sig2: F32,
  +gamma: F32,
  +max_iters: U32,
  +abs_tol: F32,
  +rel_tol: F32,
  dinv_s: List<&2, F32>,
  base_s: List<&2, F32>,
  w0_s: List<&2, F32>,
  lw_s: List<&2, F32>,
  uw_s: List<&2, F32>,
  c1m_s: List<&2, F32>
) -> Maybe<&2, SolveOut>:
  Equil{a_norm, L.Vec{_, lc_s}, L.Vec{_, uc_s}, L.Vec{_, sc_s}} = eq
  solve.with_uf(build_uf(U32.is_lt(0, k), b, cov_f, n, rho), a_norm, n, m, has_l1, gmv, mu, mu_c, sig2, gamma, max_iters, abs_tol, rel_tol, dinv_s, base_s, w0_s, lw_s, uw_s, c1m_s, lc_s, uc_s, sc_s)

def solve.run(
  +b: L.Mat,
  +cov_f: L.Mat,
  +d_s: List<&2, F32>,
  a_s: List<&2, F32>,
  +w0_s: List<&2, F32>,
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
  +max_iters: U32,
  +abs_tol: F32,
  +rel_tol: F32,
  +rho_admm: F32,
  +relax: F32
) -> Maybe<&2, SolveOut>:
  +mean_d = list_mean.go(list_diag_scale(d_s, c2_s, rho), 0.0, 0.0)
  +lfac = lam_fac_est(b, cov_f, k, rho)
  +mu_auto = clip(F32.sqrt((mean_d * (mean_d + lfac : F32) : F32)), 1.0e-4, 1.0e4)
  +muc_auto = clip(fmax(mu_auto, (mean_d + lfac : F32)), 1.0e-4, 1.0e4)
  +mu = Bool.pick(F32, F32.is_gt(rho_admm, 0.0), rho_admm, mu_auto)
  +mu_c = Bool.pick(F32, F32.is_gt(rho_admm, 0.0), rho_admm, muc_auto)
  +has_l1 = any_pos(c1_s)
  +sig2 = Bool.pick(F32, has_l1, mu, 0.0)
  +gamma = clip(relax, 1.0, 1.9)
  +dinv_s = list_dinv(d_s, c2_s, rho, (mu + sig2 : F32))
  +base_s = list_base_rhs(a_s, c2_s, w0_s)
  +c1m_s = scale_list(c1_s, (1.0 / mu : F32))
  solve.with_equil(equilibrate(a_mat, lc_v, uc_v), b, cov_f, n, k, m, has_l1, gmv, rho, mu, mu_c, sig2, gamma, max_iters, abs_tol, rel_tol, dinv_s, base_s, w0_s, lw_s, uw_s, c1m_s)

def solve.gmv_ok(ok: Bool, b: L.Mat, cov_f: L.Mat, d_s: List<&2, F32>, a_s: List<&2, F32>, w0_s: List<&2, F32>, lw_s: List<&2, F32>, uw_s: List<&2, F32>, a_mat: L.Mat, lc_v: L.Vec, uc_v: L.Vec, c1_s: List<&2, F32>, c2_s: List<&2, F32>, +n: U32, +k: U32, +m: U32, +gmv: F32, +rho: F32, +max_iters: U32, +abs_tol: F32, +rel_tol: F32, +rho_admm: F32, +relax: F32) -> Maybe<&2, SolveOut>:
  match ok:
    case True{}:
      solve.run(b, cov_f, d_s, a_s, w0_s, lw_s, uw_s, a_mat, lc_v, uc_v, c1_s, c2_s, n, k, m, gmv, rho, max_iters, abs_tol, rel_tol, rho_admm, relax)
    case False{}:
      None{}

def solve_checked(
  b: L.Mat,
  cov_f: L.Mat,
  d_s: List<&2, F32>,
  a_s: List<&2, F32>,
  w0_s: List<&2, F32>,
  +lw_s: List<&2, F32>,
  +uw_s: List<&2, F32>,
  a_mat: L.Mat,
  +lc_v: L.Vec,
  +uc_v: L.Vec,
  c1_s: List<&2, F32>,
  c2_s: List<&2, F32>,
  +n: U32,
  +k: U32,
  +m: U32,
  +gmv: F32,
  +rho: F32,
  +max_iters: U32,
  +abs_tol: F32,
  +rel_tol: F32,
  +rho_admm: F32,
  +relax: F32
) -> Maybe<&2, SolveOut>:
  L.Vec{_, lc_raw} = lc_v
  L.Vec{_, uc_raw} = uc_v
  +bok = Bool.and(bounds_ok(lw_s, uw_s), bounds_ok(lc_raw, uc_raw))
  +gmv_ok = Bool.or(F32.is_le(gmv, 0.0), F32.is_le(min_box_l1.go(lw_s, uw_s, 0.0), gmv))
  solve.gmv_ok(Bool.and(bok, gmv_ok), b, cov_f, d_s, a_s, w0_s, lw_s, uw_s, a_mat, lc_v, uc_v, c1_s, c2_s, n, k, m, gmv, rho, max_iters, abs_tol, rel_tol, rho_admm, relax)
