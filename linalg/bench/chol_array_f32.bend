import Base

# Cholesky (K x K) and Cyclic Jacobi symmetric eigen (K x K) on flat Array<F32>.
# K <= 64 (4096-slot Array<F32>).
# Usage: out/chol_array_f32 [K] [chol_reps] [jacobi_sweeps]   (default 50 50 6)

def lcg(+s: U32) -> U32:
  ((s * 1664525) + 1013904223 : U32)

def sym_val(+i: U32, +j: U32) -> F32:
  +lo = U32.min(i, j)
  +hi = U32.max(i, j)
  +h = lcg((((hi * 73856093) .^. (lo * 19349663)) + 12345 : U32))
  +u = ((U32.to_f32((h >> 8n : U32)) / 16777216.0) - 0.5 : F32)
  Bool.pick(F32, U32.is_eq(i, j), (10.0 + (U32.to_f32(i) * 0.5) : F32), (u * 0.2 : F32))

def fill_row(rem: Nat, a: Array<F32>, +i: U32, +j: U32, +k: U32) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+p:
      fill_row(p, Array.set(F32, a, ((i * k) + j : U32), sym_val(i, j)), i, (j + 1 : U32), k)

def fill_spd(rem: Nat, a: Array<F32>, +i: U32, +k: U32) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+p:
      fill_spd(p, fill_row(U32.to_nat(k), a, i, 0, k), (i + 1 : U32), k)

# ---- Cholesky L L^T = A (writing lower triangle into l)
type CSt is Type:
  CSt{a: Array<F32>, l: Array<F32>}

def dot_l2(p: Array<F32> & F32, +v1: F32, +acc: F32) -> Array<F32> & F32:
  (l, v2) = p
  (l, (acc + (v1 * v2) : F32))

def dot_l1(p: Array<F32> & F32, +o2: U32, +acc: F32) -> Array<F32> & F32:
  (l, v1) = p
  dot_l2(Array.get(F32, l, o2), v1, acc)

def dot_l(rem: Nat, st: Array<F32> & F32, +o1: U32, +o2: U32) -> Array<F32> & F32:
  match rem:
    case 0n:
      st
    case 1n+p:
      (l, acc) = st
      dot_l(p, dot_l1(Array.get(F32, l, o1), o2, acc), (o1 + 1 : U32), (o2 + 1 : U32))

def chol_set_off(p: Array<F32> & F32, a: Array<F32>, +aij: F32, +s: F32, +idx: U32) -> CSt:
  (l, ljj) = p
  CSt{a, Array.set(F32, l, idx, ((aij - s) / ljj : F32))}

def chol_cell_branch(diag: Bool, a: Array<F32>, l: Array<F32>, +aij: F32, +s: F32, +i: U32, +j: U32, +k: U32) -> CSt:
  match diag:
    case True{}:
      CSt{a, Array.set(F32, l, ((i * k) + j : U32), F32.sqrt((aij - s : F32)))}
    case False{}:
      chol_set_off(Array.get(F32, l, ((j * k) + j : U32)), a, aij, s, ((i * k) + j : U32))

def chol_cell_a(pa: Array<F32> & F32, pl: Array<F32> & F32, +i: U32, +j: U32, +k: U32) -> CSt:
  (a, aij) = pa
  (l, s) = pl
  chol_cell_branch(U32.is_eq(i, j), a, l, aij, s, i, j, k)

def chol_j(rem: Nat, st: CSt, +i: U32, +j: U32, +k: U32) -> CSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      CSt{a, l} = st
      st1 = chol_cell_a(Array.get(F32, a, ((i * k) + j : U32)), dot_l(U32.to_nat(j), (l, 0.0), (i * k : U32), (j * k : U32)), i, j, k)
      chol_j(p, st1, i, (j + 1 : U32), k)

def chol_i(rem: Nat, st: CSt, +i: U32, +k: U32) -> CSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      chol_i(p, chol_j(U32.to_nat((i + 1 : U32)), st, i, 0, k), (i + 1 : U32), k)

def diag_sum_step(p: Array<F32> & F32, +acc: F32) -> Array<F32> & F32:
  (a, v) = p
  (a, (acc + v : F32))

def diag_sum(rem: Nat, st: Array<F32> & F32, +i: U32, +k: U32) -> Array<F32> & F32:
  match rem:
    case 0n:
      st
    case 1n+p:
      (a, acc) = st
      diag_sum(p, diag_sum_step(Array.get(F32, a, ((i * k) + i : U32)), acc), (i + 1 : U32), k)

def chol_rep_fin(r: Array<F32> & F32, a: Array<F32>, +acc: F32) -> Array<F32> & F32:
  (_, d) = r
  (a, (acc + d : F32))

def chol_rep_once(st: CSt, +k: U32, +acc: F32) -> Array<F32> & F32:
  CSt{a, l} = st
  chol_rep_fin(diag_sum(U32.to_nat(k), (l, 0.0), 0, k), a, acc)

def chol_reps(rem: Nat, st: Array<F32> & F32, +k: U32) -> Array<F32> & F32:
  match rem:
    case 0n:
      st
    case 1n+p:
      (a, acc) = st
      st1 = chol_rep_once(chol_i(U32.to_nat(k), CSt{a, [0.0 : F32*4096n]}, 0, k), k, acc)
      chol_reps(p, st1, k)

# ---- Cyclic Jacobi symmetric eigendecomposition (in-place on A, accumulating V)
type JSt is Type:
  JSt{a: Array<F32>, v: Array<F32>}

def eye_loop(rem: Nat, v: Array<F32>, +i: U32, +k: U32) -> Array<F32>:
  match rem:
    case 0n:
      v
    case 1n+p:
      eye_loop(p, Array.set(F32, v, ((i * k) + i : U32), 1.0), (i + 1 : U32), k)

# Rotate row/col pair (p, q) at index r (for r != p, r != q) in symmetric matrix A
def rot_a_set(p2: Array<F32> & F32, +arp: F32, +c: F32, +s: F32, +rp: U32, +pr: U32, +rq: U32, +qr: U32) -> Array<F32>:
  (a, +arq) = p2
  +np = ((c * arp) - (s * arq) : F32)
  +nq = ((s * arp) + (c * arq) : F32)
  a1 = Array.set(F32, a, rp, np)
  a2 = Array.set(F32, a1, pr, np)
  a3 = Array.set(F32, a2, rq, nq)
  Array.set(F32, a3, qr, nq)

def rot_a_get1(p1: Array<F32> & F32, +c: F32, +s: F32, +rp: U32, +pr: U32, +rq: U32, +qr: U32) -> Array<F32>:
  (a, arp) = p1
  rot_a_set(Array.get(F32, a, rq), arp, c, s, rp, pr, rq, qr)

def rot_a_skip(skip: Bool, a: Array<F32>, +r: U32, +p: U32, +q: U32, +k: U32, +c: F32, +s: F32) -> Array<F32>:
  match skip:
    case True{}:
      a
    case False{}:
      +rp = ((r * k) + p : U32)
      +pr = ((p * k) + r : U32)
      +rq = ((r * k) + q : U32)
      +qr = ((q * k) + r : U32)
      rot_a_get1(Array.get(F32, a, rp), c, s, rp, pr, rq, qr)

def rot_a_loop(rem: Nat, a: Array<F32>, +r: U32, +p: U32, +q: U32, +k: U32, +c: F32, +s: F32) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+m:
      +skip = Bool.or(U32.is_eq(r, p), U32.is_eq(r, q))
      rot_a_loop(m, rot_a_skip(skip, a, r, p, q, k, c, s), (r + 1 : U32), p, q, k, c, s)

# Rotate columns p, q of eigenvector matrix V
def rot_v_set(p2: Array<F32> & F32, +vrp: F32, +c: F32, +s: F32, +rp: U32, +rq: U32) -> Array<F32>:
  (v, +vrq) = p2
  v1 = Array.set(F32, v, rp, ((c * vrp) - (s * vrq) : F32))
  Array.set(F32, v1, rq, ((s * vrp) + (c * vrq) : F32))

def rot_v_get1(p1: Array<F32> & F32, +c: F32, +s: F32, +rp: U32, +rq: U32) -> Array<F32>:
  (v, vrp) = p1
  rot_v_set(Array.get(F32, v, rq), vrp, c, s, rp, rq)

def rot_v_loop(rem: Nat, v: Array<F32>, +r: U32, +p: U32, +q: U32, +k: U32, +c: F32, +s: F32) -> Array<F32>:
  match rem:
    case 0n:
      v
    case 1n+m:
      +rp = ((r * k) + p : U32)
      +rq = ((r * k) + q : U32)
      rot_v_loop(m, rot_v_get1(Array.get(F32, v, rp), c, s, rp, rq), (r + 1 : U32), p, q, k, c, s)

def jac_apply(small: Bool, a: Array<F32>, v: Array<F32>, +app: F32, +aqq: F32, +apq: F32, +p: U32, +q: U32, +k: U32) -> JSt:
  match small:
    case True{}:
      JSt{a, v}
    case False{}:
      +tau = ((aqq - app) / (2.0 * apq) : F32)
      +abs_tau = F32.abs(tau)
      +denom = (abs_tau + F32.hypot(1.0, tau) : F32)
      +t = Bool.pick(F32, F32.is_ge(tau, 0.0), (1.0 / denom : F32), (F32.neg(1.0) / denom : F32))
      +c = (1.0 / F32.sqrt((1.0 + (t * t) : F32)) : F32)
      +s = (t * c : F32)
      a1 = rot_a_loop(U32.to_nat(k), a, 0, p, q, k, c, s)
      +npp = (((c * c * app) - (2.0 * s * c * apq)) + (s * s * aqq) : F32)
      +nqq = (((s * s * app) + (2.0 * s * c * apq)) + (c * c * aqq) : F32)
      a2 = Array.set(F32, a1, ((p * k) + p : U32), npp)
      a3 = Array.set(F32, a2, ((q * k) + q : U32), nqq)
      a4 = Array.set(F32, a3, ((p * k) + q : U32), 0.0)
      a5 = Array.set(F32, a4, ((q * k) + p : U32), 0.0)
      v1 = rot_v_loop(U32.to_nat(k), v, 0, p, q, k, c, s)
      JSt{a5, v1}

def jac_g3(r: Array<F32> & F32, v: Array<F32>, +app: F32, +aqq: F32, +p: U32, +q: U32, +k: U32) -> JSt:
  (a, +apq) = r
  jac_apply(F32.is_lt(F32.abs(apq), 1.0e-12), a, v, app, aqq, apq, p, q, k)

def jac_g2(r: Array<F32> & F32, v: Array<F32>, +app: F32, +p: U32, +q: U32, +k: U32) -> JSt:
  (a, aqq) = r
  jac_g3(Array.get(F32, a, ((p * k) + q : U32)), v, app, aqq, p, q, k)

def jac_g1(r: Array<F32> & F32, v: Array<F32>, +p: U32, +q: U32, +k: U32) -> JSt:
  (a, app) = r
  jac_g2(Array.get(F32, a, ((q * k) + q : U32)), v, app, p, q, k)

def jac_q(rem: Nat, st: JSt, +p: U32, +q: U32, +k: U32) -> JSt:
  match rem:
    case 0n:
      st
    case 1n+m:
      JSt{a, v} = st
      jac_q(m, jac_g1(Array.get(F32, a, ((p * k) + p : U32)), v, p, q, k), p, (q + 1 : U32), k)

def jac_p(rem: Nat, st: JSt, +p: U32, +k: U32) -> JSt:
  match rem:
    case 0n:
      st
    case 1n+m:
      +q0 = (p + 1 : U32)
      jac_p(m, jac_q(U32.to_nat((k - q0 : U32)), st, p, q0, k), q0, k)

def jac_sweeps(rem: Nat, st: JSt, +k: U32) -> JSt:
  match rem:
    case 0n:
      st
    case 1n+m:
      jac_sweeps(m, jac_p(U32.to_nat((k - 1 : U32)), st, 0, k), k)

def snd_f32(r: Array<F32> & F32) -> F32:
  (_, v) = r
  v

def jac_trace(st: JSt, +k: U32) -> F32:
  JSt{a, _} = st
  snd_f32(diag_sum(U32.to_nat(k), (a, 0.0), 0, k))

def num(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{n}:
      n
    case None{}:
      0

def tu(s: String) -> U32:
  num(U32.read(s))

def run_after_chol(r: Array<F32> & F32, +k: U32, +reps: U32, +sweeps: U32, +t0: Nat) -> IO(Unit):
  (a1, +chk_c) = r
  do IO<Unit>:
    +t1 : Nat <- IO.now()
    v0 : Array<F32> = eye_loop(U32.to_nat(k), [0.0 : F32*4096n], 0, k)
    +tr_j : F32 = jac_trace(jac_sweeps(U32.to_nat(sweeps), JSt{a1, v0}, k), k)
    t2 : Nat <- IO.now()
    IO.print("chol_chk=" ++ F32.show(chk_c) ++ " chol_total_ms=" ++ Nat.show(Nat.sub(t1, t0)) ++ " reps=" ++ U32.show(reps) ++ " jac_tr=" ++ F32.show(tr_j) ++ " jac_ms=" ++ Nat.show(Nat.sub(t2, t1)))

def run(+k: U32, +reps: U32, +sweeps: U32) -> IO(Unit):
  do IO<Unit>:
    a0 : Array<F32> = fill_spd(U32.to_nat(k), [0.0 : F32*4096n], 0, k)
    +t0 : Nat <- IO.now()
    run_after_chol(chol_reps(U32.to_nat(reps), (a0, 0.0), k), k, reps, sweeps, t0)

def go(args: List<String>) -> IO(Unit):
  match args:
    case _ <> ks <> rs <> ss <> _:
      run(tu(ks), tu(rs), tu(ss))
    case _:
      run(50, 50, 6)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
