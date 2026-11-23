# Fast flat-Array<F32> deterministic subspace-iteration top-K SVD.
# Exploits K << min(m, n) via QR-stabilized power iterations in O(n_iter * m * n * (k + p)),
# delegating directly to exact linalg.svd_thin when min(m, n) is small or 2*k >= min(m, n).
# Internal kernel to risk; public entry points live in risk.bend.
import Base
import bend-kit-f32array@0.2.1.0/f32array.bend as A
import bend-quant-linalg@0.1.0.0/linalg.bend as L

# ---------------------------------------------------------------- flat array helpers

def arr_depth.go(rem: Nat, +d: Nat, +cap: U32, +n: U32) -> Nat:
  match rem:
    case 0n:
      d
    case 1n+p:
      +lt = U32.is_lt(cap, n)
      arr_depth.go(p, Bool.pick(Nat, lt, 1n+d, d), Bool.pick(U32, lt, (cap << 1n : U32), cap), n)

def arr_depth(+n: U32) -> Nat:
  arr_depth.go(30n, 0n, 1, n)

def fill_row_rm(r: List<&2, F32>, a: Array<F32>, +idx: U32) -> Array<F32>:
  match r:
    case Nil{}:
      a
    case Con{x, t}:
      fill_row_rm(t, Array.set(F32, a, idx, x), (idx + 1 : U32))

def fill_mat_rm(rows: List<&2, List<&2, F32>>, a: Array<F32>, +off: U32, +nc: U32) -> Array<F32>:
  match rows:
    case Nil{}:
      a
    case Con{r, t}:
      fill_mat_rm(t, fill_row_rm(r, a, off), (off + nc : U32), nc)

def mat_to_rm(rows: List<&2, List<&2, F32>>, +m: U32, +n: U32) -> Array<F32>:
  fill_mat_rm(rows, Array.new(F32, arr_depth((m * n : U32)), 0.0), 0, n)

# Extract column-major m x q array into row-major List<&2, List<&2, F32>>.
type CMRow is Type:
  CMRow{a: Array<F32>, row: List<&2, F32>}

def cm_row.push(p: Array<F32> & F32, row: List<&2, F32>) -> CMRow:
  (a, v) = p
  CMRow{a, v <> row}

def cm_row.go(rem: Nat, st: CMRow, +i: U32, +j: U32, +m: U32) -> CMRow:
  match rem:
    case 0n:
      st
    case 1n+p:
      CMRow{a, row} = st
      cm_row.go(p, cm_row.push(Array.get(F32, a, ((j * m) + i : U32)), row), i, (j - 1 : U32), m)

type CMMat is Type:
  CMMat{a: Array<F32>, rows: List<&2, List<&2, F32>>}

def cm_mat.push(st: CMRow, rows: List<&2, List<&2, F32>>) -> CMMat:
  CMRow{a, row} = st
  CMMat{a, row <> rows}

def cm_mat.go(rem: Nat, st: CMMat, +i: U32, +m: U32, +q: U32, +qn: Nat) -> List<&2, List<&2, F32>>:
  match rem:
    case 0n:
      CMMat{_, rows} = st
      rows
    case 1n+p:
      CMMat{a, rows} = st
      st1 = cm_mat.push(cm_row.go(qn, CMRow{a, Nil{}}, i, (q - 1 : U32), m), rows)
      cm_mat.go(p, st1, (i - 1 : U32), m, q, qn)

def cm_to_mat(a: Array<F32>, +m: U32, +q: U32) -> L.Mat:
  L.Mat{m, q, cm_mat.go(U32.to_nat(m), CMMat{a, Nil{}}, (m - 1 : U32), m, q, U32.to_nat(q))}

# Extract row-major q x n array into L.Mat.
def rm_row.go(rem: Nat, st: CMRow, +off: U32) -> CMRow:
  match rem:
    case 0n:
      st
    case 1n+p:
      CMRow{a, row} = st
      rm_row.go(p, cm_row.push(Array.get(F32, a, off), row), (off - 1 : U32))

def rm_mat.go(rem: Nat, st: CMMat, +i: U32, +n: U32, +nn: Nat) -> List<&2, List<&2, F32>>:
  match rem:
    case 0n:
      CMMat{_, rows} = st
      rows
    case 1n+p:
      CMMat{a, rows} = st
      +last = (((i * n) + n) - 1 : U32)
      st1 = cm_mat.push(rm_row.go(nn, CMRow{a, Nil{}}, last), rows)
      rm_mat.go(p, st1, (i - 1 : U32), n, nn)

def rm_to_mat(a: Array<F32>, +q: U32, +n: U32) -> L.Mat:
  L.Mat{q, n, rm_mat.go(U32.to_nat(q), CMMat{a, Nil{}}, (q - 1 : U32), n, U32.to_nat(n))}

# ---------------------------------------------------------------- deterministic probe matrix (n x q, col-major)

# Deterministic LCG in [-1, 1] (pure, zero IO).
def lcg_next(+s: U32) -> U32:
  (((s * 1664525) + 1013904223) : U32)

def lcg_f32(+s: U32) -> F32:
  # Map top 24 bits to [-1, 1]
  +u = U32.to_f32((s >> 8n : U32))
  (((u * 1.1920929e-7) - 1.0) : F32)

def probe.fill(rem: Nat, a: Array<F32>, +idx: U32, +seed: U32) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+p:
      +s1 = lcg_next(seed)
      probe.fill(p, Array.set(F32, a, idx, lcg_f32(s1)), (idx + 1 : U32), s1)

def make_probe(+n: U32, +q: U32) -> Array<F32>:
  +tot = (n * q : U32)
  probe.fill(U32.to_nat(tot), Array.new(F32, arr_depth(tot), 0.0), 0, 2463534242)

# ---------------------------------------------------------------- flat-array matrix products
# A is row-major m x n; X is col-major n x q; Y is col-major m x q.

type DotRMCM is Type:
  DotRMCM{a: Array<F32>, x: Array<F32>, acc: F32}

def dot_rmcm.step2(px: Array<F32> & F32, a: Array<F32>, +av: F32, +acc: F32) -> DotRMCM:
  (x, xv) = px
  DotRMCM{a, x, (acc + (av * xv) : F32)}

def dot_rmcm.step1(pa: Array<F32> & F32, x: Array<F32>, +xi: U32, +acc: F32) -> DotRMCM:
  (a, av) = pa
  dot_rmcm.step2(Array.get(F32, x, xi), a, av, acc)

def dot_rmcm(rem: Nat, st: DotRMCM, +ai: U32, +xi: U32) -> DotRMCM:
  match rem:
    case 0n:
      st
    case 1n+p:
      DotRMCM{a, x, acc} = st
      dot_rmcm(p, dot_rmcm.step1(Array.get(F32, a, ai), x, xi, acc), (ai + 1 : U32), (xi + 1 : U32))

type MulSt is Type:
  MulSt{a: Array<F32>, x: Array<F32>, y: Array<F32>}

def mul_ax.set(st: DotRMCM, y: Array<F32>, +yi: U32) -> MulSt:
  DotRMCM{a, x, acc} = st
  MulSt{a, x, Array.set(F32, y, yi, acc)}

# Y[i, col] = sum_j A[i*n + j] * X[col*n + j]
def mul_ax.i(rem: Nat, st: MulSt, +i: U32, +col: U32, +m: U32, +n: U32, +nn: Nat) -> MulSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      MulSt{a, x, y} = st
      st1 = mul_ax.set(dot_rmcm(nn, DotRMCM{a, x, 0.0}, (i * n : U32), (col * n : U32)), y, ((col * m) + i : U32))
      mul_ax.i(p, st1, (i + 1 : U32), col, m, n, nn)

def mul_ax.col(rem: Nat, st: MulSt, +col: U32, +m: U32, +mm: Nat, +n: U32, +nn: Nat) -> MulSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      mul_ax.col(p, mul_ax.i(mm, st, 0, col, m, n, nn), (col + 1 : U32), m, mm, n, nn)

# Computes Y = A * X where A is m x n (row-major), X is n x q (col-major), Y is m x q (col-major).
# Returns (A, Y) (consumes X).
def mul_ax.fin(st: MulSt) -> Array<F32> & Array<F32>:
  MulSt{a, _, y} = st
  (a, y)

def mul_ax(a: Array<F32>, x: Array<F32>, +m: U32, +n: U32, +q: U32) -> Array<F32> & Array<F32>:
  y0 = Array.new(F32, arr_depth((m * q : U32)), 0.0)
  mul_ax.fin(mul_ax.col(U32.to_nat(q), MulSt{a, x, y0}, 0, m, U32.to_nat(m), n, U32.to_nat(n)))

# Computes Z = A^T * Q where A is m x n (row-major), Q is m x q (col-major), Z is n x q (col-major).
# Accumulates row-wise over i = 0..m-1: Z[col*n + j] += A[i*n + j] * Q[col*m + i].
type AtQRow is Type:
  AtQRow{a: Array<F32>, z: Array<F32>}

def atq.upd(pz: Array<F32> & F32, a: Array<F32>, +av: F32, +qv: F32, +zi: U32) -> AtQRow:
  (z, zv) = pz
  AtQRow{a, Array.set(F32, z, zi, (zv + (av * qv) : F32))}

def atq.step_a(pa: Array<F32> & F32, z: Array<F32>, +qv: F32, +zi: U32) -> AtQRow:
  (a, av) = pa
  atq.upd(Array.get(F32, z, zi), a, av, qv, zi)

def atq.j(rem: Nat, st: AtQRow, +ai: U32, +zi: U32, +qv: F32) -> AtQRow:
  match rem:
    case 0n:
      st
    case 1n+p:
      AtQRow{a, z} = st
      atq.j(p, atq.step_a(Array.get(F32, a, ai), z, qv, zi), (ai + 1 : U32), (zi + 1 : U32), qv)

def atq.wrap_col(st: AtQRow, q: Array<F32>) -> MulSt:
  AtQRow{a, z} = st
  MulSt{a, q, z}

def atq.get_q(pq: Array<F32> & F32, a: Array<F32>, z: Array<F32>, +ai0: U32, +zi0: U32, +nn: Nat) -> MulSt:
  (q, qv) = pq
  atq.wrap_col(atq.j(nn, AtQRow{a, z}, ai0, zi0, qv), q)

def atq.col(rem: Nat, st: MulSt, +i: U32, +col: U32, +m: U32, +n: U32, +nn: Nat) -> MulSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      MulSt{a, q, z} = st
      st1 = atq.get_q(Array.get(F32, q, ((col * m) + i : U32)), a, z, (i * n : U32), (col * n : U32), nn)
      atq.col(p, st1, i, (col + 1 : U32), m, n, nn)

def atq.i(rem: Nat, st: MulSt, +i: U32, +m: U32, +n: U32, +nn: Nat, +qn: Nat) -> MulSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      atq.i(p, atq.col(qn, st, i, 0, m, n, nn), (i + 1 : U32), m, n, nn, qn)

def mul_atq.fin(st: MulSt) -> Array<F32> & Array<F32>:
  MulSt{a, _, z} = st
  (a, z)

def mul_atq(a: Array<F32>, q: Array<F32>, +m: U32, +n: U32, +qcols: U32) -> Array<F32> & Array<F32>:
  z0 = Array.new(F32, arr_depth((n * qcols : U32)), 0.0)
  mul_atq.fin(atq.i(U32.to_nat(m), MulSt{a, q, z0}, 0, m, n, U32.to_nat(n), U32.to_nat(qcols)))

# Computes B = Q^T * A (row-major q x n) while keeping Q intact!
# Here Z = A^T * Q in col-major n x q IS ALREADY B = Q^T * A in row-major q x n!
# Because Z[col * n + j] = (A^T Q)[j, col] = (Q^T A)[col, j] = B[col * n + j]!
def mul_qta.fin(st: MulSt) -> Array<F32> & Array<F32>:
  MulSt{_, q1, b} = st
  (q1, b)

def mul_qta(a: Array<F32>, q: Array<F32>, +m: U32, +n: U32, +qcols: U32) -> Array<F32> & Array<F32>:
  z0 = Array.new(F32, arr_depth((n * qcols : U32)), 0.0)
  mul_qta.fin(atq.i(U32.to_nat(m), MulSt{a, q, z0}, 0, m, n, U32.to_nat(n), U32.to_nat(qcols)))

# ---------------------------------------------------------------- flat-array orthonormalization (Modified Gram-Schmidt x2)
# Twice-iterated MGS (Kahan-Parlett) on col-major m x q array achieves machine-precision
# orthogonality (< 1e-6 in F32) in ~1/3 the code of Householder QR and keeps Q in place!

def cm_col_ss.step(p: Array<F32> & F32, +acc: F32) -> Array<F32> & F32:
  (a, +v) = p
  (a, (acc + (v * v) : F32))

def cm_col_ss(rem: Nat, st: Array<F32> & F32, +idx: U32) -> Array<F32> & F32:
  match rem:
    case 0n:
      st
    case 1n+p:
      (a, acc) = st
      cm_col_ss(p, cm_col_ss.step(Array.get(F32, a, idx), acc), (idx + 1 : U32))

def cm_col_dot.step2(p: Array<F32> & F32, +v1: F32, +acc: F32) -> Array<F32> & F32:
  (a, v2) = p
  (a, (acc + (v1 * v2) : F32))

def cm_col_dot.step1(p: Array<F32> & F32, +i2: U32, +acc: F32) -> Array<F32> & F32:
  (a, v1) = p
  cm_col_dot.step2(Array.get(F32, a, i2), v1, acc)

def cm_col_dot(rem: Nat, st: Array<F32> & F32, +i1: U32, +i2: U32) -> Array<F32> & F32:
  match rem:
    case 0n:
      st
    case 1n+p:
      (a, acc) = st
      cm_col_dot(p, cm_col_dot.step1(Array.get(F32, a, i1), i2, acc), (i1 + 1 : U32), (i2 + 1 : U32))

# col_k -= d * col_j
def cm_col_axpy.step2(p: Array<F32> & F32, +vj: F32, +d: F32, +ik: U32) -> Array<F32>:
  (a, vk) = p
  Array.set(F32, a, ik, (vk - (d * vj) : F32))

def cm_col_axpy.step1(p: Array<F32> & F32, +ik: U32, +d: F32) -> Array<F32>:
  (a, vj) = p
  cm_col_axpy.step2(Array.get(F32, a, ik), vj, d, ik)

def cm_col_axpy(rem: Nat, a: Array<F32>, +ij: U32, +ik: U32, +d: F32) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+p:
      cm_col_axpy(p, cm_col_axpy.step1(Array.get(F32, a, ij), ik, d), (ij + 1 : U32), (ik + 1 : U32), d)

# col_k *= s
def cm_col_scale.step(p: Array<F32> & F32, +ik: U32, +s: F32) -> Array<F32>:
  (a, v) = p
  Array.set(F32, a, ik, (v * s : F32))

def cm_col_scale(rem: Nat, a: Array<F32>, +ik: U32, +s: F32) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+p:
      cm_col_scale(p, cm_col_scale.step(Array.get(F32, a, ik), ik, s), (ik + 1 : U32), s)

# Single pass orthogonalizing col k against cols 0..k-1.
def mgs.orth_one(p: Array<F32> & F32, +joff: U32, +koff: U32, +mm: Nat) -> Array<F32>:
  (a, d) = p
  cm_col_axpy(mm, a, joff, koff, d)

def mgs.orth_loop(rem: Nat, a: Array<F32>, +j: U32, +koff: U32, +m: U32, +mm: Nat) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+p:
      +joff = (j * m : U32)
      a1 = mgs.orth_one(cm_col_dot(mm, (a, 0.0), joff, koff), joff, koff, mm)
      mgs.orth_loop(p, a1, (j + 1 : U32), koff, m, mm)

def mgs.norm_col(p: Array<F32> & F32, +koff: U32, +mm: Nat) -> Array<F32>:
  (a, ss) = p
  +nrm = F32.sqrt(ss)
  +ok = F32.is_gt(nrm, 1.0e-12)
  +sc = Bool.pick(F32, ok, (1.0 / nrm : F32), 0.0)
  cm_col_scale(mm, a, koff, sc)

def mgs.cols(rem: Nat, a: Array<F32>, +k: U32, +m: U32, +mm: Nat) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+p:
      +koff = (k * m : U32)
      +kn = U32.to_nat(k)
      a1 = mgs.orth_loop(kn, a, 0, koff, m, mm)
      a2 = mgs.orth_loop(kn, a1, 0, koff, m, mm)
      a3 = mgs.norm_col(cm_col_ss(mm, (a2, 0.0), koff), koff, mm)
      mgs.cols(p, a3, (k + 1 : U32), m, mm)

def orthonormalize_cm(a: Array<F32>, +m: U32, +q: U32) -> Array<F32>:
  mgs.cols(U32.to_nat(q), a, 0, m, U32.to_nat(m))

# ---------------------------------------------------------------- subspace iteration loop

def sub_iter.step2(p: Array<F32> & Array<F32>, +m: U32, +q: U32) -> Array<F32> & Array<F32>:
  (a, y) = p
  (a, orthonormalize_cm(y, m, q))

def sub_iter.step1(p: Array<F32> & Array<F32>, +m: U32, +n: U32, +q: U32) -> Array<F32> & Array<F32>:
  (a, z) = p
  z1 = orthonormalize_cm(z, n, q)
  sub_iter.step2(mul_ax(a, z1, m, n, q), m, q)

def sub_iter.go(rem: Nat, st: Array<F32> & Array<F32>, +m: U32, +n: U32, +q: U32) -> Array<F32> & Array<F32>:
  match rem:
    case 0n:
      st
    case 1n+p:
      (a, qmat) = st
      sub_iter.go(p, sub_iter.step1(mul_atq(a, qmat, m, n, q), m, n, q), m, n, q)

# ---------------------------------------------------------------- slicing top-k from L.SVD

def take_f32(k: Nat, xs: List<&2, F32>) -> List<&2, F32>:
  match k xs:
    case 0n _:
      Nil{}
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{h, t}:
      h <> take_f32(p, t)

def slice_svd(svd: L.SVD, +k: U32) -> L.SVD:
  L.SVD{u, L.Vec{_, ss}, vt} = svd
  L.SVD{L.slice_cols(u, 0, k), L.Vec{k, take_f32(U32.to_nat(k), ss)}, L.slice_rows(vt, 0, k)}

def svd_subspace.pick_u(mu: Maybe<&2, L.Mat>, fallback: L.Mat, sb: L.Vec, vtb: L.Mat, +k: U32) -> L.SVD:
  match mu:
    case Some{um}:
      slice_svd(L.SVD{um, sb, vtb}, k)
    case None{}:
      slice_svd(L.SVD{fallback, sb, vtb}, k)

def svd_subspace.combine1(svd: L.SVD, +q_mat: L.Mat, +k: U32) -> L.SVD:
  L.SVD{ub, sb, vtb} = svd
  svd_subspace.pick_u(L.matmul(q_mat, ub), q_mat, sb, vtb, k)

def svd_subspace.combine(q_mat: L.Mat, b_mat: L.Mat, +k: U32) -> L.SVD:
  svd_subspace.combine1(L.svd_thin(b_mat), q_mat, k)

def svd_subspace.finish2(p: Array<F32> & Array<F32>, +m: U32, +n: U32, +q: U32, +k: U32) -> L.SVD:
  (q1, b_arr) = p
  svd_subspace.combine(cm_to_mat(q1, m, q), rm_to_mat(b_arr, q, n), k)

def svd_subspace.finish(p: Array<F32> & Array<F32>, +m: U32, +n: U32, +q: U32, +k: U32) -> L.SVD:
  (a, q_arr) = p
  svd_subspace.finish2(mul_qta(a, q_arr, m, n, q), m, n, q, k)

def svd_subspace.tall1(p: Array<F32> & Array<F32>, +m: U32, +n: U32, +q: U32, +k: U32, +n_iter: U32) -> L.SVD:
  (a1, y0) = p
  q0 = orthonormalize_cm(y0, m, q)
  svd_subspace.finish(sub_iter.go(U32.to_nat(n_iter), (a1, q0), m, n, q), m, n, q, k)

def svd_subspace.tall(rows: List<&2, List<&2, F32>>, +m: U32, +n: U32, +k: U32, +oversample: U32, +n_iter: U32) -> L.SVD:
  +q = U32.min(U32.min(m, n), (k + oversample : U32))
  a0 = mat_to_rm(rows, m, n)
  om = make_probe(n, q)
  svd_subspace.tall1(mul_ax(a0, om, m, n, q), m, n, q, k, n_iter)

def svd_subspace.wide_fin(svd: L.SVD) -> L.SVD:
  L.SVD{u_t, s, vt_t} = svd
  L.SVD{L.transpose(vt_t), s, L.transpose(u_t)}

def svd_subspace.wide1(at: L.Mat, +k: U32, +oversample: U32, +n_iter: U32) -> L.SVD:
  L.Mat{m, n, rows} = at
  svd_subspace.wide_fin(svd_subspace.tall(rows, m, n, k, oversample, n_iter))

def svd_subspace.wide(a: L.Mat, +k: U32, +oversample: U32, +n_iter: U32) -> L.SVD:
  svd_subspace.wide1(L.transpose(a), k, oversample, n_iter)

def svd_subspace.orient(is_tall: Bool, a: L.Mat, +k: U32, +oversample: U32, +n_iter: U32) -> L.SVD:
  match is_tall:
    case True{}:
      L.Mat{m, n, rows} = a
      svd_subspace.tall(rows, m, n, k, oversample, n_iter)
    case False{}:
      svd_subspace.wide(a, k, oversample, n_iter)

def svd_top_k.branch(exact: Bool, +a: L.Mat, +k: U32, +oversample: U32, +n_iter: U32) -> L.SVD:
  match exact:
    case True{}:
      slice_svd(L.svd_thin(a), k)
    case False{}:
      L.Mat{+m, +n, _} = a
      svd_subspace.orient(U32.is_ge(m, n), a, k, oversample, n_iter)

def svd_top_k.zero(is_zero: Bool, +a: L.Mat, +k: U32, +oversample: U32, +n_iter: U32) -> L.SVD:
  match is_zero:
    case True{}:
      L.Mat{+m, +n, _} = a
      L.SVD{L.Mat.zeros(m, 0), L.Vec{0, Nil{}}, L.Mat.zeros(0, n)}
    case False{}:
      L.Mat{+m, +n, _} = a
      +mn = U32.min(m, n)
      +k_clamped = U32.min(k, mn)
      +use_exact = Bool.or(U32.is_le(mn, U32.max((k_clamped + oversample : U32), 40)), U32.is_ge((k_clamped * 2 : U32), mn))
      svd_top_k.branch(use_exact, a, k_clamped, oversample, n_iter)

# Fast deterministic top-k SVD of a (m x n):
#   a ~= U * diag(s) * Vt,  U is m x k, s is length k (descending), Vt is k x n.
# Uses exact linalg.svd_thin when min(m, n) <= max(k + oversample, 40) or 2*k >= min(m, n),
# otherwise runs QR/MGS-stabilized subspace iteration in flat Array<F32>.
def svd_top_k(+a: L.Mat, +k: U32, +oversample: U32, +n_iter: U32) -> L.SVD:
  L.Mat{+m, +n, _} = a
  +mn = U32.min(m, n)
  svd_top_k.zero(Bool.or(U32.is_eq(k, 0), U32.is_eq(mn, 0)), a, k, oversample, n_iter)
