import Base

# Thin Householder QR on N x K matrix in flat Array<F32> (column-major: col j, row r at j*N + r).
# N*K <= 65536 (e.g. N=1000, K=50). Computes R in-place in upper triangle.
# Usage: out/qr_array_f32 [N] [K] [reps]   (default 1000 50 5)

def lcg(+s: U32) -> U32:
  ((s * 1664525) + 1013904223 : U32)

def unif(+s: U32) -> F32:
  ((U32.to_f32((s >> 8n : U32)) / 16777216.0) - 0.5 : F32)

def gen_col(rem: Nat, a: Array<F32>, +idx: U32, +s: U32) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+p:
      +s1 = lcg(s)
      gen_col(p, Array.set(F32, a, idx, unif(s1)), (idx + 1 : U32), s1)

def gen_mat(rem: Nat, a: Array<F32>, +j: U32, +n: U32, +s: U32) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+p:
      +s2 = lcg(((s * 2654435761) + 7 : U32))
      gen_mat(p, gen_col(U32.to_nat(n), a, (j * n : U32), s2), (j + 1 : U32), n, s2)

# Sum of squares of col k from row r0 to n-1
def col_ss_step(p: Array<F32> & F32, +acc: F32) -> Array<F32> & F32:
  (a, +v) = p
  (a, (acc + (v * v) : F32))

def col_ss(rem: Nat, st: Array<F32> & F32, +idx: U32) -> Array<F32> & F32:
  match rem:
    case 0n:
      st
    case 1n+p:
      (a, acc) = st
      col_ss(p, col_ss_step(Array.get(F32, a, idx), acc), (idx + 1 : U32))

# Dot product of col k (v, starting at k*n+k) with col j (starting at j*n+k), length n-k
def dot2(p: Array<F32> & F32, +vi: F32, +acc: F32) -> Array<F32> & F32:
  (a, vj) = p
  (a, (acc + (vi * vj) : F32))

def dot1(p: Array<F32> & F32, +oj: U32, +acc: F32) -> Array<F32> & F32:
  (a, vi) = p
  dot2(Array.get(F32, a, oj), vi, acc)

def col_dot(rem: Nat, st: Array<F32> & F32, +ok: U32, +oj: U32) -> Array<F32> & F32:
  match rem:
    case 0n:
      st
    case 1n+p:
      (a, acc) = st
      col_dot(p, dot1(Array.get(F32, a, ok), oj, acc), (ok + 1 : U32), (oj + 1 : U32))

# Update col j: A[r, j] -= scale * A[r, k] for r = k..n-1
def axpy2(p: Array<F32> & F32, +vk: F32, +scale: F32, +oj: U32) -> Array<F32>:
  (a, vj) = p
  Array.set(F32, a, oj, (vj - (scale * vk) : F32))

def axpy1(p: Array<F32> & F32, +oj: U32, +scale: F32) -> Array<F32>:
  (a, vk) = p
  axpy2(Array.get(F32, a, oj), vk, scale, oj)

def col_axpy(rem: Nat, a: Array<F32>, +ok: U32, +oj: U32, +scale: F32) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+p:
      col_axpy(p, axpy1(Array.get(F32, a, ok), oj, scale), (ok + 1 : U32), (oj + 1 : U32), scale)

def apply_col_do(r: Array<F32> & F32, +len: Nat, +ok: U32, +oj: U32, +beta: F32) -> Array<F32>:
  (a, d) = r
  col_axpy(len, a, ok, oj, (beta * d : F32))

def apply_cols(rem: Nat, a: Array<F32>, +j: U32, +k: U32, +n: U32, +beta: F32) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+p:
      +len = U32.to_nat((n - k : U32))
      +ok = ((k * n) + k : U32)
      +oj = ((j * n) + k : U32)
      a1 = apply_col_do(col_dot(len, (a, 0.0), ok, oj), len, ok, oj, beta)
      apply_cols(p, a1, (j + 1 : U32), k, n, beta)

def qr_step_apply(zero: Bool, a: Array<F32>, +k: U32, +n: U32, +m_cols: U32, +v0: F32, +rkk: F32, +tail_ss: F32) -> Array<F32>:
  match zero:
    case True{}:
      a
    case False{}:
      +v_norm2 = ((v0 * v0) + tail_ss : F32)
      +beta = (2.0 / v_norm2 : F32)
      +kk = ((k * n) + k : U32)
      a1 = Array.set(F32, a, kk, v0)
      a2 = apply_cols(U32.to_nat((m_cols - (k + 1) : U32)), a1, (k + 1 : U32), k, n, beta)
      Array.set(F32, a2, kk, rkk)

def qr_step_head(p: Array<F32> & F32, +tail_ss: F32, +k: U32, +n: U32, +m_cols: U32) -> Array<F32>:
  (a, +x0) = p
  +norm_x = F32.sqrt(((x0 * x0) + tail_ss : F32))
  +sign = Bool.pick(F32, F32.is_ge(x0, 0.0), 1.0, F32.neg(1.0))
  +v0 = (x0 + (sign * norm_x) : F32)
  +rkk = (F32.neg(sign) * norm_x : F32)
  qr_step_apply(F32.is_eq(norm_x, 0.0), a, k, n, m_cols, v0, rkk, tail_ss)

def qr_step_ss(r: Array<F32> & F32, +k: U32, +n: U32, +m_cols: U32) -> Array<F32>:
  (a, tail_ss) = r
  qr_step_head(Array.get(F32, a, ((k * n) + k : U32)), tail_ss, k, n, m_cols)

def qr_loop(rem: Nat, a: Array<F32>, +k: U32, +n: U32, +m_cols: U32) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+p:
      +tail_len = U32.to_nat((n - (k + 1) : U32))
      a1 = qr_step_ss(col_ss(tail_len, (a, 0.0), ((k * n) + (k + 1) : U32)), k, n, m_cols)
      qr_loop(p, a1, (k + 1 : U32), n, m_cols)

def r_diag_step(p: Array<F32> & F32, +acc: F32) -> Array<F32> & F32:
  (a, v) = p
  (a, (acc + F32.abs(v) : F32))

def r_diag_sum(rem: Nat, st: Array<F32> & F32, +i: U32, +n: U32) -> F32:
  match rem:
    case 0n:
      (_, acc) = st
      acc
    case 1n+p:
      (a, acc) = st
      r_diag_sum(p, r_diag_step(Array.get(F32, a, ((i * n) + i : U32)), acc), (i + 1 : U32), n)

def num(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{n}:
      n
    case None{}:
      0

def tu(s: String) -> U32:
  num(U32.read(s))

def run(+n: U32, +k: U32) -> IO(Unit):
  do IO<Unit>:
    a0 : Array<F32> = gen_mat(U32.to_nat(k), [0.0 : F32*65536n], 0, n, 12345)
    t0 : Nat <- IO.now()
    a1 : Array<F32> = qr_loop(U32.to_nat(k), a0, 0, n, k)
    +chk : F32 = r_diag_sum(U32.to_nat(k), (a1, 0.0), 0, n)
    t1 : Nat <- IO.now()
    IO.print("qr_chk=" ++ F32.show(chk) ++ " qr_ms=" ++ Nat.show(Nat.sub(t1, t0)))

def go(args: List<String>) -> IO(Unit):
  match args:
    case _ <> ns <> ks <> _:
      run(tu(ns), tu(ks))
    case _:
      run(1000, 50)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
