import Base

# Gram matrix G = B^T B for B of size N x K, using flat Array<F32>.
# B stored column-major: col j, row r is at index j * N + r (N*K <= 65536).
# G stored row-major in a 4096-slot Array<F32> (K <= 64).
# Usage: out/gram_array_f32 [N] [K]   (default 1000 50)

def lcg(+s: U32) -> U32:
  ((s * 1664525) + 1013904223 : U32)

def unif(+s: U32) -> F32:
  ((U32.to_f32((s >> 8n : U32)) / 16777216.0) - 0.5 : F32)

def gen_col(r_left: Nat, a: Array<F32>, +idx: U32, +s: U32) -> Array<F32>:
  match r_left:
    case 0n:
      a
    case 1n+p:
      +s1 = lcg(s)
      gen_col(p, Array.set(F32, a, idx, unif(s1)), (idx + 1 : U32), s1)

def gen_mat(k_left: Nat, a: Array<F32>, +j: U32, +n: U32, +s: U32) -> Array<F32>:
  match k_left:
    case 0n:
      a
    case 1n+p:
      +s2 = lcg(((s * 2654435761) + 7 : U32))
      gen_mat(p, gen_col(U32.to_nat(n), a, (j * n : U32), s2), (j + 1 : U32), n, s2)

# dot(col i, col j) in flat array a, returning (a, sum)
def dot_step2(p: Array<F32> & F32, +vi: F32, +acc: F32) -> Array<F32> & F32:
  (a, vj) = p
  (a, (acc + (vi * vj) : F32))

def dot_step1(p: Array<F32> & F32, +oj: U32, +acc: F32) -> Array<F32> & F32:
  (a, vi) = p
  dot_step2(Array.get(F32, a, oj), vi, acc)

def dot_loop(rem: Nat, st: Array<F32> & F32, +oi: U32, +oj: U32) -> Array<F32> & F32:
  match rem:
    case 0n:
      st
    case 1n+p:
      (a, acc) = st
      dot_loop(p, dot_step1(Array.get(F32, a, oi), oj, acc), (oi + 1 : U32), (oj + 1 : U32))

type GSt is Type:
  GSt{b: Array<F32>, g: Array<F32>}

def set_g(r: Array<F32> & F32, g: Array<F32>, +i: U32, +j: U32, +k: U32) -> GSt:
  (b, +v) = r
  g1 = Array.set(F32, g, ((i * k) + j : U32), v)
  g2 = Array.set(F32, g1, ((j * k) + i : U32), v)
  GSt{b, g2}

def gram_j(rem: Nat, st: GSt, +i: U32, +j: U32, +n: U32, +k: U32) -> GSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      GSt{b, g} = st
      st1 = set_g(dot_loop(U32.to_nat(n), (b, 0.0), (i * n : U32), (j * n : U32)), g, i, j, k)
      gram_j(p, st1, i, (j + 1 : U32), n, k)

def gram_i(rem: Nat, st: GSt, +i: U32, +n: U32, +k: U32) -> GSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      st1 = gram_j(U32.to_nat((k - i : U32)), st, i, i, n, k)
      gram_i(p, st1, (i + 1 : U32), n, k)

def sum_arr_step(p: Array<F32> & F32, +acc: F32) -> Array<F32> & F32:
  (a, v) = p
  (a, (acc + v : F32))

def sum_arr(rem: Nat, st: Array<F32> & F32, +idx: U32) -> F32:
  match rem:
    case 0n:
      (_, acc) = st
      acc
    case 1n+p:
      (a, acc) = st
      sum_arr(p, sum_arr_step(Array.get(F32, a, idx), acc), (idx + 1 : U32))

def extract_g(st: GSt) -> Array<F32>:
  GSt{_, g} = st
  g

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
    t0 : Nat <- IO.now()
    b : Array<F32> = gen_mat(U32.to_nat(k), [0.0 : F32*65536n], 0, n, 12345)
    +t1 : Nat <- IO.now()
    g : Array<F32> = extract_g(gram_i(U32.to_nat(k), GSt{b, [0.0 : F32*4096n]}, 0, n, k))
    +chk : F32 = sum_arr(U32.to_nat((k * k : U32)), (g, 0.0), 0)
    t2 : Nat <- IO.now()
    IO.print("chk=" ++ F32.show(chk) ++ " gen_ms=" ++ Nat.show(Nat.sub(t1, t0)) ++ " gram_ms=" ++ Nat.show(Nat.sub(t2, t1)))

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
