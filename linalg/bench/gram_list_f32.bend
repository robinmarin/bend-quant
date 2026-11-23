import Base

# Gram matrix G = B^T B for B of size N x K, using List<&2, List<&2, F32>>.
# Stored as K columns of length N (i.e. B^T), so G[i, j] = dot(col_i, col_j).
# Usage: out/gram_list_f32 [N] [K] [depth]   (default 1000 50 3)

def lcg(+s: U32) -> U32:
  ((s * 1664525) + 1013904223 : U32)

def unif(+s: U32) -> F32:
  ((U32.to_f32((s >> 8n : U32)) / 16777216.0) - 0.5 : F32)

def gen_col(n: Nat, +s: U32, acc: List<&2, F32>) -> List<&2, F32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +s1 = lcg(s)
      gen_col(p, s1, unif(s1) <> acc)

def gen_cols(k: Nat, +n: Nat, +s: U32, acc: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match k:
    case 0n:
      acc
    case 1n+p:
      +s2 = lcg(((s * 2654435761) + 7 : U32))
      gen_cols(p, n, s2, gen_col(n, s2, Nil{}) <> acc)

def dot(xs: List<&2, F32>, ys: List<&2, F32>, +acc: F32) -> F32:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      dot(xt, yt, (acc + (x * y) : F32))
    case _ _:
      acc

def gram_row(+ci: List<&2, F32>, cols: List<&2, List<&2, F32>>, acc: List<&2, F32>) -> List<&2, F32>:
  match cols:
    case Nil{}:
      List.reverse(&2, F32, acc)
    case Con{cj, rest}:
      gram_row(ci, rest, dot(ci, cj, 0.0) <> acc)

def gram_seq(rows: List<&2, List<&2, F32>>, +all_cols: List<&2, List<&2, F32>>, acc: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match rows:
    case Nil{}:
      List.reverse(&2, List<&2, F32>, acc)
    case Con{ci, rest}:
      gram_seq(rest, all_cols, gram_row(ci, all_cols, Nil{}) <> acc)

def half_nat(n: Nat) -> Nat:
  U32.to_nat((U32.from_nat(n) >> 1n : U32))

def gram_par(+depth: Nat, +rows: List<&2, List<&2, F32>>, +all_cols: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match depth:
    case 0n:
      gram_seq(rows, all_cols, Nil{})
    case 1n+d:
      +h = half_nat(List.length(&2, List<&2, F32>, rows))
      a b = gram_par(d, List.take(&2, List<&2, F32>, rows, h), all_cols) gram_par(d, List.drop(&2, List<&2, F32>, rows, h), all_cols)
      List.append(&2, List<&2, F32>, a, b)

def sum_list(xs: List<&2, F32>, +acc: F32) -> F32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      sum_list(t, (acc + h : F32))

def sum_mat(m: List<&2, List<&2, F32>>, +acc: F32) -> F32:
  match m:
    case Nil{}:
      acc
    case Con{r, t}:
      sum_mat(t, (acc + sum_list(r, 0.0) : F32))

def num(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{n}:
      n
    case None{}:
      0

def tn(s: String) -> Nat:
  U32.to_nat(num(U32.read(s)))

def run(+n: Nat, +k: Nat, +d: Nat) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    +cols : List<&2, List<&2, F32>> = gen_cols(k, n, 12345, Nil{})
    +t1 : Nat <- IO.now()
    g : List<&2, List<&2, F32>> = gram_par(d, cols, cols)
    +chk : F32 = sum_mat(g, 0.0)
    t2 : Nat <- IO.now()
    IO.print("chk=" ++ F32.show(chk) ++ " gen_ms=" ++ Nat.show(Nat.sub(t1, t0)) ++ " gram_ms=" ++ Nat.show(Nat.sub(t2, t1)))

def go(args: List<String>) -> IO(Unit):
  match args:
    case _ <> ns <> ks <> ds <> _:
      run(tn(ns), tn(ks), tn(ds))
    case _ <> ns <> ks <> _:
      run(tn(ns), tn(ks), 3n)
    case _:
      run(1000n, 50n, 3n)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
