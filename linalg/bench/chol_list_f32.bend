import Base

# Cholesky (K x K) on List<&2, List<&2, F32>> to compare against flat Array<F32>.
# Row i of L is built directly from previously completed rows L[0..i-1]:
#   for each prior row L[j] (j = 0..i-1):
#     L[i, j] = (A[i, j] - dot(L[i, 0..j-1], L[j, 0..j-1])) / L[j, j]
#   L[i, i] = sqrt(A[i, i] - dot(L[i, 0..i-1], L[i, 0..i-1]))
# Storing each row L[j] in reverse order (or forward) makes this purely sequential without random indexing!
# Usage: out/chol_list_f32 [K] [reps]   (default 50 50)

def lcg(+s: U32) -> U32:
  ((s * 1664525) + 1013904223 : U32)

def sym_val(+i: U32, +j: U32) -> F32:
  +lo = U32.min(i, j)
  +hi = U32.max(i, j)
  +h = lcg((((hi * 73856093) .^. (lo * 19349663)) + 12345 : U32))
  +u = ((U32.to_f32((h >> 8n : U32)) / 16777216.0) - 0.5 : F32)
  Bool.pick(F32, U32.is_eq(i, j), (10.0 + (U32.to_f32(i) * 0.5) : F32), (u * 0.2 : F32))

def gen_row(rem: Nat, +i: U32, +j: U32, acc: List<&2, F32>) -> List<&2, F32>:
  match rem:
    case 0n:
      List.reverse(&2, F32, acc)
    case 1n+p:
      gen_row(p, i, (j + 1 : U32), sym_val(i, j) <> acc)

def gen_spd(rem: Nat, +i: U32, +k: U32, acc: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match rem:
    case 0n:
      List.reverse(&2, List<&2, F32>, acc)
    case 1n+p:
      gen_spd(p, (i + 1 : U32), k, gen_row(U32.to_nat(k), i, 0, Nil{}) <> acc)

def dot(xs: List<&2, F32>, ys: List<&2, F32>, +acc: F32) -> F32:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      dot(xt, yt, (acc + (x * y) : F32))
    case _ _:
      acc

def sum_sq(xs: List<&2, F32>, +acc: F32) -> F32:
  match xs:
    case Nil{}:
      acc
    case Con{+x, t}:
      sum_sq(t, (acc + (x * x) : F32))

# Each completed row of L is stored as (diag, reversed prefix [L[j,j-1], ..., L[j,0]])
type LRow is Data:
  LRow{diag: F32, rev: List<&2, F32>}

# Compute row i of L (in reverse order) by walking prior LRows in forward order j = 0..i-1
# Note: row_i_rev has length j (reversed), so reversing row_i_rev vs storing forward:
# Actually store forward prefix [L[j,0], ..., L[j,j-1]] and append? No, dot(rev(a), rev(b)) == dot(a, b)!
# Wait: L[j] has length j, and row_i_rev ALSO has length j (indices j-1 down to 0)!
# So dot(row_i_rev, L[j].rev) computes sum_{p=0}^{j-1} L[i,p] * L[j,p] in O(j) with zero reverses!
def build_row(prev_rows: List<&2, LRow>, a_row: List<&2, F32>, +row_rev: List<&2, F32>) -> LRow:
  match prev_rows a_row:
    case Nil{} Con{aii, _}:
      LRow{F32.sqrt((aii - sum_sq(row_rev, 0.0) : F32)), row_rev}
    case Con{LRow{ljj, lj_rev}, rest_l} Con{aij, rest_a}:
      +lij = ((aij - dot(row_rev, lj_rev, 0.0)) / ljj : F32)
      build_row(rest_l, rest_a, lij <> row_rev)
    case _ _:
      LRow{0.0, row_rev}

def chol_rows(a_rows: List<&2, List<&2, F32>>, +done_fwd: List<&2, LRow>) -> List<&2, LRow>:
  match a_rows:
    case Nil{}:
      done_fwd
    case Con{ar, rest}:
      +lr = build_row(done_fwd, ar, Nil{})
      chol_rows(rest, List.append(&2, LRow, done_fwd, lr <> Nil{}))

def diag_sum(rows: List<&2, LRow>, +acc: F32) -> F32:
  match rows:
    case Nil{}:
      acc
    case Con{LRow{d, _}, rest}:
      diag_sum(rest, (acc + d : F32))

def chol_reps(rem: Nat, +a: List<&2, List<&2, F32>>, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      chol_reps(p, a, (acc + diag_sum(chol_rows(a, Nil{}), 0.0) : F32))

def num(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{n}:
      n
    case None{}:
      0

def tu(s: String) -> U32:
  num(U32.read(s))

def run(+k: U32, +reps: U32) -> IO(Unit):
  do IO<Unit>:
    +a : List<&2, List<&2, F32>> = gen_spd(U32.to_nat(k), 0, k, Nil{})
    t0 : Nat <- IO.now()
    +chk : F32 = chol_reps(U32.to_nat(reps), a, 0.0)
    t1 : Nat <- IO.now()
    IO.print("chol_chk=" ++ F32.show(chk) ++ " chol_total_ms=" ++ Nat.show(Nat.sub(t1, t0)) ++ " reps=" ++ U32.show(reps))

def go(args: List<String>) -> IO(Unit):
  match args:
    case _ <> ks <> rs <> _:
      run(tu(ks), tu(rs))
    case _:
      run(50, 50)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
