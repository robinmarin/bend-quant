# linalg: dense linear algebra over float32 vectors and matrices.
# Design notes: https://github.com/robinmarin/bend-quant/blob/main/linalg/DESIGN.md
#
# Public: Vec, Mat, QR, Eigen, SVD, Vec.from_list, Vec.from_flat, Vec.zeros,
# Vec.ones, Vec.get, Mat.from_rows, Mat.from_flat, Mat.zeros, Mat.eye,
# Mat.diag, Mat.get, Mat.diag_vec, dot, norm1, norm2, vscale, vadd, vsub, axpy,
# vmul, vdiv, outer, scale, madd, msub, frobenius, trace, transpose,
# slice_rows, slice_cols, submatrix, diag_mul, mul_diag, matvec, matvec_t,
# matmul, gram, wgram, quad_form, cholesky, solve_lower, solve_upper,
# solve_lower_mat, solve_upper_mat, cholesky_solve, cholesky_solve_mat,
# cholesky_logdet, woodbury_solve, woodbury_logdet, qr_thin, lstsq, wlstsq,
# lstsq_mat, project_orth, lstsq_constrained, sym_eigen, spd_pow, svd_thin,
# pinv, procrustes.
# Every other def is internal. LAWS.bend and PROOF.bend name them, and they can
# change in any version.
import Base
import bend-kit-f32array@0.2.1.0/f32array.bend as A

# A length-n vector of F32 values.
type Vec is Data:
  Vec{n: U32, data: List<&2, F32>}

# An m x n row-major matrix of F32 values.
type Mat is Data:
  Mat{m: U32, n: U32, rows: List<&2, List<&2, F32>>}

# ---------------------------------------------------------------- parallel map
# Identical fork-join structure to signal's pmap, proved equal to pseq in PROOF.bend.

type Two<-A: Data> is Data:
  Two{l: List<&2, A>, r: List<&2, A>}

def split.cons(-A: Data, h: A, two: Two<A>) -> Two<A>:
  Two{l, r} = two
  Two{h <> l, r}

def split(-A: Data, k: Nat, xs: List<&2, A>) -> Two<A>:
  match k xs:
    case 0n _:
      Two{Nil{}, xs}
    case 1n+p Nil{}:
      Two{Nil{}, Nil{}}
    case 1n+p Con{h, t}:
      split.cons(A, h, split(A, p, t))

def pseq(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, xs: List<&2, A>, +c: C) -> List<&2, B>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      f(c, h) <> pseq(~A, ~B, ~C, ~f, t, c)

def par(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, +depth: Nat, two: Two<A>, +h: U32, +r: U32, +c: C) -> List<&2, B>:
  match depth:
    case 0n:
      Two{xl, xr} = two
      a b = pseq(~A, ~B, ~C, ~f, xl, c) pseq(~A, ~B, ~C, ~f, xr, c)
      List.append(&2, B, a, b)
    case 1n+d:
      Two{xl, xr} = two
      +hl = (h >> 1n : U32)
      +hr = (r >> 1n : U32)
      a b = par(~A, ~B, ~C, ~f, d, split(A, U32.to_nat(hl), xl), hl, (h - hl : U32), c) par(~A, ~B, ~C, ~f, d, split(A, U32.to_nat(hr), xr), hr, (r - hr : U32), c)
      List.append(&2, B, a, b)

# Parallel map over a list of known length t: 2 tasks below 64, 64 tasks at 64+.
def pmap(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, xs: List<&2, A>, +t: U32, +c: C) -> List<&2, B>:
  +h = (t >> 1n : U32)
  +d = Bool.pick(Nat, U32.is_lt(t, 64), 0n, 5n)
  par(~A, ~B, ~C, ~f, d, split(A, U32.to_nat(h), xs), h, (t - h : U32), c)

# ---------------------------------------------------------------- constructors & accessors

def Vec.from_list(+xs: List<&2, F32>) -> Vec:
  Vec{U32.from_nat(List.length(&2, F32, xs)), xs}

def Vec.from_flat.k(p: A.F32Array & U32) -> Vec:
  (a, len) = p
  Vec{len, A.to_list(a)}

def Vec.from_flat(a: A.F32Array) -> Vec:
  Vec.from_flat.k(A.length(a))

def Vec.zeros(+n: U32) -> Vec:
  Vec{n, List.replicate(F32, U32.to_nat(n), 0.0)}

def Vec.ones(+n: U32) -> Vec:
  Vec{n, List.replicate(F32, U32.to_nat(n), 1.0)}

def Vec.get(v: Vec, i: Nat) -> Maybe<&2, F32>:
  Vec{_, xs} = v
  List.get(&2, F32, xs, i)

def Mat.rows.ok(xs: List<&2, List<&2, F32>>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{r, t}:
      Bool.and(Nat.is_eq(List.length(&2, F32, r), n), Mat.rows.ok(t, n))

def Mat.rows.pick(ok: Bool, +rows: List<&2, List<&2, F32>>, +n: Nat) -> Maybe<&2, Mat>:
  match ok:
    case True{}:
      Some{Mat{U32.from_nat(List.length(&2, List<&2, F32>, rows)), U32.from_nat(n), rows}}
    case False{}:
      None{}

# None when two rows differ in length.
def Mat.from_rows(xs: List<&2, List<&2, F32>>) -> Maybe<&2, Mat>:
  match xs:
    case Nil{}:
      Some{Mat{0, 0, Nil{}}}
    case Con{+r, +t}:
      +n = List.length(&2, F32, r)
      Mat.rows.pick(Mat.rows.ok(r <> t, n), r <> t, n)

type Flat is Type:
  Flat{a: A.F32Array, rows: List<&2, List<&2, F32>>}

def Mat.flat.add(r: A.F32Array & A.F32Array, rows: List<&2, List<&2, F32>>) -> Flat:
  (a, row) = r
  Flat{a, A.to_list(row) <> rows}

def Mat.flat.go(k: Nat, st: Flat, +n: U32, +i: U32) -> List<&2, List<&2, F32>>:
  match k:
    case 0n:
      Flat{_, rows} = st
      List.reverse(&2, List<&2, F32>, rows)
    case 1n+p:
      Flat{a, rows} = st
      Mat.flat.go(p, Mat.flat.add(A.slice(a, (i * n : U32), n), rows), n, (i + 1 : U32))

# A row-major m x n array, as numpy's tofile writes it.
def Mat.from_flat(a: A.F32Array, +m: U32, +n: U32) -> Mat:
  Mat{m, n, Mat.flat.go(U32.to_nat(m), Flat{a, Nil{}}, n, 0)}

def Mat.zeros(+m: U32, +n: U32) -> Mat:
  Mat{m, n, List.replicate(List<&2, F32>, U32.to_nat(m), List.replicate(F32, U32.to_nat(n), 0.0))}

def row_unit(rem: Nat, +j: Nat, +target: Nat) -> List<&2, F32>:
  match rem:
    case 0n:
      Nil{}
    case 1n+p:
      Bool.pick(F32, Nat.is_eq(j, target), 1.0, 0.0) <> row_unit(p, 1n+j, target)

def eye_rows(rem: Nat, +i: Nat, +n: Nat) -> List<&2, List<&2, F32>>:
  match rem:
    case 0n:
      Nil{}
    case 1n+p:
      row_unit(n, 0n, i) <> eye_rows(p, 1n+i, n)

def Mat.eye(+n: U32) -> Mat:
  +nn = U32.to_nat(n)
  Mat{n, n, eye_rows(nn, 0n, nn)}

def diag_row(rem: Nat, +j: Nat, +target: Nat, +val: F32) -> List<&2, F32>:
  match rem:
    case 0n:
      Nil{}
    case 1n+p:
      Bool.pick(F32, Nat.is_eq(j, target), val, 0.0) <> diag_row(p, 1n+j, target, val)

def diag_rows(xs: List<&2, F32>, +i: Nat, +n: Nat) -> List<&2, List<&2, F32>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      diag_row(n, 0n, i, x) <> diag_rows(t, 1n+i, n)

def Mat.diag(v: Vec) -> Mat:
  Vec{+n, xs} = v
  Mat{n, n, diag_rows(xs, 0n, U32.to_nat(n))}

def row_get(mr: Maybe<&2, List<&2, F32>>, j: Nat) -> Maybe<&2, F32>:
  match mr:
    case None{}:
      None{}
    case Some{r}:
      List.get(&2, F32, r, j)

def mat_get(rows: List<&2, List<&2, F32>>, i: Nat, j: Nat) -> Maybe<&2, F32>:
  row_get(List.get(&2, List<&2, F32>, rows, i), j)

def Mat.get(a: Mat, i: Nat, j: Nat) -> Maybe<&2, F32>:
  Mat{_, _, rows} = a
  mat_get(rows, i, j)

def diag_extract.pick(mv: Maybe<&2, F32>, rest: List<&2, F32>) -> List<&2, F32>:
  match mv:
    case None{}:
      Nil{}
    case Some{v}:
      v <> rest

def diag_extract(rows: List<&2, List<&2, F32>>, +i: Nat) -> List<&2, F32>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      diag_extract.pick(List.get(&2, F32, r, i), diag_extract(t, 1n+i))

def Mat.diag_vec(a: Mat) -> Vec:
  Mat{+m, +n, rows} = a
  Vec{U32.min(m, n), diag_extract(rows, 0n)}

# ---------------------------------------------------------------- vector ops

def dot.go(xs: List<&2, F32>, ys: List<&2, F32>, +acc: F32) -> F32:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      dot.go(xt, yt, (acc + (x * y) : F32))
    case _ _:
      acc

def dot_raw(xs: List<&2, F32>, ys: List<&2, F32>) -> F32:
  dot.go(xs, ys, 0.0)

def dot.chk(ok: Bool, xs: List<&2, F32>, ys: List<&2, F32>) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      Some{dot_raw(xs, ys)}
    case False{}:
      None{}

def dot(x: Vec, y: Vec) -> Maybe<&2, F32>:
  Vec{nx, xs} = x
  Vec{ny, ys} = y
  dot.chk(U32.is_eq(nx, ny), xs, ys)

def norm1.go(xs: List<&2, F32>, +acc: F32) -> F32:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      norm1.go(t, (acc + F32.abs(x) : F32))

def norm1(x: Vec) -> F32:
  Vec{_, xs} = x
  norm1.go(xs, 0.0)

def sum_sq.go(xs: List<&2, F32>, +acc: F32) -> F32:
  match xs:
    case Nil{}:
      acc
    case Con{+x, t}:
      sum_sq.go(t, (acc + (x * x) : F32))

def norm2(x: Vec) -> F32:
  Vec{_, xs} = x
  F32.sqrt(sum_sq.go(xs, 0.0))

def vscale.go(+s: F32, xs: List<&2, F32>) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      (s * x : F32) <> vscale.go(s, t)

def vscale(+s: F32, x: Vec) -> Vec:
  Vec{n, xs} = x
  Vec{n, vscale.go(s, xs)}

def vadd.go(xs: List<&2, F32>, ys: List<&2, F32>) -> List<&2, F32>:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      (x + y : F32) <> vadd.go(xt, yt)
    case _ _:
      Nil{}

def vadd.chk(ok: Bool, n: U32, xs: List<&2, F32>, ys: List<&2, F32>) -> Maybe<&2, Vec>:
  match ok:
    case True{}:
      Some{Vec{n, vadd.go(xs, ys)}}
    case False{}:
      None{}

def vadd(x: Vec, y: Vec) -> Maybe<&2, Vec>:
  Vec{+nx, xs} = x
  Vec{ny, ys} = y
  vadd.chk(U32.is_eq(nx, ny), nx, xs, ys)

def vsub.go(xs: List<&2, F32>, ys: List<&2, F32>) -> List<&2, F32>:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      (x - y : F32) <> vsub.go(xt, yt)
    case _ _:
      Nil{}

def vsub.chk(ok: Bool, n: U32, xs: List<&2, F32>, ys: List<&2, F32>) -> Maybe<&2, Vec>:
  match ok:
    case True{}:
      Some{Vec{n, vsub.go(xs, ys)}}
    case False{}:
      None{}

def vsub(x: Vec, y: Vec) -> Maybe<&2, Vec>:
  Vec{+nx, xs} = x
  Vec{ny, ys} = y
  vsub.chk(U32.is_eq(nx, ny), nx, xs, ys)

def axpy.go(+a: F32, xs: List<&2, F32>, ys: List<&2, F32>) -> List<&2, F32>:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      ((a * x) + y : F32) <> axpy.go(a, xt, yt)
    case _ _:
      Nil{}

def axpy.chk(ok: Bool, n: U32, a: F32, xs: List<&2, F32>, ys: List<&2, F32>) -> Maybe<&2, Vec>:
  match ok:
    case True{}:
      Some{Vec{n, axpy.go(a, xs, ys)}}
    case False{}:
      None{}

def axpy(a: F32, x: Vec, y: Vec) -> Maybe<&2, Vec>:
  Vec{+nx, xs} = x
  Vec{ny, ys} = y
  axpy.chk(U32.is_eq(nx, ny), nx, a, xs, ys)

def vmul.go(xs: List<&2, F32>, ys: List<&2, F32>) -> List<&2, F32>:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      (x * y : F32) <> vmul.go(xt, yt)
    case _ _:
      Nil{}

def vmul.chk(ok: Bool, n: U32, xs: List<&2, F32>, ys: List<&2, F32>) -> Maybe<&2, Vec>:
  match ok:
    case True{}:
      Some{Vec{n, vmul.go(xs, ys)}}
    case False{}:
      None{}

def vmul(x: Vec, y: Vec) -> Maybe<&2, Vec>:
  Vec{+nx, xs} = x
  Vec{ny, ys} = y
  vmul.chk(U32.is_eq(nx, ny), nx, xs, ys)

def vdiv.go(xs: List<&2, F32>, ys: List<&2, F32>) -> List<&2, F32>:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      (x / y : F32) <> vdiv.go(xt, yt)
    case _ _:
      Nil{}

def vdiv.chk(ok: Bool, n: U32, xs: List<&2, F32>, ys: List<&2, F32>) -> Maybe<&2, Vec>:
  match ok:
    case True{}:
      Some{Vec{n, vdiv.go(xs, ys)}}
    case False{}:
      None{}

def vdiv(x: Vec, y: Vec) -> Maybe<&2, Vec>:
  Vec{+nx, xs} = x
  Vec{ny, ys} = y
  vdiv.chk(U32.is_eq(nx, ny), nx, xs, ys)

def outer.row(ys: List<&2, F32>, xi: F32) -> List<&2, F32>:
  vscale.go(xi, ys)

def outer(x: Vec, y: Vec) -> Mat:
  Vec{+m, xs} = x
  Vec{n, ys} = y
  Mat{m, n, pmap(~F32, ~List<&2, F32>, ~List<&2, F32>, ~outer.row, xs, m, ys)}

# ---------------------------------------------------------------- matrix ops

def scale.row(s: F32, r: List<&2, F32>) -> List<&2, F32>:
  vscale.go(s, r)

def scale(s: F32, a: Mat) -> Mat:
  Mat{+m, n, rows} = a
  Mat{m, n, pmap(~List<&2, F32>, ~List<&2, F32>, ~F32, ~scale.row, rows, m, s)}

def madd.rows(xs: List<&2, List<&2, F32>>, ys: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match xs ys:
    case Con{rx, tx} Con{ry, ty}:
      vadd.go(rx, ry) <> madd.rows(tx, ty)
    case _ _:
      Nil{}

def madd.chk(ok: Bool, m: U32, n: U32, xs: List<&2, List<&2, F32>>, ys: List<&2, List<&2, F32>>) -> Maybe<&2, Mat>:
  match ok:
    case True{}:
      Some{Mat{m, n, madd.rows(xs, ys)}}
    case False{}:
      None{}

def madd(a: Mat, b: Mat) -> Maybe<&2, Mat>:
  Mat{+ma, +na, ra} = a
  Mat{mb, nb, rb} = b
  madd.chk(Bool.and(U32.is_eq(ma, mb), U32.is_eq(na, nb)), ma, na, ra, rb)

def msub.rows(xs: List<&2, List<&2, F32>>, ys: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match xs ys:
    case Con{rx, tx} Con{ry, ty}:
      vsub.go(rx, ry) <> msub.rows(tx, ty)
    case _ _:
      Nil{}

def msub.chk(ok: Bool, m: U32, n: U32, xs: List<&2, List<&2, F32>>, ys: List<&2, List<&2, F32>>) -> Maybe<&2, Mat>:
  match ok:
    case True{}:
      Some{Mat{m, n, msub.rows(xs, ys)}}
    case False{}:
      None{}

def msub(a: Mat, b: Mat) -> Maybe<&2, Mat>:
  Mat{+ma, +na, ra} = a
  Mat{mb, nb, rb} = b
  msub.chk(Bool.and(U32.is_eq(ma, mb), U32.is_eq(na, nb)), ma, na, ra, rb)

def frob.rows(rows: List<&2, List<&2, F32>>, +acc: F32) -> F32:
  match rows:
    case Nil{}:
      acc
    case Con{r, t}:
      frob.rows(t, sum_sq.go(r, acc))

def frobenius(a: Mat) -> F32:
  Mat{_, _, rows} = a
  F32.sqrt(frob.rows(rows, 0.0))

def sum_list(xs: List<&2, F32>, +acc: F32) -> F32:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      sum_list(t, (acc + x : F32))

def trace.chk(ok: Bool, rows: List<&2, List<&2, F32>>) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      Some{sum_list(diag_extract(rows, 0n), 0.0)}
    case False{}:
      None{}

def trace(a: Mat) -> Maybe<&2, F32>:
  Mat{m, n, rows} = a
  trace.chk(U32.is_eq(m, n), rows)

# ---- transpose

def zip_cons(r: List<&2, F32>, cols: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match r cols:
    case Con{x, xt} Con{c, ct}:
      (x <> c) <> zip_cons(xt, ct)
    case _ _:
      Nil{}

def transpose.rows(rows: List<&2, List<&2, F32>>, +n: Nat) -> List<&2, List<&2, F32>>:
  match rows:
    case Nil{}:
      List.replicate(List<&2, F32>, n, Nil{})
    case Con{r, rs}:
      zip_cons(r, transpose.rows(rs, n))

def transpose(a: Mat) -> Mat:
  Mat{m, +n, rows} = a
  Mat{n, m, transpose.rows(rows, U32.to_nat(n))}

# ---- slicing

def clamp_len(+total: U32, +start: U32, +len: U32) -> U32:
  +avail = Bool.pick(U32, U32.is_lt(start, total), (total - start : U32), 0)
  U32.min(len, avail)

def slice_rows(a: Mat, +start: U32, +len: U32) -> Mat:
  Mat{+m, n, rows} = a
  +k = clamp_len(m, start, len)
  Mat{k, n, List.take(&2, List<&2, F32>, List.drop(&2, List<&2, F32>, rows, U32.to_nat(start)), U32.to_nat(k))}

type SliceCfg is Data:
  SliceCfg{start: Nat, len: Nat}

def slice_col.row(cfg: SliceCfg, r: List<&2, F32>) -> List<&2, F32>:
  SliceCfg{st, ln} = cfg
  List.take(&2, F32, List.drop(&2, F32, r, st), ln)

def slice_cols(a: Mat, +start: U32, +len: U32) -> Mat:
  Mat{+m, +n, rows} = a
  +k = clamp_len(n, start, len)
  Mat{m, k, pmap(~List<&2, F32>, ~List<&2, F32>, ~SliceCfg, ~slice_col.row, rows, m, SliceCfg{U32.to_nat(start), U32.to_nat(k)})}

def submatrix(a: Mat, r0: U32, rm: U32, c0: U32, cn: U32) -> Mat:
  slice_cols(slice_rows(a, r0, rm), c0, cn)

# ---- diagonal scaling

def diag_mul.rows(ds: List<&2, F32>, rows: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match ds rows:
    case Con{d, dt} Con{r, rt}:
      vscale.go(d, r) <> diag_mul.rows(dt, rt)
    case _ _:
      Nil{}

def diag_mul.chk(ok: Bool, m: U32, n: U32, ds: List<&2, F32>, rows: List<&2, List<&2, F32>>) -> Maybe<&2, Mat>:
  match ok:
    case True{}:
      Some{Mat{m, n, diag_mul.rows(ds, rows)}}
    case False{}:
      None{}

# diag(d) * A: scales row i of A by d_i.
def diag_mul(d: Vec, a: Mat) -> Maybe<&2, Mat>:
  Vec{nd, ds} = d
  Mat{+m, n, rows} = a
  diag_mul.chk(U32.is_eq(nd, m), m, n, ds, rows)

def mul_diag.row(ds: List<&2, F32>, r: List<&2, F32>) -> List<&2, F32>:
  vmul.go(r, ds)

def mul_diag.chk(ok: Bool, +m: U32, n: U32, rows: List<&2, List<&2, F32>>, ds: List<&2, F32>) -> Maybe<&2, Mat>:
  match ok:
    case True{}:
      Some{Mat{m, n, pmap(~List<&2, F32>, ~List<&2, F32>, ~List<&2, F32>, ~mul_diag.row, rows, m, ds)}}
    case False{}:
      None{}

# A * diag(d): scales column j of A by d_j.
def mul_diag(a: Mat, d: Vec) -> Maybe<&2, Mat>:
  Mat{m, +n, rows} = a
  Vec{nd, ds} = d
  mul_diag.chk(U32.is_eq(n, nd), m, n, rows, ds)

# ---------------------------------------------------------------- products

def matvec.row(x: List<&2, F32>, r: List<&2, F32>) -> F32:
  dot_raw(r, x)

def matvec.chk(ok: Bool, +m: U32, rows: List<&2, List<&2, F32>>, x: List<&2, F32>) -> Maybe<&2, Vec>:
  match ok:
    case True{}:
      Some{Vec{m, pmap(~List<&2, F32>, ~F32, ~List<&2, F32>, ~matvec.row, rows, m, x)}}
    case False{}:
      None{}

def matvec(a: Mat, x: Vec) -> Maybe<&2, Vec>:
  Mat{m, n, rows} = a
  Vec{nx, xs} = x
  matvec.chk(U32.is_eq(n, nx), m, rows, xs)

def matmul.dots(+r: List<&2, F32>, cols: List<&2, List<&2, F32>>) -> List<&2, F32>:
  match cols:
    case Nil{}:
      Nil{}
    case Con{c, ct}:
      dot_raw(r, c) <> matmul.dots(r, ct)

def matmul.row(bcols: List<&2, List<&2, F32>>, r: List<&2, F32>) -> List<&2, F32>:
  matmul.dots(r, bcols)

def matmul.chk(ok: Bool, +ma: U32, +nb: U32, ra: List<&2, List<&2, F32>>, rb: List<&2, List<&2, F32>>) -> Maybe<&2, Mat>:
  match ok:
    case True{}:
      +bcols = transpose.rows(rb, U32.to_nat(nb))
      Some{Mat{ma, nb, pmap(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~matmul.row, ra, ma, bcols)}}
    case False{}:
      None{}

def matmul(a: Mat, b: Mat) -> Maybe<&2, Mat>:
  Mat{ma, na, ra} = a
  Mat{mb, nb, rb} = b
  matmul.chk(U32.is_eq(na, mb), ma, nb, ra, rb)

# Turn an upper-triangular row list [[g00..g0(n-1)], [g11..g1(n-1)], ...] into
# the full symmetric n x n matrix by prepending each off-diagonal row as a column.
def mirror_upper(upper: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match upper:
    case Nil{}:
      Nil{}
    case Con{Nil{}, sub}:
      Nil{} <> mirror_upper(sub)
    case Con{Con{d, +rest}, sub}:
      (d <> rest) <> zip_cons(rest, mirror_upper(sub))

# Quadratic form x^T A x; None unless A is n x n and len(x) == n.
def quad_form.k(ax: Maybe<&2, Vec>, x: Vec) -> Maybe<&2, F32>:
  match ax:
    case None{}:
      None{}
    case Some{v}:
      dot(x, v)

def quad_form.chk(ok: Bool, a: Mat, +x: Vec) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      quad_form.k(matvec(a, x), x)
    case False{}:
      None{}

def quad_form(x: Vec, a: Mat) -> Maybe<&2, F32>:
  Vec{+nx, xs} = x
  Mat{+m, +n, rows} = a
  quad_form.chk(Bool.and(U32.is_eq(m, n), U32.is_eq(n, nx)), Mat{m, n, rows}, Vec{nx, xs})

# ---------------------------------------------------------------- flat Array helpers

def arr_depth.step(rem: Nat, done: Bool, +d: Nat, +cap: U32, +n: U32) -> Nat:
  match rem done:
    case _ True{}:
      d
    case 0n False{}:
      d
    case 1n+p False{}:
      +cap2 = (cap << 1n : U32)
      arr_depth.step(p, U32.is_ge(cap2, n), 1n+d, cap2, n)

# Smallest d such that 2^d >= max(1, n).
def arr_depth(+n: U32) -> Nat:
  arr_depth.step(30n, U32.is_ge(1, n), 0n, 1, n)

def fill_list(xs: List<&2, F32>, a: Array<F32>, +idx: U32) -> Array<F32>:
  match xs:
    case Nil{}:
      a
    case Con{x, t}:
      fill_list(t, Array.set(F32, a, idx, x), (idx + 1 : U32))

def vec_to_arr(xs: List<&2, F32>, +n: U32) -> Array<F32>:
  fill_list(xs, Array.new(F32, arr_depth(n), 0.0), 0)

def fill_rows(rows: List<&2, List<&2, F32>>, a: Array<F32>, +row_off: U32, +n: U32) -> Array<F32>:
  match rows:
    case Nil{}:
      a
    case Con{r, t}:
      fill_rows(t, fill_list(r, a, row_off), (row_off + n : U32), n)

def mat_to_arr(rows: List<&2, List<&2, F32>>, +m: U32, +n: U32) -> Array<F32>:
  fill_rows(rows, Array.new(F32, arr_depth((m * n : U32)), 0.0), 0, n)

# Prepends v and then a[base + 0..rem-1] onto acc (parameter r lets proofs
# destructure Array<F32> linearly without mutual recursion).
def read_down.loop(+rem: Nat, r: Array<F32> & F32, acc: List<&2, F32>, +base: U32) -> Array<F32> & List<&2, F32>:
  match rem:
    case 0n:
      (a, v) = r
      (a, v <> acc)
    case 1n+p:
      (a, v) = r
      read_down.loop(p, Array.get(F32, a, (base + U32.from_nat(p) : U32)), v <> acc, base)

# Prepends a[base + 0..rem-1] onto acc.
def read_down(+rem: Nat, a: Array<F32>, acc: List<&2, F32>, +base: U32) -> Array<F32> & List<&2, F32>:
  match rem:
    case 0n:
      (a, acc)
    case 1n+p:
      read_down.loop(p, Array.get(F32, a, (base + U32.from_nat(p) : U32)), acc, base)

def arr_to_list.fin(r: Array<F32> & List<&2, F32>) -> List<&2, F32>:
  (_, xs) = r
  xs

def arr_to_list(a: Array<F32>, +n: U32) -> List<&2, F32>:
  arr_to_list.fin(read_down(U32.to_nat(n), a, Nil{}, 0))

# ---- Provable lower-triangular extractor
# Reads entries j = 0..min(i, n-1) from a[i * n + j] onto a tail of
# (n - min(i + 1, n)) literal 0.0s. Zero reversals, zero appends, and lets
# PROOF.bend prove exact shape and exact 0.0 strictly above the diagonal.

def lower_row(a: Array<F32>, +i: Nat, +n: Nat, +row_off: U32) -> Array<F32> & List<&2, F32>:
  +take_n = Nat.min(1n+i, n)
  +pad_n = Nat.sub(n, take_n)
  read_down(take_n, a, List.replicate(F32, pad_n, 0.0), row_off)

def lower_rows.loop(+rem: Nat, r: Array<F32> & List<&2, F32>, acc: List<&2, List<&2, F32>>, +n: Nat, +nu: U32) -> Array<F32> & List<&2, List<&2, F32>>:
  match rem:
    case 0n:
      (a, row) = r
      (a, row <> acc)
    case 1n+p:
      (a, row) = r
      lower_rows.loop(p, lower_row(a, p, n, (U32.from_nat(p) * nu : U32)), row <> acc, n, nu)

def lower_rows.go(+rem: Nat, a: Array<F32>, acc: List<&2, List<&2, F32>>, +n: Nat, +nu: U32) -> Array<F32> & List<&2, List<&2, F32>>:
  match rem:
    case 0n:
      (a, acc)
    case 1n+p:
      lower_rows.loop(p, lower_row(a, p, n, (U32.from_nat(p) * nu : U32)), acc, n, nu)

def arr_lower_rows.fin(r: Array<F32> & List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  (_, rows) = r
  rows

def arr_lower_rows(a: Array<F32>, +n: U32) -> List<&2, List<&2, F32>>:
  +nn = U32.to_nat(n)
  arr_lower_rows.fin(lower_rows.go(nn, a, Nil{}, nn, n))

# ---------------------------------------------------------------- Cholesky

type CSt is Type:
  CSt{a: Array<F32>, l: Array<F32>, ok: Bool}

def arr_dot2(p: Array<F32> & F32, +v1: F32, +acc: F32) -> Array<F32> & F32:
  (arr, v2) = p
  (arr, (acc + (v1 * v2) : F32))

def arr_dot1(p: Array<F32> & F32, +o2: U32, +acc: F32) -> Array<F32> & F32:
  (arr, v1) = p
  arr_dot2(Array.get(F32, arr, o2), v1, acc)

def arr_dot(rem: Nat, st: Array<F32> & F32, +o1: U32, +o2: U32) -> Array<F32> & F32:
  match rem:
    case 0n:
      st
    case 1n+p:
      (arr, acc) = st
      arr_dot(p, arr_dot1(Array.get(F32, arr, o1), o2, acc), (o1 + 1 : U32), (o2 + 1 : U32))

def chol.set_diag(pos: Bool, a: Array<F32>, l: Array<F32>, +idx: U32, +val: F32) -> CSt:
  match pos:
    case True{}:
      CSt{a, Array.set(F32, l, idx, F32.sqrt(val)), True{}}
    case False{}:
      CSt{a, l, False{}}

def chol.set_off(p: Array<F32> & F32, a: Array<F32>, +aij: F32, +s: F32, +idx: U32) -> CSt:
  (l, ljj) = p
  CSt{a, Array.set(F32, l, idx, ((aij - s) / ljj : F32)), True{}}

def chol.cell_branch(diag: Bool, a: Array<F32>, l: Array<F32>, +aij: F32, +s: F32, +i: U32, +j: U32, +n: U32) -> CSt:
  match diag:
    case True{}:
      +val = (aij - s : F32)
      chol.set_diag(F32.is_gt(val, 0.0), a, l, ((i * n) + j : U32), val)
    case False{}:
      chol.set_off(Array.get(F32, l, ((j * n) + j : U32)), a, aij, s, ((i * n) + j : U32))

def chol.cell_a(pa: Array<F32> & F32, pl: Array<F32> & F32, +i: U32, +j: U32, +n: U32) -> CSt:
  (a, aij) = pa
  (l, s) = pl
  chol.cell_branch(U32.is_eq(i, j), a, l, aij, s, i, j, n)

def chol.j(rem: Nat, st: CSt, +i: U32, +j: U32, +n: U32) -> CSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      match st:
        case CSt{a, l, False{}}:
          CSt{a, l, False{}}
        case CSt{a, l, True{}}:
          st1 = chol.cell_a(Array.get(F32, a, ((i * n) + j : U32)), arr_dot(U32.to_nat(j), (l, 0.0), (i * n : U32), (j * n : U32)), i, j, n)
          chol.j(p, st1, i, (j + 1 : U32), n)

def chol.i(rem: Nat, st: CSt, +i: U32, +n: U32) -> CSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      match st:
        case CSt{a, l, False{}}:
          CSt{a, l, False{}}
        case CSt{a, l, True{}}:
          chol.i(p, chol.j(U32.to_nat((i + 1 : U32)), CSt{a, l, True{}}, i, 0, n), (i + 1 : U32), n)

def chol.fin(st: CSt, +n: U32) -> Maybe<&2, Mat>:
  match st:
    case CSt{_, _, False{}}:
      None{}
    case CSt{_, l, True{}}:
      Some{Mat{n, n, arr_lower_rows(l, n)}}

def chol.run(+n: U32, rows: List<&2, List<&2, F32>>) -> CSt:
  +d = arr_depth((n * n : U32))
  chol.i(U32.to_nat(n), CSt{mat_to_arr(rows, n, n), Array.new(F32, d, 0.0), True{}}, 0, n)

def chol.chk(ok: Bool, +n: U32, rows: List<&2, List<&2, F32>>) -> Maybe<&2, Mat>:
  match ok:
    case True{}:
      chol.fin(chol.run(n, rows), n)
    case False{}:
      None{}

# Lower-triangular Cholesky factor L such that A = L L^T; None if not square or not SPD.
def cholesky(a: Mat) -> Maybe<&2, Mat>:
  Mat{m, +n, rows} = a
  chol.chk(U32.is_eq(m, n), n, rows)

# ---------------------------------------------------------------- triangular solves

type TriSt is Type:
  TriSt{m: Array<F32>, x: Array<F32>, ok: Bool}

def is_nonzero_fin(+v: F32) -> Bool:
  Bool.and(F32.is_ne(v, 0.0), F32.is_eq(v, v))

# Sum_{j=0..count-1} M[m_off + j * m_stride] * x[x_off + j]
type DotMX is Type:
  DotMX{m: Array<F32>, x: Array<F32>, acc: F32}

def dot_mx2(px: Array<F32> & F32, m: Array<F32>, +mv: F32, +acc: F32) -> DotMX:
  (x, xv) = px
  DotMX{m, x, (acc + (mv * xv) : F32)}

def dot_mx1(pm: Array<F32> & F32, x: Array<F32>, +xi: U32, +acc: F32) -> DotMX:
  (m, mv) = pm
  dot_mx2(Array.get(F32, x, xi), m, mv, acc)

def dot_mx(rem: Nat, st: DotMX, +mo: U32, +ms: U32, +xo: U32) -> DotMX:
  match rem:
    case 0n:
      st
    case 1n+p:
      DotMX{m, x, acc} = st
      dot_mx(p, dot_mx1(Array.get(F32, m, mo), x, xo, acc), (mo + ms : U32), ms, (xo + 1 : U32))

# ---- Column-major loaders (plain & weighted)

def fill_row_cm(r: List<&2, F32>, a: Array<F32>, +idx: U32, +stride: U32) -> Array<F32>:
  match r:
    case Nil{}:
      a
    case Con{x, t}:
      fill_row_cm(t, Array.set(F32, a, idx, x), (idx + stride : U32), stride)

def fill_mat_cm(rows: List<&2, List<&2, F32>>, a: Array<F32>, +row_i: U32, +m: U32) -> Array<F32>:
  match rows:
    case Nil{}:
      a
    case Con{r, t}:
      fill_mat_cm(t, fill_row_cm(r, a, row_i, m), (row_i + 1 : U32), m)

def mat_to_colmajor(rows: List<&2, List<&2, F32>>, +m: U32, +n: U32) -> Array<F32>:
  fill_mat_cm(rows, Array.new(F32, arr_depth((m * n : U32)), 0.0), 0, m)

def fill_row_cm_w(r: List<&2, F32>, a: Array<F32>, +w: F32, +idx: U32, +stride: U32) -> Array<F32>:
  match r:
    case Nil{}:
      a
    case Con{x, t}:
      fill_row_cm_w(t, Array.set(F32, a, idx, (w * x : F32)), w, (idx + stride : U32), stride)

def fill_mat_cm_w(rows: List<&2, List<&2, F32>>, ws: List<&2, F32>, a: Array<F32>, +row_i: U32, +m: U32) -> Array<F32>:
  match rows ws:
    case Con{r, rt} Con{w, wt}:
      fill_mat_cm_w(rt, wt, fill_row_cm_w(r, a, w, row_i, m), (row_i + 1 : U32), m)
    case _ _:
      a

def mat_to_colmajor_w(rows: List<&2, List<&2, F32>>, ws: List<&2, F32>, +m: U32, +n: U32) -> Array<F32>:
  fill_mat_cm_w(rows, ws, Array.new(F32, arr_depth((m * n : U32)), 0.0), 0, m)

def fill_list_w(xs: List<&2, F32>, ws: List<&2, F32>, a: Array<F32>, +idx: U32) -> Array<F32>:
  match xs ws:
    case Con{x, xt} Con{w, wt}:
      fill_list_w(xt, wt, Array.set(F32, a, idx, (w * x : F32)), (idx + 1 : U32))
    case _ _:
      a

def vec_to_arr_w(xs: List<&2, F32>, ws: List<&2, F32>, +n: U32) -> Array<F32>:
  fill_list_w(xs, ws, Array.new(F32, arr_depth(n), 0.0), 0)

# ---- Transpose-free matvec_t (A^T x) via single row-wise accumulation

def matvec_t.step(p: Array<F32> & F32, +rv: F32, +xi: F32, +j: U32) -> Array<F32>:
  (y, cur) = p
  Array.set(F32, y, j, (cur + (rv * xi) : F32))

def matvec_t.row(r: List<&2, F32>, y: Array<F32>, +xi: F32, +j: U32) -> Array<F32>:
  match r:
    case Nil{}:
      y
    case Con{rv, rt}:
      matvec_t.row(rt, matvec_t.step(Array.get(F32, y, j), rv, xi, j), xi, (j + 1 : U32))

def matvec_t.go(rows: List<&2, List<&2, F32>>, xs: List<&2, F32>, y: Array<F32>) -> Array<F32>:
  match rows xs:
    case Con{r, rt} Con{x, xt}:
      matvec_t.go(rt, xt, matvec_t.row(r, y, x, 0))
    case _ _:
      y

def matvec_t.chk(ok: Bool, +n: U32, rows: List<&2, List<&2, F32>>, xs: List<&2, F32>) -> Maybe<&2, Vec>:
  match ok:
    case True{}:
      Some{Vec{n, arr_to_list(matvec_t.go(rows, xs, Array.new(F32, arr_depth(n), 0.0)), n)}}
    case False{}:
      None{}

def matvec_t(a: Mat, x: Vec) -> Maybe<&2, Vec>:
  Mat{m, +n, rows} = a
  Vec{nx, xs} = x
  matvec_t.chk(U32.is_eq(m, nx), n, rows, xs)

# ---- Fast, provably symmetric Gram matrices A^T A and A^T diag(w) A
# Computes the upper triangle (j >= i) on flat column-major Array<F32>, extracts
# it as rows of lengths n, n-1, ..., 1 via arr_upper_tri, and mirrors into the
# lower triangle via mirror_upper (preserving exact structural symmetry proofs).

def upper_tri.loop(+rem: Nat, r: Array<F32> & List<&2, F32>, acc: List<&2, List<&2, F32>>, +n: Nat, +nu: U32) -> Array<F32> & List<&2, List<&2, F32>>:
  match rem:
    case 0n:
      (a, row) = r
      (a, row <> acc)
    case 1n+p:
      (a, row) = r
      +pu = U32.from_nat(p)
      upper_tri.loop(p, read_down(Nat.sub(n, p), a, Nil{}, ((pu * nu) + pu : U32)), row <> acc, n, nu)

def upper_tri.go(+rem: Nat, a: Array<F32>, acc: List<&2, List<&2, F32>>, +n: Nat, +nu: U32) -> Array<F32> & List<&2, List<&2, F32>>:
  match rem:
    case 0n:
      (a, acc)
    case 1n+p:
      +pu = U32.from_nat(p)
      upper_tri.loop(p, read_down(Nat.sub(n, p), a, Nil{}, ((pu * nu) + pu : U32)), acc, n, nu)

def arr_upper_tri(a: Array<F32>, +n: U32) -> List<&2, List<&2, F32>>:
  +nn = U32.to_nat(n)
  arr_lower_rows.fin(upper_tri.go(nn, a, Nil{}, nn, n))

type GramSt is Type:
  GramSt{a: Array<F32>, g: Array<F32>}

def gram_arr.set(r: Array<F32> & F32, g: Array<F32>, +idx: U32) -> GramSt:
  (a, val) = r
  GramSt{a, Array.set(F32, g, idx, val)}

def gram_arr.j(rem: Nat, st: GramSt, +i: U32, +j: U32, +m: U32, +mm: Nat, +n: U32) -> GramSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      GramSt{a, g} = st
      st1 = gram_arr.set(arr_dot(mm, (a, 0.0), (i * m : U32), (j * m : U32)), g, ((i * n) + j : U32))
      gram_arr.j(p, st1, i, (j + 1 : U32), m, mm, n)

def gram_arr.i(rem: Nat, st: GramSt, +i: U32, +m: U32, +mm: Nat, +n: U32) -> GramSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      gram_arr.i(p, gram_arr.j(U32.to_nat((n - i : U32)), st, i, i, m, mm, n), (i + 1 : U32), m, mm, n)

def gram_arr.fin(st: GramSt) -> Array<F32>:
  GramSt{_, g} = st
  g

def gram_arr(rows: List<&2, List<&2, F32>>, +m: U32, +n: U32) -> Array<F32>:
  a = mat_to_colmajor(rows, m, n)
  g0 = Array.new(F32, arr_depth((n * n : U32)), 0.0)
  gram_arr.fin(gram_arr.i(U32.to_nat(n), GramSt{a, g0}, 0, m, U32.to_nat(m), n))

def gram(a: Mat) -> Mat:
  Mat{+m, +n, rows} = a
  Mat{n, n, mirror_upper(arr_upper_tri(gram_arr(rows, m, n), n))}

type WGramSt is Type:
  WGramSt{a: Array<F32>, wa: Array<F32>, g: Array<F32>}

def wgram_arr.set(dm: DotMX, g: Array<F32>, +idx: U32) -> WGramSt:
  DotMX{a, wa, val} = dm
  WGramSt{a, wa, Array.set(F32, g, idx, val)}

def wgram_arr.j(rem: Nat, st: WGramSt, +i: U32, +j: U32, +m: U32, +mm: Nat, +n: U32) -> WGramSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      WGramSt{a, wa, g} = st
      st1 = wgram_arr.set(dot_mx(mm, DotMX{a, wa, 0.0}, (i * m : U32), 1, (j * m : U32)), g, ((i * n) + j : U32))
      wgram_arr.j(p, st1, i, (j + 1 : U32), m, mm, n)

def wgram_arr.i(rem: Nat, st: WGramSt, +i: U32, +m: U32, +mm: Nat, +n: U32) -> WGramSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      wgram_arr.i(p, wgram_arr.j(U32.to_nat((n - i : U32)), st, i, i, m, mm, n), (i + 1 : U32), m, mm, n)

def wgram_arr.fin(st: WGramSt) -> Array<F32>:
  WGramSt{_, _, g} = st
  g

def wgram_arr(+rows: List<&2, List<&2, F32>>, ws: List<&2, F32>, +m: U32, +n: U32) -> Array<F32>:
  a = mat_to_colmajor(rows, m, n)
  wa = mat_to_colmajor_w(rows, ws, m, n)
  g0 = Array.new(F32, arr_depth((n * n : U32)), 0.0)
  wgram_arr.fin(wgram_arr.i(U32.to_nat(n), WGramSt{a, wa, g0}, 0, m, U32.to_nat(m), n))

def wgram.chk(ok: Bool, +m: U32, +n: U32, rows: List<&2, List<&2, F32>>, ws: List<&2, F32>) -> Maybe<&2, Mat>:
  match ok:
    case True{}:
      Some{Mat{n, n, mirror_upper(arr_upper_tri(wgram_arr(rows, ws, m, n), n))}}
    case False{}:
      None{}

# Weighted Gram matrix A^T diag(w) A; None if len(w) != m.
def wgram(a: Mat, w: Vec) -> Maybe<&2, Mat>:
  Mat{+m, n, rows} = a
  Vec{nw, ws} = w
  wgram.chk(U32.is_eq(m, nw), m, n, rows, ws)

def tri_set_ok(ok: Bool, m: Array<F32>, x: Array<F32>, +i: U32, +bi: F32, +s: F32, +d: F32) -> TriSt:
  match ok:
    case True{}:
      TriSt{m, Array.set(F32, x, i, ((bi - s) / d : F32)), True{}}
    case False{}:
      TriSt{m, x, False{}}

def tri_step_b(px: Array<F32> & F32, m: Array<F32>, +i: U32, +s: F32, +d: F32) -> TriSt:
  (x, bi) = px
  tri_set_ok(is_nonzero_fin(d), m, x, i, bi, s, d)

def tri_step_d(pm: Array<F32> & F32, x: Array<F32>, +i: U32, +s: F32) -> TriSt:
  (m, d) = pm
  tri_step_b(Array.get(F32, x, i), m, i, s, d)

def tri_step_dot(dm: DotMX, +i: U32, +n: U32) -> TriSt:
  DotMX{m1, x1, s} = dm
  tri_step_d(Array.get(F32, m1, ((i * n) + i : U32)), x1, i, s)

# Forward substitution L x = b (in place on x, initialized to b).
def solve_l.go(rem: Nat, st: TriSt, +i: U32, +n: U32) -> TriSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      match st:
        case TriSt{m, x, False{}}:
          TriSt{m, x, False{}}
        case TriSt{m, x, True{}}:
          st1 = tri_step_dot(dot_mx(U32.to_nat(i), DotMX{m, x, 0.0}, (i * n : U32), 1, 0), i, n)
          solve_l.go(p, st1, (i + 1 : U32), n)

# Backward substitution U x = b (in place on x, initialized to b).
def solve_u.go(+rem: Nat, st: TriSt, +n: U32) -> TriSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      match st:
        case TriSt{m, x, False{}}:
          TriSt{m, x, False{}}
        case TriSt{m, x, True{}}:
          +i = U32.from_nat(p)
          +i1 = (i + 1 : U32)
          st1 = tri_step_dot(dot_mx(U32.to_nat((n - i1 : U32)), DotMX{m, x, 0.0}, ((i * n) + i1 : U32), 1, i1), i, n)
          solve_u.go(p, st1, n)

# Backward substitution L^T x = b directly from lower-triangular L (stride = n).
def solve_lt.go(+rem: Nat, st: TriSt, +n: U32) -> TriSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      match st:
        case TriSt{m, x, False{}}:
          TriSt{m, x, False{}}
        case TriSt{m, x, True{}}:
          +i = U32.from_nat(p)
          +i1 = (i + 1 : U32)
          st1 = tri_step_dot(dot_mx(U32.to_nat((n - i1 : U32)), DotMX{m, x, 0.0}, ((i1 * n) + i : U32), n, i1), i, n)
          solve_lt.go(p, st1, n)

def tri.fin_vec(st: TriSt, +n: U32) -> Maybe<&2, Vec>:
  match st:
    case TriSt{_, _, False{}}:
      None{}
    case TriSt{_, x, True{}}:
      Some{Vec{n, arr_to_list(x, n)}}

def solve_lower.chk(ok: Bool, +n: U32, lrows: List<&2, List<&2, F32>>, bs: List<&2, F32>) -> Maybe<&2, Vec>:
  match ok:
    case True{}:
      tri.fin_vec(solve_l.go(U32.to_nat(n), TriSt{mat_to_arr(lrows, n, n), vec_to_arr(bs, n), True{}}, 0, n), n)
    case False{}:
      None{}

def solve_lower(l: Mat, b: Vec) -> Maybe<&2, Vec>:
  Mat{lm, +ln, lrows} = l
  Vec{nb, bs} = b
  solve_lower.chk(Bool.and(U32.is_eq(lm, ln), U32.is_eq(ln, nb)), ln, lrows, bs)

def solve_upper.chk(ok: Bool, +n: U32, urows: List<&2, List<&2, F32>>, bs: List<&2, F32>) -> Maybe<&2, Vec>:
  match ok:
    case True{}:
      tri.fin_vec(solve_u.go(U32.to_nat(n), TriSt{mat_to_arr(urows, n, n), vec_to_arr(bs, n), True{}}, n), n)
    case False{}:
      None{}

def solve_upper(u: Mat, b: Vec) -> Maybe<&2, Vec>:
  Mat{um, +un, urows} = u
  Vec{nb, bs} = b
  solve_upper.chk(Bool.and(U32.is_eq(um, un), U32.is_eq(un, nb)), un, urows, bs)

# Solve (L L^T) x = b given Cholesky factor L.
def chol_solve_arr.k(st1: TriSt, +n: U32) -> TriSt:
  match st1:
    case TriSt{m1, x1, False{}}:
      TriSt{m1, x1, False{}}
    case TriSt{m1, x1, True{}}:
      solve_lt.go(U32.to_nat(n), TriSt{m1, x1, True{}}, n)

def chol_solve_arr(l_arr: Array<F32>, x_arr: Array<F32>, +n: U32) -> TriSt:
  chol_solve_arr.k(solve_l.go(U32.to_nat(n), TriSt{l_arr, x_arr, True{}}, 0, n), n)

def cholesky_solve.chk(ok: Bool, +n: U32, lrows: List<&2, List<&2, F32>>, bs: List<&2, F32>) -> Maybe<&2, Vec>:
  match ok:
    case True{}:
      tri.fin_vec(chol_solve_arr(mat_to_arr(lrows, n, n), vec_to_arr(bs, n), n), n)
    case False{}:
      None{}

def cholesky_solve(l: Mat, b: Vec) -> Maybe<&2, Vec>:
  Mat{lm, +ln, lrows} = l
  Vec{nb, bs} = b
  cholesky_solve.chk(Bool.and(U32.is_eq(lm, ln), U32.is_eq(ln, nb)), ln, lrows, bs)

# Multi-RHS triangular & Cholesky solves: mode 0 = L, 1 = U, 2 = L L^T.
type MultiSt is Type:
  MultiSt{m: Array<F32>, cols: List<&2, List<&2, F32>>, ok: Bool}

def solve_mode.hi(is_u: Bool, m: Array<F32>, x: Array<F32>, +n: U32) -> TriSt:
  match is_u:
    case True{}:
      solve_u.go(U32.to_nat(n), TriSt{m, x, True{}}, n)
    case False{}:
      chol_solve_arr(m, x, n)

def solve_mode.go(is_l: Bool, is_u: Bool, m: Array<F32>, x: Array<F32>, +n: U32) -> TriSt:
  match is_l:
    case True{}:
      solve_l.go(U32.to_nat(n), TriSt{m, x, True{}}, 0, n)
    case False{}:
      solve_mode.hi(is_u, m, x, n)

def multi_push(st: TriSt, cols: List<&2, List<&2, F32>>, +n: U32) -> MultiSt:
  match st:
    case TriSt{m, _, False{}}:
      MultiSt{m, cols, False{}}
    case TriSt{m, x, True{}}:
      MultiSt{m, arr_to_list(x, n) <> cols, True{}}

def solve_cols(bcols: List<&2, List<&2, F32>>, st: MultiSt, +mode: U32, +n: U32) -> MultiSt:
  match bcols:
    case Nil{}:
      st
    case Con{bc, rest}:
      match st:
        case MultiSt{m, acc, False{}}:
          MultiSt{m, acc, False{}}
        case MultiSt{m, acc, True{}}:
          st1 = multi_push(solve_mode.go(U32.is_eq(mode, 0), U32.is_eq(mode, 1), m, vec_to_arr(bc, n), n), acc, n)
          solve_cols(rest, st1, mode, n)

def multi.fin(st: MultiSt, +n: U32, +k: U32) -> Maybe<&2, Mat>:
  match st:
    case MultiSt{_, _, False{}}:
      None{}
    case MultiSt{_, rev_cols, True{}}:
      Some{Mat{n, k, transpose.rows(List.reverse(&2, List<&2, F32>, rev_cols), U32.to_nat(n))}}

def solve_mat.chk(ok: Bool, +mode: U32, +n: U32, +k: U32, mrows: List<&2, List<&2, F32>>, brows: List<&2, List<&2, F32>>) -> Maybe<&2, Mat>:
  match ok:
    case True{}:
      bcols = transpose.rows(brows, U32.to_nat(k))
      multi.fin(solve_cols(bcols, MultiSt{mat_to_arr(mrows, n, n), Nil{}, True{}}, mode, n), n, k)
    case False{}:
      None{}

def solve_lower_mat(l: Mat, b: Mat) -> Maybe<&2, Mat>:
  Mat{lm, +ln, lrows} = l
  Mat{bm, bn, brows} = b
  solve_mat.chk(Bool.and(U32.is_eq(lm, ln), U32.is_eq(ln, bm)), 0, ln, bn, lrows, brows)

def solve_upper_mat(u: Mat, b: Mat) -> Maybe<&2, Mat>:
  Mat{um, +un, urows} = u
  Mat{bm, bn, brows} = b
  solve_mat.chk(Bool.and(U32.is_eq(um, un), U32.is_eq(un, bm)), 1, un, bn, urows, brows)

def cholesky_solve_mat(l: Mat, b: Mat) -> Maybe<&2, Mat>:
  Mat{lm, +ln, lrows} = l
  Mat{bm, bn, brows} = b
  solve_mat.chk(Bool.and(U32.is_eq(lm, ln), U32.is_eq(ln, bm)), 2, ln, bn, lrows, brows)

# ---- logdet from Cholesky factor L: 2 * sum_i log(L_ii)

def log_pos.step(pos: Bool, +x: F32, rest: Maybe<&2, F32>) -> Maybe<&2, F32>:
  match pos rest:
    case True{} Some{s}:
      Some{(F32.log(x) + s : F32)}
    case _ _:
      None{}

def sum_log_pos(xs: List<&2, F32>) -> Maybe<&2, F32>:
  match xs:
    case Nil{}:
      Some{0.0}
    case Con{+x, t}:
      log_pos.step(F32.is_gt(x, 0.0), x, sum_log_pos(t))

def scale_maybe(s: F32, mv: Maybe<&2, F32>) -> Maybe<&2, F32>:
  match mv:
    case None{}:
      None{}
    case Some{v}:
      Some{(s * v : F32)}

def cholesky_logdet.chk(ok: Bool, rows: List<&2, List<&2, F32>>) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      scale_maybe(2.0, sum_log_pos(diag_extract(rows, 0n)))
    case False{}:
      None{}

def cholesky_logdet(l: Mat) -> Maybe<&2, F32>:
  Mat{m, n, rows} = l
  cholesky_logdet.chk(U32.is_eq(m, n), rows)

# ---------------------------------------------------------------- Woodbury & Determinant Lemma
# Uses the inverse-free Cholesky form for D + U M U^T (M = L_m L_m^T, D = diag(d), d > 0):
#   G = U^T D^-1 U
#   C = I_K + L_m^T G L_m  (always SPD with eigenvalues >= 1, avoids inverting M)
#   (D + U M U^T)^-1 b = D^-1 b - D^-1 (U (L_m (C^-1 (L_m^T (U^T (D^-1 b))))))
#   log det(D + U M U^T) = sum log(d_i) + log det(C)

def inv_pos.step(pos: Bool, +x: F32, rest: Maybe<&2, List<&2, F32>>) -> Maybe<&2, List<&2, F32>>:
  match pos rest:
    case True{} Some{xs}:
      Some{(1.0 / x : F32) <> xs}
    case _ _:
      None{}

def inv_pos_list(xs: List<&2, F32>) -> Maybe<&2, List<&2, F32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case Con{+x, t}:
      inv_pos.step(F32.is_gt(x, 0.0), x, inv_pos_list(t))

type MatPair is Data:
  MatPair{a: Mat, b: Mat}

def woodbury_core.k(+lm: Mat, +k: U32, g: Maybe<&2, Mat>) -> Maybe<&2, MatPair>:
  match g:
    case None{}:
      None{}
    case Some{gm}:
      +lt = transpose(lm)
      do Maybe<&2, MatPair>:
        t1 : Mat <- matmul(lt, gm)
        t2 : Mat <- matmul(t1, lm)
        c : Mat <- madd(Mat.eye(k), t2)
        lc : Mat <- cholesky(c)
        return MatPair{lm, lc}

def woodbury_core(d_inv: Vec, u: Mat, m: Mat, +k: U32) -> Maybe<&2, MatPair>:
  do Maybe<&2, MatPair>:
    +lm : Mat <- cholesky(m)
    woodbury_core.k(lm, k, wgram(u, d_inv))

def woodbury_solve.run(+d_inv: Vec, +u: Mat, +b: Vec, pair: MatPair) -> Maybe<&2, Vec>:
  MatPair{+lm, lc} = pair
  do Maybe<&2, Vec>:
    +d_inv_b : Vec <- vmul(d_inv, b)
    v : Vec <- matvec_t(u, d_inv_b)
    y : Vec <- matvec_t(lm, v)
    z : Vec <- cholesky_solve(lc, y)
    q : Vec <- matvec(lm, z)
    uq : Vec <- matvec(u, q)
    corr : Vec <- vmul(d_inv, uq)
    vsub(d_inv_b, corr)

def woodbury_solve.inv(d_inv_l: Maybe<&2, List<&2, F32>>, +n: U32, +k: U32, +u: Mat, m: Mat, b: Vec) -> Maybe<&2, Vec>:
  match d_inv_l:
    case None{}:
      None{}
    case Some{di}:
      +d_inv = {Vec{n, di} : Vec}
      do Maybe<&2, Vec>:
        pair : MatPair <- woodbury_core(d_inv, u, m, k)
        woodbury_solve.run(d_inv, u, b, pair)

def woodbury_solve.chk(ok: Bool, +n: U32, +k: U32, ds: List<&2, F32>, u: Mat, m: Mat, b: Vec) -> Maybe<&2, Vec>:
  match ok:
    case True{}:
      woodbury_solve.inv(inv_pos_list(ds), n, k, u, m, b)
    case False{}:
      None{}

# Solve (diag(d) + U M U^T) x = b. None on shape mismatch, non-positive d, or non-SPD M.
def woodbury_solve(d: Vec, u: Mat, m: Mat, b: Vec) -> Maybe<&2, Vec>:
  Vec{+nd, ds} = d
  Mat{+nu, +ku, urows} = u
  Mat{+mm, +mn, mrows} = m
  Vec{+nb, bs} = b
  +ok = Bool.and(U32.is_eq(nd, nu), Bool.and(U32.is_eq(nu, nb), Bool.and(U32.is_eq(mm, ku), U32.is_eq(mn, ku))))
  woodbury_solve.chk(ok, nu, ku, ds, Mat{nu, ku, urows}, Mat{mm, mn, mrows}, Vec{nb, bs})

def woodbury_logdet.fin(+sum_log_d: F32, pair: MatPair) -> Maybe<&2, F32>:
  MatPair{_, lc} = pair
  do Maybe<&2, F32>:
    ld_c : F32 <- cholesky_logdet(lc)
    return (sum_log_d + ld_c : F32)

def woodbury_logdet.inv(d_inv_l: Maybe<&2, List<&2, F32>>, log_d: Maybe<&2, F32>, +n: U32, +k: U32, u: Mat, m: Mat) -> Maybe<&2, F32>:
  match d_inv_l log_d:
    case Some{di} Some{ld}:
      do Maybe<&2, F32>:
        pair : MatPair <- woodbury_core(Vec{n, di}, u, m, k)
        woodbury_logdet.fin(ld, pair)
    case _ _:
      None{}

def woodbury_logdet.chk(ok: Bool, +n: U32, +k: U32, +ds: List<&2, F32>, u: Mat, m: Mat) -> Maybe<&2, F32>:
  match ok:
    case True{}:
      woodbury_logdet.inv(inv_pos_list(ds), sum_log_pos(ds), n, k, u, m)
    case False{}:
      None{}

# Compute log det(diag(d) + U M U^T) via the Matrix Determinant Lemma.
def woodbury_logdet(d: Vec, u: Mat, m: Mat) -> Maybe<&2, F32>:
  Vec{+nd, ds} = d
  Mat{+nu, +ku, urows} = u
  Mat{+mm, +mn, mrows} = m
  +ok = Bool.and(U32.is_eq(nd, nu), Bool.and(U32.is_eq(mm, ku), U32.is_eq(mn, ku)))
  woodbury_logdet.chk(ok, nu, ku, ds, Mat{nu, ku, urows}, Mat{mm, mn, mrows})

# ---------------------------------------------------------------- QR & least squares

type QR is Data:
  QR{q: Mat, r: Mat}

type QRPack is Type:
  QRPack{a: Array<F32>, tau: Array<F32>}

type ArrPair is Type:
  ArrPair{a: Array<F32>, b: Array<F32>}

type QRApplySt is Type:
  QRApplySt{a: Array<F32>, tau: Array<F32>, b: Array<F32>}

# ---- provable Q / R extractors

# Strided downward reader: prepends a[base + 0*stride .. (rem-1)*stride] onto acc.
def read_down_s.loop(+rem: Nat, r: Array<F32> & F32, acc: List<&2, F32>, +base: U32, +stride: U32) -> Array<F32> & List<&2, F32>:
  match rem:
    case 0n:
      (a, v) = r
      (a, v <> acc)
    case 1n+p:
      (a, v) = r
      read_down_s.loop(p, Array.get(F32, a, (base + (U32.from_nat(p) * stride) : U32)), v <> acc, base, stride)

def read_down_s(+rem: Nat, a: Array<F32>, acc: List<&2, F32>, +base: U32, +stride: U32) -> Array<F32> & List<&2, F32>:
  match rem:
    case 0n:
      (a, acc)
    case 1n+p:
      read_down_s.loop(p, Array.get(F32, a, (base + (U32.from_nat(p) * stride) : U32)), acc, base, stride)

# Extract m x n row-major list from column-major Array<F32> (stride = m).
def cm_rows.loop(+rem: Nat, r: Array<F32> & List<&2, F32>, acc: List<&2, List<&2, F32>>, +nn: Nat, +m: U32) -> Array<F32> & List<&2, List<&2, F32>>:
  match rem:
    case 0n:
      (a, row) = r
      (a, row <> acc)
    case 1n+p:
      (a, row) = r
      cm_rows.loop(p, read_down_s(nn, a, Nil{}, U32.from_nat(p), m), row <> acc, nn, m)

def cm_rows.go(+rem: Nat, a: Array<F32>, acc: List<&2, List<&2, F32>>, +nn: Nat, +m: U32) -> Array<F32> & List<&2, List<&2, F32>>:
  match rem:
    case 0n:
      (a, acc)
    case 1n+p:
      cm_rows.loop(p, read_down_s(nn, a, Nil{}, U32.from_nat(p), m), acc, nn, m)

def arr_colmajor_rows(a: Array<F32>, +m: U32, +n: U32) -> List<&2, List<&2, F32>>:
  arr_lower_rows.fin(cm_rows.go(U32.to_nat(m), a, Nil{}, U32.to_nat(n), m))

# Provable upper-triangular extractor: row i has i leading literal 0.0s
# followed by a[j * m + i] for j = i .. n-1.
def prepend_zeros(k: Nat, xs: List<&2, F32>) -> List<&2, F32>:
  match k:
    case 0n:
      xs
    case 1n+p:
      0.0 <> prepend_zeros(p, xs)

def upper_rows.loop(+rem: Nat, r: Array<F32> & List<&2, F32>, acc: List<&2, List<&2, F32>>, +n: Nat, +m: U32) -> Array<F32> & List<&2, List<&2, F32>>:
  match rem:
    case 0n:
      (a, hi) = r
      (a, hi <> acc)
    case 1n+p:
      (a, hi) = r
      +pu = U32.from_nat(p)
      upper_rows.loop(p, read_down_s(Nat.sub(n, p), a, Nil{}, ((pu * m) + pu : U32), m), prepend_zeros(1n+p, hi) <> acc, n, m)

def upper_rows.go(+rem: Nat, a: Array<F32>, acc: List<&2, List<&2, F32>>, +n: Nat, +m: U32) -> Array<F32> & List<&2, List<&2, F32>>:
  match rem:
    case 0n:
      (a, acc)
    case 1n+p:
      +pu = U32.from_nat(p)
      upper_rows.loop(p, read_down_s(Nat.sub(n, p), a, Nil{}, ((pu * m) + pu : U32), m), acc, n, m)

def arr_upper_rows(a: Array<F32>, +m: U32, +n: U32) -> List<&2, List<&2, F32>>:
  +nn = U32.to_nat(n)
  arr_lower_rows.fin(upper_rows.go(nn, a, Nil{}, nn, m))

# ---- Householder QR factorization in-place (LAPACK dgeqrf convention)

def col_ss.step(p: Array<F32> & F32, +acc: F32) -> Array<F32> & F32:
  (a, +v) = p
  (a, (acc + (v * v) : F32))

def col_ss(rem: Nat, st: Array<F32> & F32, +idx: U32) -> Array<F32> & F32:
  match rem:
    case 0n:
      st
    case 1n+p:
      (a, acc) = st
      col_ss(p, col_ss.step(Array.get(F32, a, idx), acc), (idx + 1 : U32))

def col_scale.step(p: Array<F32> & F32, +idx: U32, +s: F32) -> Array<F32>:
  (a, v) = p
  Array.set(F32, a, idx, (v * s : F32))

def col_scale(rem: Nat, a: Array<F32>, +idx: U32, +s: F32) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+p:
      col_scale(p, col_scale.step(Array.get(F32, a, idx), idx, s), (idx + 1 : U32), s)

def col_axpy2(p: Array<F32> & F32, +vk: F32, +s: F32, +oj: U32) -> Array<F32>:
  (a, vj) = p
  Array.set(F32, a, oj, (vj - (s * vk) : F32))

def col_axpy1(p: Array<F32> & F32, +oj: U32, +s: F32) -> Array<F32>:
  (a, vk) = p
  col_axpy2(Array.get(F32, a, oj), vk, s, oj)

def col_axpy(rem: Nat, a: Array<F32>, +ok: U32, +oj: U32, +s: F32) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+p:
      col_axpy(p, col_axpy1(Array.get(F32, a, ok), oj, s), (ok + 1 : U32), (oj + 1 : U32), s)

def qr.apply_col_dot(r: Array<F32> & F32, +tail_len: Nat, +ok1: U32, +oj0: U32, +oj1: U32, +ajk: F32, +tau_k: F32) -> Array<F32>:
  (a, d) = r
  +s = (tau_k * d : F32)
  a1 = Array.set(F32, a, oj0, (ajk - s : F32))
  col_axpy(tail_len, a1, ok1, oj1, s)

def qr.apply_col_head(p: Array<F32> & F32, +tail_len: Nat, +ok1: U32, +oj0: U32, +tau_k: F32) -> Array<F32>:
  (a, +ajk) = p
  +oj1 = (oj0 + 1 : U32)
  qr.apply_col_dot(arr_dot(tail_len, (a, ajk), ok1, oj1), tail_len, ok1, oj0, oj1, ajk, tau_k)

def qr.apply_cols(rem: Nat, a: Array<F32>, +j: U32, +k: U32, +m: U32, +tau_k: F32) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+p:
      +tail_len = U32.to_nat((m - (k + 1) : U32))
      +ok1 = (((k * m) + k) + 1 : U32)
      +oj0 = ((j * m) + k : U32)
      a1 = qr.apply_col_head(Array.get(F32, a, oj0), tail_len, ok1, oj0, tau_k)
      qr.apply_cols(p, a1, (j + 1 : U32), k, m, tau_k)

def qr.step_apply(zero_tail: Bool, a: Array<F32>, tau: Array<F32>, +k: U32, +m: U32, +n: U32, +x0: F32, +tail_ss: F32) -> QRPack:
  match zero_tail:
    case True{}:
      QRPack{a, Array.set(F32, tau, k, 0.0)}
    case False{}:
      +norm_x = F32.hypot(x0, F32.sqrt(tail_ss))
      +sign = Bool.pick(F32, F32.is_ge(x0, 0.0), 1.0, F32.neg(1.0))
      +v0 = (x0 + (sign * norm_x) : F32)
      +rkk = (F32.neg(sign) * norm_x : F32)
      +tau_k = (F32.abs(v0) / norm_x : F32)
      +kk = ((k * m) + k : U32)
      +tail_len = U32.to_nat((m - (k + 1) : U32))
      a1 = Array.set(F32, a, kk, rkk)
      a2 = col_scale(tail_len, a1, (kk + 1 : U32), (1.0 / v0 : F32))
      a3 = qr.apply_cols(U32.to_nat((n - (k + 1) : U32)), a2, (k + 1 : U32), k, m, tau_k)
      QRPack{a3, Array.set(F32, tau, k, tau_k)}

def qr.step_head(p: Array<F32> & F32, tau: Array<F32>, +tail_ss: F32, +k: U32, +m: U32, +n: U32) -> QRPack:
  (a, x0) = p
  qr.step_apply(F32.is_eq(tail_ss, 0.0), a, tau, k, m, n, x0, tail_ss)

def qr.step_ss(r: Array<F32> & F32, tau: Array<F32>, +k: U32, +m: U32, +n: U32) -> QRPack:
  (a, tail_ss) = r
  qr.step_head(Array.get(F32, a, ((k * m) + k : U32)), tau, tail_ss, k, m, n)

def qr.factor_loop(rem: Nat, pk: QRPack, +k: U32, +m: U32, +n: U32) -> QRPack:
  match rem:
    case 0n:
      pk
    case 1n+p:
      QRPack{a, tau} = pk
      +tail_len = U32.to_nat((m - (k + 1) : U32))
      pk1 = qr.step_ss(col_ss(tail_len, (a, 0.0), (((k * m) + k) + 1 : U32)), tau, k, m, n)
      qr.factor_loop(p, pk1, (k + 1 : U32), m, n)

def qr_factor_arr(rows: List<&2, List<&2, F32>>, +m: U32, +n: U32) -> QRPack:
  qr.factor_loop(U32.to_nat(n), QRPack{mat_to_colmajor(rows, m, n), Array.new(F32, arr_depth(n), 0.0)}, 0, m, n)

# ---- Applying packed Householder reflector H_k from array a to another array q

def axpy_aq2(pq: Array<F32> & F32, a: Array<F32>, +va: F32, +s: F32, +oq: U32) -> ArrPair:
  (q, vq) = pq
  ArrPair{a, Array.set(F32, q, oq, (vq - (s * va) : F32))}

def axpy_aq1(pa: Array<F32> & F32, q: Array<F32>, +oq: U32, +s: F32) -> ArrPair:
  (a, va) = pa
  axpy_aq2(Array.get(F32, q, oq), a, va, s, oq)

def axpy_aq(rem: Nat, st: ArrPair, +oa: U32, +oq: U32, +s: F32) -> ArrPair:
  match rem:
    case 0n:
      st
    case 1n+p:
      ArrPair{a, q} = st
      axpy_aq(p, axpy_aq1(Array.get(F32, a, oa), q, oq, s), (oa + 1 : U32), (oq + 1 : U32), s)

def qr_apply_h.dot(dm: DotMX, +tail_len: Nat, +oa1: U32, +oq0: U32, +oq1: U32, +qk: F32, +tau_k: F32) -> ArrPair:
  DotMX{a1, q1, d} = dm
  +s = (tau_k * d : F32)
  q2 = Array.set(F32, q1, oq0, (qk - s : F32))
  axpy_aq(tail_len, ArrPair{a1, q2}, oa1, oq1, s)

def qr_apply_h.head(pq: Array<F32> & F32, a: Array<F32>, +tail_len: Nat, +oa1: U32, +oq0: U32, +tau_k: F32) -> ArrPair:
  (q, +qk) = pq
  +oq1 = (oq0 + 1 : U32)
  qr_apply_h.dot(dot_mx(tail_len, DotMX{a, q, qk}, oa1, 1, oq1), tail_len, oa1, oq0, oq1, qk, tau_k)

def qr_apply_h_col(a: Array<F32>, q: Array<F32>, +k: U32, +m: U32, +col_off: U32, +tau_k: F32) -> ArrPair:
  +tail_len = U32.to_nat((m - (k + 1) : U32))
  +oa1 = (((k * m) + k) + 1 : U32)
  +oq0 = (col_off + k : U32)
  qr_apply_h.head(Array.get(F32, q, oq0), a, tail_len, oa1, oq0, tau_k)

# ---- Explicit Q accumulation (supports both thin q_cols=n and full q_cols=m)

def fill_eye_cm(rem: Nat, q: Array<F32>, +j: U32, +m: U32) -> Array<F32>:
  match rem:
    case 0n:
      q
    case 1n+p:
      fill_eye_cm(p, Array.set(F32, q, ((j * m) + j : U32), 1.0), (j + 1 : U32), m)

def qr_q.cols(rem: Nat, st: ArrPair, +j: U32, +k: U32, +m: U32, +tau_k: F32) -> ArrPair:
  match rem:
    case 0n:
      st
    case 1n+p:
      ArrPair{a, q} = st
      qr_q.cols(p, qr_apply_h_col(a, q, k, m, (j * m : U32), tau_k), (j + 1 : U32), k, m, tau_k)

def qr_q.step_nz(is_z: Bool, a: Array<F32>, q: Array<F32>, +k: U32, +m: U32, +q_cols: U32, +tau_k: F32) -> ArrPair:
  match is_z:
    case True{}:
      ArrPair{a, q}
    case False{}:
      qr_q.cols(U32.to_nat((q_cols - k : U32)), ArrPair{a, q}, k, k, m, tau_k)

def qr_q.wrap(p: ArrPair, tau: Array<F32>) -> QRApplySt:
  ArrPair{a1, q1} = p
  QRApplySt{a1, tau, q1}

def qr_q.step_tau(pt: Array<F32> & F32, a: Array<F32>, q: Array<F32>, +k: U32, +m: U32, +q_cols: U32) -> QRApplySt:
  (tau, +tau_k) = pt
  qr_q.wrap(qr_q.step_nz(F32.is_eq(tau_k, 0.0), a, q, k, m, q_cols, tau_k), tau)

def qr_q.loop(+rem: Nat, st: QRApplySt, +m: U32, +q_cols: U32) -> ArrPair:
  match rem:
    case 0n:
      QRApplySt{a, _, q} = st
      ArrPair{a, q}
    case 1n+p:
      QRApplySt{a, tau, q} = st
      +k = U32.from_nat(p)
      qr_q.loop(p, qr_q.step_tau(Array.get(F32, tau, k), a, q, k, m, q_cols), m, q_cols)

def qr_build_q(a: Array<F32>, tau: Array<F32>, +m: U32, +k_ref: U32, +q_cols: U32) -> ArrPair:
  q0 = fill_eye_cm(U32.to_nat(q_cols), Array.new(F32, arr_depth((m * q_cols : U32)), 0.0), 0, m)
  qr_q.loop(U32.to_nat(k_ref), QRApplySt{a, tau, q0}, m, q_cols)

def qr_thin.from_pair(p: ArrPair, +m: U32, +n: U32) -> QR:
  ArrPair{a1, q_arr} = p
  QR{Mat{m, n, arr_colmajor_rows(q_arr, m, n)}, Mat{n, n, arr_upper_rows(a1, m, n)}}

def qr_thin.fin(pk: QRPack, +m: U32, +n: U32) -> QR:
  QRPack{a, tau} = pk
  qr_thin.from_pair(qr_build_q(a, tau, m, n, n), m, n)

def qr_thin.chk(ok: Bool, +m: U32, +n: U32, rows: List<&2, List<&2, F32>>) -> Maybe<&2, QR>:
  match ok:
    case True{}:
      Some{qr_thin.fin(qr_factor_arr(rows, m, n), m, n)}
    case False{}:
      None{}

# Thin Householder QR decomposition for m >= n: A = Q R, with Q (m x n)
# orthonormal and R (n x n) upper triangular. None if m < n.
def qr_thin(a: Mat) -> Maybe<&2, QR>:
  Mat{+m, +n, rows} = a
  qr_thin.chk(U32.is_ge(m, n), m, n, rows)

# Internal full QR for m >= n: Q is m x m orthogonal, R is n x n upper triangular.
def qr_full.from_pair(p: ArrPair, +m: U32, +n: U32) -> QR:
  ArrPair{a1, q_arr} = p
  QR{Mat{m, m, arr_colmajor_rows(q_arr, m, m)}, Mat{n, n, arr_upper_rows(a1, m, n)}}

def qr_full.fin(pk: QRPack, +m: U32, +n: U32) -> QR:
  QRPack{a, tau} = pk
  qr_full.from_pair(qr_build_q(a, tau, m, n, m), m, n)

# ---- Direct Q^T b application & column-major R backward solve for lstsq

def qr_qt.step_nz(is_z: Bool, a: Array<F32>, b: Array<F32>, +k: U32, +m: U32, +tau_k: F32) -> ArrPair:
  match is_z:
    case True{}:
      ArrPair{a, b}
    case False{}:
      qr_apply_h_col(a, b, k, m, 0, tau_k)

def qr_qt.step_tau(pt: Array<F32> & F32, a: Array<F32>, b: Array<F32>, +k: U32, +m: U32) -> QRApplySt:
  (tau, +tau_k) = pt
  qr_q.wrap(qr_qt.step_nz(F32.is_eq(tau_k, 0.0), a, b, k, m, tau_k), tau)

def qr_qt.loop(rem: Nat, st: QRApplySt, +k: U32, +m: U32) -> QRApplySt:
  match rem:
    case 0n:
      st
    case 1n+p:
      QRApplySt{a, tau, b} = st
      qr_qt.loop(p, qr_qt.step_tau(Array.get(F32, tau, k), a, b, k, m), (k + 1 : U32), m)

def tri_step_dot_at(dm: DotMX, +i: U32, +diag_idx: U32) -> TriSt:
  DotMX{m1, x1, s} = dm
  tri_step_d(Array.get(F32, m1, diag_idx), x1, i, s)

# Backward substitution R x = y where R (n x n) is top-left of column-major m x n array a.
def solve_r_cm.go(+rem: Nat, st: TriSt, +m: U32, +n: U32) -> TriSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      match st:
        case TriSt{a, x, False{}}:
          TriSt{a, x, False{}}
        case TriSt{a, x, True{}}:
          +i = U32.from_nat(p)
          +i1 = (i + 1 : U32)
          st1 = tri_step_dot_at(dot_mx(U32.to_nat((n - i1 : U32)), DotMX{a, x, 0.0}, ((i1 * m) + i : U32), m, i1), i, ((i * m) + i : U32))
          solve_r_cm.go(p, st1, m, n)

def lstsq.solve_pack(st: QRApplySt, +m: U32, +n: U32) -> Maybe<&2, Vec>:
  QRApplySt{a, _, qtb} = st
  tri.fin_vec(solve_r_cm.go(U32.to_nat(n), TriSt{a, qtb, True{}}, m, n), n)

def lstsq.run(pk: QRPack, bs: List<&2, F32>, +m: U32, +n: U32) -> Maybe<&2, Vec>:
  QRPack{a, tau} = pk
  lstsq.solve_pack(qr_qt.loop(U32.to_nat(n), QRApplySt{a, tau, vec_to_arr(bs, m)}, 0, m), m, n)

def lstsq.chk(ok: Bool, +m: U32, +n: U32, rows: List<&2, List<&2, F32>>, bs: List<&2, F32>) -> Maybe<&2, Vec>:
  match ok:
    case True{}:
      lstsq.run(qr_factor_arr(rows, m, n), bs, m, n)
    case False{}:
      None{}

# Ordinary least squares min_x ||A x - b||_2 via thin Householder QR.
# None if m < n, len(b) != m, or A is numerically rank-deficient (zero R_ii).
def lstsq(a: Mat, b: Vec) -> Maybe<&2, Vec>:
  Mat{+m, +n, rows} = a
  Vec{nb, bs} = b
  lstsq.chk(Bool.and(U32.is_ge(m, n), U32.is_eq(m, nb)), m, n, rows, bs)

# ---- Weighted least squares min_x (A x - b)^T diag(w) (A x - b)

def sqrt_nn.step(ok: Bool, +x: F32, rest: Maybe<&2, List<&2, F32>>) -> Maybe<&2, List<&2, F32>>:
  match ok rest:
    case True{} Some{xs}:
      Some{F32.sqrt(x) <> xs}
    case _ _:
      None{}

def sqrt_nonneg_list(xs: List<&2, F32>) -> Maybe<&2, List<&2, F32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case Con{+x, t}:
      sqrt_nn.step(F32.is_ge(x, 0.0), x, sqrt_nonneg_list(t))

def lstsq.run_arr(pk: QRPack, b_arr: Array<F32>, +m: U32, +n: U32) -> Maybe<&2, Vec>:
  QRPack{a, tau} = pk
  lstsq.solve_pack(qr_qt.loop(U32.to_nat(n), QRApplySt{a, tau, b_arr}, 0, m), m, n)

def wlstsq.run(sw: Maybe<&2, List<&2, F32>>, +m: U32, a: Mat, b: Vec) -> Maybe<&2, Vec>:
  match sw:
    case None{}:
      None{}
    case Some{+sws}:
      Mat{_, +n, arows} = a
      Vec{_, bs} = b
      a_w = mat_to_colmajor_w(arows, sws, m, n)
      b_w = vec_to_arr_w(bs, sws, m)
      pk = qr.factor_loop(U32.to_nat(n), QRPack{a_w, Array.new(F32, arr_depth(n), 0.0)}, 0, m, n)
      lstsq.run_arr(pk, b_w, m, n)

def wlstsq.chk(ok: Bool, +m: U32, ws: List<&2, F32>, a: Mat, b: Vec) -> Maybe<&2, Vec>:
  match ok:
    case True{}:
      wlstsq.run(sqrt_nonneg_list(ws), m, a, b)
    case False{}:
      None{}

# Weighted least squares via QR on (diag(sqrt(w)) A, sqrt(w) .* b).
# None on shape mismatch, m < n, negative/NaN weight, or rank-deficient R.
def wlstsq(a: Mat, w: Vec, b: Vec) -> Maybe<&2, Vec>:
  Mat{+m, +n, rows} = a
  Vec{+nw, ws} = w
  Vec{+nb, bs} = b
  +ok = Bool.and(U32.is_ge(m, n), Bool.and(U32.is_eq(m, nw), U32.is_eq(m, nb)))
  wlstsq.chk(ok, m, ws, Mat{m, n, rows}, Vec{nb, bs})

# ---- Multi-RHS least squares min_X ||A X - B||_F (single QR factorization)

type QRMulSt is Type:
  QRMulSt{a: Array<F32>, tau: Array<F32>, cols: List<&2, List<&2, F32>>, ok: Bool}

def qr_mul.push(ts: TriSt, tau: Array<F32>, cols: List<&2, List<&2, F32>>, +n: U32) -> QRMulSt:
  match ts:
    case TriSt{a, _, False{}}:
      QRMulSt{a, tau, cols, False{}}
    case TriSt{a, x, True{}}:
      QRMulSt{a, tau, arr_to_list(x, n) <> cols, True{}}

def qr_mul.solve_one(ap: QRApplySt, cols: List<&2, List<&2, F32>>, +m: U32, +n: U32) -> QRMulSt:
  QRApplySt{a, tau, qtb} = ap
  qr_mul.push(solve_r_cm.go(U32.to_nat(n), TriSt{a, qtb, True{}}, m, n), tau, cols, n)

def qr_mul.cols(bcols: List<&2, List<&2, F32>>, st: QRMulSt, +m: U32, +n: U32) -> QRMulSt:
  match bcols:
    case Nil{}:
      st
    case Con{bc, rest}:
      match st:
        case QRMulSt{a, tau, acc, False{}}:
          QRMulSt{a, tau, acc, False{}}
        case QRMulSt{a, tau, acc, True{}}:
          st1 = qr_mul.solve_one(qr_qt.loop(U32.to_nat(n), QRApplySt{a, tau, vec_to_arr(bc, m)}, 0, m), acc, m, n)
          qr_mul.cols(rest, st1, m, n)

def qr_mul.fin(st: QRMulSt, +n: U32, +k: U32) -> Maybe<&2, Mat>:
  match st:
    case QRMulSt{_, _, _, False{}}:
      None{}
    case QRMulSt{_, _, rev_cols, True{}}:
      Some{Mat{n, k, transpose.rows(List.reverse(&2, List<&2, F32>, rev_cols), U32.to_nat(n))}}

def lstsq_mat.run(pk: QRPack, bcols: List<&2, List<&2, F32>>, +m: U32, +n: U32, +k: U32) -> Maybe<&2, Mat>:
  QRPack{a, tau} = pk
  qr_mul.fin(qr_mul.cols(bcols, QRMulSt{a, tau, Nil{}, True{}}, m, n), n, k)

def lstsq_mat.chk(ok: Bool, +m: U32, +n: U32, +k: U32, arows: List<&2, List<&2, F32>>, brows: List<&2, List<&2, F32>>) -> Maybe<&2, Mat>:
  match ok:
    case True{}:
      lstsq_mat.run(qr_factor_arr(arows, m, n), transpose.rows(brows, U32.to_nat(k)), m, n, k)
    case False{}:
      None{}

# Multi-RHS least squares min_X ||A X - B||_F; factors A once via thin QR.
def lstsq_mat(a: Mat, b: Mat) -> Maybe<&2, Mat>:
  Mat{+ma, +na, arows} = a
  Mat{mb, nb, brows} = b
  lstsq_mat.chk(Bool.and(U32.is_ge(ma, na), U32.is_eq(ma, mb)), ma, na, nb, arows, brows)

# ---- Orthogonal projection (I - Q Q^T) x on flat Array<F32> (zero transposes)

def proj_qtx.set(pqtx: Array<F32> & F32, q: Array<F32>, +qv: F32, +xi: F32, +j: U32) -> ArrPair:
  (qtx, cur) = pqtx
  ArrPair{q, Array.set(F32, qtx, j, (cur + (qv * xi) : F32))}

def proj_qtx.get_q(pq: Array<F32> & F32, qtx: Array<F32>, +xi: F32, +j: U32) -> ArrPair:
  (q, qv) = pq
  proj_qtx.set(Array.get(F32, qtx, j), q, qv, xi, j)

def proj_qtx.cols(rem: Nat, st: ArrPair, +q_off: U32, +xi: F32, +j: U32) -> ArrPair:
  match rem:
    case 0n:
      st
    case 1n+p:
      ArrPair{q, qtx} = st
      proj_qtx.cols(p, proj_qtx.get_q(Array.get(F32, q, (q_off + j : U32)), qtx, xi, j), q_off, xi, (j + 1 : U32))

def proj_qtx.row(px: Array<F32> & F32, q: Array<F32>, qtx: Array<F32>, +q_off: U32, +nn: Nat) -> QRApplySt:
  (x, xi) = px
  qr_q.wrap(proj_qtx.cols(nn, ArrPair{q, qtx}, q_off, xi, 0), x)

def proj_qtx.rows(rem: Nat, st: QRApplySt, +i: U32, +n: U32, +nn: Nat) -> QRApplySt:
  match rem:
    case 0n:
      st
    case 1n+p:
      QRApplySt{q, x, qtx} = st
      proj_qtx.rows(p, proj_qtx.row(Array.get(F32, x, i), q, qtx, (i * n : U32), nn), (i + 1 : U32), n, nn)

def proj_sub.set(px: Array<F32> & F32, q: Array<F32>, qtx: Array<F32>, +i: U32, +dot_v: F32) -> QRApplySt:
  (x, xi) = px
  QRApplySt{q, Array.set(F32, x, i, (xi - dot_v : F32)), qtx}

def proj_sub.dot(dm: DotMX, x: Array<F32>, +i: U32) -> QRApplySt:
  DotMX{q, qtx, s} = dm
  proj_sub.set(Array.get(F32, x, i), q, qtx, i, s)

def proj_sub.rows(rem: Nat, st: QRApplySt, +i: U32, +n: U32, +nn: Nat) -> QRApplySt:
  match rem:
    case 0n:
      st
    case 1n+p:
      QRApplySt{q, x, qtx} = st
      proj_sub.rows(p, proj_sub.dot(dot_mx(nn, DotMX{q, qtx, 0.0}, (i * n : U32), 1, 0), x, i), (i + 1 : U32), n, nn)

def proj_pass.fin(st: QRApplySt) -> ArrPair:
  QRApplySt{q, x, _} = st
  ArrPair{q, x}

def proj_pass(st: ArrPair, +m: U32, +n: U32) -> ArrPair:
  ArrPair{q, x} = st
  +mm = U32.to_nat(m)
  +nn = U32.to_nat(n)
  qtx0 = Array.new(F32, arr_depth(n), 0.0)
  st1 = proj_qtx.rows(mm, QRApplySt{q, x, qtx0}, 0, n, nn)
  proj_pass.fin(proj_sub.rows(mm, st1, 0, n, nn))

def proj_orth.fin(st: ArrPair, +m: U32) -> Vec:
  ArrPair{_, x} = st
  Vec{m, arr_to_list(x, m)}

def project_orth.chk(ok: Bool, +q: Mat, x: Vec) -> Maybe<&2, Vec>:
  match ok:
    case True{}:
      Mat{+m, +n, qrows} = q
      Vec{_, xs} = x
      Some{proj_orth.fin(proj_pass(proj_pass(ArrPair{mat_to_arr(qrows, m, n), vec_to_arr(xs, m)}, m, n), m, n), m)}
    case False{}:
      None{}

# Orthogonal projection (I - Q Q^T) x for orthonormal Q (e.g. from qr_thin).
# Applies (I - Q Q^T) twice (Kahan-Parlett) for full F32 orthogonality.
def project_orth(q: Mat, x: Vec) -> Maybe<&2, Vec>:
  Mat{+mq, +nq, qrows} = q
  Vec{+nx, xs} = x
  project_orth.chk(U32.is_eq(mq, nx), Mat{mq, nq, qrows}, Vec{nx, xs})

# ---- Equality-constrained least squares: min ||A x - b||_2^2 s.t. C^T x = d
# Uses null-space QR of C = [Q1 Q2] [Rc; 0], so A may be rank-deficient
# (e.g. market + industry dummies with a cap-weight constraint).

def lstsq_c.null(full_con: Bool, +a: Mat, b: Vec, q: Mat, +x1: Vec, +n: U32, +p: U32) -> Maybe<&2, Vec>:
  match full_con:
    case True{}:
      Some{x1}
    case False{}:
      +q2 = slice_cols(q, p, (n - p : U32))
      do Maybe<&2, Vec>:
        ax1 : Vec <- matvec(a, x1)
        rhs : Vec <- vsub(b, ax1)
        aq2 : Mat <- matmul(a, q2)
        y2 : Vec <- lstsq(aq2, rhs)
        x2 : Vec <- matvec(q2, y2)
        vadd(x1, x2)

def lstsq_c.run_qr(qr: QR, a: Mat, b: Vec, d: Vec, +n: U32, +p: U32) -> Maybe<&2, Vec>:
  QR{+q, rc} = qr
  +q1 = slice_cols(q, 0, p)
  do Maybe<&2, Vec>:
    y1 : Vec <- solve_lower(transpose(rc), d)
    x1 : Vec <- matvec(q1, y1)
    lstsq_c.null(U32.is_eq(p, n), a, b, q, x1, n, p)

def lstsq_c.run(a: Mat, b: Vec, crows: List<&2, List<&2, F32>>, d: Vec, +n: U32, +p: U32) -> Maybe<&2, Vec>:
  lstsq_c.run_qr(qr_full.fin(qr_factor_arr(crows, n, p), n, p), a, b, d, n, p)

def lstsq_c.zero(no_con: Bool, a: Mat, b: Vec, crows: List<&2, List<&2, F32>>, d: Vec, +n: U32, +p: U32) -> Maybe<&2, Vec>:
  match no_con:
    case True{}:
      lstsq(a, b)
    case False{}:
      lstsq_c.run(a, b, crows, d, n, p)

def lstsq_c.chk(ok: Bool, a: Mat, b: Vec, crows: List<&2, List<&2, F32>>, d: Vec, +n: U32, +p: U32) -> Maybe<&2, Vec>:
  match ok:
    case True{}:
      lstsq_c.zero(U32.is_eq(p, 0), a, b, crows, d, n, p)
    case False{}:
      None{}

# Equality-constrained least squares: min ||A x - b||_2^2 subject to C^T x = d,
# where A is m x n, b is m, C is n x p (p <= n), d is p, and m >= n - p.
def lstsq_constrained(a: Mat, b: Vec, c: Mat, d: Vec) -> Maybe<&2, Vec>:
  Mat{+ma, +na, arows} = a
  Vec{+nb, bs} = b
  Mat{+cm, +cp, crows} = c
  Vec{+nd, ds} = d
  +ok = Bool.and(U32.is_eq(ma, nb), Bool.and(U32.is_eq(cm, na), Bool.and(U32.is_eq(cp, nd), Bool.and(U32.is_ge(na, cp), U32.is_ge(ma, (na - cp : U32))))))
  lstsq_c.chk(ok, Mat{ma, na, arows}, Vec{nb, bs}, crows, Vec{nd, ds}, na, cp)

# ---------------------------------------------------------------- Symmetric Eigen (Cyclic Jacobi)

type Eigen is Data:
  Eigen{values: Vec, vectors: Mat}

type EigCol is Data:
  EigCol{val: F32, col: List<&2, F32>}

type JSt is Type:
  JSt{a: Array<F32>, v: Array<F32>, changed: Bool}

# ---- Symmetrize row-major n x n array: A_ij = A_ji = 0.5 * (A_ij + A_ji)

def sym_pair2(p2: Array<F32> & F32, +aij: F32, +ij: U32, +ji: U32) -> Array<F32>:
  (a, aji) = p2
  +avg = (0.5 * (aij + aji) : F32)
  Array.set(F32, Array.set(F32, a, ij, avg), ji, avg)

def sym_pair1(p1: Array<F32> & F32, +ij: U32, +ji: U32) -> Array<F32>:
  (a, aij) = p1
  sym_pair2(Array.get(F32, a, ji), aij, ij, ji)

def sym_arr.j(rem: Nat, a: Array<F32>, +i: U32, +j: U32, +n: U32) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+p:
      +ij = ((i * n) + j : U32)
      +ji = ((j * n) + i : U32)
      sym_arr.j(p, sym_pair1(Array.get(F32, a, ij), ij, ji), i, (j + 1 : U32), n)

def sym_arr.i(rem: Nat, a: Array<F32>, +i: U32, +n: U32) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+p:
      +j0 = (i + 1 : U32)
      sym_arr.i(p, sym_arr.j(U32.to_nat((n - j0 : U32)), a, i, j0, n), j0, n)

def symmetrize_arr(a: Array<F32>, +n: U32) -> Array<F32>:
  sym_arr.i(U32.to_nat((n - 1 : U32)), a, 0, n)

# ---- Jacobi rotations on symmetric A and eigenvector matrix V (both row-major n x n)

def jac.rot_a_set(p2: Array<F32> & F32, +arp: F32, +c: F32, +s: F32, +rp: U32, +pr: U32, +rq: U32, +qr: U32) -> Array<F32>:
  (a, +arq) = p2
  +np = ((c * arp) - (s * arq) : F32)
  +nq = ((s * arp) + (c * arq) : F32)
  a1 = Array.set(F32, a, rp, np)
  a2 = Array.set(F32, a1, pr, np)
  a3 = Array.set(F32, a2, rq, nq)
  Array.set(F32, a3, qr, nq)

def jac.rot_a_get1(p1: Array<F32> & F32, +c: F32, +s: F32, +rp: U32, +pr: U32, +rq: U32, +qr: U32) -> Array<F32>:
  (a, arp) = p1
  jac.rot_a_set(Array.get(F32, a, rq), arp, c, s, rp, pr, rq, qr)

def jac.rot_a_skip(skip: Bool, a: Array<F32>, +r: U32, +p: U32, +q: U32, +n: U32, +c: F32, +s: F32) -> Array<F32>:
  match skip:
    case True{}:
      a
    case False{}:
      +rp = ((r * n) + p : U32)
      +pr = ((p * n) + r : U32)
      +rq = ((r * n) + q : U32)
      +qr = ((q * n) + r : U32)
      jac.rot_a_get1(Array.get(F32, a, rp), c, s, rp, pr, rq, qr)

def jac.rot_a(rem: Nat, a: Array<F32>, +r: U32, +p: U32, +q: U32, +n: U32, +c: F32, +s: F32) -> Array<F32>:
  match rem:
    case 0n:
      a
    case 1n+m:
      +skip = Bool.or(U32.is_eq(r, p), U32.is_eq(r, q))
      jac.rot_a(m, jac.rot_a_skip(skip, a, r, p, q, n, c, s), (r + 1 : U32), p, q, n, c, s)

def jac.rot_v_set(p2: Array<F32> & F32, +vrp: F32, +c: F32, +s: F32, +rp: U32, +rq: U32) -> Array<F32>:
  (v, +vrq) = p2
  v1 = Array.set(F32, v, rp, ((c * vrp) - (s * vrq) : F32))
  Array.set(F32, v1, rq, ((s * vrp) + (c * vrq) : F32))

def jac.rot_v_get1(p1: Array<F32> & F32, +c: F32, +s: F32, +rp: U32, +rq: U32) -> Array<F32>:
  (v, vrp) = p1
  jac.rot_v_set(Array.get(F32, v, rq), vrp, c, s, rp, rq)

def jac.rot_v(rem: Nat, v: Array<F32>, +r: U32, +p: U32, +q: U32, +n: U32, +c: F32, +s: F32) -> Array<F32>:
  match rem:
    case 0n:
      v
    case 1n+m:
      +rp = ((r * n) + p : U32)
      +rq = ((r * n) + q : U32)
      jac.rot_v(m, jac.rot_v_get1(Array.get(F32, v, rp), c, s, rp, rq), (r + 1 : U32), p, q, n, c, s)

def jac.apply(small: Bool, a: Array<F32>, v: Array<F32>, ch: Bool, +app: F32, +aqq: F32, +apq: F32, +p: U32, +q: U32, +n: U32) -> JSt:
  match small:
    case True{}:
      JSt{a, v, ch}
    case False{}:
      +tau = ((aqq - app) / (2.0 * apq) : F32)
      +abs_tau = F32.abs(tau)
      +denom = (abs_tau + F32.hypot(1.0, tau) : F32)
      +t = Bool.pick(F32, F32.is_ge(tau, 0.0), (1.0 / denom : F32), (F32.neg(1.0) / denom : F32))
      +c = (1.0 / F32.hypot(1.0, t) : F32)
      +s = (t * c : F32)
      a1 = jac.rot_a(U32.to_nat(n), a, 0, p, q, n, c, s)
      +npp = (app - (t * apq) : F32)
      +nqq = (aqq + (t * apq) : F32)
      a2 = Array.set(F32, a1, ((p * n) + p : U32), npp)
      a3 = Array.set(F32, a2, ((q * n) + q : U32), nqq)
      a4 = Array.set(F32, a3, ((p * n) + q : U32), 0.0)
      a5 = Array.set(F32, a4, ((q * n) + p : U32), 0.0)
      v1 = jac.rot_v(U32.to_nat(n), v, 0, p, q, n, c, s)
      JSt{a5, v1, True{}}

def jac.g3(r: Array<F32> & F32, v: Array<F32>, ch: Bool, +app: F32, +aqq: F32, +p: U32, +q: U32, +n: U32, +tol: F32) -> JSt:
  (a, +apq) = r
  +small = Bool.or(F32.is_eq(apq, 0.0), F32.is_le(F32.abs(apq), tol))
  jac.apply(small, a, v, ch, app, aqq, apq, p, q, n)

def jac.g2(r: Array<F32> & F32, v: Array<F32>, ch: Bool, +app: F32, +p: U32, +q: U32, +n: U32, +tol: F32) -> JSt:
  (a, aqq) = r
  jac.g3(Array.get(F32, a, ((p * n) + q : U32)), v, ch, app, aqq, p, q, n, tol)

def jac.g1(r: Array<F32> & F32, v: Array<F32>, ch: Bool, +p: U32, +q: U32, +n: U32, +tol: F32) -> JSt:
  (a, app) = r
  jac.g2(Array.get(F32, a, ((q * n) + q : U32)), v, ch, app, p, q, n, tol)

def jac.q(rem: Nat, st: JSt, +p: U32, +q: U32, +n: U32, +tol: F32) -> JSt:
  match rem:
    case 0n:
      st
    case 1n+m:
      JSt{a, v, ch} = st
      jac.q(m, jac.g1(Array.get(F32, a, ((p * n) + p : U32)), v, ch, p, q, n, tol), p, (q + 1 : U32), n, tol)

def jac.p(rem: Nat, st: JSt, +p: U32, +n: U32, +tol: F32) -> JSt:
  match rem:
    case 0n:
      st
    case 1n+m:
      +q0 = (p + 1 : U32)
      jac.p(m, jac.q(U32.to_nat((n - q0 : U32)), st, p, q0, n, tol), q0, n, tol)

def jac.sweeps(rem: Nat, st: JSt, +n: U32, +tol: F32) -> JSt:
  match rem:
    case 0n:
      st
    case 1n+m:
      match st:
        case JSt{a, v, False{}}:
          JSt{a, v, False{}}
        case JSt{a, v, True{}}:
          jac.sweeps(m, jac.p(U32.to_nat((n - 1 : U32)), JSt{a, v, False{}}, 0, n, tol), n, tol)

# ---- Provable extraction & descending sort for sym_eigen

def eig_ins.pick(ge: Bool, x: EigCol, y: EigCol, t: List<&2, EigCol>, rec: List<&2, EigCol>) -> List<&2, EigCol>:
  match ge:
    case True{}:
      x <> (y <> t)
    case False{}:
      y <> rec

def eig_ins(+x: EigCol, xs: List<&2, EigCol>) -> List<&2, EigCol>:
  match x xs:
    case EigCol{+vx, +cx} Nil{}:
      EigCol{vx, cx} <> Nil{}
    case EigCol{+vx, +cx} Con{EigCol{+vy, +cy}, +t}:
      eig_ins.pick(F32.is_ge(vx, vy), EigCol{vx, cx}, EigCol{vy, cy}, t, eig_ins(EigCol{vx, cx}, t))

def eig_sort(xs: List<&2, EigCol>) -> List<&2, EigCol>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      eig_ins(h, eig_sort(t))

def eig_vals(xs: List<&2, EigCol>) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{EigCol{v, _}, t}:
      v <> eig_vals(t)

def eig_cols(xs: List<&2, EigCol>) -> List<&2, List<&2, F32>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{EigCol{_, c}, t}:
      c <> eig_cols(t)

def jac_extract.loop(+rem: Nat, ra: Array<F32> & F32, rv: Array<F32> & List<&2, F32>, acc: List<&2, EigCol>, +nn: Nat, +n: U32) -> List<&2, EigCol>:
  match rem:
    case 0n:
      (_, lam) = ra
      (_, col) = rv
      EigCol{lam, col} <> acc
    case 1n+p:
      (a, lam) = ra
      (v, col) = rv
      +pu = U32.from_nat(p)
      jac_extract.loop(p, Array.get(F32, a, ((pu * n) + pu : U32)), read_down_s(nn, v, Nil{}, pu, n), EigCol{lam, col} <> acc, nn, n)

def jac_extract.go(+rem: Nat, a: Array<F32>, v: Array<F32>, acc: List<&2, EigCol>, +nn: Nat, +n: U32) -> List<&2, EigCol>:
  match rem:
    case 0n:
      acc
    case 1n+p:
      +pu = U32.from_nat(p)
      jac_extract.loop(p, Array.get(F32, a, ((pu * n) + pu : U32)), read_down_s(nn, v, Nil{}, pu, n), acc, nn, n)

def jac_extract.build(ec: List<&2, EigCol>, +n: U32) -> Eigen:
  +sorted = eig_sort(ec)
  Eigen{Vec{n, eig_vals(sorted)}, Mat{n, n, transpose.rows(eig_cols(sorted), U32.to_nat(n))}}

def jac.fin(st: JSt, +n: U32) -> Eigen:
  JSt{a, v, _} = st
  jac_extract.build(jac_extract.go(U32.to_nat(n), a, v, Nil{}, U32.to_nat(n), n), n)

def jac.run_n(le1: Bool, +n: U32, +rows: List<&2, List<&2, F32>>) -> JSt:
  match le1:
    case True{}:
      a0 = mat_to_arr(rows, n, n)
      v0 = fill_eye_cm(U32.to_nat(n), Array.new(F32, arr_depth((n * n : U32)), 0.0), 0, n)
      JSt{a0, v0, False{}}
    case False{}:
      +scale = F32.max(1.0e-30, frobenius(Mat{n, n, rows}))
      +tol = (1.0e-8 * scale : F32)
      a0 = symmetrize_arr(mat_to_arr(rows, n, n), n)
      v0 = fill_eye_cm(U32.to_nat(n), Array.new(F32, arr_depth((n * n : U32)), 0.0), 0, n)
      jac.sweeps(20n, JSt{a0, v0, True{}}, n, tol)

def sym_eigen.chk(ok: Bool, +n: U32, rows: List<&2, List<&2, F32>>) -> Maybe<&2, Eigen>:
  match ok:
    case True{}:
      Some{jac.fin(jac.run_n(U32.is_le(n, 1), n, rows), n)}
    case False{}:
      None{}

# Symmetric eigendecomposition A = V diag(values) V^T via cyclic Jacobi.
# Eigenvalues are sorted in descending order; columns of vectors are orthonormal.
# None if A is not square.
def sym_eigen(a: Mat) -> Maybe<&2, Eigen>:
  Mat{m, +n, rows} = a
  sym_eigen.chk(U32.is_eq(m, n), n, rows)

# ---------------------------------------------------------------- SPD Matrix Power A^p

def pow_pos(+lam: F32, +p: F32) -> F32:
  Bool.pick(F32, F32.is_eq(p, 0.0), 1.0,
    Bool.pick(F32, F32.is_eq(p, 1.0), lam,
      Bool.pick(F32, F32.is_eq(p, 0.5), F32.sqrt(lam),
        Bool.pick(F32, F32.is_eq(p, F32.neg(0.5)), (1.0 / F32.sqrt(lam) : F32),
          Bool.pick(F32, F32.is_eq(p, F32.neg(1.0)), (1.0 / lam : F32),
            F32.exp((p * F32.log(lam) : F32)))))))

def pow_pos_list.step(pos: Bool, +lam: F32, +p: F32, rest: Maybe<&2, List<&2, F32>>) -> Maybe<&2, List<&2, F32>>:
  match pos rest:
    case True{} Some{xs}:
      Some{pow_pos(lam, p) <> xs}
    case _ _:
      None{}

def pow_pos_list(xs: List<&2, F32>, +p: F32) -> Maybe<&2, List<&2, F32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case Con{+x, t}:
      pow_pos_list.step(F32.is_gt(x, 0.0), x, p, pow_pos_list(t, p))

def spd_pow.build(lp: Maybe<&2, List<&2, F32>>, +n: U32, ut: Mat) -> Maybe<&2, Mat>:
  match lp:
    case None{}:
      None{}
    case Some{lps}:
      wgram(ut, Vec{n, lps})

def spd_pow.from_eig(eig: Eigen, +p: F32) -> Maybe<&2, Mat>:
  Eigen{Vec{+n, lams}, u} = eig
  spd_pow.build(pow_pos_list(lams, p), n, transpose(u))

def spd_pow.chk(me: Maybe<&2, Eigen>, +p: F32) -> Maybe<&2, Mat>:
  match me:
    case None{}:
      None{}
    case Some{eig}:
      spd_pow.from_eig(eig, p)

# Real power A^p = U diag(lambda^p) U^T for symmetric positive-definite A.
# Covers A^(1/2), A^(-1/2), A^(-1), etc. Result is structurally symmetric.
# None if A is not square or has any non-positive eigenvalue.
def spd_pow(a: Mat, +p: F32) -> Maybe<&2, Mat>:
  spd_pow.chk(sym_eigen(a), p)

# ---------------------------------------------------------------- Thin SVD (QR + One-Sided Jacobi)

type SVD is Data:
  SVD{u: Mat, s: Vec, vt: Mat}

type SVDCol is Data:
  SVDCol{sig: F32, ucol: List<&2, F32>, vcol: List<&2, F32>}

# Rotate contiguous column-major columns p (offset op) and q (offset oq) of length rem.
def rot_cm2(p2: Array<F32> & F32, +bp: F32, +c: F32, +s: F32, +op: U32, +oq: U32) -> Array<F32>:
  (b, +bq) = p2
  b1 = Array.set(F32, b, op, ((c * bp) - (s * bq) : F32))
  Array.set(F32, b1, oq, ((s * bp) + (c * bq) : F32))

def rot_cm1(p1: Array<F32> & F32, +c: F32, +s: F32, +op: U32, +oq: U32) -> Array<F32>:
  (b, bp) = p1
  rot_cm2(Array.get(F32, b, oq), bp, c, s, op, oq)

def rot_cm(rem: Nat, b: Array<F32>, +op: U32, +oq: U32, +c: F32, +s: F32) -> Array<F32>:
  match rem:
    case 0n:
      b
    case 1n+p:
      rot_cm(p, rot_cm1(Array.get(F32, b, op), c, s, op, oq), (op + 1 : U32), (oq + 1 : U32), c, s)

def svd_j.apply(skip: Bool, b: Array<F32>, v: Array<F32>, ch: Bool, +alpha: F32, +beta: F32, +gamma: F32, +op: U32, +oq: U32, +nn: Nat) -> JSt:
  match skip:
    case True{}:
      JSt{b, v, ch}
    case False{}:
      +tau = ((beta - alpha) / (2.0 * gamma) : F32)
      +abs_tau = F32.abs(tau)
      +denom = (abs_tau + F32.hypot(1.0, tau) : F32)
      +t = Bool.pick(F32, F32.is_ge(tau, 0.0), (1.0 / denom : F32), (F32.neg(1.0) / denom : F32))
      +c = (1.0 / F32.hypot(1.0, t) : F32)
      +s = (t * c : F32)
      b1 = rot_cm(nn, b, op, oq, c, s)
      v1 = rot_cm(nn, v, op, oq, c, s)
      JSt{b1, v1, True{}}

def svd_j.g3(rg: Array<F32> & F32, v: Array<F32>, ch: Bool, +alpha: F32, +beta: F32, +op: U32, +oq: U32, +nn: Nat) -> JSt:
  (b, +gamma) = rg
  +ab = (F32.sqrt(alpha) * F32.sqrt(beta) : F32)
  +skip = Bool.or(F32.is_eq(ab, 0.0), F32.is_le(F32.abs(gamma), (5.0e-8 * ab : F32)))
  svd_j.apply(skip, b, v, ch, alpha, beta, gamma, op, oq, nn)

def svd_j.g2(rb: Array<F32> & F32, v: Array<F32>, ch: Bool, +alpha: F32, +op: U32, +oq: U32, +nn: Nat) -> JSt:
  (b, beta) = rb
  svd_j.g3(arr_dot(nn, (b, 0.0), op, oq), v, ch, alpha, beta, op, oq, nn)

def svd_j.g1(ra: Array<F32> & F32, v: Array<F32>, ch: Bool, +op: U32, +oq: U32, +nn: Nat) -> JSt:
  (b, alpha) = ra
  svd_j.g2(col_ss(nn, (b, 0.0), oq), v, ch, alpha, op, oq, nn)

def svd_j.q(rem: Nat, st: JSt, +p: U32, +q: U32, +n: U32, +nn: Nat) -> JSt:
  match rem:
    case 0n:
      st
    case 1n+m:
      JSt{b, v, ch} = st
      +op = (p * n : U32)
      +oq = (q * n : U32)
      svd_j.q(m, svd_j.g1(col_ss(nn, (b, 0.0), op), v, ch, op, oq, nn), p, (q + 1 : U32), n, nn)

def svd_j.p(rem: Nat, st: JSt, +p: U32, +n: U32, +nn: Nat) -> JSt:
  match rem:
    case 0n:
      st
    case 1n+m:
      +q0 = (p + 1 : U32)
      svd_j.p(m, svd_j.q(U32.to_nat((n - q0 : U32)), st, p, q0, n, nn), q0, n, nn)

def svd_j.sweeps(rem: Nat, st: JSt, +n: U32, +nn: Nat) -> JSt:
  match rem:
    case 0n:
      st
    case 1n+m:
      match st:
        case JSt{b, v, False{}}:
          JSt{b, v, False{}}
        case JSt{b, v, True{}}:
          svd_j.sweeps(m, svd_j.p(U32.to_nat((n - 1 : U32)), JSt{b, v, False{}}, 0, n, nn), n, nn)

# ---- Extract, sort descending, and orthonormalize U columns (including zero-sigma completion)

def svd_ins.pick(ge: Bool, x: SVDCol, y: SVDCol, t: List<&2, SVDCol>, rec: List<&2, SVDCol>) -> List<&2, SVDCol>:
  match ge:
    case True{}:
      x <> (y <> t)
    case False{}:
      y <> rec

def svd_ins(+x: SVDCol, xs: List<&2, SVDCol>) -> List<&2, SVDCol>:
  match x xs:
    case SVDCol{+sx, +ux, +vx} Nil{}:
      SVDCol{sx, ux, vx} <> Nil{}
    case SVDCol{+sx, +ux, +vx} Con{SVDCol{+sy, +uy, +vy}, +t}:
      svd_ins.pick(F32.is_ge(sx, sy), SVDCol{sx, ux, vx}, SVDCol{sy, uy, vy}, t, svd_ins(SVDCol{sx, ux, vx}, t))

def svd_sort(xs: List<&2, SVDCol>) -> List<&2, SVDCol>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      svd_ins(h, svd_sort(t))

def svd_extract.loop(+rem: Nat, rb: Array<F32> & List<&2, F32>, rv: Array<F32> & List<&2, F32>, acc: List<&2, SVDCol>, +nn: Nat, +n: U32) -> List<&2, SVDCol>:
  match rem:
    case 0n:
      (_, +bcol) = rb
      (_, vcol) = rv
      +sig = F32.sqrt(dot_raw(bcol, bcol))
      SVDCol{sig, bcol, vcol} <> acc
    case 1n+p:
      (b, +bcol) = rb
      (v, vcol) = rv
      +sig = F32.sqrt(dot_raw(bcol, bcol))
      +off = (U32.from_nat(p) * n : U32)
      svd_extract.loop(p, read_down(nn, b, Nil{}, off), read_down(nn, v, Nil{}, off), SVDCol{sig, bcol, vcol} <> acc, nn, n)

def svd_extract.go(+rem: Nat, b: Array<F32>, v: Array<F32>, acc: List<&2, SVDCol>, +nn: Nat, +n: U32) -> List<&2, SVDCol>:
  match rem:
    case 0n:
      acc
    case 1n+p:
      +off = (U32.from_nat(p) * n : U32)
      svd_extract.loop(p, read_down(nn, b, Nil{}, off), read_down(nn, v, Nil{}, off), acc, nn, n)

# Project vector x orthogonal to a list of orthonormal basis vectors (two passes).
def orth_against.one(basis: List<&2, List<&2, F32>>, +x: List<&2, F32>) -> List<&2, F32>:
  match basis:
    case Nil{}:
      x
    case Con{+q, qs}:
      +d = dot_raw(q, x)
      orth_against.one(qs, axpy.go(F32.neg(d), q, x))

def orth_against(+basis: List<&2, List<&2, F32>>, x: List<&2, F32>) -> List<&2, F32>:
  orth_against.one(basis, orth_against.one(basis, x))

def basis_complete.loop(rem: Nat, found: Bool, best: List<&2, F32>, +idx: Nat, +nn: Nat, +basis: List<&2, List<&2, F32>>) -> List<&2, F32>:
  match rem found:
    case _ True{}:
      best
    case 0n False{}:
      best
    case 1n+p False{}:
      +cand = orth_against(basis, row_unit(nn, 0n, idx))
      +nrm = F32.sqrt(dot_raw(cand, cand))
      +ok = F32.is_gt(nrm, 0.1)
      +nxt = Bool.pick(List<&2, F32>, ok, vscale.go((1.0 / nrm : F32), cand), best)
      basis_complete.loop(p, ok, nxt, 1n+idx, nn, basis)

def basis_complete(+nn: Nat, basis: List<&2, List<&2, F32>>) -> List<&2, F32>:
  basis_complete.loop(nn, False{}, row_unit(nn, 0n, 0n), 0n, nn, basis)

def svd_norm_u.pick(ok: Bool, cand: List<&2, F32>, +nrm: F32, +nn: Nat, basis: List<&2, List<&2, F32>>) -> List<&2, F32>:
  match ok:
    case True{}:
      vscale.go((1.0 / nrm : F32), cand)
    case False{}:
      basis_complete(nn, basis)

def svd_norm_u.pos(pos: Bool, +sig: F32, ucol: List<&2, F32>, +nn: Nat, +basis: List<&2, List<&2, F32>>) -> List<&2, F32>:
  match pos:
    case True{}:
      +scaled = vscale.go((1.0 / sig : F32), ucol)
      +cand = orth_against(basis, scaled)
      +nrm = F32.sqrt(dot_raw(cand, cand))
      svd_norm_u.pick(F32.is_gt(nrm, 0.1), cand, nrm, nn, basis)
    case False{}:
      basis_complete(nn, basis)

def svd_build_u(cols: List<&2, SVDCol>, +basis: List<&2, List<&2, F32>>, +nn: Nat) -> List<&2, List<&2, F32>>:
  match cols:
    case Nil{}:
      List.reverse(&2, List<&2, F32>, basis)
    case Con{SVDCol{+sig, ucol, _}, t}:
      +u = svd_norm_u.pos(F32.is_gt(sig, 0.0), sig, ucol, nn, basis)
      svd_build_u(t, u <> basis, nn)

def svd_sigs(cols: List<&2, SVDCol>) -> List<&2, F32>:
  match cols:
    case Nil{}:
      Nil{}
    case Con{SVDCol{s, _, _}, t}:
      s <> svd_sigs(t)

def svd_vrows(cols: List<&2, SVDCol>) -> List<&2, List<&2, F32>>:
  match cols:
    case Nil{}:
      Nil{}
    case Con{SVDCol{_, _, v}, t}:
      v <> svd_vrows(t)

def svd_tall.fin(st: JSt, q0_rows: List<&2, List<&2, F32>>, +m: U32, +n: U32) -> SVD:
  JSt{b, v, _} = st
  +nn = U32.to_nat(n)
  +sorted = svd_sort(svd_extract.go(nn, b, v, Nil{}, nn, n))
  +u_cols = svd_build_u(sorted, Nil{}, nn)
  +u_rows = pmap(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~matmul.row, q0_rows, m, u_cols)
  SVD{Mat{m, n, u_rows}, Vec{n, svd_sigs(sorted)}, Mat{n, n, svd_vrows(sorted)}}

def svd_tall.from_qr(qr: QR, +m: U32, +n: U32) -> SVD:
  QR{Mat{_, _, q0_rows}, Mat{_, _, r0_rows}} = qr
  +nn = U32.to_nat(n)
  b0 = mat_to_colmajor(r0_rows, n, n)
  v0 = fill_eye_cm(nn, Array.new(F32, arr_depth((n * n : U32)), 0.0), 0, n)
  st = svd_j.sweeps(20n, JSt{b0, v0, True{}}, n, nn)
  svd_tall.fin(st, q0_rows, m, n)

def svd_tall.n1_col(rows: List<&2, List<&2, F32>>) -> List<&2, F32>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{Con{x, _}, t}:
      x <> svd_tall.n1_col(t)
    case Con{Nil{}, t}:
      0.0 <> svd_tall.n1_col(t)

def svd_tall.n1_unit(pos: Bool, +s0: F32, col: List<&2, F32>, +m: U32) -> List<&2, F32>:
  match pos:
    case True{}:
      vscale.go((1.0 / s0 : F32), col)
    case False{}:
      row_unit(U32.to_nat(m), 0n, 0n)

def svd_tall.n1(rows: List<&2, List<&2, F32>>, +m: U32) -> SVD:
  +col = svd_tall.n1_col(rows)
  +s0 = F32.sqrt(dot_raw(col, col))
  +ucol = svd_tall.n1_unit(F32.is_gt(s0, 0.0), s0, col, m)
  +urows = transpose.rows(ucol <> Nil{}, U32.to_nat(m))
  SVD{Mat{m, 1, urows}, Vec{1, s0 <> Nil{}}, Mat{1, 1, (1.0 <> Nil{}) <> Nil{}}}

def svd_tall.gt0(is_one: Bool, rows: List<&2, List<&2, F32>>, +m: U32, +n: U32) -> SVD:
  match is_one:
    case True{}:
      svd_tall.n1(rows, m)
    case False{}:
      svd_tall.from_qr(qr_thin.fin(qr_factor_arr(rows, m, n), m, n), m, n)

def svd_tall.go(is_zero: Bool, rows: List<&2, List<&2, F32>>, +m: U32, +n: U32) -> SVD:
  match is_zero:
    case True{}:
      SVD{Mat.zeros(m, 0), Vec{0, Nil{}}, Mat{0, 0, Nil{}}}
    case False{}:
      svd_tall.gt0(U32.is_eq(n, 1), rows, m, n)

def svd_wide.flip(sv: SVD) -> SVD:
  SVD{ut, s, vtt} = sv
  SVD{transpose(vtt), s, transpose(ut)}

def svd_thin.dir(tall: Bool, +m: U32, +n: U32, rows: List<&2, List<&2, F32>>) -> SVD:
  match tall:
    case True{}:
      svd_tall.go(U32.is_eq(n, 0), rows, m, n)
    case False{}:
      svd_wide.flip(svd_tall.go(U32.is_eq(m, 0), transpose.rows(rows, U32.to_nat(n)), n, m))

# Thin SVD A = U diag(s) V^T for any m x n matrix, with k = min(m, n):
# U is m x k orthonormal, s is length-k descending non-negative singular values,
# V^T is k x n orthonormal. Exploits min(m, n) when m < n.
def svd_thin(a: Mat) -> SVD:
  Mat{+m, +n, rows} = a
  svd_thin.dir(U32.is_ge(m, n), m, n, rows)

# ---------------------------------------------------------------- Pseudoinverse & Procrustes

def pinv.inv_sigs(xs: List<&2, F32>, +cut: F32) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+s, t}:
      +inv = Bool.pick(F32, Bool.and(F32.is_gt(s, cut), F32.is_gt(s, 0.0)), (1.0 / s : F32), 0.0)
      inv <> pinv.inv_sigs(t, cut)

def pinv.max_sig(xs: List<&2, F32>) -> F32:
  match xs:
    case Nil{}:
      0.0
    case Con{s, _}:
      s

def pinv.from_svd(sv: SVD, +m: U32, +n: U32, +tol: F32) -> Mat:
  SVD{Mat{_, _, urows}, Vec{k, +sigs}, Mat{_, _, vtrows}} = sv
  +cut = (F32.max(0.0, tol) * pinv.max_sig(sigs) : F32)
  +sinv = pinv.inv_sigs(sigs, cut)
  +vrows = transpose.rows(vtrows, U32.to_nat(n))
  +utrows = transpose.rows(urows, U32.to_nat(k))
  +sut_rows = diag_mul.rows(sinv, utrows)
  +sut_cols = transpose.rows(sut_rows, U32.to_nat(m))
  Mat{n, m, pmap(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~matmul.row, vrows, n, sut_cols)}

# Moore-Penrose pseudoinverse A^+ = V Sigma^+ U^T via thin SVD.
# Singular values <= max(0, tol) * sigma_max are treated as zero.
def pinv(a: Mat, +tol: F32) -> Mat:
  Mat{+m, +n, rows} = a
  pinv.from_svd(svd_thin(Mat{m, n, rows}), m, n, tol)

def atb_arr.j(rem: Nat, st: WGramSt, +i: U32, +j: U32, +m: U32, +mm: Nat, +k: U32) -> WGramSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      WGramSt{a, b, g} = st
      st1 = wgram_arr.set(dot_mx(mm, DotMX{a, b, 0.0}, (i * m : U32), 1, (j * m : U32)), g, ((j * k) + i : U32))
      atb_arr.j(p, st1, i, (j + 1 : U32), m, mm, k)

def atb_arr.i(rem: Nat, st: WGramSt, +i: U32, +m: U32, +mm: Nat, +k: U32) -> WGramSt:
  match rem:
    case 0n:
      st
    case 1n+p:
      atb_arr.i(p, atb_arr.j(U32.to_nat(k), st, i, 0, m, mm, k), (i + 1 : U32), m, mm, k)

def atb_mat(arows: List<&2, List<&2, F32>>, brows: List<&2, List<&2, F32>>, +m: U32, +k: U32) -> Mat:
  a = mat_to_colmajor(arows, m, k)
  b = mat_to_colmajor(brows, m, k)
  g0 = Array.new(F32, arr_depth((k * k : U32)), 0.0)
  g = wgram_arr.fin(atb_arr.i(U32.to_nat(k), WGramSt{a, b, g0}, 0, m, U32.to_nat(m), k))
  Mat{k, k, arr_colmajor_rows(g, k, k)}

def procrustes.from_svd(sv: SVD) -> Maybe<&2, Mat>:
  SVD{u, _, vt} = sv
  matmul(transpose(vt), transpose(u))

def procrustes.run(a: Mat, b: Mat) -> Maybe<&2, Mat>:
  Mat{+m, +k, arows} = a
  Mat{_, _, brows} = b
  procrustes.from_svd(svd_thin(atb_mat(arows, brows, m, k)))

def procrustes.chk(ok: Bool, a: Mat, b: Mat) -> Maybe<&2, Mat>:
  match ok:
    case True{}:
      procrustes.run(a, b)
    case False{}:
      None{}

# Orthogonal Procrustes: orthogonal k x k matrix X = V U^T minimizing ||A - B X||_F,
# where A^T B = U Sigma V^T. None if A and B do not have identical shapes.
def procrustes(a: Mat, b: Mat) -> Maybe<&2, Mat>:
  Mat{+ma, +na, arows} = a
  Mat{+mb, +nb, brows} = b
  procrustes.chk(Bool.and(U32.is_eq(ma, mb), U32.is_eq(na, nb)), Mat{ma, na, arows}, Mat{mb, nb, brows})
