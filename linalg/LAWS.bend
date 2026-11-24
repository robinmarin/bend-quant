# Laws for linalg. The checker doesn't run F32 arithmetic, so numerical values
# are verified against NumPy and SciPy in check.py. These laws prove structural
# invariants for every input.
import Base
import ./linalg.bend as L

def is_some_mat(m: Maybe<&2, L.Mat>) -> Bool:
  match m:
    case Some{_}:
      True{}
    case None{}:
      False{}

def row(n: Nat) -> List<&2, F32>:
  List.replicate(F32, n, 1.0)

# ---------------------------------------------------------------- from_rows

law from_rows_equal:
  {is_some_mat(L.Mat.from_rows([row(3n), row(3n), row(3n)])) == True{} : Bool}

law from_rows_ragged:
  {is_some_mat(L.Mat.from_rows([row(3n), row(2n), row(3n)])) == False{} : Bool}

law from_rows_ragged_last:
  {is_some_mat(L.Mat.from_rows([row(3n), row(3n), row(4n)])) == False{} : Bool}

law from_rows_empty:
  {is_some_mat(L.Mat.from_rows(Nil{})) == True{} : Bool}

# ---------------------------------------------------------------- header checks
# Ops trust the declared m x n header. Mat.ok checks it against the rows.

law mat_ok_rect:
  {L.Mat.ok(L.Mat{2, 3, [row(3n), row(3n)]}) == True{} : Bool}

law mat_ok_wrong_m:
  {L.Mat.ok(L.Mat{3, 3, [row(3n), row(3n)]}) == False{} : Bool}

law mat_ok_ragged:
  {L.Mat.ok(L.Mat{2, 3, [row(3n), row(2n)]}) == False{} : Bool}

# ---------------------------------------------------------------- parallel map

law pmap_seq:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: C -> A -> B
  for +xs: List<&2, A>
  for +t: U32
  for +c: C
  {L.pmap(~A, ~B, ~C, ~f, xs, t, c) == L.pseq(~A, ~B, ~C, ~f, xs, c) : List<&2, B>}

def fmap(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, +c: C, m: Maybe<&2, A>) -> Maybe<&2, B>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{f(c, x)}

law pseq_get:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: C -> A -> B
  for +xs: List<&2, A>
  for +c: C
  for +i: Nat
  {List.get(&2, B, L.pseq(~A, ~B, ~C, ~f, xs, c), i) == fmap(~A, ~B, ~C, ~f, c, List.get(&2, A, xs, i)) : Maybe<&2, B>}

# ---------------------------------------------------------------- transpose

# Transposing a rectangular m x n matrix produces n rows.
law transpose_len:
  for +rows: List<&2, List<&2, F32>>
  for +n: Nat
  for +h: {L.Mat.rows.ok(rows, n) == True{} : Bool}
  {List.length(&2, List<&2, F32>, L.transpose.rows(rows, n)) == n : Nat}

# Every row of the transpose of a rectangular m x n matrix has length m.
law transpose_row_len:
  for +rows: List<&2, List<&2, F32>>
  for +n: Nat
  for +h: {L.Mat.rows.ok(rows, n) == True{} : Bool}
  {L.Mat.rows.ok(L.transpose.rows(rows, n), List.length(&2, List<&2, F32>, rows)) == True{} : Bool}

# Indexing the transpose swaps row and column indices for every (i, j)
# (both in-bounds and out-of-bounds) on any rectangular m x n matrix.
law transpose_get:
  for +rows: List<&2, List<&2, F32>>
  for +n: Nat
  for +i: Nat
  for +j: Nat
  for +h: {L.Mat.rows.ok(rows, n) == True{} : Bool}
  {L.mat_get(L.transpose.rows(rows, n), j, i) == L.mat_get(rows, i, j) : Maybe<&2, F32>}

# Transpose is an involution on every rectangular matrix: (A^T)^T == A.
law transpose_involutive:
  for +rows: List<&2, List<&2, F32>>
  for +n: Nat
  for +h: {L.Mat.rows.ok(rows, n) == True{} : Bool}
  {L.transpose.rows(L.transpose.rows(rows, n), List.length(&2, List<&2, F32>, rows)) == rows : List<&2, List<&2, F32>>}

# A well-formed m x n matrix transposes to a well-formed n x m matrix.
law transpose_ok:
  for +a: L.Mat
  for +h: {L.Mat.ok(a) == True{} : Bool}
  {L.Mat.ok(L.transpose(a)) == True{} : Bool}

# ---------------------------------------------------------------- products

def mm_ok(mm: Maybe<&2, L.Mat>) -> Bool:
  match mm:
    case None{}:
      False{}
    case Some{a}:
      L.Mat.ok(a)

def mv_ok(mv: Maybe<&2, L.Vec>) -> Bool:
  match mv:
    case None{}:
      False{}
    case Some{v}:
      L.Vec.ok(v)

def mv_get(mv: Maybe<&2, L.Vec>, i: Nat) -> Maybe<&2, F32>:
  match mv:
    case None{}:
      None{}
    case Some{v}:
      L.Vec.get(v, i)

def mm_get(mm: Maybe<&2, L.Mat>, i: Nat, j: Nat) -> Maybe<&2, F32>:
  match mm:
    case None{}:
      None{}
    case Some{a}:
      L.Mat.get(a, i, j)

def opt_dot(mr: Maybe<&2, List<&2, F32>>, mc: Maybe<&2, List<&2, F32>>) -> Maybe<&2, F32>:
  match mr mc:
    case Some{r} Some{c}:
      Some{L.dot_raw(r, c)}
    case _ _:
      None{}

# Entry i of matvec(A, x) is dot(row i of A, x) whenever dimensions match.
law matvec_entry:
  for +ma: U32
  for +na: U32
  for +nx: U32
  for +ra: List<&2, List<&2, F32>>
  for +xs: List<&2, F32>
  for +i: Nat
  for e: {U32.is_eq(na, nx) == True{} : Bool}
  {mv_get(L.matvec(L.Mat{ma, na, ra}, L.Vec{nx, xs}), i) == fmap(~List<&2, F32>, ~F32, ~List<&2, F32>, ~L.matvec.row, xs, List.get(&2, List<&2, F32>, ra, i)) : Maybe<&2, F32>}

# Entry (i, j) of matmul(A, B) is dot(row i of A, col j of B) whenever na == mb.
law matmul_entry:
  for +ma: U32
  for +na: U32
  for +mb: U32
  for +nb: U32
  for +ra: List<&2, List<&2, F32>>
  for +rb: List<&2, List<&2, F32>>
  for +i: Nat
  for +j: Nat
  for e: {U32.is_eq(na, mb) == True{} : Bool}
  {mm_get(L.matmul(L.Mat{ma, na, ra}, L.Mat{mb, nb, rb}), i, j) == opt_dot(List.get(&2, List<&2, F32>, ra, i), List.get(&2, List<&2, F32>, L.transpose.rows(rb, U32.to_nat(nb)), j)) : Maybe<&2, F32>}

# matvec of a well-formed matrix succeeds with a well-formed vector of length m.
law matvec_ok:
  for +ma: U32
  for +na: U32
  for +nx: U32
  for +ra: List<&2, List<&2, F32>>
  for +xs: List<&2, F32>
  for e: {U32.is_eq(na, nx) == True{} : Bool}
  for +ha: {L.Mat.ok(L.Mat{ma, na, ra}) == True{} : Bool}
  {mv_ok(L.matvec(L.Mat{ma, na, ra}, L.Vec{nx, xs})) == True{} : Bool}

# matmul of well-formed matrices succeeds with a well-formed ma x nb matrix.
law matmul_ok:
  for +ma: U32
  for +na: U32
  for +mb: U32
  for +nb: U32
  for +ra: List<&2, List<&2, F32>>
  for +rb: List<&2, List<&2, F32>>
  for e: {U32.is_eq(na, mb) == True{} : Bool}
  for +ha: {L.Mat.ok(L.Mat{ma, na, ra}) == True{} : Bool}
  for +hb: {L.Mat.ok(L.Mat{mb, nb, rb}) == True{} : Bool}
  {mm_ok(L.matmul(L.Mat{ma, na, ra}, L.Mat{mb, nb, rb})) == True{} : Bool}

# Mismatched shapes return None.
law matmul_mismatch:
  for +ma: U32
  for +na: U32
  for +mb: U32
  for +nb: U32
  for +ra: List<&2, List<&2, F32>>
  for +rb: List<&2, List<&2, F32>>
  for e: {U32.is_eq(na, mb) == False{} : Bool}
  {L.matmul(L.Mat{ma, na, ra}, L.Mat{mb, nb, rb}) == None{} : Maybe<&2, L.Mat>}

# ---------------------------------------------------------------- Gram symmetry

# An upper-triangular list of rows of lengths n, n-1, ..., 1.
def upper_ok(up: List<&2, List<&2, F32>>, +n: Nat) -> Bool:
  match up n:
    case Nil{} 0n:
      True{}
    case Con{r, t} 1n+p:
      Bool.and(Nat.is_eq(List.length(&2, F32, r), 1n+p), upper_ok(t, p))
    case _ _:
      False{}

# Mirroring any well-formed upper triangle produces an exactly symmetric matrix
# at every index pair (i, j).
law mirror_upper_sym:
  for +up: List<&2, List<&2, F32>>
  for +n: Nat
  for +i: Nat
  for +j: Nat
  for +h: {upper_ok(up, n) == True{} : Bool}
  {L.mat_get(L.mirror_upper(up), i, j) == L.mat_get(L.mirror_upper(up), j, i) : Maybe<&2, F32>}

# gram(A) is structurally symmetric for every rectangular matrix A and all (i, j).
law gram_sym:
  for +m: U32
  for +n: U32
  for +rows: List<&2, List<&2, F32>>
  for +i: Nat
  for +j: Nat
  for h: {L.Mat.rows.ok(rows, U32.to_nat(n)) == True{} : Bool}
  {L.Mat.get(L.gram(L.Mat{m, n, rows}), i, j) == L.Mat.get(L.gram(L.Mat{m, n, rows}), j, i) : Maybe<&2, F32>}

# wgram(A, w) is structurally symmetric for every matching rectangular A and w.
law wgram_sym:
  for +m: U32
  for +n: U32
  for +nw: U32
  for +rows: List<&2, List<&2, F32>>
  for +ws: List<&2, F32>
  for +i: Nat
  for +j: Nat
  for e: {U32.is_eq(m, nw) == True{} : Bool}
  for h: {L.Mat.rows.ok(rows, U32.to_nat(n)) == True{} : Bool}
  {mm_get(L.wgram(L.Mat{m, n, rows}, L.Vec{nw, ws}), i, j) == mm_get(L.wgram(L.Mat{m, n, rows}, L.Vec{nw, ws}), j, i) : Maybe<&2, F32>}

# ---------------------------------------------------------------- Cholesky & solves

def mat_m(a: L.Mat) -> U32:
  L.Mat{m, _, _} = a
  m

def mat_n(a: L.Mat) -> U32:
  L.Mat{_, n, _} = a
  n

def mat_rows(a: L.Mat) -> List<&2, List<&2, F32>>:
  L.Mat{_, _, rows} = a
  rows

# Non-square matrices fail Cholesky with None.
law cholesky_nonsquare:
  for +m: U32
  for +n: U32
  for +rows: List<&2, List<&2, F32>>
  for e: {U32.is_eq(m, n) == False{} : Bool}
  {L.cholesky(L.Mat{m, n, rows}) == None{} : Maybe<&2, L.Mat>}

# Whenever cholesky(A) succeeds with Some{L}, L is n x n with n rows of length n.
law cholesky_shape:
  for +a: L.Mat
  for +l: L.Mat
  for +hc: {L.cholesky(a) == Some{l} : Maybe<&2, L.Mat>}
  {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, mat_rows(l)), U32.to_nat(mat_n(a))), L.Mat.rows.ok(mat_rows(l), U32.to_nat(mat_n(a)))) == True{} : Bool}

# Whenever cholesky(A) succeeds with Some{L}, every entry strictly above the
# diagonal (i < j < n) is exact 0.0.
law cholesky_upper_zero:
  for +a: L.Mat
  for +l: L.Mat
  for +i: Nat
  for +k: Nat
  for +hc: {L.cholesky(a) == Some{l} : Maybe<&2, L.Mat>}
  for +hb: {Nat.is_lt(Nat.add(1n+i, k), U32.to_nat(mat_n(a))) == True{} : Bool}
  {L.Mat.get(l, i, Nat.add(1n+i, k)) == Some{0.0} : Maybe<&2, F32>}

# Mismatched shapes return None for triangular solves.
law solve_lower_mismatch:
  for +lm: U32
  for +ln: U32
  for +nb: U32
  for +lrows: List<&2, List<&2, F32>>
  for +bs: List<&2, F32>
  for e: {Bool.and(U32.is_eq(lm, ln), U32.is_eq(ln, nb)) == False{} : Bool}
  {L.solve_lower(L.Mat{lm, ln, lrows}, L.Vec{nb, bs}) == None{} : Maybe<&2, L.Vec>}

law solve_upper_mismatch:
  for +um: U32
  for +un: U32
  for +nb: U32
  for +urows: List<&2, List<&2, F32>>
  for +bs: List<&2, F32>
  for e: {Bool.and(U32.is_eq(um, un), U32.is_eq(un, nb)) == False{} : Bool}
  {L.solve_upper(L.Mat{um, un, urows}, L.Vec{nb, bs}) == None{} : Maybe<&2, L.Vec>}

# Mismatched shapes return None for woodbury_solve.
law woodbury_solve_mismatch:
  for +nd: U32
  for +nu: U32
  for +ku: U32
  for +mm: U32
  for +mn: U32
  for +nb: U32
  for +ds: List<&2, F32>
  for +urows: List<&2, List<&2, F32>>
  for +mrows: List<&2, List<&2, F32>>
  for +bs: List<&2, F32>
  for e: {Bool.and(U32.is_eq(nd, nu), Bool.and(U32.is_eq(nu, nb), Bool.and(U32.is_eq(mm, ku), U32.is_eq(mn, ku)))) == False{} : Bool}
  {L.woodbury_solve(L.Vec{nd, ds}, L.Mat{nu, ku, urows}, L.Mat{mm, mn, mrows}, L.Vec{nb, bs}) == None{} : Maybe<&2, L.Vec>}

# ---------------------------------------------------------------- QR & least squares

def qr_q(qr: L.QR) -> L.Mat:
  L.QR{q, _} = qr
  q

def qr_r(qr: L.QR) -> L.Mat:
  L.QR{_, r} = qr
  r

# Wide matrices (m < n) fail qr_thin with None.
law qr_thin_wide:
  for +m: U32
  for +n: U32
  for +rows: List<&2, List<&2, F32>>
  for e: {U32.is_ge(m, n) == False{} : Bool}
  {L.qr_thin(L.Mat{m, n, rows}) == None{} : Maybe<&2, L.QR>}

# Whenever qr_thin(A) succeeds with Some{QR{Q, R}}, Q has m rows of length n.
law qr_q_shape:
  for +a: L.Mat
  for +qr: L.QR
  for +hq: {L.qr_thin(a) == Some{qr} : Maybe<&2, L.QR>}
  {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, mat_rows(qr_q(qr))), U32.to_nat(mat_m(a))), L.Mat.rows.ok(mat_rows(qr_q(qr)), U32.to_nat(mat_n(a)))) == True{} : Bool}

# Whenever qr_thin(A) succeeds with Some{QR{Q, R}}, R has n rows of length n.
law qr_r_shape:
  for +a: L.Mat
  for +qr: L.QR
  for +hq: {L.qr_thin(a) == Some{qr} : Maybe<&2, L.QR>}
  {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, mat_rows(qr_r(qr))), U32.to_nat(mat_n(a))), L.Mat.rows.ok(mat_rows(qr_r(qr)), U32.to_nat(mat_n(a)))) == True{} : Bool}

# Whenever qr_thin(A) succeeds with Some{QR{Q, R}}, every entry of R strictly
# below the diagonal (j < i < n) is exact 0.0.
law qr_r_lower_zero:
  for +a: L.Mat
  for +qr: L.QR
  for +j: Nat
  for +k: Nat
  for +hq: {L.qr_thin(a) == Some{qr} : Maybe<&2, L.QR>}
  for +hb: {Nat.is_lt(Nat.add(1n+j, k), U32.to_nat(mat_n(a))) == True{} : Bool}
  {L.Mat.get(qr_r(qr), Nat.add(1n+j, k), j) == Some{0.0} : Maybe<&2, F32>}

# Mismatched shapes return None for least squares & projection ops.
law lstsq_mismatch:
  for +m: U32
  for +n: U32
  for +nb: U32
  for +rows: List<&2, List<&2, F32>>
  for +bs: List<&2, F32>
  for e: {Bool.and(U32.is_ge(m, n), U32.is_eq(m, nb)) == False{} : Bool}
  {L.lstsq(L.Mat{m, n, rows}, L.Vec{nb, bs}) == None{} : Maybe<&2, L.Vec>}

law wlstsq_mismatch:
  for +m: U32
  for +n: U32
  for +nw: U32
  for +nb: U32
  for +rows: List<&2, List<&2, F32>>
  for +ws: List<&2, F32>
  for +bs: List<&2, F32>
  for e: {Bool.and(U32.is_ge(m, n), Bool.and(U32.is_eq(m, nw), U32.is_eq(m, nb))) == False{} : Bool}
  {L.wlstsq(L.Mat{m, n, rows}, L.Vec{nw, ws}, L.Vec{nb, bs}) == None{} : Maybe<&2, L.Vec>}

law lstsq_mat_mismatch:
  for +ma: U32
  for +na: U32
  for +mb: U32
  for +nb: U32
  for +arows: List<&2, List<&2, F32>>
  for +brows: List<&2, List<&2, F32>>
  for e: {Bool.and(U32.is_ge(ma, na), U32.is_eq(ma, mb)) == False{} : Bool}
  {L.lstsq_mat(L.Mat{ma, na, arows}, L.Mat{mb, nb, brows}) == None{} : Maybe<&2, L.Mat>}

law project_orth_mismatch:
  for +mq: U32
  for +nq: U32
  for +nx: U32
  for +qrows: List<&2, List<&2, F32>>
  for +xs: List<&2, F32>
  for e: {U32.is_eq(mq, nx) == False{} : Bool}
  {L.project_orth(L.Mat{mq, nq, qrows}, L.Vec{nx, xs}) == None{} : Maybe<&2, L.Vec>}

law lstsq_constrained_mismatch:
  for +ma: U32
  for +na: U32
  for +nb: U32
  for +cm: U32
  for +cp: U32
  for +nd: U32
  for +arows: List<&2, List<&2, F32>>
  for +bs: List<&2, F32>
  for +crows: List<&2, List<&2, F32>>
  for +ds: List<&2, F32>
  for e: {Bool.and(U32.is_eq(ma, nb), Bool.and(U32.is_eq(cm, na), Bool.and(U32.is_eq(cp, nd), Bool.and(U32.is_ge(na, cp), U32.is_ge(ma, (na - cp : U32)))))) == False{} : Bool}
  {L.lstsq_constrained(L.Mat{ma, na, arows}, L.Vec{nb, bs}, L.Mat{cm, cp, crows}, L.Vec{nd, ds}) == None{} : Maybe<&2, L.Vec>}

# ---------------------------------------------------------------- Symmetric Eigen, SPD power, SVD & Procrustes

def eig_values(e: L.Eigen) -> List<&2, F32>:
  L.Eigen{L.Vec{_, xs}, _} = e
  xs

def eig_vectors(e: L.Eigen) -> L.Mat:
  L.Eigen{_, v} = e
  v

def svd_u(sv: L.SVD) -> L.Mat:
  L.SVD{u, _, _} = sv
  u

def svd_s_n(sv: L.SVD) -> U32:
  L.SVD{_, L.Vec{n, _}, _} = sv
  n

def svd_vt(sv: L.SVD) -> L.Mat:
  L.SVD{_, _, vt} = sv
  vt

# Non-square matrices fail sym_eigen with None.
law sym_eigen_nonsquare:
  for +m: U32
  for +n: U32
  for +rows: List<&2, List<&2, F32>>
  for e: {U32.is_eq(m, n) == False{} : Bool}
  {L.sym_eigen(L.Mat{m, n, rows}) == None{} : Maybe<&2, L.Eigen>}

# Whenever sym_eigen(A) succeeds with Some{Eigen{vals, V}}, vals has length n
# and V has n rows of length n.
law sym_eigen_shape:
  for +a: L.Mat
  for +eig: L.Eigen
  for +he: {L.sym_eigen(a) == Some{eig} : Maybe<&2, L.Eigen>}
  {Bool.and(Nat.is_eq(List.length(&2, F32, eig_values(eig)), U32.to_nat(mat_n(a))), Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, mat_rows(eig_vectors(eig))), U32.to_nat(mat_n(a))), L.Mat.rows.ok(mat_rows(eig_vectors(eig)), U32.to_nat(mat_n(a))))) == True{} : Bool}

# Non-square matrices fail spd_pow with None.
law spd_pow_nonsquare:
  for +m: U32
  for +n: U32
  for +rows: List<&2, List<&2, F32>>
  for +p: F32
  for e: {U32.is_eq(m, n) == False{} : Bool}
  {L.spd_pow(L.Mat{m, n, rows}, p) == None{} : Maybe<&2, L.Mat>}

# spd_pow(A, p) is structurally symmetric whenever it succeeds.
law spd_pow_sym:
  for +a: L.Mat
  for +p: F32
  for +i: Nat
  for +j: Nat
  {mm_get(L.spd_pow(a, p), i, j) == mm_get(L.spd_pow(a, p), j, i) : Maybe<&2, F32>}

# Mismatched shapes return None for procrustes.
law procrustes_mismatch:
  for +ma: U32
  for +na: U32
  for +mb: U32
  for +nb: U32
  for +arows: List<&2, List<&2, F32>>
  for +brows: List<&2, List<&2, F32>>
  for e: {Bool.and(U32.is_eq(ma, mb), U32.is_eq(na, nb)) == False{} : Bool}
  {L.procrustes(L.Mat{ma, na, arows}, L.Mat{mb, nb, brows}) == None{} : Maybe<&2, L.Mat>}
