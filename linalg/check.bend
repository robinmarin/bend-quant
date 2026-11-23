# Numerical test harness for linalg. Driven by check.py, which compares outputs
# against NumPy and SciPy.
import Base
import ./linalg.bend as L
import ./io.bend as I

def show_list(xs: List<&2, F32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, Nil{}}:
      F32.show(x)
    case Con{x, t}:
      F32.show(x) ++ " " ++ show_list(t)

def show_vec(tag: String, v: L.Vec) -> String:
  L.Vec{n, xs} = v
  tag ++ " " ++ U32.show(n) ++ " " ++ show_list(xs) ++ "\n"

def show_mvec(tag: String, mv: Maybe<&2, L.Vec>) -> String:
  match mv:
    case None{}:
      tag ++ " none\n"
    case Some{v}:
      show_vec(tag, v)

def show_mf32(tag: String, mv: Maybe<&2, F32>) -> String:
  match mv:
    case None{}:
      tag ++ " none\n"
    case Some{x}:
      tag ++ " " ++ F32.show(x) ++ "\n"

def show_rows(rows: List<&2, List<&2, F32>>) -> String:
  match rows:
    case Nil{}:
      ""
    case Con{r, Nil{}}:
      show_list(r)
    case Con{r, t}:
      show_list(r) ++ " " ++ show_rows(t)

def show_mat(tag: String, a: L.Mat) -> String:
  L.Mat{m, n, rows} = a
  tag ++ " " ++ U32.show(m) ++ " " ++ U32.show(n) ++ " " ++ show_rows(rows) ++ "\n"

def show_mmat(tag: String, mm: Maybe<&2, L.Mat>) -> String:
  match mm:
    case None{}:
      tag ++ " none\n"
    case Some{a}:
      show_mat(tag, a)

# ---- mode 0: core ops

def run_core(
  ra: Result<&1, &1, U32 & String, L.Mat>,
  rb: Result<&1, &1, U32 & String, L.Mat>,
  rc: Result<&1, &1, U32 & String, L.Mat>,
  rx: Result<&1, &1, U32 & String, L.Vec>,
  ry: Result<&1, &1, U32 & String, L.Vec>,
  rw: Result<&1, &1, U32 & String, L.Vec>
) -> String:
  match ra rb rc rx ry rw:
    case Done{+a} Done{+b} Done{+c} Done{+x} Done{+y} Done{+w}:
      s0 = show_mf32("dot", L.dot(x, y))
      s1 = "norm1 " ++ F32.show(L.norm1(x)) ++ "\n"
      s2 = "norm2 " ++ F32.show(L.norm2(x)) ++ "\n"
      s3 = show_vec("vscale", L.vscale(2.5, x))
      s4 = show_mvec("vadd", L.vadd(x, y))
      s5 = show_mvec("vsub", L.vsub(x, y))
      s6 = show_mvec("axpy", L.axpy((0.0 - 1.5 : F32), x, y))
      s7 = show_mvec("vmul", L.vmul(x, y))
      s8 = show_mvec("vdiv", L.vdiv(x, y))
      s9 = show_mat("outer", L.outer(x, w))
      s10 = show_mat("scale", L.scale(0.5, a))
      s11 = show_mmat("madd", L.madd(a, a))
      s12 = show_mmat("msub", L.msub(a, L.scale(0.25, a)))
      s13 = "frob " ++ F32.show(L.frobenius(a)) ++ "\n"
      s14 = show_mf32("trace_sq", L.trace(c))
      s15 = show_mf32("trace_rect", L.trace(a))
      s16 = show_mat("transpose", L.transpose(a))
      s17 = show_mat("submatrix", L.submatrix(a, 1, 2, 1, 3))
      s18 = show_mmat("diag_mul", L.diag_mul(w, a))
      s19 = show_mmat("mul_diag", L.mul_diag(a, x))
      s20 = show_mvec("matvec", L.matvec(a, x))
      s21 = show_mvec("matvec_t", L.matvec_t(a, w))
      s22 = show_mmat("matmul", L.matmul(a, b))
      s23 = show_mmat("matmul_bad", L.matmul(a, a))
      s24 = show_mat("gram", L.gram(a))
      s25 = show_mmat("wgram", L.wgram(a, w))
      s26 = show_mf32("quad_form", L.quad_form(x, c))
      s27 = show_mat("eye", L.Mat.eye(4))
      s28 = show_mat("diag", L.Mat.diag(x))
      s29 = show_vec("diag_vec", L.Mat.diag_vec(a))
      s0 ++ s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6 ++ s7 ++ s8 ++ s9 ++ s10 ++ s11 ++ s12 ++ s13 ++ s14 ++ s15 ++ s16 ++ s17 ++ s18 ++ s19 ++ s20 ++ s21 ++ s22 ++ s23 ++ s24 ++ s25 ++ s26 ++ s27 ++ s28 ++ s29
    case _ _ _ _ _ _:
      "load_failed\n"

# ---- mode 1: Cholesky & triangular solves

def run_chol_with_l(ml: Maybe<&2, L.Mat>, +bv: L.Vec, +bm: L.Mat, +bad_tri: L.Mat, +n: U32) -> String:
  match ml:
    case None{}:
      "chol none\n"
    case Some{+l}:
      +lt = L.transpose(l)
      +bt = L.transpose(bad_tri)
      s0 = show_mat("chol", l)
      s1 = show_mf32("chol_logdet", L.cholesky_logdet(l))
      s2 = show_mf32("chol_logdet_nonsq", L.cholesky_logdet(bm))
      s3 = show_mf32("chol_logdet_bad", L.cholesky_logdet(bad_tri))
      s4 = show_mvec("solve_lower", L.solve_lower(l, bv))
      s5 = show_mvec("solve_upper", L.solve_upper(lt, bv))
      s6 = show_mmat("solve_lower_mat", L.solve_lower_mat(l, bm))
      s7 = show_mmat("solve_upper_mat", L.solve_upper_mat(lt, bm))
      s8 = show_mvec("chol_solve", L.cholesky_solve(l, bv))
      s9 = show_mmat("chol_solve_mat", L.cholesky_solve_mat(l, bm))
      s10 = show_mmat("chol_inv", L.cholesky_solve_mat(l, L.Mat.eye(n)))
      s11 = show_mvec("solve_lower_zero", L.solve_lower(bad_tri, bv))
      s12 = show_mvec("solve_upper_zero", L.solve_upper(bt, bv))
      s13 = show_mvec("solve_lower_bad", L.solve_lower(bm, bv))
      s14 = show_mvec("solve_upper_bad", L.solve_upper(bm, bv))
      s15 = show_mvec("chol_solve_bad", L.cholesky_solve(bm, bv))
      s0 ++ s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6 ++ s7 ++ s8 ++ s9 ++ s10 ++ s11 ++ s12 ++ s13 ++ s14 ++ s15

def run_chol(
  ra: Result<&1, &1, U32 & String, L.Mat>,
  rbv: Result<&1, &1, U32 & String, L.Vec>,
  rbm: Result<&1, &1, U32 & String, L.Mat>,
  rns: Result<&1, &1, U32 & String, L.Mat>,
  rbt: Result<&1, &1, U32 & String, L.Mat>,
  +n: U32
) -> String:
  match ra rbv rbm rns rbt:
    case Done{a} Done{+bv} Done{+bm} Done{nonspd} Done{+bad_tri}:
      p0 = show_mmat("chol_nonspd", L.cholesky(nonspd))
      p1 = show_mmat("chol_nonsq", L.cholesky(bm))
      p0 ++ p1 ++ run_chol_with_l(L.cholesky(a), bv, bm, bad_tri, n)
    case _ _ _ _ _:
      "load_failed\n"

# ---- mode 2: Woodbury & determinant lemma

def run_woodbury(
  rd: Result<&1, &1, U32 & String, L.Vec>,
  ru: Result<&1, &1, U32 & String, L.Mat>,
  rm: Result<&1, &1, U32 & String, L.Mat>,
  rb: Result<&1, &1, U32 & String, L.Vec>
) -> String:
  match rd ru rm rb:
    case Done{+d} Done{+u} Done{+m} Done{b}:
      s0 = show_mvec("wb_solve", L.woodbury_solve(d, u, m, b))
      s1 = show_mf32("wb_logdet", L.woodbury_logdet(d, u, m))
      s0 ++ s1
    case _ _ _ _:
      "load_failed\n"

# ---- mode 3: QR, OLS, WLS, multi-RHS LS, orthogonal projection

def run_qr_with(mqr: Maybe<&2, L.QR>, +x: L.Vec) -> String:
  match mqr:
    case None{}:
      "qr_q none\nqr_r none\nproject_orth none\n"
    case Some{qr}:
      L.QR{+q, r} = qr
      s0 = show_mat("qr_q", q)
      s1 = show_mat("qr_r", r)
      s2 = show_mvec("project_orth", L.project_orth(q, x))
      s3 = show_mvec("project_orth_bad", L.project_orth(q, L.Vec{0, Nil{}}))
      s0 ++ s1 ++ s2 ++ s3

def run_qr(
  ra: Result<&1, &1, U32 & String, L.Mat>,
  rb: Result<&1, &1, U32 & String, L.Vec>,
  rw: Result<&1, &1, U32 & String, L.Vec>,
  rbm: Result<&1, &1, U32 & String, L.Mat>,
  rx: Result<&1, &1, U32 & String, L.Vec>
) -> String:
  match ra rb rw rbm rx:
    case Done{+a} Done{+b} Done{w} Done{bm} Done{x}:
      s0 = run_qr_with(L.qr_thin(a), x)
      s1 = show_mvec("lstsq", L.lstsq(a, b))
      s2 = show_mvec("wlstsq", L.wlstsq(a, w, b))
      s3 = show_mmat("lstsq_mat", L.lstsq_mat(a, bm))
      s0 ++ s1 ++ s2 ++ s3
    case _ _ _ _ _:
      "load_failed\n"

# ---- mode 4: equality-constrained least squares

def run_constrained(
  ra: Result<&1, &1, U32 & String, L.Mat>,
  rb: Result<&1, &1, U32 & String, L.Vec>,
  rc: Result<&1, &1, U32 & String, L.Mat>,
  rd: Result<&1, &1, U32 & String, L.Vec>
) -> String:
  match ra rb rc rd:
    case Done{a} Done{b} Done{c} Done{d}:
      show_mvec("lstsq_c", L.lstsq_constrained(a, b, c, d))
    case _ _ _ _:
      "load_failed\n"

# ---- mode 5: sym_eigen & spd_pow

def show_meig(me: Maybe<&2, L.Eigen>) -> String:
  match me:
    case None{}:
      "eig_vals none\neig_vecs none\n"
    case Some{e}:
      L.Eigen{vals, vecs} = e
      show_vec("eig_vals", vals) ++ show_mat("eig_vecs", vecs)

def run_eigen(ra: Result<&1, &1, U32 & String, L.Mat>) -> String:
  match ra:
    case Done{+a}:
      s0 = show_meig(L.sym_eigen(a))
      s1 = show_mmat("spd_sqrt", L.spd_pow(a, 0.5))
      s2 = show_mmat("spd_inv_sqrt", L.spd_pow(a, F32.neg(0.5)))
      s3 = show_mmat("spd_inv", L.spd_pow(a, F32.neg(1.0)))
      s4 = show_mmat("spd_cube_rt", L.spd_pow(a, (1.0 / 3.0 : F32)))
      s0 ++ s1 ++ s2 ++ s3 ++ s4
    case _:
      "load_failed\n"

# ---- mode 6: svd_thin & pinv

def show_svd(sv: L.SVD) -> String:
  L.SVD{u, s, vt} = sv
  show_mat("svd_u", u) ++ show_vec("svd_s", s) ++ show_mat("svd_vt", vt)

def run_svd(ra: Result<&1, &1, U32 & String, L.Mat>) -> String:
  match ra:
    case Done{+a}:
      show_svd(L.svd_thin(a)) ++ show_mat("pinv", L.pinv(a, 1.0e-5))
    case _:
      "load_failed\n"

# ---- mode 7: procrustes

def run_procrustes(
  ra: Result<&1, &1, U32 & String, L.Mat>,
  rb: Result<&1, &1, U32 & String, L.Mat>
) -> String:
  match ra rb:
    case Done{a} Done{b}:
      show_mmat("procrustes", L.procrustes(a, b))
    case _ _:
      "load_failed\n"

# ---- CLI dispatch

def num(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{n}:
      n
    case None{}:
      0

def tu(s: String) -> U32:
  num(U32.read(s))

def go_core(rest: List<String>) -> IO(Unit):
  match rest:
    case pa <> pb <> pc <> px <> py <> pw <> ms <> ns <> ks <> _:
      +m = tu(ms)
      +n = tu(ns)
      +k = tu(ks)
      do IO<Unit>:
        ra : Result<&1, &1, U32 & String, L.Mat> <- I.Mat.load(pa, m, n)
        rb : Result<&1, &1, U32 & String, L.Mat> <- I.Mat.load(pb, n, k)
        rc : Result<&1, &1, U32 & String, L.Mat> <- I.Mat.load(pc, n, n)
        rx : Result<&1, &1, U32 & String, L.Vec> <- I.Vec.load(px, n)
        ry : Result<&1, &1, U32 & String, L.Vec> <- I.Vec.load(py, n)
        rw : Result<&1, &1, U32 & String, L.Vec> <- I.Vec.load(pw, m)
        IO.write(run_core(ra, rb, rc, rx, ry, rw))
    case _:
      IO.print("usage: 0 a b c x y w m n k")

def go_chol(rest: List<String>) -> IO(Unit):
  match rest:
    case pa <> pbv <> pbm <> pns <> pbt <> ns <> ks <> _:
      +n = tu(ns)
      +k = tu(ks)
      do IO<Unit>:
        ra : Result<&1, &1, U32 & String, L.Mat> <- I.Mat.load(pa, n, n)
        rbv : Result<&1, &1, U32 & String, L.Vec> <- I.Vec.load(pbv, n)
        rbm : Result<&1, &1, U32 & String, L.Mat> <- I.Mat.load(pbm, n, k)
        rns : Result<&1, &1, U32 & String, L.Mat> <- I.Mat.load(pns, n, n)
        rbt : Result<&1, &1, U32 & String, L.Mat> <- I.Mat.load(pbt, n, n)
        IO.write(run_chol(ra, rbv, rbm, rns, rbt, n))
    case _:
      IO.print("usage: 1 a bv bm nonspd bad_tri n k")

def go_woodbury(rest: List<String>) -> IO(Unit):
  match rest:
    case pd <> pu <> pm <> pb <> nds <> nus <> kus <> mms <> mns <> nbs <> _:
      +nd = tu(nds)
      +nu = tu(nus)
      +ku = tu(kus)
      +mm = tu(mms)
      +mn = tu(mns)
      +nb = tu(nbs)
      do IO<Unit>:
        rd : Result<&1, &1, U32 & String, L.Vec> <- I.Vec.load(pd, nd)
        ru : Result<&1, &1, U32 & String, L.Mat> <- I.Mat.load(pu, nu, ku)
        rm : Result<&1, &1, U32 & String, L.Mat> <- I.Mat.load(pm, mm, mn)
        rb : Result<&1, &1, U32 & String, L.Vec> <- I.Vec.load(pb, nb)
        IO.write(run_woodbury(rd, ru, rm, rb))
    case _:
      IO.print("usage: 2 d u m b nd nu ku mm mn nb")

def go_qr(rest: List<String>) -> IO(Unit):
  match rest:
    case pa <> pb <> pw <> pbm <> px <> ms <> ns <> ks <> _:
      +m = tu(ms)
      +n = tu(ns)
      +k = tu(ks)
      do IO<Unit>:
        ra : Result<&1, &1, U32 & String, L.Mat> <- I.Mat.load(pa, m, n)
        rb : Result<&1, &1, U32 & String, L.Vec> <- I.Vec.load(pb, m)
        rw : Result<&1, &1, U32 & String, L.Vec> <- I.Vec.load(pw, m)
        rbm : Result<&1, &1, U32 & String, L.Mat> <- I.Mat.load(pbm, m, k)
        rx : Result<&1, &1, U32 & String, L.Vec> <- I.Vec.load(px, m)
        IO.write(run_qr(ra, rb, rw, rbm, rx))
    case _:
      IO.print("usage: 3 a b w bm x m n k")

def go_constrained(rest: List<String>) -> IO(Unit):
  match rest:
    case pa <> pb <> pc <> pd <> mas <> nas <> nbs <> cms <> cps <> nds <> _:
      +ma = tu(mas)
      +na = tu(nas)
      +nb = tu(nbs)
      +cm = tu(cms)
      +cp = tu(cps)
      +nd = tu(nds)
      do IO<Unit>:
        ra : Result<&1, &1, U32 & String, L.Mat> <- I.Mat.load(pa, ma, na)
        rb : Result<&1, &1, U32 & String, L.Vec> <- I.Vec.load(pb, nb)
        rc : Result<&1, &1, U32 & String, L.Mat> <- I.Mat.load(pc, cm, cp)
        rd : Result<&1, &1, U32 & String, L.Vec> <- I.Vec.load(pd, nd)
        IO.write(run_constrained(ra, rb, rc, rd))
    case _:
      IO.print("usage: 4 a b c d ma na nb cm cp nd")

def go_eigen(rest: List<String>) -> IO(Unit):
  match rest:
    case pa <> ms <> ns <> _:
      +m = tu(ms)
      +n = tu(ns)
      do IO<Unit>:
        ra : Result<&1, &1, U32 & String, L.Mat> <- I.Mat.load(pa, m, n)
        IO.write(run_eigen(ra))
    case _:
      IO.print("usage: 5 a m n")

def go_svd(rest: List<String>) -> IO(Unit):
  match rest:
    case pa <> ms <> ns <> _:
      +m = tu(ms)
      +n = tu(ns)
      do IO<Unit>:
        ra : Result<&1, &1, U32 & String, L.Mat> <- I.Mat.load(pa, m, n)
        IO.write(run_svd(ra))
    case _:
      IO.print("usage: 6 a m n")

def go_procrustes(rest: List<String>) -> IO(Unit):
  match rest:
    case pa <> pb <> mas <> nas <> mbs <> nbs <> _:
      +ma = tu(mas)
      +na = tu(nas)
      +mb = tu(mbs)
      +nb = tu(nbs)
      do IO<Unit>:
        ra : Result<&1, &1, U32 & String, L.Mat> <- I.Mat.load(pa, ma, na)
        rb : Result<&1, &1, U32 & String, L.Mat> <- I.Mat.load(pb, mb, nb)
        IO.write(run_procrustes(ra, rb))
    case _:
      IO.print("usage: 7 a b ma na mb nb")

def go.m67(is_svd: Bool, rest: List<String>) -> IO(Unit):
  match is_svd:
    case True{}:
      go_svd(rest)
    case False{}:
      go_procrustes(rest)

def go.m5(is_eig: Bool, is_svd: Bool, rest: List<String>) -> IO(Unit):
  match is_eig:
    case True{}:
      go_eigen(rest)
    case False{}:
      go.m67(is_svd, rest)

def go.m4(is_con: Bool, is_eig: Bool, is_svd: Bool, rest: List<String>) -> IO(Unit):
  match is_con:
    case True{}:
      go_constrained(rest)
    case False{}:
      go.m5(is_eig, is_svd, rest)

def go.m3(is_qr: Bool, is_con: Bool, is_eig: Bool, is_svd: Bool, rest: List<String>) -> IO(Unit):
  match is_qr:
    case True{}:
      go_qr(rest)
    case False{}:
      go.m4(is_con, is_eig, is_svd, rest)

def go.m2(is_wb: Bool, is_qr: Bool, is_con: Bool, is_eig: Bool, is_svd: Bool, rest: List<String>) -> IO(Unit):
  match is_wb:
    case True{}:
      go_woodbury(rest)
    case False{}:
      go.m3(is_qr, is_con, is_eig, is_svd, rest)

def go.m1(is_chol: Bool, is_wb: Bool, is_qr: Bool, is_con: Bool, is_eig: Bool, is_svd: Bool, rest: List<String>) -> IO(Unit):
  match is_chol:
    case True{}:
      go_chol(rest)
    case False{}:
      go.m2(is_wb, is_qr, is_con, is_eig, is_svd, rest)

def go.dispatch(is_core: Bool, is_chol: Bool, is_wb: Bool, is_qr: Bool, is_con: Bool, is_eig: Bool, is_svd: Bool, rest: List<String>) -> IO(Unit):
  match is_core:
    case True{}:
      go_core(rest)
    case False{}:
      go.m1(is_chol, is_wb, is_qr, is_con, is_eig, is_svd, rest)

def go(args: List<String>) -> IO(Unit):
  match args:
    case _ <> mode <> rest:
      +m = tu(mode)
      go.dispatch(U32.is_eq(m, 0), U32.is_eq(m, 1), U32.is_eq(m, 2), U32.is_eq(m, 3), U32.is_eq(m, 4), U32.is_eq(m, 5), U32.is_eq(m, 6), rest)
    case _:
      IO.print("usage: <mode: 0..7> ...")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
