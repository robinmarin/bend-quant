# End-to-end benchmark of the actual linalg.bend library at Paleologo quant sizes.
# Measures real public API calls (including Data <-> Array boundaries) with warmup
# and checksum accumulation to prevent dead-code elimination.
import Base
import ../linalg.bend as L

def lcg(+s: U32) -> U32:
  ((s * 1664525) + 1013904223 : U32)

def unif(+s: U32) -> F32:
  ((U32.to_f32((s >> 8n : U32)) / 16777216.0) - 0.5 : F32)

def gen_list(rem: Nat, +s: U32) -> List<&2, F32>:
  match rem:
    case 0n:
      Nil{}
    case 1n+p:
      +s1 = lcg(s)
      unif(s1) <> gen_list(p, s1)

def gen_pos_list(rem: Nat, +s: U32) -> List<&2, F32>:
  match rem:
    case 0n:
      Nil{}
    case 1n+p:
      +s1 = lcg(s)
      (0.5 + F32.abs(unif(s1)) : F32) <> gen_pos_list(p, s1)

def gen_rows(rem: Nat, +n: Nat, +s: U32) -> List<&2, List<&2, F32>>:
  match rem:
    case 0n:
      Nil{}
    case 1n+p:
      +s1 = lcg(((s * 2654435761) + 17 : U32))
      gen_list(n, s1) <> gen_rows(p, n, s1)

def gen_mat(+m: U32, +n: U32, +s: U32) -> L.Mat:
  L.Mat{m, n, gen_rows(U32.to_nat(m), U32.to_nat(n), s)}

def gen_vec(+n: U32, +s: U32) -> L.Vec:
  L.Vec{n, gen_list(U32.to_nat(n), s)}

def gen_pos_vec(+n: U32, +s: U32) -> L.Vec:
  L.Vec{n, gen_pos_list(U32.to_nat(n), s)}

def gen_spd_row(rem: Nat, +i: U32, +j: U32, +s: U32) -> List<&2, F32>:
  match rem:
    case 0n:
      Nil{}
    case 1n+p:
      +lo = U32.min(i, j)
      +hi = U32.max(i, j)
      +h = lcg((((hi * 73856093) .^. (lo * 19349663)) + s : U32))
      +val = Bool.pick(F32, U32.is_eq(i, j), (10.0 + (U32.to_f32(i) * 0.25) : F32), (unif(h) * 0.15 : F32))
      val <> gen_spd_row(p, i, (j + 1 : U32), s)

def gen_spd_rows(rem: Nat, +i: U32, +k: U32, +s: U32) -> List<&2, List<&2, F32>>:
  match rem:
    case 0n:
      Nil{}
    case 1n+p:
      gen_spd_row(U32.to_nat(k), i, 0, s) <> gen_spd_rows(p, (i + 1 : U32), k, s)

def gen_spd(+k: U32, +s: U32) -> L.Mat:
  L.Mat{k, k, gen_spd_rows(U32.to_nat(k), 0, k, s)}

# Lightweight checksum extractors so results are forced to normal form
def chk_list(xs: List<&2, F32>) -> F32:
  match xs:
    case Nil{}:
      0.0
    case Con{x, _}:
      x

def chk_vec(v: L.Vec) -> F32:
  L.Vec{_, xs} = v
  chk_list(xs)

def chk_mvec(mv: Maybe<&2, L.Vec>) -> F32:
  match mv:
    case None{}:
      0.0
    case Some{v}:
      chk_vec(v)

def chk_mf32(mv: Maybe<&2, F32>) -> F32:
  match mv:
    case None{}:
      0.0
    case Some{x}:
      x

def chk_mat(a: L.Mat) -> F32:
  L.Mat{_, _, rows} = a
  match rows:
    case Nil{}:
      0.0
    case Con{r, _}:
      chk_list(r)

def chk_mmat(mm: Maybe<&2, L.Mat>) -> F32:
  match mm:
    case None{}:
      0.0
    case Some{a}:
      chk_mat(a)

def chk_mqr(mqr: Maybe<&2, L.QR>) -> F32:
  match mqr:
    case None{}:
      0.0
    case Some{L.QR{q, r}}:
      (chk_mat(q) + chk_mat(r) : F32)

def chk_meig(me: Maybe<&2, L.Eigen>) -> F32:
  match me:
    case None{}:
      0.0
    case Some{L.Eigen{vals, vecs}}:
      (chk_vec(vals) + chk_mat(vecs) : F32)

def chk_svd(sv: L.SVD) -> F32:
  L.SVD{u, s, vt} = sv
  ((chk_mat(u) + chk_vec(s)) + chk_mat(vt) : F32)

# Benchmark loops
def rep_matvec(rem: Nat, +a: L.Mat, +x: L.Vec, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_matvec(p, a, x, (acc + chk_mvec(L.matvec(a, x)) : F32))

def rep_matmul(rem: Nat, +a: L.Mat, +b: L.Mat, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_matmul(p, a, b, (acc + chk_mmat(L.matmul(a, b)) : F32))

def rep_gram(rem: Nat, +a: L.Mat, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_gram(p, a, (acc + chk_mat(L.gram(a)) : F32))

def rep_wgram(rem: Nat, +a: L.Mat, +w: L.Vec, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_wgram(p, a, w, (acc + chk_mmat(L.wgram(a, w)) : F32))

def rep_chol(rem: Nat, +s: L.Mat, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_chol(p, s, (acc + chk_mmat(L.cholesky(s)) : F32))

def rep_chol_solve(rem: Nat, +l: L.Mat, +b: L.Vec, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_chol_solve(p, l, b, (acc + chk_mvec(L.cholesky_solve(l, b)) : F32))

def rep_wb_solve(rem: Nat, +d: L.Vec, +u: L.Mat, +m: L.Mat, +b: L.Vec, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_wb_solve(p, d, u, m, b, (acc + chk_mvec(L.woodbury_solve(d, u, m, b)) : F32))

def rep_wb_logdet(rem: Nat, +d: L.Vec, +u: L.Mat, +m: L.Mat, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_wb_logdet(p, d, u, m, (acc + chk_mf32(L.woodbury_logdet(d, u, m)) : F32))

def rep_qr(rem: Nat, +a: L.Mat, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_qr(p, a, (acc + chk_mqr(L.qr_thin(a)) : F32))

def rep_lstsq(rem: Nat, +a: L.Mat, +b: L.Vec, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_lstsq(p, a, b, (acc + chk_mvec(L.lstsq(a, b)) : F32))

def rep_wlstsq(rem: Nat, +a: L.Mat, +w: L.Vec, +b: L.Vec, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_wlstsq(p, a, w, b, (acc + chk_mvec(L.wlstsq(a, w, b)) : F32))

def rep_proj(rem: Nat, +q: L.Mat, +x: L.Vec, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_proj(p, q, x, (acc + chk_mvec(L.project_orth(q, x)) : F32))

def rep_lstsq_c(rem: Nat, +a: L.Mat, +b: L.Vec, +c: L.Mat, +d: L.Vec, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_lstsq_c(p, a, b, c, d, (acc + chk_mvec(L.lstsq_constrained(a, b, c, d)) : F32))

def rep_eigen(rem: Nat, +s: L.Mat, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_eigen(p, s, (acc + chk_meig(L.sym_eigen(s)) : F32))

def rep_spd_pow(rem: Nat, +s: L.Mat, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_spd_pow(p, s, (acc + chk_mmat(L.spd_pow(s, F32.neg(0.5))) : F32))

def rep_svd(rem: Nat, +a: L.Mat, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_svd(p, a, (acc + chk_svd(L.svd_thin(a)) : F32))

def rep_pinv(rem: Nat, +a: L.Mat, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_pinv(p, a, (acc + chk_mat(L.pinv(a, 1.0e-5)) : F32))

def rep_proc(rem: Nat, +a: L.Mat, +b: L.Mat, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_proc(p, a, b, (acc + chk_mmat(L.procrustes(a, b)) : F32))

def unwrap_mat(mm: Maybe<&2, L.Mat>) -> L.Mat:
  match mm:
    case Some{m}:
      m
    case None{}:
      L.Mat.eye(1)

def unwrap_q(mqr: Maybe<&2, L.QR>) -> L.Mat:
  match mqr:
    case Some{L.QR{q, _}}:
      q
    case None{}:
      L.Mat.eye(1)

def report(name: String, reps: Nat, t0: Nat, t1: Nat, chk: F32) -> IO(Unit):
  IO.print(name ++ " reps=" ++ Nat.show(reps) ++ " total_ms=" ++ Nat.show(Nat.sub(t1, t0)) ++ " chk=" ++ F32.show(chk))

def main() -> IO(Unit):
  do IO<Unit>:
    +b1000 : L.Mat = gen_mat(1000, 50, 101)
    +omega50 : L.Mat = gen_spd(50, 202)
    +l50 : L.Mat = unwrap_mat(L.cholesky(omega50))
    +q1000 : L.Mat = unwrap_q(L.qr_thin(b1000))
    +x50 : L.Vec = gen_vec(50, 303)
    +y1000 : L.Vec = gen_vec(1000, 404)
    +d1000 : L.Vec = gen_pos_vec(1000, 505)
    +w1000 : L.Vec = gen_pos_vec(1000, 606)
    +a500 : L.Mat = gen_mat(500, 30, 707)
    +b500 : L.Mat = gen_mat(500, 30, 808)
    +a500_t : L.Mat = L.transpose(a500)
    +y500 : L.Vec = gen_vec(500, 909)
    +c30 : L.Mat = gen_mat(30, 3, 1010)
    +dc3 : L.Vec = gen_vec(3, 1111)
    +a200 : L.Mat = gen_mat(200, 30, 1212)

    +t0 : Nat <- IO.now()
    +c0 : F32 = rep_matvec(20n, b1000, x50, 0.0)
    +t1 : Nat <- IO.now()
    report("matvec_1000x50", 20n, t0, t1, c0)

    +t2 : Nat <- IO.now()
    +c1 : F32 = rep_matmul(5n, b1000, omega50, 0.0)
    +t3 : Nat <- IO.now()
    report("matmul_1000x50x50", 5n, t2, t3, c1)

    +t4 : Nat <- IO.now()
    +c2 : F32 = rep_gram(10n, b1000, 0.0)
    +t5 : Nat <- IO.now()
    report("gram_1000x50", 10n, t4, t5, c2)

    +t6 : Nat <- IO.now()
    +c3 : F32 = rep_wgram(10n, b1000, w1000, 0.0)
    +t7 : Nat <- IO.now()
    report("wgram_1000x50", 10n, t6, t7, c3)

    +t8 : Nat <- IO.now()
    +c4 : F32 = rep_chol(100n, omega50, 0.0)
    +t9 : Nat <- IO.now()
    report("cholesky_50x50", 100n, t8, t9, c4)

    +t10 : Nat <- IO.now()
    +c5 : F32 = rep_chol_solve(100n, l50, x50, 0.0)
    +t11 : Nat <- IO.now()
    report("chol_solve_50x50", 100n, t10, t11, c5)

    +t12 : Nat <- IO.now()
    +c6 : F32 = rep_wb_solve(5n, d1000, b1000, omega50, y1000, 0.0)
    +t13 : Nat <- IO.now()
    report("woodbury_solve_1000x50", 5n, t12, t13, c6)

    +t14 : Nat <- IO.now()
    +c7 : F32 = rep_wb_logdet(5n, d1000, b1000, omega50, 0.0)
    +t15 : Nat <- IO.now()
    report("woodbury_logdet_1000x50", 5n, t14, t15, c7)

    +t16 : Nat <- IO.now()
    +c8 : F32 = rep_qr(5n, b1000, 0.0)
    +t17 : Nat <- IO.now()
    report("qr_thin_1000x50", 5n, t16, t17, c8)

    +t18 : Nat <- IO.now()
    +c9 : F32 = rep_lstsq(5n, b1000, y1000, 0.0)
    +t19 : Nat <- IO.now()
    report("lstsq_1000x50", 5n, t18, t19, c9)

    +t20 : Nat <- IO.now()
    +c10 : F32 = rep_wlstsq(5n, b1000, w1000, y1000, 0.0)
    +t21 : Nat <- IO.now()
    report("wlstsq_1000x50", 5n, t20, t21, c10)

    +t22 : Nat <- IO.now()
    +c11 : F32 = rep_proj(20n, q1000, y1000, 0.0)
    +t23 : Nat <- IO.now()
    report("project_orth_1000x50", 20n, t22, t23, c11)

    +t24 : Nat <- IO.now()
    +c12 : F32 = rep_lstsq_c(5n, a500, y500, c30, dc3, 0.0)
    +t25 : Nat <- IO.now()
    report("lstsq_con_500x30_p3", 5n, t24, t25, c12)

    +t26 : Nat <- IO.now()
    +c13 : F32 = rep_eigen(20n, omega50, 0.0)
    +t27 : Nat <- IO.now()
    report("sym_eigen_50x50", 20n, t26, t27, c13)

    +t28 : Nat <- IO.now()
    +c14 : F32 = rep_spd_pow(10n, omega50, 0.0)
    +t29 : Nat <- IO.now()
    report("spd_pow_50x50", 10n, t28, t29, c14)

    +t30 : Nat <- IO.now()
    +c15 : F32 = rep_svd(5n, a500, 0.0)
    +t31 : Nat <- IO.now()
    report("svd_thin_500x30", 5n, t30, t31, c15)

    +t32 : Nat <- IO.now()
    +c16 : F32 = rep_svd(5n, a500_t, 0.0)
    +t33 : Nat <- IO.now()
    report("svd_thin_30x500", 5n, t32, t33, c16)

    +t34 : Nat <- IO.now()
    +c17 : F32 = rep_pinv(5n, a200, 0.0)
    +t35 : Nat <- IO.now()
    report("pinv_200x30", 5n, t34, t35, c17)

    +t36 : Nat <- IO.now()
    +c18 : F32 = rep_proc(5n, a500, b500, 0.0)
    +t37 : Nat <- IO.now()
    report("procrustes_500x30", 5n, t36, t37, c18)
