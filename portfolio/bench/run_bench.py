#!/usr/bin/env python3
"""Benchmark bend-quant-portfolio vs NumPy (and OSQP if installed)."""
import argparse
import os
import platform
import subprocess
import tempfile
import time
import numpy as np

try:
    import osqp
    import scipy.sparse as sp
    HAS_OSQP = True
except ImportError:
    HAS_OSQP = False

ROOT = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(ROOT, "out", "bench_portfolio")


def write_f32(path, arr):
    np.asarray(arr, dtype="<f4").tofile(path)


def make_fm(rng, n, k):
    b = (rng.standard_normal((n, k)) * 0.5).astype(np.float32)
    q, _ = np.linalg.qr(rng.standard_normal((k, k)))
    cov_f = (q @ np.diag(np.geomspace(1.0, 50.0, k) * 1e-4) @ q.T).astype(np.float32)
    cov_f = 0.5 * (cov_f + cov_f.T)
    d = np.exp(rng.uniform(-6.0, -3.5, size=n)).astype(np.float32)
    return b, cov_f, d


def rts_prefix(threads):
    if threads and threads > 0:
        return ["+RTS", "--threads", str(threads), "-RTS"]
    return []


def time_bend(args, reps, rep_idx=1, threads=0):
    pref = rts_prefix(threads)
    a1 = list(args)
    a1[rep_idx] = "1"
    t0 = time.perf_counter()
    subprocess.run([BIN, *pref, *a1], capture_output=True, text=True, check=True)
    t1 = time.perf_counter() - t0

    a2 = list(args)
    a2[rep_idx] = str(1 + reps)
    t0 = time.perf_counter()
    r2 = subprocess.run([BIN, *pref, *a2], capture_output=True, text=True, check=True)
    t2 = time.perf_counter() - t0
    return max((t2 - t1) / reps, 1e-6) * 1000.0, r2.stdout.strip()


def time_py(fn, reps=20):
    fn()
    t0 = time.perf_counter()
    for _ in range(reps):
        fn()
    return (time.perf_counter() - t0) / reps * 1000.0


def bench_osqp_mvo(ba, cfa, da, aa, w0a, lwa, uwa, Aa, lca, uca, c1a, c2a, rho, gmv, reps=5):
    """Sparse factor-model OSQP formulation matching mvo_constrained exactly:
    Variables x = [w (N), f (K), t (N), g (N)]:
      min 0.5*rho*(w^T D w + f^T cov_f f) + 0.5*sum(c2*(w-w0)^2) - a^T w + c1^T t
      s.t. f = B^T w,
           l_w <= w <= u_w,
           l_c <= A w <= u_c,
           -t <= w - w0 <= t  (i.e. w - t <= w0, -w - t <= -w0),
           -g <= w <= g,      (i.e. w - g <= 0, -w - g <= 0),
           1^T g <= gmv.
    """
    n, k = ba.shape
    m = Aa.shape[0]
    B = ba.astype(np.float64)
    Cf = cfa.astype(np.float64)
    D = da.astype(np.float64)
    a = aa.astype(np.float64)
    w0 = w0a.astype(np.float64)
    lw = lwa.astype(np.float64)
    uw = uwa.astype(np.float64)
    A = Aa.astype(np.float64)
    lc = lca.astype(np.float64)
    uc = uca.astype(np.float64)
    c1 = c1a.astype(np.float64)
    c2 = c2a.astype(np.float64)

    def build_and_solve():
        P_w = sp.diags(rho * D + c2, format="csc")
        P_f = sp.csc_matrix(rho * Cf)
        P_z = sp.csc_matrix((2 * n, 2 * n))
        P = sp.block_diag([P_w, P_f, P_z], format="csc")
        q = np.concatenate([-a - c2 * w0, np.zeros(k), c1, np.zeros(n)])

        I_n = sp.eye(n, format="csc")
        I_k = sp.eye(k, format="csc")
        Z_nk = sp.csc_matrix((n, k))
        Z_nn = sp.csc_matrix((n, n))
        Z_kn = sp.csc_matrix((k, n))
        Z_mk = sp.csc_matrix((m, k))
        Z_mn = sp.csc_matrix((m, n))

        # Rows:
        # 1. B^T w - f = 0
        # 2. w in [lw, uw]
        # 3. A w in [lc, uc]
        # 4. w - t <= w0
        # 5. -w - t <= -w0
        # 6. w - g <= 0
        # 7. -w - g <= 0
        # 8. 1^T g <= gmv
        C = sp.bmat([
            [sp.csc_matrix(B.T), -I_k, Z_kn, Z_kn],
            [I_n, Z_nk, Z_nn, Z_nn],
            [sp.csc_matrix(A), Z_mk, Z_mn, Z_mn],
            [I_n, Z_nk, -I_n, Z_nn],
            [-I_n, Z_nk, -I_n, Z_nn],
            [I_n, Z_nk, Z_nn, -I_n],
            [-I_n, Z_nk, Z_nn, -I_n],
            [sp.csc_matrix((1, n)), sp.csc_matrix((1, k)), sp.csc_matrix((1, n)), sp.csc_matrix(np.ones((1, n)))],
        ], format="csc")

        inf = np.inf
        lb = np.concatenate([
            np.zeros(k), lw, lc,
            np.full(n, -inf), np.full(n, -inf),
            np.full(n, -inf), np.full(n, -inf),
            np.array([-inf]),
        ])
        ub = np.concatenate([
            np.zeros(k), uw, uc,
            w0, -w0,
            np.zeros(n), np.zeros(n),
            np.array([float(gmv)]),
        ])

        prob = osqp.OSQP()
        prob.setup(P, q, C, lb, ub, eps_abs=1e-5, eps_rel=1e-4, verbose=False, polish=False)
        res = prob.solve()
        return res

    res = build_and_solve()
    t0 = time.perf_counter()
    for _ in range(reps):
        res = build_and_solve()
    ms = (time.perf_counter() - t0) / reps * 1000.0
    w = res.x[:n]
    return ms, res.info.iter, float(np.sum(w))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--threads", type=int, default=0, help="Bend RTS threads (0 = runtime default)")
    ap.add_argument("--skip-py", action="store_true", help="Skip NumPy/OSQP timings")
    args = ap.parse_args()

    rng = np.random.default_rng(42)
    tlabel = f"Bend {args.threads}t" if args.threads > 0 else "Bend def"
    print(f"# host={platform.machine()} threads={args.threads or 'default'} osqp={HAS_OSQP}")
    print(f"{'operation':<38} | {tlabel + ' (ms)':>12} | {'Py/OSQP (ms)':>12} | notes")
    print("-" * 92)

    with tempfile.TemporaryDirectory() as td:
        # 1. Core N=1000, K=30 ops
        n, k, m_h = 1000, 30, 10
        b, cf, d = make_fm(rng, n, k)
        a = (rng.standard_normal(n) * 0.01).astype(np.float32)
        w = rng.standard_normal(n).astype(np.float32)
        fr = (rng.standard_normal(k) * 0.01).astype(np.float32)
        r = (b @ fr + rng.standard_normal(n) * np.sqrt(d)).astype(np.float32)
        hmat = rng.standard_normal((n, m_h)).astype(np.float32)

        ps = {}
        for key, arr in [("b", b), ("cf", cf), ("d", d), ("a", a), ("w", w), ("r", r), ("fr", fr), ("h", hmat)]:
            ps[key] = os.path.join(td, f"{key}.f32")
            write_f32(ps[key], arr)

        ops = [
            (0, "risk_decomp (1000x30)", 200, lambda: (
                (b.T @ w) @ cf @ (b.T @ w) + np.sum(w * w * d)
            )),
            (1, "mvo_target_vol (1000x30)", 15, lambda: (
                (lambda Lf: (lambda U, di: (lambda y0: y0 - di * (U @ np.linalg.solve(np.eye(k, dtype=np.float32) + U.T @ (di[:, None] * U), U.T @ y0)))(di * a))(b @ Lf, 1.0 / d))(np.linalg.cholesky(cf))
            )),
            (2, "mvo_factor_neutral (1000x30)", 15, lambda: (
                (lambda disq: (lambda Q, ta: disq * (ta - Q @ (Q.T @ ta)))(np.linalg.qr(disq[:, None] * b, mode="reduced")[0], disq * a))(1.0 / np.sqrt(d))
            )),
            (3, "fmp (1000x30)", 10, lambda: (
                (lambda disq: (lambda Q, R: disq[:, None] * np.linalg.solve(R, Q.T).T)(*np.linalg.qr(disq[:, None] * b, mode="reduced")))(1.0 / np.sqrt(d))
            )),
            (4, "hedge_instruments (1000x30, M=10)", 15, lambda: (
                (lambda bh, omw: -np.linalg.solve(bh.T @ cf @ bh + hmat.T @ (d[:, None] * hmat), hmat.T @ omw))(b.T @ hmat, b @ (cf @ (b.T @ w)) + d * w)
            )),
            (5, "attribute_period (1000x30)", 15, lambda: (
                (lambda exp, eps, R: (exp * fr, w * eps, np.linalg.norm(np.linalg.solve(R.T, exp))**2))(b.T @ w, r - b @ fr, np.linalg.qr((1.0 / np.sqrt(d))[:, None] * b, mode="reduced")[1])
            )),
        ]
        for op_id, label, reps, py_fn in ops:
            b_args = ["0", str(op_id), "1", ps["b"], ps["cf"], ps["d"], ps["a"], ps["w"], ps["r"], ps["fr"], ps["h"], str(n), str(k), str(m_h)]
            b_ms, _ = time_bend(b_args, reps=reps, rep_idx=2, threads=args.threads)
            if args.skip_py:
                print(f"{label:<38} | {b_ms:>12.2f} | {'—':>12} |")
            else:
                p_ms = time_py(py_fn, reps=50)
                print(f"{label:<38} | {b_ms:>12.2f} | {p_ms:>12.3f} | ratio={b_ms/p_ms:.1f}x")

        # 2. Forward PnL parallel (T=252, N=1000)
        T, N_p = 252, 1000
        Wp = rng.standard_normal((T, N_p)).astype(np.float32)
        Rp = (rng.standard_normal((T, N_p)) * 0.01).astype(np.float32)
        wpp, rpp = os.path.join(td, "wp.f32"), os.path.join(td, "rp.f32")
        write_f32(wpp, Wp); write_f32(rpp, Rp)
        b_ms, _ = time_bend(["2", "1", wpp, rpp, str(T), str(N_p)], reps=60, rep_idx=1, threads=args.threads)
        if args.skip_py:
            print(f"{'forward_pnl (252x1000, pmap)':<38} | {b_ms:>12.2f} | {'—':>12} |")
        else:
            p_ms = time_py(lambda: np.sum(Wp[:-1] * Rp[1:], axis=1), reps=100)
            print(f"{'forward_pnl (252x1000, pmap)':<38} | {b_ms:>12.2f} | {p_ms:>12.3f} | ratio={b_ms/p_ms:.1f}x")

        # 3. Forward Attribute parallel (T=252, N=200, K=15)
        Ta, Na, Ka = 252, 200, 15
        bfa, cffa, dfa = make_fm(rng, Na, Ka)
        Wa = rng.standard_normal((Ta, Na)).astype(np.float32)
        FRa = (rng.standard_normal((Ta, Ka)) * 0.01).astype(np.float32)
        Ra = (FRa @ bfa.T + rng.standard_normal((Ta, Na)) * np.sqrt(dfa)).astype(np.float32)
        fa_p = {}
        for key, arr in [("b", bfa), ("cf", cffa), ("d", dfa), ("w", Wa), ("r", Ra), ("fr", FRa)]:
            fa_p[key] = os.path.join(td, f"fa_{key}.f32")
            write_f32(fa_p[key], arr)
        b_ms, _ = time_bend(
            ["3", "1", fa_p["b"], fa_p["cf"], fa_p["d"], fa_p["w"], fa_p["r"], fa_p["fr"], str(Ta), str(Na), str(Ka)],
            reps=3, rep_idx=1, threads=args.threads,
        )
        if args.skip_py:
            print(f"{'forward_attribute (252x200x15, pmap)':<38} | {b_ms:>12.2f} | {'—':>12} |")
        else:
            def py_fattr():
                disq = (1.0 / np.sqrt(dfa))[:, None]
                out = 0.0
                for t in range(Ta - 1):
                    wt = Wa[t]
                    rt = Ra[t + 1]
                    ft = FRa[t + 1]
                    exp = bfa.T @ wt
                    eps = rt - bfa @ ft
                    _, R = np.linalg.qr(disq * bfa, mode="reduced")
                    out += float(np.dot(exp, ft) + np.dot(wt, eps) + np.linalg.norm(np.linalg.solve(R.T, exp))**2)
                return out
            p_ms = time_py(py_fattr, reps=5)
            print(f"{'forward_attribute (252x200x15, pmap)':<38} | {b_ms:>12.2f} | {p_ms:>12.3f} | ratio={b_ms/p_ms:.1f}x")

        # 4. Woodbury-ADMM constrained MVO at N=200, 500, 1000
        for N_a, K_a, reps_a in [(200, 15, 5), (500, 30, 3), (1000, 30, 2)]:
            ba, cfa, da = make_fm(rng, N_a, K_a)
            aa = (rng.standard_normal(N_a) * 0.01).astype(np.float32)
            w0a = (rng.standard_normal(N_a) * 0.01).astype(np.float32)
            lwa = np.full(N_a, -0.02, dtype=np.float32)
            uwa = np.full(N_a, 0.02, dtype=np.float32)
            Aa = np.vstack([np.ones((1, N_a), dtype=np.float32), ba.T])
            Ma = Aa.shape[0]
            lca = np.concatenate([[0.0], np.full(K_a, -0.02)]).astype(np.float32)
            uca = np.concatenate([[0.0], np.full(K_a, 0.02)]).astype(np.float32)
            c1a = np.full(N_a, 0.0005, dtype=np.float32)
            c2a = np.full(N_a, 0.005, dtype=np.float32)
            pa = np.array([2.0, 2.0, 1e-5, 1e-4, 0.0, 1.6], dtype=np.float32)

            fp = {}
            for key, arr in [("b", ba), ("cf", cfa), ("d", da), ("a", aa), ("w0", w0a),
                             ("lw", lwa), ("uw", uwa), ("am", Aa), ("lc", lca), ("uc", uca),
                             ("c1", c1a), ("c2", c2a), ("p", pa)]:
                fp[key] = os.path.join(td, f"admm_{N_a}_{key}.f32")
                write_f32(fp[key], arr)

            b_ms, info = time_bend(
                ["1", "1", fp["b"], fp["cf"], fp["d"], fp["a"], fp["w0"], fp["lw"], fp["uw"],
                 fp["am"], fp["lc"], fp["uc"], fp["c1"], fp["c2"], fp["p"],
                 str(N_a), str(K_a), str(Ma), "1000"],
                reps=reps_a, rep_idx=1, threads=args.threads,
            )
            label = f"mvo_constrained ({N_a}x{K_a}, M={Ma})"
            if HAS_OSQP and not args.skip_py:
                o_ms, o_it, o_sum = bench_osqp_mvo(ba, cfa, da, aa, w0a, lwa, uwa, Aa, lca, uca, c1a, c2a, 2.0, 2.0, reps=reps_a)
                print(f"{label:<38} | {b_ms:>12.2f} | {o_ms:>12.2f} | {info} | osqp_it={o_it} ratio={b_ms/o_ms:.2f}x")
            else:
                print(f"{label:<38} | {b_ms:>12.2f} | {'—':>12} | {info}")


if __name__ == "__main__":
    main()
