#!/usr/bin/env python3
"""Benchmark bend-quant-risk vs NumPy / SciPy / scikit-learn."""
import argparse
import os
import platform
import subprocess
import tempfile
import time
import numpy as np
from scipy import linalg as sla
from sklearn.covariance import LedoitWolf

ROOT = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(ROOT, "out", "bench_risk")


def write_f32(path, arr):
    np.asarray(arr, dtype="<f4").tofile(path)


def make_fm(rng, n, k):
    b = (rng.standard_normal((n, k)) * 0.5).astype(np.float32)
    q, _ = np.linalg.qr(rng.standard_normal((k, k)))
    cf = (q @ np.diag(np.geomspace(1.0, 50.0, k) * 1e-4) @ q.T).astype(np.float32)
    cf = 0.5 * (cf + cf.T)
    d = np.exp(rng.uniform(-7.0, -4.5, size=n)).astype(np.float32)
    return b, cf, d


def rts_prefix(threads):
    if threads and threads > 0:
        return ["+RTS", "--threads", str(threads), "-RTS"]
    return []


def time_bend(args, reps, rep_idx=2, threads=0):
    pref = rts_prefix(threads)
    a1 = list(args); a1[rep_idx] = "1"
    t0 = time.perf_counter()
    subprocess.run([BIN, *pref, *a1], capture_output=True, text=True, check=True)
    t1 = time.perf_counter() - t0

    a2 = list(args); a2[rep_idx] = str(1 + reps)
    t0 = time.perf_counter()
    r2 = subprocess.run([BIN, *pref, *a2], capture_output=True, text=True, check=True)
    t2 = time.perf_counter() - t0
    return max((t2 - t1) / reps, 1e-6) * 1000.0, r2.stdout.strip()


def time_py(fn, reps=10):
    fn()
    t0 = time.perf_counter()
    for _ in range(reps):
        fn()
    return (time.perf_counter() - t0) / reps * 1000.0


def ewma_w(t, hl):
    lam = np.float32(2.0 ** (-1.0 / hl))
    w = lam ** np.arange(t - 1, -1, -1, dtype=np.float32)
    return w / np.sum(w)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--threads", type=int, default=0, help="Bend RTS threads (0 = runtime default)")
    ap.add_argument("--skip-py", action="store_true", help="Skip NumPy/SciPy/sklearn timings")
    args = ap.parse_args()

    rng = np.random.default_rng(42)
    tlabel = f"Bend {args.threads}t" if args.threads > 0 else "Bend def"
    print(f"# host={platform.machine()} threads={args.threads or 'default'}")
    print(f"{'operation':<44} | {tlabel + ' (ms)':>12} | {'Py/Ref (ms)':>12} | notes")
    print("-" * 92)

    with tempfile.TemporaryDirectory() as td:
        # ---- 1. Ch 6 Covariance estimators (T=252, K=30) ----
        t_c, k_c = 252, 30
        F_c = (rng.standard_normal((t_c, k_c)) * 0.012).astype(np.float32)
        fp = os.path.join(td, "f_cov.f32")
        write_f32(fp, F_c)

        def py_lw():
            return LedoitWolf(assume_centered=False).fit(F_c).covariance_

        def py_nw():
            w = ewma_w(t_c, 63.0)
            C = (F_c.T * w) @ F_c
            for l in range(1, 6):
                kw = np.float32(1.0 - l / 6.0)
                Gl = (F_c[l:].T * w[l:]) @ F_c[:-l]
                C = C + kw * (Gl + Gl.T)
            return C

        def py_dcc():
            lam_v = np.float32(np.exp(-np.log(2.0) / 30.0))
            v = np.maximum(F_c[0]**2, np.float32(1e-12))
            Z = np.empty_like(F_c)
            for ti in range(t_c):
                v = lam_v * v + (np.float32(1.0) - lam_v) * (F_c[ti]**2)
                Z[ti] = F_c[ti] / np.sqrt(np.maximum(v, np.float32(1e-12)))
            wv = ewma_w(t_c, 30.0)
            wc = ewma_w(t_c, 90.0)
            s = np.sqrt(np.maximum(np.sum((F_c**2) * wv[:, None], axis=0), np.float32(1e-12)))
            R = (Z.T * wc) @ Z
            rd = np.sqrt(np.maximum(np.diag(R), np.float32(1e-12)))
            return np.outer(s, s) * (R / np.outer(rd, rd))

        for op_id, label, reps, py_fn in [
            (0, "ledoit_wolf_cov (252x30)", 150, py_lw),
            (1, "cov_newey_west (252x30, L=5)", 40, py_nw),
            (2, "dcc_cov (252x30)", 60, py_dcc),
        ]:
            b_ms, _ = time_bend(["0", str(op_id), "1", fp, str(t_c), str(k_c)], reps=reps, rep_idx=2, threads=args.threads)
            if args.skip_py:
                print(f"{label:<44} | {b_ms:>12.2f} | {'—':>12} |")
            else:
                p_ms = time_py(py_fn, reps=30)
                print(f"{label:<44} | {b_ms:>12.2f} | {p_ms:>12.3f} | ratio={b_ms/p_ms:.2f}x")

        # ---- 2. Ch 5 Woodbury OOS evaluation (T=252, N=500, K=30, pmap) ----
        t5, n5, k5 = 252, 500, 30
        b5, cf5, d5 = make_fm(rng, n5, k5)
        rets5 = (rng.standard_normal((t5, k5)).astype(np.float32) * 0.01 @ b5.T +
                 rng.standard_normal((t5, n5)).astype(np.float32) * np.sqrt(d5)).astype(np.float32)
        bv5 = np.full(n5, 1.0 / n5, dtype=np.float32)
        p5 = {}
        for key, arr in [("b", b5), ("cf", cf5), ("d", d5), ("r", rets5), ("bv", bv5)]:
            p5[key] = os.path.join(td, f"ch5_{key}.f32")
            write_f32(p5[key], arr)

        def py_qdist_woodbury():
            tot = 0.0
            for ti in range(t5 - 1):
                rn = rets5[ti + 1]
                di = 1.0 / d5
                Lf = np.linalg.cholesky(cf5)
                U = b5 @ Lf
                M = np.eye(k5, dtype=np.float32) + U.T @ (di[:, None] * U)
                Lm = np.linalg.cholesky(M)
                logdet = float(np.sum(np.log(d5)) + 2.0 * np.sum(np.log(np.diag(Lm))))
                y0 = di * rn
                z = sla.cho_solve((Lm, True), U.T @ y0)
                inv_r = y0 - di * (U @ z)
                tot += logdet + float(np.dot(rn, inv_r))
            return tot

        def py_qdist_dense():
            tot = 0.0
            for ti in range(t5 - 1):
                Om = b5 @ cf5 @ b5.T + np.diag(d5)
                rn = rets5[ti + 1]
                _, ld = np.linalg.slogdet(Om)
                tot += float(ld + rn @ np.linalg.solve(Om, rn))
            return tot

        def py_mahal_woodbury():
            tot = 0.0
            for ti in range(t5 - 1):
                rn = rets5[ti + 1]
                di = 1.0 / d5
                Lf = np.linalg.cholesky(cf5)
                U = b5 @ Lf
                M = np.eye(k5, dtype=np.float32) + U.T @ (di[:, None] * U)
                Lm = np.linalg.cholesky(M)
                y0 = di * rn
                z = sla.cho_solve((Lm, True), U.T @ y0)
                inv_r = y0 - di * (U @ z)
                tot += float(np.dot(rn, inv_r)) / n5
            return tot

        def py_mvp_woodbury():
            tot = 0.0
            for ti in range(t5 - 1):
                rn = rets5[ti + 1]
                di = 1.0 / d5
                Lf = np.linalg.cholesky(cf5)
                U = b5 @ Lf
                M = np.eye(k5, dtype=np.float32) + U.T @ (di[:, None] * U)
                Lm = np.linalg.cholesky(M)
                y0 = di * bv5
                z = sla.cho_solve((Lm, True), U.T @ y0)
                inv_b = y0 - di * (U @ z)
                tot += float(np.dot(rn, inv_b) / np.dot(bv5, inv_b))
            return tot

        for op_id, label, reps, py_fn, extra_fn in [
            (0, "qdist (252x500x30, pmap)", 2, py_qdist_woodbury, py_qdist_dense),
            (1, "mahalanobis_test (252x500x30, pmap)", 2, py_mahal_woodbury, None),
            (2, "mvp_test (252x500x30, pmap)", 2, py_mvp_woodbury, None),
        ]:
            b_ms, _ = time_bend(["1", str(op_id), "1", p5["b"], p5["cf"], p5["d"], p5["r"], p5["bv"], str(t5), str(n5), str(k5)],
                                reps=reps, rep_idx=2, threads=args.threads)
            if args.skip_py:
                print(f"{label:<44} | {b_ms:>12.2f} | {'—':>12} |")
            else:
                p_ms = time_py(py_fn, reps=5)
                note = f"ratio={b_ms/p_ms:.2f}x (Woodbury)"
                if extra_fn is not None:
                    d_ms = time_py(extra_fn, reps=2)
                    note += f" | dense={d_ms:.1f}ms ({d_ms/b_ms:.1f}x vs dense)"
                print(f"{label:<44} | {b_ms:>12.2f} | {p_ms:>12.2f} | {note}")

        # ---- 3. Ch 6 Fundamental multi-period (T=252, N=500, K=30, pmap) ----
        def py_fser():
            out = np.empty((t5, k5), dtype=np.float32)
            for ti in range(t5):
                Q, R = np.linalg.qr(b5, mode="reduced")
                out[ti] = sla.solve_triangular(R, Q.T @ rets5[ti])
            return out

        for op_id, label, reps, py_fn in [
            (0, "estimate_factor_series (252x500x30, pmap)", 2, py_fser),
            (1, "fit_fundamental_model (252x500x30, pmap)", 1, None),
        ]:
            b_ms, _ = time_bend(["2", str(op_id), "1", p5["b"], p5["r"], str(t5), str(n5), str(k5)],
                                reps=reps, rep_idx=2, threads=args.threads)
            if args.skip_py or py_fn is None:
                print(f"{label:<44} | {b_ms:>12.2f} | {'—':>12} |")
            else:
                p_ms = time_py(py_fn, reps=3)
                print(f"{label:<44} | {b_ms:>12.2f} | {p_ms:>12.2f} | ratio={b_ms/p_ms:.2f}x")

        # ---- 4. Ch 7 PCA / Subspace SVD & Statistical Model (T=250, N=500, K=15 and T=250, N=1000, K=15) ----
        for N7, K7, do_exact in [(500, 15, True), (1000, 15, False)]:
            T7 = 250
            B7 = (rng.standard_normal((N7, K7)) * 0.5).astype(np.float32)
            F7 = (rng.standard_normal((T7, K7)) * np.geomspace(0.05, 0.015, K7)).astype(np.float32)
            R7 = (F7 @ B7.T + rng.standard_normal((T7, N7)) * 0.006).astype(np.float32)
            rp7 = os.path.join(td, f"r7_{N7}.f32")
            write_f32(rp7, R7)

            if do_exact:
                b_ex, _ = time_bend(["3", "0", "1", rp7, str(T7), str(N7), str(K7), "126"], reps=1, rep_idx=2, threads=args.threads)
            b_sub, _ = time_bend(["3", "1", "1", rp7, str(T7), str(N7), str(K7), "126"], reps=3, rep_idx=2, threads=args.threads)
            b_sf, _ = time_bend(["3", "2", "1", rp7, str(T7), str(N7), str(K7), "126"], reps=2, rep_idx=2, threads=args.threads)

            if args.skip_py:
                if do_exact:
                    print(f"{f'pca_svd exact ({T7}x{N7}, K={K7})':<44} | {b_ex:>12.2f} | {'—':>12} |")
                print(f"{f'pca_svd subspace ({T7}x{N7}, K={K7})':<44} | {b_sub:>12.2f} | {'—':>12} |")
                print(f"{f'fit_statistical_model ({T7}x{N7}, K={K7})':<44} | {b_sf:>12.2f} | {'—':>12} |")
            else:
                p_svd = time_py(lambda: np.linalg.svd(R7 / np.float32(np.sqrt(T7)), full_matrices=False), reps=10)
                if do_exact:
                    print(f"{f'pca_svd exact ({T7}x{N7}, K={K7})':<44} | {b_ex:>12.2f} | {p_svd:>12.2f} | ratio={b_ex/p_svd:.1f}x")
                note_sub = f"ratio={b_sub/p_svd:.2f}x" + (f" ({b_ex/b_sub:.1f}x faster than exact)" if do_exact else "")
                print(f"{f'pca_svd subspace ({T7}x{N7}, K={K7})':<44} | {b_sub:>12.2f} | {p_svd:>12.2f} | {note_sub}")
                print(f"{f'fit_statistical_model ({T7}x{N7}, K={K7})':<44} | {b_sf:>12.2f} | {'—':>12} | 2-stage p=5 + subspace")

        # ---- 5. Ch 7 Rolling Statistical Models (T=252, W=126, N=150, K=10, 127 windows, pmap) ----
        Tr, Wr, Nr, Kr = 252, 126, 150, 10
        Br = (rng.standard_normal((Nr, Kr)) * 0.5).astype(np.float32)
        Fr = (rng.standard_normal((Tr, Kr)) * np.geomspace(0.04, 0.015, Kr)).astype(np.float32)
        Rr = (Fr @ Br.T + rng.standard_normal((Tr, Nr)) * 0.008).astype(np.float32)
        rpr = os.path.join(td, "r_roll.f32")
        write_f32(rpr, Rr)

        b_rl, _ = time_bend(["3", "3", "1", rpr, str(Tr), str(Nr), str(Kr), str(Wr)], reps=1, rep_idx=2, threads=args.threads)
        if args.skip_py:
            print(f"{'rolling_stat (127x126x150, K=10, pmap)':<44} | {b_rl:>12.2f} | {'—':>12} |")
        else:
            def py_roll():
                prev_b = None
                for i in range(Tr - Wr + 1):
                    win = Rr[i:i + Wr] / np.float32(np.sqrt(Wr))
                    _, s, vt = np.linalg.svd(win, full_matrices=False)
                    b_cur = vt[:Kr].T
                    if prev_b is not None:
                        X, _ = sla.orthogonal_procrustes(b_cur, prev_b)
                        b_cur = b_cur @ X
                    prev_b = b_cur
                return prev_b
            p_rl = time_py(py_roll, reps=3)
            print(f"{'rolling_stat (127x126x150, K=10, pmap)':<44} | {b_rl:>12.2f} | {p_rl:>12.2f} | ratio={b_rl/p_rl:.2f}x")


if __name__ == "__main__":
    main()
