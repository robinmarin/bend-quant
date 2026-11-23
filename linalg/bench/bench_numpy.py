"""Apples-to-apples NumPy/SciPy (f32 and f64) timing baseline matching bench_suite.bend."""
import time
import numpy as np
from scipy.linalg import cho_factor, cho_solve, orthogonal_procrustes


def make_spd(rng, n, dtype):
    G = rng.standard_normal((n, n))
    Q, _ = np.linalg.qr(G)
    eigs = np.geomspace(1.0, 20.0, n)
    A = (Q * eigs) @ Q.T
    A = 0.5 * (A + A.T)
    return A.astype(dtype)


def bench(fn, reps=20):
    fn()  # warmup
    t0 = time.perf_counter()
    for _ in range(reps):
        fn()
    return (time.perf_counter() - t0) * 1000.0 / reps


def run_dtype(dtype):
    rng = np.random.default_rng(42)
    B = rng.standard_normal((1000, 50)).astype(dtype)
    Omega = make_spd(rng, 50, dtype)
    L = np.linalg.cholesky(Omega)
    Q, _ = np.linalg.qr(B, mode="reduced")
    x50 = rng.standard_normal(50).astype(dtype)
    y1000 = rng.standard_normal(1000).astype(dtype)
    d1000 = rng.uniform(0.5, 1.5, 1000).astype(dtype)
    w1000 = rng.uniform(0.5, 1.5, 1000).astype(dtype)
    A500 = rng.standard_normal((500, 30)).astype(dtype)
    B500 = rng.standard_normal((500, 30)).astype(dtype)
    A500_T = np.ascontiguousarray(A500.T)
    y500 = rng.standard_normal(500).astype(dtype)
    C30 = rng.standard_normal((30, 3)).astype(dtype)
    dc3 = rng.standard_normal(3).astype(dtype)
    A200 = rng.standard_normal((200, 30)).astype(dtype)

    def woodbury_solve():
        di = 1.0 / d1000
        Lm = np.linalg.cholesky(Omega)
        G = B.T @ (di[:, None] * B)
        C = np.eye(50, dtype=dtype) + Lm.T @ G @ Lm
        Lc = cho_factor(C, lower=True)
        dib = di * y1000
        v = Lm.T @ (B.T @ dib)
        z = cho_solve(Lc, v)
        return dib - di * (B @ (Lm @ z))

    def woodbury_logdet():
        di = 1.0 / d1000
        Lm = np.linalg.cholesky(Omega)
        G = B.T @ (di[:, None] * B)
        C = np.eye(50, dtype=dtype) + Lm.T @ G @ Lm
        Lc = np.linalg.cholesky(C)
        return float(np.sum(np.log(d1000)) + 2.0 * np.sum(np.log(np.diag(Lc))))

    def wlstsq():
        sw = np.sqrt(w1000)
        return np.linalg.lstsq(sw[:, None] * B, sw * y1000, rcond=None)[0]

    def lstsq_c():
        Qc, Rc = np.linalg.qr(C30, mode="complete")
        Q1, Q2 = Qc[:, :3], Qc[:, 3:]
        y1 = np.linalg.solve(Rc[:3, :3].T, dc3)
        x1 = Q1 @ y1
        y2 = np.linalg.lstsq(A500 @ Q2, y500 - A500 @ x1, rcond=None)[0]
        return x1 + Q2 @ y2

    def spd_pow_neg_half():
        w, u = np.linalg.eigh(Omega)
        return (u * (1.0 / np.sqrt(w))) @ u.T

    cases = [
        ("matvec_1000x50", lambda: B @ x50, 200),
        ("matmul_1000x50x50", lambda: B @ Omega, 50),
        ("gram_1000x50", lambda: B.T @ B, 100),
        ("wgram_1000x50", lambda: B.T @ (w1000[:, None] * B), 50),
        ("cholesky_50x50", lambda: np.linalg.cholesky(Omega), 200),
        ("chol_solve_50x50", lambda: cho_solve((L, True), x50), 200),
        ("woodbury_solve_1000x50", woodbury_solve, 50),
        ("woodbury_logdet_1000x50", woodbury_logdet, 50),
        ("qr_thin_1000x50", lambda: np.linalg.qr(B, mode="reduced"), 20),
        ("lstsq_1000x50", lambda: np.linalg.lstsq(B, y1000, rcond=None), 20),
        ("wlstsq_1000x50", wlstsq, 20),
        ("project_orth_1000x50", lambda: y1000 - Q @ (Q.T @ y1000), 200),
        ("lstsq_con_500x30_p3", lstsq_c, 20),
        ("sym_eigen_50x50", lambda: np.linalg.eigh(Omega), 50),
        ("spd_pow_50x50", spd_pow_neg_half, 50),
        ("svd_thin_500x30", lambda: np.linalg.svd(A500, full_matrices=False), 20),
        ("svd_thin_30x500", lambda: np.linalg.svd(A500_T, full_matrices=False), 20),
        ("pinv_200x30", lambda: np.linalg.pinv(A200, rcond=1e-5), 20),
        ("procrustes_500x30", lambda: orthogonal_procrustes(B500, A500), 20),
    ]
    return {name: bench(fn, reps) for name, fn, reps in cases}


def main():
    r32 = run_dtype(np.float32)
    r64 = run_dtype(np.float64)
    print(f"{'op':<26} {'numpy_f32_ms':>12} {'numpy_f64_ms':>12}")
    for k in r32:
        print(f"{k:<26} {r32[k]:>12.4f} {r64[k]:>12.4f}")


if __name__ == "__main__":
    main()
