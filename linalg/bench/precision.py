"""Precision and timing reference for bend-quant/linalg benchmark spike.

Tests realistic Paleologo factor-model workloads across condition numbers:
  1. Gram matrix G = B^T B for B (N x K)
  2. Cholesky + solve on K x K SPD matrices (f32 vs f64)
  3. Cross-sectional WLS min ||W^(1/2)(r - B f)||_2:
     - Normal equations (B^T W B) in f32 vs f64
     - Thin Householder QR in f32 vs f64
     - Mixed: f32 B -> f64 Gram/Cholesky
  4. Woodbury MVO solve (D + B Omega_f B^T)^(-1) alpha:
     - Weight relative error and Sharpe Ratio Efficiency (Paleologo Ch 10.3)
  5. Symmetric eigendecomposition (Jacobi / eigh) on spiked K x K covariance
  6. Rank-deficient loadings (market + industry dummies, Ch 6.2.1): ridge & SVD pinv
"""
import time
import numpy as np
from scipy import linalg as sla


def make_factor_matrix(rng, n, k, cond):
    """Build an N x K matrix with controlled singular values spanning [1, cond]."""
    u, _ = np.linalg.qr(rng.standard_normal((n, k)))
    v, _ = np.linalg.qr(rng.standard_normal((k, k)))
    s = np.geomspace(cond, 1.0, k)
    return (u * s) @ v.T


def householder_qr_solve(A, b, dtype):
    """Pure Householder thin QR + back-substitution in given dtype (matches what Bend will do)."""
    A = A.astype(dtype, copy=True)
    b = b.astype(dtype, copy=True)
    m, n = A.shape
    for k in range(n):
        x = A[k:, k]
        norm_x = dtype(np.sqrt(np.dot(x, x)))
        if norm_x == dtype(0.0):
            continue
        sign = dtype(1.0) if x[0] >= dtype(0.0) else dtype(-1.0)
        v = x.copy()
        v[0] = v[0] + sign * norm_x
        v_norm2 = np.dot(v, v)
        if v_norm2 == dtype(0.0):
            continue
        beta = dtype(2.0) / v_norm2
        # Apply H = I - beta v v^T to A[k:, k:] and b[k:]
        A[k:, k:] -= np.outer(beta * v, v @ A[k:, k:])
        b[k:] -= (beta * np.dot(v, b[k:])) * v
    # Back-substitution on R = A[:n, :n]
    x_sol = np.zeros(n, dtype=dtype)
    for i in range(n - 1, -1, -1):
        s = b[i] - np.dot(A[i, i + 1:n], x_sol[i + 1:n])
        x_sol[i] = s / A[i, i]
    return x_sol


def cholesky_solve_ref(A, b, dtype):
    """Pure Cholesky L L^T + forward/back solve in given dtype."""
    A = A.astype(dtype, copy=False)
    b = b.astype(dtype, copy=False)
    n = A.shape[0]
    L = np.zeros((n, n), dtype=dtype)
    for i in range(n):
        for j in range(i + 1):
            s = np.dot(L[i, :j], L[j, :j])
            if i == j:
                val = A[i, i] - s
                if val <= dtype(0.0):
                    return None
                L[i, j] = np.sqrt(val)
            else:
                L[i, j] = (A[i, j] - s) / L[j, j]
    # Forward solve L y = b
    y = np.zeros(n, dtype=dtype)
    for i in range(n):
        y[i] = (b[i] - np.dot(L[i, :i], y[:i])) / L[i, i]
    # Back solve L^T x = y
    x = np.zeros(n, dtype=dtype)
    for i in range(n - 1, -1, -1):
        x[i] = (y[i] - np.dot(L[i + 1:, i], x[i + 1:])) / L[i, i]
    return x


def jacobi_eigen(A, dtype, max_sweeps=15):
    """Cyclic Jacobi symmetric eigendecomposition in given dtype."""
    A = A.astype(dtype, copy=True)
    n = A.shape[0]
    V = np.eye(n, dtype=dtype)
    for _ in range(max_sweeps):
        off = dtype(0.0)
        for p in range(n - 1):
            for q in range(p + 1, n):
                apq = A[p, q]
                off = max(off, abs(apq))
                if abs(apq) <= dtype(1e-30):
                    continue
                app = A[p, p]
                aqq = A[q, q]
                tau = (aqq - app) / (dtype(2.0) * apq)
                if tau >= dtype(0.0):
                    t = dtype(1.0) / (tau + np.hypot(dtype(1.0), tau))
                else:
                    t = dtype(-1.0) / (-tau + np.hypot(dtype(1.0), tau))
                c = dtype(1.0) / np.sqrt(dtype(1.0) + t * t)
                s = t * c
                # Rotate rows/cols p, q of A
                ap = A[:, p].copy()
                aq = A[:, q].copy()
                A[:, p] = c * ap - s * aq
                A[:, q] = s * ap + c * aq
                A[p, :] = A[:, p]
                A[q, :] = A[:, q]
                A[p, p] = c * c * app - dtype(2.0) * s * c * apq + s * s * aqq
                A[q, q] = s * s * app + dtype(2.0) * s * c * apq + c * c * aqq
                A[p, q] = dtype(0.0)
                A[q, p] = dtype(0.0)
                # Accumulate eigenvectors
                vp = V[:, p].copy()
                vq = V[:, q].copy()
                V[:, p] = c * vp - s * vq
                V[:, q] = s * vp + c * vq
        if off < (dtype(1e-6) if dtype == np.float32 else dtype(1e-13)):
            break
    vals = np.diag(A)
    idx = np.argsort(vals)[::-1]
    return vals[idx], V[:, idx]


def test_wls_precision(n=1000, k=50):
    print(f"=== 1. WLS precision (N={n}, K={k}): relative error ||f - f_ref|| / ||f_ref|| ===")
    print(f"{'cond(B)':>10} | {'NE f32':>11} | {'NE f32->f64':>11} | {'QR f32':>11} | {'NE f64':>11} | {'QR f64':>11}")
    print("-" * 78)
    rng = np.random.default_rng(42)
    f_true = rng.standard_normal(k)
    eps = rng.standard_normal(n) * 0.05
    w_inv_sqrt = rng.uniform(0.5, 2.0, n)  # Omega_eps^(-1/2)

    for cond in [1e1, 1e2, 1e3, 1e4, 1e5, 1e6]:
        B = make_factor_matrix(rng, n, k, cond)
        r = B @ f_true + eps
        # Whitened system A f ≈ y
        A64 = w_inv_sqrt[:, None] * B
        y64 = w_inv_sqrt * r
        f_ref, *_ = np.linalg.lstsq(A64, y64, rcond=None)
        ref_norm = np.linalg.norm(f_ref)

        # 1) Normal equations in f32
        A32 = A64.astype(np.float32)
        y32 = y64.astype(np.float32)
        G32 = A32.T @ A32
        rhs32 = A32.T @ y32
        f_ne32 = cholesky_solve_ref(G32, rhs32, np.float32)
        e_ne32 = "FAIL(NPD)" if f_ne32 is None else f"{np.linalg.norm(f_ne32.astype(np.float64) - f_ref) / ref_norm:.2e}"

        # 2) Mixed: f32 A -> f64 Gram & Cholesky (models f32 stored panel, f64 inner solve)
        G_mix = A32.astype(np.float64).T @ A32.astype(np.float64)
        rhs_mix = A32.astype(np.float64).T @ y32.astype(np.float64)
        f_mix = cholesky_solve_ref(G_mix, rhs_mix, np.float64)
        e_mix = "FAIL(NPD)" if f_mix is None else f"{np.linalg.norm(f_mix - f_ref) / ref_norm:.2e}"

        # 3) Thin Householder QR in f32
        f_qr32 = householder_qr_solve(A32, y32, np.float32)
        e_qr32 = f"{np.linalg.norm(f_qr32.astype(np.float64) - f_ref) / ref_norm:.2e}"

        # 4) Normal equations in f64
        f_ne64 = cholesky_solve_ref(A64.T @ A64, A64.T @ y64, np.float64)
        e_ne64 = "FAIL(NPD)" if f_ne64 is None else f"{np.linalg.norm(f_ne64 - f_ref) / ref_norm:.2e}"

        # 5) Thin QR in f64
        f_qr64 = householder_qr_solve(A64, y64, np.float64)
        e_qr64 = f"{np.linalg.norm(f_qr64 - f_ref) / ref_norm:.2e}"

        print(f"{cond:10.0e} | {e_ne32:>11} | {e_mix:>11} | {e_qr32:>11} | {e_ne64:>11} | {e_qr64:>11}")


def test_woodbury_mvo(n=1000, k=50):
    print(f"\n=== 2. Woodbury MVO (D + B Omega_f B^T)^(-1) alpha (N={n}, K={k}) ===")
    print(f"{'cond(Of)':>10} | {'w err f32':>11} | {'SRE f32':>10} | {'w err mix':>11} | {'SRE mix':>10} | {'logdet f32':>11}")
    print("-" * 78)
    rng = np.random.default_rng(7)
    B64 = make_factor_matrix(rng, n, k, 20.0) / np.sqrt(n)
    d64 = rng.uniform(0.01, 0.16, n)  # idiosyncratic variances (10%..40% annual vol)^2
    alpha64 = rng.standard_normal(n) * 0.05

    for cond_f in [1e1, 1e2, 1e3, 1e4, 1e5, 1e6]:
        u, _ = np.linalg.qr(rng.standard_normal((k, k)))
        eig_f = np.geomspace(0.04, 0.04 / cond_f, k)
        Of64 = (u * eig_f) @ u.T
        Omega64 = np.diag(d64) + B64 @ Of64 @ B64.T
        w_ref = np.linalg.solve(Omega64, alpha64)
        sr_ref = np.sqrt(alpha64 @ w_ref)
        _, ld_ref = np.linalg.slogdet(Omega64)

        def woodbury(d, B, Of, a, dtype, inner_dtype):
            d_i = (1.0 / d).astype(dtype)
            d_inv_a = d_i * a
            d_inv_B = d_i[:, None] * B
            # M = Of^(-1) + B^T D^(-1) B
            G = (B.astype(inner_dtype).T @ d_inv_B.astype(inner_dtype)).astype(inner_dtype)
            Of_in = Of.astype(inner_dtype)
            L_of = np.linalg.cholesky(Of_in)
            Of_inv = sla.cho_solve((L_of, True), np.eye(k, dtype=inner_dtype))
            M = Of_inv + G
            L_m = np.linalg.cholesky(M)
            rhs = (B.astype(inner_dtype).T @ d_inv_a.astype(inner_dtype)).astype(inner_dtype)
            z = sla.cho_solve((L_m, True), rhs)
            w = d_inv_a.astype(inner_dtype) - d_inv_B.astype(inner_dtype) @ z
            ld = (np.sum(np.log(d.astype(inner_dtype)))
                  + 2.0 * np.sum(np.log(np.diag(L_of)))
                  + 2.0 * np.sum(np.log(np.diag(L_m))))
            return w.astype(np.float64), float(ld)

        B32, d32, Of32, a32 = B64.astype(np.float32), d64.astype(np.float32), Of64.astype(np.float32), alpha64.astype(np.float32)
        try:
            w32, ld32 = woodbury(d32, B32, Of32, a32, np.float32, np.float32)
            ew32 = f"{np.linalg.norm(w32 - w_ref) / np.linalg.norm(w_ref):.2e}"
            sre32 = f"{(alpha64 @ w32) / np.sqrt(w32 @ Omega64 @ w32) / sr_ref:.6f}"
            eld32 = f"{abs(ld32 - ld_ref) / abs(ld_ref):.2e}"
        except np.linalg.LinAlgError:
            ew32, sre32, eld32 = "FAIL(NPD)", "FAIL", "FAIL"

        try:
            wmix, _ = woodbury(d32, B32, Of32, a32, np.float32, np.float64)
            ewmix = f"{np.linalg.norm(wmix - w_ref) / np.linalg.norm(w_ref):.2e}"
            sremix = f"{(alpha64 @ wmix) / np.sqrt(wmix @ Omega64 @ wmix) / sr_ref:.6f}"
        except np.linalg.LinAlgError:
            ewmix, sremix = "FAIL(NPD)", "FAIL"

        print(f"{cond_f:10.0e} | {ew32:>11} | {sre32:>10} | {ewmix:>11} | {sremix:>10} | {eld32:>11}")


def test_jacobi_eigen(k=50):
    print(f"\n=== 3. Cyclic Jacobi symmetric eigen (K={k}, spiked covariance) ===")
    rng = np.random.default_rng(99)
    u, _ = np.linalg.qr(rng.standard_normal((k, k)))
    # 10 spiked factors + 40 decaying tail factors (Paleologo Ch 7.2)
    eigs_true = np.concatenate([np.geomspace(100.0, 4.0, 10), np.geomspace(1.5, 0.01, k - 10)])
    A64 = (u * eigs_true) @ u.T
    A64 = 0.5 * (A64 + A64.T)
    vals_ref, _ = np.linalg.eigh(A64)
    vals_ref = vals_ref[::-1]

    for name, dt in [("f32", np.float32), ("f64", np.float64)]:
        vals, V = jacobi_eigen(A64, dt)
        eig_err = np.max(np.abs(vals.astype(np.float64) - vals_ref) / np.abs(vals_ref))
        orth_err = np.linalg.norm(V.astype(np.float64).T @ V.astype(np.float64) - np.eye(k), "fro")
        rec_err = np.linalg.norm((V.astype(np.float64) * vals.astype(np.float64)) @ V.astype(np.float64).T - A64, "fro") / np.linalg.norm(A64, "fro")
        print(f"  {name}: max_rel_eig_err={eig_err:.2e}  ||V^T V - I||_F={orth_err:.2e}  recon_err={rec_err:.2e}")


def test_numpy_timings(n=1000, k=50):
    print(f"\n=== 4. NumPy/SciPy reference timings (N={n}, K={k}) ===")
    rng = np.random.default_rng(1)
    B64 = rng.standard_normal((n, k))
    B32 = B64.astype(np.float32)
    G64 = B64.T @ B64 + np.eye(k)
    G32 = G64.astype(np.float32)
    b64 = rng.standard_normal(k)
    b32 = b64.astype(np.float32)

    for label, fn in [
        ("gram  1000x50 f32", lambda: B32.T @ B32),
        ("gram  1000x50 f64", lambda: B64.T @ B64),
        ("chol    50x50 f32", lambda: np.linalg.cholesky(G32)),
        ("chol    50x50 f64", lambda: np.linalg.cholesky(G64)),
        ("qr    1000x50 f32", lambda: np.linalg.qr(B32, mode="reduced")),
        ("qr    1000x50 f64", lambda: np.linalg.qr(B64, mode="reduced")),
        ("eigh    50x50 f32", lambda: np.linalg.eigh(G32)),
        ("eigh    50x50 f64", lambda: np.linalg.eigh(G64)),
    ]:
        fn()  # warmup
        reps = 50
        t0 = time.perf_counter()
        for _ in range(reps):
            fn()
        dt_ms = (time.perf_counter() - t0) * 1000 / reps
        print(f"  {label}: {dt_ms:7.3f} ms")


if __name__ == "__main__":
    test_wls_precision()
    test_woodbury_mvo()
    test_jacobi_eigen()
    test_numpy_timings()
