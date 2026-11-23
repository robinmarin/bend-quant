"""Check linalg against NumPy/SciPy. Run from anywhere: python3 linalg/check.py

Builds check.bend into out/ (or uses existing binary if --no-build), writes
test matrices/vectors, and compares every op against NumPy/SciPy. Exits non-zero
on any mismatch.
"""
import os, shutil, subprocess, sys, tempfile
import numpy as np
from scipy.linalg import solve_triangular, orthogonal_procrustes

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, "out", "check")
TOL = 1e-4

SCALAR_TAGS = {
    "dot", "norm1", "norm2", "frob", "trace_sq", "trace_rect", "quad_form",
    "chol_logdet", "chol_logdet_nonsq", "chol_logdet_bad", "wb_logdet",
}
VEC_TAGS = {
    "vscale", "vadd", "vsub", "axpy", "vmul", "vdiv", "matvec", "matvec_t", "diag_vec",
    "solve_lower", "solve_upper", "chol_solve",
    "solve_lower_zero", "solve_upper_zero",
    "solve_lower_bad", "solve_upper_bad", "chol_solve_bad",
    "wb_solve",
    "lstsq", "wlstsq", "project_orth", "project_orth_bad", "lstsq_c",
    "eig_vals", "svd_s",
}


def find_bend():
    return os.environ.get("BEND") or shutil.which("bend") or os.path.expanduser("~/.bend/bin/bend")


def build():
    os.makedirs(os.path.dirname(BIN), exist_ok=True)
    r = subprocess.run([find_bend(), "check.bend", "-o", BIN], cwd=HERE, capture_output=True, text=True)
    if r.returncode != 0 or not os.path.exists(BIN):
        sys.exit(r.stdout + r.stderr)


def parse_output(out):
    got = {}
    for line in out.splitlines():
        line = line.strip()
        if not line:
            continue
        parts = line.split()
        tag, rest = parts[0], parts[1:]
        if rest == ["none"]:
            got[tag] = None
        elif tag in SCALAR_TAGS:
            got[tag] = float(rest[0])
        elif tag in VEC_TAGS:
            ln = int(rest[0])
            got[tag] = np.array([float(v) for v in rest[1:]], dtype=np.float64)
            assert len(got[tag]) == ln, f"{tag}: declared {ln}, got {len(got[tag])}"
        else:
            rm, rn = int(rest[0]), int(rest[1])
            vals = [float(v) for v in rest[2:]]
            got[tag] = np.array(vals, dtype=np.float64).reshape(rm, rn)
    return got


def compare_dict(name, got, want, tol=TOL):
    max_err = 0.0
    bad = []
    for key, wv in want.items():
        gv = got.get(key)
        if wv is None:
            if gv is not None:
                bad.append((key, "expected None", gv))
        elif isinstance(wv, float):
            if gv is None:
                bad.append((key, "got None", wv))
            else:
                err = abs(gv - wv) / max(1.0, abs(wv))
                max_err = max(max_err, err)
                if err > tol:
                    bad.append((key, err, gv, wv))
        else:
            if gv is None or gv.shape != wv.shape:
                bad.append((key, f"shape {None if gv is None else gv.shape} != {wv.shape}"))
            else:
                denom = max(1.0, float(np.max(np.abs(wv))) if wv.size else 1.0)
                err = float(np.max(np.abs(gv - wv))) / denom if wv.size else 0.0
                max_err = max(max_err, err)
                if err > tol:
                    bad.append((key, err))
    if bad:
        sys.exit(f"FAIL {name}: {bad}")
    return max_err


# ---- core tests

def run_core(A, B, C, x, y, w):
    m, n = A.shape
    _, k = B.shape
    with tempfile.TemporaryDirectory() as d:
        paths = {}
        for name, arr in [("a", A), ("b", B), ("c", C), ("x", x), ("y", y), ("w", w)]:
            p = os.path.join(d, f"{name}.f32")
            arr.astype("<f4").tofile(p)
            paths[name] = p
        out = subprocess.run(
            [BIN, "0", paths["a"], paths["b"], paths["c"], paths["x"], paths["y"], paths["w"],
             str(m), str(n), str(k)],
            capture_output=True, text=True, check=True,
        ).stdout
    return parse_output(out)


def check_core(name, m, n, k, seed):
    rng = np.random.default_rng(seed)
    A = rng.standard_normal((m, n)).astype(np.float32)
    B = rng.standard_normal((n, k)).astype(np.float32)
    C = rng.standard_normal((n, n)).astype(np.float32)
    x = rng.standard_normal(n).astype(np.float32)
    y = rng.uniform(0.5, 2.0, n).astype(np.float32) * rng.choice([-1.0, 1.0], n).astype(np.float32)
    w = rng.uniform(0.2, 3.0, m).astype(np.float32)

    got = run_core(A, B, C, x, y, w)
    A64, B64, C64 = A.astype(np.float64), B.astype(np.float64), C.astype(np.float64)
    x64, y64, w64 = x.astype(np.float64), y.astype(np.float64), w.astype(np.float64)

    want = {
        "dot": float(x64 @ y64),
        "norm1": float(np.sum(np.abs(x64))),
        "norm2": float(np.linalg.norm(x64)),
        "vscale": 2.5 * x64,
        "vadd": x64 + y64,
        "vsub": x64 - y64,
        "axpy": -1.5 * x64 + y64,
        "vmul": x64 * y64,
        "vdiv": x64 / y64,
        "outer": np.outer(x64, w64),
        "scale": 0.5 * A64,
        "madd": A64 + A64,
        "msub": A64 - 0.25 * A64,
        "frob": float(np.linalg.norm(A64, "fro")),
        "trace_sq": float(np.trace(C64)),
        "trace_rect": None if m != n else float(np.trace(A64)),
        "transpose": A64.T,
        "submatrix": A64[1:3, 1:4],
        "diag_mul": w64[:, None] * A64,
        "mul_diag": A64 * x64[None, :],
        "matvec": A64 @ x64,
        "matvec_t": A64.T @ w64,
        "matmul": A64 @ B64,
        "matmul_bad": None if m != n else A64 @ A64,
        "gram": A64.T @ A64,
        "wgram": A64.T @ (w64[:, None] * A64),
        "quad_form": float(x64 @ C64 @ x64),
        "eye": np.eye(4),
        "diag": np.diag(x64),
        "diag_vec": np.diag(A64),
    }

    max_err = compare_dict(name, got, want)
    assert np.array_equal(got["gram"], got["gram"].T), f"{name}: gram not bitwise symmetric"
    assert np.array_equal(got["wgram"], got["wgram"].T), f"{name}: wgram not bitwise symmetric"
    print(f"ok   {name:<22} ({m}x{n} * {n}x{k})  max_rel_err={max_err:.2e}")


# ---- Cholesky & triangular solve tests

def make_spd(rng, n, cond=20.0):
    G = rng.standard_normal((n, n))
    Q, _ = np.linalg.qr(G)
    eigs = np.geomspace(1.0, cond, n)
    A = (Q * eigs) @ Q.T
    A = 0.5 * (A + A.T)
    return A.astype(np.float32)


def run_chol(A, bv, bm, nonspd, bad_tri):
    n = A.shape[0]
    k = bm.shape[1]
    with tempfile.TemporaryDirectory() as d:
        paths = {}
        for name, arr in [("a", A), ("bv", bv), ("bm", bm), ("ns", nonspd), ("bt", bad_tri)]:
            p = os.path.join(d, f"{name}.f32")
            arr.astype("<f4").tofile(p)
            paths[name] = p
        out = subprocess.run(
            [BIN, "1", paths["a"], paths["bv"], paths["bm"], paths["ns"], paths["bt"],
             str(n), str(k)],
            capture_output=True, text=True, check=True,
        ).stdout
    return parse_output(out)


def check_chol(name, n, k, cond, seed, tol=TOL):
    rng = np.random.default_rng(seed)
    A = make_spd(rng, n, cond=cond)
    bv = rng.standard_normal(n).astype(np.float32)
    bm = rng.standard_normal((n, k)).astype(np.float32)
    nonspd = A.copy()
    nonspd[n // 2, n // 2] = -1.0  # indefinite
    bad_tri = np.tril(rng.standard_normal((n, n))).astype(np.float32)
    np.fill_diagonal(bad_tri, 2.0)
    bad_tri[n // 2, n // 2] = 0.0  # singular diagonal

    got = run_chol(A, bv, bm, nonspd, bad_tri)
    A64 = A.astype(np.float64)
    bv64 = bv.astype(np.float64)
    bm64 = bm.astype(np.float64)
    L64 = np.linalg.cholesky(A64)
    sign, logdet64 = np.linalg.slogdet(A64)
    assert sign > 0

    want = {
        "chol": L64,
        "chol_nonspd": None,
        "chol_nonsq": None,
        "chol_logdet": float(logdet64),
        "chol_logdet_nonsq": None,
        "chol_logdet_bad": None,
        "solve_lower": solve_triangular(L64, bv64, lower=True),
        "solve_upper": solve_triangular(L64.T, bv64, lower=False),
        "solve_lower_mat": solve_triangular(L64, bm64, lower=True),
        "solve_upper_mat": solve_triangular(L64.T, bm64, lower=False),
        "chol_solve": np.linalg.solve(A64, bv64),
        "chol_solve_mat": np.linalg.solve(A64, bm64),
        "chol_inv": np.linalg.inv(A64),
        "solve_lower_zero": None,
        "solve_upper_zero": None,
        "solve_lower_bad": None,
        "solve_upper_bad": None,
        "chol_solve_bad": None,
    }

    max_err = compare_dict(name, got, want, tol=tol)
    # Exact structural zero strictly above the diagonal of L
    L_got = got["chol"]
    upper = L_got[np.triu_indices(n, k=1)]
    assert np.all(upper == 0.0), f"{name}: L has non-zero above diagonal"
    # Reconstruction check L @ L.T ≈ A
    recon_err = float(np.max(np.abs(L_got @ L_got.T - A64))) / float(np.max(np.abs(A64)))
    assert recon_err < tol, f"{name}: L L^T reconstruction err {recon_err:.2e}"
    print(f"ok   {name:<22} ({n}x{n}, cond={cond:g})  max_rel_err={max_err:.2e}  recon={recon_err:.2e}")


# ---- Woodbury & determinant lemma tests

def run_woodbury(d, U, M, b):
    nd = d.shape[0]
    nu, ku = U.shape
    mm, mn = M.shape
    nb = b.shape[0]
    with tempfile.TemporaryDirectory() as td:
        paths = {}
        for name, arr in [("d", d), ("u", U), ("m", M), ("b", b)]:
            p = os.path.join(td, f"{name}.f32")
            arr.astype("<f4").tofile(p)
            paths[name] = p
        out = subprocess.run(
            [BIN, "2", paths["d"], paths["u"], paths["m"], paths["b"],
             str(nd), str(nu), str(ku), str(mm), str(mn), str(nb)],
            capture_output=True, text=True, check=True,
        ).stdout
    return parse_output(out)


def check_woodbury(name, n, k, cond_m, seed, tol=TOL):
    rng = np.random.default_rng(seed)
    d = rng.uniform(0.05, 0.5, n).astype(np.float32)
    U = (rng.standard_normal((n, k)) * 0.3).astype(np.float32)
    M = make_spd(rng, k, cond=cond_m) if k > 0 else np.zeros((0, 0), dtype=np.float32)
    b = rng.standard_normal(n).astype(np.float32)

    got = run_woodbury(d, U, M, b)
    d64 = d.astype(np.float64)
    U64 = U.astype(np.float64)
    M64 = M.astype(np.float64)
    b64 = b.astype(np.float64)
    Sigma = np.diag(d64) + (U64 @ M64 @ U64.T if k > 0 else 0.0)
    sign, logdet64 = np.linalg.slogdet(Sigma)
    assert sign > 0

    want = {
        "wb_solve": np.linalg.solve(Sigma, b64),
        "wb_logdet": float(logdet64),
    }
    max_err = compare_dict(name, got, want, tol=tol)
    print(f"ok   {name:<22} (N={n}, K={k}, condM={cond_m:g})  max_rel_err={max_err:.2e}")


def check_woodbury_errors():
    rng = np.random.default_rng(99)
    n, k = 10, 3
    d = rng.uniform(0.1, 1.0, n).astype(np.float32)
    U = rng.standard_normal((n, k)).astype(np.float32)
    M = make_spd(rng, k, cond=10.0)
    b = rng.standard_normal(n).astype(np.float32)

    # Non-positive d
    d_zero = d.copy(); d_zero[3] = 0.0
    got = run_woodbury(d_zero, U, M, b)
    compare_dict("wb_d_zero", got, {"wb_solve": None, "wb_logdet": None})

    d_neg = d.copy(); d_neg[0] = -0.2
    got = run_woodbury(d_neg, U, M, b)
    compare_dict("wb_d_neg", got, {"wb_solve": None, "wb_logdet": None})

    # Non-SPD M
    M_bad = M.copy(); M_bad[1, 1] = -2.0
    got = run_woodbury(d, U, M_bad, b)
    compare_dict("wb_m_nonspd", got, {"wb_solve": None, "wb_logdet": None})

    # Shape mismatches
    b_bad = rng.standard_normal(n + 1).astype(np.float32)
    got = run_woodbury(d, U, M, b_bad)
    compare_dict("wb_b_mismatch", got, {"wb_solve": None})

    M_rect = rng.standard_normal((k + 1, k)).astype(np.float32)
    got = run_woodbury(d, U, M_rect, b)
    compare_dict("wb_m_mismatch", got, {"wb_solve": None, "wb_logdet": None})

    print("ok   woodbury_errors        (non-pos d, non-SPD M, shape mismatches)")


# ---- QR & least squares tests

def make_cond_mat(rng, m, n, cond):
    U, _ = np.linalg.qr(rng.standard_normal((m, n)))
    V, _ = np.linalg.qr(rng.standard_normal((n, n)))
    s = np.geomspace(1.0, 1.0 / cond, n)
    return ((U * s) @ V.T).astype(np.float32)


def run_qr(A, b, w, bm, x):
    m, n = A.shape
    k = bm.shape[1]
    with tempfile.TemporaryDirectory() as td:
        paths = {}
        for name, arr in [("a", A), ("b", b), ("w", w), ("bm", bm), ("x", x)]:
            p = os.path.join(td, f"{name}.f32")
            arr.astype("<f4").tofile(p)
            paths[name] = p
        out = subprocess.run(
            [BIN, "3", paths["a"], paths["b"], paths["w"], paths["bm"], paths["x"],
             str(m), str(n), str(k)],
            capture_output=True, text=True, check=True,
        ).stdout
    return parse_output(out)


def check_qr(name, m, n, k, cond, seed, tol=TOL, zero_w=False, consistent=False):
    rng = np.random.default_rng(seed)
    A = make_cond_mat(rng, m, n, cond) if n > 0 else np.zeros((m, 0), dtype=np.float32)
    if consistent and n > 0:
        b = (A @ rng.standard_normal(n) + 0.01 * rng.standard_normal(m)).astype(np.float32)
        bm = (A @ rng.standard_normal((n, k)) + 0.01 * rng.standard_normal((m, k))).astype(np.float32)
    else:
        b = rng.standard_normal(m).astype(np.float32)
        bm = rng.standard_normal((m, k)).astype(np.float32)
    w = rng.uniform(0.2, 3.0, m).astype(np.float32)
    if zero_w:
        w[:5] = 0.0
    # Include a vector strongly correlated with col(A) to stress project_orth
    x = (A @ rng.standard_normal(n) * 5.0 + rng.standard_normal(m) * 0.1).astype(np.float32) if n > 0 else rng.standard_normal(m).astype(np.float32)

    got = run_qr(A, b, w, bm, x)
    A64, b64, w64 = A.astype(np.float64), b.astype(np.float64), w.astype(np.float64)
    bm64, x64 = bm.astype(np.float64), x.astype(np.float64)

    Q_got = got["qr_q"]
    R_got = got["qr_r"]
    assert Q_got is not None and Q_got.shape == (m, n), f"{name}: bad Q shape"
    assert R_got is not None and R_got.shape == (n, n), f"{name}: bad R shape"
    # Exact structural zeros strictly below the diagonal of R
    if n > 1:
        lower = R_got[np.tril_indices(n, k=-1)]
        assert np.all(lower == 0.0), f"{name}: R has non-zero below diagonal"
    # Orthogonality Q^T Q ≈ I and reconstruction Q R ≈ A
    orth_err = float(np.max(np.abs(Q_got.T @ Q_got - np.eye(n)))) if n > 0 else 0.0
    recon_err = float(np.max(np.abs(Q_got @ R_got - A64))) / max(1.0, float(np.max(np.abs(A64)))) if n > 0 else 0.0
    assert orth_err < 1e-5, f"{name}: Q orthogonality err {orth_err:.2e}"
    assert recon_err < 1e-5, f"{name}: QR reconstruction err {recon_err:.2e}"

    if n > 0:
        x_ols, _, _, _ = np.linalg.lstsq(A64, b64, rcond=None)
        sw = np.sqrt(w64)
        x_wls, _, _, _ = np.linalg.lstsq(sw[:, None] * A64, sw * b64, rcond=None)
        X_mat, _, _, _ = np.linalg.lstsq(A64, bm64, rcond=None)
        Q64, _ = np.linalg.qr(A64, mode="reduced")
        proj64 = x64 - Q64 @ (Q64.T @ x64)
    else:
        x_ols = np.zeros(0)
        x_wls = np.zeros(0)
        X_mat = np.zeros((0, k))
        proj64 = x64

    want = {
        "lstsq": x_ols,
        "wlstsq": x_wls,
        "lstsq_mat": X_mat,
        "project_orth": proj64,
        "project_orth_bad": None if m > 0 else np.zeros(0),
    }
    max_err = compare_dict(name, got, want, tol=tol)
    if n > 0:
        p_orth = float(np.max(np.abs(Q_got.T @ got["project_orth"]))) / max(1.0, float(np.linalg.norm(got["project_orth"])))
        assert p_orth < 1e-5, f"{name}: project_orth not orthogonal to Q ({p_orth:.2e})"
    print(f"ok   {name:<22} ({m}x{n}, cond={cond:g})  max_rel_err={max_err:.2e}  orth={orth_err:.2e}  recon={recon_err:.2e}")


def check_qr_errors():
    rng = np.random.default_rng(40)
    # Wide matrix (m < n)
    A = rng.standard_normal((4, 6)).astype(np.float32)
    b = rng.standard_normal(4).astype(np.float32)
    w = rng.uniform(0.5, 2.0, 4).astype(np.float32)
    bm = rng.standard_normal((4, 2)).astype(np.float32)
    got = run_qr(A, b, w, bm, b)
    compare_dict("qr_wide", got, {"qr_q": None, "qr_r": None, "lstsq": None, "wlstsq": None, "lstsq_mat": None})

    # Negative weight
    A2 = rng.standard_normal((8, 3)).astype(np.float32)
    b2 = rng.standard_normal(8).astype(np.float32)
    w2 = rng.uniform(0.5, 2.0, 8).astype(np.float32); w2[2] = -0.1
    bm2 = rng.standard_normal((8, 2)).astype(np.float32)
    got2 = run_qr(A2, b2, w2, bm2, b2)
    compare_dict("wlstsq_neg_w", got2, {"wlstsq": None})

    # Zero column (exact rank deficiency)
    A3 = rng.standard_normal((8, 3)).astype(np.float32); A3[:, 1] = 0.0
    w3 = rng.uniform(0.5, 2.0, 8).astype(np.float32)
    got3 = run_qr(A3, b2, w3, bm2, b2)
    compare_dict("lstsq_zero_col", got3, {"lstsq": None, "wlstsq": None, "lstsq_mat": None})

    print("ok   qr_errors              (wide m<n, neg weight, zero col)")


def run_constrained(A, b, C, d):
    ma, na = A.shape
    nb = b.shape[0]
    cm, cp = C.shape
    nd = d.shape[0]
    with tempfile.TemporaryDirectory() as td:
        paths = {}
        for name, arr in [("a", A), ("b", b), ("c", C), ("d", d)]:
            p = os.path.join(td, f"{name}.f32")
            arr.astype("<f4").tofile(p)
            paths[name] = p
        out = subprocess.run(
            [BIN, "4", paths["a"], paths["b"], paths["c"], paths["d"],
             str(ma), str(na), str(nb), str(cm), str(cp), str(nd)],
            capture_output=True, text=True, check=True,
        ).stdout
    return parse_output(out)


def solve_constrained_ref(A64, b64, C64, d64):
    """Exact float64 KKT reference for min ||A x - b||^2 s.t. C^T x = d."""
    n, p = C64.shape
    if p == 0:
        x, _, _, _ = np.linalg.lstsq(A64, b64, rcond=None)
        return x
    KKT = np.block([[A64.T @ A64, C64], [C64.T, np.zeros((p, p))]])
    rhs = np.concatenate([A64.T @ b64, d64])
    return np.linalg.solve(KKT, rhs)[:n]


def check_constrained():
    rng = np.random.default_rng(50)

    # 1. Paleologo market + 5 industry dummies (rank-deficient A: col0 = sum(col1..5))
    m, k_ind = 100, 5
    n = 1 + k_ind
    ind = rng.integers(0, k_ind, size=m)
    A = np.zeros((m, n), dtype=np.float32)
    A[:, 0] = 1.0
    for i, g in enumerate(ind):
        A[i, 1 + g] = 1.0
    b = rng.standard_normal(m).astype(np.float32)
    cap_w = rng.uniform(0.1, 0.4, k_ind).astype(np.float32)
    cap_w /= cap_w.sum()
    C = np.zeros((n, 1), dtype=np.float32)
    C[1:, 0] = cap_w
    d = np.array([0.0], dtype=np.float32)
    got = run_constrained(A, b, C, d)
    want = solve_constrained_ref(A.astype(np.float64), b.astype(np.float64), C.astype(np.float64), d.astype(np.float64))
    err1 = compare_dict("lstsq_c_dummies", got, {"lstsq_c": want})
    con_res1 = float(np.max(np.abs(C.astype(np.float64).T @ got["lstsq_c"] - d.astype(np.float64))))
    assert con_res1 < 1e-5
    print(f"ok   lstsq_c_dummies        (100x6 rank-5, p=1)  max_rel_err={err1:.2e}  |C^Tx-d|={con_res1:.2e}")

    # 2. Multi-constraint non-zero RHS (m=50, n=10, p=3)
    A2 = rng.standard_normal((50, 10)).astype(np.float32)
    b2 = rng.standard_normal(50).astype(np.float32)
    C2 = rng.standard_normal((10, 3)).astype(np.float32)
    d2 = rng.standard_normal(3).astype(np.float32)
    got2 = run_constrained(A2, b2, C2, d2)
    want2 = solve_constrained_ref(A2.astype(np.float64), b2.astype(np.float64), C2.astype(np.float64), d2.astype(np.float64))
    err2 = compare_dict("lstsq_c_multi", got2, {"lstsq_c": want2})
    con_res2 = float(np.max(np.abs(C2.astype(np.float64).T @ got2["lstsq_c"] - d2.astype(np.float64))))
    assert con_res2 < 1e-5
    print(f"ok   lstsq_c_multi          (50x10, p=3)  max_rel_err={err2:.2e}  |C^Tx-d|={con_res2:.2e}")

    # 3. Fully constrained (p == n)
    A3 = rng.standard_normal((8, 5)).astype(np.float32)
    b3 = rng.standard_normal(8).astype(np.float32)
    C3 = rng.standard_normal((5, 5)).astype(np.float32)
    d3 = rng.standard_normal(5).astype(np.float32)
    got3 = run_constrained(A3, b3, C3, d3)
    want3 = np.linalg.solve(C3.astype(np.float64).T, d3.astype(np.float64))
    err3 = compare_dict("lstsq_c_full", got3, {"lstsq_c": want3})
    print(f"ok   lstsq_c_full           (8x5, p=5)  max_rel_err={err3:.2e}")

    # 4. Zero constraints (p == 0) -> falls back to lstsq
    C4 = np.zeros((5, 0), dtype=np.float32)
    d4 = np.zeros(0, dtype=np.float32)
    got4 = run_constrained(A3, b3, C4, d4)
    want4 = solve_constrained_ref(A3.astype(np.float64), b3.astype(np.float64), C4.astype(np.float64), d4.astype(np.float64))
    err4 = compare_dict("lstsq_c_p0", got4, {"lstsq_c": want4})
    print(f"ok   lstsq_c_p0             (8x5, p=0)  max_rel_err={err4:.2e}")

    # 5. Underdetermined m < n rescued by constraints (m=4, n=6, p=3 => m >= n-p=3)
    A5 = rng.standard_normal((4, 6)).astype(np.float32)
    b5 = rng.standard_normal(4).astype(np.float32)
    C5 = rng.standard_normal((6, 3)).astype(np.float32)
    d5 = rng.standard_normal(3).astype(np.float32)
    got5 = run_constrained(A5, b5, C5, d5)
    want5 = solve_constrained_ref(A5.astype(np.float64), b5.astype(np.float64), C5.astype(np.float64), d5.astype(np.float64))
    err5 = compare_dict("lstsq_c_underdet", got5, {"lstsq_c": want5})
    print(f"ok   lstsq_c_underdet       (4x6, p=3)  max_rel_err={err5:.2e}")

    # 6. Error cases: bad dims, p > n, m < n - p, zero constraint col
    compare_dict("lstsq_c_bad_b", run_constrained(A2, b2[:10], C2, d2), {"lstsq_c": None})
    compare_dict("lstsq_c_p_gt_n", run_constrained(A3, b3, rng.standard_normal((5, 6)).astype(np.float32), rng.standard_normal(6).astype(np.float32)), {"lstsq_c": None})
    compare_dict("lstsq_c_few_rows", run_constrained(A5[:2], b5[:2], C5, d5), {"lstsq_c": None})
    C_zero = C2.copy(); C_zero[:, 1] = 0.0
    compare_dict("lstsq_c_zero_c", run_constrained(A2, b2, C_zero, d2), {"lstsq_c": None})
    print("ok   lstsq_c_errors         (bad dims, p>n, m<n-p, zero constraint col)")


# ---- Symmetric eigen & SPD matrix power tests

def run_eigen(A):
    m, n = A.shape
    with tempfile.TemporaryDirectory() as td:
        p = os.path.join(td, "a.f32")
        A.astype("<f4").tofile(p)
        out = subprocess.run([BIN, "5", p, str(m), str(n)], capture_output=True, text=True, check=True).stdout
    return parse_output(out)


def check_eigen_spd(name, n, cond, seed, tol=TOL):
    rng = np.random.default_rng(seed)
    A = make_spd(rng, n, cond=cond) if n > 0 else np.zeros((0, 0), dtype=np.float32)
    got = run_eigen(A)
    A64 = A.astype(np.float64)
    vals = got["eig_vals"]
    vecs = got["eig_vecs"]
    assert vals is not None and vals.shape == (n,)
    assert vecs is not None and vecs.shape == (n, n)
    if n > 1:
        assert np.all(np.diff(vals) <= 1e-6), f"{name}: eigenvalues not descending: {vals}"
    if n > 0:
        w64, u64 = np.linalg.eigh(A64)
        w64 = w64[::-1]
        u64 = u64[:, ::-1]
        orth_err = float(np.max(np.abs(vecs.T @ vecs - np.eye(n))))
        recon_err = float(np.max(np.abs((vecs * vals) @ vecs.T - A64))) / max(1.0, float(np.max(np.abs(A64))))
        assert orth_err < tol, f"{name}: V orth err {orth_err:.2e}"
        assert recon_err < tol, f"{name}: eigen recon err {recon_err:.2e}"
        want = {
            "eig_vals": w64,
            "spd_sqrt": (u64 * np.sqrt(w64)) @ u64.T,
            "spd_inv_sqrt": (u64 * (1.0 / np.sqrt(w64))) @ u64.T,
            "spd_inv": (u64 * (1.0 / w64)) @ u64.T,
            "spd_cube_rt": (u64 * np.power(w64, 1.0 / 3.0)) @ u64.T,
        }
    else:
        orth_err = recon_err = 0.0
        want = {
            "eig_vals": np.zeros(0),
            "spd_sqrt": np.zeros((0, 0)),
            "spd_inv_sqrt": np.zeros((0, 0)),
            "spd_inv": np.zeros((0, 0)),
            "spd_cube_rt": np.zeros((0, 0)),
        }
    max_err = compare_dict(name, got, want, tol=tol)
    for k in ("spd_sqrt", "spd_inv_sqrt", "spd_inv", "spd_cube_rt"):
        assert np.array_equal(got[k], got[k].T), f"{name}: {k} not bitwise symmetric"
    print(f"ok   {name:<22} ({n}x{n}, cond={cond:g})  max_rel_err={max_err:.2e}  orth={orth_err:.2e}  recon={recon_err:.2e}")


def check_eigen_extra():
    rng = np.random.default_rng(65)
    # Indefinite symmetric matrix with repeated and negative eigenvalues
    n = 8
    Q, _ = np.linalg.qr(rng.standard_normal((n, n)))
    eigs = np.array([5.0, 2.0, 2.0, 0.0, -1.0, -1.0, -3.0, -7.0])
    A = ((Q * eigs) @ Q.T).astype(np.float32)
    A = (0.5 * (A + A.T)).astype(np.float32)
    got = run_eigen(A)
    A64 = A.astype(np.float64)
    w64 = np.linalg.eigvalsh(A64)[::-1]
    vals, vecs = got["eig_vals"], got["eig_vecs"]
    assert np.all(np.diff(vals) <= 1e-6)
    orth_err = float(np.max(np.abs(vecs.T @ vecs - np.eye(n))))
    recon_err = float(np.max(np.abs((vecs * vals) @ vecs.T - A64))) / float(np.max(np.abs(A64)))
    assert orth_err < TOL and recon_err < TOL
    err = compare_dict("eig_indef", got, {
        "eig_vals": w64,
        "spd_sqrt": None,
        "spd_inv_sqrt": None,
        "spd_inv": None,
        "spd_cube_rt": None,
    })
    print(f"ok   eig_indef              (8x8 indef+repeated)  max_rel_err={err:.2e}  orth={orth_err:.2e}  recon={recon_err:.2e}")

    # Non-square -> all None
    A_ns = rng.standard_normal((4, 5)).astype(np.float32)
    got_ns = run_eigen(A_ns)
    compare_dict("eig_nonsq", got_ns, {
        "eig_vals": None, "eig_vecs": None,
        "spd_sqrt": None, "spd_inv_sqrt": None, "spd_inv": None, "spd_cube_rt": None,
    })
    print("ok   eig_nonsq              (4x5 -> None)")


# ---- Thin SVD & Moore-Penrose pseudoinverse tests

def run_svd(A):
    m, n = A.shape
    with tempfile.TemporaryDirectory() as td:
        p = os.path.join(td, "a.f32")
        A.astype("<f4").tofile(p)
        out = subprocess.run([BIN, "6", p, str(m), str(n)], capture_output=True, text=True, check=True).stdout
    return parse_output(out)


def check_svd(name, A, tol=TOL, check_pinv=True, pinv_tol=None):
    m, n = A.shape
    k = min(m, n)
    got = run_svd(A)
    A64 = A.astype(np.float64)
    U, s, Vt = got["svd_u"], got["svd_s"], got["svd_vt"]
    assert U.shape == (m, k), f"{name}: U shape {U.shape} != {(m, k)}"
    assert s.shape == (k,), f"{name}: s shape {s.shape} != {(k,)}"
    assert Vt.shape == (k, n), f"{name}: Vt shape {Vt.shape} != {(k, n)}"
    if k > 1:
        assert np.all(np.diff(s) <= 1e-6), f"{name}: singular values not descending"
    if k > 0:
        assert np.all(s >= 0.0), f"{name}: negative singular value"
        s64 = np.linalg.svd(A64, compute_uv=False)
        u_orth = float(np.max(np.abs(U.T @ U - np.eye(k))))
        v_orth = float(np.max(np.abs(Vt @ Vt.T - np.eye(k))))
        recon = float(np.max(np.abs((U * s) @ Vt - A64))) / max(1.0, float(np.max(np.abs(A64))))
        assert u_orth < 1e-4, f"{name}: U orth err {u_orth:.2e}"
        assert v_orth < 1e-4, f"{name}: V orth err {v_orth:.2e}"
        assert recon < 1e-4, f"{name}: SVD recon err {recon:.2e}"
        s_err = float(np.max(np.abs(s - s64))) / max(1.0, float(s64[0]))
        assert s_err < tol, f"{name}: singular value err {s_err:.2e}"
    else:
        u_orth = v_orth = recon = s_err = 0.0

    p_err = 0.0
    if check_pinv:
        Ap = got["pinv"]
        assert Ap.shape == (n, m), f"{name}: pinv shape {Ap.shape} != {(n, m)}"
        Ap64 = np.linalg.pinv(A64, rcond=1e-5)
        ptol = tol if pinv_tol is None else pinv_tol
        p_err = compare_dict(f"{name}_pinv", {"pinv": Ap}, {"pinv": Ap64}, tol=ptol)
        # Moore-Penrose axioms
        if m > 0 and n > 0:
            a_scale = max(1.0, float(np.max(np.abs(A64))))
            ap_scale = max(1.0, float(np.max(np.abs(Ap64))))
            assert float(np.max(np.abs(A64 @ Ap @ A64 - A64))) / a_scale < ptol
            assert float(np.max(np.abs(Ap @ A64 @ Ap - Ap))) / ap_scale < ptol
    print(f"ok   {name:<22} ({m}x{n})  s_err={s_err:.2e}  pinv={p_err:.2e}  orth={max(u_orth, v_orth):.2e}  recon={recon:.2e}")


def check_svd_suite():
    rng = np.random.default_rng(70)
    check_svd("svd_tall", make_cond_mat(rng, 40, 8, 100.0))
    check_svd("svd_wide", make_cond_mat(rng, 60, 12, 100.0).T)
    check_svd("svd_square", make_cond_mat(rng, 10, 10, 500.0), pinv_tol=5e-4)
    # Ill-conditioned 100x15 (cond=1e4): checks smallest singular value accuracy!
    A_ill = make_cond_mat(rng, 100, 15, 1e4)
    check_svd("svd_ill_1e4", A_ill, check_pinv=False)
    got_ill = run_svd(A_ill)
    s64_ill = np.linalg.svd(A_ill.astype(np.float64), compute_uv=False)
    rel_min = abs(got_ill["svd_s"][-1] - s64_ill[-1]) / s64_ill[-1]
    assert rel_min < 2e-2, f"svd_ill_1e4: smallest singular value rel err {rel_min:.2e}"
    # Rank-deficient (20x8, exact rank 5, plus an all-zero column)
    L5 = rng.standard_normal((20, 5))
    R5 = rng.standard_normal((5, 8))
    R5[:, 3] = 0.0
    A_rd = (L5 @ R5).astype(np.float32)
    check_svd("svd_rank_def", A_rd, pinv_tol=5e-4)
    # Edge cases: 1-col, 1-row, 0-col, 0-row, all-zero
    check_svd("svd_col1", rng.standard_normal((7, 1)).astype(np.float32))
    check_svd("svd_row1", rng.standard_normal((1, 7)).astype(np.float32))
    check_svd("svd_zero_col", np.zeros((5, 0), dtype=np.float32))
    check_svd("svd_zero_row", np.zeros((0, 4), dtype=np.float32))
    check_svd("svd_all_zero", np.zeros((4, 3), dtype=np.float32))


# ---- Orthogonal Procrustes tests

def run_procrustes(A, B):
    ma, na = A.shape
    mb, nb = B.shape
    with tempfile.TemporaryDirectory() as td:
        pa = os.path.join(td, "a.f32")
        pb = os.path.join(td, "b.f32")
        A.astype("<f4").tofile(pa)
        B.astype("<f4").tofile(pb)
        out = subprocess.run([BIN, "7", pa, pb, str(ma), str(na), str(mb), str(nb)], capture_output=True, text=True, check=True).stdout
    return parse_output(out)


def check_procrustes():
    rng = np.random.default_rng(80)
    # 1. Exact orthogonal recovery: A = B @ R_true
    B = rng.standard_normal((100, 10)).astype(np.float32)
    R_true, _ = np.linalg.qr(rng.standard_normal((10, 10)))
    A = (B.astype(np.float64) @ R_true).astype(np.float32)
    got = run_procrustes(A, B)
    X = got["procrustes"]
    orth_err = float(np.max(np.abs(X.T @ X - np.eye(10))))
    err1 = compare_dict("proc_exact", got, {"procrustes": R_true})
    assert orth_err < 1e-5
    print(f"ok   proc_exact             (100x10)  max_rel_err={err1:.2e}  orth={orth_err:.2e}")

    # 2. Noisy Procrustes vs SciPy orthogonal_procrustes(B, A) (minimizes ||B X - A||_F)
    B2 = rng.standard_normal((80, 12)).astype(np.float32)
    R2, _ = np.linalg.qr(rng.standard_normal((12, 12)))
    A2 = (B2.astype(np.float64) @ R2 + 0.1 * rng.standard_normal((80, 12))).astype(np.float32)
    got2 = run_procrustes(A2, B2)
    X2 = got2["procrustes"]
    X2_ref, _ = orthogonal_procrustes(B2.astype(np.float64), A2.astype(np.float64))
    orth_err2 = float(np.max(np.abs(X2.T @ X2 - np.eye(12))))
    err2 = compare_dict("proc_noisy", got2, {"procrustes": X2_ref})
    assert orth_err2 < 1e-5
    print(f"ok   proc_noisy             (80x12)   max_rel_err={err2:.2e}  orth={orth_err2:.2e}")

    # 3. Rank-deficient A^T B: X must still be orthogonal and achieve optimal objective
    B3 = (rng.standard_normal((15, 3)) @ rng.standard_normal((3, 5))).astype(np.float32)
    A3 = (rng.standard_normal((15, 3)) @ rng.standard_normal((3, 5))).astype(np.float32)
    got3 = run_procrustes(A3, B3)
    X3 = got3["procrustes"]
    X3_ref, _ = orthogonal_procrustes(B3.astype(np.float64), A3.astype(np.float64))
    orth_err3 = float(np.max(np.abs(X3.T @ X3 - np.eye(5))))
    obj_got = float(np.linalg.norm(A3.astype(np.float64) - B3.astype(np.float64) @ X3, "fro"))
    obj_ref = float(np.linalg.norm(A3.astype(np.float64) - B3.astype(np.float64) @ X3_ref, "fro"))
    assert orth_err3 < 1e-5 and abs(obj_got - obj_ref) / max(1.0, obj_ref) < 1e-5
    print(f"ok   proc_rank_def          (15x5 rank-3)  obj_err={abs(obj_got-obj_ref)/max(1.0,obj_ref):.2e}  orth={orth_err3:.2e}")

    # 4. Shape mismatch -> None
    compare_dict("proc_mismatch", run_procrustes(A2, B2[:10]), {"procrustes": None})
    print("ok   proc_mismatch          (80x12 vs 10x12 -> None)")


def main():
    if "--no-build" not in sys.argv:
        build()
    # Core ops
    check_core("small_rect", 5, 4, 3, seed=1)
    check_core("wide_rect", 4, 7, 5, seed=2)
    check_core("parallel_pmap", 80, 12, 6, seed=3)  # m >= 64 exercises 64-task pmap

    # Cholesky & triangular solves
    check_chol("chol_small", 4, 3, cond=10.0, seed=10)
    check_chol("chol_med", 12, 5, cond=100.0, seed=11)
    check_chol("chol_factor50", 50, 8, cond=500.0, seed=12, tol=5e-4)

    # Woodbury & Matrix Determinant Lemma
    check_woodbury("wb_k0", 12, 0, cond_m=1.0, seed=20)
    check_woodbury("wb_80x12", 80, 12, cond_m=100.0, seed=21)
    check_woodbury("wb_200x20_ill", 200, 20, cond_m=1e4, seed=22, tol=5e-4)
    check_woodbury_errors()

    # QR & least squares
    check_qr("qr_small", 6, 4, 3, cond=10.0, seed=30)
    check_qr("qr_square", 8, 8, 4, cond=100.0, seed=31)
    check_qr("qr_n0", 5, 0, 2, cond=1.0, seed=32)
    check_qr("qr_ill_cond", 200, 20, 4, cond=1e4, seed=33, tol=2e-3, consistent=True)
    check_qr("qr_inconsistent", 200, 20, 4, cond=1e3, seed=35, tol=5e-4)
    check_qr("qr_factor_scale", 500, 30, 5, cond=100.0, seed=34, tol=5e-4, zero_w=True)
    check_qr_errors()
    check_constrained()

    # Symmetric eigen, SPD power, thin SVD, pinv & Procrustes
    check_eigen_spd("eig_n0", 0, cond=1.0, seed=60)
    check_eigen_spd("eig_n1", 1, cond=1.0, seed=61)
    check_eigen_spd("eig_small", 4, cond=20.0, seed=62)
    check_eigen_spd("eig_med", 12, cond=100.0, seed=63)
    check_eigen_spd("eig_spiked50", 50, cond=500.0, seed=64, tol=5e-4)
    check_eigen_extra()
    check_svd_suite()
    check_procrustes()

    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
