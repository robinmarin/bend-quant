#!/usr/bin/env python3
"""Numerical verification suite for bend-quant-portfolio against NumPy / SciPy."""
import argparse
import os
import subprocess
import sys
import tempfile
import numpy as np

ROOT = os.path.dirname(os.path.abspath(__file__))
BEND = "/Users/robin/.bend/bin/bend"
BIN = os.path.join(ROOT, "out", "check")


def build():
    os.makedirs(os.path.join(ROOT, "out"), exist_ok=True)
    cmd = [BEND, "check.bend", "-o", "out/check"]
    res = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    if res.returncode != 0:
        print("BUILD FAILED:\n", res.stdout, res.stderr)
        sys.exit(1)


def write_f32(path, arr):
    np.asarray(arr, dtype="<f4").tofile(path)


def run_cli(*args):
    res = subprocess.run([BIN, *[str(a) for a in args]], capture_output=True, text=True)
    if res.returncode != 0:
        raise RuntimeError(f"CLI failed ({res.returncode}): {res.stderr}\n{res.stdout}")
    return res.stdout.splitlines()


class Parser:
    def __init__(self, lines):
        self.lines = lines
        self.i = 0

    def next_line(self):
        line = self.lines[self.i]
        self.i += 1
        return line

    def read_vec(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "VEC", f"Expected VEC, got {hdr}"
        n = int(hdr[1])
        vals = self.next_line().split() if n > 0 else (self.next_line() and [])
        if n == 0:
            return np.zeros(0, dtype=np.float64)
        return np.array([float(x) for x in vals], dtype=np.float64)

    def read_mat(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "MAT", f"Expected MAT, got {hdr}"
        m, n = int(hdr[1]), int(hdr[2])
        rows = []
        for _ in range(m):
            line = self.next_line()
            rows.append([float(x) for x in line.split()] if n > 0 else [])
        return np.array(rows, dtype=np.float64).reshape(m, n)

    def read_f32(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "F32", f"Expected F32, got {hdr}"
        return float(hdr[1])

    def read_risk(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "RISK", f"Expected RISK, got {hdr}"
        vals = [float(x) for x in hdr[1:]]
        exp = self.read_vec()
        return {
            "total_var": vals[0],
            "factor_var": vals[1],
            "idio_var": vals[2],
            "total_vol": vals[3],
            "factor_vol": vals[4],
            "idio_vol": vals[5],
            "pct_idio": vals[6],
            "exposures": exp,
        }


    def read_opt(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "OPT", f"Expected OPT, got {hdr}"
        iters = int(hdr[1])
        rp = float(hdr[2])
        rd = float(hdr[3])
        conv = hdr[4] == "1"
        w = self.read_vec()
        return {"iters": iters, "primal_res": rp, "dual_res": rd, "converged": conv, "weights": w}

    def read_shrink(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "SHRINK", f"Expected SHRINK, got {hdr}"
        return [float(x) for x in hdr[1:]]

    def read_dd(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "DD", f"Expected DD, got {hdr}"
        t = int(hdr[1])
        rows = [[float(x) for x in self.next_line().split()] for _ in range(t)]
        return np.array(rows, dtype=np.float64)

    def read_pattr(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "PATTR", f"Expected PATTR, got {hdr}"
        vals = [float(x) for x in hdr[1:]]
        fc = self.read_vec()
        ic = self.read_vec()
        return {"pos": vals[0], "trading": vals[1], "factor": vals[2], "idio": vals[3], "error_var": vals[4], "fc": fc, "ic": ic}

    def read_mattr(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "MATTR", f"Expected MATTR, got {hdr}"
        sp, rp = float(hdr[1]), float(hdr[2])
        adj = self.read_vec()
        rf = self.read_vec()
        rc = self.read_mat()
        return {"subset_pnl": sp, "resid_pnl": rp, "adj": adj, "rf": rf, "rc": rc}

    def read_nested(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "NESTED", f"Expected NESTED, got {hdr}"
        g = int(hdr[1])
        out = []
        for _ in range(g):
            gh = self.next_line().split()
            assert gh[0] == "NG", f"Expected NG, got {gh}"
            out.append({"pnl": float(gh[1]), "adj": self.read_vec()})
        return out

    def read_ss(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "SS", f"Expected SS, got {hdr}"
        v = [float(x) for x in hdr[1:]]
        return {"ir": v[0], "sel": v[1], "div": v[2], "siz": v[3], "sel_l": v[4], "sel_s": v[5], "q_l": v[6], "q_s": v[7]}

    def read_fattr(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "FATTR", f"Expected FATTR, got {hdr}"
        t = int(hdr[1])
        return [self.read_pattr() for _ in range(t)]


def rel_err(got, ref):
    got = np.asarray(got, dtype=np.float64)
    ref = np.asarray(ref, dtype=np.float64)
    denom = max(np.linalg.norm(ref), 1e-12)
    return float(np.linalg.norm(got - ref) / denom)


def make_factor_model(rng, n, k, cond_f=20.0):
    b = rng.standard_normal((n, k)) * 0.5
    if k > 0:
        q, _ = np.linalg.qr(rng.standard_normal((k, k)))
        eigs = np.geomspace(1.0, cond_f, k) * 1e-4
        cov_f = q @ np.diag(eigs) @ q.T
        cov_f = 0.5 * (cov_f + cov_f.T)
    else:
        cov_f = np.zeros((0, 0))
    idio_var = np.exp(rng.uniform(-6.0, -3.5, size=n))
    return b.astype(np.float32), cov_f.astype(np.float32), idio_var.astype(np.float32)


def test_risk_and_mvo(name, n, k, cond_f=20.0, seed=42, tol=5e-5):
    rng = np.random.default_rng(seed)
    b, cov_f, d = make_factor_model(rng, n, k, cond_f=cond_f)
    w = rng.standard_normal(n).astype(np.float32)
    wb = rng.standard_normal(n).astype(np.float32) * 0.5
    alpha = rng.standard_normal(n).astype(np.float32) * 0.01
    w0 = rng.standard_normal(n).astype(np.float32) * 0.3
    cq = np.exp(rng.uniform(-6.0, -2.0, size=n)).astype(np.float32)
    lf = rng.standard_normal(k).astype(np.float32) * 0.01
    rho = 2.5
    tvol = 0.12
    tau_sq = 0.002

    # Reference in float64 using the exact f32 inputs
    B = b.astype(np.float64)
    Of = cov_f.astype(np.float64)
    D = d.astype(np.float64)
    W = w.astype(np.float64)
    Wb = wb.astype(np.float64)
    A = alpha.astype(np.float64)
    W0 = w0.astype(np.float64)
    Cq = cq.astype(np.float64)
    Lf = lf.astype(np.float64)

    Omega = B @ Of @ B.T + np.diag(D)

    with tempfile.TemporaryDirectory() as td:
        bp = os.path.join(td, "b.f32")
        cfp = os.path.join(td, "cf.f32")
        dp = os.path.join(td, "d.f32")
        wp = os.path.join(td, "w.f32")
        wbp = os.path.join(td, "wb.f32")
        ap = os.path.join(td, "a.f32")
        w0p = os.path.join(td, "w0.f32")
        cqp = os.path.join(td, "cq.f32")
        lfp = os.path.join(td, "lf.f32")
        write_f32(bp, b)
        write_f32(cfp, cov_f)
        write_f32(dp, d)
        write_f32(wp, w)
        write_f32(wbp, wb)
        write_f32(ap, alpha)
        write_f32(w0p, w0)
        write_f32(cqp, cq)
        write_f32(lfp, lf)

        # --- Risk tests ---
        p = Parser(run_cli(0, bp, cfp, dp, wp, wbp, n, k))
        got_exp = p.read_vec()
        got_omw = p.read_vec()
        got_rd = p.read_risk()
        got_ar = p.read_risk()
        got_mr = p.read_vec()
        got_rc = p.read_vec()
        got_h = p.read_f32()
        got_eb = p.read_f32()

        ref_exp = B.T @ W
        ref_omw = Omega @ W
        ref_fvar = float(ref_exp @ Of @ ref_exp) if k > 0 else 0.0
        ref_ivar = float(np.sum(W * W * D))
        ref_tvar = ref_fvar + ref_ivar
        ref_tvol = np.sqrt(ref_tvar)
        ref_mr = ref_omw / ref_tvol
        ref_rc = W * ref_mr
        Wa = W - Wb
        ref_aexp = B.T @ Wa
        ref_atvar = float(Wa @ Omega @ Wa)
        ref_h = (np.linalg.norm(W, 2) / np.linalg.norm(W, 1)) ** 2
        wtilde = np.sqrt(D) * W
        ref_eb = np.linalg.norm(wtilde, 1) / np.linalg.norm(wtilde, 2)

        errs = {
            "exposures": rel_err(got_exp, ref_exp) if k > 0 else 0.0,
            "cov_matvec": rel_err(got_omw, ref_omw),
            "total_var": abs(got_rd["total_var"] - ref_tvar) / max(ref_tvar, 1e-12),
            "factor_var": abs(got_rd["factor_var"] - ref_fvar) / max(ref_fvar, 1e-12) if k > 0 else abs(got_rd["factor_var"]),
            "idio_var": abs(got_rd["idio_var"] - ref_ivar) / max(ref_ivar, 1e-12),
            "pct_idio": abs(got_rd["pct_idio"] - ref_ivar / ref_tvar),
            "active_var": abs(got_ar["total_var"] - ref_atvar) / max(ref_atvar, 1e-12),
            "marginal_risk": rel_err(got_mr, ref_mr),
            "risk_contrib": rel_err(got_rc, ref_rc),
            "euler_sum": abs(np.sum(got_rc) - ref_tvol) / ref_tvol,
            "herfindahl": abs(got_h - ref_h) / ref_h,
            "eff_breadth": abs(got_eb - ref_eb) / ref_eb,
        }

        # --- MVO tests ---
        pp = os.path.join(td, "params.f32")
        write_f32(pp, np.array([rho, tvol, tau_sq], dtype=np.float32))
        p2 = Parser(run_cli(1, bp, cfp, dp, ap, w0p, cqp, lfp, pp, n, k))
        got_mvo = p2.read_vec()
        got_tvol = p2.read_vec()
        got_rob = p2.read_vec()
        got_tq = p2.read_vec()
        got_fmp = p2.read_mat()
        got_fa = p2.read_vec()
        got_sp = p2.read_vec()
        got_orth = p2.read_vec()
        got_fn = p2.read_vec()
        got_fs = p2.read_vec()

        z = np.linalg.solve(Omega, A)
        ref_mvo = z / rho
        ref_tvol_w = (tvol / np.sqrt(A @ z)) * z
        ref_rob = np.linalg.solve(Omega + tau_sq * np.eye(n), A) / rho
        ref_tq = np.linalg.solve(rho * Omega + np.diag(Cq), A + Cq * W0)

        errs["mvo_unconstrained"] = rel_err(got_mvo, ref_mvo)
        errs["mvo_target_vol"] = rel_err(got_tvol, ref_tvol_w)
        errs["target_vol_achieved"] = abs(np.sqrt(got_tvol @ Omega @ got_tvol) - tvol) / tvol
        errs["mvo_robust"] = rel_err(got_rob, ref_rob)
        errs["mvo_trade_quad"] = rel_err(got_tq, ref_tq)

        if k > 0:
            G = B.T @ np.diag(1.0 / D) @ B
            ref_fmp = np.diag(1.0 / D) @ B @ np.linalg.inv(G)
            ref_fa = np.linalg.solve(G, B.T @ (A / D))
            ref_sp = B @ ref_fa
            ref_orth = A - ref_sp
            w_fn_raw = ref_orth / D
            ref_fn = (tvol / np.sqrt(w_fn_raw @ (D * w_fn_raw))) * w_fn_raw
            ref_fs = ref_fmp @ (np.linalg.solve(Of, Lf) / rho)

            errs["fmp"] = rel_err(got_fmp, ref_fmp)
            errs["fmp_unit_exp"] = float(np.max(np.abs(B.T @ got_fmp - np.eye(k))))
            errs["alpha_factor"] = rel_err(got_fa, ref_fa)
            errs["alpha_spanned"] = rel_err(got_sp, ref_sp)
            errs["alpha_orth"] = rel_err(got_orth, ref_orth)
            errs["alpha_sum"] = rel_err(got_sp + got_orth, A)
            errs["mvo_fn"] = rel_err(got_fn, ref_fn)
            errs["mvo_fn_neutral"] = float(np.linalg.norm(B.T @ got_fn) / (np.linalg.norm(B, "fro") * np.linalg.norm(got_fn)))
            errs["mvo_fn_vol"] = abs(np.sqrt(got_fn @ (D * got_fn)) - tvol) / tvol
            errs["mvo_fspace"] = rel_err(got_fs, ref_fs)
        else:
            assert got_fmp.shape == (n, 0)
            w_fn_raw = A / D
            ref_fn = (tvol / np.sqrt(w_fn_raw @ (D * w_fn_raw))) * w_fn_raw
            errs["mvo_fn"] = rel_err(got_fn, ref_fn)

        mx = max(errs.values())
        worst = max(errs, key=errs.get)
        status = "PASS" if mx <= tol else "FAIL"
        print(f"[{status}] {name} (N={n}, K={k}, cond_f={cond_f}): max_err={mx:.2e} ({worst})")
        if mx > tol:
            for kk, vv in errs.items():
                if vv > tol:
                    print(f"   {kk}: {vv:.2e}")
            sys.exit(1)


def test_sre(name, n, k, seed=7, tol=5e-5):
    rng = np.random.default_rng(seed)
    bt, cft, dt = make_factor_model(rng, n, k, cond_f=100.0)
    # Perturb estimated model and alpha
    be = (bt + rng.standard_normal(bt.shape) * 0.05).astype(np.float32)
    cfe = (cft * 1.15).astype(np.float32)
    de = (dt * np.exp(rng.uniform(-0.2, 0.2, size=n))).astype(np.float32)
    at = (rng.standard_normal(n) * 0.01).astype(np.float32)
    ae = (at + rng.standard_normal(n) * 0.003).astype(np.float32)

    Bt, Oft, Dt = bt.astype(np.float64), cft.astype(np.float64), dt.astype(np.float64)
    Be, Ofe, De = be.astype(np.float64), cfe.astype(np.float64), de.astype(np.float64)
    At, Ae = at.astype(np.float64), ae.astype(np.float64)
    Om_t = Bt @ Oft @ Bt.T + np.diag(Dt)
    Om_e = Be @ Ofe @ Be.T + np.diag(De)

    w_est = np.linalg.solve(Om_e, Ae)
    z_true = np.linalg.solve(Om_t, At)
    ref_sre = float((At @ w_est) / (np.sqrt(w_est @ Om_t @ w_est) * np.sqrt(At @ z_true)))

    with tempfile.TemporaryDirectory() as td:
        paths = {}
        for key, arr in [("be", be), ("cfe", cfe), ("de", de), ("ae", ae), ("bt", bt), ("cft", cft), ("dt", dt), ("at", at)]:
            paths[key] = os.path.join(td, f"{key}.f32")
            write_f32(paths[key], arr)

        # Exact match => SRE == 1.0
        p_id = Parser(run_cli(2, paths["bt"], paths["cft"], paths["dt"], paths["at"],
                              paths["bt"], paths["cft"], paths["dt"], paths["at"], n, k))
        got_id = p_id.read_f32()
        err_id = abs(got_id - 1.0)

        # Perturbed => matches ref_sre
        p_pt = Parser(run_cli(2, paths["be"], paths["cfe"], paths["de"], paths["ae"],
                              paths["bt"], paths["cft"], paths["dt"], paths["at"], n, k))
        got_pt = p_pt.read_f32()
        err_pt = abs(got_pt - ref_sre)

        mx = max(err_id, err_pt)
        status = "PASS" if mx <= tol else "FAIL"
        print(f"[{status}] {name} (N={n}, K={k}): id_err={err_id:.2e}, pert_err={err_pt:.2e} (sre={got_pt:.6f})")
        if mx > tol:
            sys.exit(1)


def solve_ref_qp(Omega, alpha, w0, lw, uw, A, lc, uc, c1, c2, rho, gmv_max):
    """Exact reference solver via SciPy SLSQP (splitting |w - w0| and |w| if needed)."""
    from scipy.optimize import minimize
    n = len(alpha)
    has_l1 = bool(np.any(c1 > 0))
    has_gmv = gmv_max > 0.0

    # Variables: [w (n), tp (n), tm (n) if has_l1, wp (n), wm (n) if has_gmv]
    off_t = n
    off_g = n + (2 * n if has_l1 else 0)
    dim = off_g + (2 * n if has_gmv else 0)

    def obj_and_grad(x):
        w = x[:n]
        dw = w - w0
        val = 0.5 * rho * (w @ Omega @ w) - alpha @ w + 0.5 * np.sum(c2 * dw * dw)
        g = np.zeros(dim)
        g[:n] = rho * (Omega @ w) - alpha + c2 * dw
        if has_l1:
            tp = x[off_t:off_t + n]
            tm = x[off_t + n:off_t + 2 * n]
            val += np.sum(c1 * (tp + tm))
            g[off_t:off_t + n] = c1
            g[off_t + n:off_t + 2 * n] = c1
        return val, g

    bounds = list(zip(lw, uw))
    if has_l1:
        bounds += [(0.0, None)] * (2 * n)
    if has_gmv:
        bounds += [(0.0, None)] * (2 * n)

    cons = []
    m = A.shape[0]
    for j in range(m):
        row = A[j]
        if abs(lc[j] - uc[j]) < 1e-12:
            def eq_fun(x, r=row, rhs=lc[j]):
                return float(r @ x[:n] - rhs)
            def eq_jac(x, r=row):
                g = np.zeros(dim); g[:n] = r; return g
            cons.append({"type": "eq", "fun": eq_fun, "jac": eq_jac})
        else:
            if np.isfinite(lc[j]) and lc[j] > -1e15:
                def lo_fun(x, r=row, rhs=lc[j]):
                    return float(r @ x[:n] - rhs)
                def lo_jac(x, r=row):
                    g = np.zeros(dim); g[:n] = r; return g
                cons.append({"type": "ineq", "fun": lo_fun, "jac": lo_jac})
            if np.isfinite(uc[j]) and uc[j] < 1e15:
                def hi_fun(x, r=row, rhs=uc[j]):
                    return float(rhs - r @ x[:n])
                def hi_jac(x, r=row):
                    g = np.zeros(dim); g[:n] = -r; return g
                cons.append({"type": "ineq", "fun": hi_fun, "jac": hi_jac})

    if has_l1:
        # w - w0 - tp + tm == 0
        def l1_eq(x):
            return x[:n] - w0 - x[off_t:off_t + n] + x[off_t + n:off_t + 2 * n]
        J_l1 = np.zeros((n, dim))
        J_l1[:, :n] = np.eye(n)
        J_l1[:, off_t:off_t + n] = -np.eye(n)
        J_l1[:, off_t + n:off_t + 2 * n] = np.eye(n)
        cons.append({"type": "eq", "fun": l1_eq, "jac": lambda x: J_l1})

    if has_gmv:
        def gmv_eq(x):
            return x[:n] - x[off_g:off_g + n] + x[off_g + n:off_g + 2 * n]
        J_ge = np.zeros((n, dim))
        J_ge[:, :n] = np.eye(n)
        J_ge[:, off_g:off_g + n] = -np.eye(n)
        J_ge[:, off_g + n:off_g + 2 * n] = np.eye(n)
        cons.append({"type": "eq", "fun": gmv_eq, "jac": lambda x: J_ge})

        def gmv_ineq(x):
            return gmv_max - np.sum(x[off_g:off_g + 2 * n])
        j_gi = np.zeros(dim)
        j_gi[off_g:off_g + 2 * n] = -1.0
        cons.append({"type": "ineq", "fun": gmv_ineq, "jac": lambda x: j_gi})

    x0 = np.zeros(dim)
    x0[:n] = np.clip(w0, lw, uw)
    if has_l1:
        dw0 = x0[:n] - w0
        x0[off_t:off_t + n] = np.maximum(dw0, 0.0)
        x0[off_t + n:off_t + 2 * n] = np.maximum(-dw0, 0.0)
    if has_gmv:
        x0[off_g:off_g + n] = np.maximum(x0[:n], 0.0)
        x0[off_g + n:off_g + 2 * n] = np.maximum(-x0[:n], 0.0)

    res = minimize(obj_and_grad, x0, jac=True, method="SLSQP", bounds=bounds, constraints=cons,
                   options={"ftol": 1e-13, "maxiter": 1000})
    assert res.success, f"SLSQP failed: {res.message}"
    return res.x[:n]


def eval_obj(Omega, alpha, w0, c1, c2, rho, w):
    dw = w - w0
    return float(0.5 * rho * (w @ Omega @ w) - alpha @ w + 0.5 * np.sum(c2 * dw * dw) + np.sum(c1 * np.abs(dw)))


def test_constrained_case(name, n, k, A_fn, lw, uw, lc, uc, c1, c2, rho, gmv_max=0.0,
                          max_iters=2000, abs_tol=1e-6, rel_tol=1e-5, seed=10,
                          check_scipy=True, tol_w=2e-3, tol_obj=1e-4, tol_feas=5e-5):
    import time
    rng = np.random.default_rng(seed)
    b, cov_f, d = make_factor_model(rng, n, k, cond_f=25.0)
    alpha = (rng.standard_normal(n) * 0.01).astype(np.float32)
    w0 = (rng.standard_normal(n) * 0.05).astype(np.float32)
    B = b.astype(np.float64)
    Of = cov_f.astype(np.float64)
    D = d.astype(np.float64)
    Omega = B @ Of @ B.T + np.diag(D)

    A_mat = A_fn(B).astype(np.float32)
    m = A_mat.shape[0]
    lw32 = np.asarray(lw, dtype=np.float32)
    uw32 = np.asarray(uw, dtype=np.float32)
    lc32 = np.asarray(lc, dtype=np.float32)
    uc32 = np.asarray(uc, dtype=np.float32)
    c1_32 = np.asarray(c1, dtype=np.float32)
    c2_32 = np.asarray(c2, dtype=np.float32)

    with tempfile.TemporaryDirectory() as td:
        files = {}
        for key, arr in [("b", b), ("cf", cov_f), ("d", d), ("a", alpha), ("w0", w0),
                         ("lw", lw32), ("uw", uw32), ("amat", A_mat), ("lc", lc32), ("uc", uc32),
                         ("c1", c1_32), ("c2", c2_32)]:
            files[key] = os.path.join(td, f"{key}.f32")
            write_f32(files[key], arr)
        pp = os.path.join(td, "params.f32")
        write_f32(pp, np.array([rho, gmv_max, abs_tol, rel_tol, 0.0, 1.6], dtype=np.float32))

        t0 = time.perf_counter()
        p = Parser(run_cli(3, files["b"], files["cf"], files["d"], files["a"], files["w0"],
                           files["lw"], files["uw"], files["amat"], files["lc"], files["uc"],
                           files["c1"], files["c2"], pp, n, k, m, max_iters))
        dt_ms = (time.perf_counter() - t0) * 1000.0
        opt = p.read_opt()
        assert opt is not None, f"{name}: returned None"
        w_got = opt["weights"]

    A64 = A_mat.astype(np.float64)
    lw64, uw64 = lw32.astype(np.float64), uw32.astype(np.float64)
    lc64, uc64 = lc32.astype(np.float64), uc32.astype(np.float64)
    c1_64, c2_64 = c1_32.astype(np.float64), c2_32.astype(np.float64)
    a64, w064 = alpha.astype(np.float64), w0.astype(np.float64)

    box_viol = float(max(np.max(np.maximum(lw64 - w_got, 0.0)), np.max(np.maximum(w_got - uw64, 0.0))))
    lin_viol = 0.0
    if m > 0:
        aw = A64 @ w_got
        lin_viol = float(max(np.max(np.maximum(lc64 - aw, 0.0)), np.max(np.maximum(aw - uc64, 0.0))))
    gmv_viol = float(max(0.0, np.sum(np.abs(w_got)) - gmv_max)) if gmv_max > 0.0 else 0.0
    max_viol = max(box_viol, lin_viol, gmv_viol)

    obj_got = eval_obj(Omega, a64, w064, c1_64, c2_64, rho, w_got)

    extra = ""
    ok = opt["converged"] and max_viol <= tol_feas
    if check_scipy:
        w_ref = solve_ref_qp(Omega, a64, w064, lw64, uw64, A64, lc64, uc64, c1_64, c2_64, rho, gmv_max)
        obj_ref = eval_obj(Omega, a64, w064, c1_64, c2_64, rho, w_ref)
        w_err = rel_err(w_got, w_ref)
        obj_err = abs(obj_got - obj_ref) / max(abs(obj_ref), 1e-12)
        extra = f", w_err={w_err:.2e}, obj_err={obj_err:.2e}"
        ok = ok and w_err <= tol_w and obj_err <= tol_obj

    status = "PASS" if ok else "FAIL"
    print(f"[{status}] admm/{name} (N={n}, K={k}, M={m}): iters={opt['iters']}, conv={opt['converged']}, viol={max_viol:.2e}{extra}, {dt_ms:.1f}ms")
    if not ok:
        print(f"   primal_res={opt['primal_res']:.2e}, dual_res={opt['dual_res']:.2e}, box={box_viol:.2e}, lin={lin_viol:.2e}, gmv={gmv_viol:.2e}")
        sys.exit(1)


def test_trade_costs():
    rng = np.random.default_rng(99)
    n = 40
    w = rng.standard_normal(n).astype(np.float32)
    w0 = rng.standard_normal(n).astype(np.float32)
    c1 = np.exp(rng.uniform(-7, -4, size=n)).astype(np.float32)
    c2 = np.exp(rng.uniform(-5, -2, size=n)).astype(np.float32)
    sig = np.exp(rng.uniform(-4, -2, size=n)).astype(np.float32)
    adv = np.exp(rng.uniform(2, 6, size=n)).astype(np.float32)
    kappa, beta = 0.5, 0.6

    with tempfile.TemporaryDirectory() as td:
        paths = {}
        for k, arr in [("w", w), ("w0", w0), ("c1", c1), ("c2", c2), ("sig", sig), ("adv", adv)]:
            paths[k] = os.path.join(td, f"{k}.f32")
            write_f32(paths[k], arr)
        pp = os.path.join(td, "p.f32")
        write_f32(pp, np.array([kappa, beta], dtype=np.float32))
        p = Parser(run_cli(4, paths["w"], paths["w0"], paths["c1"], paths["c2"], paths["sig"], paths["adv"], pp, n))
        got_l = p.read_f32()
        got_q = p.read_f32()
        got_p = p.read_f32()

    dw = np.abs(w.astype(np.float64) - w0.astype(np.float64))
    ref_l = float(np.sum(c1.astype(np.float64) * dw))
    ref_q = float(0.5 * np.sum(c2.astype(np.float64) * dw * dw))
    ref_p = float(np.sum(kappa * sig.astype(np.float64) * (dw / adv.astype(np.float64)) ** beta * dw))
    errs = [abs(got_l - ref_l) / ref_l, abs(got_q - ref_q) / ref_q, abs(got_p - ref_p) / ref_p]
    mx = max(errs)
    status = "PASS" if mx <= 2e-6 else "FAIL"
    print(f"[{status}] trade_costs (N={n}): max_err={mx:.2e}")
    if mx > 2e-6:
        sys.exit(1)


def test_hedging():
    rng = np.random.default_rng(201)
    n, k, m = 40, 6, 4
    b, cov_f, d = make_factor_model(rng, n, k, cond_f=30.0)
    wc = rng.standard_normal(n).astype(np.float32)
    wh = rng.standard_normal(n).astype(np.float32)
    hmat = rng.standard_normal((n, m)).astype(np.float32)
    bh = (rng.standard_normal(n) * 0.8 + 0.5).astype(np.float32)
    se = np.exp(rng.uniform(-2.5, -0.8, size=n)).astype(np.float32)
    # Correlated error covariance Omega_eta (Ch 12.3 step 4)
    rho_eta = 0.25
    corr = (1.0 - rho_eta) * np.eye(n) + rho_eta * np.ones((n, n))
    ceta = (np.outer(se, se) * corr).astype(np.float32)
    mu_h, sig_h = 0.002, 0.015

    B, Of, D = b.astype(np.float64), cov_f.astype(np.float64), d.astype(np.float64)
    Om = B @ Of @ B.T + np.diag(D)
    Wc, Wh, H = wc.astype(np.float64), wh.astype(np.float64), hmat.astype(np.float64)
    Bh, Se, Ceta = bh.astype(np.float64), se.astype(np.float64), ceta.astype(np.float64)

    with tempfile.TemporaryDirectory() as td:
        paths = {}
        for key, arr in [("b", b), ("cf", cov_f), ("d", d), ("wc", wc), ("wh", wh),
                         ("hmat", hmat), ("bh", bh), ("se", se), ("ceta", ceta)]:
            paths[key] = os.path.join(td, f"{key}.f32")
            write_f32(paths[key], arr)
        pp = os.path.join(td, "p.f32")
        write_f32(pp, np.array([mu_h, sig_h], dtype=np.float32))
        p = Parser(run_cli(5, paths["b"], paths["cf"], paths["d"], paths["wc"], paths["wh"],
                           paths["hmat"], paths["bh"], paths["se"], paths["ceta"], pp, n, k, m))
        got_ratio = p.read_f32()
        got_inst = p.read_vec()
        got_fex = p.read_vec()
        got_sh = p.read_shrink()
        got_shc = p.read_shrink()
        got_trk = p.read_vec()
        got_trk0 = p.read_vec()

    ref_ratio = -float((Wc @ Om @ Wh) / (Wh @ Om @ Wh))
    ref_inst = -np.linalg.solve(H.T @ Om @ H, H.T @ Om @ Wc)
    G = B.T @ np.diag(1.0 / D) @ B
    P_fmp = np.diag(1.0 / D) @ B @ np.linalg.inv(G)
    ref_fex = -P_fmp @ (B.T @ Wc)
    raw = float(Wc @ Bh)
    ev = float(np.sum((Wc * Se) ** 2))
    yh = max(0.0, 1.0 - ev / (raw * raw))
    ref_sh = [raw, ev, yh, -yh * raw]
    evc = float(Wc @ Ceta @ Wc)
    yhc = max(0.0, 1.0 - evc / (raw * raw))
    ref_shc = [raw, evc, yhc, -yhc * raw]
    ref_trk = np.linalg.solve(Om + (mu_h ** 2) * np.diag(Se ** 2) + (mu_h ** 2) * np.outer(Bh, Bh), (mu_h ** 2 + sig_h ** 2) * Bh)
    ref_trk0 = np.linalg.solve(Om, (sig_h ** 2) * Bh)

    errs = {
        "ratio": abs(got_ratio - ref_ratio) / abs(ref_ratio),
        "instruments": rel_err(got_inst, ref_inst),
        "factor_exact": rel_err(got_fex, ref_fex),
        "factor_exact_zero_exp": float(np.linalg.norm(B.T @ (Wc + got_fex))),
        "shrink": rel_err(got_sh, ref_sh),
        "shrink_cov": rel_err(got_shc, ref_shc),
        "track": rel_err(got_trk, ref_trk),
        "track_mu0": rel_err(got_trk0, ref_trk0),
    }
    mx = max(errs.values())
    worst = max(errs, key=errs.get)
    status = "PASS" if mx <= 2e-5 else "FAIL"
    print(f"[{status}] hedging (N={n}, K={k}, M={m}): max_err={mx:.2e} ({worst})")
    if mx > 2e-5:
        for kk, vv in errs.items():
            if vv > 2e-5:
                print(f"   {kk}: {vv:.2e}")
        sys.exit(1)


def test_sizing():
    rng = np.random.default_rng(202)
    mu, sig, frac, max_dd, cur_dd = 0.0008, 0.01, 0.5, 0.25, 0.10
    rets = (rng.standard_normal(200) * sig + mu).astype(np.float32)
    # Inject a crash to test drawdown stop-out
    rets[50:65] = -0.025

    with tempfile.TemporaryDirectory() as td:
        rp_ret = os.path.join(td, "rets.f32")
        pp = os.path.join(td, "p.f32")
        write_f32(rp_ret, rets)
        write_f32(pp, np.array([mu, sig, frac, max_dd, cur_dd], dtype=np.float32))
        p = Parser(run_cli(6, rp_ret, pp, len(rets)))
        got_k = p.read_f32()
        got_kd = p.read_f32()
        got_fk = p.read_f32()
        got_gz = p.read_f32()
        got_gz_stop = p.read_f32()
        got_path = p.read_dd()

    ref_k = mu / (sig ** 2)
    ref_kd = mu / (mu ** 2 + sig ** 2)
    ref_fk = frac * ref_k
    ref_gz = ref_k * max(0.0, 1.0 - (1.0 - max_dd) / (1.0 - cur_dd))

    w, m, f = 1.0, 1.0, ref_k * max_dd
    ref_path = []
    for r in rets.astype(np.float64):
        w = max(0.0, w * (1.0 + f * r))
        m = max(m, w)
        dd = 1.0 - w / m if m > 0 else 1.0
        f = ref_k * max(0.0, 1.0 - (1.0 - max_dd) / (1.0 - dd)) if dd < 1.0 else 0.0
        ref_path.append([w, m, dd, f])
    ref_path = np.array(ref_path)

    errs = {
        "kelly": abs(got_k - ref_k) / ref_k,
        "kelly_disc": abs(got_kd - ref_kd) / ref_kd,
        "frac_kelly": abs(got_fk - ref_fk) / ref_fk,
        "gz": abs(got_gz - ref_gz) / ref_gz,
        "gz_stop": abs(got_gz_stop),
        "gz_path": rel_err(got_path, ref_path),
    }
    mx = max(errs.values())
    status = "PASS" if mx <= 2e-5 else "FAIL"
    print(f"[{status}] sizing (T={len(rets)}): max_err={mx:.2e}, max_dd_realized={np.max(got_path[:, 2]):.4f}")
    if mx > 2e-5:
        print(errs)
        sys.exit(1)


def test_attribution_and_forward():
    rng = np.random.default_rng(203)
    n, k = 50, 6
    b, cov_f, d = make_factor_model(rng, n, k, cond_f=25.0)
    w = rng.standard_normal(n).astype(np.float32)
    f_true = (rng.standard_normal(k) * 0.01).astype(np.float32)
    eps_true = (rng.standard_normal(n) * np.sqrt(d)).astype(np.float32)
    r = (b @ f_true + eps_true).astype(np.float32)
    rpnl = float(np.dot(w.astype(np.float64), r.astype(np.float64)) - 0.0042)

    B, Of, D = b.astype(np.float64), cov_f.astype(np.float64), d.astype(np.float64)
    W, R, Fr, Eps = w.astype(np.float64), r.astype(np.float64), f_true.astype(np.float64), eps_true.astype(np.float64)

    with tempfile.TemporaryDirectory() as td:
        paths = {}
        for key, arr in [("b", b), ("cf", cov_f), ("d", d), ("w", w), ("r", r), ("fr", f_true), ("eps", eps_true)]:
            paths[key] = os.path.join(td, f"{key}.f32")
            write_f32(paths[key], arr)
        pp = os.path.join(td, "p.f32")
        write_f32(pp, np.array([rpnl], dtype=np.float32))
        p = Parser(run_cli(7, paths["b"], paths["cf"], paths["d"], paths["w"], paths["r"],
                           paths["fr"], paths["eps"], pp, n, k))
        got_fhat = p.read_vec()
        got_aev = p.read_f32()
        got_pa = p.read_pattr()
        got_ma = p.read_mattr()
        got_ng = p.read_nested()
        got_ss = p.read_ss()

    G = B.T @ np.diag(1.0 / D) @ B
    ref_fhat = np.linalg.solve(G, B.T @ (R / D))
    b_exp = B.T @ W
    ref_aev = float(b_exp @ np.linalg.inv(G) @ b_exp)
    ref_pos = float(W @ R)
    ref_fc = b_exp * Fr
    ref_ic = W * (R - B @ Fr)

    # Maximal attribution on S = [0, 2], Sbar = [1, 3, 4, 5]
    S, Sb = [0, 2], [1, 3, 4, 5]
    Oss = Of[np.ix_(S, S)]
    Osb = Of[np.ix_(S, Sb)]
    Obb = Of[np.ix_(Sb, Sb)]
    X = np.linalg.solve(Oss, Osb)
    ref_adj = b_exp[S] + X @ b_exp[Sb]
    ref_rf = Fr[Sb] - X.T @ Fr[S]
    ref_rc = Obb - Osb.T @ X
    ref_sp = float(ref_adj @ Fr[S])
    ref_rp = float(b_exp[Sb] @ ref_rf)
    tot_fpnl = float(b_exp @ Fr)

    # Selection vs sizing exact identity
    sig = np.sqrt(D)
    w_t = sig * W
    vol = np.linalg.norm(w_t, 2)
    ref_ir = float(np.dot(W, Eps) / vol)

    errs = {
        "est_fhat": rel_err(got_fhat, ref_fhat),
        "aev": abs(got_aev - ref_aev) / ref_aev,
        "pa_pos": abs(got_pa["pos"] - ref_pos) / max(abs(ref_pos), 1e-12),
        "pa_identity": abs((got_pa["factor"] + got_pa["idio"]) - got_pa["pos"]) / max(abs(ref_pos), 1e-12),
        "pa_trading": abs((got_pa["pos"] + got_pa["trading"]) - rpnl) / max(abs(rpnl), 1e-12),
        "pa_fc": rel_err(got_pa["fc"], ref_fc),
        "pa_ic": rel_err(got_pa["ic"], ref_ic),
        "ma_adj": rel_err(got_ma["adj"], ref_adj),
        "ma_rf": rel_err(got_ma["rf"], ref_rf),
        "ma_rc": rel_err(got_ma["rc"], ref_rc),
        "ma_sum": abs((got_ma["subset_pnl"] + got_ma["resid_pnl"]) - tot_fpnl) / max(abs(tot_fpnl), 1e-12),
        "nested_sum": abs(sum(g["pnl"] for g in got_ng) - tot_fpnl) / max(abs(tot_fpnl), 1e-12),
        "nested_g0": abs(got_ng[0]["pnl"] - ref_sp) / max(abs(ref_sp), 1e-12),
        "ss_ir": abs(got_ss["ir"] - ref_ir) / max(abs(ref_ir), 1e-12),
        "ss_identity": abs((got_ss["sel"] * got_ss["div"] + got_ss["siz"]) - got_ss["ir"]) / max(abs(ref_ir), 1e-12),
        "ss_ls_split": abs((got_ss["q_l"] * got_ss["sel_l"] + got_ss["q_s"] * got_ss["sel_s"]) - got_ss["sel"]) / max(abs(got_ss["sel"]), 1e-12),
    }
    mx = max(errs.values())
    worst = max(errs, key=errs.get)
    status = "PASS" if mx <= 2e-5 else "FAIL"
    print(f"[{status}] attribution (N={n}, K={k}): max_err={mx:.2e} ({worst})")
    if mx > 2e-5:
        for kk, vv in errs.items():
            if vv > 2e-5:
                print(f"   {kk}: {vv:.2e}")
        sys.exit(1)

    # Forward PnL & forward attribution (T=80 triggers parallel pmap!)
    T = 80
    W_pan = rng.standard_normal((T, n)).astype(np.float32)
    F_pan = (rng.standard_normal((T, k)) * 0.01).astype(np.float32)
    R_pan = (F_pan @ b.T + rng.standard_normal((T, n)) * np.sqrt(d)).astype(np.float32)
    with tempfile.TemporaryDirectory() as td:
        paths = {}
        for key, arr in [("b", b), ("cf", cov_f), ("d", d), ("w", W_pan), ("r", R_pan), ("fr", F_pan)]:
            paths[key] = os.path.join(td, f"{key}.f32")
            write_f32(paths[key], arr)
        p2 = Parser(run_cli(8, paths["b"], paths["cf"], paths["d"], paths["w"], paths["r"], paths["fr"], T, n, k))
        got_fpnl = p2.read_vec()
        got_fattr = p2.read_fattr()

    ref_fpnl = np.sum(W_pan[:-1].astype(np.float64) * R_pan[1:].astype(np.float64), axis=1)
    assert len(got_fpnl) == T - 1 and len(got_fattr) == T - 1
    e_fpnl = rel_err(got_fpnl, ref_fpnl)
    e_fattr = max(abs(got_fattr[t]["pos"] - ref_fpnl[t]) / max(abs(ref_fpnl[t]), 1e-6) for t in range(T - 1))
    # Verify NO lookahead: same-day dot product should differ wildly
    same_day = np.sum(W_pan[:-1].astype(np.float64) * R_pan[:-1].astype(np.float64), axis=1)
    assert rel_err(got_fpnl, same_day) > 0.5
    mx2 = max(e_fpnl, e_fattr)
    status2 = "PASS" if mx2 <= 2e-5 else "FAIL"
    print(f"[{status2}] forward_parallel (T={T}, N={n}, K={k}): pnl_err={e_fpnl:.2e}, attr_err={e_fattr:.2e}")
    if mx2 > 2e-5:
        sys.exit(1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-build", action="store_true")
    args = ap.parse_args()
    if not args.no_build:
        build()

    test_risk_and_mvo("small", n=12, k=3, cond_f=10.0, seed=1)
    test_risk_and_mvo("zero_factors", n=15, k=0, cond_f=1.0, seed=2)
    test_risk_and_mvo("medium_parallel", n=80, k=10, cond_f=100.0, seed=3)
    test_risk_and_mvo("large_ill_cond", n=250, k=20, cond_f=1e4, seed=4, tol=2e-4)
    test_sre("sre_medium", n=100, k=12, seed=5)
    test_trade_costs()

    # Constrained MVO (ADMM) tests
    test_constrained_case("unconstrained_quad", n=20, k=4,
                          A_fn=lambda B: np.zeros((0, B.shape[0])),
                          lw=np.full(20, -1e6), uw=np.full(20, 1e6),
                          lc=np.zeros(0), uc=np.zeros(0),
                          c1=np.zeros(20), c2=np.full(20, 0.01), rho=2.0, seed=11)
    test_constrained_case("long_only_budget", n=25, k=5,
                          A_fn=lambda B: np.ones((1, B.shape[0])),
                          lw=np.zeros(25), uw=np.full(25, 0.15),
                          lc=np.array([1.0]), uc=np.array([1.0]),
                          c1=np.zeros(25), c2=np.zeros(25), rho=5.0, seed=12)
    test_constrained_case("factor_neutral_box", n=30, k=5,
                          A_fn=lambda B: B.T,
                          lw=np.full(30, -0.15), uw=np.full(30, 0.15),
                          lc=np.zeros(5), uc=np.zeros(5),
                          c1=np.zeros(30), c2=np.zeros(30), rho=3.0, seed=13)
    test_constrained_case("gmv_dollar_neutral", n=20, k=4,
                          A_fn=lambda B: np.ones((1, B.shape[0])),
                          lw=np.full(20, -0.25), uw=np.full(20, 0.25),
                          lc=np.array([0.0]), uc=np.array([0.0]),
                          c1=np.zeros(20), c2=np.zeros(20), rho=1.0, gmv_max=1.5, seed=14)
    test_constrained_case("l1_l2_factor_bounds", n=25, k=4,
                          A_fn=lambda B: np.vstack([np.ones((1, B.shape[0])), B.T]),
                          lw=np.full(25, -0.2), uw=np.full(25, 0.2),
                          lc=np.array([0.0, -0.05, -0.05, -0.05, -0.05]),
                          uc=np.array([0.0, 0.05, 0.05, 0.05, 0.05]),
                          c1=np.full(25, 0.002), c2=np.full(25, 0.02), rho=2.0, seed=15)
    test_constrained_case("diag_k0_l1_gmv", n=20, k=0,
                          A_fn=lambda B: np.zeros((0, B.shape[0])),
                          lw=np.full(20, -0.2), uw=np.full(20, 0.2),
                          lc=np.zeros(0), uc=np.zeros(0),
                          c1=np.full(20, 0.001), c2=np.full(20, 0.01), rho=2.0, gmv_max=1.2, seed=16)
    test_constrained_case("book_200x15_full", n=200, k=15,
                          A_fn=lambda B: np.vstack([np.ones((1, B.shape[0])), B.T]),
                          lw=np.full(200, -0.03), uw=np.full(200, 0.03),
                          lc=np.concatenate([[0.0], np.full(15, -0.02)]),
                          uc=np.concatenate([[0.0], np.full(15, 0.02)]),
                          c1=np.full(200, 0.0005), c2=np.full(200, 0.005), rho=2.0, gmv_max=2.0,
                          max_iters=2000, abs_tol=1e-5, rel_tol=1e-4, seed=17,
                          check_scipy=False, tol_feas=1e-4)

    # Hedging (Ch 12), Dynamic Sizing (Ch 13), Attribution & Forward Parallel (Ch 14)
    test_hedging()
    test_sizing()
    test_attribution_and_forward()
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
