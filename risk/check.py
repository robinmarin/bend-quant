#!/usr/bin/env python3
"""Numerical verification suite for bend-quant-risk (Paleologo Ch 4-7)
against NumPy, SciPy, scikit-learn (LedoitWolf), and statsmodels (cov_hac).
"""
import argparse
import os
import subprocess
import sys
import tempfile
import numpy as np
from scipy import linalg as sla
from scipy.special import digamma
from sklearn.covariance import LedoitWolf
from statsmodels.stats.sandwich_covariance import weights_bartlett

ROOT = os.path.dirname(os.path.abspath(__file__))
BEND = "/Users/robin/.bend/bin/bend"
BIN = os.path.join(ROOT, "out", "check")


def build():
    os.makedirs(os.path.join(ROOT, "out"), exist_ok=True)
    res = subprocess.run([BEND, "check.bend", "-o", "out/check"], cwd=ROOT, capture_output=True, text=True)
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
        line = self.next_line()
        if n == 0:
            return np.zeros(0, dtype=np.float64)
        return np.array([float(x) for x in line.split()], dtype=np.float64)

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

    def read_u32(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "U32", f"Expected U32, got {hdr}"
        return int(hdr[1])

    def read_fm(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "FM", f"Expected FM, got {hdr}"
        return {"b": self.read_mat(), "cov_f": self.read_mat(), "idio_var": self.read_vec()}

    def read_fms(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "FMS", f"Expected FMS, got {hdr}"
        cnt = int(hdr[1])
        return [self.read_fm() for _ in range(cnt)]

    def read_group_risk(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "GRISK", f"Expected GRISK, got {hdr}"
        return {
            "total_factor_var": float(hdr[1]),
            "total_factor_vol": float(hdr[2]),
            "group_cov": self.read_mat(),
            "group_vars": self.read_vec(),
            "group_shares": self.read_vec(),
            "group_mcr": self.read_vec(),
        }

    def read_qdist(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "QDIST", f"Expected QDIST, got {hdr}"
        return {"mean": float(hdr[1]), "total": float(hdr[2]), "per_period": self.read_vec()}

    def read_mahal(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "MAHAL", f"Expected MAHAL, got {hdr}"
        return {"mean_nu": float(hdr[1]), "malv": float(hdr[2]), "nu": self.read_vec()}

    def read_mvp(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "MVP", f"Expected MVP, got {hdr}"
        v = [float(x) for x in hdr[1:]]
        return {
            "realized_var": v[0], "realized_vol": v[1], "mean_pred_vol": v[2],
            "qlike": v[3], "vol_mse": v[4], "bias_stat": v[5],
            "returns": self.read_vec(), "pred_vars": self.read_vec(),
        }

    def read_voleval(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "VOLEVAL", f"Expected VOLEVAL, got {hdr}"
        return {
            "qlike": float(hdr[1]), "vol_mse": float(hdr[2]), "bias_stat": float(hdr[3]),
            "realized_vol": float(hdr[4]), "mean_pred_vol": float(hdr[5]), "count": int(hdr[6]),
        }

    def read_turnover(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "TURN", f"Expected TURN, got {hdr}"
        return {"mean": float(hdr[1]), "per_period": self.read_vec()}

    def read_betaerr(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "BERR", f"Expected BERR, got {hdr}"
        return {"total": float(hdr[1]), "mean": float(hdr[2]), "per_period": self.read_vec()}

    def read_shrink(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "SHRINK", f"Expected SHRINK, got {hdr}"
        return {"shrinkage": float(hdr[1]), "target_diag": float(hdr[2]), "cov": self.read_mat()}

    def read_pairs(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "PAIRS", f"Expected PAIRS, got {hdr}"
        cnt = int(hdr[1])
        out = []
        for _ in range(cnt):
            a, b, c = self.next_line().split()
            out.append((int(a), int(b), float(c)))
        return out

    def read_rebase(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "REBASE", f"Expected REBASE, got {hdr}"
        return {"c_loadings": self.read_mat(), "cov_c": self.read_mat()}

    def read_csreg(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "CSREG", f"Expected CSREG, got {hdr}"
        return {"f_ret": self.read_vec(), "resid": self.read_vec(), "est_cov": self.read_mat()}

    def read_fser(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "FSER", f"Expected FSER, got {hdr}"
        return {"f_rets": self.read_mat(), "resid": self.read_mat()}

    def read_fundfit(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "FUNDFIT", f"Expected FUNDFIT, got {hdr}"
        return {"model": self.read_fm(), "f_rets": self.read_mat(), "resid": self.read_mat()}

    def read_pca(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "PCA", f"Expected PCA, got {hdr}"
        return {
            "loadings": self.read_mat(), "f_rets": self.read_mat(),
            "singular_values": self.read_vec(), "eigenvalues": self.read_vec(),
        }

    def read_baing(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "BAING", f"Expected BAING, got {hdr}"
        return {"k_ic": int(hdr[1]), "k_pc": int(hdr[2]), "ic": self.read_vec(), "pc": self.read_vec()}

    def read_eigto(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "EIGTO", f"Expected EIGTO, got {hdr}"
        return {"mean": float(hdr[1]), "per_factor": self.read_vec()}

    def read_statfit(self):
        hdr = self.next_line().split()
        if hdr[0] == "NONE":
            return None
        assert hdr[0] == "STATFIT", f"Expected STATFIT, got {hdr}"
        return {
            "model": self.read_fm(), "f_rets": self.read_mat(),
            "resid": self.read_mat(), "singular_values": self.read_vec(),
        }


def rel_err(got, ref):
    got = np.asarray(got, dtype=np.float64)
    ref = np.asarray(ref, dtype=np.float64)
    denom = max(float(np.linalg.norm(ref)), 1e-12)
    return float(np.linalg.norm(got - ref) / denom)


def fm_cov(fm):
    b, cf, d = fm["b"], fm["cov_f"], fm["idio_var"]
    return b @ cf @ b.T + np.diag(d)


def make_spd(rng, k, lo=1e-4, hi=2e-3):
    q, _ = np.linalg.qr(rng.standard_normal((k, k)))
    eigs = np.geomspace(lo, hi, k)
    m = q @ np.diag(eigs) @ q.T
    return (0.5 * (m + m.T)).astype(np.float32)


def ewma_w_ref(t, hl):
    lam = 2.0 ** (-1.0 / hl)
    idx = np.arange(t - 1, -1, -1, dtype=np.float64)
    w = lam ** idx
    return w / np.sum(w)


def report(name, errs, tol):
    mx = max(errs.values())
    worst = max(errs, key=errs.get)
    ok = mx <= tol
    print(f"[{'PASS' if ok else 'FAIL'}] {name}: max_err={mx:.2e} ({worst}, tol={tol:.1e})")
    if not ok:
        for k, v in errs.items():
            if v > tol:
                print(f"   {k}: {v:.2e}")
        sys.exit(1)


# ===================================================================== Chapter 4
def test_ch4():
    rng = np.random.default_rng(401)
    n, k, p = 35, 6, 3
    # Make column 0 of B equal to ones so B @ a_vec = 1 with a_vec = [1, 0, ..., 0]
    b = (rng.standard_normal((n, k)) * 0.6).astype(np.float32)
    b[:, 0] = 1.0
    cf = make_spd(rng, k, 1e-4, 1.5e-3)
    d = np.exp(rng.uniform(-6.0, -3.5, size=n)).astype(np.float32)
    cmat = (rng.standard_normal((k, k)) * 0.5 + np.eye(k) * 1.2).astype(np.float32)
    amat = (rng.standard_normal((n, p)) * 0.7).astype(np.float32)
    cg = make_spd(rng, p, 2e-4, 1e-3)
    dnew = np.exp(rng.uniform(-6.2, -3.8, size=n)).astype(np.float32)
    avec = np.zeros(k, dtype=np.float32); avec[0] = 1.0
    sh = (rng.standard_normal(k) * 0.15).astype(np.float32); sh[0] = 0.0
    sc = np.exp(rng.uniform(-0.3, 0.3, size=k)).astype(np.float32)
    w = rng.standard_normal(n).astype(np.float32)

    with tempfile.TemporaryDirectory() as td:
        ps = {}
        for key, arr in [("b", b), ("cf", cf), ("d", d), ("c", cmat), ("a", amat),
                         ("cg", cg), ("dn", dnew), ("av", avec), ("sh", sh), ("sc", sc), ("w", w)]:
            ps[key] = os.path.join(td, f"{key}.f32")
            write_f32(ps[key], arr)
        par = Parser(run_cli(0, ps["b"], ps["cf"], ps["d"], ps["c"], ps["a"], ps["cg"],
                             ps["dn"], ps["av"], ps["sh"], ps["sc"], ps["w"], n, k, p))
        g_rot = par.read_fm()
        g_id = par.read_fm()
        g_orth = par.read_fm()
        g_zs = par.read_fm()
        g_proj = par.read_fm()
        g_po_h = par.read_mat()
        g_po_m = par.read_fm()
        g_gr = par.read_group_risk()

    B, Cf, D = b.astype(np.float64), cf.astype(np.float64), d.astype(np.float64)
    C, A, Cg, Dn = cmat.astype(np.float64), amat.astype(np.float64), cg.astype(np.float64), dnew.astype(np.float64)
    Av, Sh, Sc, W = avec.astype(np.float64), sh.astype(np.float64), sc.astype(np.float64), w.astype(np.float64)
    Om_orig = B @ Cf @ B.T + np.diag(D)

    # Projection reference
    H_proj = np.linalg.lstsq(A, B, rcond=None)[0]
    DB = B - A @ H_proj
    ref_proj_covg = H_proj @ Cf @ H_proj.T
    ref_proj_d = D + np.sum((DB @ Cf) * DB, axis=1)

    # Pushout reference: H = (I - B (B^T D^{-1} B)^{-1} B^T D^{-1}) A
    G_w = B.T @ (B / D[:, None])
    ref_po_h = A - B @ np.linalg.solve(G_w, B.T @ (A / D[:, None]))

    # Group risk reference: groups [[0,1], [2,3], [4,5]]
    b_exp = B.T @ W
    grps = [[0, 1], [2, 3], [4, 5]]
    E = np.zeros((3, k))
    for gi, grp in enumerate(grps):
        for j in grp:
            E[gi, j] = b_exp[j]
    ref_gcov = E @ Cf @ E.T
    ref_tfv = float(b_exp @ Cf @ b_exp)
    ref_tvol = np.sqrt(ref_tfv)
    ref_rsums = np.sum(ref_gcov, axis=1)
    ref_gshares = ref_rsums / ref_tfv
    ref_gvars = np.diag(ref_gcov)
    ref_gmcr = ref_rsums / (np.sqrt(ref_gvars) * ref_tvol)

    # Z-score transformed loadings reference: (B + 1 * sh^T) diag(sc)
    ref_zs_b = (B + np.outer(np.ones(n), Sh)) * Sc[None, :]

    errs = {
        "rot_cov_invar": rel_err(fm_cov(g_rot), Om_orig),
        "rot_sym": float(np.max(np.abs(g_rot["cov_f"] - g_rot["cov_f"].T))),
        "id_cov_invar": rel_err(fm_cov(g_id), Om_orig),
        "id_cov_is_I": rel_err(g_id["cov_f"], np.eye(k)),
        "orth_cov_invar": rel_err(fm_cov(g_orth), Om_orig),
        "orth_BtB_is_I": rel_err(g_orth["b"].T @ g_orth["b"], np.eye(k)),
        "zs_cov_invar": rel_err(fm_cov(g_zs), Om_orig),
        "zs_loadings": rel_err(g_zs["b"], ref_zs_b),
        "proj_cov_f": rel_err(g_proj["cov_f"], ref_proj_covg),
        "proj_idio": rel_err(g_proj["idio_var"], ref_proj_d),
        "proj_trace_preserve": abs(float(np.trace(fm_cov(g_proj)) - np.trace(Om_orig))) / float(np.trace(Om_orig)),
        "pushout_H": rel_err(g_po_h, ref_po_h),
        "pushout_orth": float(np.linalg.norm(g_po_h.T @ (B / D[:, None])) / max(np.linalg.norm(B), 1e-12)),
        "pushout_model_b": rel_err(g_po_m["b"], np.hstack([B, ref_po_h])),
        "pushout_model_cf": rel_err(g_po_m["cov_f"], sla.block_diag(Cf, Cg)),
        "grisk_cov": rel_err(g_gr["group_cov"], ref_gcov),
        "grisk_shares": rel_err(g_gr["group_shares"], ref_gshares),
        "grisk_shares_sum1": abs(float(np.sum(g_gr["group_shares"])) - 1.0),
        "grisk_mcr": rel_err(g_gr["group_mcr"], ref_gmcr),
    }
    report("ch4_transformations_and_group_risk", errs, tol=5e-5)


# ===================================================================== Chapter 5
def test_ch5():
    rng = np.random.default_rng(501)
    t, n, k = 30, 25, 5
    vhat = np.exp(rng.uniform(-9.0, -7.0, size=t)).astype(np.float32)
    r1d = (rng.standard_normal(t) * np.sqrt(vhat) * 1.1).astype(np.float32)

    bs = np.empty((t, n, k), dtype=np.float32)
    cfs = np.empty((t, k, k), dtype=np.float32)
    ds = np.empty((t, n), dtype=np.float32)
    rets = np.empty((t, n), dtype=np.float32)
    ws = rng.standard_normal((t, n)).astype(np.float32)
    bvec = (np.ones(n) / n + rng.standard_normal(n) * 0.01).astype(np.float32)
    wref = (np.ones(n) / n).astype(np.float32)
    hl_beta = 10.0

    b0 = (rng.standard_normal((n, k)) * 0.5).astype(np.float32)
    cf0 = make_spd(rng, k, 1e-4, 8e-4)
    d0 = np.exp(rng.uniform(-8.0, -6.0, size=n)).astype(np.float32)
    for ti in range(t):
        bs[ti] = (b0 + rng.standard_normal((n, k)) * 0.03).astype(np.float32)
        cfs[ti] = (cf0 * (1.0 + 0.05 * np.sin(ti))).astype(np.float32)
        ds[ti] = (d0 * np.exp(rng.uniform(-0.1, 0.1, size=n))).astype(np.float32)
        Lf = np.linalg.cholesky(cfs[ti].astype(np.float64))
        ft = Lf @ rng.standard_normal(k)
        rets[ti] = (bs[ti].astype(np.float64) @ ft + rng.standard_normal(n) * np.sqrt(ds[ti].astype(np.float64))).astype(np.float32)

    with tempfile.TemporaryDirectory() as td:
        ps = {}
        for key, arr in [("v", vhat), ("r1", r1d), ("bs", bs), ("cfs", cfs), ("ds", ds),
                         ("rets", rets), ("ws", ws), ("bv", bvec), ("wr", wref),
                         ("p", np.array([hl_beta], dtype=np.float32))]:
            ps[key] = os.path.join(td, f"{key}.f32")
            write_f32(ps[key], arr)
        par = Parser(run_cli(1, ps["v"], ps["r1"], ps["bs"], ps["cfs"], ps["ds"],
                             ps["rets"], ps["ws"], ps["bv"], ps["wr"], ps["p"], t, n, k))
        g_ql = par.read_f32()
        g_mse = par.read_f32()
        g_bias = par.read_f32()
        g_qd = par.read_qdist()
        g_mh = par.read_mahal()
        g_mvp = par.read_mvp()
        g_pv = par.read_voleval()
        g_to = par.read_turnover()
        g_be = par.read_betaerr()
        g_r2 = par.read_f32()

    # Reference scalar metrics
    vh64, r164 = vhat.astype(np.float64), r1d.astype(np.float64)
    ref_ql = float(np.mean(r164**2 / vh64 - np.log(r164**2 / vh64) - 1.0))
    ref_mse = float(np.mean((r164**2 - vh64)**2))
    ref_bias = float(np.sqrt(np.mean(r164**2 / vh64)))

    # OOS pairs: model at t paired with return at t+1 (t = 0 .. T-2)
    R64 = rets.astype(np.float64)
    W64 = ws.astype(np.float64)
    Bv64 = bvec.astype(np.float64)
    Wr64 = wref.astype(np.float64)
    Oms = [bs[ti].astype(np.float64) @ cfs[ti].astype(np.float64) @ bs[ti].astype(np.float64).T + np.diag(ds[ti].astype(np.float64)) for ti in range(t)]

    qd_pp, nu_pp, mvp_r, mvp_pv, pv_r, pv_v = [], [], [], [], [], []
    for ti in range(t - 1):
        Om = Oms[ti]
        rn = R64[ti + 1]
        _, logdet = np.linalg.slogdet(Om)
        quad = float(rn @ np.linalg.solve(Om, rn))
        qd_pp.append(logdet + quad + n * np.log(2.0 * np.pi))
        nu_pp.append(quad / n)
        z = np.linalg.solve(Om, Bv64)
        denom = float(Bv64 @ z)
        w_mvp = z / denom
        mvp_r.append(float(w_mvp @ rn))
        mvp_pv.append(1.0 / denom)
        wt = W64[ti]
        pv_r.append(float(wt @ rn))
        pv_v.append(float(wt @ Om @ wt))

    qd_pp, nu_pp = np.array(qd_pp), np.array(nu_pp)
    mvp_r, mvp_pv = np.array(mvp_r), np.array(mvp_pv)
    pv_r, pv_v = np.array(pv_r), np.array(pv_v)
    ref_malv = float(np.mean((nu_pp - np.mean(nu_pp))**2))
    ref_mvp_rv = float(np.mean(mvp_r**2))
    ref_mvp_ql = float(np.mean(mvp_r**2 / mvp_pv - np.log(mvp_r**2 / mvp_pv) - 1.0))
    ref_pv_ql = float(np.mean(pv_r**2 / pv_v - np.log(pv_r**2 / pv_v) - 1.0))
    ref_pv_bias = float(np.sqrt(np.mean(pv_r**2 / pv_v)))

    # FMP turnover
    fmps = []
    for ti in range(t):
        Bt = bs[ti].astype(np.float64)
        Dt = ds[ti].astype(np.float64)
        Gt = Bt.T @ (Bt / Dt[:, None])
        fmps.append((Bt / Dt[:, None]) @ np.linalg.inv(Gt))
    to_pp = np.array([float(np.linalg.norm(fmps[ti] - fmps[ti - 1], "fro")) for ti in range(1, t)])

    # Beta error (compare O(TN) against exact dense EWMA Omega_r!)
    lam_b = 2.0 ** (-1.0 / hl_beta)
    be_pp = []
    for ti in range(t):
        # Exact EWMA cov on R[0..ti]
        idxs = np.arange(ti, -1, -1, dtype=np.float64)
        aw = lam_b ** idxs
        aw = aw / np.sum(aw)
        Om_r = (R64[:ti + 1].T * aw) @ R64[:ti + 1]
        v_r = Om_r @ Wr64
        beta_r = v_r / max(float(Wr64 @ v_r), 1e-12)
        v_m = Oms[ti] @ Wr64
        beta_m = v_m / max(float(Wr64 @ v_m), 1e-12)
        be_pp.append(float(np.sum((beta_m - beta_r)**2)))
    be_pp = np.array(be_pp)

    # Cross-sectional R^2
    num_r2, den_r2 = 0.0, 0.0
    for ti in range(t):
        Bt = bs[ti].astype(np.float64)
        Dt = ds[ti].astype(np.float64)
        rt = R64[ti]
        fhat = np.linalg.solve(Bt.T @ (Bt / Dt[:, None]), Bt.T @ (rt / Dt))
        eps = rt - Bt @ fhat
        num_r2 += float(np.sum((eps**2) / Dt))
        den_r2 += float(np.sum((rt**2) / Dt))
    ref_r2 = 1.0 - num_r2 / den_r2

    errs = {
        "qlike": abs(g_ql - ref_ql) / max(abs(ref_ql), 1e-12),
        "vol_mse": abs(g_mse - ref_mse) / max(abs(ref_mse), 1e-12),
        "bias_stat": abs(g_bias - ref_bias) / ref_bias,
        "qdist_pp": rel_err(g_qd["per_period"], qd_pp),
        "qdist_mean": abs(g_qd["mean"] - np.mean(qd_pp)) / max(abs(np.mean(qd_pp)), 1e-12),
        "mahal_nu": rel_err(g_mh["nu"], nu_pp),
        "mahal_malv": abs(g_mh["malv"] - ref_malv) / max(ref_malv, 1e-12),
        "mvp_rets": rel_err(g_mvp["returns"], mvp_r),
        "mvp_pvars": rel_err(g_mvp["pred_vars"], mvp_pv),
        "mvp_rvar": abs(g_mvp["realized_var"] - ref_mvp_rv) / ref_mvp_rv,
        "mvp_qlike": abs(g_mvp["qlike"] - ref_mvp_ql) / max(abs(ref_mvp_ql), 1e-12),
        "pvol_qlike": abs(g_pv["qlike"] - ref_pv_ql) / max(abs(ref_pv_ql), 1e-12),
        "pvol_bias": abs(g_pv["bias_stat"] - ref_pv_bias) / ref_pv_bias,
        "fmp_to_pp": rel_err(g_to["per_period"], to_pp),
        "beta_err_pp": rel_err(g_be["per_period"], be_pp),
        "cs_r2": abs(g_r2 - ref_r2),
    }
    report("ch5_risk_evaluation", errs, tol=5e-4)


# ===================================================================== Chapter 6a
def test_ch6a():
    rng = np.random.default_rng(601)
    t, k, n = 80, 6, 18
    k1, k2, q = 3, 4, 4
    l_max, win, target_idx = 3, 15, 1
    hl_vol, hl_corr, hl_fast = 20.0, 40.0, 10.0
    rho, eig_fl, k_cai, thr_cl, d_max, rho_lk = 0.2, 1e-6, 2.0, 0.35, 3.0, 0.7

    # Generate autocorrelated factor returns so Newey-West / Cohen have nontrivial lag terms
    f_raw = rng.standard_normal((t, k)) * 0.012
    for ti in range(1, t):
        f_raw[ti] += 0.25 * f_raw[ti - 1]
    f = f_raw.astype(np.float32)

    # Generate residuals with two strongly correlated pairs (0,1) and (2,3) + one outlier spike for winsorize
    eps_raw = rng.standard_normal((t, n)) * 0.015
    eps_raw[:, 1] = 0.75 * eps_raw[:, 0] + 0.66 * eps_raw[:, 1]
    eps_raw[:, 3] = -0.70 * eps_raw[:, 2] + 0.71 * eps_raw[:, 3]
    eps_raw[40, 0] = 0.35
    eps_raw[55, 4] = -0.28
    eps = eps_raw.astype(np.float32)

    b = (rng.standard_normal((n, k)) * 0.6).astype(np.float32)
    d = np.exp(rng.uniform(-9.0, -7.0, size=n)).astype(np.float32)
    evw = rng.uniform(0.0, 1.0, size=(t, n)).astype(np.float32)

    # Indefinite symmetric matrix for psd_project
    q_ind, _ = np.linalg.qr(rng.standard_normal((k, k)))
    eigs_ind = np.array([-0.002, -0.0005, 0.0001, 0.001, 0.003, 0.008])
    indef = (q_ind @ np.diag(eigs_ind) @ q_ind.T).astype(np.float32)
    indef = 0.5 * (indef + indef.T)

    # Linking inputs
    loc0 = make_spd(rng, k1, 2e-4, 1e-3)
    loc1 = make_spd(rng, k2, 3e-4, 1.5e-3)
    joint = make_spd(rng, k1 + k2, 1e-4, 2e-3)

    # Currency rebasing inputs (C is N x Q one-hot currency membership, cov_c is Q x Q)
    cmat = np.zeros((n, q), dtype=np.float32)
    for i in range(n):
        cmat[i, i % q] = 1.0
    covc = make_spd(rng, q, 5e-5, 4e-4)

    params = np.array([hl_vol, hl_corr, hl_fast, rho, eig_fl, k_cai, thr_cl, d_max, rho_lk], dtype=np.float32)

    with tempfile.TemporaryDirectory() as td:
        ps = {}
        for key, arr in [("f", f), ("eps", eps), ("b", b), ("d", d), ("evw", evw),
                         ("ind", indef), ("l0", loc0), ("l1", loc1), ("j", joint),
                         ("cm", cmat), ("cc", covc), ("p", params)]:
            ps[key] = os.path.join(td, f"{key}.f32")
            write_f32(ps[key], arr)
        par = Parser(run_cli(2, ps["f"], ps["eps"], ps["b"], ps["d"], ps["evw"], ps["ind"],
                             ps["l0"], ps["l1"], ps["j"], ps["cm"], ps["cc"], ps["p"],
                             t, k, n, k1, k2, q, l_max, win, target_idx))
        g_ew = par.read_vec()
        g_sc_c = par.read_mat()
        g_sc_u = par.read_mat()
        g_ec_c = par.read_mat()
        g_ec_u = par.read_mat()
        g_sh_id = par.read_mat()
        g_deb = par.read_mat()
        g_stvu_ex = par.read_f32()
        g_stvu_lin = par.read_f32()
        g_stvu_cov = par.read_mat()
        g_lw_c = par.read_shrink()
        g_lw_u = par.read_shrink()
        g_psd = par.read_mat()
        g_dcc = par.read_mat()
        g_nw0 = par.read_mat()
        g_nw_e = par.read_mat()
        g_coh0 = par.read_mat()
        g_coh_e = par.read_mat()
        g_iv_e = par.read_vec()
        g_iv_sh = par.read_vec()
        g_iv_st = par.read_vec()
        g_cai = par.read_f32()
        g_pairs = par.read_pairs()
        g_win = par.read_mat()
        g_link = par.read_mat()
        g_reb = par.read_rebase()

    F = f.astype(np.float64)
    E = eps.astype(np.float64)
    B, D, EVW = b.astype(np.float64), d.astype(np.float64), evw.astype(np.float64)
    w_vol = ewma_w_ref(t, hl_vol)
    w_corr = ewma_w_ref(t, hl_corr)
    w_fast = ewma_w_ref(t, hl_fast)

    # Sample & EWMA cov (Bessel-corrected when centered)
    Fc = F - np.mean(F, axis=0, keepdims=True)
    ref_sc_c = (Fc.T @ Fc) / (t - 1)
    ref_sc_u = (F.T @ F) / t
    F_ewc = F - (w_vol @ F)[None, :]
    ref_ec_c = ((F_ewc.T * w_vol) @ F_ewc) / (1.0 - float(np.sum(w_vol**2)))
    ref_ec_u = (F.T * w_vol) @ F

    # Shrink to identity
    ref_sh_id = (1.0 - rho) * ref_sc_c + rho * (np.trace(ref_sc_c) / k) * np.eye(k)

    # Debias factor cov (Eq 6.5)
    G_db = B.T @ (B / D[:, None])
    raw_db = ref_sc_c - np.linalg.inv(G_db)
    ev_db, ec_db = np.linalg.eigh(0.5 * (raw_db + raw_db.T))
    ref_deb = ec_db @ np.diag(np.maximum(ev_db, eig_fl)) @ ec_db.T

    # STVU (exact Eq 6.8 with scipy.special.digamma & linear Eq 6.11)
    ev_s, ec_s = np.linalg.eigh(ref_sc_c)
    inv_sq = ec_s @ np.diag(1.0 / np.sqrt(ev_s)) @ ec_s.T
    U = F @ inv_sq
    u2 = np.maximum(np.sum(U**2, axis=1), 1e-12)
    kappa_ref = np.log(2.0) + digamma(0.5 * k)
    ref_stvu_ex = float(np.exp(np.sum(w_fast * (np.log(u2) - kappa_ref))))
    ref_stvu_lin = float(np.sum(w_fast * np.sqrt(u2 / k)) ** 2)

    # Ledoit-Wolf vs scikit-learn!
    lw_sk_c = LedoitWolf(assume_centered=False).fit(F)
    lw_sk_u = LedoitWolf(assume_centered=True).fit(F)

    # PSD project
    ev_i, ec_i = np.linalg.eigh(indef.astype(np.float64))
    ref_psd = ec_i @ np.diag(np.maximum(ev_i, eig_fl)) @ ec_i.T

    # DCC cov (causal EWMA vol standardization + slow EWMA correlation + fast final vol)
    lam_v = np.exp(-np.log(2.0) / hl_vol)
    v_cur = np.maximum(F[0]**2, 1e-12)
    Z = np.empty_like(F)
    for ti in range(t):
        v_cur = lam_v * v_cur + (1.0 - lam_v) * (F[ti]**2)
        Z[ti] = F[ti] / np.sqrt(np.maximum(v_cur, 1e-12))
    s_fast = np.sqrt(np.maximum(np.sum((F**2) * w_vol[:, None], axis=0), 1e-12))
    R_raw = (Z.T * w_corr) @ Z
    rd = np.sqrt(np.maximum(np.diag(R_raw), 1e-12))
    R_corr = R_raw / np.outer(rd, rd)
    ref_dcc = np.outer(s_fast, s_fast) * R_corr

    # Newey-West vs statsmodels cov_hac (using OLS with identity design on F) AND exact EWMA formula
    def hac_ref(X, w, lm, is_nw):
        C = (X.T * w) @ X
        for l in range(1, lm + 1):
            kw = (1.0 - l / (lm + 1.0)) if is_nw else 0.5
            wl = w[l:]
            Gl = (X[l:].T * wl) @ X[:-l]
            C = C + kw * (Gl + Gl.T)
        return C
    w_eq = np.full(t, 1.0 / t)
    ref_nw0 = hac_ref(F, w_eq, l_max, True)
    # Direct cross-check against statsmodels Bartlett kernel weights:
    wb = weights_bartlett(l_max)
    ref_nw_sm = (F.T @ F) / t
    for l in range(1, l_max + 1):
        Gl = (F[l:].T @ F[:-l]) / t
        ref_nw_sm = ref_nw_sm + wb[l] * (Gl + Gl.T)
    assert rel_err(ref_nw0, ref_nw_sm) < 1e-14

    ref_nw_e = hac_ref(F, w_vol, l_max, True)
    ref_coh0 = hac_ref(F, w_eq, l_max, False)
    ref_coh_e = hac_ref(F, w_vol, l_max, False)

    # Idio var EWMA, shrink, STVU
    ref_iv_e = np.sum((E**2) * w_vol[:, None], axis=0)
    ref_iv_sh = (1.0 - rho) * D + rho * np.mean(D)
    ratios = []
    for ti in range(t):
        num = np.sum(EVW[ti] * (E[ti]**2 / D))
        den = np.sum(EVW[ti])
        ratios.append(np.sqrt(num / den))
    mult_id = (np.sum(w_fast * np.array(ratios))) ** 2
    ref_iv_st = ((1.0 - EVW[-1]) + EVW[-1] * mult_id) * D

    # Cai threshold & corr clusters
    ref_cai = k_cai * np.sqrt(np.log(n) / t)
    Ec = E - np.mean(E, axis=0, keepdims=True)
    En = Ec / np.linalg.norm(Ec, axis=0, keepdims=True)
    Cmat_corr = En.T @ En
    ref_pairs = [(i, j, float(Cmat_corr[i, j])) for i in range(n) for j in range(i + 1, n) if abs(Cmat_corr[i, j]) > thr_cl]

    # Causal winsorize_log_mad
    ref_win = np.empty_like(E)
    hist = [[] for _ in range(n)]
    for ti in range(t):
        for j in range(n):
            r = E[ti, j]
            lr = np.log(max(1.0 + r, 1e-6))
            alr = abs(lr)
            med = float(np.median(hist[j])) if len(hist[j]) > 0 else 0.0
            lim = d_max * med
            if med > 1e-12 and alr > lim:
                ref_win[ti, j] = np.exp(np.clip(lr, -lim, lim)) - 1.0
            else:
                ref_win[ti, j] = r
            hist[j] = ([alr] + hist[j])[:win]

    # Linking (§6.6.1)
    L0, L1, J = loc0.astype(np.float64), loc1.astype(np.float64), joint.astype(np.float64)
    J00, J11, J01 = J[:k1, :k1], J[k1:, k1:], J[:k1, k1:]
    C0 = sla.fractional_matrix_power(J00, -0.5) @ sla.fractional_matrix_power(L0, 0.5)
    C1 = sla.fractional_matrix_power(J11, -0.5) @ sla.fractional_matrix_power(L1, 0.5)
    ref_link = np.zeros_like(J)
    ref_link[:k1, :k1] = L0
    ref_link[k1:, k1:] = L1
    off01 = rho_lk * (C0.T @ J01 @ C1)
    ref_link[:k1, k1:] = off01
    ref_link[k1:, :k1] = off01.T

    # Currency rebasing (§6.6.2)
    Cm, Cc = cmat.astype(np.float64), covc.astype(np.float64)
    A_reb = np.eye(q)
    A_reb[:, target_idx] -= 1.0
    ref_reb_cl = Cm @ A_reb
    ref_reb_cc = A_reb @ Cc @ A_reb.T

    errs = {
        "ewma_weights": rel_err(g_ew, w_vol),
        "sample_cov_c": rel_err(g_sc_c, ref_sc_c),
        "sample_cov_u": rel_err(g_sc_u, ref_sc_u),
        "ewma_cov_c": rel_err(g_ec_c, ref_ec_c),
        "ewma_cov_u": rel_err(g_ec_u, ref_ec_u),
        "shrink_to_id": rel_err(g_sh_id, ref_sh_id),
        "debias_cov": rel_err(g_deb, ref_deb),
        "stvu_exact": abs(g_stvu_ex - ref_stvu_ex) / ref_stvu_ex,
        "stvu_linear": abs(g_stvu_lin - ref_stvu_lin) / ref_stvu_lin,
        "stvu_adjust": rel_err(g_stvu_cov, ref_stvu_ex * ref_sc_c),
        "lw_c_cov": rel_err(g_lw_c["cov"], lw_sk_c.covariance_),
        "lw_c_shrink": abs(g_lw_c["shrinkage"] - lw_sk_c.shrinkage_),
        "lw_u_cov": rel_err(g_lw_u["cov"], lw_sk_u.covariance_),
        "lw_u_shrink": abs(g_lw_u["shrinkage"] - lw_sk_u.shrinkage_),
        "psd_project": rel_err(g_psd, ref_psd),
        "dcc_cov": rel_err(g_dcc, ref_dcc),
        "nw_eq_sm": rel_err(g_nw0, ref_nw_sm),
        "nw_ewma": rel_err(g_nw_e, ref_nw_e),
        "cohen_eq": rel_err(g_coh0, ref_coh0),
        "cohen_ewma": rel_err(g_coh_e, ref_coh_e),
        "idio_ewma": rel_err(g_iv_e, ref_iv_e),
        "idio_shrink": rel_err(g_iv_sh, ref_iv_sh),
        "idio_stvu": rel_err(g_iv_st, ref_iv_st),
        "cai_thresh": abs(g_cai - ref_cai) / ref_cai,
        "corr_pairs_cnt": abs(len(g_pairs) - len(ref_pairs)),
        "corr_pairs_val": max([abs(a[2] - b_[2]) for a, b_ in zip(g_pairs, ref_pairs)] + [0.0]) if len(g_pairs) == len(ref_pairs) else 1.0,
        "winsorize": rel_err(g_win, ref_win),
        "link_models_ir": rel_err(g_link, ref_link),
        "link_preserves_l0": rel_err(g_link[:k1, :k1], L0),
        "link_preserves_l1": rel_err(g_link[k1:, k1:], L1),
        "rebase_cl": rel_err(g_reb["c_loadings"], ref_reb_cl),
        "rebase_cc": rel_err(g_reb["cov_c"], ref_reb_cc),
        "rebase_zero_target": float(np.max(np.abs(g_reb["cov_c"][target_idx, :]))),
    }
    report("ch6a_covariance_and_utilities", errs, tol=5e-4)


# ===================================================================== Chapter 6b
def test_ch6b():
    rng = np.random.default_rng(602)
    n, k = 40, 5
    # Rank-deficient market + 5 sector dummies (k_rd = 6, constraint: cap-weighted sum of sector returns = 0)
    k_rd, p_cons = 6, 1
    t, win = 70, 50  # t >= 64 exercises pmap!
    delta, tol_rl = 0.25, 1e-4

    b = (rng.standard_normal((n, k)) * 0.6).astype(np.float32)
    r = (rng.standard_normal(n) * 0.02).astype(np.float32)
    w = np.exp(rng.uniform(-1.0, 1.0, size=n)).astype(np.float32)

    # Market + 5 mutually exclusive sectors -> exact collinearity!
    brd = np.zeros((n, k_rd), dtype=np.float32)
    brd[:, 0] = 1.0
    for i in range(n):
        brd[i, 1 + (i % 5)] = 1.0
    ccon = np.zeros((k_rd, p_cons), dtype=np.float32)
    ccon[1:, 0] = np.array([0.25, 0.20, 0.15, 0.22, 0.18], dtype=np.float32)
    dcon = np.array([0.0], dtype=np.float32)

    # Panel for estimate_factor_series, fit_fundamental_model, rolling_fundamental_models
    bs = np.empty((t, n, k), dtype=np.float32)
    rets = np.empty((t, n), dtype=np.float32)
    wmat = np.exp(rng.uniform(-0.8, 0.8, size=(t, n))).astype(np.float32)
    cf_true = make_spd(rng, k, 1e-4, 8e-4).astype(np.float64)
    Lf = np.linalg.cholesky(cf_true)
    d_true = np.exp(rng.uniform(-8.5, -6.5, size=n))
    for ti in range(t):
        bs[ti] = (b + rng.standard_normal((n, k)) * 0.05).astype(np.float32)
        ft = Lf @ rng.standard_normal(k)
        rets[ti] = (bs[ti].astype(np.float64) @ ft + rng.standard_normal(n) * np.sqrt(d_true)).astype(np.float32)

    with tempfile.TemporaryDirectory() as td:
        ps = {}
        for key, arr in [("b", b), ("r", r), ("w", w), ("brd", brd), ("cc", ccon), ("dc", dcon),
                         ("bs", bs), ("rets", rets), ("wm", wmat),
                         ("p", np.array([delta, tol_rl], dtype=np.float32))]:
            ps[key] = os.path.join(td, f"{key}.f32")
            write_f32(ps[key], arr)
        par = Parser(run_cli(3, ps["b"], ps["r"], ps["w"], ps["brd"], ps["cc"], ps["dc"],
                             ps["bs"], ps["rets"], ps["wm"], ps["p"], n, k, k_rd, p_cons, t, win))
        g_wls = par.read_csreg()
        g_con = par.read_csreg()
        g_rdg = par.read_csreg()
        g_rl = par.read_csreg()
        g_fser = par.read_fser()
        g_ffit = par.read_fundfit()
        g_roll = par.read_fms()

    B, R, W = b.astype(np.float64), r.astype(np.float64), w.astype(np.float64)
    Brd, Cc, Dc = brd.astype(np.float64), ccon.astype(np.float64), dcon.astype(np.float64)

    # WLS
    G_w = B.T @ (B * W[:, None])
    ref_wls_f = np.linalg.solve(G_w, B.T @ (W * R))
    ref_wls_res = R - B @ ref_wls_f
    ref_wls_ec = np.linalg.inv(G_w)

    # Constrained WLS (KKT system)
    G_rd = Brd.T @ (Brd * W[:, None])
    KKT = np.block([[G_rd, Cc], [Cc.T, np.zeros((p_cons, p_cons))]])
    rhs = np.concatenate([Brd.T @ (W * R), Dc])
    sol_kkt = np.linalg.solve(KKT, rhs)
    ref_con_f = sol_kkt[:k_rd]
    ref_con_res = R - Brd @ ref_con_f

    # Ridge
    G_rg = G_w + delta * np.eye(k)
    ref_rdg_f = np.linalg.solve(G_rg, B.T @ (W * R))
    ref_rdg_res = R - B @ ref_rdg_f

    # Ridgeless (minimum-norm pseudoinverse of sqrt(W) B)
    sw = np.sqrt(W)
    ref_rl_f = np.linalg.pinv(Brd * sw[:, None], rcond=tol_rl) @ (sw * R)

    # Factor series
    ref_fser = np.empty((t, k))
    ref_rser = np.empty((t, n))
    for ti in range(t):
        Bt = bs[ti].astype(np.float64)
        Wt = wmat[ti].astype(np.float64)
        Rt = rets[ti].astype(np.float64)
        ft = np.linalg.solve(Bt.T @ (Bt * Wt[:, None]), Bt.T @ (Wt * Rt))
        ref_fser[ti] = ft
        ref_rser[ti] = Rt - Bt @ ft

    # Verify rolling count = t - win + 1 and last model matches single fit
    errs = {
        "wls_f": rel_err(g_wls["f_ret"], ref_wls_f),
        "wls_res": rel_err(g_wls["resid"], ref_wls_res),
        "wls_ec": rel_err(g_wls["est_cov"], ref_wls_ec),
        "con_f": rel_err(g_con["f_ret"], ref_con_f),
        "con_res": rel_err(g_con["resid"], ref_con_res),
        "con_satisfies": float(np.linalg.norm(Cc.T @ g_con["f_ret"] - Dc)),
        "ridge_f": rel_err(g_rdg["f_ret"], ref_rdg_f),
        "ridge_res": rel_err(g_rdg["resid"], ref_rdg_res),
        "ridgeless_f": rel_err(g_rl["f_ret"], ref_rl_f),
        "fser_f": rel_err(g_fser["f_rets"], ref_fser),
        "fser_res": rel_err(g_fser["resid"], ref_rser),
        "fundfit_sym": float(np.max(np.abs(g_ffit["model"]["cov_f"] - g_ffit["model"]["cov_f"].T))),
        "fundfit_psd": float(max(0.0, -np.min(np.linalg.eigvalsh(g_ffit["model"]["cov_f"])))),
        "fundfit_idio_pos": float(max(0.0, -np.min(g_ffit["model"]["idio_var"]))),
        "rolling_len": abs(len(g_roll) - (t - win + 1)),
    }
    report("ch6b_cross_sectional_and_fundamental", errs, tol=5e-4)


# ===================================================================== Chapter 7
def test_ch7():
    rng = np.random.default_rng(701)
    t, n, k = 90, 24, 4
    # Spiked panel (true K = 4 strong factors) for Bai-Ng, gap, threshold, PCA, PPCA, stat model
    B_true = rng.standard_normal((n, k)) * 0.6
    F_true = rng.standard_normal((t, k)) * np.array([0.045, 0.030, 0.022, 0.016])
    E_true = rng.standard_normal((t, n)) * 0.008
    rets = (F_true @ B_true.T + E_true).astype(np.float32)

    # Larger spiked panel (120 x 100, kb = 6) so subspace_svd actually runs subspace iteration (min(120,100)=100 > max(6+8, 40)=40)
    tb, nb, kb = 120, 100, 6
    Bb = rng.standard_normal((nb, kb)) * 0.5
    Fb = rng.standard_normal((tb, kb)) * np.geomspace(0.05, 0.015, kb)
    rets_big = (Fb @ Bb.T + rng.standard_normal((tb, nb)) * 0.005).astype(np.float32)

    # Alignment test inputs: B_curr = B_prev @ Q_true + small noise
    bp = (rng.standard_normal((n, k)) * 0.7).astype(np.float32)
    q_rand, _ = np.linalg.qr(rng.standard_normal((k, k)))
    bc = (bp.astype(np.float64) @ q_rand + rng.standard_normal((n, k)) * 0.02).astype(np.float32)
    cfp = make_spd(rng, k)
    cfc = make_spd(rng, k)
    dp = np.exp(rng.uniform(-7.0, -5.0, size=n)).astype(np.float32)
    dc = np.exp(rng.uniform(-7.0, -5.0, size=n)).astype(np.float32)

    # Imputation & interpretation inputs
    m_new, p_ch, win = 8, 5, 60
    a_new = (F_true @ (rng.standard_normal((k, m_new)) * 0.5) + rng.standard_normal((t, m_new)) * 0.008).astype(np.float32)
    g_known = rng.standard_normal((n, p_ch)).astype(np.float32)
    g_new = rng.standard_normal((m_new, p_ch)).astype(np.float32)

    with tempfile.TemporaryDirectory() as td:
        ps = {}
        for key, arr in [("r", rets), ("rb", rets_big), ("bp", bp), ("bc", bc),
                         ("cfp", cfp), ("cfc", cfc), ("dp", dp), ("dc", dc),
                         ("an", a_new), ("gk", g_known), ("gn", g_new)]:
            ps[key] = os.path.join(td, f"{key}.f32")
            write_f32(ps[key], arr)
        par = Parser(run_cli(4, ps["r"], ps["rb"], ps["bp"], ps["bc"], ps["cfp"], ps["cfc"],
                             ps["dp"], ps["dc"], ps["an"], ps["gk"], ps["gn"],
                             t, n, k, tb, nb, kb, m_new, p_ch, win))
        g_pca_eq = par.read_pca()
        g_pca_ew = par.read_pca()
        g_big_ex = par.read_pca()
        g_big_sub = par.read_pca()
        g_ppca = par.read_fm()
        g_sh0 = par.read_vec()
        g_sh1 = par.read_vec()
        g_sh2 = par.read_vec()
        g_sh3 = par.read_vec()
        g_k_thr = par.read_u32()
        g_k_glin = par.read_u32()
        g_k_glog = par.read_u32()
        g_baing = par.read_baing()
        g_eto = par.read_eigto()
        g_asign = par.read_mat()
        g_aproc = par.read_fm()
        g_sdist = par.read_f32()
        g_stat0 = par.read_statfit()
        g_stat1 = par.read_statfit()
        g_imp_ts = par.read_mat()
        g_interp = par.read_mat()
        g_imp_ch = par.read_mat()
        g_roll_s = par.read_fms()
        g_roll_p = par.read_fms()

    R64 = rets.astype(np.float64)
    Rb64 = rets_big.astype(np.float64)

    # PCA equal-weighted & EWMA references
    _, s_eq, vt_eq = np.linalg.svd(R64 / np.sqrt(t), full_matrices=False)
    w_ew = ewma_w_ref(t, 25.0)
    _, s_ew, vt_ew = np.linalg.svd(R64 * np.sqrt(w_ew)[:, None], full_matrices=False)
    _, s_big, vt_big = np.linalg.svd(Rb64 / np.sqrt(tb), full_matrices=False)

    # PPCA reference
    lams_all = s_eq**2
    lam_bar = (np.sum(lams_all) - np.sum(lams_all[:k])) / (n - k)
    V_k = vt_eq[:k].T
    ref_ppca_cov = V_k @ np.diag(np.maximum(lams_all[:k] - lam_bar, 1e-8)) @ V_k.T + lam_bar * np.eye(n)

    # Spiked shrinkage modes 0..3
    gamma = n / t
    ref_sh0 = np.maximum(lams_all, 1e-8)
    ref_sh1 = np.maximum(lams_all - gamma, 1e-8)
    ref_sh2 = np.maximum(lams_all - 0.0, 1e-8)
    ref_sh3 = np.maximum(0.9 * lams_all - 1e-5, 1e-8)

    # Bai-Ng reference (on singular values of R / sqrt(t) passed from pca_svd(rets, n, 0.0))
    # Note: Bai-Ng is invariant to uniform scaling of s_j for IC_p1 and PC_p1!
    s2 = s_eq**2
    pen = ((n + t) / (n * t)) * np.log((n * t) / (n + t))
    kmax = 8
    vks = [max(np.sum(s2[j:]) / (n * t), 1e-20) for j in range(kmax + 1)]
    ref_ics = np.array([np.log(vks[j]) + j * pen for j in range(kmax + 1)])
    ref_pcs = np.array([vks[j] + j * vks[kmax] * pen for j in range(kmax + 1)])

    # Eigenfactor turnover, sign alignment, Procrustes, subspace distance
    Bp, Bc = bp.astype(np.float64), bc.astype(np.float64)
    Cfc, Dc = cfc.astype(np.float64), dc.astype(np.float64)
    cos_cols = [min(1.0, abs(np.dot(Bp[:, j], Bc[:, j])) / (np.linalg.norm(Bp[:, j]) * np.linalg.norm(Bc[:, j]))) for j in range(k)]
    ref_eto = np.array([2.0 * (1.0 - c) for c in cos_cols])

    ref_asign = Bc.copy()
    for j in range(k):
        if np.dot(Bp[:, j], Bc[:, j]) < 0:
            ref_asign[:, j] *= -1.0

    X_proc, _ = sla.orthogonal_procrustes(Bc, Bp)
    ref_proc_b = Bc @ X_proc
    ref_proc_cf = X_proc.T @ Cfc @ X_proc
    Om_curr = Bc @ Cfc @ Bc.T + np.diag(Dc)

    Q1, _ = np.linalg.qr(Bp, mode="reduced")
    Q2, _ = np.linalg.qr(Bc, mode="reduced")
    ref_sdist = float(np.sqrt(max(0.0, 1.0 - np.linalg.norm(Q1.T @ Q2, "fro")**2 / k)))

    # Imputation & interpretation references against g_stat0
    B_st = g_stat0["model"]["b"]
    F_st = g_stat0["f_rets"]
    ref_imp_ts = np.linalg.lstsq(F_st, a_new.astype(np.float64), rcond=None)[0].T
    ref_interp = np.linalg.lstsq(g_known.astype(np.float64), B_st, rcond=None)[0]
    ref_imp_ch = 0.95 * (g_new.astype(np.float64) @ ref_interp)

    # Subspace distance between exact SVD and subspace-iteration SVD on big panel
    Q_ex, _ = np.linalg.qr(g_big_ex["loadings"], mode="reduced")
    Q_sub, _ = np.linalg.qr(g_big_sub["loadings"], mode="reduced")
    sub_vs_ex_dist = float(np.sqrt(max(0.0, 1.0 - np.linalg.norm(Q_ex.T @ Q_sub, "fro")**2 / kb)))

    # Verify rolling alignment: consecutive Procrustes-aligned models have small ||B_{t-1} - B_t||
    roll_sym = max(float(np.max(np.abs(m["cov_f"] - m["cov_f"].T))) for m in g_roll_p)

    # Also verify select_k_threshold, select_k_gap against exact formulas
    ref_k_thr = int(np.sum(lams_all >= 1.0 * (1.0 + np.sqrt(n / t))**2))
    ref_k_glin = int(np.argmax(lams_all[:8] - lams_all[1:9]) + 1)
    ref_k_glog = int(np.argmax(np.log(np.maximum(lams_all[:8], 1e-20)) - np.log(np.maximum(lams_all[1:9], 1e-20))) + 1)

    errs = {
        "pca_eq_sv": rel_err(g_pca_eq["singular_values"], s_eq[:k]),
        "pca_eq_ev": rel_err(g_pca_eq["eigenvalues"], s_eq[:k]**2),
        "pca_eq_subspace": float(np.sqrt(max(0.0, 1.0 - np.linalg.norm(g_pca_eq["loadings"].T @ vt_eq[:k].T, "fro")**2 / k))),
        "pca_ew_sv": rel_err(g_pca_ew["singular_values"], s_ew[:k]),
        "subspace_svd_sv": rel_err(g_big_sub["singular_values"], s_big[:kb]),
        "subspace_svd_vs_exact_sv": rel_err(g_big_sub["singular_values"], g_big_ex["singular_values"]),
        "subspace_svd_dist": sub_vs_ex_dist,
        "ppca_cov": rel_err(fm_cov(g_ppca), ref_ppca_cov),
        "shrink_m0": rel_err(g_sh0, ref_sh0),
        "shrink_m1": rel_err(g_sh1, ref_sh1),
        "shrink_m2": rel_err(g_sh2, ref_sh2),
        "shrink_m3": rel_err(g_sh3, ref_sh3),
        "select_k_thr": abs(g_k_thr - ref_k_thr),
        "select_k_glin": abs(g_k_glin - ref_k_glin),
        "select_k_glog": abs(g_k_glog - ref_k_glog),
        "baing_ic_vec": rel_err(g_baing["ic"], ref_ics),
        "baing_pc_vec": rel_err(g_baing["pc"], ref_pcs),
        "baing_recovers_k": abs(g_baing["k_ic"] - k),
        "baing_pc_recovers_k": abs(g_baing["k_pc"] - k),
        "eigto_vec": rel_err(g_eto["per_factor"], ref_eto),
        "align_sign": rel_err(g_asign, ref_asign),
        "align_proc_b": rel_err(g_aproc["b"], ref_proc_b),
        "align_proc_cf": rel_err(g_aproc["cov_f"], ref_proc_cf),
        "align_proc_cov_invar": rel_err(fm_cov(g_aproc), Om_curr),
        "subspace_dist": abs(g_sdist - ref_sdist),
        "stat0_sym": float(np.max(np.abs(g_stat0["model"]["cov_f"] - g_stat0["model"]["cov_f"].T))),
        "stat1_sym": float(np.max(np.abs(g_stat1["model"]["cov_f"] - g_stat1["model"]["cov_f"].T))),
        "stat0_idio_pos": float(max(0.0, -np.min(g_stat0["model"]["idio_var"]))),
        "stat1_idio_pos": float(max(0.0, -np.min(g_stat1["model"]["idio_var"]))),
        "impute_ts": rel_err(g_imp_ts, ref_imp_ts),
        "interpret": rel_err(g_interp, ref_interp),
        "impute_char": rel_err(g_imp_ch, ref_imp_ch),
        "rolling_sign_len": abs(len(g_roll_s) - (t - win + 1)),
        "rolling_proc_len": abs(len(g_roll_p) - (t - win + 1)),
        "rolling_proc_sym": roll_sym,
    }
    print(f"       select_k: threshold={g_k_thr}, gap_lin={g_k_glin}, gap_log={g_k_glog}, bai_ng_ic={g_baing['k_ic']}, bai_ng_pc={g_baing['k_pc']} (true K={k})")
    report("ch7_statistical_pca_rmt_alignment", errs, tol=5e-4)


# ===================================================================== Edge cases
def test_edge():
    lines = [l for l in run_cli(5) if l.strip()]
    assert len(lines) == 10 and all(l == "NONE" for l in lines), f"Expected 10 NONEs, got {lines}"
    print("[PASS] edge_cases_and_mismatch_guards: 10/10 returned NONE")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-build", action="store_true")
    args = ap.parse_args()
    if not args.no_build:
        build()
    test_ch4()
    test_ch5()
    test_ch6a()
    test_ch6b()
    test_ch7()
    test_edge()
    print("\nALL CHECKS PASSED")


if __name__ == "__main__":
    main()
