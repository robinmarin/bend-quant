"""Check signal against scipy. Run from anywhere: python3 signal/check.py

Builds check.bend into out/, writes test panels with ties and NaNs, and compares
every per-date IC and the rank IC summary. Exits non-zero on any mismatch.
"""
import os, subprocess, sys, tempfile
import numpy as np
from scipy import stats
import pandas as pd
from statsmodels.regression.linear_model import OLS

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, "out", "check")
TOL = 2e-5  # F32 rounding on ICs in [-1, 1]


def build():
    os.makedirs(os.path.dirname(BIN), exist_ok=True)
    r = subprocess.run(["bend", "check.bend", "-o", BIN], cwd=HERE, capture_output=True, text=True)
    if not os.path.exists(BIN):
        sys.exit(r.stdout + r.stderr)


def want(x, y, rank):
    out = []
    for a, b in zip(x, y):
        ok = ~(np.isnan(a) | np.isnan(b))
        a, b = a[ok].astype(np.float64), b[ok].astype(np.float64)
        if len(a) < 3 or np.ptp(a) == 0 or np.ptp(b) == 0:
            out.append(np.nan)
        else:
            f = stats.spearmanr if rank else stats.pearsonr
            out.append(f(a, b)[0])
    return np.array(out)


def summary(ics):
    v = ics[~np.isnan(ics)]
    if len(v) < 2:
        return None
    m, sd = v.mean(), v.std(ddof=1)
    return [m, sd, m / sd, m / sd * np.sqrt(len(v)), (v > 0).mean(), len(v)]


def run(x, y, ty=None, h=0):
    t, n = x.shape
    with tempfile.TemporaryDirectory() as d:
        xp, yp = os.path.join(d, "x.f32"), os.path.join(d, "y.f32")
        x.astype("<f4").tofile(xp)
        y.astype("<f4").tofile(yp)
        out = subprocess.run([BIN, xp, yp, str(t), str(n), str(ty or t), str(h)],
                             capture_output=True, text=True, check=True).stdout
    got = {"rank": [], "ic": [], "sum": None, "none": [], "nw": {}}
    for line in filter(None, map(str.strip, out.splitlines())):
        tag, *vals = line.split()
        if vals == ["none"]:
            got["none"].append(tag)
        elif tag == "nw":
            got["nw"][int(vals[0])] = None if vals[1] == "none" else float(vals[1])
        elif tag == "sum":
            got["sum"] = [float(v) for v in vals]
        else:
            got[tag].append(float(vals[0]))
    return got


def nw(ics, lags):
    """statsmodels HAC t of the mean, Bartlett weights, no small-sample correction."""
    v = ics[~np.isnan(ics)]
    if len(v) < 2:
        return None
    fit = OLS(v, np.ones(len(v))).fit(cov_type="HAC", cov_kwds={"maxlags": lags, "use_correction": False})
    return float(fit.tvalues[0])


def close(a, b, tol=TOL):
    a, b = np.asarray(a, float), np.asarray(b, float)
    return a.shape == b.shape and np.allclose(a, b, atol=tol, rtol=0, equal_nan=True)


def lead(y, h):
    """Row i becomes row i + h; the last min(h, t) rows are NaN."""
    k = min(h, len(y))
    return np.vstack([y[k:], np.full((k, y.shape[1]), np.nan, y.dtype)])


def case(name, x, y, h=0):
    x, y = x.astype(np.float32), y.astype(np.float32)
    got = run(x, y, h=h)
    wr, wi = want(x, lead(y, h), True), want(x, lead(y, h), False)
    ok = close(got["rank"], wr) and close(got["ic"], wi)
    ws, gs = summary(wr), got["sum"]
    ok = ok and (ws is None) == (gs is None)
    if ws is not None and gs is not None:
        # relative on mean, sd and the ratios; exact on hit rate and count
        ok = ok and np.allclose(gs[:4], ws[:4], rtol=1e-4, atol=TOL) and close(gs[4:], ws[4:], 1e-6)
    for lags in (0, 1, 5):
        w, g = nw(wr, lags), got["nw"].get(lags)
        ok = ok and (w is None) == (g is None) and (w is None or abs(g - w) <= 1e-4 * max(1, abs(w)))
    err = max(np.nanmax(np.abs(np.array(got["rank"]) - wr), initial=0),
              np.nanmax(np.abs(np.array(got["ic"]) - wi), initial=0))
    print(f"{'ok  ' if ok else 'FAIL'} {name:<28} t={x.shape[0]:<4} n={x.shape[1]:<4} max|err|={err:.1e}")
    if not ok:
        print("  rank got ", np.round(got["rank"][:8], 6), "\n  rank want", np.round(wr[:8], 6))
        print("  ic   got ", np.round(got["ic"][:8], 6), "\n  ic   want", np.round(wi[:8], 6))
        print("  sum  got ", gs, "\n  sum  want", ws)
        print("  nw   got ", got["nw"], "\n  nw   want", {l: nw(wr, l) for l in (0, 1, 5)})
    return ok


def transforms(name, x):
    """Every transform of x against pandas, row-wise on dates and time-series per name."""
    x = x.astype(np.float32)
    t, n = x.shape
    with tempfile.TemporaryDirectory() as d:
        xp = os.path.join(d, "x.f32")
        x.astype("<f4").tofile(xp)
        out = subprocess.run([BIN, xp, str(t), str(n)], capture_output=True, text=True, check=True).stdout
    got = {}
    for line in filter(None, map(str.strip, out.splitlines())):
        tag, *vals = line.split()
        got.setdefault(tag, []).append([float(v) for v in vals])
    df = pd.DataFrame(x.astype(np.float64))
    rows = df.T  # columns are dates, for row-wise ops
    want = {
        "zscore": ((rows - rows.mean()) / rows.std(ddof=1)).T,
        "demean": (rows - rows.mean()).T,
        "rank": rows.rank(pct=True).T,
        "winsorize": rows.clip(rows.quantile(0.1), rows.quantile(0.9), axis=1).T,
        "ewma": df.ewm(alpha=0.3, adjust=False, ignore_na=True).mean(),
        "rolling": df.rolling(3, min_periods=1).mean(),
    }
    ok = True
    for tag, w in want.items():
        g = np.array(got.get(tag, []))
        good = g.shape == w.shape and np.allclose(g, w.to_numpy(), atol=1e-5, rtol=1e-5, equal_nan=True)
        err = np.nanmax(np.abs(g - w.to_numpy())) if g.shape == w.shape else float("inf")
        print(f"{'ok  ' if good else 'FAIL'} {name + ' ' + tag:<28} t={t:<4} n={n:<4} max|err|={err:.1e}")
        ok = ok and good
    return ok


def main():
    build()
    rng = np.random.default_rng(7)
    res = []

    x = rng.standard_normal((40, 57)); y = 0.1 * x + rng.standard_normal((40, 57))
    res.append(case("continuous", x, y))

    xt, yt = np.round(x, 0), np.round(y * 2, 0)  # few distinct values: heavy ties
    res.append(case("heavy ties", xt, yt))

    xn, yn = x.copy(), y.copy()
    xn[rng.random(x.shape) < 0.15] = np.nan; yn[rng.random(y.shape) < 0.15] = np.nan
    res.append(case("15% NaN each side", xn, yn))

    e = rng.standard_normal((6, 9)); f = rng.standard_normal((6, 9))
    e[0] = np.nan                 # all missing
    e[1, 2:] = np.nan             # 2 complete pairs
    e[2, 3:] = np.nan             # exactly 3
    e[3] = 1.0                    # constant row: IC undefined
    f[4] = np.nan                 # y all missing
    res.append(case("edge dates", e, f))

    one = rng.standard_normal((1, 30))
    res.append(case("single date (no summary)", one, one * 2))

    big_x = rng.standard_normal((300, 400)); big_y = 0.05 * big_x + rng.standard_normal((300, 400))
    big_x[rng.random(big_x.shape) < 0.05] = np.nan
    res.append(case("parallel path, t >= 64", np.round(big_x, 2), big_y))

    res.append(case("lead 1", x, y, h=1))
    res.append(case("lead 5, ties and NaN", xn, np.round(yn, 0), h=5))
    res.append(case("lead past the end", x, y, h=50))

    xs = x.copy(); xs[rng.random(x.shape) < 0.2] = np.nan
    xs[:, 3] = np.nan; xs[5] = np.nan; xs[7, :55] = np.nan   # a dead name, a dead date, a 2-name date
    res.append(transforms("tf", np.round(xs, 1)))

    got = run(x.astype(np.float32), y.astype(np.float32), ty=39)
    ok = got["none"] == ["rank", "ic"]
    print(f"{'ok  ' if ok else 'FAIL'} shape mismatch -> none")
    res.append(ok)

    print("all ok" if all(res) else "FAILURES")
    sys.exit(0 if all(res) else 1)


if __name__ == "__main__":
    main()
