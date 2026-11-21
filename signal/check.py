"""Check signal against scipy. Run from anywhere: python3 signal/check.py

Builds check.bend into out/, writes test panels with ties and NaNs, and compares
every per-date IC and the rank IC summary. Exits non-zero on any mismatch.
"""
import os, subprocess, sys, tempfile
import numpy as np
from scipy import stats

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


def run(x, y, ty=None):
    t, n = x.shape
    with tempfile.TemporaryDirectory() as d:
        xp, yp = os.path.join(d, "x.f32"), os.path.join(d, "y.f32")
        x.astype("<f4").tofile(xp)
        y.astype("<f4").tofile(yp)
        out = subprocess.run([BIN, xp, yp, xp, yp, str(t), str(n), str(ty or t)],
                             capture_output=True, text=True, check=True).stdout
    got = {"rank": [], "ic": [], "sum": None, "none": []}
    for line in filter(None, map(str.strip, out.splitlines())):
        tag, *vals = line.split()
        if vals == ["none"]:
            got["none"].append(tag)
        elif tag == "sum":
            got["sum"] = [float(v) for v in vals]
        else:
            got[tag].append(float(vals[0]))
    return got


def close(a, b, tol=TOL):
    a, b = np.asarray(a, float), np.asarray(b, float)
    return a.shape == b.shape and np.allclose(a, b, atol=tol, rtol=0, equal_nan=True)


def case(name, x, y):
    x, y = x.astype(np.float32), y.astype(np.float32)
    got = run(x, y)
    wr, wi = want(x, y, True), want(x, y, False)
    ok = close(got["rank"], wr) and close(got["ic"], wi)
    ws, gs = summary(wr), got["sum"]
    ok = ok and (ws is None) == (gs is None)
    if ws is not None and gs is not None:
        # relative on mean, sd and the ratios; exact on hit rate and count
        ok = ok and np.allclose(gs[:4], ws[:4], rtol=1e-4, atol=TOL) and close(gs[4:], ws[4:], 1e-6)
    err = max(np.nanmax(np.abs(np.array(got["rank"]) - wr), initial=0),
              np.nanmax(np.abs(np.array(got["ic"]) - wi), initial=0))
    print(f"{'ok  ' if ok else 'FAIL'} {name:<28} t={x.shape[0]:<4} n={x.shape[1]:<4} max|err|={err:.1e}")
    if not ok:
        print("  rank got ", np.round(got["rank"][:8], 6), "\n  rank want", np.round(wr[:8], 6))
        print("  ic   got ", np.round(got["ic"][:8], 6), "\n  ic   want", np.round(wi[:8], 6))
        print("  sum  got ", gs, "\n  sum  want", ws)
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

    got = run(x.astype(np.float32), y.astype(np.float32), ty=39)
    ok = got["none"] == ["rank", "ic"]
    print(f"{'ok  ' if ok else 'FAIL'} shape mismatch -> none")
    res.append(ok)

    print("all ok" if all(res) else "FAILURES")
    sys.exit(0 if all(res) else 1)


if __name__ == "__main__":
    main()
