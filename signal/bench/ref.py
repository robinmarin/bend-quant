"""Same panel as list_f32.bend (same LCG), rank IC in numpy. Usage: ref.py T N [64]"""
import sys, time
import numpy as np

T, N = int(sys.argv[1]), int(sys.argv[2])
F = np.float64 if sys.argv[3:] == ["64"] else np.float32
M = np.uint32
with np.errstate(over="ignore"):
    def lcg(s): return (s * M(1664525) + M(1013904223)).astype(M)
    def unif(s): return ((s >> M(8)).astype(F) / F(16777216.0))

    seeds = np.empty(T, M); s = M(12345)
    for t in range(T):
        s = lcg(M(s * M(2654435761) + M(7))); seeds[t] = s
    x = np.empty((T, N), F); y = np.empty((T, N), F)
    s = seeds.copy()
    for i in range(N):
        s1 = lcg(s); s2 = lcg(s1)
        xi = unif(s1) - F(0.5); e = unif(s2) - F(0.5)
        x[:, i] = xi; y[:, i] = F(0.1) * xi + e
        s = s2

t0 = time.perf_counter()
rx = x.argsort(1).argsort(1).astype(np.float64)  # ordinal ranks, like the Bend version
ry = y.argsort(1).argsort(1).astype(np.float64)
rx -= rx.mean(1, keepdims=True); ry -= ry.mean(1, keepdims=True)
ic = (rx * ry).sum(1) / np.sqrt((rx**2).sum(1) * (ry**2).sum(1))
m, sd = ic.mean(), ic.std(ddof=1)
ms = (time.perf_counter() - t0) * 1e3
print(f"gen chk={x.sum(1, dtype=np.float64).sum():.6f}")
print(f"ic={m:.8f} sd={sd:.8f} t={m / sd * np.sqrt(T):.6f}")
print(f"ic_ms={ms:.1f}")
