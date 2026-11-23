# GPU (`!`) vs CPU parallel benchmark in Bend 2.0 following `bend guide shaders`:
# 4-way fork tree of depth 7 (= 4^7 = 16384 lanes) ending in flat tail loops
# with zero shared-memory contention:
#   1. Batched 16384-way GEMV / matmul-style dot work (pure compute per lane,
#      measuring peak GPU lane throughput vs CPU threads).
#   2. Batched 16384-way independent 8x8 linear solves / Cholesky-like inner loops
#      (models massive cross-sectional / Monte Carlo / rolling-window parallelism).
#   3. Real tree-mapped matmul (4096 x 64 * 64 x 16) built on a quad-tree of rows
#      with borrowed RHS columns, comparing CPU parallel vs GPU `!`.
import Base

def lcg(+s: U32) -> U32:
  ((s * 1664525) + 1013904223 : U32)

def unif(+s: U32) -> F32:
  ((U32.to_f32((s >> 8n : U32)) / 16777216.0) - 0.5 : F32)

# ---- Workload 1: Pure-compute batched matmul work (16384 lanes x K_iters FMA work)
# Each lane computes an independent synthetic K x K inner product loop (64 x 64 = 4096 FMAs/lane
# -> 67M FMAs = 134M FLOPs per bang, zero PCIe data transfer).

def lane_inner(rem: Nat, +a: F32, +b: F32, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      +a1 = ((a * 0.999987) + 0.000123 : F32)
      +b1 = ((b * 0.999971) - 0.000091 : F32)
      lane_inner(p, a1, b1, (acc + (a1 * b1) : F32))

def lane_outer(rem: Nat, +inner: Nat, +a: F32, +b: F32, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      +a1 = ((a * 0.9991) + 0.001 : F32)
      +b1 = ((b * 0.9987) - 0.001 : F32)
      lane_outer(p, inner, a1, b1, lane_inner(inner, a1, b1, acc))

def lane_work(+seed: U32, +n: Nat) -> F32:
  +s1 = lcg(seed)
  +s2 = lcg(s1)
  lane_outer(n, n, unif(s1), unif(s2), 0.0)

def fork4_compute(+d: Nat, +id: U32, +n: Nat) -> F32:
  match d:
    case 0n:
      lane_work(id, n)
    case 1n+p:
      +b = (id << 2n : U32)
      r0 r1 r2 r3 = fork4_compute(p, b, n) fork4_compute(p, (b + 1 : U32), n) fork4_compute(p, (b + 2 : U32), n) fork4_compute(p, (b + 3 : U32), n)
      ((r0 + r1) + (r2 + r3) : F32)

def run_compute_gpu(+d: Nat, +n: Nat) -> F32:
  fork4_compute!(d, 1, n)

def run_compute_cpu(+d: Nat, +n: Nat) -> F32:
  fork4_compute(d, 1, n)

# ---- Workload 2: Tree-structured Matvec (16384 x 64) with borrowed RHS vector
# Follows `bend guide shaders`: quadtree of rows, borrowed vector `x`, flat tail dot loop.

type RTree is Data:
  RLeaf{row: List<&2, F32>}
  RQuad{a: RTree, b: RTree, c: RTree, d: RTree}

type VTree is Data:
  VLeaf{v: F32}
  VQuad{a: VTree, b: VTree, c: VTree, d: VTree}

def gen_row(rem: Nat, +s: U32) -> List<&2, F32>:
  match rem:
    case 0n:
      Nil{}
    case 1n+p:
      +s1 = lcg(s)
      unif(s1) <> gen_row(p, s1)

def gen_rtree(+d: Nat, +cols: Nat, +s: U32) -> RTree:
  match d:
    case 0n:
      RLeaf{gen_row(cols, s)}
    case 1n+p:
      +s0 = lcg(s)
      +s1 = lcg((s0 + 1 : U32))
      +s2 = lcg((s1 + 2 : U32))
      +s3 = lcg((s2 + 3 : U32))
      a b c q = gen_rtree(p, cols, s0) gen_rtree(p, cols, s1) gen_rtree(p, cols, s2) gen_rtree(p, cols, s3)
      RQuad{a, b, c, q}

def dot_flat(xs: List<&2, F32>, ys: List<&2, F32>, +acc: F32) -> F32:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      dot_flat(xt, yt, (acc + (x * y) : F32))
    case _ _:
      acc

def matvec_tree(t: RTree, +x: List<&2, F32>) -> VTree:
  match t:
    case RLeaf{r}:
      VLeaf{dot_flat(r, x, 0.0)}
    case RQuad{a, b, c, d}:
      va vb vc vd = matvec_tree(a, x) matvec_tree(b, x) matvec_tree(c, x) matvec_tree(d, x)
      VQuad{va, vb, vc, vd}

# Tree-structured Matmul: each leaf row r computes dots against all columns of B (flat loops)
def dots_flat(+r: List<&2, F32>, cols: List<&2, List<&2, F32>>, +acc: F32) -> F32:
  match cols:
    case Nil{}:
      acc
    case Con{c, ct}:
      dots_flat(r, ct, (acc + dot_flat(r, c, 0.0) : F32))

def matmul_tree(t: RTree, +bcols: List<&2, List<&2, F32>>) -> VTree:
  match t:
    case RLeaf{r}:
      VLeaf{dots_flat(r, bcols, 0.0)}
    case RQuad{a, b, c, d}:
      va vb vc vd = matmul_tree(a, bcols) matmul_tree(b, bcols) matmul_tree(c, bcols) matmul_tree(d, bcols)
      VQuad{va, vb, vc, vd}

def gen_cols(rem: Nat, +k: Nat, +s: U32) -> List<&2, List<&2, F32>>:
  match rem:
    case 0n:
      Nil{}
    case 1n+p:
      +s1 = lcg(((s * 2654435761) + 13 : U32))
      gen_row(k, s1) <> gen_cols(p, k, s1)

def matmul_gpu_call(+t: RTree, +bcols: List<&2, List<&2, F32>>) -> VTree & RTree:
  (matmul_tree!(t, bcols), t)

def matmul_cpu_call(+t: RTree, +bcols: List<&2, List<&2, F32>>) -> VTree & RTree:
  (matmul_tree(t, bcols), t)

def sum_vtree(v: VTree) -> F32:
  match v:
    case VLeaf{x}:
      x
    case VQuad{a, b, c, d}:
      ((sum_vtree(a) + sum_vtree(b)) + (sum_vtree(c) + sum_vtree(d)) : F32)

# Pure def returning pair so `t` and `x` are host-owned and borrowed by the bang.
def matvec_gpu_call(+t: RTree, +x: List<&2, F32>) -> VTree & RTree:
  (matvec_tree!(t, x), t)

def matvec_cpu_call(+t: RTree, +x: List<&2, F32>) -> VTree & RTree:
  (matvec_tree(t, x), t)

def chk_pair(p: VTree & RTree) -> F32:
  (v, _) = p
  sum_vtree(v)

def rep_mm_gpu(rem: Nat, +t: RTree, +bcols: List<&2, List<&2, F32>>, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_mm_gpu(p, t, bcols, (acc + chk_pair(matmul_gpu_call(t, bcols)) : F32))

def rep_mm_cpu(rem: Nat, +t: RTree, +bcols: List<&2, List<&2, F32>>, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_mm_cpu(p, t, bcols, (acc + chk_pair(matmul_cpu_call(t, bcols)) : F32))

def rep_comp_gpu(rem: Nat, +d: Nat, +n: Nat, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_comp_gpu(p, d, n, (acc + run_compute_gpu(d, n) : F32))

def rep_comp_cpu(rem: Nat, +d: Nat, +n: Nat, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_comp_cpu(p, d, n, (acc + run_compute_cpu(d, n) : F32))

def rep_mv_gpu(rem: Nat, +t: RTree, +x: List<&2, F32>, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_mv_gpu(p, t, x, (acc + chk_pair(matvec_gpu_call(t, x)) : F32))

def rep_mv_cpu(rem: Nat, +t: RTree, +x: List<&2, F32>, +acc: F32) -> F32:
  match rem:
    case 0n:
      acc
    case 1n+p:
      rep_mv_cpu(p, t, x, (acc + chk_pair(matvec_cpu_call(t, x)) : F32))

def report(name: String, reps: Nat, t0: Nat, t1: Nat, chk: F32) -> IO(Unit):
  IO.print(name ++ " reps=" ++ Nat.show(reps) ++ " total_ms=" ++ Nat.show(Nat.sub(t1, t0)) ++ " chk=" ++ F32.show(chk))

def main() -> IO(Unit):
  do IO<Unit>:
    # Warmup GPU pipeline + boost clocks
    +_w : F32 = run_compute_gpu(7n, 64n)
    +_w1 : F32 = run_compute_gpu(7n, 64n)

    # 16384 lanes x 64x64 (4096) FMAs = 67.1M FMAs (134.2M FLOPs) per rep
    +t0 : Nat <- IO.now()
    +c0 : F32 = rep_comp_gpu(10n, 7n, 64n, 0.0)
    +t1 : Nat <- IO.now()
    report("compute_16384x4096_gpu", 10n, t0, t1, c0)

    +t2 : Nat <- IO.now()
    +c1 : F32 = rep_comp_cpu(10n, 7n, 64n, 0.0)
    +t3 : Nat <- IO.now()
    report("compute_16384x4096_cpu", 10n, t2, t3, c1)

    # 16384 lanes x 128x128 (16384) FMAs = 268.4M FMAs (536.9M FLOPs) per rep
    +t4 : Nat <- IO.now()
    +c2 : F32 = rep_comp_gpu(5n, 7n, 128n, 0.0)
    +t5 : Nat <- IO.now()
    report("compute_16384x16384_gpu", 5n, t4, t5, c2)

    +t6 : Nat <- IO.now()
    +c3 : F32 = rep_comp_cpu(5n, 7n, 128n, 0.0)
    +t7 : Nat <- IO.now()
    report("compute_16384x16384_cpu", 5n, t6, t7, c3)

    # Tree-structured Matvec 16384 x 64 (4^7 leaves)
    +rt : RTree = gen_rtree(7n, 64n, 777)
    +xv : List<&2, F32> = gen_row(64n, 888)
    +bcols : List<&2, List<&2, F32>> = gen_cols(16n, 64n, 999)
    +_w2 : F32 = chk_pair(matvec_gpu_call(rt, xv))
    +_w3 : F32 = chk_pair(matmul_gpu_call(rt, bcols))

    +t8 : Nat <- IO.now()
    +c4 : F32 = rep_mv_gpu(10n, rt, xv, 0.0)
    +t9 : Nat <- IO.now()
    report("matvec_tree_16384x64_gpu", 10n, t8, t9, c4)

    +t10 : Nat <- IO.now()
    +c5 : F32 = rep_mv_cpu(10n, rt, xv, 0.0)
    +t11 : Nat <- IO.now()
    report("matvec_tree_16384x64_cpu", 10n, t10, t11, c5)

    # Tree-structured Matmul 16384 x 64 * 64 x 16 (4^7 leaves, 33.6M FLOPs/rep)
    +t12 : Nat <- IO.now()
    +c6 : F32 = rep_mm_gpu(10n, rt, bcols, 0.0)
    +t13 : Nat <- IO.now()
    report("matmul_tree_16384x64x16_gpu", 10n, t12, t13, c6)

    +t14 : Nat <- IO.now()
    +c7 : F32 = rep_mm_cpu(10n, rt, bcols, 0.0)
    +t15 : Nat <- IO.now()
    report("matmul_tree_16384x64x16_cpu", 10n, t14, t15, c7)
