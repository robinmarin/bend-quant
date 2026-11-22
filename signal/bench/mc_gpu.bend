import Base

# Compute-dense Monte Carlo European Call (GBM Euler-Maruyama, 252 daily steps)
# Zero heap allocation in the hot loop — uniform numeric GPU workload.
# Usage: out/mc_gpu PATHS STEPS DEPTH [+RTS --gpu off -RTS]

type MC is Data:
  MC{s: F32, s2: F32, n: U32}

type PathSt is Data:
  PathSt{spot: F32, s: U32}

type LeafSt is Data:
  LeafSt{s: U32, acc: F32, acc2: F32, n: U32}

def lcg(+s: U32) -> U32:
  ((s * 1664525) + 1013904223 : U32)

def unif(+s: U32) -> F32:
  (U32.to_f32((s >> 8n : U32)) / 16777216.0 : F32)

# Irwin-Hall approximation to N(0,1): sum of 12 U(0,1) - 6
def randn_loop(k: Nat, +s: U32, +acc: F32) -> PathSt:
  match k:
    case 0n:
      PathSt{(acc - 6.0 : F32), s}
    case 1n+p:
      +s1 = lcg(s)
      randn_loop(p, s1, (acc + unif(s1) : F32))

def apply_z(+spot: F32, r: PathSt) -> PathSt:
  PathSt{z, s2} = r
  +mult = ((1.0001984 + (0.012598816 * z)) : F32)
  PathSt{(spot * mult : F32), s2}

def one_step(st: PathSt) -> PathSt:
  PathSt{spot, s} = st
  apply_z(spot, randn_loop(12n, s, 0.0))

def sim_steps(steps: Nat, st: PathSt) -> PathSt:
  match steps:
    case 0n:
      st
    case 1n+p:
      sim_steps(p, one_step(st))

def sel_f(b: Bool, x: F32, y: F32) -> F32:
  match b:
    case True{}:
      x
    case False{}:
      y

def max0(+x: F32) -> F32:
  sel_f((x > 0.0 : F32), x, 0.0)

def acc_path(r: PathSt, +acc: F32, +acc2: F32, +n: U32) -> LeafSt:
  PathSt{spot, s2} = r
  +payoff = max0((spot - 100.0 : F32))
  LeafSt{s2, (acc + payoff : F32), (acc2 + (payoff * payoff) : F32), (n + 1 : U32)}

def one_path(+steps: Nat, st: LeafSt) -> LeafSt:
  LeafSt{s, acc, acc2, n} = st
  acc_path(sim_steps(steps, PathSt{100.0, s}), acc, acc2, n)

def leaf_fin(st: LeafSt) -> MC:
  LeafSt{_, acc, acc2, n} = st
  MC{acc, acc2, n}

def leaf_paths(cnt: Nat, +steps: Nat, st: LeafSt) -> MC:
  match cnt:
    case 0n:
      leaf_fin(st)
    case 1n+p:
      leaf_paths(p, steps, one_path(steps, st))

def add_mc(a: MC, b: MC) -> MC:
  MC{sa, s2a, na} = a
  MC{sb, s2b, nb} = b
  MC{(sa + sb : F32), (s2a + s2b : F32), (na + nb : U32)}

def par_mc(+d: Nat, +idx: U32, +cnt: U32, +steps: Nat) -> MC:
  match d:
    case 0n:
      +seed = lcg(((idx * 2654435761) + 12345 : U32))
      leaf_paths(U32.to_nat(cnt), steps, LeafSt{seed, 0.0, 0.0, 0})
    case 1n+e:
      +h = (cnt >> 1n : U32)
      a b = par_mc(e, idx, h, steps) par_mc(e, (idx + h : U32), (cnt - h : U32), steps)
      add_mc(a, b)

def run_mc(+d: Nat, +paths: U32, +steps: Nat) -> MC:
  par_mc!(d, 0, paths, steps)

def show_mc(m: MC) -> String:
  MC{+s, +s2, +n} = m
  +nf = U32.to_f32(n)
  +price = ((0.9512294 * (s / nf)) : F32)
  "price=" ++ F32.show(price) ++ " paths=" ++ U32.show(n)

def num(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{n}:
      n
    case None{}:
      0

def tu(s: String) -> U32:
  num(U32.read(s))

def run(+paths: U32, +steps: U32, +d: U32) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    res : MC = run_mc(U32.to_nat(d), paths, U32.to_nat(steps))
    IO.print(show_mc(res))
    t1 : Nat <- IO.now()
    IO.print("mc_ms=" ++ Nat.show(Nat.sub(t1, t0)))

def go(args: List<String>) -> IO(Unit):
  match args:
    case _ <> ps <> ss <> ds <> _:
      run(tu(ps), tu(ss), tu(ds))
    case _:
      IO.print("usage: PATHS STEPS DEPTH")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
