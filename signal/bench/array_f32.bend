import Base

# Rank IC on flat Array<F32>, in-place heapsort. Usage: out/array_f32 T N [D]
# One array per date, 2048 slots, interleaved: slot 2k = key, 2k+1 = payload (N <= 1024).
# Same panel and same algorithm as list_f32.bend (two sorts, no unsort, two-pass Pearson).
# D: fork-join over dates, 2^(D+1) tasks.

type S is Type:
  S{a: Array<F32>, i: U32, n: U32, done: Bool}

def lcg(+s: U32) -> U32:
  ((s * 1664525) + 1013904223 : U32)

def unif(+s: U32) -> F32:
  (U32.to_f32((s >> 8n : U32)) / 16777216.0 : F32)

def ninf() -> F32:
  (0.0 - 1000000000.0 : F32)

def sel_f(b: Bool, x: F32, y: F32) -> F32:
  match b:
    case True{}:
      x
    case False{}:
      y

def sel_u(b: Bool, x: U32, y: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      y

# ---- slot swap: a[x] <-> a[y]
def sw2(p: Array<F32> & F32, x: U32) -> Array<F32>:
  (a, vy) = p
  Array.set(F32, a, x, vy)

def sw1(p: Array<F32> & F32, +x: U32, y: U32) -> Array<F32>:
  (a, vx) = p
  sw2(Array.swap(F32, a, y, vx), x)

def sw(a: Array<F32>, +x: U32, y: U32) -> Array<F32>:
  sw1(Array.get(F32, a, x), x, y)

# swap pairs i and m (key and payload)
def swp(a: Array<F32>, +i: U32, +m: U32) -> Array<F32>:
  sw(sw(a, (2 * i : U32), (2 * m : U32)), ((2 * i) + 1 : U32), ((2 * m) + 1 : U32))

# ---- one sift-down step at node i of a max-heap of size n
def st4(a: Array<F32>, +i: U32, +n: U32, +m: U32) -> S:
  S{swp(a, i, m), m, n, U32.is_eq(m, i)}

def st3(p: Array<F32> & F32, +ki: F32, +kl: F32, +i: U32, +n: U32, +l: U32, +r: U32) -> S:
  (a, kr0) = p
  +kr = sel_f(U32.is_lt(r, n), kr0, ninf())
  +gl = (kl > ki : F32)
  +m1 = sel_u(gl, l, i)
  +k1 = sel_f(gl, kl, ki)
  st4(a, i, n, sel_u((kr > k1 : F32), r, m1))

def st2(p: Array<F32> & F32, +ki: F32, +i: U32, +n: U32, +l: U32, +r: U32) -> S:
  (a, kl0) = p
  st3(Array.get(F32, a, (2 * r : U32)), ki, sel_f(U32.is_lt(l, n), kl0, ninf()), i, n, l, r)

def st1(p: Array<F32> & F32, +i: U32, +n: U32) -> S:
  (a, ki) = p
  +l = ((2 * i) + 1 : U32)
  st2(Array.get(F32, a, (2 * l : U32)), ki, i, n, l, (l + 1 : U32))

def step(a: Array<F32>, +i: U32, +n: U32) -> S:
  st1(Array.get(F32, a, (2 * i : U32)), i, n)

def sift(fuel: Nat, s: S) -> Array<F32>:
  match fuel:
    case 0n:
      S{a, _, _, _} = s
      a
    case 1n+p:
      match s:
        case S{a, i, n, done}:
          match done:
            case True{}:
              a
            case False{}:
              sift(p, step(a, i, n))

def sift0(a: Array<F32>, +i: U32, +n: U32) -> Array<F32>:
  sift(11n, S{a, i, n, False{}})

# heapify: i = start, start-1, .., 0
def build(fuel: Nat, a: Array<F32>, +i: U32, +n: U32) -> Array<F32>:
  match fuel:
    case 0n:
      a
    case 1n+p:
      build(p, sift0(a, i, n), (i - 1 : U32), n)

# sortdown: end = n-1 .. 1
def down(fuel: Nat, a: Array<F32>, +e: U32) -> Array<F32>:
  match fuel:
    case 0n:
      a
    case 1n+p:
      down(p, sift0(swp(a, 0, e), 0, e), (e - 1 : U32))

# ascending heapsort of n pairs by key
def hsort(a: Array<F32>, +n: U32) -> Array<F32>:
  +h = (n >> 1n : U32)
  down(U32.to_nat((n - 1 : U32)), build(U32.to_nat(h), a, (h - 1 : U32), n), (n - 1 : U32))

# pair k: (key, payload) -> (payload, k)
def en1(p: Array<F32> & F32, +k: U32) -> Array<F32>:
  (a, v) = p
  Array.set(F32, Array.set(F32, a, (2 * k : U32), v), ((2 * k) + 1 : U32), U32.to_f32(k))

def enum(fuel: Nat, a: Array<F32>, +k: U32) -> Array<F32>:
  match fuel:
    case 0n:
      a
    case 1n+p:
      enum(p, en1(Array.get(F32, a, ((2 * k) + 1 : U32)), k), (k + 1 : U32))

# ---- two-pass Pearson over pairs
type Acc is Type:
  Acc{a: Array<F32>, x: F32, y: F32, z: F32}

def ps2(p: Array<F32> & F32, +va: F32, +ma: F32, +mb: F32, +saa: F32, +sbb: F32, +sab: F32) -> Acc:
  (a, vb) = p
  +da = (va - ma : F32)
  +db = (vb - mb : F32)
  Acc{a, (saa + (da * da) : F32), (sbb + (db * db) : F32), (sab + (da * db) : F32)}

def ps1(p: Array<F32> & F32, +k: U32, +ma: F32, +mb: F32, +saa: F32, +sbb: F32, +sab: F32) -> Acc:
  (a, va) = p
  ps2(Array.get(F32, a, ((2 * k) + 1 : U32)), va, ma, mb, saa, sbb, sab)

def cent(fuel: Nat, s: Acc, +k: U32, +ma: F32, +mb: F32) -> F32:
  match fuel:
    case 0n:
      Acc{_, saa, sbb, sab} = s
      (sab / F32.sqrt((saa * sbb : F32)) : F32)
    case 1n+p:
      Acc{a, saa, sbb, sab} = s
      cent(p, ps1(Array.get(F32, a, (2 * k : U32)), k, ma, mb, saa, sbb, sab), (k + 1 : U32), ma, mb)

def sm2(p: Array<F32> & F32, +va: F32, +sa: F32, +sb: F32) -> Acc:
  (a, vb) = p
  Acc{a, (sa + va : F32), (sb + vb : F32), 0.0}

def sm1(p: Array<F32> & F32, +k: U32, +sa: F32, +sb: F32) -> Acc:
  (a, va) = p
  sm2(Array.get(F32, a, ((2 * k) + 1 : U32)), va, sa, sb)

def sums(fuel: Nat, s: Acc, +k: U32) -> Acc:
  match fuel:
    case 0n:
      s
    case 1n+p:
      Acc{a, sa, sb, _} = s
      sums(p, sm1(Array.get(F32, a, (2 * k : U32)), k, sa, sb), (k + 1 : U32))

def pearson.k(s: Acc, +n: U32) -> F32:
  Acc{a, sa, sb, _} = s
  +nf = U32.to_f32(n)
  cent(U32.to_nat(n), Acc{a, 0.0, 0.0, 0.0}, 0, (sa / nf : F32), (sb / nf : F32))

def pearson(a: Array<F32>, +n: U32) -> F32:
  pearson.k(sums(U32.to_nat(n), Acc{a, 0.0, 0.0, 0.0}, 0), n)

def rank_ic(a: Array<F32>, +n: U32) -> F32:
  +nn = U32.to_nat(n)
  r1 = enum(nn, hsort(a, n), 0)
  r2 = enum(nn, hsort(r1, n), 0)
  pearson(r2, n)

# ---- panel
def gen_xs(fuel: Nat, a: Array<F32>, +k: U32, +s: U32) -> Array<F32>:
  match fuel:
    case 0n:
      a
    case 1n+p:
      +s1 = lcg(s)
      +s2 = lcg(s1)
      +x = (unif(s1) - 0.5 : F32)
      +e = (unif(s2) - 0.5 : F32)
      gen_xs(p, Array.set(F32, Array.set(F32, a, (2 * k : U32), x), ((2 * k) + 1 : U32), ((0.1 * x) + e : F32)), (k + 1 : U32), s2)

def gen_panel(t: Nat, +n: U32, +s: U32, acc: List<Array<F32>>) -> List<Array<F32>>:
  match t:
    case 0n:
      acc
    case 1n+p:
      +s2 = lcg(((s * 2654435761) + 7 : U32))
      gen_panel(p, n, s2, gen_xs(U32.to_nat(n), [0.0 : F32*2048n], 0, s2) <> acc)

def ics(panel: List<Array<F32>>, +n: U32, acc: List<&2, F32>) -> List<&2, F32>:
  match panel:
    case Nil{}:
      acc
    case Con{h, t}:
      ics(t, n, rank_ic(h, n) <> acc)

type Two is Type:
  Two{l: List<Array<F32>>, r: List<Array<F32>>}

def split(k: Nat, xs: List<Array<F32>>, acc: List<Array<F32>>) -> Two:
  match k:
    case 0n:
      Two{acc, xs}
    case 1n+p:
      match xs:
        case Nil{}:
          Two{acc, Nil{}}
        case Con{h, t}:
          split(p, t, h <> acc)

# fork-join over dates: two holds the halves (h and r dates); 2^(depth+1) leaves
def ics_par(+depth: Nat, two: Two, +h: U32, +r: U32, +n: U32) -> List<&2, F32>:
  match depth:
    case 0n:
      Two{xl, xr} = two
      a b = ics(xl, n, Nil{}) ics(xr, n, Nil{})
      List.append(&2, F32, a, b)
    case 1n+d:
      Two{xl, xr} = two
      +hl = (h >> 1n : U32)
      +hr = (r >> 1n : U32)
      a b = ics_par(d, split(U32.to_nat(hl), xl, Nil{}), hl, (h - hl : U32), n) ics_par(d, split(U32.to_nat(hr), xr, Nil{}), hr, (r - hr : U32), n)
      List.append(&2, F32, a, b)

def ics_top(+d: U32, panel: List<Array<F32>>, +t: U32, +n: U32) -> List<&2, F32>:
  +h = (t >> 1n : U32)
  ics_par(U32.to_nat(d), split(U32.to_nat(h), panel, Nil{}), h, (t - h : U32), n)

def sum1(xs: List<&2, F32>, +s: F32, +n: F32) -> F32 & F32:
  match xs:
    case Nil{}:
      (s, n)
    case Con{h, t}:
      sum1(t, (s + h : F32), (n + 1.0 : F32))

def ss1(xs: List<&2, F32>, +m: F32, +s: F32) -> F32:
  match xs:
    case Nil{}:
      s
    case Con{h, t}:
      +d = (h - m : F32)
      ss1(t, m, (s + (d * d) : F32))

def summary.k(r: F32 & F32, +xs: List<&2, F32>) -> String:
  (s, n) = r
  +nn = n
  +m = (s / nn : F32)
  +sd = F32.sqrt((ss1(xs, m, 0.0) / (nn - 1.0) : F32))
  "ic=" ++ F32.show(m) ++ " sd=" ++ F32.show(sd) ++ " t=" ++ F32.show(((m / sd) * F32.sqrt(nn) : F32))

def summary(+xs: List<&2, F32>) -> String:
  summary.k(sum1(xs, 0.0, 0.0), xs)

def num(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{n}:
      n
    case None{}:
      0

def tu(s: String) -> U32:
  num(U32.read(s))

def run(+t: U32, +n: U32, +d: U32) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    +ic : List<&2, F32> = ics_top(d, gen_panel(U32.to_nat(t), n, 12345, Nil{}), t, n)
    IO.print(summary(ic))
    t1 : Nat <- IO.now()
    IO.print("gen+ic_ms=" ++ Nat.show(Nat.sub(t1, t0)))

def go(args: List<String>) -> IO(Unit):
  match args:
    case _ <> ts <> ns <> ds <> _:
      run(tu(ts), tu(ns), tu(ds))
    case _ <> ts <> ns <> _:
      run(tu(ts), tu(ns), 0)
    case _:
      IO.print("usage: T N [D]")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
