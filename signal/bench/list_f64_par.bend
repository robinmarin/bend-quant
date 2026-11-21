import Base
import bend-kit-f64@0.1.3.0/f64.bend as F

# Rank-IC benchmark, bend-kit soft-float F64. Usage: out/list_f64_par T N (2^6 tasks over dates)
# Panel: T dates x N names, x ~ U(-.5,.5), y = 0.1 x + U(-.5,.5), from a U32 LCG.
# Per date: Spearman(x, y) by two sorts (no unsort; ordinal ranks, ties ignored).
# Then mean IC, sd, t over the T dates.

type Px is Data:
  Px{a: F.F64, b: F.F64}

def half() -> F.F64:
  F.F64.div(F.F64.one(), F.F64.from_u32(2))

def tenth() -> F.F64:
  F.F64.div(F.F64.one(), F.F64.from_u32(10))

def lcg(+s: U32) -> U32:
  ((s * 1664525) + 1013904223 : U32)

def unif(+s: U32) -> F.F64:
  (F.F64.from_u32((s >> 8n : U32)) / F.F64.from_u32(16777216) : F.F64)

def gen_xs(n: Nat, +s: U32, acc: List<&2, Px>) -> List<&2, Px>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +s1 = lcg(s)
      +s2 = lcg(s1)
      +x = (unif(s1) - half() : F.F64)
      +e = (unif(s2) - half() : F.F64)
      gen_xs(p, s2, Px{x, ((tenth() * x) + e : F.F64)} <> acc)

def gen_panel(t: Nat, +n: Nat, +s: U32, acc: List<&2, List<&2, Px>>) -> List<&2, List<&2, Px>>:
  match t:
    case 0n:
      acc
    case 1n+p:
      +s2 = lcg(((s * 2654435761) + 7 : U32))
      gen_panel(p, n, s2, gen_xs(n, s2, Nil{}) <> acc)

def le_a(p: Px, q: Px) -> Bool:
  Px{pa, _} = p
  Px{qa, _} = q
  (pa <= qa : F.F64)

# (a, b) sorted by a -> (b, position)
def enum(xs: List<&2, Px>, +i: F.F64, acc: List<&2, Px>) -> List<&2, Px>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      Px{_, b} = h
      enum(t, (i + F.F64.one() : F.F64), Px{b, i} <> acc)

def sums(xs: List<&2, Px>, +sa: F.F64, +sb: F.F64, +n: F.F64) -> Px & F.F64:
  match xs:
    case Nil{}:
      (Px{sa, sb}, n)
    case Con{h, t}:
      Px{+a, +b} = h
      sums(t, (sa + a : F.F64), (sb + b : F.F64), (n + F.F64.one() : F.F64))

def cent(xs: List<&2, Px>, +ma: F.F64, +mb: F.F64, +saa: F.F64, +sbb: F.F64, +sab: F.F64) -> F.F64:
  match xs:
    case Nil{}:
      (sab / F.F64.sqrt((saa * sbb : F.F64)) : F.F64)
    case Con{h, t}:
      Px{+a, +b} = h
      +da = (a - ma : F.F64)
      +db = (b - mb : F.F64)
      cent(t, ma, mb, (saa + (da * da) : F.F64), (sbb + (db * db) : F.F64), (sab + (da * db) : F.F64))

# two-pass Pearson over pairs
def pearson.k(r: Px & F.F64, +xs: List<&2, Px>) -> F.F64:
  (m, n) = r
  Px{sa, sb} = m
  +nn = n
  cent(xs, (sa / nn : F.F64), (sb / nn : F.F64), F.F64.zero(), F.F64.zero(), F.F64.zero())

def pearson(+xs: List<&2, Px>) -> F.F64:
  pearson.k(sums(xs, F.F64.zero(), F.F64.zero(), F.F64.zero()), xs)

def rank_ic(xs: List<&2, Px>) -> F.F64:
  r1 = enum(List.sort(~Px, ~le_a, xs), F.F64.zero(), Nil{})
  r2 = enum(List.sort(~Px, ~le_a, r1), F.F64.zero(), Nil{})
  pearson(r2)

def ics(panel: List<&2, List<&2, Px>>, acc: List<&2, F.F64>) -> List<&2, F.F64>:
  match panel:
    case Nil{}:
      acc
    case Con{h, t}:
      ics(t, rank_ic(h) <> acc)

def half_nat(n: Nat) -> Nat:
  U32.to_nat((U32.from_nat(n) >> 1n : U32))

# fork-join over dates: 2^depth balanced tasks
def ics_par(+depth: Nat, +panel: List<&2, List<&2, Px>>) -> List<&2, F.F64>:
  match depth:
    case 0n:
      ics(panel, Nil{})
    case 1n+d:
      +k = half_nat(List.length(&2, List<&2, Px>, panel))
      a b = ics_par(d, List.take(&2, List<&2, Px>, panel, k)) ics_par(d, List.drop(&2, List<&2, Px>, panel, k))
      List.append(&2, F.F64, a, b)

def sum1(xs: List<&2, F.F64>, +s: F.F64, +n: F.F64) -> F.F64 & F.F64:
  match xs:
    case Nil{}:
      (s, n)
    case Con{h, t}:
      sum1(t, (s + h : F.F64), (n + F.F64.one() : F.F64))

def ss1(xs: List<&2, F.F64>, +m: F.F64, +s: F.F64) -> F.F64:
  match xs:
    case Nil{}:
      s
    case Con{h, t}:
      +d = (h - m : F.F64)
      ss1(t, m, (s + (d * d) : F.F64))

# mean IC, sd, t
def summary.k(r: F.F64 & F.F64, +xs: List<&2, F.F64>) -> String:
  (s, n) = r
  +nn = n
  +m = (s / nn : F.F64)
  +sd = F.F64.sqrt((ss1(xs, m, F.F64.zero()) / (nn - F.F64.one()) : F.F64))
  "ic=" ++ F.F64.show(m) ++ " sd=" ++ F.F64.show(sd) ++ " t=" ++ F.F64.show(((m / sd) * F.F64.sqrt(nn) : F.F64))

def summary(+xs: List<&2, F.F64>) -> String:
  summary.k(sum1(xs, F.F64.zero(), F.F64.zero()), xs)

def fst(r: Px & F.F64) -> F.F64:
  (m, _) = r
  Px{a, _} = m
  a

def chk(+panel: List<&2, List<&2, Px>>, +s: F.F64) -> F.F64:
  match panel:
    case Nil{}:
      s
    case Con{h, t}:
      chk(t, (s + fst(sums(h, F.F64.zero(), F.F64.zero(), F.F64.zero())) : F.F64))

def num(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{n}:
      n
    case None{}:
      0

def tn(s: String) -> Nat:
  U32.to_nat(num(U32.read(s)))

def run(+t: Nat, +n: Nat) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    +panel : List<&2, List<&2, Px>> = gen_panel(t, n, 12345, Nil{})
    IO.print("gen chk=" ++ F.F64.show(chk(panel, F.F64.zero())))
    +t1 : Nat <- IO.now()
    +ic : List<&2, F.F64> = ics_par(6n, panel)
    IO.print(summary(ic))
    t2 : Nat <- IO.now()
    IO.print("gen_ms=" ++ Nat.show(Nat.sub(t1, t0)) ++ " ic_ms=" ++ Nat.show(Nat.sub(t2, t1)))

def go(args: List<String>) -> IO(Unit):
  match args:
    case _ <> ts <> ns <> _:
      run(tn(ts), tn(ns))
    case _:
      IO.print("usage: T N")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
