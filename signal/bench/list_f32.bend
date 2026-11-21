import Base

# Rank-IC benchmark, native F32. Usage: out/list_f32 T N
# Panel: T dates x N names, x ~ U(-.5,.5), y = 0.1 x + U(-.5,.5), from a U32 LCG.
# Per date: Spearman(x, y) by two sorts (no unsort; ordinal ranks, ties ignored).
# Then mean IC, sd, t over the T dates.

type Px is Data:
  Px{a: F32, b: F32}

def lcg(+s: U32) -> U32:
  ((s * 1664525) + 1013904223 : U32)

def unif(+s: U32) -> F32:
  (U32.to_f32((s >> 8n : U32)) / 16777216.0 : F32)

def gen_xs(n: Nat, +s: U32, acc: List<&2, Px>) -> List<&2, Px>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +s1 = lcg(s)
      +s2 = lcg(s1)
      +x = (unif(s1) - 0.5 : F32)
      +e = (unif(s2) - 0.5 : F32)
      gen_xs(p, s2, Px{x, ((0.1 * x) + e : F32)} <> acc)

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
  (pa <= qa : F32)

# (a, b) sorted by a -> (b, position)
def enum(xs: List<&2, Px>, +i: F32, acc: List<&2, Px>) -> List<&2, Px>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      Px{_, b} = h
      enum(t, (i + 1.0 : F32), Px{b, i} <> acc)

def sums(xs: List<&2, Px>, +sa: F32, +sb: F32, +n: F32) -> Px & F32:
  match xs:
    case Nil{}:
      (Px{sa, sb}, n)
    case Con{h, t}:
      Px{+a, +b} = h
      sums(t, (sa + a : F32), (sb + b : F32), (n + 1.0 : F32))

def cent(xs: List<&2, Px>, +ma: F32, +mb: F32, +saa: F32, +sbb: F32, +sab: F32) -> F32:
  match xs:
    case Nil{}:
      (sab / F32.sqrt((saa * sbb : F32)) : F32)
    case Con{h, t}:
      Px{+a, +b} = h
      +da = (a - ma : F32)
      +db = (b - mb : F32)
      cent(t, ma, mb, (saa + (da * da) : F32), (sbb + (db * db) : F32), (sab + (da * db) : F32))

# two-pass Pearson over pairs
def pearson.k(r: Px & F32, +xs: List<&2, Px>) -> F32:
  (m, n) = r
  Px{sa, sb} = m
  +nn = n
  cent(xs, (sa / nn : F32), (sb / nn : F32), 0.0, 0.0, 0.0)

def pearson(+xs: List<&2, Px>) -> F32:
  pearson.k(sums(xs, 0.0, 0.0, 0.0), xs)

def rank_ic(xs: List<&2, Px>) -> F32:
  r1 = enum(List.sort(~Px, ~le_a, xs), 0.0, Nil{})
  r2 = enum(List.sort(~Px, ~le_a, r1), 0.0, Nil{})
  pearson(r2)

def ics(panel: List<&2, List<&2, Px>>, acc: List<&2, F32>) -> List<&2, F32>:
  match panel:
    case Nil{}:
      acc
    case Con{h, t}:
      ics(t, rank_ic(h) <> acc)

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

# mean IC, sd, t
def summary.k(r: F32 & F32, +xs: List<&2, F32>) -> String:
  (s, n) = r
  +nn = n
  +m = (s / nn : F32)
  +sd = F32.sqrt((ss1(xs, m, 0.0) / (nn - 1.0) : F32))
  "ic=" ++ F32.show(m) ++ " sd=" ++ F32.show(sd) ++ " t=" ++ F32.show(((m / sd) * F32.sqrt(nn) : F32))

def summary(+xs: List<&2, F32>) -> String:
  summary.k(sum1(xs, 0.0, 0.0), xs)

def fst(r: Px & F32) -> F32:
  (m, _) = r
  Px{a, _} = m
  a

def chk(+panel: List<&2, List<&2, Px>>, +s: F32) -> F32:
  match panel:
    case Nil{}:
      s
    case Con{h, t}:
      chk(t, (s + fst(sums(h, 0.0, 0.0, 0.0)) : F32))

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
    IO.print("gen chk=" ++ F32.show(chk(panel, 0.0)))
    +t1 : Nat <- IO.now()
    +ic : List<&2, F32> = ics(panel, Nil{})
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
