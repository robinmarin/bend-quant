# Prints rank IC, Pearson IC, and the rank IC summary for two panels on disk.
# check.py writes the panels, runs this, and compares with scipy.
# Usage: out/check x.f32 y.f32 T N TY H
# y loads TY rows; TY != T tests the shape check. H = 0 runs rank_ic(x, y) and
# ic(x, y); H > 0 runs forward_rank_ic and forward_ic with horizon H - 1, so row i
# meets row i + H of y.
import Base
import ./signal.bend as S
import ./io.bend as I

def lines(+tag: String, xs: List<&2, F32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      tag ++ " " ++ F32.show(h) ++ "\n" ++ lines(tag, t)

def show.sum(m: Maybe<&2, S.Summary>) -> String:
  match m:
    case None{}:
      "sum none\n"
    case Some{s}:
      match s:
        case S.Summary{mean, sd, ir, t, hit, count}:
          "sum " ++ F32.show(mean) ++ " " ++ F32.show(sd) ++ " " ++ F32.show(ir) ++ " " ++ F32.show(t) ++ " " ++ F32.show(hit) ++ " " ++ U32.show(count) ++ "\n"

def show.rank(m: Maybe<&2, List<&2, F32>>) -> String:
  match m:
    case None{}:
      "rank none\n"
    case Some{+xs}:
      lines("rank", xs) ++ show.sum(S.summary(xs))

def show.ic(m: Maybe<&2, List<&2, F32>>) -> String:
  match m:
    case None{}:
      "ic none\n"
    case Some{xs}:
      lines("ic", xs)

def pair(same: Bool, +a: S.Panel, +b: S.Panel, +k: Nat) -> String:
  match same:
    case True{}:
      show.rank(S.rank_ic(a, b)) ++ show.ic(S.ic(a, b))
    case False{}:
      show.rank(S.forward_rank_ic(a, b, k)) ++ show.ic(S.forward_ic(a, b, k))

def report(px: Result<&1, &1, U32 & String, S.Panel>, py: Result<&1, &1, U32 & String, S.Panel>, +h: U32) -> String:
  match px py:
    case Done{+a} Done{+b}:
      pair(U32.is_eq(h, 0), a, b, U32.to_nat((h - 1 : U32)))
    case _ _:
      "load failed\n"

# ---- transforms mode: out/check x.f32 T N prints every transform of x, one row per line

def vals(xs: List<&2, F32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      " " ++ F32.show(x) ++ vals(t)

def rows(+tag: String, xs: List<&2, List<&2, F32>>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{r, t}:
      tag ++ vals(r) ++ "\n" ++ rows(tag, t)

def show.panel(+tag: String, p: S.Panel) -> String:
  S.Panel{_, _, r} = p
  rows(tag, r)

def transforms(px: Result<&1, &1, U32 & String, S.Panel>) -> String:
  match px:
    case Done{+a}:
      show.panel("zscore", S.zscore(a)) ++ show.panel("demean", S.demean(a)) ++ show.panel("rank", S.rank(a)) ++ show.panel("winsorize", S.winsorize(a, 0.1)) ++ show.panel("ewma", S.ewma(a, 0.3)) ++ show.panel("rolling", S.rolling_mean(a, 3n))
    case Fail{_}:
      "load failed\n"

def run.tf(xp: String, +t: U32, +n: U32) -> IO(Unit):
  do IO<Unit>:
    px : Result<&1, &1, U32 & String, S.Panel> <- I.Panel.load(xp, t, n)
    IO.print(transforms(px))

def num(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{n}:
      n
    case None{}:
      0

def run(xp: String, yp: String, +t: U32, +n: U32, +ty: U32, +h: U32) -> IO(Unit):
  do IO<Unit>:
    px : Result<&1, &1, U32 & String, S.Panel> <- I.Panel.load(xp, t, n)
    py : Result<&1, &1, U32 & String, S.Panel> <- I.Panel.load(yp, ty, n)
    IO.print(report(px, py, h))

def go(args: List<String>) -> IO(Unit):
  match args:
    case _ <> xp <> yp <> ts <> ns <> tys <> hs <> _:
      run(xp, yp, num(U32.read(ts)), num(U32.read(ns)), num(U32.read(tys)), num(U32.read(hs)))
    case _ <> xp <> ts <> ns <> Nil{}:
      run.tf(xp, num(U32.read(ts)), num(U32.read(ns)))
    case _:
      IO.print("usage: check x.f32 y.f32 T N TY H, or check x.f32 T N for transforms")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
