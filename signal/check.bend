# Prints rank IC, Pearson IC, and the rank IC summary for two panels on disk.
# check.py writes the panels, runs this, and compares with scipy.
# Usage: out/check x.f32 y.f32 T N TY H
# y loads TY rows; TY != T tests the shape check. ICs are of x against lead(y, H).
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

def report(px: Result<&1, &1, U32 & String, S.Panel>, py: Result<&1, &1, U32 & String, S.Panel>, +h: U32) -> String:
  match px py:
    case Done{+a} Done{b}:
      +c = S.lead(b, h)
      show.rank(S.rank_ic(a, c)) ++ show.ic(S.ic(a, c))
    case _ _:
      "load failed\n"

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
    case _:
      IO.print("usage: check x.f32 y.f32 T N TY H")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
