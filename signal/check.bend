# Prints rank IC, Pearson IC, and the rank IC summary for two panels on disk.
# check.py writes the panels, runs this, and compares with scipy.
# Usage: out/check x.f32 y.f32 x.f32 y.f32 T N TY
# Each panel is consumed, so each path comes twice. y loads TY rows; TY != T tests the shape check.
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

def report(
  px: Result<&1, &1, U32 & String, S.Panel>, py: Result<&1, &1, U32 & String, S.Panel>,
  qx: Result<&1, &1, U32 & String, S.Panel>, qy: Result<&1, &1, U32 & String, S.Panel>
) -> String:
  match px py qx qy:
    case Done{a} Done{b} Done{c} Done{d}:
      show.rank(S.rank_ic(a, b)) ++ show.ic(S.ic(c, d))
    case _ _ _ _:
      "load failed\n"

def num(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{n}:
      n
    case None{}:
      0

def run(xp: String, yp: String, xp2: String, yp2: String, +t: U32, +n: U32, +ty: U32) -> IO(Unit):
  do IO<Unit>:
    px : Result<&1, &1, U32 & String, S.Panel> <- I.Panel.load(xp, t, n)
    py : Result<&1, &1, U32 & String, S.Panel> <- I.Panel.load(yp, ty, n)
    qx : Result<&1, &1, U32 & String, S.Panel> <- I.Panel.load(xp2, t, n)
    qy : Result<&1, &1, U32 & String, S.Panel> <- I.Panel.load(yp2, ty, n)
    IO.print(report(px, py, qx, qy))

def go(args: List<String>) -> IO(Unit):
  match args:
    case _ <> xp <> yp <> xp2 <> yp2 <> ts <> ns <> tys <> _:
      run(xp, yp, xp2, yp2, num(U32.read(ts)), num(U32.read(ns)), num(U32.read(tys)))
    case _:
      IO.print("usage: check x.f32 y.f32 x.f32 y.f32 T N TY")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
