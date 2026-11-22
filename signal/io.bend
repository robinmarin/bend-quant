# Panel.load: read a row-major t x n float32 file, as numpy's
# `a.astype("<f4").tofile(path)` writes it. Kept apart from signal.bend so the
# proofs import no effects.
#
# Public: Panel.load. The load.* defs are internal.
import Base
import bend-kit-f32array@0.2.1.0/f32array.bend as A
import bend-kit-f32array@0.2.1.0/io.bend as F
import ./signal.bend as S

def load.panel(r: Result<&1, &1, U32 & String, A.F32Array>, +t: U32, +n: U32) -> Result<&1, &1, U32 & String, S.Panel>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{a}:
      Done{S.Panel.from_flat(a, t, n)}

def load.fin(got: File & Result<&1, &1, U32 & String, A.F32Array>, +t: U32, +n: U32) -> IO(Result<&1, &1, U32 & String, S.Panel>):
  (f, r) = got
  do IO<Result<&1, &1, U32 & String, S.Panel>>:
    File.close(f)
    return load.panel(r, t, n)

def load.open(r: Result<&1, &1, U32 & String, File>, +t: U32, +n: U32) -> IO(Result<&1, &1, U32 & String, S.Panel>):
  match r:
    case Fail{e}:
      IO.pure(Result<&1, &1, U32 & String, S.Panel>, Fail{e})
    case Done{f}:
      do IO<Result<&1, &1, U32 & String, S.Panel>>:
        got : File & Result<&1, &1, U32 & String, A.F32Array> <- F.read.le.at(f, 0, 0, (t * n : U32))
        load.fin(got, t, n)

# Fails when the file can't be opened or holds fewer than t * n floats.
# ponytail: one read of t * n floats, so t * n must stay under 2^30
def Panel.load(path: String, +t: U32, +n: U32) -> IO(Result<&1, &1, U32 & String, S.Panel>):
  do IO<Result<&1, &1, U32 & String, S.Panel>>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    load.open(r, t, n)
