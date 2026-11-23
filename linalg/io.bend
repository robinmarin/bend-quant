# Mat.load and Vec.load: read row-major float32 files, as numpy's
# `a.astype("<f4").tofile(path)` writes them. Kept apart from linalg.bend so
# PROOF.bend imports no effects.
#
# Public: Vec.load, Mat.load. The load.* defs are internal.
import Base
import bend-kit-f32array@0.2.1.0/f32array.bend as A
import bend-kit-f32array@0.2.1.0/io.bend as F
import ./linalg.bend as L

def load.vec.wrap(r: Result<&1, &1, U32 & String, A.F32Array>) -> Result<&1, &1, U32 & String, L.Vec>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{a}:
      Done{L.Vec.from_flat(a)}

def load.vec.fin(got: File & Result<&1, &1, U32 & String, A.F32Array>) -> IO(Result<&1, &1, U32 & String, L.Vec>):
  (f, r) = got
  do IO<Result<&1, &1, U32 & String, L.Vec>>:
    File.close(f)
    return load.vec.wrap(r)

def load.vec.open(r: Result<&1, &1, U32 & String, File>, +n: U32) -> IO(Result<&1, &1, U32 & String, L.Vec>):
  match r:
    case Fail{e}:
      IO.pure(Result<&1, &1, U32 & String, L.Vec>, Fail{e})
    case Done{f}:
      do IO<Result<&1, &1, U32 & String, L.Vec>>:
        got : File & Result<&1, &1, U32 & String, A.F32Array> <- F.read.le.at(f, 0, 0, n)
        load.vec.fin(got)

# Fails when the file can't be opened or holds fewer than n floats.
def Vec.load(path: String, +n: U32) -> IO(Result<&1, &1, U32 & String, L.Vec>):
  do IO<Result<&1, &1, U32 & String, L.Vec>>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    load.vec.open(r, n)

def load.mat.wrap(r: Result<&1, &1, U32 & String, A.F32Array>, +m: U32, +n: U32) -> Result<&1, &1, U32 & String, L.Mat>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{a}:
      Done{L.Mat.from_flat(a, m, n)}

def load.mat.fin(got: File & Result<&1, &1, U32 & String, A.F32Array>, +m: U32, +n: U32) -> IO(Result<&1, &1, U32 & String, L.Mat>):
  (f, r) = got
  do IO<Result<&1, &1, U32 & String, L.Mat>>:
    File.close(f)
    return load.mat.wrap(r, m, n)

def load.mat.open(r: Result<&1, &1, U32 & String, File>, +m: U32, +n: U32) -> IO(Result<&1, &1, U32 & String, L.Mat>):
  match r:
    case Fail{e}:
      IO.pure(Result<&1, &1, U32 & String, L.Mat>, Fail{e})
    case Done{f}:
      do IO<Result<&1, &1, U32 & String, L.Mat>>:
        got : File & Result<&1, &1, U32 & String, A.F32Array> <- F.read.le.at(f, 0, 0, (m * n : U32))
        load.mat.fin(got, m, n)

# Fails when the file can't be opened or holds fewer than m * n floats.
def Mat.load(path: String, +m: U32, +n: U32) -> IO(Result<&1, &1, U32 & String, L.Mat>):
  do IO<Result<&1, &1, U32 & String, L.Mat>>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    load.mat.open(r, m, n)
