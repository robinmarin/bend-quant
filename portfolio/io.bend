# FactorModel.load: read row-major float32 files for B (N x K), Omega_f (K x K),
# and diag(Omega_eps) (N). Kept apart from portfolio.bend so PROOF.bend imports
# no effects.
#
# Public: FactorModel.load.
import Base
import bend-quant-linalg@0.1.0.0/linalg.bend as L
import bend-quant-linalg@0.1.0.0/io.bend as LI
import ./portfolio.bend as P

def load.fm.from_maybe(mfm: Maybe<&2, P.FactorModel>) -> Result<&1, &1, U32 & String, P.FactorModel>:
  match mfm:
    case Some{fm}:
      Done{fm}
    case None{}:
      Fail{(0, "invalid FactorModel (shape mismatch, short file, or non-positive idio_var)")}

def load.fm.wrap(rb: Result<&1, &1, U32 & String, L.Mat>, rcf: Result<&1, &1, U32 & String, L.Mat>, rd: Result<&1, &1, U32 & String, L.Vec>) -> Result<&1, &1, U32 & String, P.FactorModel>:
  match rb rcf rd:
    case Done{b} Done{cf} Done{d}:
      load.fm.from_maybe(P.FactorModel.new(b, cf, d))
    case Fail{e} _ _:
      Fail{e}
    case Done{_} Fail{e} _:
      Fail{e}
    case Done{_} Done{_} Fail{e}:
      Fail{e}

# Loads B (n x k), cov_f (k x k), and idio_var (n) from raw little-endian float32 files.
def FactorModel.load(b_path: String, cov_f_path: String, idio_path: String, +n: U32, +k: U32) -> IO(Result<&1, &1, U32 & String, P.FactorModel>):
  do IO<Result<&1, &1, U32 & String, P.FactorModel>>:
    rb : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(b_path, n, k)
    rcf : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(cov_f_path, k, k)
    rd : Result<&1, &1, U32 & String, L.Vec> <- LI.Vec.load(idio_path, n)
    return load.fm.wrap(rb, rcf, rd)
