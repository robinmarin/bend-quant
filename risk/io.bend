# File IO helpers for risk. Kept apart from risk.bend so PROOF.bend imports
# no effects and zero @unsafe.
#
# Public: Returns.load, LoadingsSeries.load.
import Base
import bend-quant-linalg@0.1.0.0/linalg.bend as L
import bend-quant-linalg@0.1.0.0/io.bend as LI

# Loads a T x N return panel from a row-major little-endian float32 file.
def Returns.load(path: String, +t: U32, +n: U32) -> IO(Result<&1, &1, U32 & String, L.Mat>):
  LI.Mat.load(path, t, n)

# Non-mutual chunking: split rows into rem matrices of shape n x k.
def drop_rows(rem: Nat, rows: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match rem rows:
    case 0n _:
      rows
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{_, rt}:
      drop_rows(p, rt)

def take_rows(rem: Nat, rows: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match rem rows:
    case 0n _:
      Nil{}
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{r, rt}:
      r <> take_rows(p, rt)

def chunk_mats(rem: Nat, +rows: List<&2, List<&2, F32>>, +n: U32, +nn: Nat, +k: U32) -> List<&2, L.Mat>:
  match rem:
    case 0n:
      Nil{}
    case 1n+p:
      L.Mat{n, k, take_rows(nn, rows)} <> chunk_mats(p, drop_rows(nn, rows), n, nn, k)

def load_series.wrap(rm: Result<&1, &1, U32 & String, L.Mat>, +t: U32, +n: U32, +k: U32) -> Result<&1, &1, U32 & String, List<&2, L.Mat>>:
  match rm:
    case Done{L.Mat{_, _, rows}}:
      Done{chunk_mats(U32.to_nat(t), rows, n, U32.to_nat(n), k)}
    case Fail{e}:
      Fail{e}

# Loads T loadings matrices B_0..B_{T-1} (each N x K) from a contiguous row-major float32 file
# of shape (T, N, K) (T * N * K floats).
def LoadingsSeries.load(path: String, +t: U32, +n: U32, +k: U32) -> IO(Result<&1, &1, U32 & String, List<&2, L.Mat>>):
  do IO<Result<&1, &1, U32 & String, List<&2, L.Mat>>>:
    rm : Result<&1, &1, U32 & String, L.Mat> <- LI.Mat.load(path, (t * n : U32), k)
    return load_series.wrap(rm, t, n, k)
