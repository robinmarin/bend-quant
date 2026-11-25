# linalg

Dense float32 linear algebra in Bend: vector and matrix ops, Cholesky, triangular solves, Woodbury and the Matrix Determinant Lemma, thin Householder QR, ordinary / weighted / equality-constrained least squares, cyclic Jacobi eigendecomposition, SPD matrix powers, thin SVD, Moore–Penrose pseudoinverse, and orthogonal Procrustes. [DESIGN.md](DESIGN.md) explains the layout and precision choices, and [bench/](bench/README.md) has the benchmark and conditioning numbers behind them.

```bend
import bend-quant-linalg@0.1.1.0/linalg.bend as L
import bend-quant-linalg@0.1.1.0/io.bend as I
```

From a clone, import `./linalg/linalg.bend` and `./linalg/io.bend` instead. A `Mat` is a `Data` row list (`List<&2, List<&2, F32>>`), matching `signal`'s `Panel` layout directly so panels and matrices share rows with zero copying. `io.bend` imports `bend-kit-f32array@0.2.1.0` to read row-major float32 files.

The types and defs in the API table below are the public ones. Every other def is internal: the laws and proofs name them, and they can change in any version.

## What is proved and what is tested

`LAWS.bend` states 45 laws and `PROOF.bend` proves all of them with zero `@unsafe` and no IO imports. 24 are structural laws over every input, 14 are dimension guards, and 7 are fixed examples. `PROOF.bend` uses `bend-mathlib@0.1.0.0` for generic list lemmas.

Ops trust the `m × n` header on a `Mat` and the `n` on a `Vec`; they do not walk the rows to check it. `Mat.from_rows` builds a correct header from the rows. For a matrix from anywhere else (`Mat{...}` directly, `Mat.load`, `Mat.from_flat` on a short file), check `Mat.ok(a)` / `Vec.ok(v)` first. The `_ok` laws below say that well-formed inputs give well-formed outputs.

Structural laws (every input):

- **Parallel equivalence (`pmap_seq`, `pseq_get`):** the parallel fork-join map (`pmap`) gives the same list as the sequential loop (`pseq`) for every length. `scale`, `slice_cols`, `mul_diag`, `outer`, `matvec`, `matmul`, `gram` and `wgram` run on it.
- **Transpose (`transpose_len`, `transpose_row_len`, `transpose_get`, `transpose_involutive`, `transpose_ok`):** transposing a rectangular `m × n` row list gives `n` rows of length `m`, swaps `(i, j)` for every index in or out of bounds, and is an involution. A well-formed `Mat` transposes to a well-formed `Mat`.
- **Products (`matvec_entry`, `matmul_entry`, `matvec_ok`, `matmul_ok`):** each entry of `matvec` and `matmul` is the expected row-column dot product, and well-formed inputs give a well-formed result.
- **Exact symmetry (`mirror_upper_sym`, `gram_sym`, `wgram_sym`, `spd_pow_sym`):** `get(M, i, j) == get(M, j, i)` bitwise for every `(i, j)`.
- **Cholesky (`cholesky_shape`, `cholesky_upper_zero`):** whenever `cholesky` succeeds, `L` has `n` rows of length `n` and exact `0.0` above the diagonal.
- **Thin QR (`qr_q_shape`, `qr_r_shape`, `qr_r_lower_zero`):** whenever `qr_thin` succeeds, `Q` has `m` rows of length `n`, `R` has `n` rows of length `n`, and `R` has exact `0.0` below the diagonal.
- **Eigen (`sym_eigen_shape`):** whenever `sym_eigen` succeeds, `values` has length `n` and `vectors` has `n` rows of length `n`.
- **SVD, pseudoinverse, Procrustes (`svd_thin_ok`, `pinv_ok`, `procrustes_shape`):** for a well-formed `m × n` matrix, `svd_thin` gives `U` (`m × k`), `s` (length `k`) and `V^T` (`k × n`) with headers that match their rows, and `pinv` gives a well-formed `n × m` matrix. Whenever `procrustes(A, B)` succeeds, the result is a well-formed `k × k` matrix, `k` the column count of `A`.

Dimension guards: `cholesky_nonsquare`, `sym_eigen_nonsquare`, `spd_pow_nonsquare`, `qr_thin_wide`, `matmul_mismatch`, `solve_lower_mismatch`, `solve_upper_mismatch`, `woodbury_solve_mismatch`, `lstsq_mismatch`, `wlstsq_mismatch`, `lstsq_mat_mismatch`, `project_orth_mismatch`, `lstsq_constrained_mismatch`, `procrustes_mismatch`. Each says the op returns `None` when the headers don't fit. They compare headers only.

Fixed examples: `from_rows_equal`, `from_rows_ragged`, `from_rows_ragged_last`, `from_rows_empty` (`Mat.from_rows` accepts rectangular lists and rejects ragged ones), and `mat_ok_rect`, `mat_ok_wrong_m`, `mat_ok_ragged`.


Bend's checker does not reduce `F32` arithmetic, so numerical accuracy is verified against NumPy and SciPy in `check.py` instead.

## Example

Write a design matrix `A` (`m × n`) and response vector `b` (`m`) from Python as little-endian float32:

```python
A.astype("<f4").tofile("a.f32")
b.astype("<f4").tofile("b.f32")
```

Solve `min_x ||A x - b||_2` via thin Householder QR in Bend:

```bend
import Base
import bend-quant-linalg@0.1.1.0/linalg.bend as L
import bend-quant-linalg@0.1.1.0/io.bend as I

def solve(ra: Result<&1, &1, U32 & String, L.Mat>, rb: Result<&1, &1, U32 & String, L.Vec>) -> String:
  match ra rb:
    case Done{a} Done{b}:
      match L.lstsq(a, b):
        case Some{L.Vec{n, _}}:
          "solved length " ++ U32.show(n)
        case None{}:
          "singular or shape mismatch"
    case _ _:
      "load failed"

def main() -> IO(Unit):
  do IO<Unit>:
    ra : Result<&1, &1, U32 & String, L.Mat> <- I.Mat.load("a.f32", 500, 30)
    rb : Result<&1, &1, U32 & String, L.Vec> <- I.Vec.load("b.f32", 500)
    IO.print(solve(ra, rb))
```

`check.bend` is a complete CLI exercising every operation in the library.

## API

### Types

- `L.Vec{n: U32, data: List<&2, F32>}` (`Data`)
- `L.Mat{m: U32, n: U32, rows: List<&2, List<&2, F32>>}` (`Data`)
- `L.QR{q: Mat, r: Mat}` (`Data`)
- `L.Eigen{values: Vec, vectors: Mat}` (`Data`)
- `L.SVD{u: Mat, s: Vec, vt: Mat}` (`Data`)

### Constructors, accessors & IO

| def | result |
|---|---|
| `L.Vec.from_list(xs: List<&2, F32>)` | `Vec` |
| `L.Vec.from_flat(a: A.F32Array)` | `Vec` from a flat float32 array |
| `L.Vec.zeros(n: U32)`, `L.Vec.ones(n: U32)` | length-`n` constant `Vec` |
| `L.Vec.get(v: Vec, i: Nat)` | `Maybe<&2, F32>` |
| `L.Mat.from_rows(rows: List<&2, List<&2, F32>>)` | `Maybe<&2, Mat>`, `None` when two rows differ in length |
| `L.Mat.ok(a)` / `L.Vec.ok(v)` | `Bool`, whether the declared header matches the rows (`m` rows of length `n`) or the data length |
| `L.Mat.from_flat(a: A.F32Array, m: U32, n: U32)` | `Mat` from a row-major flat array |
| `L.Mat.zeros(m, n)`, `L.Mat.eye(n)`, `L.Mat.diag(v)` | zero, identity, and diagonal `Mat` |
| `L.Mat.get(a: Mat, i: Nat, j: Nat)` | `Maybe<&2, F32>` |
| `L.Mat.diag_vec(a: Mat)` | `Vec` of diagonal entries (`min(m, n)`) |
| `I.Vec.load(path: String, n: U32)` | `IO(Result<&1, &1, U32 & String, Vec>)` |
| `I.Mat.load(path: String, m: U32, n: U32)` | `IO(Result<&1, &1, U32 & String, Mat>)` |

### Vector & matrix operations

| def | result |
|---|---|
| `L.dot(x, y)` | `Maybe<&2, F32>` inner product |
| `L.norm1(x)`, `L.norm2(x)` | `F32` $\ell_1$ and $\ell_2$ norms |
| `L.vscale(s, x)`, `L.vadd(x, y)`, `L.vsub(x, y)` | scaled, summed, and differenced vectors |
| `L.axpy(a, x, y)`, `L.vmul(x, y)`, `L.vdiv(x, y)` | `a * x + y` and elementwise product / quotient |
| `L.outer(x, y)` | `Mat` outer product $x y^\top$ |
| `L.scale(s, a)`, `L.madd(a, b)`, `L.msub(a, b)` | scaled, summed, and differenced matrices |
| `L.frobenius(a)`, `L.trace(a)` | Frobenius norm (`F32`), trace (`Maybe<&2, F32>`, square only) |
| `L.transpose(a)` | `Mat` $A^\top$ |
| `L.slice_rows(a, r0, rm)`, `L.slice_cols(a, c0, cn)`, `L.submatrix(a, r0, rm, c0, cn)` | clamped row/column/block slices |
| `L.diag_mul(d, a)`, `L.mul_diag(a, d)` | `Maybe<&2, Mat>` $\operatorname{diag}(d) A$ and $A \operatorname{diag}(d)$ |
| `L.matvec(a, x)`, `L.matvec_t(a, x)` | `Maybe<&2, Vec>` $A x$ and $A^\top x$ |
| `L.matmul(a, b)` | `Maybe<&2, Mat>` $A B$ |
| `L.gram(a)`, `L.wgram(a, w)` | structurally symmetric $A^\top A$ and $A^\top \operatorname{diag}(w) A$ |
| `L.quad_form(x, a)` | `Maybe<&2, F32>` $x^\top A x$ |

### Cholesky, triangular solves & Woodbury

| def | result |
|---|---|
| `L.cholesky(a)` | `Maybe<&2, Mat>`, lower-triangular $L$ with $A = L L^\top$; `None` if non-square or non-SPD |
| `L.solve_lower(l, b)`, `L.solve_upper(u, b)` | `Maybe<&2, Vec>` solving $L x = b$ or $U x = b$; `None` on mismatch or zero diagonal |
| `L.solve_lower_mat(l, b)`, `L.solve_upper_mat(u, b)` | `Maybe<&2, Mat>` multi-RHS triangular solves |
| `L.cholesky_solve(l, b)`, `L.cholesky_solve_mat(l, b)` | solve $(L L^\top) x = b$ (or $X$) from factor $L$ without transposing $L$ |
| `L.cholesky_logdet(l)` | `Maybe<&2, F32>` $= 2 \sum_i \log L_{ii}$ |
| `L.woodbury_solve(d, u, m, b)` | `Maybe<&2, Vec>` solving $(\operatorname{diag}(d) + U M U^\top) x = b$ via inverse-free $K \times K$ Cholesky on $C = I_K + L_m^\top (U^\top D^{-1} U) L_m$ |
| `L.woodbury_logdet(d, u, m)` | `Maybe<&2, F32>` $= \sum_i \log d_i + \log\det(C)$ via the Matrix Determinant Lemma |

### QR, least squares & projection

| def | result |
|---|---|
| `L.qr_thin(a)` | `Maybe<&2, QR>` for $m \ge n$: orthonormal `Q` ($m \times n$) and upper-triangular `R` ($n \times n$); `None` if $m < n$ |
| `L.lstsq(a, b)` | `Maybe<&2, Vec>` $\arg\min_x \|A x - b\|_2$ via thin Householder QR (avoids squaring $\kappa(A)$) |
| `L.wlstsq(a, w, b)` | `Maybe<&2, Vec>` weighted least squares via QR on $(\operatorname{diag}(\sqrt{w}) A, \sqrt{w} \odot b)$; accepts $w_i \ge 0$, rejects $w_i < 0$ |
| `L.lstsq_mat(a, b)` | `Maybe<&2, Mat>` multi-RHS least squares, factoring `A` once |
| `L.project_orth(q, x)` | `Maybe<&2, Vec>` $(I - Q Q^\top) x$ for orthonormal `Q`, applied twice (Kahan–Parlett) for `F32` orthogonality |
| `L.lstsq_constrained(a, b, c, d)` | `Maybe<&2, Vec>` $\arg\min_x \|A x - b\|_2$ subject to $C^\top x = d$ ($C$ is $n \times p$, $m \ge n - p$) via null-space QR of $C$; supports rank-deficient $A$ |

### Spectral decomposition, thin SVD, pseudoinverse & Procrustes

| def | result |
|---|---|
| `L.sym_eigen(a)` | `Maybe<&2, Eigen>` $A = V \operatorname{diag}(\lambda) V^\top$ via cyclic Jacobi with descending $\lambda$ and orthonormal columns of $V$; `None` if non-square |
| `L.spd_pow(a, p)` | `Maybe<&2, Mat>` $A^p = V \operatorname{diag}(\lambda^p) V^\top$ (structurally symmetric); `None` if non-square or non-SPD |
| `L.svd_thin(a)` | `SVD{u, s, vt}` ($A = U \operatorname{diag}(s) V^\top$, $k = \min(m, n)$, descending $s \ge 0$) via QR + One-Sided Jacobi; exploits $\min(m, n)$ when $m < n$ |
| `L.pinv(a, tol)` | `Mat` ($n \times m$) Moore–Penrose pseudoinverse $V \Sigma^+ U^\top$, zeroing singular values $\le \max(0, \text{tol}) \cdot \sigma_{\max}$ |
| `L.procrustes(a, b)` | `Maybe<&2, Mat>` orthogonal $k \times k$ matrix $X = V U^\top$ minimizing $\|A - B X\|_F$ from the SVD of $A^\top B$; `None` on shape mismatch |

## Limits

- Streaming row ops (`scale`, `slice_cols`, `mul_diag`, `outer`, `matvec`, `matmul`, `gram`, `wgram`) parallelize over rows with `pmap` (64 tasks at $m \ge 64$, 2 below). Factorizations (`cholesky`, `qr_thin`, `sym_eigen`, `svd_thin`) run sequentially on flat `Array<F32>` scratch buffers.
- All arithmetic is `F32` (native hardware floats; soft-float `F64` is ~100× slower in Bend 2.0). To preserve precision, `lstsq`/`wlstsq` use thin Householder QR, `woodbury_solve` avoids inverting $M$, and `svd_thin` uses QR + One-Sided Jacobi rather than forming $A^\top A$.
- `sym_eigen` and `svd_thin` run up to 20 cyclic Jacobi sweeps with early convergence exit; this reaches full `F32` accuracy on matrices up to $K \approx 100$.
- API rows are linked lists (~28 bytes per float), and `Mat.load` reads the file in one call ($m \times n < 2^{30}$ floats).

## Checks

```sh
python3 linalg/check.py                   # needs bend, numpy, scipy
cd linalg && bend PROOF.bend --verdict    # checks all 45 laws twice (including Lean-verified BendTT kernel)
```

`check.py` compiles `check.bend` and verifies every public operation against NumPy and SciPy across small, wide, square, parallel (`m >= 64`), ill-conditioned ($\kappa$ up to $10^4$), rank-deficient, zero-dimension, and error cases:

- Core ops (`5×4`, `4×7`, `80×12`): `max_rel_err <= 4.12e-07`, exact bitwise symmetry on `gram` and `wgram`.
- Cholesky & triangular solves (`4×4`, `12×12`, `50×50` at $\kappa=500$): `max_rel_err <= 5.49e-06`, $L L^\top$ reconstruction `<= 1.84e-07`, exact `0.0` above diagonal.
- Woodbury & determinant lemma ($K=0$, $80\times 12$, $200\times 20$ at $\kappa(M)=10^4$): `max_rel_err <= 7.56e-07`.
- Thin QR, OLS/WLS, `project_orth`, and `lstsq_constrained` (up to `500×30`, $\kappa=10^4$, and rank-deficient `100×6` market + 5 industry dummies): `orth <= 7.39e-07`, `recon <= 2.27e-07`, exact `0.0` below diagonal of `R`, constrained residual `<= 1.21e-07`.
- `sym_eigen`, `spd_pow`, `svd_thin`, `pinv`, and `procrustes` (up to `50×50` spiked $\kappa=500$, `100×15` at $\kappa=10^4$, `12×60` wide, rank-deficient `20×8` & `15×5`): `eig` recon `<= 6.67e-06`, `svd` recon `<= 3.78e-07`, `procrustes` err `<= 6.85e-07`, exact bitwise symmetry on `spd_pow`.

Representative end-to-end `linalg.bend` timings on Apple M1 Pro (including `Data` list ↔ `Array<F32>` boundaries, from [bench/README.md](bench/README.md)):

| operation | Bend (`F32`, M1 Pro) | NumPy / Accelerate (`F32`) |
|---|---:|---:|
| `cholesky_solve` ($50 \times 50$) | `0.01 ms` | `0.007 ms` |
| `cholesky` ($50 \times 50$) | `0.09 ms` | `0.011 ms` |
| `project_orth` ($1000 \times 50$) | `0.30 ms` | `0.013 ms` |
| `sym_eigen` ($50 \times 50$) | `0.55 ms` | `0.166 ms` |
| `gram` / `wgram` ($1000 \times 50$) | `1.3–1.5 ms` | `0.008–0.025 ms` |
| `lstsq` / `wlstsq` ($1000 \times 50$) | `1.8–2.2 ms` | `0.96–1.00 ms` |
| `procrustes` ($500 \times 30$) | `1.8 ms` | `0.110 ms` |
| `woodbury_solve` ($1000 \times 50$) | `4.0 ms` | `0.085 ms` |
| `svd_thin` ($500 \times 30$) | `2.8 ms` (8t) | `0.444 ms` |
