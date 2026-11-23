# linalg: plan

Dense linear algebra in Bend, scoped directly from the factor-model, risk, portfolio-construction, and attribution operations in Paleologo's *The Elements of Quantitative Investing* (Ch 4–7, 9–12, 14).

The library itself is domain-agnostic (vectors, matrices, factorizations, linear solves), with no finance concepts in its types or names. Domain packages (`portfolio`, etc.) layer on top of `linalg` and `signal`.

## Shape regimes

Quant workloads have a sharp asymmetry:
- **N** (assets): 100 – 3,000 (up to 10,000)
- **K** (factors): 5 – 100
- **T** (rolling estimation window): 126 – 500 (often `T < N`)

Dense `N x N` covariance matrices are almost never inverted directly. Factor structure `Ω = B Ω_f Bᵀ + D` (with `D` diagonal) turns `N x N` solves and log-determinants into `N x K` matrix products plus `K x K` Cholesky solves via Woodbury.

## Target v0.1 API

All dimension-checked operations return `Maybe` on shape mismatch (or non-SPD failure for Cholesky), matching `signal`'s convention.

### 1. Core types & basic ops
- `Vec`, `Mat` (exact backing layout — `List`, `Array`, or hybrid — to be decided by `bench/`)
- `Mat.from_rows`, `Mat.from_flat`, `Mat.load` (in `io.bend`, keeping effects out of `PROOF.bend`)
- `dot`, `norm1`, `norm2`, `frobenius`, `trace`
- `scale`, `add`, `sub`, `axpy`, `outer`
- `transpose`, `slice_rows`, `slice_cols`, `submatrix`
- `diag_mul_vec`, `diag_mul_mat` (`D A`), `mat_mul_diag` (`A D`)
- `matvec` (`A x`), `matvec_t` (`Aᵀ x`), `matmul` (`A B`), `gram` (`Aᵀ A`), `wgram` (`Aᵀ D A`), `quad_form` (`xᵀ A x`)

### 2. SPD solves, Cholesky & Woodbury
- `cholesky(A)` → lower-triangular `L` such that `A = L Lᵀ` (`None` if not SPD)
- `solve_lower(L, b)`, `solve_upper(U, b)` and multi-RHS variants `solve_lower_mat`, `solve_upper_mat`
- `cholesky_solve(L, b)` / `cholesky_solve_mat(L, B)`
- `cholesky_logdet(L)` = `2 * sum(log(L_ii))` (avoids determinant overflow)
- `woodbury_solve(d, U, M, b)` for `(diag(d) + U M Uᵀ)⁻¹ b` using `K x K` Cholesky
- `woodbury_logdet(d, U, M)` via the Matrix Determinant Lemma

### 3. Orthogonalization & least squares
- `qr_thin(A)` (Householder QR for `m >= n`) → `(Q, R)`
- `lstsq(A, b)` and `wlstsq(A, w, b)` (OLS/WLS via thin QR — avoids squaring condition number `κ(A)`)
- `lstsq_mat(A, B)` (multi-RHS least squares)
- `project_orth(Q, x)` = `(I - Q Qᵀ) x` (orthogonalization / Frisch–Waugh–Lovell)
- `lstsq_constrained(A, b, C, a)` (equality-constrained LS `Cᵀ x = a`, for rank-deficient categorical loadings such as market + industry dummies)

### 4. Symmetric eigendecomposition & thin SVD
- `sym_eigen(A)` (symmetric `K x K` → descending eigenvalues `λ` and orthonormal `U`, via cyclic Jacobi or Householder tridiagonalization)
- `spd_pow(A, p)` = `U diag(λ^p) Uᵀ` (covers `A^(1/2)`, `A^(-1/2)` for whitening, STVU, and model linking)
- `svd_thin(A)` (one-sided Jacobi or Gram eigen + orthonormalization; exploits `min(m, n)` when `T < N`)
- `pinv(A, tol)` (Moore–Penrose pseudoinverse from SVD, for ridgeless regression)
- `procrustes(A, B)` (orthogonal `X = V Uᵀ` minimizing `‖A - B X‖_F`, from `K x K` SVD of `Aᵀ B`)

## Explicit non-goals for `linalg`

- **Non-symmetric eigendecomposition** — every eigenproblem in Paleologo is symmetric PSD/SPD.
- **General sparse matrices** — strict factor models use diagonal idiosyncratic variance.
- **Convex QP / SOCP / inequality constraints** (long-only, GMV, L1 turnover) — belongs in `portfolio`, layered on top of `linalg`.

## Open design decisions (to settle in `bench/`)

1. **Representation (`List` vs `Array` vs hybrid):**
   `List<&2, List<&2, F32>>` is `Data` (reusable, parallel-friendly, provable), while `Array<T>` is a linear `Type` lowered to a flat buffer (~6.5× faster random access in `signal/bench/access.bend`, but cannot be shared across parallel branches without `@unsafe Array.fork` or cloning). A likely sweet spot is `Data` row-lists at the public API + parallel `N x K` ops, with `Array` inside single-threaded `K x K` kernels — `bench/` will measure both.
2. **Precision (`F32` vs soft-float `F64`):**
   `signal/bench/` showed soft-float `F64` is ~100× slower per op than hardware `F32`. For large `N x K` matmuls/Grams, `F32` is essential. For small `K x K` solves (`K <= 100`), `K³` is small enough that `F64` may be affordable — or `F32` with thin QR (avoiding normal equations) may already be accurate enough. `bench/` measures both speed and error across condition numbers `κ = 10..10⁶`.
3. **Parallelism:**
   Fork-join over rows/blocks of `N x K` products (`pmap`), sequential inside `K x K` factorizations.

## Planned laws (`LAWS.bend` & `PROOF.bend`)

Bend's checker does not reduce `F32` arithmetic, so numerical accuracy is verified against NumPy/SciPy in `check.py`, while `LAWS.bend` / `PROOF.bend` (checked with `--verdict`) prove structural invariants for all inputs:

- **Shape invariants:** `matmul`, `transpose`, `gram`, `cholesky`, `qr_thin`, `solve_*`, `woodbury_solve` preserve exact declared dimensions and reject mismatches with `None`.
- **Transpose laws:** `transpose(transpose(A)) == A` and `get(transpose(A), i, j) == get(A, j, i)`.
- **Parallel equivalence:** `pmap_seq` — parallel matmul / matvec / Gram gives the exact same matrix as the sequential implementation for every size.
- **Triangular structure:** `cholesky` returns exact zeros strictly above the diagonal; `qr_thin` returns `R` with exact zeros strictly below the diagonal.
- **Symmetry:** `gram` and `wgram` construct structurally symmetric matrices (`get(G, i, j) == get(G, j, i)`).
- **Zero-preservation / identity structure:** structural properties of diagonal scaling and block slicing.

## Milestones

1. **Benchmark & precision spike (`linalg/bench/`):** measure `List` vs `Array` and `F32` vs `F64` (normal equations vs QR, Cholesky, Woodbury, Jacobi eigen) against NumPy/SciPy.
2. **Write `linalg/DESIGN.md`:** lock representation, precision policy, and proof strategy from benchmark numbers.
3. **Core ops + proofs:** `Vec`, `Mat`, matvec/matmul/Gram/transpose, `io.bend`, shape/transpose/parallel proofs.
4. **Cholesky & Woodbury + proofs:** `cholesky`, triangular solves, `logdet`, `woodbury_solve`, `woodbury_logdet`.
5. **QR & least squares + proofs:** thin Householder QR, `lstsq`, `wlstsq`, `project_orth`, `lstsq_constrained`.
6. **Symmetric eigen & thin SVD:** cyclic Jacobi `sym_eigen`, `spd_pow`, `svd_thin`, `pinv`, `procrustes`.
7. **Verification & publish:** full `check.py` suite against NumPy/SciPy, `bend PROOF.bend --verdict`, `README.md`, `publish.bend`.
