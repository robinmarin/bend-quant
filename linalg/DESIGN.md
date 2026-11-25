# linalg: design

`linalg` provides dense linear algebra in Bend, scoped from the factor-model, risk, portfolio-construction, and attribution operations in Paleologo's *The Elements of Quantitative Investing* (Ch 4–7, 9–12, 14). The benchmark and precision numbers behind these choices are in [bench/README.md](bench/README.md).

## Types

```bend
type Vec is Data:
  Vec{n: U32, data: List<&2, F32>}

type Mat is Data:
  Mat{m: U32, n: U32, rows: List<&2, List<&2, F32>>}
```

A `Mat` is a list of `m` rows, each a list of `n` `F32` floats. This matches `signal`'s `Panel{t, n, rows}` layout directly so panels and matrices share rows with zero copying. A `Vec` carries its length `n` alongside its elements so binary vector ops and matrix-vector products reject shape mismatches in O(1) without walking the list.

All fallible operations (shape mismatch, non-square `trace`, non-SPD `cholesky`, singular triangular solve) return `Maybe<&2, _>` with `None{}` on error.

## Decisions

**Hybrid layout: `Data` lists at the API, flat `Array<F32>` inside factorization kernels.**
`Mat` and `Vec` are `Data`, so values are reusable across calls (no affine consumption), work cleanly in parallel fork-join (`pmap`), and can be named freely in `LAWS.bend` and `PROOF.bend`.

For random-indexed, in-place factorizations (`cholesky`, `qr_thin`, `sym_eigen`, `svd_thin`), [bench/README.md](bench/README.md) shows flat `Array<F32>` is 6–12× faster than `List` (`0.012 ms` vs `0.076 ms` for $50 \times 50$ Cholesky; `2 ms` for $1000 \times 50$ thin Householder QR, within 1.4× of Apple Accelerate LAPACK). Those kernels convert their `K × K` or `N × K` input into a scratch `Array<F32>`, run the numeric loops in place, and extract the result back into `Data` `Mat`/`Vec` through provable builders that enforce exact dimensions and triangular zero-structure.

Purely sequential/parallel streaming operations (`transpose`, `matvec`, `matmul`, `gram`, `wgram`, diagonal scaling, slicing) stay on `Data` lists with `pmap` fork-join over rows so every structural law (shape, transpose involution, entry indexing, symmetry, `pmap == pseq`) holds end-to-end without `@unsafe`.

**`F32` default scalar type, with thin Householder QR for WLS/OLS.**
Soft-float `F64` (`bend-kit-f64`) is ~100× slower per op (`3.8 ms` vs `0.012 ms` for $50 \times 50$ Cholesky; `67 ms` vs `< 1 ms` for $50 \times 50$ Jacobi). The precision sweep in [bench/README.md](bench/README.md) shows:
- `F32` normal equations (`Bᵀ W B`) square the condition number and break Cholesky outright at $\kappa(B) = 10^4$ (already 2.2% error at $\kappa = 10^3$).
- `F32` **thin Householder QR** avoids squaring $\kappa(B)$, holding relative error at `3.1e-6` ($\kappa = 10^3$) and `2.5e-5` ($\kappa = 10^4$) in `2 ms`.
- `F32` **Woodbury MVO** `(D + B Ω_f Bᵀ)⁻¹ α` keeps Sharpe Ratio Efficiency at `1.000000` and weight error at `2.7e-5` even at $\kappa(\Omega_f) = 10^6$.
- `F32` **cyclic Jacobi** reaches `1.2e-5` reconstruction error on spiked $50 \times 50$ covariances when using `F32.hypot(1.0, tau)` to prevent `tau * tau` overflow on tiny off-diagonals.

So `F32` is the scalar type everywhere until Bend gets native `F64` (bendlang/bend#1120), and `lstsq` / `wlstsq` are implemented via thin Householder QR rather than normal equations.

**Structural symmetry in `gram`, `wgram`, and `spd_pow`.**
`gram(A)` and `wgram(A, w)` compute only the upper triangle ($j \ge i$) of $A^\top A$ (or $A^\top \operatorname{diag}(w) A$) on flat column-major `Array<F32>`, extract it as rows of lengths $n, n-1, \dots, 1$ via `arr_upper_tri`, and mirror it into the lower triangle with `mirror_upper`. This halves the dot-product work, runs at flat-array speed (`1.3–1.5 ms` for $1000 \times 50$), and guarantees exact bitwise symmetry `get(G, i, j) == get(G, j, i)` provably in BendTT without needing float commutativity. `spd_pow(A, p)` builds $U \operatorname{diag}(\lambda^p) U^\top$ via `wgram(transpose(U), λ^p)`, inheriting the same proof.

**Effects stay in `io.bend`.**
`Mat.load` and `Vec.load` live in [io.bend](io.bend) using `bend-kit-f32array@0.2.1.0`, matching `signal/io.bend` so `PROOF.bend` imports no IO or foreign code.

## Laws

Bend's checker treats `F32` arithmetic as opaque, so numerical accuracy is checked against NumPy and SciPy in `check.py`, while `LAWS.bend` and `PROOF.bend` (checked with `bend PROOF.bend --verdict`) prove structural invariants for all inputs:

- **Header checks:** ops trust the `Mat`/`Vec` header. `Mat.from_rows` builds it from the rows; `Mat.ok` / `Vec.ok` check any other matrix.
- **Parallel equivalence (`pmap_seq`):** parallel `pmap` returns the exact same list as sequential `pseq` for every size.
- **Shape:** `transpose`, `matvec`, `matmul`, `svd_thin` and `pinv` map well-formed inputs to well-formed outputs; `cholesky`, `qr_thin`, `sym_eigen` and `procrustes` have proved output shapes whenever they succeed. Other ops (`scale`, `madd`, `outer`, slicing, ...) have no shape law and are covered by `check.py`.
- **Transpose laws:** `transpose(transpose(A)) == A` and `get(transpose(A), j, i) == get(A, i, j)` for every rectangular matrix `A`.
- **Entry indexing:** `matvec` and `matmul` route the expected row and column to each output entry.
- **Symmetry:** `get(M, i, j) == get(M, j, i)` for `gram(A)`, `wgram(A, w)` and `spd_pow(A, p)`, for all indices.
- **Triangular zeros:** `cholesky` gives exact `0.0` above the diagonal, `qr_thin`'s `R` exact `0.0` below it.
- **Dimension guards:** fallible ops return `None` when headers don't fit.
