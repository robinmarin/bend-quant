# signal: panel design

`signal` evaluates cross-sectional signals: per-date IC, rank IC, and their summary statistics. Every one of those reads a panel, T dates by N names, so the panel type comes first. The numbers behind these choices are in [bench/README.md](bench/README.md).

## The type

```bend
type Panel is Data:
  Panel{t: U32, n: U32, rows: List<&2, List<&2, F32>>}
```

A panel is a list of rows, oldest date first. Each row is one date's cross-section, a list of `n` floats. Column `j` is the same name on every date.

## Decisions

**F32, not F64.** The benchmark shows `F32` drifts in the 7th digit of mean IC. The IC's own standard error on that panel is sd / sqrt(T) = 0.032 / 71 = 0.00045, about a thousand times larger than the drift. Soft-float `F64` costs about 100 times as much per operation, and z-scores and EWMAs are all elementwise. So rows are `F32`, and long sums use pairwise addition like `A.sum` does, not a running total. I recommended `F64` before the benchmark. The numbers changed my mind. Money paths such as compounded PnL belong to a later package, and they should revisit this, or switch once Base gets native `F64` (bendlang/bend#1120).

**NaN marks a missing value.** pandas and numpy do the same, and NaN survives a numpy `.tofile` round trip into `F32Array` (checked in a spike). Bend detects it with `F32.is_ne(x, x)`. A separate mask would double the memory and need its own alignment checks. A name that enters or leaves the universe is NaN on the dates it isn't trading. Every function drops the names that are NaN in either input for that date, so it computes on complete pairs.

**Rows are lists, not `F32Array`.** The first version used bend-kit's `F32Array`. It is a `Type`, so every value can be used once, and Bend enforces that inside proofs too. A proof that a list of rows survives a split and an append has to mention the list in two lemmas, and the checker rejects it. A lemma can't take the list as erased either, since a proof can only match on live values. As `List<&2, F32>` the rows are `Data`, the proofs can name them freely, and a loaded panel can be reused. The cost was measured on two 5000 × 1000 panels: 280 MB resident, about 28 bytes per value against 4, and the same speed, 0.32 s on 8 cores at the time (0.36 s now that the pair filter builds an explicit list). `F32Array` stays at the edge, for reading files.

Sorts copy the complete pairs of a date into a scratch `Array<F32>`, key and payload interleaved as in `bench/array_f32.bend`, and heapsort that. The copy is O(n) against the sort's O(n log n).

**Labels stay outside.** The panel holds numbers only. The caller keeps the date and ticker lists that index rows and columns. Bend strings are slow lists of characters, and no IC needs a ticker.

**The caller aligns forward returns.** `ic(x, y)` pairs row `i` of `x` with row `i` of `y`. The caller builds `y` so that row `i` holds the return from date `i` to `i + h`. A `lead(y, h)` helper can come later if building `y` by hand proves error-prone. Mismatched `t` or `n` returns `None`.

**Ties get the average rank.** The benchmark ignored ties because its draws rarely collide. Real data collides a lot, think zero returns and prices on a tick grid. After the sort, a run of equal keys gets the mean of its positions, which is scipy's `rankdata` default.

**Work splits over dates.** Each date's IC is independent, so `ic` forks over the rows the way `bench/array_f32.bend` does. Within a date the work stays sequential. N rarely passes a few thousand, and the 8-core result already beats numpy by 4.6 times.

## Loading

```sh
# Python side, from DuckDB or pandas
panel.to_numpy(dtype="<f4").tofile("signal.f32")   # T x N, row-major, NaN = missing
```

`io.bend` will expose `Panel.load(path, t, n)`. It reads row `i` with `F.read.le.at` at byte offset `4 * n * i`, the call the spike used. Like `f32array`, `io.bend` keeps effects out of the module that `PROOF.bend` imports.

## First API

All built, plus `forward_ic`, `lead`, `ewma` and `rolling_mean`; [README.md](README.md) has the exact types.

| def | result |
|---|---|
| `Panel.from_rows(rows)` | `Maybe<Panel>`, `None` when rows differ in length |
| `Panel.load(path, t, n)` | in `io.bend`, `IO(Result<Panel>)` |
| `rank_ic(x, y)` | `Maybe<List<F32>>`, one Spearman IC per date, NaN where fewer than 3 complete pairs |
| `ic(x, y)` | the same with Pearson |
| `summary(ics)` | mean, sd, IR, t, hit rate, and the count of non-NaN dates |
| `nw_t(ics, lags)` | Newey-West t of the mean IC |
| `zscore(p)`, `demean(p)`, `rank(p)`, `winsorize(p, q)` | row-wise transforms, NaN passed through |

Hidden helpers cover the array plumbing: fold, map, and sort over a scratch `Array<F32>`. In Bend every `Array.get` hands back a pair, a computed pair can't be destructured, and defs can't call each other in a cycle. A heap sift step took five helper defs in the benchmark. The public functions should never touch `get` and `set` directly.

## Laws

The checker doesn't run `F32` arithmetic, so no law can state an IC value. Laws over floats can only be fixtures, as in `f32array`. What a law can state for every input is the structure: which rows reach which IC, in what order, and how far `lead` shifts. README.md lists the laws that hold now.

Proved since: the complete-pair filter (`date_ic_missing_x`, `date_ic_missing_y`). The proof states it generically: changing one side's value where the other side is NaN leaves the IC unchanged. Still to prove:

- ranks match the counting definition, 2·rankᵢ = 2·#{xⱼ < xᵢ} + #{xⱼ = xᵢ} − 1, for any total order. bend-mathlib proves a merge sort sorted and a permutation, which is the place to start.

## Open questions

- Does any caller need a mask that tells "missing" apart from "not in the universe"? NaN merges the two. I'd wait for a caller.
- At what N should one date's sort run in parallel? The panels on hand don't need it.
