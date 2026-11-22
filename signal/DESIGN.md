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

A date's work stays on lists too. The first version copied the pairs into a scratch `Array<F32>` and heapsorted it, which was fast, but nothing about it could be proved (see Laws below).

**Labels stay outside.** The panel holds numbers only. The caller keeps the date and ticker lists that index rows and columns. Bend strings are slow lists of characters, and no IC needs a ticker.

**Forward returns are aligned in one place.** `ic(x, y)` pairs row `i` of `x` with row `i` of `y`. Building a forward `y` by hand was the easiest place to slip in a lookahead, so `forward_ic` and `forward_rank_ic` do it with `lead`, and law `forward_row` pins the offset. Mismatched `t` or `n` returns `None`.

**Ties get the average rank.** The benchmark ignored ties because its draws rarely collide. Real data collides a lot, think zero returns and prices on a tick grid. After the sort, a run of equal keys gets the mean of its positions, which is scipy's `rankdata` default.

**Work splits over dates.** Each date's IC is independent, so `ic` forks over the rows the way `bench/array_f32.bend` does. Within a date the work stays sequential. N rarely passes a few thousand, and the 8-core result already beats numpy by 4.6 times.

## Loading

```sh
# Python side, from DuckDB or pandas
panel.to_numpy(dtype="<f4").tofile("signal.f32")   # T x N, row-major, NaN = missing
```

`io.bend` exposes `Panel.load(path, t, n)`. It reads the whole file in one call and slices it into rows. Like `f32array`, `io.bend` keeps effects out of the module that `PROOF.bend` imports.

## API

[README.md](README.md) has the public defs and their exact types.

## Laws

The checker doesn't run `F32` arithmetic, so no law can state an IC value. Laws over floats can only be fixtures, as in `f32array`. What a law can state for every input is the structure: which rows reach which IC, in what order, and how far `lead` shifts. README.md lists the laws that hold now.

Proved since: the complete-pair filter (`date_ic_missing_x`, `date_ic_missing_y`) and the ranks (`rank_count`, `rank_pairs`).

The ranks took a change of algorithm. The heapsort over an `Array<F32>` was fast, but a proof about Array contents would need the tree under Base's `Array`. Ranks now come from a search tree that merges tied values into one node, built by insertion. The proof needs no sortedness: any insertion order gives the right counts, and the order only keeps the tree balanced. That cost about 3 times the heapsort on rank-heavy pipelines. A rank IC now skips the tree: it sorts the pairs by x and replaces x with its rank along the runs of equal keys, then does the same for y. Pearson reads the pairs in any order, so nothing is unsorted, and law `rank_pairs` says the pairs are the spec's in some order. That needs the sort's output proved sorted, which the tree never did. Building the tree from a sorted list instead of by insertion was tried first and saved only 15%, since sorting a list costs about as much as inserting into the tree. `winsorize` takes its quantiles from the same merge sort, and Pearson sums over the pair list. That removed the heapsort and the scratch array, the last code without a proof, for 0.2 s on the winsorize pipeline. Two Bend facts shaped the code: `Bool.pick` evaluates both branches (a recursive pick takes exponential time), and passing a subtree into a lambda hides it from the termination check. So each branch decision is computed by the caller and passed in as a parameter.

## Open questions

- Does any caller need a mask that tells "missing" apart from "not in the universe"? NaN merges the two. I'd wait for a caller.
- At what N should one date's sort run in parallel? The panels on hand don't need it.
