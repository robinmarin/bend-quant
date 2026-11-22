# signal

Per-date information coefficients for a cross-sectional signal: Spearman rank IC, Pearson IC, and their mean, sd, IR, t-stat and hit rate. A panel is T dates by N names in float32, with NaN for a missing value. [DESIGN.md](DESIGN.md) explains the choices, and [bench/](bench/README.md) has the numbers behind them.

```bend
import ./signal/signal.bend as S
import ./signal/io.bend as I
```

A row is a `List<&2, F32>`. `io.bend` imports `bend-kit-f32array@0.2.1.0` to read files.

## What is proved and what is tested

`LAWS.bend` states these for every input, and `PROOF.bend` proves them:

- `forward_row`: IC i of `forward_rank_ic(x, ret, h)` is the rank IC of signal row i against return row i + 1 + h. Row j of `ret` is the one-period return over (j - 1, j], so the nearest return a date can meet is the next one. A same-day pairing can't be written with this function.
- `rank_ic_rows` and `ic_row`: when the two panels have the same shape, `rank_ic` returns one IC per date, and IC i is the IC of row i of x against row i of y. Nothing is dropped, reordered or shifted.
- `pmap_seq`: the parallel map gives the same list as the plain loop, for every length. The IC step (`ics_seq`) and the row-wise transforms run on it.
- `date_ic_missing_y` and `date_ic_missing_x`: where a name's return is NaN, changing its signal value leaves that date's IC unchanged, and the same with the roles swapped. `date_ic_pairs` says the IC reads only the pairs present on both sides.
- `lead_row` and `lead_panel`: row i of `lead(p, h)` is row i + h of `p`, whenever that row exists.
- `scan_causal` and `pseq_causal`: for every transform built on `scan` or on a row map, the first k output rows depend only on the first k input rows. `ewma_causal` and `rolling_mean_causal` are the `scan` instances.
- `zscore_row`, `demean_row`, `rank_row`, `winsorize_row`: row i of the output is computed from row i of the input alone.
- `rank_count`: the ranks behind `rank` are average ranks. For every list and every total order, 2 x the rank of q is 1 + #{x < q} + #{x <= q}, so tied values share the mean of their places.
- `rank_pairs`: the pairs a rank IC correlates are, for each complete pair (x, y), 2 x the average rank of x among the xs and of y among the ys. Each such pair appears exactly as often as in the spec. The order differs: the ranks come out of two sorts, and Pearson doesn't depend on order. Its float sums do, by rounding only.

Both rank laws are generic over the comparison, and `--verdict` checks them through an instance at `Nat`.

A signal built only from these transforms and evaluated with `forward_rank_ic` can't see the future anywhere in this library. A full-sample z-score or a centered window can't be written as a `scan`, so it can't claim these laws.

One trust boundary remains: the meaning of the input files. If row j of `ret` holds the return over (j, j + 1] instead of (j - 1, j], every law still holds and the IC is a lookahead. The contract above is what the caller has to get right.

The checker doesn't run F32 arithmetic, so no law states a value: the IC of one date, a z-score, an EWMA, a t-stat. `check.py` tests those against scipy, pandas and statsmodels instead.

The rank laws assume one thing the checker can't see: that F32's `<=` is a total order on the values being ranked. IEEE 754 makes it one on every value except NaN, and every rank runs after the NaN filter. Bend declares float comparison without a definition, so that step stays an assumption.

## Example

Write the signal and one-period returns from Python, one row per date. Row i of `ret` is the return from date i - 1 to date i:

```python
sig.to_numpy(dtype="<f4").tofile("sig.f32")   # T x N, NaN = missing
ret.to_numpy(dtype="<f4").tofile("ret.f32")
```

Then in Bend, pair each date's signal with the next period's return:

```bend
def report(x: Result<&1, &1, U32 & String, S.Panel>, r: Result<&1, &1, U32 & String, S.Panel>) -> String:
  match x r:
    case Done{a} Done{b}:
      show(S.forward_ic(S.zscore(S.winsorize(a, 0.01)), b, 0n))   # Pearson IC per date
    case _ _:
      "load failed"

def main() -> IO(Unit):
  do IO<Unit>:
    x : Result<&1, &1, U32 & String, S.Panel> <- I.Panel.load("sig.f32", 5000, 1000)
    r : Result<&1, &1, U32 & String, S.Panel> <- I.Panel.load("ret.f32", 5000, 1000)
    IO.print(report(x, r))
```

`check.bend` is a complete program along these lines, with `show` written out.

## API

| def | result |
|---|---|
| `S.Panel.from_rows(rows: List<&2, List<&2, F32>>)` | `Maybe<&2, Panel>`, `None` when two rows differ in length |
| `S.Panel.from_flat(a: A.F32Array, t: U32, n: U32)` | `Panel` from a row-major array |
| `I.Panel.load(path: String, t: U32, n: U32)` | `IO(Result<&1, &1, U32 & String, Panel>)`, fails when the file is missing or short |
| `S.forward_rank_ic(x: Panel, ret: Panel, h: Nat)` | `Maybe<&2, List<&2, F32>>`, the Spearman IC of signal row i against return row i + 1 + h, `None` when the shapes differ |
| `S.forward_ic(x: Panel, ret: Panel, h: Nat)` | the same with Pearson |
| `S.rank_ic(x: Panel, y: Panel)`, `S.ic(x: Panel, y: Panel)` | the IC of row i against row i, for panels you have aligned yourself |
| `S.lead(p: Panel, h: U32)` | `Panel` whose row i is row i + h of `p`; the last min(h, T) rows are NaN |
| `S.summary(ics: List<&2, F32>)` | `Maybe<&2, Summary>`, `None` with fewer than 2 non-NaN ICs |
| `S.nw_t(ics: List<&2, F32>, lags: Nat)` | `Maybe<&2, F32>`, the t of the mean IC with a Newey-West (Bartlett) variance, on the non-NaN ICs; `None` with fewer than 2 |
| `S.zscore(p)`, `S.demean(p)` | each date: (x - mean) / sd, or x - mean, across names |
| `S.rank(p)` | each date: percentile rank across names, in (0, 1], ties averaged, as pandas `rank(pct=True)` |
| `S.winsorize(p, q: F32)` | each date: clip to that date's q and 1 - q quantiles, linear as pandas `quantile` |
| `S.ewma(p, a: F32)` | per name: s_i = a x_i + (1 - a) s_(i-1); NaN carries the last value, as pandas `ewm(alpha=a, adjust=False, ignore_na=True)` |
| `S.rolling_mean(p, w: Nat)` | per name: mean of the last w dates, skipping NaN, as pandas `rolling(w, min_periods=1)` |

`Summary{mean, sd, ir, t, hit, count}` covers the non-NaN dates. `sd` is the sample sd, `ir` is `mean / sd` per period, `t` is `ir * sqrt(count)`, and `hit` is the share of dates with a positive IC. That t assumes independent dates. With forward returns over h periods the ICs overlap, so use `nw_t(ics, lags)` with lags of at least h. It matches statsmodels' HAC t with `use_correction=False`.

The transforms keep NaN as NaN. A date with fewer than 2 names, or a constant row, z-scores to NaN.

Each IC uses only the names present in both panels. A date with fewer than 3 such names, or with a constant row, gets a NaN IC, as scipy gives. Ties get the average rank, which is scipy's `rankdata` default.

A `Panel` is `Data`, so one loaded panel can go to any of these as often as you like.

## Limits

- The IC step and the row-wise transforms run in parallel over dates, 64 tasks once T reaches 64 and 2 below that. `ewma` and `rolling_mean` run on one core, since each date depends on the last. One date's sort runs on one core.
- A rank IC sorts the pairs twice with a merge sort over lists. `rank` looks each value up in a search tree, built by inserting the values in an interleaved order. Sorted and random rows build a balanced tree; a row ordered adversarially to the interleave could build a deep one. Both are slower than the unproved heapsort they replaced, see the table below.
- A row is a linked list, about 28 bytes per value. Two 5000 × 1000 panels take 280 MB resident.
- Sums within a date are plain running sums in F32. ICs match scipy's float64 to about 2e-7 at N=400. Thousands of names should be fine, but past that the sums should switch to pairwise addition.
- `Panel.load` reads the file in one call, so T × N must stay under 2^30 floats (4 GiB).
- `rolling_mean` re-sums its window on each date, O(w) per value.

## Checks

```sh
python3 signal/check.py    # needs bend, numpy, scipy
cd signal && bend PROOF.bend --verdict    # needs Lean 4.34.0 on PATH; about 1 s once the kernel is built
```

`check.py` builds `check.bend` and compares every per-date IC and the summary with scipy. It covers continuous data, heavy ties, 15% NaN on each side, all-missing, 2-name, 3-name and constant dates, a single date, a 300 × 400 panel that takes the parallel path, forward ICs at horizons 1, 5 and past the end, and a shape mismatch. It compares `nw_t` at lags 0, 1 and 5 with statsmodels, and all six transforms with pandas on a panel with ties, 20% NaN, a dead name, a dead date and a date with 2 names. The tolerance is 2e-5. Breaking tie averaging on purpose fails two cases with errors near 0.06.

`ranks_proof.bend` proves the tree, about 600 lines: counts over lists and over the interleave, counts over a tree, the search-tree invariant, and the walk. `sort_proof.bend` proves the rank IC's two sorts, about 600 lines: the merge sort keeps every sum over its list and returns it sorted, the walk over runs of equal keys gives each value its average rank, and the two passes compose.

`--verdict` checks the proofs twice, the second time with BendTT's kernel, which has its own proof in Lean. Broken laws and broken code were tried and rejected:
- `lead_row` claiming row k + i + 1.
- `ic_row` pairing row i of x with row i + 1 of y.
- `forward_row` claiming return row i + h, which is same-day for h = 0.
- `zscore_row` claiming row i comes from row i + 1.
- `date_ic_missing_y` claimed for a return that is present.
- `pmap_seq` claiming the parallel map drops an element.
- `rank_count` claiming 1 + 2 x #{x < q}, which ignores ties.
- tree insertion dropping a tied value instead of counting it.
- the `<=` walk comparing the wrong way round.
- `rank_pairs` ranking y among the xs.
- the merge dropping a value, or comparing the wrong way round.
- the last run of equal keys ranked as if it had one value.
- the run test comparing the wrong way round, so a smaller key joins the run.
- `both`, the filter's test, changed to check only the return, which lets a NaN signal into the IC.

On 5000 × 1000 panels, 8 cores, including loading two panels:

| pipeline | Bend | pandas, without loading |
|---|---:|---:|
| `rank_ic` and `ic` (check.bend) | 0.85 s | 0.66 s for the rank IC alone |
| winsorize, zscore, `forward_ic` | 0.30 s | 1.12 s |
| ewma, rank, `forward_rank_ic` | 1.45 s | 0.98 s |

Before the rank proofs, ranking used an in-place heapsort: 0.36 s and 0.55 s for the first and last rows. Ranking by the tree alone took 1.33 s and 1.73 s. List code does about 10 times the work of the array heapsort on one thread as on eight, so lists, not parallelism, set the remaining gap.

Each gives the same mean IC as pandas.
