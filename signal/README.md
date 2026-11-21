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
- `ics_seq`: the parallel fork-join over dates gives the same list as the sequential loop, for every T.
- `lead_row` and `lead_panel`: row i of `lead(p, h)` is row i + h of `p`, whenever that row exists.
- `scan_causal` and `rowwise_causal`: for every transform built on `scan` or `rowwise`, the first k output rows depend only on the first k input rows. `ewma_causal` and `rolling_mean_causal` are the instances.
- `zscore_row`, `demean_row`, `rank_row`, `winsorize_row`: row i of the output is computed from row i of the input alone.

A signal built only from these transforms and evaluated with `forward_rank_ic` can't see the future anywhere in this library. A full-sample z-score or a centered window can't be written as a `scan`, so it can't claim these laws.

One trust boundary remains: the meaning of the input files. If row j of `ret` holds the return over (j, j + 1] instead of (j - 1, j], every law still holds and the IC is a lookahead. The contract above is what the caller has to get right.

The checker doesn't run F32 arithmetic, so no law states a value: the IC of one date, a z-score, an EWMA. `check.py` tests those against scipy and pandas instead.

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
| `S.zscore(p)`, `S.demean(p)` | each date: (x - mean) / sd, or x - mean, across names |
| `S.rank(p)` | each date: percentile rank across names, in (0, 1], ties averaged, as pandas `rank(pct=True)` |
| `S.winsorize(p, q: F32)` | each date: clip to that date's q and 1 - q quantiles, linear as pandas `quantile` |
| `S.ewma(p, a: F32)` | per name: s_i = a x_i + (1 - a) s_(i-1); NaN carries the last value, as pandas `ewm(alpha=a, adjust=False, ignore_na=True)` |
| `S.rolling_mean(p, w: Nat)` | per name: mean of the last w dates, skipping NaN, as pandas `rolling(w, min_periods=1)` |

`Summary{mean, sd, ir, t, hit, count}` covers the non-NaN dates. `sd` is the sample sd, `ir` is `mean / sd` per period, `t` is `ir * sqrt(count)`, and `hit` is the share of dates with a positive IC.

The transforms keep NaN as NaN. A date with fewer than 2 names, or a constant row, z-scores to NaN.

Each IC uses only the names present in both panels. A date with fewer than 3 such names, or with a constant row, gets a NaN IC, as scipy gives. Ties get the average rank, which is scipy's `rankdata` default.

A `Panel` is `Data`, so one loaded panel can go to any of these as often as you like.

## Limits

- Dates run in parallel, 64 tasks once T reaches 64 and 2 below that. One date's sort runs on one core.
- A row is a linked list, about 28 bytes per value. Two 5000 × 1000 panels take 280 MB resident.
- Sums within a date are plain running sums in F32. ICs match scipy's float64 to about 2e-7 at N=400. Thousands of names should be fine, but past that the sums should switch to pairwise addition.
- `Panel.load` reads the file in one call, so T × N must stay under 2^30 floats (4 GiB).
- `rolling_mean` re-sums its window on each date, O(w) per value.
- The transforms run on one core; only the IC step forks over dates. On 5000 × 1000 panels, loading two panels, then winsorize, zscore and `forward_ic`, takes 0.77 s on 8 cores. pandas takes 1.12 s for the same steps without loading. ewma, rank and `forward_rank_ic` takes 1.06 s against pandas' 0.98 s. Both pipelines give the same mean IC as pandas.
- The ICs are not Newey-West adjusted. `summary`'s t assumes independent dates, which overstates it for overlapping forward returns.

## Checks

```sh
python3 signal/check.py    # needs bend, numpy, scipy
cd signal && bend PROOF.bend --verdict    # needs Lean 4.34.0 on PATH
```

`check.py` builds `check.bend` and compares every per-date IC and the summary with scipy. It covers continuous data, heavy ties, 15% NaN on each side, all-missing, 2-name, 3-name and constant dates, a single date, a 300 × 400 panel that takes the parallel path, forward ICs at horizons 1, 5 and past the end, and a shape mismatch. It also compares all six transforms with pandas on a panel with ties, 20% NaN, a dead name, a dead date and a date with 2 names. The tolerance is 2e-5. Breaking tie averaging on purpose fails two cases with errors near 0.06.

`--verdict` checks the proofs twice, the second time with BendTT's kernel, which has its own proof in Lean. Four broken laws were tried and rejected: `lead_row` claiming row k + i + 1, `ic_row` pairing row i of x with row i + 1 of y, `forward_row` claiming return row i + h, which is same-day for h = 0, and `zscore_row` claiming row i comes from row i + 1.

On a 5000 × 1000 panel, `out/check` loads two panels and computes both IC series in 0.32 s on 8 cores, 1.22 s on one. pandas `rank().corrwith()` takes 0.66 s for the rank IC alone.
