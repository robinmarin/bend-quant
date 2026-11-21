# signal

Per-date information coefficients for a cross-sectional signal: Spearman rank IC, Pearson IC, and their mean, sd, IR, t-stat and hit rate. A panel is T dates by N names in float32, with NaN for a missing value. [DESIGN.md](DESIGN.md) explains the choices, and [bench/](bench/README.md) has the numbers behind them.

```bend
import ./signal/signal.bend as S
import ./signal/io.bend as I
```

A row is a `List<&2, F32>`. `io.bend` imports `bend-kit-f32array@0.2.1.0` to read files.

## What is proved and what is tested

`LAWS.bend` states these for every input, and `PROOF.bend` proves them:

- `rank_ic_rows` and `ic_row`: when the two panels have the same shape, `rank_ic` returns one IC per date, and IC i is the IC of row i of x against row i of y. Nothing is dropped, reordered or shifted.
- `ics_seq`: the parallel fork-join over dates gives the same list as the sequential loop, for every T.
- `lead_row` and `lead_panel`: row i of `lead(p, h)` is row i + h of `p`, whenever that row exists.

Together they say that `rank_ic(x, lead(r, h))` pairs the signal on date i with the returns h rows later, and with nothing else. Pair a signal with same-day returns and the result is still one IC per date, so no law can catch that mistake. What the laws rule out is code that silently pairs the wrong rows.

The checker doesn't run F32 arithmetic, so the IC of one date has no law. `check.py` tests those values against scipy instead.

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
      show(S.rank_ic(a, S.lead(b, 1)))   # Maybe<&2, List<&2, F32>>, one IC per date
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
| `S.lead(p: Panel, h: U32)` | `Panel` whose row i is row i + h of `p`; the last min(h, T) rows are NaN |
| `S.rank_ic(x: Panel, y: Panel)` | `Maybe<&2, List<&2, F32>>`, the Spearman IC of each date, `None` when the shapes differ |
| `S.ic(x: Panel, y: Panel)` | the same with Pearson |
| `S.summary(ics: List<&2, F32>)` | `Maybe<&2, Summary>`, `None` with fewer than 2 non-NaN ICs |

`Summary{mean, sd, ir, t, hit, count}` covers the non-NaN dates. `sd` is the sample sd, `ir` is `mean / sd` per period, `t` is `ir * sqrt(count)`, and `hit` is the share of dates with a positive IC.

Each date uses only the names present in both panels. A date with fewer than 3 such names, or with a constant row, gets a NaN IC, as scipy gives. Ties get the average rank, which is scipy's `rankdata` default.

A `Panel` is `Data`, so one loaded panel can go to `rank_ic`, `ic` and `lead` as often as you like.

## Limits

- Dates run in parallel, 64 tasks once T reaches 64 and 2 below that. One date's sort runs on one core.
- A row is a linked list, about 28 bytes per value. Two 5000 × 1000 panels take 280 MB resident.
- Sums within a date are plain running sums in F32. ICs match scipy's float64 to about 2e-7 at N=400. Thousands of names should be fine, but past that the sums should switch to pairwise addition.
- `Panel.load` reads the file in one call, so T × N must stay under 2^30 floats (4 GiB).
- The ICs are not Newey-West adjusted. `summary`'s t assumes independent dates, which overstates it for overlapping forward returns.

## Checks

```sh
python3 signal/check.py    # needs bend, numpy, scipy
cd signal && bend PROOF.bend --verdict    # needs Lean 4.34.0 on PATH
```

`check.py` builds `check.bend` and compares every per-date IC and the summary with scipy. It covers continuous data, heavy ties, 15% NaN on each side, all-missing, 2-name, 3-name and constant dates, a single date, a 300 × 400 panel that takes the parallel path, leads of 1, 5 and past the end, and a shape mismatch. The tolerance is 2e-5. Breaking tie averaging on purpose fails two cases with errors near 0.06.

`--verdict` checks the proofs twice, the second time with BendTT's kernel, which has its own proof in Lean. Two broken laws were tried and rejected: `lead_row` claiming row k + i + 1, and `ic_row` pairing row i of x with row i + 1 of y.

On a 5000 × 1000 panel, `out/check` loads two panels and computes both IC series in 0.32 s on 8 cores, 1.22 s on one. pandas `rank().corrwith()` takes 0.66 s for the rank IC alone.
