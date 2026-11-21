# signal

Per-date information coefficients for a cross-sectional signal: Spearman rank IC, Pearson IC, and their mean, sd, IR, t-stat and hit rate. A panel is T dates by N names in float32, with NaN for a missing value. [DESIGN.md](DESIGN.md) explains the choices, and [bench/](bench/README.md) has the numbers behind them.

```bend
import ./signal/signal.bend as S
import ./signal/io.bend as I
```

It imports `bend-kit-f32array@0.2.1.0`. Rows are that package's `F32Array`.

## Example

Write the signal and the forward returns from Python, one row per date, aligned so that row i of `fwd` is the return over the period after date i:

```python
sig.to_numpy(dtype="<f4").tofile("sig.f32")   # T x N, NaN = missing
fwd.to_numpy(dtype="<f4").tofile("fwd.f32")
```

Then in Bend:

```bend
def report(x: Result<&1, &1, U32 & String, S.Panel>, y: Result<&1, &1, U32 & String, S.Panel>) -> String:
  match x y:
    case Done{a} Done{b}:
      show(S.rank_ic(a, b))   # Maybe<&2, List<&2, F32>>, one IC per date
    case _ _:
      "load failed"

def main() -> IO(Unit):
  do IO<Unit>:
    x : Result<&1, &1, U32 & String, S.Panel> <- I.Panel.load("sig.f32", 5000, 1000)
    y : Result<&1, &1, U32 & String, S.Panel> <- I.Panel.load("fwd.f32", 5000, 1000)
    IO.print(report(x, y))
```

`check.bend` is a complete program along these lines, with `show` written out.

## API

| def | result |
|---|---|
| `S.Panel.from_rows(rows: List<&1, A.F32Array>)` | `Maybe<&1, Panel>`, `None` when two rows differ in length |
| `S.Panel.from_flat(a: A.F32Array, t: U32, n: U32)` | `Panel` from a row-major array |
| `I.Panel.load(path: String, t: U32, n: U32)` | `IO(Result<&1, &1, U32 & String, Panel>)`, fails when the file is missing or short |
| `S.rank_ic(x: Panel, y: Panel)` | `Maybe<&2, List<&2, F32>>`, the Spearman IC of each date, `None` when the shapes differ |
| `S.ic(x: Panel, y: Panel)` | the same with Pearson |
| `S.summary(ics: List<&2, F32>)` | `Maybe<&2, Summary>`, `None` with fewer than 2 non-NaN ICs |

`Summary{mean, sd, ir, t, hit, count}` covers the non-NaN dates. `sd` is the sample sd, `ir` is `mean / sd` per period, `t` is `ir * sqrt(count)`, and `hit` is the share of dates with a positive IC.

Each date uses only the names present in both panels. A date with fewer than 3 such names, or with a constant row, gets a NaN IC, as scipy gives. Ties get the average rank, which is scipy's `rankdata` default.

`rank_ic` and `ic` consume both panels. To run both on the same data, load it twice.

## Limits

- Dates run in parallel, 64 tasks once T reaches 64 and 2 below that. One date's sort runs on one core.
- Sums within a date are plain running sums in F32. ICs match scipy's float64 to about 2e-7 at N=400. Thousands of names should be fine, but past that the sums should switch to pairwise addition.
- `Panel.load` reads the file in one call, so T × N must stay under 2^30 floats (4 GiB).
- The ICs are not Newey-West adjusted. `summary`'s t assumes independent dates, which overstates it for overlapping forward returns.

## Checks

```sh
python3 signal/check.py    # needs bend, numpy, scipy
cd signal && bend PROOF.bend
```

`check.py` builds `check.bend` and compares every per-date IC and the summary with scipy. It covers continuous data, heavy ties, 15% NaN on each side, all-missing, 2-name, 3-name and constant dates, a single date, a 300 × 400 panel that takes the parallel path, and a shape mismatch. The tolerance is 2e-5. Breaking tie averaging on purpose fails two cases with errors near 0.06.

`PROOF.bend` proves the laws in `LAWS.bend`: `from_rows` gives `None` for ragged rows, and the scratch array always holds at least two slots per name. The checker doesn't run F32 arithmetic, so no law covers an IC value.

On a 5000 × 1000 panel, `out/check` loads four panels and computes both IC series in 0.30 s on 8 cores, 1.16 s on one. pandas `rank().corrwith()` takes 0.66 s for the rank IC alone.
