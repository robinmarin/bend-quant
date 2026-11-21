# Rank IC benchmark

This times one rank IC pass over a panel of T dates and N names, and compares Bend with numpy and plain C. Its results set the number type and panel layout of `signal`, see [../DESIGN.md](../DESIGN.md).

## Run

```sh
./run.sh            # T=5000 N=1000
./run.sh 300 200    # deep-trend weekly size
```

You need `bend` 2.0.40, `clang`, and `python3` with numpy. Binaries go to `out/`, which git ignores. `run.sh` builds once and times one run of each, so expect a few percent of noise.

## The work

Every program builds the same panel from a U32 LCG. Per date, x and e are uniform on (-0.5, 0.5) and y = 0.1 x + e. The rank IC per date sorts the (x, y) pairs by x, replaces x with its position, sorts by y, and replaces y with its position. The Pearson correlation of the two positions is the Spearman IC, and no unsort is needed. Ranks are ordinal, so ties are not averaged. The output is the mean, sd, and t of the T ICs.

| file | what it is |
|---|---|
| `list_f32.bend` | `List.sort` (merge sort over cons cells), native `F32` |
| `list_f64.bend` | the same, on `bend-kit-f64` soft-float |
| `list_f32_par.bend`, `list_f64_par.bend` | the same, split into 64 tasks over dates with `take` and `drop` |
| `array_f32.bend` | in-place heapsort on one `Array<F32>` per date, key and payload interleaved; `D` sets 2^(D+1) tasks |
| `array_f32.c` | the heapsort of `array_f32.bend`, line for line, in C |
| `ref.py` | numpy: `argsort().argsort()` ranks, then Pearson; `64` as the third argument builds the panel in float64 |
| `access.bend` | 5000 get-and-set passes over a 1024-slot `Array<F32>`, against the same passes over a list |

`ref.py` runs four argsorts per date where the others run two sorts. It's the code you would write in numpy, not the same algorithm.

## Results

Apple M-series, 8 cores, macOS, 2026-11-21. Bend 2.0.40, clang `-O2`. T=5000, N=1000, times in ms. "1t" runs with `+RTS --threads 1`, "8t" uses every core.

| program | ms |
|---|---:|
| numpy f32 | 745 |
| numpy f64 | 751 |
| C heapsort | 571 |
| Bend list f32, 1t | 969 |
| Bend array f32, 1t | 968 |
| Bend list f64, 1t | 3033 |
| Bend list f32, 8t | 317 |
| Bend list f64, 8t | 527 |
| Bend array f32, 8t | 161 |

The list rows time IC alone; the array and C rows include building the panel, about 50 ms. All of them print the same mean IC to six digits. `F64` matches numpy float64 in every printed digit. `F32` drifts in the 7th, 0.0974750 against 0.0974755.

`access` does 5M array get-and-set pairs in 2 ms and 5M list steps in 13 ms. Base declares `Array` as a tree, but the compiler lowers it to a flat buffer.

## What it says

Single-threaded Bend takes 1.7 times as long as the same heapsort in C. Arrays and lists tie on one thread because the sort dominates. Arrays split across cores with nothing shared, so at 8 threads they run in half the time of lists and beat numpy by 4.6 times.

Soft-float `F64` costs about 0.3 µs per operation, roughly 100 times a hardware op. Building the panel takes 8.4 s in `F64` and 54 ms in `F32`. Rank IC hides this because most of its work is comparisons, but z-scores, EWMAs and PnL won't.
