# signal: cross-sectional signal evaluation over a T x N panel. See DESIGN.md.
import Base
import bend-kit-f32array@0.2.1.0/f32array.bend as A

# Rows are dates, oldest first; column j is the same name on every date. NaN = missing.
type Panel is Data:
  Panel{t: U32, n: U32, rows: List<&2, List<&2, F32>>}

# IC statistics over the non-NaN dates. ir is per period; t = ir * sqrt(count).
type Summary is Data:
  Summary{mean: F32, sd: F32, ir: F32, t: F32, hit: F32, count: U32}

def nan() -> F32:
  (0.0 / 0.0 : F32)

def is_nan(+x: F32) -> Bool:
  F32.is_ne(x, x)

# ---------------------------------------------------------------- building a panel

def Panel.rows.ok(xs: List<&2, List<&2, F32>>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{r, t}:
      Bool.and(Nat.is_eq(List.length(&2, F32, r), n), Panel.rows.ok(t, n))

def Panel.rows.pick(ok: Bool, +rows: List<&2, List<&2, F32>>, +n: Nat) -> Maybe<&2, Panel>:
  match ok:
    case True{}:
      Some{Panel{U32.from_nat(List.length(&2, List<&2, F32>, rows)), U32.from_nat(n), rows}}
    case False{}:
      None{}

# None when two rows differ in length.
def Panel.from_rows(xs: List<&2, List<&2, F32>>) -> Maybe<&2, Panel>:
  match xs:
    case Nil{}:
      Some{Panel{0, 0, Nil{}}}
    case Con{+r, +t}:
      +n = List.length(&2, F32, r)
      Panel.rows.pick(Panel.rows.ok(r <> t, n), r <> t, n)

type Flat is Type:
  Flat{a: A.F32Array, rows: List<&2, List<&2, F32>>}

def Panel.flat.add(r: A.F32Array & A.F32Array, rows: List<&2, List<&2, F32>>) -> Flat:
  (a, row) = r
  Flat{a, A.to_list(row) <> rows}

def Panel.flat.go(k: Nat, st: Flat, +n: U32, +i: U32) -> List<&2, List<&2, F32>>:
  match k:
    case 0n:
      Flat{_, rows} = st
      List.reverse(&2, List<&2, F32>, rows)
    case 1n+p:
      Flat{a, rows} = st
      Panel.flat.go(p, Panel.flat.add(A.slice(a, (i * n : U32), n), rows), n, (i + 1 : U32))

# A row-major t x n array, as numpy's tofile writes it.
def Panel.from_flat(a: A.F32Array, +t: U32, +n: U32) -> Panel:
  Panel{t, n, Panel.flat.go(U32.to_nat(t), Flat{a, Nil{}}, n, 0)}

# ---------------------------------------------------------------- one date
# The complete (x, y) pairs of a date go into a scratch Array<F32>, interleaved:
# slot 2k is the key, 2k+1 the payload, and the heapsort below runs in place.

type Fill is Type:
  Fill{buf: Array<F32>, m: U32}

def fill.ok(bad: Bool, buf: Array<F32>, +m: U32, +xv: F32, +yv: F32) -> Fill:
  match bad:
    case True{}:
      Fill{buf, m}
    case False{}:
      Fill{Array.set(F32, Array.set(F32, buf, (2 * m : U32), xv), ((2 * m) + 1 : U32), yv), (m + 1 : U32)}

def fill.add(st: Fill, +xv: F32, +yv: F32) -> Fill:
  Fill{buf, m} = st
  fill.ok(Bool.or(is_nan(xv), is_nan(yv)), buf, m, xv, yv)

# at most k pairs, so a row longer than the panel's n can't overrun the buffer
def fill.go(k: Nat, xs: List<&2, F32>, ys: List<&2, F32>, st: Fill) -> Fill:
  match k xs ys:
    case 0n _ _:
      st
    case 1n+p Nil{} _:
      st
    case 1n+p Con{_, _} Nil{}:
      st
    case 1n+p Con{xv, xt} Con{yv, yt}:
      fill.go(p, xt, yt, fill.add(st, xv, yv))

# smallest d with 2^d >= 2n, at least 1
def depth(+n: U32) -> Nat:
  1n+U32.log2(((2 * U32.max(n, 1)) - 1 : U32))

# ---- in-place heapsort of m pairs by key

type Heap is Type:
  Heap{a: Array<F32>, i: U32, n: U32, done: Bool}

def ninf() -> F32:
  (0.0 - 3.0e38 : F32)

def sw2(p: Array<F32> & F32, x: U32) -> Array<F32>:
  (a, vy) = p
  Array.set(F32, a, x, vy)

def sw1(p: Array<F32> & F32, +x: U32, y: U32) -> Array<F32>:
  (a, vx) = p
  sw2(Array.swap(F32, a, y, vx), x)

def sw(a: Array<F32>, +x: U32, y: U32) -> Array<F32>:
  sw1(Array.get(F32, a, x), x, y)

def swp(a: Array<F32>, +i: U32, +m: U32) -> Array<F32>:
  sw(sw(a, (2 * i : U32), (2 * m : U32)), ((2 * i) + 1 : U32), ((2 * m) + 1 : U32))

def heap.swap(a: Array<F32>, +i: U32, +n: U32, +m: U32) -> Heap:
  Heap{swp(a, i, m), m, n, U32.is_eq(m, i)}

def heap.r(p: Array<F32> & F32, +ki: F32, +kl: F32, +i: U32, +n: U32, +l: U32, +r: U32) -> Heap:
  (a, kr0) = p
  +kr = Bool.pick(F32, U32.is_lt(r, n), kr0, ninf())
  +gl = (kl > ki : F32)
  +m1 = Bool.pick(U32, gl, l, i)
  +k1 = Bool.pick(F32, gl, kl, ki)
  heap.swap(a, i, n, Bool.pick(U32, (kr > k1 : F32), r, m1))

def heap.l(p: Array<F32> & F32, +ki: F32, +i: U32, +n: U32, +l: U32) -> Heap:
  (a, kl0) = p
  +r = (l + 1 : U32)
  heap.r(Array.get(F32, a, (2 * r : U32)), ki, Bool.pick(F32, U32.is_lt(l, n), kl0, ninf()), i, n, l, r)

def heap.i(p: Array<F32> & F32, +i: U32, +n: U32) -> Heap:
  (a, ki) = p
  +l = ((2 * i) + 1 : U32)
  heap.l(Array.get(F32, a, (2 * l : U32)), ki, i, n, l)

def heap.step(a: Array<F32>, +i: U32, +n: U32) -> Heap:
  heap.i(Array.get(F32, a, (2 * i : U32)), i, n)

def sift.go(fuel: Nat, s: Heap) -> Array<F32>:
  match fuel:
    case 0n:
      Heap{a, _, _, _} = s
      a
    case 1n+p:
      match s:
        case Heap{a, i, n, done}:
          match done:
            case True{}:
              a
            case False{}:
              sift.go(p, heap.step(a, i, n))

def sift(a: Array<F32>, +i: U32, +n: U32) -> Array<F32>:
  sift.go(32n, Heap{a, i, n, False{}})

def heapify(k: Nat, a: Array<F32>, +i: U32, +n: U32) -> Array<F32>:
  match k:
    case 0n:
      a
    case 1n+p:
      heapify(p, sift(a, i, n), (i - 1 : U32), n)

def sortdown(k: Nat, a: Array<F32>, +e: U32) -> Array<F32>:
  match k:
    case 0n:
      a
    case 1n+p:
      sortdown(p, sift(swp(a, 0, e), 0, e), (e - 1 : U32))

def hsort(a: Array<F32>, +m: U32) -> Array<F32>:
  +h = (m >> 1n : U32)
  sortdown(U32.to_nat((m - 1 : U32)), heapify(U32.to_nat(h), a, (h - 1 : U32), m), (m - 1 : U32))

# ---- sorted (key, payload) -> (payload, average rank of key)

type Ties is Type:
  Ties{a: Array<F32>, start: U32, key: F32}

# payload slots s..e-1 get the mean position of the run, (s + e - 1) / 2
def fill_rank(k: Nat, a: Array<F32>, +j: U32, +v: F32) -> Array<F32>:
  match k:
    case 0n:
      a
    case 1n+p:
      fill_rank(p, Array.set(F32, a, ((2 * j) + 1 : U32), v), (j + 1 : U32), v)

def close_run(a: Array<F32>, +s: U32, +e: U32) -> Array<F32>:
  fill_rank(U32.to_nat((e - s : U32)), a, s, ((((U32.to_f32(s) + U32.to_f32(e)) - 1.0) / 2.0) : F32))

def ties.move(p: Array<F32> & F32, +k: U32, +start: U32, +key: F32) -> Ties:
  (a, pk) = p
  Ties{Array.set(F32, a, (2 * k : U32), pk), start, key}

def ties.run(new: Bool, a: Array<F32>, +k: U32, +start: U32, +key: F32, +kk: F32) -> Ties:
  match new:
    case True{}:
      ties.move(Array.get(F32, close_run(a, start, k), ((2 * k) + 1 : U32)), k, k, kk)
    case False{}:
      ties.move(Array.get(F32, a, ((2 * k) + 1 : U32)), k, start, key)

def ties.key(p: Array<F32> & F32, +k: U32, +start: U32, +key: F32) -> Ties:
  (a, +kk) = p
  ties.run(F32.is_ne(kk, key), a, k, start, key, kk)

def ties.add(st: Ties, +k: U32) -> Ties:
  Ties{a, start, key} = st
  ties.key(Array.get(F32, a, (2 * k : U32)), k, start, key)

def ties.go(k: Nat, st: Ties, +i: U32, +m: U32) -> Array<F32>:
  match k:
    case 0n:
      Ties{a, start, _} = st
      close_run(a, start, m)
    case 1n+p:
      ties.go(p, ties.add(st, i), (i + 1 : U32), m)

# the NaN start key differs from every key, so position 0 opens the first run
def rank_pass(a: Array<F32>, +m: U32) -> Array<F32>:
  ties.go(U32.to_nat(m), Ties{hsort(a, m), 0, nan()}, 0, m)

# ---- two-pass Pearson over m pairs

type Acc is Type:
  Acc{a: Array<F32>, x: F32, y: F32, z: F32}

def ps.b(p: Array<F32> & F32, +va: F32, +ma: F32, +mb: F32, +saa: F32, +sbb: F32, +sab: F32) -> Acc:
  (a, vb) = p
  +da = (va - ma : F32)
  +db = (vb - mb : F32)
  Acc{a, (saa + (da * da) : F32), (sbb + (db * db) : F32), (sab + (da * db) : F32)}

def ps.a(p: Array<F32> & F32, +k: U32, +ma: F32, +mb: F32, +saa: F32, +sbb: F32, +sab: F32) -> Acc:
  (a, va) = p
  ps.b(Array.get(F32, a, ((2 * k) + 1 : U32)), va, ma, mb, saa, sbb, sab)

# ponytail: plain running sums within a date; fine to a few thousand names, pairwise if N grows
def cent(k: Nat, s: Acc, +i: U32, +ma: F32, +mb: F32) -> F32:
  match k:
    case 0n:
      Acc{_, saa, sbb, sab} = s
      (sab / F32.sqrt((saa * sbb : F32)) : F32)
    case 1n+p:
      Acc{a, saa, sbb, sab} = s
      cent(p, ps.a(Array.get(F32, a, (2 * i : U32)), i, ma, mb, saa, sbb, sab), (i + 1 : U32), ma, mb)

def sm.b(p: Array<F32> & F32, +va: F32, +sa: F32, +sb: F32) -> Acc:
  (a, vb) = p
  Acc{a, (sa + va : F32), (sb + vb : F32), 0.0}

def sm.a(p: Array<F32> & F32, +k: U32, +sa: F32, +sb: F32) -> Acc:
  (a, va) = p
  sm.b(Array.get(F32, a, ((2 * k) + 1 : U32)), va, sa, sb)

def sums(k: Nat, s: Acc, +i: U32) -> Acc:
  match k:
    case 0n:
      s
    case 1n+p:
      Acc{a, sa, sb, _} = s
      sums(p, sm.a(Array.get(F32, a, (2 * i : U32)), i, sa, sb), (i + 1 : U32))

def pearson.k(s: Acc, +m: U32) -> F32:
  Acc{a, sa, sb, _} = s
  +mf = U32.to_f32(m)
  cent(U32.to_nat(m), Acc{a, 0.0, 0.0, 0.0}, 0, (sa / mf : F32), (sb / mf : F32))

def pearson(a: Array<F32>, +m: U32) -> F32:
  pearson.k(sums(U32.to_nat(m), Acc{a, 0.0, 0.0, 0.0}, 0), m)

# ---- the IC of one date

def date.m(small: Bool, buf: Array<F32>, +m: U32, rank: Bool) -> F32:
  match small:
    case True{}:
      nan()
    case False{}:
      match rank:
        case True{}:
          pearson(rank_pass(rank_pass(buf, m), m), m)
        case False{}:
          pearson(buf, m)

def date.fin(st: Fill, +rank: Bool) -> F32:
  Fill{buf, +m} = st
  date.m(U32.is_lt(m, 3), buf, m, rank)

# NaN when fewer than 3 names are present in both rows
def date_ic(x: List<&2, F32>, y: List<&2, F32>, +n: U32, +rank: Bool) -> F32:
  date.fin(fill.go(U32.to_nat(n), x, y, Fill{Array.new(F32, depth(n), 0.0), 0}), rank)

# ---------------------------------------------------------------- over dates

# Every def from here down is written for the laws in LAWS.bend: plain structural
# recursion, so the parallel version can be proved equal to the sequential one.

type XY is Data:
  XY{x: List<&2, F32>, y: List<&2, F32>, n: U32, rank: Bool}

def date_xy(p: XY) -> F32:
  XY{x, y, n, rank} = p
  date_ic(x, y, n, rank)

# row i of xs with row i of ys, up to the shorter list
def zip(xs: List<&2, List<&2, F32>>, ys: List<&2, List<&2, F32>>, +n: U32, +rank: Bool) -> List<&2, XY>:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      XY{x, y, n, rank} <> zip(xt, yt, n, rank)
    case Con{_, _} Nil{}:
      Nil{}
    case Nil{} _:
      Nil{}

# the sequential spec: one IC per pair, in order
def seq(ps: List<&2, XY>) -> List<&2, F32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      date_xy(p) <> seq(t)

type Two is Data:
  Two{l: List<&2, XY>, r: List<&2, XY>}

def split.cons(h: XY, two: Two) -> Two:
  Two{l, r} = two
  Two{h <> l, r}

# Two{take(k, xs), drop(k, xs)} in one pass
def split(k: Nat, xs: List<&2, XY>) -> Two:
  match k xs:
    case 0n Nil{}:
      Two{Nil{}, Nil{}}
    case 0n Con{h, t}:
      Two{Nil{}, h <> t}
    case 1n+p Nil{}:
      Two{Nil{}, Nil{}}
    case 1n+p Con{h, t}:
      split.cons(h, split(p, t))

# fork-join over dates: 2^(d+1) tasks. h and r only balance the split; any
# values give the same list (law par_seq).
def par(+d: Nat, two: Two, +h: U32, +r: U32) -> List<&2, F32>:
  match d:
    case 0n:
      Two{xl, xr} = two
      a b = seq(xl) seq(xr)
      List.append(&2, F32, a, b)
    case 1n+e:
      Two{xl, xr} = two
      +hl = (h >> 1n : U32)
      +hr = (r >> 1n : U32)
      a b = par(e, split(U32.to_nat(hl), xl), hl, (h - hl : U32)) par(e, split(U32.to_nat(hr), xr), hr, (r - hr : U32))
      List.append(&2, F32, a, b)

# ponytail: fixed 64 tasks once t >= 64, 2 below; tune per machine if it matters
def ics(xs: List<&2, List<&2, F32>>, ys: List<&2, List<&2, F32>>, +t: U32, +n: U32, +rank: Bool) -> List<&2, F32>:
  +h = (t >> 1n : U32)
  par(Bool.pick(Nat, U32.is_lt(t, 64), 0n, 5n), split(U32.to_nat(h), zip(xs, ys, n, rank)), h, (t - h : U32))

def ic.chk(ok: Bool, rx: List<&2, List<&2, F32>>, ry: List<&2, List<&2, F32>>, +t: U32, +n: U32, +rank: Bool) -> Maybe<&2, List<&2, F32>>:
  match ok:
    case True{}:
      Some{ics(rx, ry, t, n, rank)}
    case False{}:
      None{}

def ic.go(x: Panel, y: Panel, +rank: Bool) -> Maybe<&2, List<&2, F32>>:
  match x y:
    case Panel{+tx, +nx, rx} Panel{ty, ny, ry}:
      ic.chk(Bool.and(U32.is_eq(tx, ty), U32.is_eq(nx, ny)), rx, ry, tx, nx, rank)

# One Spearman IC per date (average ranks for ties); None when the shapes differ.
def rank_ic(x: Panel, y: Panel) -> Maybe<&2, List<&2, F32>>:
  ic.go(x, y, True{})

# One Pearson IC per date; None when the shapes differ.
def ic(x: Panel, y: Panel) -> Maybe<&2, List<&2, F32>>:
  ic.go(x, y, False{})

# ---------------------------------------------------------------- lead

def lead.rows(xs: List<&2, List<&2, F32>>, k: Nat, pad: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  List.append(&2, List<&2, F32>, List.drop(&2, List<&2, F32>, xs, k), pad)

# Row i of the result is row i + h of p (law lead_row); the last min(h, t) rows
# are NaN. With p a panel of one-period returns, lead(p, 1) pairs date i with
# the return over the period after it.
def lead(p: Panel, +h: U32) -> Panel:
  Panel{+t, +n, rows} = p
  +k = U32.to_nat(U32.min(h, t))
  Panel{t, n, lead.rows(rows, k, List.replicate(List<&2, F32>, k, List.replicate(F32, U32.to_nat(n), nan())))}

# ---------------------------------------------------------------- summary

type Tally is Data:
  Tally{s: F32, n: U32, hits: U32}

def tally.add(skip: Bool, +x: F32, st: Tally) -> Tally:
  match skip:
    case True{}:
      st
    case False{}:
      Tally{+s, +n, +hits} = st
      Tally{(s + x : F32), (n + 1 : U32), Bool.pick(U32, (x > 0.0 : F32), (hits + 1 : U32), hits)}

def tally(xs: List<&2, F32>, st: Tally) -> Tally:
  match xs:
    case Nil{}:
      st
    case Con{+x, t}:
      tally(t, tally.add(is_nan(x), x, st))

def ss(xs: List<&2, F32>, +m: F32, +acc: F32) -> F32:
  match xs:
    case Nil{}:
      acc
    case Con{+x, t}:
      +d = (x - m : F32)
      ss(t, m, Bool.pick(F32, is_nan(x), acc, (acc + (d * d) : F32)))

def summary.of(few: Bool, +s: F32, +n: U32, +hits: U32, +xs: List<&2, F32>) -> Maybe<&2, Summary>:
  match few:
    case True{}:
      None{}
    case False{}:
      +nf = U32.to_f32(n)
      +m = (s / nf : F32)
      +sd = F32.sqrt((ss(xs, m, 0.0) / (nf - 1.0) : F32))
      +ir = (m / sd : F32)
      Some{Summary{m, sd, ir, (ir * F32.sqrt(nf) : F32), (U32.to_f32(hits) / nf : F32), n}}

def summary.k(st: Tally, +xs: List<&2, F32>) -> Maybe<&2, Summary>:
  Tally{+s, +n, +hits} = st
  summary.of(U32.is_lt(n, 2), s, n, hits, xs)

# None with fewer than 2 non-NaN ICs.
def summary(+xs: List<&2, F32>) -> Maybe<&2, Summary>:
  summary.k(tally(xs, Tally{0.0, 0, 0}), xs)
