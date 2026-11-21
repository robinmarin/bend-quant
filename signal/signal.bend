# signal: cross-sectional signal evaluation over a T x N panel. See DESIGN.md.
import Base
import bend-kit-f32array@0.2.1.0/f32array.bend as A

# Rows are dates, oldest first; column j is the same name on every date. NaN = missing.
type Panel is Type:
  Panel{t: U32, n: U32, rows: List<&1, A.F32Array>}

# IC statistics over the non-NaN dates. ir is per period; t = ir * sqrt(count).
type Summary is Data:
  Summary{mean: F32, sd: F32, ir: F32, t: F32, hit: F32, count: U32}

def nan() -> F32:
  (0.0 / 0.0 : F32)

def is_nan(+x: F32) -> Bool:
  F32.is_ne(x, x)

# ---------------------------------------------------------------- building a panel
# Bend rejects a destructure of a computed pair and any call cycle, so each loop
# below keeps its state in one record and calls a non-recursive `.add` helper.

type Rows is Type:
  Rows{n: U32, t: U32, rows: List<&1, A.F32Array>, ok: Bool}

def Panel.rows.add(r: A.F32Array & U32, st: Rows) -> Rows:
  (a, +m) = r
  Rows{+n, t, rows, ok} = st
  Rows{n, (t + 1 : U32), a <> rows, Bool.and(ok, U32.is_eq(m, n))}

def Panel.rows.go(xs: List<&1, A.F32Array>, st: Rows) -> Rows:
  match xs:
    case Nil{}:
      st
    case Con{h, rest}:
      Panel.rows.go(rest, Panel.rows.add(A.length(h), st))

def Panel.rows.pick(ok: Bool, +t: U32, +n: U32, rows: List<&1, A.F32Array>) -> Maybe<&1, Panel>:
  match ok:
    case True{}:
      Some{Panel{t, n, List.reverse(&1, A.F32Array, rows)}}
    case False{}:
      None{}

def Panel.rows.fin(st: Rows) -> Maybe<&1, Panel>:
  Rows{n, t, rows, ok} = st
  Panel.rows.pick(ok, t, n, rows)

def Panel.from_rows.first(r: A.F32Array & U32, rest: List<&1, A.F32Array>) -> Maybe<&1, Panel>:
  (a, +n) = r
  Panel.rows.fin(Panel.rows.go(rest, Rows{n, 1, a <> Nil{}, True{}}))

# None when two rows differ in length.
def Panel.from_rows(xs: List<&1, A.F32Array>) -> Maybe<&1, Panel>:
  match xs:
    case Nil{}:
      Some{Panel{0, 0, Nil{}}}
    case Con{h, rest}:
      Panel.from_rows.first(A.length(h), rest)

type Flat is Type:
  Flat{a: A.F32Array, rows: List<&1, A.F32Array>}

def Panel.flat.add(r: A.F32Array & A.F32Array, rows: List<&1, A.F32Array>) -> Flat:
  (a, row) = r
  Flat{a, row <> rows}

def Panel.flat.go(k: Nat, st: Flat, +n: U32, +i: U32) -> List<&1, A.F32Array>:
  match k:
    case 0n:
      Flat{_, rows} = st
      List.reverse(&1, A.F32Array, rows)
    case 1n+p:
      Flat{a, rows} = st
      Panel.flat.go(p, Panel.flat.add(A.slice(a, (i * n : U32), n), rows), n, (i + 1 : U32))

# A row-major t x n array, as numpy's tofile writes it.
def Panel.from_flat(a: A.F32Array, +t: U32, +n: U32) -> Panel:
  Panel{t, n, Panel.flat.go(U32.to_nat(t), Flat{a, Nil{}}, n, 0)}

# ---------------------------------------------------------------- one date
# The complete (x, y) pairs of a date go into a scratch Array<F32>, interleaved:
# slot 2k is the key, 2k+1 the payload. Sorting packed F32Array cells would cost
# a lane pick per access; the copy is O(n) against the sort's O(n log n).

type Fill is Type:
  Fill{x: A.F32Array, y: A.F32Array, buf: Array<F32>, m: U32}

def fill.ok(bad: Bool, x: A.F32Array, y: A.F32Array, buf: Array<F32>, +m: U32, +xv: F32, +yv: F32) -> Fill:
  match bad:
    case True{}:
      Fill{x, y, buf, m}
    case False{}:
      Fill{x, y, Array.set(F32, Array.set(F32, buf, (2 * m : U32), xv), ((2 * m) + 1 : U32), yv), (m + 1 : U32)}

def fill.put(xm: Maybe<&2, F32>, ym: Maybe<&2, F32>, x: A.F32Array, y: A.F32Array, buf: Array<F32>, +m: U32) -> Fill:
  match xm ym:
    case Some{+xv} Some{+yv}:
      fill.ok(Bool.or(is_nan(xv), is_nan(yv)), x, y, buf, m, xv, yv)
    case Some{_} None{}:
      Fill{x, y, buf, m}
    case None{} Some{_}:
      Fill{x, y, buf, m}
    case None{} None{}:
      Fill{x, y, buf, m}

def fill.y(r: A.F32Array & Maybe<&2, F32>, x: A.F32Array, buf: Array<F32>, +m: U32, xm: Maybe<&2, F32>) -> Fill:
  (y, ym) = r
  fill.put(xm, ym, x, y, buf, m)

def fill.x(r: A.F32Array & Maybe<&2, F32>, y: A.F32Array, buf: Array<F32>, +m: U32, +i: U32) -> Fill:
  (x, xm) = r
  fill.y(A.get(y, i), x, buf, m, xm)

def fill.add(st: Fill, +i: U32) -> Fill:
  Fill{x, y, buf, m} = st
  fill.x(A.get(x, i), y, buf, m, i)

def fill.go(k: Nat, st: Fill, +i: U32) -> Fill:
  match k:
    case 0n:
      st
    case 1n+p:
      fill.go(p, fill.add(st, i), (i + 1 : U32))

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
  Fill{_, _, buf, +m} = st
  date.m(U32.is_lt(m, 3), buf, m, rank)

# NaN when fewer than 3 names are present in both rows
def date_ic(x: A.F32Array, y: A.F32Array, +n: U32, +rank: Bool) -> F32:
  date.fin(fill.go(U32.to_nat(n), Fill{x, y, Array.new(F32, depth(n), 0.0), 0}, 0), rank)

# ---------------------------------------------------------------- over dates

type XY is Type:
  XY{x: A.F32Array, y: A.F32Array}

def zip(xs: List<&1, A.F32Array>, ys: List<&1, A.F32Array>, acc: List<&1, XY>) -> List<&1, XY>:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      zip(xt, yt, XY{x, y} <> acc)
    case Con{_, _} Nil{}:
      List.reverse(&1, XY, acc)
    case Nil{} _:
      List.reverse(&1, XY, acc)

def ics(ps: List<&1, XY>, +n: U32, +rank: Bool, acc: List<&2, F32>) -> List<&2, F32>:
  match ps:
    case Nil{}:
      List.reverse(&2, F32, acc)
    case Con{p, t}:
      XY{x, y} = p
      ics(t, n, rank, date_ic(x, y, n, rank) <> acc)

type Two is Type:
  Two{l: List<&1, XY>, r: List<&1, XY>}

def split(k: Nat, xs: List<&1, XY>, acc: List<&1, XY>) -> Two:
  match k:
    case 0n:
      Two{List.reverse(&1, XY, acc), xs}
    case 1n+p:
      match xs:
        case Nil{}:
          Two{List.reverse(&1, XY, acc), Nil{}}
        case Con{h, t}:
          split(p, t, h <> acc)

# fork-join over dates: 2^(d+1) balanced tasks, results kept in date order
def ics.par(+d: Nat, two: Two, +h: U32, +r: U32, +n: U32, +rank: Bool) -> List<&2, F32>:
  match d:
    case 0n:
      Two{xl, xr} = two
      a b = ics(xl, n, rank, Nil{}) ics(xr, n, rank, Nil{})
      List.append(&2, F32, a, b)
    case 1n+e:
      Two{xl, xr} = two
      +hl = (h >> 1n : U32)
      +hr = (r >> 1n : U32)
      a b = ics.par(e, split(U32.to_nat(hl), xl, Nil{}), hl, (h - hl : U32), n, rank) ics.par(e, split(U32.to_nat(hr), xr, Nil{}), hr, (r - hr : U32), n, rank)
      List.append(&2, F32, a, b)

# ponytail: fixed 64 tasks once t >= 64, 2 below; tune per machine if it matters
def ics.top(ps: List<&1, XY>, +t: U32, +n: U32, +rank: Bool) -> List<&2, F32>:
  +h = (t >> 1n : U32)
  ics.par(Bool.pick(Nat, U32.is_lt(t, 64), 0n, 5n), split(U32.to_nat(h), ps, Nil{}), h, (t - h : U32), n, rank)

def ic.chk(ok: Bool, rx: List<&1, A.F32Array>, ry: List<&1, A.F32Array>, +t: U32, +n: U32, +rank: Bool) -> Maybe<&2, List<&2, F32>>:
  match ok:
    case True{}:
      Some{ics.top(zip(rx, ry, Nil{}), t, n, rank)}
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
