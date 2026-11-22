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

def drop_nan(xs: List<&2, F32>) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      List.filter.put(F32, x, drop_nan(t), Bool.not(is_nan(x)))

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

type Two<-A: Data> is Data:
  Two{l: List<&2, A>, r: List<&2, A>}

# ---- ranks by counting, generic over a comparison le
# For a total order le, 2 x the average 1-based rank of q among xs is
# 1 + #{x < q} + #{x <= q} (law rank_count). A search tree that merges tied
# values into one node answers both counts in one walk.

type Tr<-A: Data> is Data:
  Leaf{}
  Node{l: Tr<A>, v: A, c: Nat, s: Nat, r: Tr<A>}

def tsize(-A: Data, t: Tr<A>) -> Nat:
  match t:
    case Leaf{}:
      0n
    case Node{_, _, _, s, _}:
      s

# where a goes relative to v: EQ when tied, LT left, GT right
def ord(~A: Data, ~le: A -> A -> Bool, +a: A, +v: A) -> Cmp:
  Bool.pick(Cmp, le(a, v), Bool.pick(Cmp, le(v, a), EQ{}, LT{}), GT{})

def root_ord(~A: Data, ~le: A -> A -> Bool, t: Tr<A>, +a: A) -> Cmp:
  match t:
    case Leaf{}:
      EQ{}
    case Node{_, v, _, _, _}:
      ord(~A, ~le, a, v)

# d is root_ord(t, a), computed by the caller: a match can't branch on a
# computed value, and a helper can't call back into ins.
def ins(~A: Data, ~le: A -> A -> Bool, t: Tr<A>, +a: A, d: Cmp) -> Tr<A>:
  match t d:
    case Leaf{} _:
      Node{Leaf{}, a, 1n, 1n, Leaf{}}
    case Node{l, v, c, s, r} EQ{}:
      Node{l, v, 1n+c, 1n+s, r}
    case Node{+l, v, c, s, r} LT{}:
      Node{ins(~A, ~le, l, a, root_ord(~A, ~le, l, a)), v, c, 1n+s, r}
    case Node{l, v, c, s, +r} GT{}:
      Node{l, v, c, 1n+s, ins(~A, ~le, r, a, root_ord(~A, ~le, r, a))}

def insert(~A: Data, ~le: A -> A -> Bool, +t: Tr<A>, +a: A) -> Tr<A>:
  ins(~A, ~le, t, a, root_ord(~A, ~le, t, a))

def build(~A: Data, ~le: A -> A -> Bool, xs: List<&2, A>, t: Tr<A>) -> Tr<A>:
  match xs:
    case Nil{}:
      t
    case Con{x, rest}:
      build(~A, ~le, rest, insert(~A, ~le, t, x))

def root_lt(~A: Data, ~le: A -> A -> Bool, t: Tr<A>, +q: A) -> Bool:
  match t:
    case Leaf{}:
      False{}
    case Node{_, v, _, _, _}:
      Bool.not(le(q, v))

def root_le(~A: Data, ~le: A -> A -> Bool, t: Tr<A>, +q: A) -> Bool:
  match t:
    case Leaf{}:
      False{}
    case Node{_, v, _, _, _}:
      le(v, q)

# #{x in t : x < q}, with x < q meaning not le(q, x); d is root_lt(t, q)
def dlt(~A: Data, ~le: A -> A -> Bool, t: Tr<A>, +q: A, d: Bool) -> Nat:
  match t d:
    case Leaf{} _:
      0n
    case Node{l, _, c, _, +r} True{}:
      Nat.add(tsize(A, l), Nat.add(c, dlt(~A, ~le, r, q, root_lt(~A, ~le, r, q))))
    case Node{+l, _, _, _, _} False{}:
      dlt(~A, ~le, l, q, root_lt(~A, ~le, l, q))

# #{x in t : x <= q}; d is root_le(t, q)
def dle(~A: Data, ~le: A -> A -> Bool, t: Tr<A>, +q: A, d: Bool) -> Nat:
  match t d:
    case Leaf{} _:
      0n
    case Node{l, _, c, _, +r} True{}:
      Nat.add(tsize(A, l), Nat.add(c, dle(~A, ~le, r, q, root_le(~A, ~le, r, q))))
    case Node{+l, _, _, _, _} False{}:
      dle(~A, ~le, l, q, root_le(~A, ~le, l, q))

# ---- insertion order: interleave halves, so sorted input still builds a
# balanced tree. Any order gives the same counts (law shuffle_count).

def deal.cons(-A: Data, +x: A, two: Two<A>) -> Two<A>:
  Two{l, r} = two
  Two{x <> r, l}

# elements 0, 2, 4, .. and 1, 3, 5, ..
def deal(-A: Data, xs: List<&2, A>) -> Two<A>:
  match xs:
    case Nil{}:
      Two{Nil{}, Nil{}}
    case Con{x, t}:
      deal.cons(A, x, deal(A, t))

# k levels of dealing, then the halves in order
# ponytail: a fixed interleave, balanced for sorted rows and random ones; a
# row ordered adversarially to it could still build a deep tree
def shf(-A: Data, +k: Nat, two: Two<A>) -> List<&2, A>:
  match k:
    case 0n:
      Two{l, r} = two
      List.append(&2, A, l, r)
    case 1n+p:
      Two{l, r} = two
      List.append(&2, A, shf(A, p, deal(A, l)), shf(A, p, deal(A, r)))

def shuffle(-A: Data, k: Nat, xs: List<&2, A>) -> List<&2, A>:
  shf(A, k, deal(A, xs))

def tree(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>) -> Tr<A>:
  build(~A, ~le, shuffle(A, U32.log2(U32.from_nat(List.length(&2, A, xs))), xs), Leaf{})

# 2 x the average 1-based rank of q among the values in t
def rank_of(~A: Data, ~le: A -> A -> Bool, +t: Tr<A>, +q: A) -> Nat:
  1n+Nat.add(dlt(~A, ~le, t, q, root_lt(~A, ~le, t, q)), dle(~A, ~le, t, q, root_le(~A, ~le, t, q)))

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

def date.m(small: Bool, buf: Array<F32>, +m: U32) -> F32:
  match small:
    case True{}:
      nan()
    case False{}:
      pearson(buf, m)

def date.fin(st: Fill) -> F32:
  Fill{buf, +m} = st
  date.m(U32.is_lt(m, 3), buf, m)

# ---- the complete pairs of a date: the only thing an IC reads (laws date_ic_*)

type Pr is Data:
  Pr{x: F32, y: F32}

# name j of xs with name j of ys, up to the shorter row
def zip2(xs: List<&2, F32>, ys: List<&2, F32>) -> List<&2, Pr>:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      Pr{x, y} <> zip2(xt, yt)
    case Con{_, _} Nil{}:
      Nil{}
    case Nil{} _:
      Nil{}

# present on both sides; y is tested first, so a NaN y decides without x
def both(p: Pr) -> Bool:
  Pr{+x, +y} = p
  Bool.and(Bool.not(is_nan(y)), Bool.not(is_nan(x)))

def complete(xs: List<&2, F32>, ys: List<&2, F32>) -> List<&2, Pr>:
  List.filter(~Pr, ~both, zip2(xs, ys))

def fill.pairs(ps: List<&2, Pr>, st: Fill) -> Fill:
  match ps:
    case Nil{}:
      st
    case Con{p, t}:
      Pr{x, y} = p
      Fill{buf, +m} = st
      fill.pairs(t, Fill{Array.set(F32, Array.set(F32, buf, (2 * m : U32), x), ((2 * m) + 1 : U32), y), (m + 1 : U32)})

def nat_f32(n: Nat) -> F32:
  U32.to_f32(U32.from_nat(n))

# ---- rank IC by two sorts
# Sort the pairs by x and replace each x with its rank, then the same for y.
# Pearson reads the pairs in any order, so nothing is unsorted. Law
# rank_pairs: the rank pairs are those of the spec, each as often.

type KV<-A: Data, -B: Data> is Data:
  KV{k: A, v: B}

def key(-A: Data, -B: Data, x: KV<A, B>) -> A:
  KV{k, _} = x
  k

def val(-A: Data, -B: Data, x: KV<A, B>) -> B:
  KV{_, v} = x
  v

def kle(~A: Data, ~B: Data, ~le: A -> A -> Bool, x: KV<A, B>, y: KV<A, B>) -> Bool:
  le(key(A, B, x), key(A, B, y))

# merge with the heads unpacked; d is kle(x, y)
def mrg(~A: Data, ~B: Data, ~le: A -> A -> Bool, xt: List<&2, KV<A, B>>, yt: List<&2, KV<A, B>>, +x: KV<A, B>, +y: KV<A, B>, d: Bool) -> List<&2, KV<A, B>>:
  match xt yt d:
    case Nil{} _ True{}:
      x <> y <> yt
    case Con{+a, at} _ True{}:
      x <> mrg(~A, ~B, ~le, at, yt, a, y, kle(~A, ~B, ~le, a, y))
    case _ Nil{} False{}:
      y <> x <> xt
    case _ Con{+b, bt} False{}:
      y <> mrg(~A, ~B, ~le, xt, bt, x, b, kle(~A, ~B, ~le, x, b))

def merge(~A: Data, ~B: Data, ~le: A -> A -> Bool, xs: List<&2, KV<A, B>>, ys: List<&2, KV<A, B>>) -> List<&2, KV<A, B>>:
  match xs ys:
    case Nil{} _:
      ys
    case Con{x, xt} Nil{}:
      x <> xt
    case Con{+x, xt} Con{+y, yt}:
      mrg(~A, ~B, ~le, xt, yt, x, y, kle(~A, ~B, ~le, x, y))

# only runs when msorted's fuel is short, which msort never lets happen
def isort(~A: Data, ~B: Data, ~le: A -> A -> Bool, xs: List<&2, KV<A, B>>) -> List<&2, KV<A, B>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      merge(~A, ~B, ~le, x <> Nil{}, isort(~A, ~B, ~le, t))

def msorted(~A: Data, ~B: Data, ~le: A -> A -> Bool, k: Nat, two: Two<KV<A, B>>) -> List<&2, KV<A, B>>:
  match k:
    case 0n:
      Two{l, r} = two
      merge(~A, ~B, ~le, isort(~A, ~B, ~le, l), isort(~A, ~B, ~le, r))
    case 1n+(+p):
      Two{l, r} = two
      merge(~A, ~B, ~le, msorted(~A, ~B, ~le, p, deal(KV<A, B>, l)), msorted(~A, ~B, ~le, p, deal(KV<A, B>, r)))

def msort(~A: Data, ~B: Data, ~le: A -> A -> Bool, +xs: List<&2, KV<A, B>>) -> List<&2, KV<A, B>>:
  msorted(~A, ~B, ~le, {1n+U32.log2(U32.from_nat(List.length(&2, KV<A, B>, xs))) : Nat}, deal(KV<A, B>, xs))

# le(key of the head of t, v); False on an empty list
def nxt(~A: Data, ~B: Data, ~le: A -> A -> Bool, t: List<&2, KV<A, B>>, +v: A) -> Bool:
  match t:
    case Nil{}:
      False{}
    case Con{x, _}:
      le(key(A, B, x), v)

def emit(-B: Data, ys: List<&2, B>, +r: Nat, acc: List<&2, KV<B, Nat>>) -> List<&2, KV<B, Nat>>:
  match ys:
    case Nil{}:
      acc
    case Con{y, t}:
      emit(B, t, r, KV{y, r} <> acc)

# a list sorted by key in; (value, 2 x the average rank of its key) out.
# The current run has key v, c values ys, and p values before it.
def runs(~A: Data, ~B: Data, ~le: A -> A -> Bool, ps: List<&2, KV<A, B>>, +v: A, +p: Nat, +c: Nat, ys: List<&2, B>, acc: List<&2, KV<B, Nat>>, d: Bool) -> List<&2, KV<B, Nat>>:
  match ps d:
    case Nil{} _:
      emit(B, ys, 1n+Nat.add(Nat.add(p, p), c), acc)
    case Con{KV{_, y}, +t} True{}:
      runs(~A, ~B, ~le, t, v, p, 1n+c, y <> ys, acc, nxt(~A, ~B, ~le, t, v))
    case Con{KV{+w, y}, +t} False{}:
      runs(~A, ~B, ~le, t, w, Nat.add(p, c), 1n, y <> Nil{}, emit(B, ys, 1n+Nat.add(Nat.add(p, p), c), acc), nxt(~A, ~B, ~le, t, w))

def rk(~A: Data, ~B: Data, ~le: A -> A -> Bool, ps: List<&2, KV<A, B>>) -> List<&2, KV<B, Nat>>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{KV{+x, y}, +t}:
      runs(~A, ~B, ~le, t, x, 0n, 1n, y <> Nil{}, Nil{}, nxt(~A, ~B, ~le, t, x))

# sort by key and rank it
def step(~A: Data, ~B: Data, ~le: A -> A -> Bool, +ps: List<&2, KV<A, B>>) -> List<&2, KV<B, Nat>>:
  rk(~A, ~B, ~le, msort(~A, ~B, ~le, ps))

# (x, y) pairs in, (2 x rank of x, 2 x rank of y) out, in some order
def rank2(~A: Data, ~le: A -> A -> Bool, +ps: List<&2, KV<A, A>>) -> List<&2, KV<Nat, Nat>>:
  step(~A, ~Nat, ~le, step(~A, ~A, ~le, ps))

def pr_kv(ps: List<&2, Pr>) -> List<&2, KV<F32, F32>>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{Pr{x, y}, t}:
      KV{x, y} <> pr_kv(t)

def kv_pr(xs: List<&2, KV<Nat, Nat>>) -> List<&2, Pr>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{KV{a, b}, t}:
      Pr{nat_f32(a), nat_f32(b)} <> kv_pr(t)

# the pairs a Pearson IC runs on: the values, or for a rank IC their ranks
# (2 x the average rank; Pearson doesn't see the scale or the order)
def prep(+ps: List<&2, Pr>, rank: Bool) -> List<&2, Pr>:
  match rank:
    case True{}:
      kv_pr(rank2(~F32, ~F32.is_le, pr_kv(ps)))
    case False{}:
      ps

# the IC of a list of complete pairs; NaN for fewer than 3
def core(+ps: List<&2, Pr>, +rank: Bool) -> F32:
  date.fin(fill.pairs(prep(ps, rank), Fill{Array.new(F32, depth(U32.from_nat(List.length(&2, Pr, ps))), 0.0), 0}))

# NaN when fewer than 3 names are present in both rows
def date_ic(x: List<&2, F32>, y: List<&2, F32>, +rank: Bool) -> F32:
  core(complete(x, y), rank)

# ---------------------------------------------------------------- over dates

# ---- a proved parallel map
# pmap forks over the elements and pseq is the plain loop; law pmap_seq says they
# give the same list. The IC step and the row-wise transforms both run on pmap.

# f(c, a) for each element a, in order
def pseq(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, xs: List<&2, A>, +c: C) -> List<&2, B>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      f(c, x) <> pseq(~A, ~B, ~C, ~f, t, c)

def split.cons(-A: Data, h: A, two: Two<A>) -> Two<A>:
  Two{l, r} = two
  Two{h <> l, r}

# Two{take(k, xs), drop(k, xs)} in one pass
def split(-A: Data, k: Nat, xs: List<&2, A>) -> Two<A>:
  match k xs:
    case 0n Nil{}:
      Two{Nil{}, Nil{}}
    case 0n Con{h, t}:
      Two{Nil{}, h <> t}
    case 1n+p Nil{}:
      Two{Nil{}, Nil{}}
    case 1n+p Con{h, t}:
      split.cons(A, h, split(A, p, t))

# fork-join: 2^(d+1) tasks. h and r only balance the split; any values give
# the same list.
def par(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, +d: Nat, two: Two<A>, +h: U32, +r: U32, +c: C) -> List<&2, B>:
  match d:
    case 0n:
      Two{xl, xr} = two
      a b = pseq(~A, ~B, ~C, ~f, xl, c) pseq(~A, ~B, ~C, ~f, xr, c)
      List.append(&2, B, a, b)
    case 1n+e:
      Two{xl, xr} = two
      +hl = (h >> 1n : U32)
      +hr = (r >> 1n : U32)
      a b = par(~A, ~B, ~C, ~f, e, split(A, U32.to_nat(hl), xl), hl, (h - hl : U32), c) par(~A, ~B, ~C, ~f, e, split(A, U32.to_nat(hr), xr), hr, (r - hr : U32), c)
      List.append(&2, B, a, b)

# t is the length of xs, used only to balance the split.
# ponytail: fixed 64 tasks once t >= 64, 2 below; tune per machine if it matters
def pmap(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, xs: List<&2, A>, +t: U32, +c: C) -> List<&2, B>:
  +h = (t >> 1n : U32)
  par(~A, ~B, ~C, ~f, Bool.pick(Nat, U32.is_lt(t, 64), 0n, 5n), split(A, U32.to_nat(h), xs), h, (t - h : U32), c)

# ---- one IC per date

type XY is Data:
  XY{x: List<&2, F32>, y: List<&2, F32>}

def date_xy(rank: Bool, p: XY) -> F32:
  XY{x, y} = p
  date_ic(x, y, rank)

# row i of xs with row i of ys, up to the shorter list
def zip(xs: List<&2, List<&2, F32>>, ys: List<&2, List<&2, F32>>) -> List<&2, XY>:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      XY{x, y} <> zip(xt, yt)
    case Con{_, _} Nil{}:
      Nil{}
    case Nil{} _:
      Nil{}

def ics(xs: List<&2, List<&2, F32>>, ys: List<&2, List<&2, F32>>, +t: U32, +rank: Bool) -> List<&2, F32>:
  pmap(~XY, ~F32, ~Bool, ~date_xy, zip(xs, ys), t, rank)

def ic.chk(ok: Bool, rx: List<&2, List<&2, F32>>, ry: List<&2, List<&2, F32>>, +t: U32, +rank: Bool) -> Maybe<&2, List<&2, F32>>:
  match ok:
    case True{}:
      Some{ics(rx, ry, t, rank)}
    case False{}:
      None{}

def ic.go(x: Panel, y: Panel, +rank: Bool) -> Maybe<&2, List<&2, F32>>:
  match x y:
    case Panel{+tx, nx, rx} Panel{ty, ny, ry}:
      ic.chk(Bool.and(U32.is_eq(tx, ty), U32.is_eq(nx, ny)), rx, ry, tx, rank)

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

# ---------------------------------------------------------------- forward IC
# The entry point for evaluating a signal. ret holds one-period returns: row j is
# the return over (j - 1, j]. h counts extra periods, so the nearest return a
# date can meet is the next one; a same-day pairing has no spelling here.

def fwd.rows(rs: List<&2, List<&2, F32>>, +h: Nat, +t: U32, +n: U32) -> List<&2, List<&2, F32>>:
  lead.rows(rs, 1n+h, List.replicate(List<&2, F32>, Nat.min(1n+h, U32.to_nat(t)), List.replicate(F32, U32.to_nat(n), nan())))

def fwd(p: Panel, +h: Nat) -> Panel:
  Panel{+t, +n, rs} = p
  Panel{t, n, fwd.rows(rs, h, t, n)}

# IC i is the rank IC of signal row i against return row i + 1 + h (law forward_row).
def forward_rank_ic(x: Panel, ret: Panel, +h: Nat) -> Maybe<&2, List<&2, F32>>:
  rank_ic(x, fwd(ret, h))

# The same with Pearson.
def forward_ic(x: Panel, ret: Panel, +h: Nat) -> Maybe<&2, List<&2, F32>>:
  ic(x, fwd(ret, h))

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

# ---------------------------------------------------------------- transforms
# Each transform is a scan over the dates or a map over the rows (pmap). LAWS.bend
# proves both shapes causal: output rows 0..k-1 depend only on input rows
# 0..k-1, so nothing built from them can look ahead.

# state S; next folds row i into it; out builds output row i from the new state and row i
def scan(~S: Data, ~next: S -> List<&2, F32> -> S, ~out: S -> List<&2, F32> -> List<&2, F32>, xs: List<&2, List<&2, F32>>, +s: S) -> List<&2, List<&2, F32>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      +s2 = next(s, x)
      out(s2, x) <> scan(~S, ~next, ~out, t, s2)

# ---- one row; NaN stays NaN

def row.affine(xs: List<&2, F32>, +a: F32, +b: F32) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      ((x - a) / b : F32) <> row.affine(t, a, b)

def row.mean.of(st: Tally) -> F32:
  Tally{s, n, _} = st
  (s / U32.to_f32(n) : F32)

def row.mean(+xs: List<&2, F32>) -> F32:
  row.mean.of(tally(xs, Tally{0.0, 0, 0}))

def row.sd.of(st: Tally, +xs: List<&2, F32>, +m: F32) -> F32:
  Tally{_, n, _} = st
  F32.sqrt((ss(xs, m, 0.0) / (U32.to_f32(n) - 1.0) : F32))

# (x - mean) / sample sd over the present names; NaN when fewer than 2 or sd = 0
def row.zscore(+xs: List<&2, F32>) -> List<&2, F32>:
  +m = row.mean(xs)
  row.affine(xs, m, row.sd.of(tally(xs, Tally{0.0, 0, 0}), xs, m))

def row.demean(+xs: List<&2, F32>) -> List<&2, F32>:
  row.affine(xs, row.mean(xs), 1.0)

# -- percentile rank: average rank / count, in (0, 1], as pandas rank(pct=True)

def pct.go(xs: List<&2, F32>, +t: Tr<F32>, +m2: F32) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, rest}:
      Bool.pick(Unit -> F32, is_nan(x), u => x, u => (nat_f32(rank_of(~F32, ~F32.is_le, t, x)) / m2 : F32))(Unit{}) <> pct.go(rest, t, m2)

def row.rank(+xs: List<&2, F32>, +n: U32) -> List<&2, F32>:
  +vs = drop_nan(xs)
  pct.go(xs, tree(~F32, ~F32.is_le, vs), (2.0 * nat_f32(List.length(&2, F32, vs)) : F32))

def fill.idx.add(st: Fill, +v: F32, +i: U32) -> Fill:
  Fill{buf, m} = st
  fill.ok(is_nan(v), buf, m, v, U32.to_f32(i))

# the present values of a row, as keys with their index as payload
def fill.idx(k: Nat, xs: List<&2, F32>, +i: U32, st: Fill) -> Fill:
  match k xs:
    case 0n _:
      st
    case 1n+p Nil{}:
      st
    case 1n+p Con{v, t}:
      fill.idx(p, t, (i + 1 : U32), fill.idx.add(st, v, i))

# -- winsorize: clip at the q and 1 - q quantiles (linear, as pandas quantile)

def q.at.b(p: Array<F32> & F32, +lo: F32, +t: F32) -> Array<F32> & F32:
  (a, hi) = p
  (a, (lo + (t * (hi - lo))) : F32)

def q.at.a(p: Array<F32> & F32, +j: U32, +t: F32) -> Array<F32> & F32:
  (a, lo) = p
  q.at.b(Array.get(F32, a, (2 * j : U32)), lo, t)

def q.at.pick(empty: Bool, a: Array<F32>, +i: U32, +j: U32, +t: F32) -> Array<F32> & F32:
  match empty:
    case True{}:
      (a, nan())
    case False{}:
      q.at.a(Array.get(F32, a, (2 * i : U32)), j, t)

# the q quantile of m sorted keys; NaN for m = 0
def q.at(a: Array<F32>, +m: U32, +q: F32) -> Array<F32> & F32:
  +h = ((U32.to_f32(m) - 1.0) * q : F32)
  +i = F32.to_u32(F32.floor(h))
  +j = U32.min((i + 1 : U32), (m - 1 : U32))
  q.at.pick(U32.is_eq(m, 0), a, i, j, (h - F32.floor(h) : F32))

def clip(xs: List<&2, F32>, +lo: F32, +hi: F32) -> List<&2, F32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Bool.pick(F32, is_nan(x), x, F32.max(lo, F32.min(x, hi))) <> clip(t, lo, hi)

def wz.hi(p: Array<F32> & F32, +xs: List<&2, F32>, +lo: F32) -> List<&2, F32>:
  (_, hi) = p
  clip(xs, lo, hi)

def wz.lo(p: Array<F32> & F32, +xs: List<&2, F32>, +m: U32, +q: F32) -> List<&2, F32>:
  (a, lo) = p
  wz.hi(q.at(a, m, (1.0 - q : F32)), xs, lo)

def wz.of(st: Fill, +xs: List<&2, F32>, +q: F32) -> List<&2, F32>:
  Fill{buf, +m} = st
  wz.lo(q.at(hsort(buf, m), m, q), xs, m, q)

def row.winsorize(+xs: List<&2, F32>, +n: U32, +q: F32) -> List<&2, F32>:
  wz.of(fill.idx(U32.to_nat(n), xs, 0, Fill{Array.new(F32, depth(n), 0.0), 0}), xs, q)

# ---- row-wise panel transforms

type Cfg is Data:
  Cfg{n: U32, q: F32}

def zscore.f(c: Cfg, x: List<&2, F32>) -> List<&2, F32>:
  row.zscore(x)

def demean.f(c: Cfg, x: List<&2, F32>) -> List<&2, F32>:
  row.demean(x)

def rank.f(c: Cfg, x: List<&2, F32>) -> List<&2, F32>:
  Cfg{n, _} = c
  row.rank(x, n)

def winsorize.f(c: Cfg, x: List<&2, F32>) -> List<&2, F32>:
  Cfg{n, q} = c
  row.winsorize(x, n, q)

# Each date: (x - mean) / sd across names.
def zscore(p: Panel) -> Panel:
  Panel{+t, +n, rows} = p
  Panel{t, n, pmap(~List<&2, F32>, ~List<&2, F32>, ~Cfg, ~zscore.f, rows, t, Cfg{n, 0.0})}

# Each date: x - mean across names.
def demean(p: Panel) -> Panel:
  Panel{+t, +n, rows} = p
  Panel{t, n, pmap(~List<&2, F32>, ~List<&2, F32>, ~Cfg, ~demean.f, rows, t, Cfg{n, 0.0})}

# Each date: percentile rank across names, in (0, 1].
def rank(p: Panel) -> Panel:
  Panel{+t, +n, rows} = p
  Panel{t, n, pmap(~List<&2, F32>, ~List<&2, F32>, ~Cfg, ~rank.f, rows, t, Cfg{n, 0.0})}

# Each date: clip to that date's q and 1 - q quantiles.
def winsorize(p: Panel, +q: F32) -> Panel:
  Panel{+t, +n, rows} = p
  Panel{t, n, pmap(~List<&2, F32>, ~List<&2, F32>, ~Cfg, ~winsorize.f, rows, t, Cfg{n, q})}

# ---- time-series panel transforms, per name across dates

type Ew is Data:
  Ew{a: F32, s: List<&2, F32>}

def ew.one(+p: F32, +v: F32, +a: F32) -> F32:
  Bool.pick(F32, is_nan(v), p, Bool.pick(F32, is_nan(p), v, ((a * v) + ((1.0 - a) * p) : F32)))

def ew.row(ps: List<&2, F32>, xs: List<&2, F32>, +a: F32) -> List<&2, F32>:
  match ps xs:
    case Con{p, pt} Con{v, vt}:
      ew.one(p, v, a) <> ew.row(pt, vt, a)
    case Con{_, _} Nil{}:
      Nil{}
    case Nil{} _:
      Nil{}

def ew.next(st: Ew, x: List<&2, F32>) -> Ew:
  Ew{+a, s} = st
  Ew{a, ew.row(s, x, a)}

def ew.out(st: Ew, x: List<&2, F32>) -> List<&2, F32>:
  Ew{_, s} = st
  s

# s_i = a x_i + (1 - a) s_(i-1) per name. A NaN carries the last value on, and
# a name is NaN until its first value, as pandas ewm(alpha=a, adjust=False, ignore_na=True).
def ewma(p: Panel, +a: F32) -> Panel:
  Panel{+t, +n, rows} = p
  Panel{t, n, scan(~Ew, ~ew.next, ~ew.out, rows, Ew{a, List.replicate(F32, U32.to_nat(n), nan())})}

type Win is Data:
  Win{w: Nat, rows: List<&2, List<&2, F32>>}

def win.next(st: Win, x: List<&2, F32>) -> Win:
  Win{+w, rows} = st
  Win{w, List.take(&2, List<&2, F32>, x <> rows, w)}

type Cols is Data:
  Cols{s: List<&2, F32>, c: List<&2, F32>}

def col.cons(+s: F32, +c: F32, r: Cols) -> Cols:
  Cols{st, ct} = r
  Cols{s <> st, c <> ct}

def col.add(ss: List<&2, F32>, cs: List<&2, F32>, xs: List<&2, F32>) -> Cols:
  match ss cs xs:
    case Con{+s, st} Con{+c, ct} Con{+x, xt}:
      col.cons(Bool.pick(F32, is_nan(x), s, (s + x : F32)), Bool.pick(F32, is_nan(x), c, (c + 1.0 : F32)), col.add(st, ct, xt))
    case _ _ _:
      Cols{Nil{}, Nil{}}

def col.sum(rows: List<&2, List<&2, F32>>, acc: Cols) -> Cols:
  match rows:
    case Nil{}:
      acc
    case Con{r, t}:
      Cols{s, c} = acc
      col.sum(t, col.add(s, c, r))

def col.div(ss: List<&2, F32>, cs: List<&2, F32>) -> List<&2, F32>:
  match ss cs:
    case Con{s, st} Con{c, ct}:
      (s / c : F32) <> col.div(st, ct)
    case _ _:
      Nil{}

def win.out.of(r: Cols) -> List<&2, F32>:
  Cols{s, c} = r
  col.div(s, c)

def win.out(st: Win, x: List<&2, F32>) -> List<&2, F32>:
  Win{_, rows} = st
  +n = List.length(&2, F32, x)
  win.out.of(col.sum(rows, Cols{List.replicate(F32, n, 0.0), List.replicate(F32, n, 0.0)}))

# Mean over the last w dates per name, skipping NaN; NaN only when all w are
# missing, as pandas rolling(w, min_periods=1).mean().
# ponytail: re-sums the window each date, O(w) per value; running sums if w gets large
def rolling_mean(p: Panel, +w: Nat) -> Panel:
  Panel{+t, +n, rows} = p
  Panel{t, n, scan(~Win, ~win.next, ~win.out, rows, Win{w, Nil{}})}

# ---------------------------------------------------------------- Newey-West t

def dot(xs: List<&2, F32>, ys: List<&2, F32>, +acc: F32) -> F32:
  match xs ys:
    case Con{a, at} Con{b, bt}:
      dot(at, bt, (acc + (a * b) : F32))
    case Con{_, _} Nil{}:
      acc
    case Nil{} _:
      acc

# 2 * sum over lags l = j..L of (1 - l / (L + 1)) * gamma_l, gamma_l = sum d_t d_(t-l) / T
def nw.sum(k: Nat, +j: Nat, +lags: Nat, +ds: List<&2, F32>, +tf: F32, +acc: F32) -> F32:
  match k:
    case 0n:
      acc
    case 1n+p:
      +w = (1.0 - (F32.from_nat(j) / F32.from_nat(1n+lags)) : F32)
      +g = (dot(List.drop(&2, F32, ds, j), ds, 0.0) / tf : F32)
      nw.sum(p, 1n+j, lags, ds, tf, (acc + ((2.0 * w) * g) : F32))

def nw.of(few: Bool, +vs: List<&2, F32>, +lags: Nat) -> Maybe<&2, F32>:
  match few:
    case True{}:
      None{}
    case False{}:
      +tf = F32.from_nat(List.length(&2, F32, vs))
      +m = row.mean(vs)
      +ds = row.affine(vs, m, 1.0)
      +s = ((dot(ds, ds, 0.0) / tf) + nw.sum(lags, 1n, lags, ds, tf, 0.0) : F32)
      Some{(m / F32.sqrt((s / tf : F32)) : F32)}

# t of the mean IC with a Newey-West (Bartlett) variance over `lags` lags, on the
# non-NaN ICs. Use it when forward returns overlap: with horizon h, lags >= h.
# lags = 0 is the plain t of summary, except the variance divides by T, not T - 1.
# None with fewer than 2 non-NaN ICs.
def nw_t(+ics: List<&2, F32>, +lags: Nat) -> Maybe<&2, F32>:
  +vs = drop_nan(ics)
  nw.of(Nat.is_lt(List.length(&2, F32, vs), 2n), vs, lags)
