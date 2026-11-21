# Laws for signal. The checker doesn't run F32 arithmetic, so IC values are
# checked against scipy in check.py. These laws cover the structure.
import Base
import ./signal.bend as S

def is_some(m: Maybe<&2, S.Panel>) -> Bool:
  match m:
    case Some{_}:
      True{}
    case None{}:
      False{}

def row(n: Nat) -> List<&2, F32>:
  List.replicate(F32, n, 1.0)

# Rows of equal length make a panel.
law from_rows_equal:
  {is_some(S.Panel.from_rows([row(3n), row(3n), row(3n)])) == True{} : Bool}

# One short row anywhere gives None.
law from_rows_ragged:
  {is_some(S.Panel.from_rows([row(3n), row(2n), row(3n)])) == False{} : Bool}

law from_rows_ragged_last:
  {is_some(S.Panel.from_rows([row(3n), row(3n), row(4n)])) == False{} : Bool}

# No rows is the empty panel, not an error.
law from_rows_empty:
  {is_some(S.Panel.from_rows(Nil{})) == True{} : Bool}

# The scratch array holds 2^depth(n) slots, two per name: at least 2n.
law depth_one:
  {S.depth(1) == 1n : Nat}

law depth_pow2:
  {S.depth(1024) == 11n : Nat}

law depth_odd:
  {S.depth(1000) == 11n : Nat}

law depth_past_pow2:
  {S.depth(1025) == 12n : Nat}

law depth_zero:
  {S.depth(0) == 1n : Nat}

# ---------------------------------------------------------------- alignment
# These are statements over every input, not examples. The IC of one date
# (S.date_ic) is F32 arithmetic and stays opaque: the laws say which rows reach
# it, in which order, and that the parallel path computes the same list.

# The IC of rows mx and my, or None when either row is missing.
def at.y(+x: List<&2, F32>, my: Maybe<&2, List<&2, F32>>, +rank: Bool) -> Maybe<&2, F32>:
  match my:
    case None{}:
      None{}
    case Some{y}:
      Some{S.date_ic(x, y, rank)}

def at(mx: Maybe<&2, List<&2, F32>>, my: Maybe<&2, List<&2, F32>>, +rank: Bool) -> Maybe<&2, F32>:
  match mx:
    case None{}:
      None{}
    case Some{x}:
      at.y(x, my, rank)

def rows(+p: S.Panel) -> List<&2, List<&2, F32>>:
  S.Panel{_, _, r} = p
  r

# Element i of the IC list is the IC of row i of xs and row i of ys.
law ic_row:
  for +xs: List<&2, List<&2, F32>>
  for +ys: List<&2, List<&2, F32>>
  for +rank: Bool
  for i: Nat
  {List.get(&2, F32, S.pseq(~S.XY, ~F32, ~Bool, ~S.date_xy, S.zip(xs, ys), rank), i) == at(List.get(&2, List<&2, F32>, xs, i), List.get(&2, List<&2, F32>, ys, i), rank) : Maybe<&2, F32>}

# pmap, the parallel map under the IC step and the row-wise transforms, gives
# the same list as the plain loop pseq, for every t.
law pmap_seq:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: C -> A -> B
  for +xs: List<&2, A>
  for +t: U32
  for +c: C
  {S.pmap(~A, ~B, ~C, ~f, xs, t, c) == S.pseq(~A, ~B, ~C, ~f, xs, c) : List<&2, B>}

# So the parallel IC step gives the sequential list, for every t.
law ics_seq:
  for +xs: List<&2, List<&2, F32>>
  for +ys: List<&2, List<&2, F32>>
  for +t: U32
  for +rank: Bool
  {S.ics(xs, ys, t, rank) == S.pseq(~S.XY, ~F32, ~Bool, ~S.date_xy, S.zip(xs, ys), rank) : List<&2, F32>}

# When the shapes match, rank_ic is that list. With ic_row: IC i is the rank IC
# of row i of x against row i of y.
law rank_ic_rows:
  for +tx: U32
  for +nx: U32
  for +ty: U32
  for +ny: U32
  for +xs: List<&2, List<&2, F32>>
  for +ys: List<&2, List<&2, F32>>
  for e: {Bool.and(U32.is_eq(tx, ty), U32.is_eq(nx, ny)) == True{} : Bool}
  {S.rank_ic(S.Panel{tx, nx, xs}, S.Panel{ty, ny, ys}) == Some{S.pseq(~S.XY, ~F32, ~Bool, ~S.date_xy, S.zip(xs, ys), True{})} : Maybe<&2, List<&2, F32>>}

# ---------------------------------------------------------------- lead
# Row i of lead.rows(xs, k, pad) is row k + i of xs, whenever that row exists.
law lead_row:
  for +xs: List<&2, List<&2, F32>>
  for k: Nat
  for +pad: List<&2, List<&2, F32>>
  for i: Nat
  for h: {Nat.is_le(1n+Nat.add(k, i), List.length(&2, List<&2, F32>, xs)) == True{} : Bool}
  {List.get(&2, List<&2, F32>, S.lead.rows(xs, k, pad), i) == List.get(&2, List<&2, F32>, xs, Nat.add(k, i)) : Maybe<&2, List<&2, F32>>}

# The same through the public lead: row i of lead(p, h) is row k + i of p, where
# k = min(h, t), whenever that row exists.
law lead_panel:
  for +t: U32
  for +n: U32
  for +xs: List<&2, List<&2, F32>>
  for +h: U32
  for i: Nat
  for e: {Nat.is_le(1n+Nat.add(U32.to_nat(U32.min(h, t)), i), List.length(&2, List<&2, F32>, xs)) == True{} : Bool}
  {List.get(&2, List<&2, F32>, rows(S.lead(S.Panel{t, n, xs}, h)), i) == List.get(&2, List<&2, F32>, xs, Nat.add(U32.to_nat(U32.min(h, t)), i)) : Maybe<&2, List<&2, F32>>}

# ---------------------------------------------------------------- forward IC

def nth(m: Maybe<&2, List<&2, F32>>, +i: Nat) -> Maybe<&2, F32>:
  match m:
    case None{}:
      None{}
    case Some{xs}:
      List.get(&2, F32, xs, i)

# IC i of forward_rank_ic is the rank IC of signal row i against return row
# i + 1 + h, whenever that return row exists. No h reaches row i itself.
law forward_row:
  for +tx: U32
  for +nx: U32
  for +tr: U32
  for +nr: U32
  for +xs: List<&2, List<&2, F32>>
  for +rs: List<&2, List<&2, F32>>
  for +h: Nat
  for +i: Nat
  for e: {Bool.and(U32.is_eq(tx, tr), U32.is_eq(nx, nr)) == True{} : Bool}
  for l: {Nat.is_le(1n+Nat.add(1n+h, i), List.length(&2, List<&2, F32>, rs)) == True{} : Bool}
  {nth(S.forward_rank_ic(S.Panel{tx, nx, xs}, S.Panel{tr, nr, rs}, h), i) == at(List.get(&2, List<&2, F32>, xs, i), List.get(&2, List<&2, F32>, rs, Nat.add(1n+h, i)), True{}) : Maybe<&2, F32>}

# ---------------------------------------------------------------- transforms
# Causal: the first k output rows depend only on the first k input rows. A
# transform that read a later date, a full-sample mean or a centered window,
# could not satisfy this.

law scan_causal:
  for ~T: Data
  for ~next: T -> List<&2, F32> -> T
  for ~out: T -> List<&2, F32> -> List<&2, F32>
  for +xs: List<&2, List<&2, F32>>
  for +s: T
  for +k: Nat
  {List.take(&2, List<&2, F32>, S.scan(~T, ~next, ~out, xs, s), k) == S.scan(~T, ~next, ~out, List.take(&2, List<&2, F32>, xs, k), s) : List<&2, List<&2, F32>>}

law pseq_causal:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: C -> A -> B
  for +xs: List<&2, A>
  for +c: C
  for +k: Nat
  {List.take(&2, B, S.pseq(~A, ~B, ~C, ~f, xs, c), k) == S.pseq(~A, ~B, ~C, ~f, List.take(&2, A, xs, k), c) : List<&2, B>}

def fmap(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, +c: C, m: Maybe<&2, A>) -> Maybe<&2, B>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{f(c, x)}

# A map reads one element: element i of the output is f of element i alone.
law pseq_row:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: C -> A -> B
  for +xs: List<&2, A>
  for +c: C
  for +i: Nat
  {List.get(&2, B, S.pseq(~A, ~B, ~C, ~f, xs, c), i) == fmap(~A, ~B, ~C, ~f, c, List.get(&2, A, xs, i)) : Maybe<&2, B>}

law zscore_row:
  for +t: U32
  for +n: U32
  for +xs: List<&2, List<&2, F32>>
  for +i: Nat
  {List.get(&2, List<&2, F32>, rows(S.zscore(S.Panel{t, n, xs})), i) == fmap(~List<&2, F32>, ~List<&2, F32>, ~S.Cfg, ~S.zscore.f, S.Cfg{n, 0.0}, List.get(&2, List<&2, F32>, xs, i)) : Maybe<&2, List<&2, F32>>}

law demean_row:
  for +t: U32
  for +n: U32
  for +xs: List<&2, List<&2, F32>>
  for +i: Nat
  {List.get(&2, List<&2, F32>, rows(S.demean(S.Panel{t, n, xs})), i) == fmap(~List<&2, F32>, ~List<&2, F32>, ~S.Cfg, ~S.demean.f, S.Cfg{n, 0.0}, List.get(&2, List<&2, F32>, xs, i)) : Maybe<&2, List<&2, F32>>}

law rank_row:
  for +t: U32
  for +n: U32
  for +xs: List<&2, List<&2, F32>>
  for +i: Nat
  {List.get(&2, List<&2, F32>, rows(S.rank(S.Panel{t, n, xs})), i) == fmap(~List<&2, F32>, ~List<&2, F32>, ~S.Cfg, ~S.rank.f, S.Cfg{n, 0.0}, List.get(&2, List<&2, F32>, xs, i)) : Maybe<&2, List<&2, F32>>}

law winsorize_row:
  for +t: U32
  for +n: U32
  for +xs: List<&2, List<&2, F32>>
  for +q: F32
  for +i: Nat
  {List.get(&2, List<&2, F32>, rows(S.winsorize(S.Panel{t, n, xs}, q)), i) == fmap(~List<&2, F32>, ~List<&2, F32>, ~S.Cfg, ~S.winsorize.f, S.Cfg{n, q}, List.get(&2, List<&2, F32>, xs, i)) : Maybe<&2, List<&2, F32>>}

law ewma_causal:
  for +t: U32
  for +n: U32
  for +xs: List<&2, List<&2, F32>>
  for +a: F32
  for +k: Nat
  {List.take(&2, List<&2, F32>, rows(S.ewma(S.Panel{t, n, xs}, a)), k) == rows(S.ewma(S.Panel{t, n, List.take(&2, List<&2, F32>, xs, k)}, a)) : List<&2, List<&2, F32>>}

law rolling_mean_causal:
  for +t: U32
  for +n: U32
  for +xs: List<&2, List<&2, F32>>
  for +w: Nat
  for +k: Nat
  {List.take(&2, List<&2, F32>, rows(S.rolling_mean(S.Panel{t, n, xs}, w)), k) == rows(S.rolling_mean(S.Panel{t, n, List.take(&2, List<&2, F32>, xs, k)}, w)) : List<&2, List<&2, F32>>}

# ---------------------------------------------------------------- missing values
# A name that is NaN on either side takes no part in that date's IC.

# The IC of a date reads only the complete pairs: the names present on both sides.
law date_ic_pairs:
  for +xs: List<&2, F32>
  for +ys: List<&2, F32>
  for +rank: Bool
  {S.date_ic(xs, ys, rank) == S.core(S.complete(xs, ys), rank) : F32}

law complete_filter:
  for +xs: List<&2, F32>
  for +ys: List<&2, F32>
  {S.complete(xs, ys) == List.filter(~S.Pr, ~S.both, S.zip2(xs, ys)) : List<&2, S.Pr>}

# Where the return is NaN, the signal value can be anything: the IC is the same.
law date_ic_missing_y:
  for +xs: List<&2, F32>
  for +ys: List<&2, F32>
  for +rank: Bool
  for +i: Nat
  for +v: F32
  for +y: F32
  for h1: {List.get(&2, F32, ys, i) == Some{y} : Maybe<&2, F32>}
  for h2: {S.is_nan(y) == True{} : Bool}
  {S.date_ic(List.set(&2, F32, xs, i, v), ys, rank) == S.date_ic(xs, ys, rank) : F32}

# Where the signal is NaN, the return can be anything: the IC is the same.
law date_ic_missing_x:
  for +xs: List<&2, F32>
  for +ys: List<&2, F32>
  for +rank: Bool
  for +i: Nat
  for +v: F32
  for +x: F32
  for h1: {List.get(&2, F32, xs, i) == Some{x} : Maybe<&2, F32>}
  for h2: {S.is_nan(x) == True{} : Bool}
  {S.date_ic(xs, List.set(&2, F32, ys, i, v), rank) == S.date_ic(xs, ys, rank) : F32}

# ---------------------------------------------------------------- ranks
# The ranks behind rank_ic and rank are proved against counting, for any total
# order. F32's <= is one on the values that reach a rank, since the NaN filter
# runs first, but floats are opaque to the checker, so that step is assumed.

def ind(b: Bool) -> Nat:
  Bool.pick(Nat, b, 1n, 0n)

# #{x in xs : x < q}
def cnt_lt(~A: Data, ~le: A -> A -> Bool, xs: List<&2, A>, +q: A) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, t}:
      Nat.add(ind(Bool.not(le(q, x))), cnt_lt(~A, ~le, t, q))

# #{x in xs : x <= q}
def cnt_le(~A: Data, ~le: A -> A -> Bool, xs: List<&2, A>, +q: A) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, t}:
      Nat.add(ind(le(x, q)), cnt_le(~A, ~le, t, q))


# 2 x the average 1-based rank of q among xs: ties share the mean of their places.
law rank_count:
  for ~A: Data
  for ~le: A -> A -> Bool
  for ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}
  for ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}
  for +xs: List<&2, A>
  for +q: A
  {S.rank_of(~A, ~le, S.tree(~A, ~le, xs), q) == 1n+Nat.add(cnt_lt(~A, ~le, xs, q), cnt_le(~A, ~le, xs, q)) : Nat}

def spec_ranks(~A: Data, ~le: A -> A -> Bool, xs: List<&2, A>, +all: List<&2, A>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+q, t}:
      (1n+Nat.add(cnt_lt(~A, ~le, all, q), cnt_le(~A, ~le, all, q))) <> spec_ranks(~A, ~le, t, all)

# ranks(xs) is that number for each element, in place.
law ranks_spec:
  for ~A: Data
  for ~le: A -> A -> Bool
  for ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}
  for ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}
  for +xs: List<&2, A>
  {S.ranks(~A, ~le, xs) == spec_ranks(~A, ~le, xs, xs) : List<&2, Nat>}
