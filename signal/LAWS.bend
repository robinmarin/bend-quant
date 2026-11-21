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
def at.y(+x: List<&2, F32>, my: Maybe<&2, List<&2, F32>>, +n: U32, +rank: Bool) -> Maybe<&2, F32>:
  match my:
    case None{}:
      None{}
    case Some{y}:
      Some{S.date_ic(x, y, n, rank)}

def at(mx: Maybe<&2, List<&2, F32>>, my: Maybe<&2, List<&2, F32>>, +n: U32, +rank: Bool) -> Maybe<&2, F32>:
  match mx:
    case None{}:
      None{}
    case Some{x}:
      at.y(x, my, n, rank)

def rows(+p: S.Panel) -> List<&2, List<&2, F32>>:
  S.Panel{_, _, r} = p
  r

# Element i of the IC list is the IC of row i of xs and row i of ys.
law ic_row:
  for +xs: List<&2, List<&2, F32>>
  for +ys: List<&2, List<&2, F32>>
  for +n: U32
  for +rank: Bool
  for i: Nat
  {List.get(&2, F32, S.seq(S.zip(xs, ys, n, rank)), i) == at(List.get(&2, List<&2, F32>, xs, i), List.get(&2, List<&2, F32>, ys, i), n, rank) : Maybe<&2, F32>}

# The parallel fork-join over dates gives the sequential list, for every t.
law ics_seq:
  for +xs: List<&2, List<&2, F32>>
  for +ys: List<&2, List<&2, F32>>
  for +t: U32
  for +n: U32
  for +rank: Bool
  {S.ics(xs, ys, t, n, rank) == S.seq(S.zip(xs, ys, n, rank)) : List<&2, F32>}

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
  {S.rank_ic(S.Panel{tx, nx, xs}, S.Panel{ty, ny, ys}) == Some{S.seq(S.zip(xs, ys, nx, True{}))} : Maybe<&2, List<&2, F32>>}

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
