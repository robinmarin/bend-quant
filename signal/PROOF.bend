import Base
import ./LAWS.bend as Laws
import ./signal.bend as S

def Laws.from_rows_equal():
  {==}

def Laws.from_rows_ragged():
  {==}

def Laws.from_rows_ragged_last():
  {==}

def Laws.from_rows_empty():
  {==}

def Laws.depth_one():
  {==}

def Laws.depth_pow2():
  {==}

def Laws.depth_odd():
  {==}

def Laws.depth_past_pow2():
  {==}

def Laws.depth_zero():
  {==}

# ---------------------------------------------------------------- helpers

def false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : Bool.pick(Type, _, Empty, Unit)
  Unit{}

def at_none_r(mx: Maybe<&2, List<&2, F32>>, +n: U32, +rank: Bool) -> {Laws.at(mx, None{}, n, rank) == None{} : Maybe<&2, F32>}:
  match mx:
    case None{}:
      {==}
    case Some{x}:
      {==}

def seq2(two: S.Two) -> List<&2, F32>:
  S.Two{l, r} = two
  List.append(&2, F32, S.seq(l), S.seq(r))

def cons_seq2(+h: S.XY, +two: S.Two) -> {seq2(S.split.cons(h, two)) == S.date_xy(h) <> seq2(two) : List<&2, F32>}:
  match two:
    case S.Two{l, r}:
      {==}

# split(k, xs) loses and reorders nothing
def split_seq(+k: Nat, +xs: List<&2, S.XY>) -> {seq2(S.split(k, xs)) == S.seq(xs) : List<&2, F32>}:
  match k xs:
    case 0n Nil{}:
      {==}
    case 0n Con{h, t}:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{+h, +t}:
      %split_seq(p, t) : {seq2(S.split.cons(h, S.split(p, t))) == S.date_xy(h) <> _ : List<&2, F32>}
      cons_seq2(h, S.split(p, t))

def par_seq(+d: Nat, +two: S.Two, +h: U32, +r: U32) -> {S.par(d, two, h, r) == seq2(two) : List<&2, F32>}:
  match d:
    case 0n:
      match two:
        case S.Two{l, q}:
          {==}
    case 1n+e:
      match two:
        case S.Two{+l, +q}:
          +hl = (h >> 1n : U32)
          +hr = (r >> 1n : U32)
          +pl = S.par(e, S.split(U32.to_nat(hl), l), hl, (h - hl : U32))
          +pr = S.par(e, S.split(U32.to_nat(hr), q), hr, (r - hr : U32))
          el = Equal.trans(List<&2, F32>, pl, seq2(S.split(U32.to_nat(hl), l)), S.seq(l), par_seq(e, S.split(U32.to_nat(hl), l), hl, (h - hl : U32)), split_seq(U32.to_nat(hl), l))
          er = Equal.trans(List<&2, F32>, pr, seq2(S.split(U32.to_nat(hr), q)), S.seq(q), par_seq(e, S.split(U32.to_nat(hr), q), hr, (r - hr : U32)), split_seq(U32.to_nat(hr), q))
          %el : {List.append(&2, F32, pl, pr) == List.append(&2, F32, _, S.seq(q)) : List<&2, F32>}
          %er : {List.append(&2, F32, pl, pr) == List.append(&2, F32, pl, _) : List<&2, F32>}
          {==}

def get_append_left(+xs: List<&2, List<&2, F32>>, +ys: List<&2, List<&2, F32>>, +i: Nat, h: {Nat.is_le(1n+i, List.length(&2, List<&2, F32>, xs)) == True{} : Bool}) -> {List.get(&2, List<&2, F32>, List.append(&2, List<&2, F32>, xs, ys), i) == List.get(&2, List<&2, F32>, xs, i) : Maybe<&2, List<&2, F32>>}:
  match xs i:
    case Nil{} _:
      Empty.absurd({List.get(&2, List<&2, F32>, ys, i) == None{} : Maybe<&2, List<&2, F32>>}, false_ne_true(h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      get_append_left(t, ys, p, h)

# ---------------------------------------------------------------- alignment

def Laws.ic_row(xs, ys, n, rank, i):
  match xs ys i:
    case Nil{} _ _:
      {==}
    case Con{x, xt} Nil{} 0n:
      {==}
    case Con{x, +xt} Nil{} 1n+p:
      Equal.sym(Maybe<&2, F32>, Laws.at(List.get(&2, List<&2, F32>, xt, p), None{}, n, rank), None{}, at_none_r(List.get(&2, List<&2, F32>, xt, p), n, rank))
    case Con{x, xt} Con{y, yt} 0n:
      {==}
    case Con{x, xt} Con{y, yt} 1n+p:
      Laws.ic_row(xt, yt, n, rank, p)

def Laws.ics_seq(xs, ys, t, n, rank):
  +z = S.zip(xs, ys, n, rank)
  +k = U32.to_nat((t >> 1n : U32))
  +d = Bool.pick(Nat, U32.is_lt(t, 64), 0n, 5n)
  Equal.trans(List<&2, F32>, S.par(d, S.split(k, z), (t >> 1n : U32), (t - (t >> 1n : U32) : U32)), seq2(S.split(k, z)), S.seq(z), par_seq(d, S.split(k, z), (t >> 1n : U32), (t - (t >> 1n : U32) : U32)), split_seq(k, z))

def Laws.rank_ic_rows(tx, nx, ty, ny, xs, ys, e):
  %Equal.sym(Bool, Bool.and(U32.is_eq(tx, ty), U32.is_eq(nx, ny)), True{}, e) : {S.ic.chk(_, xs, ys, tx, nx, True{}) == Some{S.seq(S.zip(xs, ys, nx, True{}))} : Maybe<&2, List<&2, F32>>}
  %Laws.ics_seq(xs, ys, tx, nx, True{}) : {Some{S.ics(xs, ys, tx, nx, True{})} == Some{_} : Maybe<&2, List<&2, F32>>}
  {==}

# ---------------------------------------------------------------- lead

def Laws.lead_row(xs, k, pad, i, h):
  match xs k:
    case Nil{} _:
      Empty.absurd({List.get(&2, List<&2, F32>, S.lead.rows(Nil{}, k, pad), i) == None{} : Maybe<&2, List<&2, F32>>}, false_ne_true(h))
    case Con{+x, +t} 0n:
      get_append_left(x <> t, pad, i, h)
    case Con{x, t} 1n+p:
      Laws.lead_row(t, p, pad, i, h)

def Laws.lead_panel(t, n, xs, h, i, e):
  +k = U32.to_nat(U32.min(h, t))
  Laws.lead_row(xs, k, List.replicate(List<&2, F32>, k, List.replicate(F32, U32.to_nat(n), S.nan())), i, e)

# ---------------------------------------------------------------- forward IC

def Laws.forward_row(tx, nx, tr, nr, xs, rs, h, i, e, l):
  +f = S.fwd.rows(rs, h, tr, nr)
  +pad = List.replicate(List<&2, F32>, Nat.min(1n+h, U32.to_nat(tr)), List.replicate(F32, U32.to_nat(nr), S.nan()))
  +want = Laws.at(List.get(&2, List<&2, F32>, xs, i), List.get(&2, List<&2, F32>, rs, Nat.add(1n+h, i)), nx, True{})
  %Equal.sym(Maybe<&2, List<&2, F32>>, S.rank_ic(S.Panel{tx, nx, xs}, S.Panel{tr, nr, f}), Some{S.seq(S.zip(xs, f, nx, True{}))}, Laws.rank_ic_rows(tx, nx, tr, nr, xs, f, e)) : {Laws.nth(_, i) == want : Maybe<&2, F32>}
  %Equal.sym(Maybe<&2, F32>, List.get(&2, F32, S.seq(S.zip(xs, f, nx, True{})), i), Laws.at(List.get(&2, List<&2, F32>, xs, i), List.get(&2, List<&2, F32>, f, i), nx, True{}), Laws.ic_row(xs, f, nx, True{}, i)) : {_ == want : Maybe<&2, F32>}
  %Laws.lead_row(rs, 1n+h, pad, i, l) : {Laws.at(List.get(&2, List<&2, F32>, xs, i), List.get(&2, List<&2, F32>, f, i), nx, True{}) == Laws.at(List.get(&2, List<&2, F32>, xs, i), _, nx, True{}) : Maybe<&2, F32>}
  {==}

# ---------------------------------------------------------------- transforms

def Laws.scan_causal(T, next, out, xs, s, k):
  match xs k:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{+x, +t} 1n+p:
      %Laws.scan_causal(~T, ~next, ~out, t, next(s, x), p) : {out(next(s, x), x) <> List.take(&2, List<&2, F32>, S.scan(~T, ~next, ~out, t, next(s, x)), p) == out(next(s, x), x) <> _ : List<&2, List<&2, F32>>}
      {==}

def Laws.rowwise_causal(C, f, xs, c, k):
  match xs k:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{+x, +t} 1n+p:
      %Laws.rowwise_causal(~C, ~f, t, c, p) : {f(c, x) <> List.take(&2, List<&2, F32>, S.rowwise(~C, ~f, t, c), p) == f(c, x) <> _ : List<&2, List<&2, F32>>}
      {==}

def Laws.rowwise_row(C, f, xs, c, i):
  match xs i:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      Laws.rowwise_row(~C, ~f, t, c, p)

def Laws.zscore_row(t, n, xs, i):
  Laws.rowwise_row(~S.Cfg, ~S.zscore.f, xs, S.Cfg{n, 0.0}, i)

def Laws.demean_row(t, n, xs, i):
  Laws.rowwise_row(~S.Cfg, ~S.demean.f, xs, S.Cfg{n, 0.0}, i)

def Laws.rank_row(t, n, xs, i):
  Laws.rowwise_row(~S.Cfg, ~S.rank.f, xs, S.Cfg{n, 0.0}, i)

def Laws.winsorize_row(t, n, xs, q, i):
  Laws.rowwise_row(~S.Cfg, ~S.winsorize.f, xs, S.Cfg{n, q}, i)

def Laws.ewma_causal(t, n, xs, a, k):
  Laws.scan_causal(~S.Ew, ~S.ew.next, ~S.ew.out, xs, S.Ew{a, List.replicate(F32, U32.to_nat(n), S.nan())}, k)

def Laws.rolling_mean_causal(t, n, xs, w, k):
  Laws.scan_causal(~S.Win, ~S.win.next, ~S.win.out, xs, S.Win{w, Nil{}}, k)
