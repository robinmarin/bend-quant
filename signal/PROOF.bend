import Base
import ./LAWS.bend as Laws
import ./signal.bend as S
import ./ranks_proof.bend as RP

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

def at_none_r(mx: Maybe<&2, List<&2, F32>>, +rank: Bool) -> {Laws.at(mx, None{}, rank) == None{} : Maybe<&2, F32>}:
  match mx:
    case None{}:
      {==}
    case Some{x}:
      {==}

def seq2(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, two: S.Two<A>, +c: C) -> List<&2, B>:
  S.Two{l, r} = two
  List.append(&2, B, S.pseq(~A, ~B, ~C, ~f, l, c), S.pseq(~A, ~B, ~C, ~f, r, c))

def cons_seq2(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, +h: A, +two: S.Two<A>, +c: C) -> {seq2(~A, ~B, ~C, ~f, S.split.cons(A, h, two), c) == f(c, h) <> seq2(~A, ~B, ~C, ~f, two, c) : List<&2, B>}:
  match two:
    case S.Two{l, r}:
      {==}

# split(k, xs) loses and reorders nothing
def split_seq(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, +k: Nat, +xs: List<&2, A>, +c: C) -> {seq2(~A, ~B, ~C, ~f, S.split(A, k, xs), c) == S.pseq(~A, ~B, ~C, ~f, xs, c) : List<&2, B>}:
  match k xs:
    case 0n Nil{}:
      {==}
    case 0n Con{h, t}:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{+h, +t}:
      %split_seq(~A, ~B, ~C, ~f, p, t, c) : {seq2(~A, ~B, ~C, ~f, S.split.cons(A, h, S.split(A, p, t)), c) == f(c, h) <> _ : List<&2, B>}
      cons_seq2(~A, ~B, ~C, ~f, h, S.split(A, p, t), c)

def par_seq(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, +d: Nat, +two: S.Two<A>, +h: U32, +r: U32, +c: C) -> {S.par(~A, ~B, ~C, ~f, d, two, h, r, c) == seq2(~A, ~B, ~C, ~f, two, c) : List<&2, B>}:
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
          +pl = S.par(~A, ~B, ~C, ~f, e, S.split(A, U32.to_nat(hl), l), hl, (h - hl : U32), c)
          +pr = S.par(~A, ~B, ~C, ~f, e, S.split(A, U32.to_nat(hr), q), hr, (r - hr : U32), c)
          el = Equal.trans(List<&2, B>, pl, seq2(~A, ~B, ~C, ~f, S.split(A, U32.to_nat(hl), l), c), S.pseq(~A, ~B, ~C, ~f, l, c), par_seq(~A, ~B, ~C, ~f, e, S.split(A, U32.to_nat(hl), l), hl, (h - hl : U32), c), split_seq(~A, ~B, ~C, ~f, U32.to_nat(hl), l, c))
          er = Equal.trans(List<&2, B>, pr, seq2(~A, ~B, ~C, ~f, S.split(A, U32.to_nat(hr), q), c), S.pseq(~A, ~B, ~C, ~f, q, c), par_seq(~A, ~B, ~C, ~f, e, S.split(A, U32.to_nat(hr), q), hr, (r - hr : U32), c), split_seq(~A, ~B, ~C, ~f, U32.to_nat(hr), q, c))
          %el : {List.append(&2, B, pl, pr) == List.append(&2, B, _, S.pseq(~A, ~B, ~C, ~f, q, c)) : List<&2, B>}
          %er : {List.append(&2, B, pl, pr) == List.append(&2, B, pl, _) : List<&2, B>}
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

def Laws.ic_row(xs, ys, rank, i):
  match xs ys i:
    case Nil{} _ _:
      {==}
    case Con{x, xt} Nil{} 0n:
      {==}
    case Con{x, +xt} Nil{} 1n+p:
      Equal.sym(Maybe<&2, F32>, Laws.at(List.get(&2, List<&2, F32>, xt, p), None{}, rank), None{}, at_none_r(List.get(&2, List<&2, F32>, xt, p), rank))
    case Con{x, xt} Con{y, yt} 0n:
      {==}
    case Con{x, xt} Con{y, yt} 1n+p:
      Laws.ic_row(xt, yt, rank, p)

def Laws.pmap_seq(A, B, C, f, xs, t, c):
  +k = U32.to_nat((t >> 1n : U32))
  +d = Bool.pick(Nat, U32.is_lt(t, 64), 0n, 5n)
  +sp = S.split(A, k, xs)
  Equal.trans(List<&2, B>, S.par(~A, ~B, ~C, ~f, d, sp, (t >> 1n : U32), (t - (t >> 1n : U32) : U32), c), seq2(~A, ~B, ~C, ~f, sp, c), S.pseq(~A, ~B, ~C, ~f, xs, c), par_seq(~A, ~B, ~C, ~f, d, sp, (t >> 1n : U32), (t - (t >> 1n : U32) : U32), c), split_seq(~A, ~B, ~C, ~f, k, xs, c))

def Laws.ics_seq(xs, ys, t, rank):
  Laws.pmap_seq(~S.XY, ~F32, ~Bool, ~S.date_xy, S.zip(xs, ys), t, rank)

def Laws.rank_ic_rows(tx, nx, ty, ny, xs, ys, e):
  %Equal.sym(Bool, Bool.and(U32.is_eq(tx, ty), U32.is_eq(nx, ny)), True{}, e) : {S.ic.chk(_, xs, ys, tx, True{}) == Some{S.pseq(~S.XY, ~F32, ~Bool, ~S.date_xy, S.zip(xs, ys), True{})} : Maybe<&2, List<&2, F32>>}
  %Laws.ics_seq(xs, ys, tx, True{}) : {Some{S.ics(xs, ys, tx, True{})} == Some{_} : Maybe<&2, List<&2, F32>>}
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
  +want = Laws.at(List.get(&2, List<&2, F32>, xs, i), List.get(&2, List<&2, F32>, rs, Nat.add(1n+h, i)), True{})
  %Equal.sym(Maybe<&2, List<&2, F32>>, S.rank_ic(S.Panel{tx, nx, xs}, S.Panel{tr, nr, f}), Some{S.pseq(~S.XY, ~F32, ~Bool, ~S.date_xy, S.zip(xs, f), True{})}, Laws.rank_ic_rows(tx, nx, tr, nr, xs, f, e)) : {Laws.nth(_, i) == want : Maybe<&2, F32>}
  %Equal.sym(Maybe<&2, F32>, List.get(&2, F32, S.pseq(~S.XY, ~F32, ~Bool, ~S.date_xy, S.zip(xs, f), True{}), i), Laws.at(List.get(&2, List<&2, F32>, xs, i), List.get(&2, List<&2, F32>, f, i), True{}), Laws.ic_row(xs, f, True{}, i)) : {_ == want : Maybe<&2, F32>}
  %Laws.lead_row(rs, 1n+h, pad, i, l) : {Laws.at(List.get(&2, List<&2, F32>, xs, i), List.get(&2, List<&2, F32>, f, i), True{}) == Laws.at(List.get(&2, List<&2, F32>, xs, i), _, True{}) : Maybe<&2, F32>}
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

def Laws.pseq_causal(A, B, C, f, xs, c, k):
  match xs k:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{+x, +t} 1n+p:
      %Laws.pseq_causal(~A, ~B, ~C, ~f, t, c, p) : {f(c, x) <> List.take(&2, B, S.pseq(~A, ~B, ~C, ~f, t, c), p) == f(c, x) <> _ : List<&2, B>}
      {==}

def Laws.pseq_row(A, B, C, f, xs, c, i):
  match xs i:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      Laws.pseq_row(~A, ~B, ~C, ~f, t, c, p)

# a row-wise panel transform: pmap is pseq (pmap_seq), then pseq_row
def row_law(~f: S.Cfg -> List<&2, F32> -> List<&2, F32>, +xs: List<&2, List<&2, F32>>, +t: U32, +c: S.Cfg, +i: Nat) -> {List.get(&2, List<&2, F32>, S.pmap(~List<&2, F32>, ~List<&2, F32>, ~S.Cfg, ~f, xs, t, c), i) == Laws.fmap(~List<&2, F32>, ~List<&2, F32>, ~S.Cfg, ~f, c, List.get(&2, List<&2, F32>, xs, i)) : Maybe<&2, List<&2, F32>>}:
  %Equal.sym(List<&2, List<&2, F32>>, S.pmap(~List<&2, F32>, ~List<&2, F32>, ~S.Cfg, ~f, xs, t, c), S.pseq(~List<&2, F32>, ~List<&2, F32>, ~S.Cfg, ~f, xs, c), Laws.pmap_seq(~List<&2, F32>, ~List<&2, F32>, ~S.Cfg, ~f, xs, t, c)) : {List.get(&2, List<&2, F32>, _, i) == Laws.fmap(~List<&2, F32>, ~List<&2, F32>, ~S.Cfg, ~f, c, List.get(&2, List<&2, F32>, xs, i)) : Maybe<&2, List<&2, F32>>}
  Laws.pseq_row(~List<&2, F32>, ~List<&2, F32>, ~S.Cfg, ~f, xs, c, i)

def Laws.zscore_row(t, n, xs, i):
  row_law(~S.zscore.f, xs, t, S.Cfg{n, 0.0}, i)

def Laws.demean_row(t, n, xs, i):
  row_law(~S.demean.f, xs, t, S.Cfg{n, 0.0}, i)

def Laws.rank_row(t, n, xs, i):
  row_law(~S.rank.f, xs, t, S.Cfg{n, 0.0}, i)

def Laws.winsorize_row(t, n, xs, q, i):
  row_law(~S.winsorize.f, xs, t, S.Cfg{n, q}, i)

def Laws.ewma_causal(t, n, xs, a, k):
  Laws.scan_causal(~S.Ew, ~S.ew.next, ~S.ew.out, xs, S.Ew{a, List.replicate(F32, U32.to_nat(n), S.nan())}, k)

def Laws.rolling_mean_causal(t, n, xs, w, k):
  Laws.scan_causal(~S.Win, ~S.win.next, ~S.win.out, xs, S.Win{w, Nil{}}, k)

# ---------------------------------------------------------------- missing values

def unsome(m: Maybe<&2, F32>) -> F32:
  match m:
    case None{}:
      0.0
    case Some{v}:
      v

def nan_of_get(+a: F32, +b: F32, h1: {Some{a} == Some{b} : Maybe<&2, F32>}, h2: {S.is_nan(b) == True{} : Bool}) -> {S.is_nan(a) == True{} : Bool}:
  %Equal.sym(Maybe<&2, F32>, Some{a}, Some{b}, h1) : {S.is_nan(unsome(_)) == True{} : Bool}
  h2

def and_false(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.date_ic_pairs(xs, ys, rank):
  {==}

def Laws.complete_filter(xs, ys):
  {==}

# the filtered pairs don't change when x moves at a name whose y is NaN
def filt_y(+xs: List<&2, F32>, +ys: List<&2, F32>, +i: Nat, +v: F32, +y: F32, h1: {List.get(&2, F32, ys, i) == Some{y} : Maybe<&2, F32>}, h2: {S.is_nan(y) == True{} : Bool}) -> {List.filter(~S.Pr, ~S.both, S.zip2(List.set(&2, F32, xs, i, v), ys)) == List.filter(~S.Pr, ~S.both, S.zip2(xs, ys)) : List<&2, S.Pr>}:
  match xs ys i:
    case Nil{} _ _:
      {==}
    case Con{x, xt} Nil{} 0n:
      {==}
    case Con{x, xt} Nil{} 1n+p:
      {==}
    case Con{+x, +xt} Con{+y1, +yt} 0n:
      +r = List.filter(~S.Pr, ~S.both, S.zip2(xt, yt))
      %Equal.sym(Bool, S.is_nan(y1), True{}, nan_of_get(y1, y, h1, h2)) : {List.filter.put(S.Pr, S.Pr{v, y1}, r, Bool.and(Bool.not(_), Bool.not(S.is_nan(v)))) == List.filter.put(S.Pr, S.Pr{x, y1}, r, Bool.and(Bool.not(_), Bool.not(S.is_nan(x)))) : List<&2, S.Pr>}
      {==}
    case Con{+x, +xt} Con{+y1, +yt} 1n+p:
      %filt_y(xt, yt, p, v, y, h1, h2) : {List.filter.put(S.Pr, S.Pr{x, y1}, List.filter(~S.Pr, ~S.both, S.zip2(List.set(&2, F32, xt, p, v), yt)), S.both(S.Pr{x, y1})) == List.filter.put(S.Pr, S.Pr{x, y1}, _, S.both(S.Pr{x, y1})) : List<&2, S.Pr>}
      {==}

# the same with the roles swapped; x is tested second in both, hence and_false
def filt_x(+xs: List<&2, F32>, +ys: List<&2, F32>, +i: Nat, +v: F32, +x: F32, h1: {List.get(&2, F32, xs, i) == Some{x} : Maybe<&2, F32>}, h2: {S.is_nan(x) == True{} : Bool}) -> {List.filter(~S.Pr, ~S.both, S.zip2(xs, List.set(&2, F32, ys, i, v))) == List.filter(~S.Pr, ~S.both, S.zip2(xs, ys)) : List<&2, S.Pr>}:
  match xs ys i:
    case Nil{} _ _:
      {==}
    case Con{x1, xt} Nil{} _:
      {==}
    case Con{+x1, +xt} Con{+y1, +yt} 0n:
      +r = List.filter(~S.Pr, ~S.both, S.zip2(xt, yt))
      %Equal.sym(Bool, S.is_nan(x1), True{}, nan_of_get(x1, x, h1, h2)) : {List.filter.put(S.Pr, S.Pr{x1, v}, r, Bool.and(Bool.not(S.is_nan(v)), Bool.not(_))) == List.filter.put(S.Pr, S.Pr{x1, y1}, r, Bool.and(Bool.not(S.is_nan(y1)), Bool.not(_))) : List<&2, S.Pr>}
      %Equal.sym(Bool, Bool.and(Bool.not(S.is_nan(v)), False{}), False{}, and_false(Bool.not(S.is_nan(v)))) : {List.filter.put(S.Pr, S.Pr{x1, v}, r, _) == List.filter.put(S.Pr, S.Pr{x1, y1}, r, Bool.and(Bool.not(S.is_nan(y1)), False{})) : List<&2, S.Pr>}
      %Equal.sym(Bool, Bool.and(Bool.not(S.is_nan(y1)), False{}), False{}, and_false(Bool.not(S.is_nan(y1)))) : {r == List.filter.put(S.Pr, S.Pr{x1, y1}, r, _) : List<&2, S.Pr>}
      {==}
    case Con{+x1, +xt} Con{+y1, +yt} 1n+p:
      %filt_x(xt, yt, p, v, x, h1, h2) : {List.filter.put(S.Pr, S.Pr{x1, y1}, List.filter(~S.Pr, ~S.both, S.zip2(xt, List.set(&2, F32, yt, p, v))), S.both(S.Pr{x1, y1})) == List.filter.put(S.Pr, S.Pr{x1, y1}, _, S.both(S.Pr{x1, y1})) : List<&2, S.Pr>}
      {==}

# date_ic(a) == core(complete(a)) == core(complete(b)) == date_ic(b), given
# complete(a) == complete(b). Each step is a stated equality, so the kernel never
# has to unfold the IC itself.
def via_complete(+xa: List<&2, F32>, +ya: List<&2, F32>, +xb: List<&2, F32>, +yb: List<&2, F32>, +rank: Bool, e: {S.complete(xa, ya) == S.complete(xb, yb) : List<&2, S.Pr>}) -> {S.date_ic(xa, ya, rank) == S.date_ic(xb, yb, rank) : F32}:
  +ca = S.core(S.complete(xa, ya), rank)
  +cb = S.core(S.complete(xb, yb), rank)
  mid = Equal.cong(List<&2, S.Pr>, F32, c => S.core(c, rank), S.complete(xa, ya), S.complete(xb, yb), e)
  Equal.trans(F32, S.date_ic(xa, ya, rank), ca, S.date_ic(xb, yb, rank), Laws.date_ic_pairs(xa, ya, rank), Equal.trans(F32, ca, cb, S.date_ic(xb, yb, rank), mid, Equal.sym(F32, S.date_ic(xb, yb, rank), cb, Laws.date_ic_pairs(xb, yb, rank))))

# complete(a) == filter(a) == filter(b) == complete(b)
def complete_eq(+xa: List<&2, F32>, +ya: List<&2, F32>, +xb: List<&2, F32>, +yb: List<&2, F32>, e: {List.filter(~S.Pr, ~S.both, S.zip2(xa, ya)) == List.filter(~S.Pr, ~S.both, S.zip2(xb, yb)) : List<&2, S.Pr>}) -> {S.complete(xa, ya) == S.complete(xb, yb) : List<&2, S.Pr>}:
  +fa = List.filter(~S.Pr, ~S.both, S.zip2(xa, ya))
  +fb = List.filter(~S.Pr, ~S.both, S.zip2(xb, yb))
  Equal.trans(List<&2, S.Pr>, S.complete(xa, ya), fa, S.complete(xb, yb), Laws.complete_filter(xa, ya), Equal.trans(List<&2, S.Pr>, fa, fb, S.complete(xb, yb), e, Equal.sym(List<&2, S.Pr>, S.complete(xb, yb), fb, Laws.complete_filter(xb, yb))))

def Laws.date_ic_missing_y(xs, ys, rank, i, v, y, h1, h2):
  +xa = List.set(&2, F32, xs, i, v)
  via_complete(xa, ys, xs, ys, rank, complete_eq(xa, ys, xs, ys, filt_y(xs, ys, i, v, y, h1, h2)))

def Laws.date_ic_missing_x(xs, ys, rank, i, v, x, h1, h2):
  +ya = List.set(&2, F32, ys, i, v)
  via_complete(xs, ya, xs, ys, rank, complete_eq(xs, ya, xs, ys, filt_x(xs, ys, i, v, x, h1, h2)))

# ---------------------------------------------------------------- ranks
# The lemmas are in ranks_proof.bend.

def Laws.rank_count(A, le, le_total, le_trans, xs, q):
  RP.rank_count(~A, ~le, ~le_total, ~le_trans, xs, q)

def ranks_go(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +ys: List<&2, A>, +all: List<&2, A>) -> {S.ranks.go(~A, ~le, ys, S.tree(~A, ~le, all)) == Laws.spec_ranks(~A, ~le, ys, all) : List<&2, Nat>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      +h = S.rank_of(~A, ~le, S.tree(~A, ~le, all), q)
      +h2 = {1n+Nat.add(Laws.cnt_lt(~A, ~le, all, q), Laws.cnt_le(~A, ~le, all, q)) : Nat}
      +rt = S.ranks.go(~A, ~le, t, S.tree(~A, ~le, all))
      +st = Laws.spec_ranks(~A, ~le, t, all)
      Equal.trans(List<&2, Nat>, h <> rt, h2 <> rt, h2 <> st, Equal.cong(Nat, List<&2, Nat>, z => z <> rt, h, h2, RP.rank_count(~A, ~le, ~le_total, ~le_trans, all, q)), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => h2 <> z, rt, st, ranks_go(~A, ~le, ~le_total, ~le_trans, t, all)))

def Laws.ranks_spec(A, le, le_total, le_trans, xs):
  ranks_go(~A, ~le, ~le_total, ~le_trans, xs, xs)

# Nat instances: --verdict checks the template laws through a concrete order.
def rank_count_nat(+xs: List<&2, Nat>, +q: Nat) -> {S.rank_of(~Nat, ~Nat.is_le, S.tree(~Nat, ~Nat.is_le, xs), q) == 1n+Nat.add(Laws.cnt_lt(~Nat, ~Nat.is_le, xs, q), Laws.cnt_le(~Nat, ~Nat.is_le, xs, q)) : Nat}:
  Laws.rank_count(~Nat, ~Nat.is_le, ~RP.nat_le_total, ~RP.nat_le_trans, xs, q)

def ranks_spec_nat(+xs: List<&2, Nat>) -> {S.ranks(~Nat, ~Nat.is_le, xs) == Laws.spec_ranks(~Nat, ~Nat.is_le, xs, xs) : List<&2, Nat>}:
  Laws.ranks_spec(~Nat, ~Nat.is_le, ~RP.nat_le_total, ~RP.nat_le_trans, xs)
