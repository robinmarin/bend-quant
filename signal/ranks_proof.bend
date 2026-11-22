# The proof that tree ranks are average ranks (law rank_count).
# It builds up from Nat arithmetic: counts over lists, the interleave, counts over
# a tree, the search-tree invariant, and the walk. Generic over a comparison le;
# each fact of the order comes from le_total and le_trans.
import Base
import ./LAWS.bend as Laws
import ./signal.bend as S

# ---- Nat

def add_zero_r(+n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero_r(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_succ_r(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ_r(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, add_zero_r(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add_succ_r(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def add_assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

# a + (b + c) == b + (a + c)
def add_lcomm(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+Nat.add(p, c)), 1n+Nat.add(b, Nat.add(p, c)), add_succ_r(b, Nat.add(p, c))) : {1n+Nat.add(p, Nat.add(b, c)) == _ : Nat}
      %add_lcomm(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

def lt_append(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>, +ys: List<&2, A>, +q: A) -> {Laws.cnt_lt(~A, ~le, List.append(&2, A, xs, ys), q) == Nat.add(Laws.cnt_lt(~A, ~le, xs, q), Laws.cnt_lt(~A, ~le, ys, q)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +i = Laws.ind(Bool.not(le(q, x)))
      +ct = Laws.cnt_lt(~A, ~le, t, q)
      +cy = Laws.cnt_lt(~A, ~le, ys, q)
      +ca = Laws.cnt_lt(~A, ~le, List.append(&2, A, t, ys), q)
      Equal.trans(Nat, Nat.add(i, ca), Nat.add(i, Nat.add(ct, cy)), Nat.add(Nat.add(i, ct), cy), Equal.cong(Nat, Nat, z => Nat.add(i, z), ca, Nat.add(ct, cy), lt_append(~A, ~le, t, ys, q)), Equal.sym(Nat, Nat.add(Nat.add(i, ct), cy), Nat.add(i, Nat.add(ct, cy)), add_assoc(i, ct, cy)))

def le_append(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>, +ys: List<&2, A>, +q: A) -> {Laws.cnt_le(~A, ~le, List.append(&2, A, xs, ys), q) == Nat.add(Laws.cnt_le(~A, ~le, xs, q), Laws.cnt_le(~A, ~le, ys, q)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +i = Laws.ind(le(x, q))
      +ct = Laws.cnt_le(~A, ~le, t, q)
      +cy = Laws.cnt_le(~A, ~le, ys, q)
      +ca = Laws.cnt_le(~A, ~le, List.append(&2, A, t, ys), q)
      Equal.trans(Nat, Nat.add(i, ca), Nat.add(i, Nat.add(ct, cy)), Nat.add(Nat.add(i, ct), cy), Equal.cong(Nat, Nat, z => Nat.add(i, z), ca, Nat.add(ct, cy), le_append(~A, ~le, t, ys, q)), Equal.sym(Nat, Nat.add(Nat.add(i, ct), cy), Nat.add(i, Nat.add(ct, cy)), add_assoc(i, ct, cy)))

# add(a, b) == add(a2, b2) from a == a2 and b == b2
def add_eq(+a: Nat, +a2: Nat, +b: Nat, +b2: Nat, ea: {a == a2 : Nat}, eb: {b == b2 : Nat}) -> {Nat.add(a, b) == Nat.add(a2, b2) : Nat}:
  Equal.trans(Nat, Nat.add(a, b), Nat.add(a2, b), Nat.add(a2, b2), Equal.cong(Nat, Nat, z => Nat.add(z, b), a, a2, ea), Equal.cong(Nat, Nat, z => Nat.add(a2, z), b, b2, eb))

# ---- counts survive the interleave (lt)

def lt2(~A: Data, ~le: A -> A -> Bool, two: S.Two<A>, +q: A) -> Nat:
  S.Two{l, r} = two
  Nat.add(Laws.cnt_lt(~A, ~le, l, q), Laws.cnt_lt(~A, ~le, r, q))

def lt_deal_cons(~A: Data, ~le: A -> A -> Bool, +x: A, +two: S.Two<A>, +q: A) -> {lt2(~A, ~le, S.deal.cons(A, x, two), q) == Nat.add(Laws.ind(Bool.not(le(q, x))), lt2(~A, ~le, two, q)) : Nat}:
  match two:
    case S.Two{+l, +r}:
      +cl = Laws.cnt_lt(~A, ~le, l, q)
      +cr = Laws.cnt_lt(~A, ~le, r, q)
      Equal.trans(Nat, Nat.add(Nat.add(Laws.ind(Bool.not(le(q, x))), cr), cl), Nat.add(Laws.ind(Bool.not(le(q, x))), Nat.add(cr, cl)), Nat.add(Laws.ind(Bool.not(le(q, x))), Nat.add(cl, cr)), add_assoc(Laws.ind(Bool.not(le(q, x))), cr, cl), Equal.cong(Nat, Nat, z => Nat.add(Laws.ind(Bool.not(le(q, x))), z), Nat.add(cr, cl), Nat.add(cl, cr), add_comm(cr, cl)))

def lt_deal(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>, +q: A) -> {lt2(~A, ~le, S.deal(A, xs), q) == Laws.cnt_lt(~A, ~le, xs, q) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.trans(Nat, lt2(~A, ~le, S.deal.cons(A, x, S.deal(A, t)), q), Nat.add(Laws.ind(Bool.not(le(q, x))), lt2(~A, ~le, S.deal(A, t), q)), Nat.add(Laws.ind(Bool.not(le(q, x))), Laws.cnt_lt(~A, ~le, t, q)), lt_deal_cons(~A, ~le, x, S.deal(A, t), q), Equal.cong(Nat, Nat, z => Nat.add(Laws.ind(Bool.not(le(q, x))), z), lt2(~A, ~le, S.deal(A, t), q), Laws.cnt_lt(~A, ~le, t, q), lt_deal(~A, ~le, t, q)))

def lt_shf(~A: Data, ~le: A -> A -> Bool, +k: Nat, +two: S.Two<A>, +q: A) -> {Laws.cnt_lt(~A, ~le, S.shf(A, k, two), q) == lt2(~A, ~le, two, q) : Nat}:
  match k:
    case 0n:
      match two:
        case S.Two{+l, +r}:
          lt_append(~A, ~le, l, r, q)
    case 1n+p:
      match two:
        case S.Two{+l, +r}:
          +sl = S.shf(A, p, S.deal(A, l))
          +sr = S.shf(A, p, S.deal(A, r))
          +el = Equal.trans(Nat, Laws.cnt_lt(~A, ~le, sl, q), lt2(~A, ~le, S.deal(A, l), q), Laws.cnt_lt(~A, ~le, l, q), lt_shf(~A, ~le, p, S.deal(A, l), q), lt_deal(~A, ~le, l, q))
          +er = Equal.trans(Nat, Laws.cnt_lt(~A, ~le, sr, q), lt2(~A, ~le, S.deal(A, r), q), Laws.cnt_lt(~A, ~le, r, q), lt_shf(~A, ~le, p, S.deal(A, r), q), lt_deal(~A, ~le, r, q))
          Equal.trans(Nat, Laws.cnt_lt(~A, ~le, List.append(&2, A, sl, sr), q), Nat.add(Laws.cnt_lt(~A, ~le, sl, q), Laws.cnt_lt(~A, ~le, sr, q)), Nat.add(Laws.cnt_lt(~A, ~le, l, q), Laws.cnt_lt(~A, ~le, r, q)), lt_append(~A, ~le, sl, sr, q), add_eq(Laws.cnt_lt(~A, ~le, sl, q), Laws.cnt_lt(~A, ~le, l, q), Laws.cnt_lt(~A, ~le, sr, q), Laws.cnt_lt(~A, ~le, r, q), el, er))

def lt_shuffle(~A: Data, ~le: A -> A -> Bool, +k: Nat, +xs: List<&2, A>, +q: A) -> {Laws.cnt_lt(~A, ~le, S.shuffle(A, k, xs), q) == Laws.cnt_lt(~A, ~le, xs, q) : Nat}:
  Equal.trans(Nat, Laws.cnt_lt(~A, ~le, S.shf(A, k, S.deal(A, xs)), q), lt2(~A, ~le, S.deal(A, xs), q), Laws.cnt_lt(~A, ~le, xs, q), lt_shf(~A, ~le, k, S.deal(A, xs), q), lt_deal(~A, ~le, xs, q))

# ---- counts survive the interleave (le)

def le2(~A: Data, ~le: A -> A -> Bool, two: S.Two<A>, +q: A) -> Nat:
  S.Two{l, r} = two
  Nat.add(Laws.cnt_le(~A, ~le, l, q), Laws.cnt_le(~A, ~le, r, q))

def le_deal_cons(~A: Data, ~le: A -> A -> Bool, +x: A, +two: S.Two<A>, +q: A) -> {le2(~A, ~le, S.deal.cons(A, x, two), q) == Nat.add(Laws.ind(le(x, q)), le2(~A, ~le, two, q)) : Nat}:
  match two:
    case S.Two{+l, +r}:
      +cl = Laws.cnt_le(~A, ~le, l, q)
      +cr = Laws.cnt_le(~A, ~le, r, q)
      Equal.trans(Nat, Nat.add(Nat.add(Laws.ind(le(x, q)), cr), cl), Nat.add(Laws.ind(le(x, q)), Nat.add(cr, cl)), Nat.add(Laws.ind(le(x, q)), Nat.add(cl, cr)), add_assoc(Laws.ind(le(x, q)), cr, cl), Equal.cong(Nat, Nat, z => Nat.add(Laws.ind(le(x, q)), z), Nat.add(cr, cl), Nat.add(cl, cr), add_comm(cr, cl)))

def le_deal(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>, +q: A) -> {le2(~A, ~le, S.deal(A, xs), q) == Laws.cnt_le(~A, ~le, xs, q) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.trans(Nat, le2(~A, ~le, S.deal.cons(A, x, S.deal(A, t)), q), Nat.add(Laws.ind(le(x, q)), le2(~A, ~le, S.deal(A, t), q)), Nat.add(Laws.ind(le(x, q)), Laws.cnt_le(~A, ~le, t, q)), le_deal_cons(~A, ~le, x, S.deal(A, t), q), Equal.cong(Nat, Nat, z => Nat.add(Laws.ind(le(x, q)), z), le2(~A, ~le, S.deal(A, t), q), Laws.cnt_le(~A, ~le, t, q), le_deal(~A, ~le, t, q)))

def le_shf(~A: Data, ~le: A -> A -> Bool, +k: Nat, +two: S.Two<A>, +q: A) -> {Laws.cnt_le(~A, ~le, S.shf(A, k, two), q) == le2(~A, ~le, two, q) : Nat}:
  match k:
    case 0n:
      match two:
        case S.Two{+l, +r}:
          le_append(~A, ~le, l, r, q)
    case 1n+p:
      match two:
        case S.Two{+l, +r}:
          +sl = S.shf(A, p, S.deal(A, l))
          +sr = S.shf(A, p, S.deal(A, r))
          +el = Equal.trans(Nat, Laws.cnt_le(~A, ~le, sl, q), le2(~A, ~le, S.deal(A, l), q), Laws.cnt_le(~A, ~le, l, q), le_shf(~A, ~le, p, S.deal(A, l), q), le_deal(~A, ~le, l, q))
          +er = Equal.trans(Nat, Laws.cnt_le(~A, ~le, sr, q), le2(~A, ~le, S.deal(A, r), q), Laws.cnt_le(~A, ~le, r, q), le_shf(~A, ~le, p, S.deal(A, r), q), le_deal(~A, ~le, r, q))
          Equal.trans(Nat, Laws.cnt_le(~A, ~le, List.append(&2, A, sl, sr), q), Nat.add(Laws.cnt_le(~A, ~le, sl, q), Laws.cnt_le(~A, ~le, sr, q)), Nat.add(Laws.cnt_le(~A, ~le, l, q), Laws.cnt_le(~A, ~le, r, q)), le_append(~A, ~le, sl, sr, q), add_eq(Laws.cnt_le(~A, ~le, sl, q), Laws.cnt_le(~A, ~le, l, q), Laws.cnt_le(~A, ~le, sr, q), Laws.cnt_le(~A, ~le, r, q), el, er))

def le_shuffle(~A: Data, ~le: A -> A -> Bool, +k: Nat, +xs: List<&2, A>, +q: A) -> {Laws.cnt_le(~A, ~le, S.shuffle(A, k, xs), q) == Laws.cnt_le(~A, ~le, xs, q) : Nat}:
  Equal.trans(Nat, Laws.cnt_le(~A, ~le, S.shf(A, k, S.deal(A, xs)), q), le2(~A, ~le, S.deal(A, xs), q), Laws.cnt_le(~A, ~le, xs, q), le_shf(~A, ~le, k, S.deal(A, xs), q), le_deal(~A, ~le, xs, q))

def false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : Bool.pick(Type, _, Empty, Unit)
  Unit{}

# from b == False and b == True
def clash(+b: Bool, f: {b == False{} : Bool}, t: {b == True{} : Bool}) -> Empty:
  false_ne_true(Equal.trans(Bool, False{}, b, True{}, Equal.sym(Bool, b, False{}, f), t))

# ---- tied values (a <= v and v <= a) compare the same way with every q

def tie_q.f(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +a: A, +v: A, +q: A, e1: {le(a, v) == True{} : Bool}, eb: {le(q, v) == False{} : Bool}, b2: Bool, eb2: {le(q, a) == b2 : Bool}) -> {le(q, a) == False{} : Bool}:
  match b2:
    case False{}:
      eb2
    case True{}:
      Empty.absurd({le(q, a) == False{} : Bool}, clash(le(q, v), eb, le_trans(q, a, v, eb2, e1)))

# le(q, a) == le(q, v)
def tie_q(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +a: A, +v: A, +q: A, e1: {le(a, v) == True{} : Bool}, e2: {le(v, a) == True{} : Bool}, b: Bool, eb: {le(q, v) == b : Bool}) -> {le(q, a) == b : Bool}:
  match b:
    case True{}:
      le_trans(q, v, a, eb, e2)
    case False{}:
      tie_q.f(~A, ~le, ~le_trans, a, v, q, e1, eb, le(q, a), {==})

def tie_r.f(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +a: A, +v: A, +q: A, e2: {le(v, a) == True{} : Bool}, eb: {le(v, q) == False{} : Bool}, b2: Bool, eb2: {le(a, q) == b2 : Bool}) -> {le(a, q) == False{} : Bool}:
  match b2:
    case False{}:
      eb2
    case True{}:
      Empty.absurd({le(a, q) == False{} : Bool}, clash(le(v, q), eb, le_trans(v, a, q, e2, eb2)))

# le(a, q) == le(v, q)
def tie_r(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +a: A, +v: A, +q: A, e1: {le(a, v) == True{} : Bool}, e2: {le(v, a) == True{} : Bool}, b: Bool, eb: {le(v, q) == b : Bool}) -> {le(a, q) == b : Bool}:
  match b:
    case True{}:
      le_trans(a, v, q, e1, eb)
    case False{}:
      tie_r.f(~A, ~le, ~le_trans, a, v, q, e2, eb, le(a, q), {==})

# ---- counts over a tree, with multiplicity

def tlt(~A: Data, ~le: A -> A -> Bool, t: S.Tr<A>, +q: A) -> Nat:
  match t:
    case S.Leaf{}:
      0n
    case S.Node{l, v, c, _, r}:
      Nat.add(tlt(~A, ~le, l, q), Nat.add(Bool.pick(Nat, Bool.not(le(q, v)), c, 0n), tlt(~A, ~le, r, q)))

def tle(~A: Data, ~le: A -> A -> Bool, t: S.Tr<A>, +q: A) -> Nat:
  match t:
    case S.Leaf{}:
      0n
    case S.Node{l, v, c, _, r}:
      Nat.add(tle(~A, ~le, l, q), Nat.add(Bool.pick(Nat, le(v, q), c, 0n), tle(~A, ~le, r, q)))

def tall(-A: Data, t: S.Tr<A>) -> Nat:
  match t:
    case S.Leaf{}:
      0n
    case S.Node{l, _, c, _, r}:
      Nat.add(tall(A, l), Nat.add(c, tall(A, r)))

# ---- inserting a adds [a < q] to the lt count

def lt_eq_case(+L: Nat, +Rr: Nat, +c: Nat, bq: Bool) -> {Nat.add(L, Nat.add(Bool.pick(Nat, Bool.not(bq), 1n+c, 0n), Rr)) == Nat.add(Laws.ind(Bool.not(bq)), Nat.add(L, Nat.add(Bool.pick(Nat, Bool.not(bq), c, 0n), Rr))) : Nat}:
  match bq:
    case True{}:
      {==}
    case False{}:
      add_succ_r(L, Nat.add(c, Rr))

def lt_node(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +l: S.Tr<A>, +v: A, +c: Nat, +s: Nat, +r: S.Tr<A>, +a: A, +q: A, b1: Bool, e1: {le(a, v) == b1 : Bool}, b2: Bool, e2: {le(v, a) == b2 : Bool}, ihl: {tlt(~A, ~le, S.insert(~A, ~le, l, a), q) == Nat.add(Laws.ind(Bool.not(le(q, a))), tlt(~A, ~le, l, q)) : Nat}, ihr: {tlt(~A, ~le, S.insert(~A, ~le, r, a), q) == Nat.add(Laws.ind(Bool.not(le(q, a))), tlt(~A, ~le, r, q)) : Nat}) -> {tlt(~A, ~le, S.ins(~A, ~le, S.Node{l, v, c, s, r}, a, Bool.pick(Cmp, b1, Bool.pick(Cmp, b2, EQ{}, LT{}), GT{})), q) == Nat.add(Laws.ind(Bool.not(le(q, a))), tlt(~A, ~le, S.Node{l, v, c, s, r}, q)) : Nat}:
  match b1 b2:
    case True{} True{}:
      +I = Laws.ind(Bool.not(le(q, a)))
      +L = tlt(~A, ~le, l, q)
      +Rr = tlt(~A, ~le, r, q)
      +P = Bool.pick(Nat, Bool.not(le(q, v)), c, 0n)
      %Equal.sym(Bool, le(q, a), le(q, v), tie_q(~A, ~le, ~le_trans, a, v, q, e1, e2, le(q, v), {==})) : {tlt(~A, ~le, S.Node{l, v, 1n+c, 1n+s, r}, q) == Nat.add(Laws.ind(Bool.not(_)), tlt(~A, ~le, S.Node{l, v, c, s, r}, q)) : Nat}
      lt_eq_case(L, Rr, c, le(q, v))
    case True{} False{}:
      +I = Laws.ind(Bool.not(le(q, a)))
      +L = tlt(~A, ~le, l, q)
      +Rr = tlt(~A, ~le, r, q)
      +P = Bool.pick(Nat, Bool.not(le(q, v)), c, 0n)
      Equal.trans(Nat, Nat.add(tlt(~A, ~le, S.insert(~A, ~le, l, a), q), Nat.add(P, Rr)), Nat.add(Nat.add(I, L), Nat.add(P, Rr)), Nat.add(I, Nat.add(L, Nat.add(P, Rr))), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(P, Rr)), tlt(~A, ~le, S.insert(~A, ~le, l, a), q), Nat.add(I, L), ihl), add_assoc(I, L, Nat.add(P, Rr)))
    case False{} _:
      +I = Laws.ind(Bool.not(le(q, a)))
      +L = tlt(~A, ~le, l, q)
      +Rr = tlt(~A, ~le, r, q)
      +P = Bool.pick(Nat, Bool.not(le(q, v)), c, 0n)
      +T = tlt(~A, ~le, S.insert(~A, ~le, r, a), q)
      +e1 = Equal.cong(Nat, Nat, z => Nat.add(L, Nat.add(P, z)), T, Nat.add(I, Rr), ihr)
      +e2 = Equal.cong(Nat, Nat, z => Nat.add(L, z), Nat.add(P, Nat.add(I, Rr)), Nat.add(I, Nat.add(P, Rr)), add_lcomm(P, I, Rr))
      Equal.trans(Nat, Nat.add(L, Nat.add(P, T)), Nat.add(L, Nat.add(P, Nat.add(I, Rr))), Nat.add(I, Nat.add(L, Nat.add(P, Rr))), e1, Equal.trans(Nat, Nat.add(L, Nat.add(P, Nat.add(I, Rr))), Nat.add(L, Nat.add(I, Nat.add(P, Rr))), Nat.add(I, Nat.add(L, Nat.add(P, Rr))), e2, add_lcomm(L, I, Nat.add(P, Rr))))

def lt_insert(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +t: S.Tr<A>, +a: A, +q: A) -> {tlt(~A, ~le, S.insert(~A, ~le, t, a), q) == Nat.add(Laws.ind(Bool.not(le(q, a))), tlt(~A, ~le, t, q)) : Nat}:
  match t:
    case S.Leaf{}:
      {==}
    case S.Node{+l, +v, +c, +s, +r}:
      lt_node(~A, ~le, ~le_trans, l, v, c, s, r, a, q, le(a, v), {==}, le(v, a), {==}, lt_insert(~A, ~le, ~le_trans, l, a, q), lt_insert(~A, ~le, ~le_trans, r, a, q))

# ---- inserting a adds [a <= q] to the le count

def le_eq_case(+L: Nat, +Rr: Nat, +c: Nat, bq: Bool) -> {Nat.add(L, Nat.add(Bool.pick(Nat, bq, 1n+c, 0n), Rr)) == Nat.add(Laws.ind(bq), Nat.add(L, Nat.add(Bool.pick(Nat, bq, c, 0n), Rr))) : Nat}:
  match bq:
    case True{}:
      add_succ_r(L, Nat.add(c, Rr))
    case False{}:
      {==}

def le_node(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +l: S.Tr<A>, +v: A, +c: Nat, +s: Nat, +r: S.Tr<A>, +a: A, +q: A, b1: Bool, e1: {le(a, v) == b1 : Bool}, b2: Bool, e2: {le(v, a) == b2 : Bool}, ihl: {tle(~A, ~le, S.insert(~A, ~le, l, a), q) == Nat.add(Laws.ind(le(a, q)), tle(~A, ~le, l, q)) : Nat}, ihr: {tle(~A, ~le, S.insert(~A, ~le, r, a), q) == Nat.add(Laws.ind(le(a, q)), tle(~A, ~le, r, q)) : Nat}) -> {tle(~A, ~le, S.ins(~A, ~le, S.Node{l, v, c, s, r}, a, Bool.pick(Cmp, b1, Bool.pick(Cmp, b2, EQ{}, LT{}), GT{})), q) == Nat.add(Laws.ind(le(a, q)), tle(~A, ~le, S.Node{l, v, c, s, r}, q)) : Nat}:
  match b1 b2:
    case True{} True{}:
      +I = Laws.ind(le(a, q))
      +L = tle(~A, ~le, l, q)
      +Rr = tle(~A, ~le, r, q)
      +P = Bool.pick(Nat, le(v, q), c, 0n)
      %Equal.sym(Bool, le(a, q), le(v, q), tie_r(~A, ~le, ~le_trans, a, v, q, e1, e2, le(v, q), {==})) : {tle(~A, ~le, S.Node{l, v, 1n+c, 1n+s, r}, q) == Nat.add(Laws.ind(_), tle(~A, ~le, S.Node{l, v, c, s, r}, q)) : Nat}
      le_eq_case(L, Rr, c, le(v, q))
    case True{} False{}:
      +I = Laws.ind(le(a, q))
      +L = tle(~A, ~le, l, q)
      +Rr = tle(~A, ~le, r, q)
      +P = Bool.pick(Nat, le(v, q), c, 0n)
      Equal.trans(Nat, Nat.add(tle(~A, ~le, S.insert(~A, ~le, l, a), q), Nat.add(P, Rr)), Nat.add(Nat.add(I, L), Nat.add(P, Rr)), Nat.add(I, Nat.add(L, Nat.add(P, Rr))), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(P, Rr)), tle(~A, ~le, S.insert(~A, ~le, l, a), q), Nat.add(I, L), ihl), add_assoc(I, L, Nat.add(P, Rr)))
    case False{} _:
      +I = Laws.ind(le(a, q))
      +L = tle(~A, ~le, l, q)
      +Rr = tle(~A, ~le, r, q)
      +P = Bool.pick(Nat, le(v, q), c, 0n)
      +T = tle(~A, ~le, S.insert(~A, ~le, r, a), q)
      +e1 = Equal.cong(Nat, Nat, z => Nat.add(L, Nat.add(P, z)), T, Nat.add(I, Rr), ihr)
      +e2 = Equal.cong(Nat, Nat, z => Nat.add(L, z), Nat.add(P, Nat.add(I, Rr)), Nat.add(I, Nat.add(P, Rr)), add_lcomm(P, I, Rr))
      Equal.trans(Nat, Nat.add(L, Nat.add(P, T)), Nat.add(L, Nat.add(P, Nat.add(I, Rr))), Nat.add(I, Nat.add(L, Nat.add(P, Rr))), e1, Equal.trans(Nat, Nat.add(L, Nat.add(P, Nat.add(I, Rr))), Nat.add(L, Nat.add(I, Nat.add(P, Rr))), Nat.add(I, Nat.add(L, Nat.add(P, Rr))), e2, add_lcomm(L, I, Nat.add(P, Rr))))

def le_insert(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +t: S.Tr<A>, +a: A, +q: A) -> {tle(~A, ~le, S.insert(~A, ~le, t, a), q) == Nat.add(Laws.ind(le(a, q)), tle(~A, ~le, t, q)) : Nat}:
  match t:
    case S.Leaf{}:
      {==}
    case S.Node{+l, +v, +c, +s, +r}:
      le_node(~A, ~le, ~le_trans, l, v, c, s, r, a, q, le(a, v), {==}, le(v, a), {==}, le_insert(~A, ~le, ~le_trans, l, a, q), le_insert(~A, ~le, ~le_trans, r, a, q))

# ---- the total count

def tall_node(~A: Data, ~le: A -> A -> Bool, +l: S.Tr<A>, +v: A, +c: Nat, +s: Nat, +r: S.Tr<A>, +a: A, b1: Bool, b2: Bool, ihl: {tall(A, S.insert(~A, ~le, l, a)) == 1n+tall(A, l) : Nat}, ihr: {tall(A, S.insert(~A, ~le, r, a)) == 1n+tall(A, r) : Nat}) -> {tall(A, S.ins(~A, ~le, S.Node{l, v, c, s, r}, a, Bool.pick(Cmp, b1, Bool.pick(Cmp, b2, EQ{}, LT{}), GT{}))) == 1n+tall(A, S.Node{l, v, c, s, r}) : Nat}:
  match b1 b2:
    case True{} True{}:
      add_succ_r(tall(A, l), Nat.add(c, tall(A, r)))
    case True{} False{}:
      Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(c, tall(A, r))), tall(A, S.insert(~A, ~le, l, a)), 1n+tall(A, l), ihl)
    case False{} _:
      +L = tall(A, l)
      +T = tall(A, S.insert(~A, ~le, r, a))
      +e1 = Equal.cong(Nat, Nat, z => Nat.add(L, Nat.add(c, z)), T, 1n+tall(A, r), ihr)
      +e2 = Equal.cong(Nat, Nat, z => Nat.add(L, z), Nat.add(c, 1n+tall(A, r)), 1n+Nat.add(c, tall(A, r)), add_succ_r(c, tall(A, r)))
      Equal.trans(Nat, Nat.add(L, Nat.add(c, T)), Nat.add(L, Nat.add(c, 1n+tall(A, r))), 1n+Nat.add(L, Nat.add(c, tall(A, r))), e1, Equal.trans(Nat, Nat.add(L, Nat.add(c, 1n+tall(A, r))), Nat.add(L, 1n+Nat.add(c, tall(A, r))), 1n+Nat.add(L, Nat.add(c, tall(A, r))), e2, add_succ_r(L, Nat.add(c, tall(A, r)))))

def tall_insert(~A: Data, ~le: A -> A -> Bool, +t: S.Tr<A>, +a: A) -> {tall(A, S.insert(~A, ~le, t, a)) == 1n+tall(A, t) : Nat}:
  match t:
    case S.Leaf{}:
      {==}
    case S.Node{+l, +v, +c, +s, +r}:
      tall_node(~A, ~le, l, v, c, s, r, a, le(a, v), le(v, a), tall_insert(~A, ~le, l, a), tall_insert(~A, ~le, r, a))

# ---- build adds the list's lt count

def lt_build(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +xs: List<&2, A>, +t: S.Tr<A>, +q: A) -> {tlt(~A, ~le, S.build(~A, ~le, xs, t), q) == Nat.add(tlt(~A, ~le, t, q), Laws.cnt_lt(~A, ~le, xs, q)) : Nat}:
  match xs:
    case Nil{}:
      Equal.sym(Nat, Nat.add(tlt(~A, ~le, t, q), 0n), tlt(~A, ~le, t, q), add_zero_r(tlt(~A, ~le, t, q)))
    case Con{+x, +rest}:
      +I = Laws.ind(Bool.not(le(q, x)))
      +Tt = tlt(~A, ~le, t, q)
      +C = Laws.cnt_lt(~A, ~le, rest, q)
      +ih = lt_build(~A, ~le, ~le_trans, rest, S.insert(~A, ~le, t, x), q)
      +e1 = Equal.cong(Nat, Nat, z => Nat.add(z, C), tlt(~A, ~le, S.insert(~A, ~le, t, x), q), Nat.add(I, Tt), lt_insert(~A, ~le, ~le_trans, t, x, q))
      +e2 = Equal.trans(Nat, Nat.add(Nat.add(I, Tt), C), Nat.add(I, Nat.add(Tt, C)), Nat.add(Tt, Nat.add(I, C)), add_assoc(I, Tt, C), add_lcomm(I, Tt, C))
      Equal.trans(Nat, tlt(~A, ~le, S.build(~A, ~le, rest, S.insert(~A, ~le, t, x)), q), Nat.add(tlt(~A, ~le, S.insert(~A, ~le, t, x), q), C), Nat.add(Tt, Nat.add(I, C)), ih, Equal.trans(Nat, Nat.add(tlt(~A, ~le, S.insert(~A, ~le, t, x), q), C), Nat.add(Nat.add(I, Tt), C), Nat.add(Tt, Nat.add(I, C)), e1, e2))

# ---- build adds the list's le count

def le_build(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +xs: List<&2, A>, +t: S.Tr<A>, +q: A) -> {tle(~A, ~le, S.build(~A, ~le, xs, t), q) == Nat.add(tle(~A, ~le, t, q), Laws.cnt_le(~A, ~le, xs, q)) : Nat}:
  match xs:
    case Nil{}:
      Equal.sym(Nat, Nat.add(tle(~A, ~le, t, q), 0n), tle(~A, ~le, t, q), add_zero_r(tle(~A, ~le, t, q)))
    case Con{+x, +rest}:
      +I = Laws.ind(le(x, q))
      +Tt = tle(~A, ~le, t, q)
      +C = Laws.cnt_le(~A, ~le, rest, q)
      +ih = le_build(~A, ~le, ~le_trans, rest, S.insert(~A, ~le, t, x), q)
      +e1 = Equal.cong(Nat, Nat, z => Nat.add(z, C), tle(~A, ~le, S.insert(~A, ~le, t, x), q), Nat.add(I, Tt), le_insert(~A, ~le, ~le_trans, t, x, q))
      +e2 = Equal.trans(Nat, Nat.add(Nat.add(I, Tt), C), Nat.add(I, Nat.add(Tt, C)), Nat.add(Tt, Nat.add(I, C)), add_assoc(I, Tt, C), add_lcomm(I, Tt, C))
      Equal.trans(Nat, tle(~A, ~le, S.build(~A, ~le, rest, S.insert(~A, ~le, t, x)), q), Nat.add(tle(~A, ~le, S.insert(~A, ~le, t, x), q), C), Nat.add(Tt, Nat.add(I, C)), ih, Equal.trans(Nat, Nat.add(tle(~A, ~le, S.insert(~A, ~le, t, x), q), C), Nat.add(Nat.add(I, Tt), C), Nat.add(Tt, Nat.add(I, C)), e1, e2))

# ---- the search-tree invariant

# a pair of facts that can be copied
def And(-P: Data, -Q: Data) -> Data:
  Sigma<&2, &2, P, _ => Q>

# every value in t is below w
def AllLt(~A: Data, ~le: A -> A -> Bool, t: S.Tr<A>, +w: A) -> Data:
  match t:
    case S.Leaf{}:
      Unit
    case S.Node{l, x, _, _, r}:
      And({le(w, x) == False{} : Bool}, And(AllLt(~A, ~le, l, w), AllLt(~A, ~le, r, w)))

# every value in t is above w
def AllGt(~A: Data, ~le: A -> A -> Bool, t: S.Tr<A>, +w: A) -> Data:
  match t:
    case S.Leaf{}:
      Unit
    case S.Node{l, x, _, _, r}:
      And({le(x, w) == False{} : Bool}, And(AllGt(~A, ~le, l, w), AllGt(~A, ~le, r, w)))

def Inv(~A: Data, ~le: A -> A -> Bool, t: S.Tr<A>) -> Data:
  match t:
    case S.Leaf{}:
      Unit
    case S.Node{+l, +v, +c, s, +r}:
      And(AllLt(~A, ~le, l, v), And(AllGt(~A, ~le, r, v), And(Inv(~A, ~le, l), And(Inv(~A, ~le, r), {s == Nat.add(tall(A, l), Nat.add(c, tall(A, r))) : Nat}))))

# inserting a value below w keeps every value below w
def alllt_node(~A: Data, ~le: A -> A -> Bool, +l: S.Tr<A>, +v: A, +c: Nat, +s: Nat, +r: S.Tr<A>, +a: A, +w: A, b1: Bool, b2: Bool, +hv: {le(w, v) == False{} : Bool}, +hl: AllLt(~A, ~le, l, w), +hr: AllLt(~A, ~le, r, w), +ihl: AllLt(~A, ~le, S.insert(~A, ~le, l, a), w), +ihr: AllLt(~A, ~le, S.insert(~A, ~le, r, a), w)) -> AllLt(~A, ~le, S.ins(~A, ~le, S.Node{l, v, c, s, r}, a, Bool.pick(Cmp, b1, Bool.pick(Cmp, b2, EQ{}, LT{}), GT{})), w):
  match b1 b2:
    case True{} True{}:
      (hv, hl, hr)
    case True{} False{}:
      (hv, ihl, hr)
    case False{} _:
      (hv, hl, ihr)

def alllt_insert(~A: Data, ~le: A -> A -> Bool, +t: S.Tr<A>, +a: A, +w: A, +h: AllLt(~A, ~le, t, w), +ha: {le(w, a) == False{} : Bool}) -> AllLt(~A, ~le, S.insert(~A, ~le, t, a), w):
  match t:
    case S.Leaf{}:
      (ha, Unit{}, Unit{})
    case S.Node{+l, +v, +c, +s, +r}:
      (hv, hl, hr) = h
      alllt_node(~A, ~le, l, v, c, s, r, a, w, le(a, v), le(v, a), hv, hl, hr, alllt_insert(~A, ~le, l, a, w, hl, ha), alllt_insert(~A, ~le, r, a, w, hr, ha))

# inserting a value above w keeps every value above w
def allgt_node(~A: Data, ~le: A -> A -> Bool, +l: S.Tr<A>, +v: A, +c: Nat, +s: Nat, +r: S.Tr<A>, +a: A, +w: A, b1: Bool, b2: Bool, +hv: {le(v, w) == False{} : Bool}, +hl: AllGt(~A, ~le, l, w), +hr: AllGt(~A, ~le, r, w), +ihl: AllGt(~A, ~le, S.insert(~A, ~le, l, a), w), +ihr: AllGt(~A, ~le, S.insert(~A, ~le, r, a), w)) -> AllGt(~A, ~le, S.ins(~A, ~le, S.Node{l, v, c, s, r}, a, Bool.pick(Cmp, b1, Bool.pick(Cmp, b2, EQ{}, LT{}), GT{})), w):
  match b1 b2:
    case True{} True{}:
      (hv, hl, hr)
    case True{} False{}:
      (hv, ihl, hr)
    case False{} _:
      (hv, hl, ihr)

def allgt_insert(~A: Data, ~le: A -> A -> Bool, +t: S.Tr<A>, +a: A, +w: A, +h: AllGt(~A, ~le, t, w), +ha: {le(a, w) == False{} : Bool}) -> AllGt(~A, ~le, S.insert(~A, ~le, t, a), w):
  match t:
    case S.Leaf{}:
      (ha, Unit{}, Unit{})
    case S.Node{+l, +v, +c, +s, +r}:
      (hv, hl, hr) = h
      allgt_node(~A, ~le, l, v, c, s, r, a, w, le(a, v), le(v, a), hv, hl, hr, allgt_insert(~A, ~le, l, a, w, hl, ha), allgt_insert(~A, ~le, r, a, w, hr, ha))

def inv_node(~A: Data, ~le: A -> A -> Bool, +l: S.Tr<A>, +v: A, +c: Nat, +s: Nat, +r: S.Tr<A>, +a: A, b1: Bool, e1: {le(a, v) == b1 : Bool}, b2: Bool, e2: {le(v, a) == b2 : Bool}, +hl: AllLt(~A, ~le, l, v), +hr: AllGt(~A, ~le, r, v), +il: Inv(~A, ~le, l), +ir: Inv(~A, ~le, r), +hs: {s == Nat.add(tall(A, l), Nat.add(c, tall(A, r))) : Nat}, +ivl: Inv(~A, ~le, S.insert(~A, ~le, l, a)), +ivr: Inv(~A, ~le, S.insert(~A, ~le, r, a))) -> Inv(~A, ~le, S.ins(~A, ~le, S.Node{l, v, c, s, r}, a, Bool.pick(Cmp, b1, Bool.pick(Cmp, b2, EQ{}, LT{}), GT{}))):
  match b1 b2:
    case True{} True{}:
      +L = tall(A, l)
      +X = Nat.add(c, tall(A, r))
      (hl, hr, il, ir, Equal.trans(Nat, 1n+s, 1n+Nat.add(L, X), Nat.add(L, 1n+X), Equal.cong(Nat, Nat, z => 1n+z, s, Nat.add(L, X), hs), Equal.sym(Nat, Nat.add(L, 1n+X), 1n+Nat.add(L, X), add_succ_r(L, X))))
    case True{} False{}:
      +L = tall(A, l)
      +X = Nat.add(c, tall(A, r))
      +TL = tall(A, S.insert(~A, ~le, l, a))
      (alllt_insert(~A, ~le, l, a, v, hl, e2), hr, ivl, ir, Equal.trans(Nat, 1n+s, 1n+Nat.add(L, X), Nat.add(TL, X), Equal.cong(Nat, Nat, z => 1n+z, s, Nat.add(L, X), hs), Equal.cong(Nat, Nat, z => Nat.add(z, X), 1n+L, TL, Equal.sym(Nat, TL, 1n+L, tall_insert(~A, ~le, l, a)))))
    case False{} _:
      +L = tall(A, l)
      +Rr = tall(A, r)
      +TR = tall(A, S.insert(~A, ~le, r, a))
      +e_a = Equal.trans(Nat, 1n+s, 1n+Nat.add(L, Nat.add(c, Rr)), Nat.add(L, 1n+Nat.add(c, Rr)), Equal.cong(Nat, Nat, z => 1n+z, s, Nat.add(L, Nat.add(c, Rr)), hs), Equal.sym(Nat, Nat.add(L, 1n+Nat.add(c, Rr)), 1n+Nat.add(L, Nat.add(c, Rr)), add_succ_r(L, Nat.add(c, Rr))))
      +e_b = Equal.cong(Nat, Nat, z => Nat.add(L, z), 1n+Nat.add(c, Rr), Nat.add(c, 1n+Rr), Equal.sym(Nat, Nat.add(c, 1n+Rr), 1n+Nat.add(c, Rr), add_succ_r(c, Rr)))
      +e_c = Equal.cong(Nat, Nat, z => Nat.add(L, Nat.add(c, z)), 1n+Rr, TR, Equal.sym(Nat, TR, 1n+Rr, tall_insert(~A, ~le, r, a)))
      (hl, allgt_insert(~A, ~le, r, a, v, hr, e1), il, ivr, Equal.trans(Nat, 1n+s, Nat.add(L, 1n+Nat.add(c, Rr)), Nat.add(L, Nat.add(c, TR)), e_a, Equal.trans(Nat, Nat.add(L, 1n+Nat.add(c, Rr)), Nat.add(L, Nat.add(c, 1n+Rr)), Nat.add(L, Nat.add(c, TR)), e_b, e_c)))

def inv_insert(~A: Data, ~le: A -> A -> Bool, +t: S.Tr<A>, +a: A, +h: Inv(~A, ~le, t)) -> Inv(~A, ~le, S.insert(~A, ~le, t, a)):
  match t:
    case S.Leaf{}:
      (Unit{}, Unit{}, Unit{}, Unit{}, {==})
    case S.Node{+l, +v, +c, +s, +r}:
      (hl, hr, il, ir, hs) = h
      inv_node(~A, ~le, l, v, c, s, r, a, le(a, v), {==}, le(v, a), {==}, hl, hr, il, ir, hs, inv_insert(~A, ~le, l, a, il), inv_insert(~A, ~le, r, a, ir))

def inv_build(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>, +t: S.Tr<A>, +h: Inv(~A, ~le, t)) -> Inv(~A, ~le, S.build(~A, ~le, xs, t)):
  match xs:
    case Nil{}:
      h
    case Con{+x, +rest}:
      inv_build(~A, ~le, rest, S.insert(~A, ~le, t, x), inv_insert(~A, ~le, t, x, h))

# ---- four facts of a total order, with x < y meaning not le(y, x)

# x < v and v < q give x < q
def ord_a.go(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +x: A, +v: A, +q: A, h1: {le(v, x) == False{} : Bool}, h2: {le(q, v) == False{} : Bool}, b: Bool, eb: {le(q, x) == b : Bool}) -> {le(q, x) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      Empty.absurd({le(q, x) == False{} : Bool}, clash(le(q, v), h2, le_trans(q, x, v, eb, le_total(v, x, h1))))

def ord_a(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +x: A, +v: A, +q: A, h1: {le(v, x) == False{} : Bool}, h2: {le(q, v) == False{} : Bool}) -> {le(q, x) == False{} : Bool}:
  ord_a.go(~A, ~le, ~le_total, ~le_trans, x, v, q, h1, h2, le(q, x), {==})

# v < x and q <= v give q <= x
def ord_b(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +x: A, +v: A, +q: A, h1: {le(x, v) == False{} : Bool}, h2: {le(q, v) == True{} : Bool}) -> {le(q, x) == True{} : Bool}:
  le_trans(q, v, x, h2, le_total(x, v, h1))

# x < v and v <= q give x <= q
def ord_c(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +x: A, +v: A, +q: A, h1: {le(v, x) == False{} : Bool}, h2: {le(v, q) == True{} : Bool}) -> {le(x, q) == True{} : Bool}:
  le_trans(x, v, q, le_total(v, x, h1), h2)

# v < x and q < v give not x <= q
def ord_d.go(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +x: A, +v: A, +q: A, h1: {le(x, v) == False{} : Bool}, h2: {le(v, q) == False{} : Bool}, b: Bool, eb: {le(x, q) == b : Bool}) -> {le(x, q) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      Empty.absurd({le(x, q) == False{} : Bool}, clash(le(x, v), h1, le_trans(x, q, v, eb, le_total(v, q, h2))))

def ord_d(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +x: A, +v: A, +q: A, h1: {le(x, v) == False{} : Bool}, h2: {le(v, q) == False{} : Bool}) -> {le(x, q) == False{} : Bool}:
  ord_d.go(~A, ~le, ~le_total, ~le_trans, x, v, q, h1, h2, le(x, q), {==})

def lt_all(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +t: S.Tr<A>, +v: A, +q: A, +h: AllLt(~A, ~le, t, v), +hq: {le(q, v) == False{} : Bool}) -> {tlt(~A, ~le, t, q) == tall(A, t) : Nat}:
  match t:
    case S.Leaf{}:
      {==}
    case S.Node{+l, +x, +c, s, +r}:
      (hx, hlr) = h
      (hl, hr) = hlr
      +ex = ord_a(~A, ~le, ~le_total, ~le_trans, x, v, q, hx, hq)
      %Equal.sym(Bool, le(q, x), False{}, ex) : {Nat.add(tlt(~A, ~le, l, q), Nat.add(Bool.pick(Nat, Bool.not(_), c, 0n), tlt(~A, ~le, r, q))) == tall(A, S.Node{l, x, c, s, r}) : Nat}
      add_eq(tlt(~A, ~le, l, q), tall(A, l), Nat.add(c, tlt(~A, ~le, r, q)), Nat.add(c, tall(A, r)), lt_all(~A, ~le, ~le_total, ~le_trans, l, v, q, hl, hq), Equal.cong(Nat, Nat, z => Nat.add(c, z), tlt(~A, ~le, r, q), tall(A, r), lt_all(~A, ~le, ~le_total, ~le_trans, r, v, q, hr, hq)))

def lt_none(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +t: S.Tr<A>, +v: A, +q: A, +h: AllGt(~A, ~le, t, v), +hq: {le(q, v) == True{} : Bool}) -> {tlt(~A, ~le, t, q) == 0n : Nat}:
  match t:
    case S.Leaf{}:
      {==}
    case S.Node{+l, +x, +c, s, +r}:
      (hx, hlr) = h
      (hl, hr) = hlr
      +ex = ord_b(~A, ~le, ~le_total, ~le_trans, x, v, q, hx, hq)
      %Equal.sym(Bool, le(q, x), True{}, ex) : {Nat.add(tlt(~A, ~le, l, q), Nat.add(Bool.pick(Nat, Bool.not(_), c, 0n), tlt(~A, ~le, r, q))) == 0n : Nat}
      add_eq(tlt(~A, ~le, l, q), 0n, tlt(~A, ~le, r, q), 0n, lt_none(~A, ~le, ~le_total, ~le_trans, l, v, q, hl, hq), lt_none(~A, ~le, ~le_total, ~le_trans, r, v, q, hr, hq))

def le_all(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +t: S.Tr<A>, +v: A, +q: A, +h: AllLt(~A, ~le, t, v), +hq: {le(v, q) == True{} : Bool}) -> {tle(~A, ~le, t, q) == tall(A, t) : Nat}:
  match t:
    case S.Leaf{}:
      {==}
    case S.Node{+l, +x, +c, s, +r}:
      (hx, hlr) = h
      (hl, hr) = hlr
      +ex = ord_c(~A, ~le, ~le_total, ~le_trans, x, v, q, hx, hq)
      %Equal.sym(Bool, le(x, q), True{}, ex) : {Nat.add(tle(~A, ~le, l, q), Nat.add(Bool.pick(Nat, _, c, 0n), tle(~A, ~le, r, q))) == tall(A, S.Node{l, x, c, s, r}) : Nat}
      add_eq(tle(~A, ~le, l, q), tall(A, l), Nat.add(c, tle(~A, ~le, r, q)), Nat.add(c, tall(A, r)), le_all(~A, ~le, ~le_total, ~le_trans, l, v, q, hl, hq), Equal.cong(Nat, Nat, z => Nat.add(c, z), tle(~A, ~le, r, q), tall(A, r), le_all(~A, ~le, ~le_total, ~le_trans, r, v, q, hr, hq)))

def le_none(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +t: S.Tr<A>, +v: A, +q: A, +h: AllGt(~A, ~le, t, v), +hq: {le(v, q) == False{} : Bool}) -> {tle(~A, ~le, t, q) == 0n : Nat}:
  match t:
    case S.Leaf{}:
      {==}
    case S.Node{+l, +x, +c, s, +r}:
      (hx, hlr) = h
      (hl, hr) = hlr
      +ex = ord_d(~A, ~le, ~le_total, ~le_trans, x, v, q, hx, hq)
      %Equal.sym(Bool, le(x, q), False{}, ex) : {Nat.add(tle(~A, ~le, l, q), Nat.add(Bool.pick(Nat, _, c, 0n), tle(~A, ~le, r, q))) == 0n : Nat}
      add_eq(tle(~A, ~le, l, q), 0n, tle(~A, ~le, r, q), 0n, le_none(~A, ~le, ~le_total, ~le_trans, l, v, q, hl, hq), le_none(~A, ~le, ~le_total, ~le_trans, r, v, q, hr, hq))

# the stored size is the true size
def tsize_ok(~A: Data, ~le: A -> A -> Bool, +t: S.Tr<A>, +h: Inv(~A, ~le, t)) -> {S.tsize(A, t) == tall(A, t) : Nat}:
  match t:
    case S.Leaf{}:
      {==}
    case S.Node{l, v, c, s, r}:
      (_, h1) = h
      (_, h2) = h1
      (_, h3) = h2
      (_, hs) = h3
      hs

def dlt_node(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +l: S.Tr<A>, +v: A, +c: Nat, +s: Nat, +r: S.Tr<A>, +q: A, b: Bool, eb: {le(q, v) == b : Bool}, +hl: AllLt(~A, ~le, l, v), +hr: AllGt(~A, ~le, r, v), +il: Inv(~A, ~le, l), +ihl: {S.dlt(~A, ~le, l, q, S.root_lt(~A, ~le, l, q)) == tlt(~A, ~le, l, q) : Nat}, +ihr: {S.dlt(~A, ~le, r, q, S.root_lt(~A, ~le, r, q)) == tlt(~A, ~le, r, q) : Nat}) -> {S.dlt(~A, ~le, S.Node{l, v, c, s, r}, q, Bool.not(b)) == Nat.add(tlt(~A, ~le, l, q), Nat.add(Bool.pick(Nat, Bool.not(b), c, 0n), tlt(~A, ~le, r, q))) : Nat}:
  match b:
    case False{}:
      +ea = Equal.trans(Nat, S.tsize(A, l), tall(A, l), tlt(~A, ~le, l, q), tsize_ok(~A, ~le, l, il), Equal.sym(Nat, tlt(~A, ~le, l, q), tall(A, l), lt_all(~A, ~le, ~le_total, ~le_trans, l, v, q, hl, eb)))
      add_eq(S.tsize(A, l), tlt(~A, ~le, l, q), Nat.add(c, S.dlt(~A, ~le, r, q, S.root_lt(~A, ~le, r, q))), Nat.add(c, tlt(~A, ~le, r, q)), ea, Equal.cong(Nat, Nat, z => Nat.add(c, z), S.dlt(~A, ~le, r, q, S.root_lt(~A, ~le, r, q)), tlt(~A, ~le, r, q), ihr))
    case True{}:
      +Ll = tlt(~A, ~le, l, q)
      +e0 = Equal.trans(Nat, S.dlt(~A, ~le, l, q, S.root_lt(~A, ~le, l, q)), Ll, Nat.add(Ll, 0n), ihl, Equal.sym(Nat, Nat.add(Ll, 0n), Ll, add_zero_r(Ll)))
      Equal.trans(Nat, S.dlt(~A, ~le, l, q, S.root_lt(~A, ~le, l, q)), Nat.add(Ll, 0n), Nat.add(Ll, tlt(~A, ~le, r, q)), e0, Equal.cong(Nat, Nat, z => Nat.add(Ll, z), 0n, tlt(~A, ~le, r, q), Equal.sym(Nat, tlt(~A, ~le, r, q), 0n, lt_none(~A, ~le, ~le_total, ~le_trans, r, v, q, hr, eb))))

# the walk returns the true count
def dlt_ok(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +t: S.Tr<A>, +q: A, +h: Inv(~A, ~le, t)) -> {S.dlt(~A, ~le, t, q, S.root_lt(~A, ~le, t, q)) == tlt(~A, ~le, t, q) : Nat}:
  match t:
    case S.Leaf{}:
      {==}
    case S.Node{+l, +v, +c, +s, +r}:
      (hl, h1) = h
      (hr, h2) = h1
      (il, h3) = h2
      (ir, _) = h3
      dlt_node(~A, ~le, ~le_total, ~le_trans, l, v, c, s, r, q, le(q, v), {==}, hl, hr, il, dlt_ok(~A, ~le, ~le_total, ~le_trans, l, q, il), dlt_ok(~A, ~le, ~le_total, ~le_trans, r, q, ir))

def dle_node(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +l: S.Tr<A>, +v: A, +c: Nat, +s: Nat, +r: S.Tr<A>, +q: A, b: Bool, eb: {le(v, q) == b : Bool}, +hl: AllLt(~A, ~le, l, v), +hr: AllGt(~A, ~le, r, v), +il: Inv(~A, ~le, l), +ihl: {S.dle(~A, ~le, l, q, S.root_le(~A, ~le, l, q)) == tle(~A, ~le, l, q) : Nat}, +ihr: {S.dle(~A, ~le, r, q, S.root_le(~A, ~le, r, q)) == tle(~A, ~le, r, q) : Nat}) -> {S.dle(~A, ~le, S.Node{l, v, c, s, r}, q, b) == Nat.add(tle(~A, ~le, l, q), Nat.add(Bool.pick(Nat, b, c, 0n), tle(~A, ~le, r, q))) : Nat}:
  match b:
    case True{}:
      +ea = Equal.trans(Nat, S.tsize(A, l), tall(A, l), tle(~A, ~le, l, q), tsize_ok(~A, ~le, l, il), Equal.sym(Nat, tle(~A, ~le, l, q), tall(A, l), le_all(~A, ~le, ~le_total, ~le_trans, l, v, q, hl, eb)))
      add_eq(S.tsize(A, l), tle(~A, ~le, l, q), Nat.add(c, S.dle(~A, ~le, r, q, S.root_le(~A, ~le, r, q))), Nat.add(c, tle(~A, ~le, r, q)), ea, Equal.cong(Nat, Nat, z => Nat.add(c, z), S.dle(~A, ~le, r, q, S.root_le(~A, ~le, r, q)), tle(~A, ~le, r, q), ihr))
    case False{}:
      +Ll = tle(~A, ~le, l, q)
      +e0 = Equal.trans(Nat, S.dle(~A, ~le, l, q, S.root_le(~A, ~le, l, q)), Ll, Nat.add(Ll, 0n), ihl, Equal.sym(Nat, Nat.add(Ll, 0n), Ll, add_zero_r(Ll)))
      Equal.trans(Nat, S.dle(~A, ~le, l, q, S.root_le(~A, ~le, l, q)), Nat.add(Ll, 0n), Nat.add(Ll, tle(~A, ~le, r, q)), e0, Equal.cong(Nat, Nat, z => Nat.add(Ll, z), 0n, tle(~A, ~le, r, q), Equal.sym(Nat, tle(~A, ~le, r, q), 0n, le_none(~A, ~le, ~le_total, ~le_trans, r, v, q, hr, eb))))

# the walk returns the true count
def dle_ok(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +t: S.Tr<A>, +q: A, +h: Inv(~A, ~le, t)) -> {S.dle(~A, ~le, t, q, S.root_le(~A, ~le, t, q)) == tle(~A, ~le, t, q) : Nat}:
  match t:
    case S.Leaf{}:
      {==}
    case S.Node{+l, +v, +c, +s, +r}:
      (hl, h1) = h
      (hr, h2) = h1
      (il, h3) = h2
      (ir, _) = h3
      dle_node(~A, ~le, ~le_total, ~le_trans, l, v, c, s, r, q, le(v, q), {==}, hl, hr, il, dle_ok(~A, ~le, ~le_total, ~le_trans, l, q, il), dle_ok(~A, ~le, ~le_total, ~le_trans, r, q, ir))

# ---- the result: 2 x the average rank of q is 1 + #{x < q} + #{x <= q}

def rank_count(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +xs: List<&2, A>, +q: A) -> {S.rank_of(~A, ~le, S.tree(~A, ~le, xs), q) == 1n+Nat.add(Laws.cnt_lt(~A, ~le, xs, q), Laws.cnt_le(~A, ~le, xs, q)) : Nat}:
  +k = U32.log2(U32.from_nat(List.length(&2, A, xs)))
  +sh = S.shuffle(A, k, xs)
  +t = S.build(~A, ~le, sh, S.Leaf{})
  +iv = inv_build(~A, ~le, sh, S.Leaf{}, Unit{})
  +elt = Equal.trans(Nat, S.dlt(~A, ~le, t, q, S.root_lt(~A, ~le, t, q)), tlt(~A, ~le, t, q), Laws.cnt_lt(~A, ~le, xs, q), dlt_ok(~A, ~le, ~le_total, ~le_trans, t, q, iv), Equal.trans(Nat, tlt(~A, ~le, t, q), Laws.cnt_lt(~A, ~le, sh, q), Laws.cnt_lt(~A, ~le, xs, q), lt_build(~A, ~le, ~le_trans, sh, S.Leaf{}, q), lt_shuffle(~A, ~le, k, xs, q)))
  +ele = Equal.trans(Nat, S.dle(~A, ~le, t, q, S.root_le(~A, ~le, t, q)), tle(~A, ~le, t, q), Laws.cnt_le(~A, ~le, xs, q), dle_ok(~A, ~le, ~le_total, ~le_trans, t, q, iv), Equal.trans(Nat, tle(~A, ~le, t, q), Laws.cnt_le(~A, ~le, sh, q), Laws.cnt_le(~A, ~le, xs, q), le_build(~A, ~le, ~le_trans, sh, S.Leaf{}, q), le_shuffle(~A, ~le, k, xs, q)))
  Equal.cong(Nat, Nat, z => 1n+z, Nat.add(S.dlt(~A, ~le, t, q, S.root_lt(~A, ~le, t, q)), S.dle(~A, ~le, t, q, S.root_le(~A, ~le, t, q))), Nat.add(Laws.cnt_lt(~A, ~le, xs, q), Laws.cnt_le(~A, ~le, xs, q)), add_eq(S.dlt(~A, ~le, t, q, S.root_lt(~A, ~le, t, q)), Laws.cnt_lt(~A, ~le, xs, q), S.dle(~A, ~le, t, q, S.root_le(~A, ~le, t, q)), Laws.cnt_le(~A, ~le, xs, q), elt, ele))

# ---- a concrete order, so --verdict has a model for the template proofs

def nat_le_total(x: Nat, y: Nat, h: {Nat.is_le(x, y) == False{} : Bool}) -> {Nat.is_le(y, x) == True{} : Bool}:
  match x y:
    case 0n 0n:
      Empty.absurd({Nat.is_le(0n, 0n) == True{} : Bool}, false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
    case 0n 1n+b:
      Empty.absurd({Nat.is_le(1n+b, 0n) == True{} : Bool}, false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
    case 1n+a 0n:
      {==}
    case 1n+a 1n+b:
      nat_le_total(a, b, h)

def nat_le_trans(x: Nat, y: Nat, z: Nat, h1: {Nat.is_le(x, y) == True{} : Bool}, h2: {Nat.is_le(y, z) == True{} : Bool}) -> {Nat.is_le(x, z) == True{} : Bool}:
  match x y z:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+c:
      {==}
    case 0n 1n+b 0n:
      {==}
    case 0n 1n+b 1n+c:
      {==}
    case 1n+a 0n _:
      Empty.absurd({Nat.is_le(1n+a, z) == True{} : Bool}, false_ne_true(h1))
    case 1n+a 1n+b 0n:
      Empty.absurd({Nat.is_le(1n+a, 0n) == True{} : Bool}, false_ne_true(h2))
    case 1n+a 1n+b 1n+c:
      nat_le_trans(a, b, c, h1, h2)
