# The proof of law rank_pairs: the two-sort rank IC pairs each x rank with its
# y rank. The merge sort keeps every sum over the list and returns it sorted;
# the walk over runs of a sorted list gives each value its average rank.
# Generic over a comparison le; each fact of the order comes from le_total and
# le_trans.
import Base
import ./LAWS.bend as Laws
import ./signal.bend as S
import ./ranks_proof.bend as RP

# a sum over a list; c carries what f needs besides the element
def tot(~T: Data, ~C: Data, ~f: C -> T -> Nat, +c: C, xs: List<&2, T>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, t}:
      Nat.add(f(c, x), tot(~T, ~C, ~f, c, t))

# ---- the sort keeps every sum

def tot_mrg(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~C: Data, ~f: C -> S.KV<A, B> -> Nat, +c: C, +xt: List<&2, S.KV<A, B>>, +yt: List<&2, S.KV<A, B>>, +x: S.KV<A, B>, +y: S.KV<A, B>, d: Bool) -> {tot(~S.KV<A, B>, ~C, ~f, c, S.mrg(~A, ~B, ~le, xt, yt, x, y, d)) == Nat.add(tot(~S.KV<A, B>, ~C, ~f, c, x <> xt), tot(~S.KV<A, B>, ~C, ~f, c, y <> yt)) : Nat}:
  match xt yt d:
    case Nil{} _ True{}:
      Equal.cong(Nat, Nat, z => Nat.add(z, tot(~S.KV<A, B>, ~C, ~f, c, y <> yt)), f(c, x), Nat.add(f(c, x), 0n), Equal.sym(Nat, Nat.add(f(c, x), 0n), f(c, x), RP.add_zero_r(f(c, x))))
    case Con{+a, +at} _ True{}:
      +fx = f(c, x)
      +ta = tot(~S.KV<A, B>, ~C, ~f, c, a <> at)
      +ty = tot(~S.KV<A, B>, ~C, ~f, c, y <> yt)
      Equal.trans(Nat, Nat.add(fx, tot(~S.KV<A, B>, ~C, ~f, c, S.mrg(~A, ~B, ~le, at, yt, a, y, S.kle(~A, ~B, ~le, a, y)))), Nat.add(fx, Nat.add(ta, ty)), Nat.add(Nat.add(fx, ta), ty), Equal.cong(Nat, Nat, z => Nat.add(fx, z), tot(~S.KV<A, B>, ~C, ~f, c, S.mrg(~A, ~B, ~le, at, yt, a, y, S.kle(~A, ~B, ~le, a, y))), Nat.add(ta, ty), tot_mrg(~A, ~B, ~le, ~C, ~f, c, at, yt, a, y, S.kle(~A, ~B, ~le, a, y))), Equal.sym(Nat, Nat.add(Nat.add(fx, ta), ty), Nat.add(fx, Nat.add(ta, ty)), RP.add_assoc(fx, ta, ty)))
    case _ Nil{} False{}:
      +fy = f(c, y)
      +tx = tot(~S.KV<A, B>, ~C, ~f, c, x <> xt)
      Equal.trans(Nat, Nat.add(fy, tx), Nat.add(tx, fy), Nat.add(tx, Nat.add(fy, 0n)), RP.add_comm(fy, tx), Equal.cong(Nat, Nat, z => Nat.add(tx, z), fy, Nat.add(fy, 0n), Equal.sym(Nat, Nat.add(fy, 0n), fy, RP.add_zero_r(fy))))
    case _ Con{+b, +bt} False{}:
      +fy = f(c, y)
      +tx = tot(~S.KV<A, B>, ~C, ~f, c, x <> xt)
      +tb = tot(~S.KV<A, B>, ~C, ~f, c, b <> bt)
      Equal.trans(Nat, Nat.add(fy, tot(~S.KV<A, B>, ~C, ~f, c, S.mrg(~A, ~B, ~le, xt, bt, x, b, S.kle(~A, ~B, ~le, x, b)))), Nat.add(fy, Nat.add(tx, tb)), Nat.add(tx, Nat.add(fy, tb)), Equal.cong(Nat, Nat, z => Nat.add(fy, z), tot(~S.KV<A, B>, ~C, ~f, c, S.mrg(~A, ~B, ~le, xt, bt, x, b, S.kle(~A, ~B, ~le, x, b))), Nat.add(tx, tb), tot_mrg(~A, ~B, ~le, ~C, ~f, c, xt, bt, x, b, S.kle(~A, ~B, ~le, x, b))), RP.add_lcomm(fy, tx, tb))

def tot_merge(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~C: Data, ~f: C -> S.KV<A, B> -> Nat, +c: C, +xs: List<&2, S.KV<A, B>>, +ys: List<&2, S.KV<A, B>>) -> {tot(~S.KV<A, B>, ~C, ~f, c, S.merge(~A, ~B, ~le, xs, ys)) == Nat.add(tot(~S.KV<A, B>, ~C, ~f, c, xs), tot(~S.KV<A, B>, ~C, ~f, c, ys)) : Nat}:
  match xs ys:
    case Nil{} _:
      {==}
    case Con{+x, +xt} Nil{}:
      Equal.sym(Nat, Nat.add(tot(~S.KV<A, B>, ~C, ~f, c, x <> xt), 0n), tot(~S.KV<A, B>, ~C, ~f, c, x <> xt), RP.add_zero_r(tot(~S.KV<A, B>, ~C, ~f, c, x <> xt)))
    case Con{+x, +xt} Con{+y, +yt}:
      tot_mrg(~A, ~B, ~le, ~C, ~f, c, xt, yt, x, y, S.kle(~A, ~B, ~le, x, y))

def tot_isort(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~C: Data, ~f: C -> S.KV<A, B> -> Nat, +c: C, +xs: List<&2, S.KV<A, B>>) -> {tot(~S.KV<A, B>, ~C, ~f, c, S.isort(~A, ~B, ~le, xs)) == tot(~S.KV<A, B>, ~C, ~f, c, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +fx = f(c, x)
      +ti = tot(~S.KV<A, B>, ~C, ~f, c, S.isort(~A, ~B, ~le, t))
      Equal.trans(Nat, tot(~S.KV<A, B>, ~C, ~f, c, S.merge(~A, ~B, ~le, x <> Nil{}, S.isort(~A, ~B, ~le, t))), Nat.add(Nat.add(fx, 0n), ti), Nat.add(fx, tot(~S.KV<A, B>, ~C, ~f, c, t)), tot_merge(~A, ~B, ~le, ~C, ~f, c, x <> Nil{}, S.isort(~A, ~B, ~le, t)), RP.add_eq(Nat.add(fx, 0n), fx, ti, tot(~S.KV<A, B>, ~C, ~f, c, t), RP.add_zero_r(fx), tot_isort(~A, ~B, ~le, ~C, ~f, c, t)))

def tot2(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~C: Data, ~f: C -> S.KV<A, B> -> Nat, +c: C, two: S.Two<S.KV<A, B>>) -> Nat:
  S.Two{l, r} = two
  Nat.add(tot(~S.KV<A, B>, ~C, ~f, c, l), tot(~S.KV<A, B>, ~C, ~f, c, r))

def tot_deal_cons(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~C: Data, ~f: C -> S.KV<A, B> -> Nat, +c: C, +x: S.KV<A, B>, +two: S.Two<S.KV<A, B>>) -> {tot2(~A, ~B, ~le, ~C, ~f, c, S.deal.cons(S.KV<A, B>, x, two)) == Nat.add(f(c, x), tot2(~A, ~B, ~le, ~C, ~f, c, two)) : Nat}:
  match two:
    case S.Two{+l, +r}:
      +fx = f(c, x)
      +cl = tot(~S.KV<A, B>, ~C, ~f, c, l)
      +cr = tot(~S.KV<A, B>, ~C, ~f, c, r)
      Equal.trans(Nat, Nat.add(Nat.add(fx, cr), cl), Nat.add(fx, Nat.add(cr, cl)), Nat.add(fx, Nat.add(cl, cr)), RP.add_assoc(fx, cr, cl), Equal.cong(Nat, Nat, z => Nat.add(fx, z), Nat.add(cr, cl), Nat.add(cl, cr), RP.add_comm(cr, cl)))

def tot_deal(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~C: Data, ~f: C -> S.KV<A, B> -> Nat, +c: C, +xs: List<&2, S.KV<A, B>>) -> {tot2(~A, ~B, ~le, ~C, ~f, c, S.deal(S.KV<A, B>, xs)) == tot(~S.KV<A, B>, ~C, ~f, c, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.trans(Nat, tot2(~A, ~B, ~le, ~C, ~f, c, S.deal.cons(S.KV<A, B>, x, S.deal(S.KV<A, B>, t))), Nat.add(f(c, x), tot2(~A, ~B, ~le, ~C, ~f, c, S.deal(S.KV<A, B>, t))), Nat.add(f(c, x), tot(~S.KV<A, B>, ~C, ~f, c, t)), tot_deal_cons(~A, ~B, ~le, ~C, ~f, c, x, S.deal(S.KV<A, B>, t)), Equal.cong(Nat, Nat, z => Nat.add(f(c, x), z), tot2(~A, ~B, ~le, ~C, ~f, c, S.deal(S.KV<A, B>, t)), tot(~S.KV<A, B>, ~C, ~f, c, t), tot_deal(~A, ~B, ~le, ~C, ~f, c, t)))

def tot_msorted(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~C: Data, ~f: C -> S.KV<A, B> -> Nat, +c: C, +k: Nat, +two: S.Two<S.KV<A, B>>) -> {tot(~S.KV<A, B>, ~C, ~f, c, S.msorted(~A, ~B, ~le, k, two)) == tot2(~A, ~B, ~le, ~C, ~f, c, two) : Nat}:
  match k:
    case 0n:
      match two:
        case S.Two{+l, +r}:
          Equal.trans(Nat, tot(~S.KV<A, B>, ~C, ~f, c, S.merge(~A, ~B, ~le, S.isort(~A, ~B, ~le, l), S.isort(~A, ~B, ~le, r))), Nat.add(tot(~S.KV<A, B>, ~C, ~f, c, S.isort(~A, ~B, ~le, l)), tot(~S.KV<A, B>, ~C, ~f, c, S.isort(~A, ~B, ~le, r))), Nat.add(tot(~S.KV<A, B>, ~C, ~f, c, l), tot(~S.KV<A, B>, ~C, ~f, c, r)), tot_merge(~A, ~B, ~le, ~C, ~f, c, S.isort(~A, ~B, ~le, l), S.isort(~A, ~B, ~le, r)), RP.add_eq(tot(~S.KV<A, B>, ~C, ~f, c, S.isort(~A, ~B, ~le, l)), tot(~S.KV<A, B>, ~C, ~f, c, l), tot(~S.KV<A, B>, ~C, ~f, c, S.isort(~A, ~B, ~le, r)), tot(~S.KV<A, B>, ~C, ~f, c, r), tot_isort(~A, ~B, ~le, ~C, ~f, c, l), tot_isort(~A, ~B, ~le, ~C, ~f, c, r)))
    case 1n+p:
      match two:
        case S.Two{+l, +r}:
          +ml = S.msorted(~A, ~B, ~le, p, S.deal(S.KV<A, B>, l))
          +mr = S.msorted(~A, ~B, ~le, p, S.deal(S.KV<A, B>, r))
          +el = Equal.trans(Nat, tot(~S.KV<A, B>, ~C, ~f, c, ml), tot2(~A, ~B, ~le, ~C, ~f, c, S.deal(S.KV<A, B>, l)), tot(~S.KV<A, B>, ~C, ~f, c, l), tot_msorted(~A, ~B, ~le, ~C, ~f, c, p, S.deal(S.KV<A, B>, l)), tot_deal(~A, ~B, ~le, ~C, ~f, c, l))
          +er = Equal.trans(Nat, tot(~S.KV<A, B>, ~C, ~f, c, mr), tot2(~A, ~B, ~le, ~C, ~f, c, S.deal(S.KV<A, B>, r)), tot(~S.KV<A, B>, ~C, ~f, c, r), tot_msorted(~A, ~B, ~le, ~C, ~f, c, p, S.deal(S.KV<A, B>, r)), tot_deal(~A, ~B, ~le, ~C, ~f, c, r))
          Equal.trans(Nat, tot(~S.KV<A, B>, ~C, ~f, c, S.merge(~A, ~B, ~le, ml, mr)), Nat.add(tot(~S.KV<A, B>, ~C, ~f, c, ml), tot(~S.KV<A, B>, ~C, ~f, c, mr)), Nat.add(tot(~S.KV<A, B>, ~C, ~f, c, l), tot(~S.KV<A, B>, ~C, ~f, c, r)), tot_merge(~A, ~B, ~le, ~C, ~f, c, ml, mr), RP.add_eq(tot(~S.KV<A, B>, ~C, ~f, c, ml), tot(~S.KV<A, B>, ~C, ~f, c, l), tot(~S.KV<A, B>, ~C, ~f, c, mr), tot(~S.KV<A, B>, ~C, ~f, c, r), el, er))

def tot_msort(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~C: Data, ~f: C -> S.KV<A, B> -> Nat, +c: C, +xs: List<&2, S.KV<A, B>>) -> {tot(~S.KV<A, B>, ~C, ~f, c, S.msort(~A, ~B, ~le, xs)) == tot(~S.KV<A, B>, ~C, ~f, c, xs) : Nat}:
  +k = {1n+U32.log2(U32.from_nat(List.length(&2, S.KV<A, B>, xs))) : Nat}
  Equal.trans(Nat, tot(~S.KV<A, B>, ~C, ~f, c, S.msorted(~A, ~B, ~le, k, S.deal(S.KV<A, B>, xs))), tot2(~A, ~B, ~le, ~C, ~f, c, S.deal(S.KV<A, B>, xs)), tot(~S.KV<A, B>, ~C, ~f, c, xs), tot_msorted(~A, ~B, ~le, ~C, ~f, c, k, S.deal(S.KV<A, B>, xs)), tot_deal(~A, ~B, ~le, ~C, ~f, c, xs))

# ---- the sort returns its list sorted

# v <= every key in xs
def Ge(~A: Data, ~B: Data, ~le: A -> A -> Bool, +v: A, xs: List<&2, S.KV<A, B>>) -> Data:
  match xs:
    case Nil{}:
      Unit
    case Con{x, t}:
      RP.And({le(v, S.key(A, B, x)) == True{} : Bool}, Ge(~A, ~B, ~le, v, t))

# every key is <= every key after it
def SS(~A: Data, ~B: Data, ~le: A -> A -> Bool, xs: List<&2, S.KV<A, B>>) -> Data:
  match xs:
    case Nil{}:
      Unit
    case Con{+x, +t}:
      RP.And(Ge(~A, ~B, ~le, S.key(A, B, x), t), SS(~A, ~B, ~le, t))

def ge_trans(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +v: A, +w: A, +h: {le(v, w) == True{} : Bool}, +xs: List<&2, S.KV<A, B>>, +g: Ge(~A, ~B, ~le, w, xs)) -> Ge(~A, ~B, ~le, v, xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +t}:
      (hw, gt) = g
      (le_trans(v, w, S.key(A, B, x), h, hw), ge_trans(~A, ~B, ~le, ~le_trans, v, w, h, t, gt))

# a bound on both inputs bounds the merge
def ge_mrg(~A: Data, ~B: Data, ~le: A -> A -> Bool, +z: A, +xt: List<&2, S.KV<A, B>>, +yt: List<&2, S.KV<A, B>>, +x: S.KV<A, B>, +y: S.KV<A, B>, d: Bool, +hx: Ge(~A, ~B, ~le, z, x <> xt), +hy: Ge(~A, ~B, ~le, z, y <> yt)) -> Ge(~A, ~B, ~le, z, S.mrg(~A, ~B, ~le, xt, yt, x, y, d)):
  match xt yt d:
    case Nil{} _ True{}:
      (ex, _) = hx
      (ex, hy)
    case Con{+a, +at} _ True{}:
      (ex, ha) = hx
      (ex, ge_mrg(~A, ~B, ~le, z, at, yt, a, y, S.kle(~A, ~B, ~le, a, y), ha, hy))
    case _ Nil{} False{}:
      (ey, _) = hy
      (ey, hx)
    case _ Con{+b, +bt} False{}:
      (ey, hb) = hy
      (ey, ge_mrg(~A, ~B, ~le, z, xt, bt, x, b, S.kle(~A, ~B, ~le, x, b), hx, hb))

def ss_mrg(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +xt: List<&2, S.KV<A, B>>, +yt: List<&2, S.KV<A, B>>, +x: S.KV<A, B>, +y: S.KV<A, B>, d: Bool, +ed: {S.kle(~A, ~B, ~le, x, y) == d : Bool}, +sx: SS(~A, ~B, ~le, x <> xt), +sy: SS(~A, ~B, ~le, y <> yt)) -> SS(~A, ~B, ~le, S.mrg(~A, ~B, ~le, xt, yt, x, y, d)):
  match xt yt d:
    case Nil{} _ True{}:
      (gy, _) = sy
      ((ed, ge_trans(~A, ~B, ~le, ~le_trans, S.key(A, B, x), S.key(A, B, y), ed, yt, gy)), sy)
    case Con{+a, +at} _ True{}:
      (gx, sxt) = sx
      (gy, _) = sy
      +gy2 = {(ed, ge_trans(~A, ~B, ~le, ~le_trans, S.key(A, B, x), S.key(A, B, y), ed, yt, gy)) : Ge(~A, ~B, ~le, S.key(A, B, x), y <> yt)}
      (ge_mrg(~A, ~B, ~le, S.key(A, B, x), at, yt, a, y, S.kle(~A, ~B, ~le, a, y), gx, gy2), ss_mrg(~A, ~B, ~le, ~le_total, ~le_trans, at, yt, a, y, S.kle(~A, ~B, ~le, a, y), {==}, sxt, sy))
    case _ Nil{} False{}:
      (gx, _) = sx
      +eyx = le_total(S.key(A, B, x), S.key(A, B, y), ed)
      ((eyx, ge_trans(~A, ~B, ~le, ~le_trans, S.key(A, B, y), S.key(A, B, x), eyx, xt, gx)), sx)
    case _ Con{+b, +bt} False{}:
      (gx, _) = sx
      (gyb, syb) = sy
      +eyx = le_total(S.key(A, B, x), S.key(A, B, y), ed)
      +gx2 = {(eyx, ge_trans(~A, ~B, ~le, ~le_trans, S.key(A, B, y), S.key(A, B, x), eyx, xt, gx)) : Ge(~A, ~B, ~le, S.key(A, B, y), x <> xt)}
      (ge_mrg(~A, ~B, ~le, S.key(A, B, y), xt, bt, x, b, S.kle(~A, ~B, ~le, x, b), gx2, gyb), ss_mrg(~A, ~B, ~le, ~le_total, ~le_trans, xt, bt, x, b, S.kle(~A, ~B, ~le, x, b), {==}, sx, syb))

def ss_merge(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +xs: List<&2, S.KV<A, B>>, +ys: List<&2, S.KV<A, B>>, +sx: SS(~A, ~B, ~le, xs), +sy: SS(~A, ~B, ~le, ys)) -> SS(~A, ~B, ~le, S.merge(~A, ~B, ~le, xs, ys)):
  match xs ys:
    case Nil{} _:
      sy
    case Con{+x, +xt} Nil{}:
      sx
    case Con{+x, +xt} Con{+y, +yt}:
      ss_mrg(~A, ~B, ~le, ~le_total, ~le_trans, xt, yt, x, y, S.kle(~A, ~B, ~le, x, y), {==}, sx, sy)

def ss_isort(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +xs: List<&2, S.KV<A, B>>) -> SS(~A, ~B, ~le, S.isort(~A, ~B, ~le, xs)):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +t}:
      ss_merge(~A, ~B, ~le, ~le_total, ~le_trans, x <> Nil{}, S.isort(~A, ~B, ~le, t), (Unit{}, Unit{}), ss_isort(~A, ~B, ~le, ~le_total, ~le_trans, t))

def ss_msorted(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +k: Nat, +two: S.Two<S.KV<A, B>>) -> SS(~A, ~B, ~le, S.msorted(~A, ~B, ~le, k, two)):
  match k:
    case 0n:
      match two:
        case S.Two{+l, +r}:
          ss_merge(~A, ~B, ~le, ~le_total, ~le_trans, S.isort(~A, ~B, ~le, l), S.isort(~A, ~B, ~le, r), ss_isort(~A, ~B, ~le, ~le_total, ~le_trans, l), ss_isort(~A, ~B, ~le, ~le_total, ~le_trans, r))
    case 1n+p:
      match two:
        case S.Two{+l, +r}:
          ss_merge(~A, ~B, ~le, ~le_total, ~le_trans, S.msorted(~A, ~B, ~le, p, S.deal(S.KV<A, B>, l)), S.msorted(~A, ~B, ~le, p, S.deal(S.KV<A, B>, r)), ss_msorted(~A, ~B, ~le, ~le_total, ~le_trans, p, S.deal(S.KV<A, B>, l)), ss_msorted(~A, ~B, ~le, ~le_total, ~le_trans, p, S.deal(S.KV<A, B>, r)))

def ss_msort(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +xs: List<&2, S.KV<A, B>>) -> SS(~A, ~B, ~le, S.msort(~A, ~B, ~le, xs)):
  ss_msorted(~A, ~B, ~le, ~le_total, ~le_trans, {1n+U32.log2(U32.from_nat(List.length(&2, S.KV<A, B>, xs))) : Nat}, S.deal(S.KV<A, B>, xs))

# ---- facts of the order

def refl.go(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, +x: A, b: Bool, eb: {le(x, x) == b : Bool}) -> {le(x, x) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      le_total(x, x, eb)

def refl(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, +x: A) -> {le(x, x) == True{} : Bool}:
  refl.go(~A, ~le, ~le_total, x, le(x, x), {==})

# u > a and b <= a give u > b
def gt_of.go(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +u: A, +a: A, +b: A, h1: {le(u, a) == False{} : Bool}, h2: {le(b, a) == True{} : Bool}, b2: Bool, eb2: {le(u, b) == b2 : Bool}) -> {le(u, b) == False{} : Bool}:
  match b2:
    case False{}:
      eb2
    case True{}:
      Empty.absurd({le(u, b) == False{} : Bool}, RP.clash(le(u, a), h1, le_trans(u, b, a, eb2, h2)))

def gt_of(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +u: A, +a: A, +b: A, h1: {le(u, a) == False{} : Bool}, h2: {le(b, a) == True{} : Bool}) -> {le(u, b) == False{} : Bool}:
  gt_of.go(~A, ~le, ~le_trans, u, a, b, h1, h2, le(u, b), {==})

# w <= k and v < w give k > v
def ge_gt.go(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +k: A, +w: A, +v: A, h1: {le(w, k) == True{} : Bool}, h2: {le(w, v) == False{} : Bool}, b2: Bool, eb2: {le(k, v) == b2 : Bool}) -> {le(k, v) == False{} : Bool}:
  match b2:
    case False{}:
      eb2
    case True{}:
      Empty.absurd({le(k, v) == False{} : Bool}, RP.clash(le(w, v), h2, le_trans(w, k, v, h1, eb2)))

def ge_gt(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +k: A, +w: A, +v: A, h1: {le(w, k) == True{} : Bool}, h2: {le(w, v) == False{} : Bool}) -> {le(k, v) == False{} : Bool}:
  ge_gt.go(~A, ~le, ~le_trans, k, w, v, h1, h2, le(k, v), {==})

# ---- counts over keys

def klt(~A: Data, ~B: Data, ~le: A -> A -> Bool, xs: List<&2, S.KV<A, B>>, +q: A) -> Nat:
  Laws.cnt_lt(~A, ~le, Laws.keys(A, B, xs), q)

def kle(~A: Data, ~B: Data, ~le: A -> A -> Bool, xs: List<&2, S.KV<A, B>>, +q: A) -> Nat:
  Laws.cnt_le(~A, ~le, Laws.keys(A, B, xs), q)

def av(~A: Data, ~B: Data, ~le: A -> A -> Bool, +all: List<&2, S.KV<A, B>>, +q: A) -> Nat:
  Laws.avg2(~A, ~le, Laws.keys(A, B, all), q)

# every key in xs is <= v
def Le(~A: Data, ~B: Data, ~le: A -> A -> Bool, xs: List<&2, S.KV<A, B>>, +v: A) -> Data:
  match xs:
    case Nil{}:
      Unit
    case Con{x, t}:
      RP.And({le(S.key(A, B, x), v) == True{} : Bool}, Le(~A, ~B, ~le, t, v))

def le_snoc(~A: Data, ~B: Data, ~le: A -> A -> Bool, +pre: List<&2, S.KV<A, B>>, +v: A, +x: S.KV<A, B>, +hp: Le(~A, ~B, ~le, pre, v), +hx: {le(S.key(A, B, x), v) == True{} : Bool}) -> Le(~A, ~B, ~le, List.append(&2, S.KV<A, B>, pre, x <> Nil{}), v):
  match pre:
    case Nil{}:
      (hx, Unit{})
    case Con{+h, +r}:
      (e, hr) = hp
      (e, le_snoc(~A, ~B, ~le, r, v, x, hr, hx))

def le_up(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +pre: List<&2, S.KV<A, B>>, +v: A, +w: A, +hp: Le(~A, ~B, ~le, pre, v), +h: {le(v, w) == True{} : Bool}) -> Le(~A, ~B, ~le, pre, w):
  match pre:
    case Nil{}:
      Unit{}
    case Con{+x, +t}:
      (e, ht) = hp
      (le_trans(S.key(A, B, x), v, w, e, h), le_up(~A, ~B, ~le, ~le_trans, t, v, w, ht, h))

def lt_zero(~A: Data, ~B: Data, ~le: A -> A -> Bool, +ps: List<&2, S.KV<A, B>>, +w: A, +g: Ge(~A, ~B, ~le, w, ps)) -> {klt(~A, ~B, ~le, ps, w) == 0n : Nat}:
  match ps:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      (h, gt) = g
      %Equal.sym(Bool, le(w, S.key(A, B, x)), True{}, h) : {Nat.add(Laws.ind(Bool.not(_)), klt(~A, ~B, ~le, t, w)) == 0n : Nat}
      lt_zero(~A, ~B, ~le, t, w, gt)

def le_zero(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +ps: List<&2, S.KV<A, B>>, +v: A, +w: A, +g: Ge(~A, ~B, ~le, w, ps), +h: {le(w, v) == False{} : Bool}) -> {kle(~A, ~B, ~le, ps, v) == 0n : Nat}:
  match ps:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      (hk, gt) = g
      +ek = ge_gt(~A, ~le, ~le_trans, S.key(A, B, x), w, v, hk, h)
      %Equal.sym(Bool, le(S.key(A, B, x), v), False{}, ek) : {Nat.add(Laws.ind(_), kle(~A, ~B, ~le, t, v)) == 0n : Nat}
      le_zero(~A, ~B, ~le, ~le_trans, t, v, w, gt, h)

def lt_full(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +pre: List<&2, S.KV<A, B>>, +v: A, +w: A, +hp: Le(~A, ~B, ~le, pre, v), +h: {le(w, v) == False{} : Bool}) -> {klt(~A, ~B, ~le, pre, w) == List.length(&2, S.KV<A, B>, pre) : Nat}:
  match pre:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      (e, ht) = hp
      +ek = gt_of(~A, ~le, ~le_trans, w, v, S.key(A, B, x), h, e)
      %Equal.sym(Bool, le(w, S.key(A, B, x)), False{}, ek) : {Nat.add(Laws.ind(Bool.not(_)), klt(~A, ~B, ~le, t, w)) == List.length(&2, S.KV<A, B>, x <> t) : Nat}
      Equal.cong(Nat, Nat, z => 1n+z, klt(~A, ~B, ~le, t, w), List.length(&2, S.KV<A, B>, t), lt_full(~A, ~B, ~le, ~le_trans, t, v, w, ht, h))

def le_full(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +pre: List<&2, S.KV<A, B>>, +v: A, +w: A, +hp: Le(~A, ~B, ~le, pre, v), +h: {le(w, v) == False{} : Bool}) -> {kle(~A, ~B, ~le, pre, w) == List.length(&2, S.KV<A, B>, pre) : Nat}:
  match pre:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      (e, ht) = hp
      +ek = le_trans(S.key(A, B, x), v, w, e, le_total(w, v, h))
      %Equal.sym(Bool, le(S.key(A, B, x), w), True{}, ek) : {Nat.add(Laws.ind(_), kle(~A, ~B, ~le, t, w)) == List.length(&2, S.KV<A, B>, x <> t) : Nat}
      Equal.cong(Nat, Nat, z => 1n+z, kle(~A, ~B, ~le, t, w), List.length(&2, S.KV<A, B>, t), le_full(~A, ~B, ~le, ~le_total, ~le_trans, t, v, w, ht, h))

def klt_snoc(~A: Data, ~B: Data, ~le: A -> A -> Bool, +pre: List<&2, S.KV<A, B>>, +x: S.KV<A, B>, +q: A) -> {klt(~A, ~B, ~le, List.append(&2, S.KV<A, B>, pre, x <> Nil{}), q) == Nat.add(klt(~A, ~B, ~le, pre, q), Laws.ind(Bool.not(le(q, S.key(A, B, x))))) : Nat}:
  match pre:
    case Nil{}:
      RP.add_zero_r(Laws.ind(Bool.not(le(q, S.key(A, B, x)))))
    case Con{+h, +r}:
      +ih = Laws.ind(Bool.not(le(q, S.key(A, B, h))))
      +i = Laws.ind(Bool.not(le(q, S.key(A, B, x))))
      Equal.trans(Nat, Nat.add(ih, klt(~A, ~B, ~le, List.append(&2, S.KV<A, B>, r, x <> Nil{}), q)), Nat.add(ih, Nat.add(klt(~A, ~B, ~le, r, q), i)), Nat.add(Nat.add(ih, klt(~A, ~B, ~le, r, q)), i), Equal.cong(Nat, Nat, z => Nat.add(ih, z), klt(~A, ~B, ~le, List.append(&2, S.KV<A, B>, r, x <> Nil{}), q), Nat.add(klt(~A, ~B, ~le, r, q), i), klt_snoc(~A, ~B, ~le, r, x, q)), Equal.sym(Nat, Nat.add(Nat.add(ih, klt(~A, ~B, ~le, r, q)), i), Nat.add(ih, Nat.add(klt(~A, ~B, ~le, r, q), i)), RP.add_assoc(ih, klt(~A, ~B, ~le, r, q), i)))

def kle_snoc(~A: Data, ~B: Data, ~le: A -> A -> Bool, +pre: List<&2, S.KV<A, B>>, +x: S.KV<A, B>, +q: A) -> {kle(~A, ~B, ~le, List.append(&2, S.KV<A, B>, pre, x <> Nil{}), q) == Nat.add(kle(~A, ~B, ~le, pre, q), Laws.ind(le(S.key(A, B, x), q))) : Nat}:
  match pre:
    case Nil{}:
      RP.add_zero_r(Laws.ind(le(S.key(A, B, x), q)))
    case Con{+h, +r}:
      +ih = Laws.ind(le(S.key(A, B, h), q))
      +i = Laws.ind(le(S.key(A, B, x), q))
      Equal.trans(Nat, Nat.add(ih, kle(~A, ~B, ~le, List.append(&2, S.KV<A, B>, r, x <> Nil{}), q)), Nat.add(ih, Nat.add(kle(~A, ~B, ~le, r, q), i)), Nat.add(Nat.add(ih, kle(~A, ~B, ~le, r, q)), i), Equal.cong(Nat, Nat, z => Nat.add(ih, z), kle(~A, ~B, ~le, List.append(&2, S.KV<A, B>, r, x <> Nil{}), q), Nat.add(kle(~A, ~B, ~le, r, q), i), kle_snoc(~A, ~B, ~le, r, x, q)), Equal.sym(Nat, Nat.add(Nat.add(ih, kle(~A, ~B, ~le, r, q)), i), Nat.add(ih, Nat.add(kle(~A, ~B, ~le, r, q), i)), RP.add_assoc(ih, kle(~A, ~B, ~le, r, q), i)))

def klt_app(~A: Data, ~B: Data, ~le: A -> A -> Bool, +a: List<&2, S.KV<A, B>>, +b: List<&2, S.KV<A, B>>, +q: A) -> {klt(~A, ~B, ~le, List.append(&2, S.KV<A, B>, a, b), q) == Nat.add(klt(~A, ~B, ~le, a, q), klt(~A, ~B, ~le, b, q)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +r}:
      +ih = Laws.ind(Bool.not(le(q, S.key(A, B, h))))
      Equal.trans(Nat, Nat.add(ih, klt(~A, ~B, ~le, List.append(&2, S.KV<A, B>, r, b), q)), Nat.add(ih, Nat.add(klt(~A, ~B, ~le, r, q), klt(~A, ~B, ~le, b, q))), Nat.add(Nat.add(ih, klt(~A, ~B, ~le, r, q)), klt(~A, ~B, ~le, b, q)), Equal.cong(Nat, Nat, z => Nat.add(ih, z), klt(~A, ~B, ~le, List.append(&2, S.KV<A, B>, r, b), q), Nat.add(klt(~A, ~B, ~le, r, q), klt(~A, ~B, ~le, b, q)), klt_app(~A, ~B, ~le, r, b, q)), Equal.sym(Nat, Nat.add(Nat.add(ih, klt(~A, ~B, ~le, r, q)), klt(~A, ~B, ~le, b, q)), Nat.add(ih, Nat.add(klt(~A, ~B, ~le, r, q), klt(~A, ~B, ~le, b, q))), RP.add_assoc(ih, klt(~A, ~B, ~le, r, q), klt(~A, ~B, ~le, b, q))))

def kle_app(~A: Data, ~B: Data, ~le: A -> A -> Bool, +a: List<&2, S.KV<A, B>>, +b: List<&2, S.KV<A, B>>, +q: A) -> {kle(~A, ~B, ~le, List.append(&2, S.KV<A, B>, a, b), q) == Nat.add(kle(~A, ~B, ~le, a, q), kle(~A, ~B, ~le, b, q)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +r}:
      +ih = Laws.ind(le(S.key(A, B, h), q))
      Equal.trans(Nat, Nat.add(ih, kle(~A, ~B, ~le, List.append(&2, S.KV<A, B>, r, b), q)), Nat.add(ih, Nat.add(kle(~A, ~B, ~le, r, q), kle(~A, ~B, ~le, b, q))), Nat.add(Nat.add(ih, kle(~A, ~B, ~le, r, q)), kle(~A, ~B, ~le, b, q)), Equal.cong(Nat, Nat, z => Nat.add(ih, z), kle(~A, ~B, ~le, List.append(&2, S.KV<A, B>, r, b), q), Nat.add(kle(~A, ~B, ~le, r, q), kle(~A, ~B, ~le, b, q)), kle_app(~A, ~B, ~le, r, b, q)), Equal.sym(Nat, Nat.add(Nat.add(ih, kle(~A, ~B, ~le, r, q)), kle(~A, ~B, ~le, b, q)), Nat.add(ih, Nat.add(kle(~A, ~B, ~le, r, q), kle(~A, ~B, ~le, b, q))), RP.add_assoc(ih, kle(~A, ~B, ~le, r, q), kle(~A, ~B, ~le, b, q))))

def len_snoc(~A: Data, ~B: Data, ~le: A -> A -> Bool, +pre: List<&2, S.KV<A, B>>, +x: S.KV<A, B>) -> {List.length(&2, S.KV<A, B>, List.append(&2, S.KV<A, B>, pre, x <> Nil{})) == 1n+List.length(&2, S.KV<A, B>, pre) : Nat}:
  match pre:
    case Nil{}:
      {==}
    case Con{+h, +r}:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, S.KV<A, B>, List.append(&2, S.KV<A, B>, r, x <> Nil{})), 1n+List.length(&2, S.KV<A, B>, r), len_snoc(~A, ~B, ~le, r, x))

def app_snoc(~A: Data, ~B: Data, ~le: A -> A -> Bool, +pre: List<&2, S.KV<A, B>>, +x: S.KV<A, B>, +t: List<&2, S.KV<A, B>>) -> {List.append(&2, S.KV<A, B>, pre, x <> t) == List.append(&2, S.KV<A, B>, List.append(&2, S.KV<A, B>, pre, x <> Nil{}), t) : List<&2, S.KV<A, B>>}:
  match pre:
    case Nil{}:
      {==}
    case Con{+h, +r}:
      Equal.cong(List<&2, S.KV<A, B>>, List<&2, S.KV<A, B>>, z => h <> z, List.append(&2, S.KV<A, B>, r, x <> t), List.append(&2, S.KV<A, B>, List.append(&2, S.KV<A, B>, r, x <> Nil{}), t), app_snoc(~A, ~B, ~le, r, x, t))

# tied values have the same counts
def cl_tie(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +xs: List<&2, A>, +a: A, +v: A, +e1: {le(a, v) == True{} : Bool}, +e2: {le(v, a) == True{} : Bool}) -> {Laws.cnt_lt(~A, ~le, xs, a) == Laws.cnt_lt(~A, ~le, xs, v) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      RP.add_eq(Laws.ind(Bool.not(le(a, x))), Laws.ind(Bool.not(le(v, x))), Laws.cnt_lt(~A, ~le, t, a), Laws.cnt_lt(~A, ~le, t, v), Equal.cong(Bool, Nat, z => Laws.ind(Bool.not(z)), le(a, x), le(v, x), RP.tie_r(~A, ~le, ~le_trans, a, v, x, e1, e2, le(v, x), {==})), cl_tie(~A, ~le, ~le_trans, t, a, v, e1, e2))

def ce_tie(~A: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +xs: List<&2, A>, +a: A, +v: A, +e1: {le(a, v) == True{} : Bool}, +e2: {le(v, a) == True{} : Bool}) -> {Laws.cnt_le(~A, ~le, xs, a) == Laws.cnt_le(~A, ~le, xs, v) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      RP.add_eq(Laws.ind(le(x, a)), Laws.ind(le(x, v)), Laws.cnt_le(~A, ~le, t, a), Laws.cnt_le(~A, ~le, t, v), Equal.cong(Bool, Nat, z => Laws.ind(z), le(x, a), le(x, v), RP.tie_q(~A, ~le, ~le_trans, a, v, x, e1, e2, le(x, v), {==})), ce_tie(~A, ~le, ~le_trans, t, a, v, e1, e2))

def av_tie(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +all: List<&2, S.KV<A, B>>, +a: A, +v: A, +e1: {le(a, v) == True{} : Bool}, +e2: {le(v, a) == True{} : Bool}) -> {av(~A, ~B, ~le, all, a) == av(~A, ~B, ~le, all, v) : Nat}:
  +ks = Laws.keys(A, B, all)
  Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Laws.cnt_lt(~A, ~le, ks, a), Laws.cnt_le(~A, ~le, ks, a)), Nat.add(Laws.cnt_lt(~A, ~le, ks, v), Laws.cnt_le(~A, ~le, ks, v)), RP.add_eq(Laws.cnt_lt(~A, ~le, ks, a), Laws.cnt_lt(~A, ~le, ks, v), Laws.cnt_le(~A, ~le, ks, a), Laws.cnt_le(~A, ~le, ks, v), cl_tie(~A, ~le, ~le_trans, ks, a, v, e1, e2), ce_tie(~A, ~le, ~le_trans, ks, a, v, e1, e2)))

# the rank of a run's key, once the run is complete
def av_at(~A: Data, ~B: Data, ~le: A -> A -> Bool, +all: List<&2, S.KV<A, B>>, +pre: List<&2, S.KV<A, B>>, +ps: List<&2, S.KV<A, B>>, +v: A, +p: Nat, +cc: Nat, +ha: {all == List.append(&2, S.KV<A, B>, pre, ps) : List<&2, S.KV<A, B>>}, +i1: {klt(~A, ~B, ~le, pre, v) == p : Nat}, +i2: {kle(~A, ~B, ~le, pre, v) == Nat.add(p, cc) : Nat}, +z1: {klt(~A, ~B, ~le, ps, v) == 0n : Nat}, +z2: {kle(~A, ~B, ~le, ps, v) == 0n : Nat}) -> {av(~A, ~B, ~le, all, v) == 1n+Nat.add(Nat.add(p, p), cc) : Nat}:
  +pc = Nat.add(p, cc)
  +lt = Equal.trans(Nat, klt(~A, ~B, ~le, all, v), klt(~A, ~B, ~le, List.append(&2, S.KV<A, B>, pre, ps), v), p, Equal.cong(List<&2, S.KV<A, B>>, Nat, z => klt(~A, ~B, ~le, z, v), all, List.append(&2, S.KV<A, B>, pre, ps), ha), Equal.trans(Nat, klt(~A, ~B, ~le, List.append(&2, S.KV<A, B>, pre, ps), v), Nat.add(klt(~A, ~B, ~le, pre, v), klt(~A, ~B, ~le, ps, v)), p, klt_app(~A, ~B, ~le, pre, ps, v), Equal.trans(Nat, Nat.add(klt(~A, ~B, ~le, pre, v), klt(~A, ~B, ~le, ps, v)), Nat.add(p, 0n), p, RP.add_eq(klt(~A, ~B, ~le, pre, v), p, klt(~A, ~B, ~le, ps, v), 0n, i1, z1), RP.add_zero_r(p))))
  +ge = Equal.trans(Nat, kle(~A, ~B, ~le, all, v), kle(~A, ~B, ~le, List.append(&2, S.KV<A, B>, pre, ps), v), pc, Equal.cong(List<&2, S.KV<A, B>>, Nat, z => kle(~A, ~B, ~le, z, v), all, List.append(&2, S.KV<A, B>, pre, ps), ha), Equal.trans(Nat, kle(~A, ~B, ~le, List.append(&2, S.KV<A, B>, pre, ps), v), Nat.add(kle(~A, ~B, ~le, pre, v), kle(~A, ~B, ~le, ps, v)), pc, kle_app(~A, ~B, ~le, pre, ps, v), Equal.trans(Nat, Nat.add(kle(~A, ~B, ~le, pre, v), kle(~A, ~B, ~le, ps, v)), Nat.add(pc, 0n), pc, RP.add_eq(kle(~A, ~B, ~le, pre, v), pc, kle(~A, ~B, ~le, ps, v), 0n, i2, z2), RP.add_zero_r(pc))))
  Equal.cong(Nat, Nat, z => 1n+z, Nat.add(klt(~A, ~B, ~le, all, v), kle(~A, ~B, ~le, all, v)), Nat.add(Nat.add(p, p), cc), Equal.trans(Nat, Nat.add(klt(~A, ~B, ~le, all, v), kle(~A, ~B, ~le, all, v)), Nat.add(p, pc), Nat.add(Nat.add(p, p), cc), RP.add_eq(klt(~A, ~B, ~le, all, v), p, kle(~A, ~B, ~le, all, v), pc, lt, ge), Equal.sym(Nat, Nat.add(Nat.add(p, p), cc), Nat.add(p, pc), RP.add_assoc(p, p, cc))))

# ---- the walk over runs gives each value the average rank of its key

# f summed over (y, r) for each y in ys
def totv(~B: Data, ~C: Data, ~f: C -> S.KV<B, Nat> -> Nat, +c: C, ys: List<&2, B>, +r: Nat) -> Nat:
  match ys:
    case Nil{}:
      0n
    case Con{y, t}:
      Nat.add(f(c, S.KV{y, r}), totv(~B, ~C, ~f, c, t, r))

# (value, 2 x the average rank of its key among all), for each pair in ps
def spec1(~A: Data, ~B: Data, ~le: A -> A -> Bool, +all: List<&2, S.KV<A, B>>, ps: List<&2, S.KV<A, B>>) -> List<&2, S.KV<B, Nat>>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{S.KV{k, v}, t}:
      S.KV{v, av(~A, ~B, ~le, all, k)} <> spec1(~A, ~B, ~le, all, t)

def emit_tot(~B: Data, ~C: Data, ~f: C -> S.KV<B, Nat> -> Nat, +c: C, +ys: List<&2, B>, +r: Nat, +acc: List<&2, S.KV<B, Nat>>) -> {tot(~S.KV<B, Nat>, ~C, ~f, c, S.emit(B, ys, r, acc)) == Nat.add(tot(~S.KV<B, Nat>, ~C, ~f, c, acc), totv(~B, ~C, ~f, c, ys, r)) : Nat}:
  match ys:
    case Nil{}:
      Equal.sym(Nat, Nat.add(tot(~S.KV<B, Nat>, ~C, ~f, c, acc), 0n), tot(~S.KV<B, Nat>, ~C, ~f, c, acc), RP.add_zero_r(tot(~S.KV<B, Nat>, ~C, ~f, c, acc)))
    case Con{+y, +t}:
      +fy = f(c, S.KV{y, r})
      +ta = tot(~S.KV<B, Nat>, ~C, ~f, c, acc)
      +tv = totv(~B, ~C, ~f, c, t, r)
      Equal.trans(Nat, tot(~S.KV<B, Nat>, ~C, ~f, c, S.emit(B, t, r, S.KV{y, r} <> acc)), Nat.add(Nat.add(fy, ta), tv), Nat.add(ta, Nat.add(fy, tv)), emit_tot(~B, ~C, ~f, c, t, r, S.KV{y, r} <> acc), Equal.trans(Nat, Nat.add(Nat.add(fy, ta), tv), Nat.add(fy, Nat.add(ta, tv)), Nat.add(ta, Nat.add(fy, tv)), RP.add_assoc(fy, ta, tv), RP.add_lcomm(fy, ta, tv)))

# pre is what the walk has passed: all keys <= v, p of them below v and cc
# tied with it. ps is the rest, sorted, all keys >= v.
def runs_ok(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, ~C: Data, ~f: C -> S.KV<B, Nat> -> Nat, +c: C, +ps: List<&2, S.KV<A, B>>, +all: List<&2, S.KV<A, B>>, +pre: List<&2, S.KV<A, B>>, +v: A, +p: Nat, +cc: Nat, +ys: List<&2, B>, +acc: List<&2, S.KV<B, Nat>>, d: Bool, +ed: {S.nxt(~A, ~B, ~le, ps, v) == d : Bool}, +ha: {all == List.append(&2, S.KV<A, B>, pre, ps) : List<&2, S.KV<A, B>>}, +hl: {List.length(&2, S.KV<A, B>, pre) == Nat.add(p, cc) : Nat}, +hp: Le(~A, ~B, ~le, pre, v), +i1: {klt(~A, ~B, ~le, pre, v) == p : Nat}, +i2: {kle(~A, ~B, ~le, pre, v) == Nat.add(p, cc) : Nat}, +hs: SS(~A, ~B, ~le, ps), +hg: Ge(~A, ~B, ~le, v, ps)) -> {tot(~S.KV<B, Nat>, ~C, ~f, c, S.runs(~A, ~B, ~le, ps, v, p, cc, ys, acc, d)) == Nat.add(tot(~S.KV<B, Nat>, ~C, ~f, c, acc), Nat.add(totv(~B, ~C, ~f, c, ys, av(~A, ~B, ~le, all, v)), tot(~S.KV<B, Nat>, ~C, ~f, c, spec1(~A, ~B, ~le, all, ps)))) : Nat}:
  match ps d:
    case Nil{} _:
      +r0 = {1n+Nat.add(Nat.add(p, p), cc) : Nat}
      +ta = tot(~S.KV<B, Nat>, ~C, ~f, c, acc)
      +tv = totv(~B, ~C, ~f, c, ys, av(~A, ~B, ~le, all, v))
      +e0 = av_at(~A, ~B, ~le, all, pre, Nil{}, v, p, cc, ha, i1, i2, {==}, {==})
      +ev = Equal.trans(Nat, totv(~B, ~C, ~f, c, ys, r0), tv, Nat.add(tv, 0n), Equal.cong(Nat, Nat, z => totv(~B, ~C, ~f, c, ys, z), r0, av(~A, ~B, ~le, all, v), Equal.sym(Nat, av(~A, ~B, ~le, all, v), r0, e0)), Equal.sym(Nat, Nat.add(tv, 0n), tv, RP.add_zero_r(tv)))
      Equal.trans(Nat, tot(~S.KV<B, Nat>, ~C, ~f, c, S.emit(B, ys, r0, acc)), Nat.add(ta, totv(~B, ~C, ~f, c, ys, r0)), Nat.add(ta, Nat.add(tv, 0n)), emit_tot(~B, ~C, ~f, c, ys, r0, acc), Equal.cong(Nat, Nat, z => Nat.add(ta, z), totv(~B, ~C, ~f, c, ys, r0), Nat.add(tv, 0n), ev))
    case Con{S.KV{+w, +y}, +t} True{}:
      (_, hst) = hs
      (hvw, hgt) = hg
      +x = {S.KV{w, y} : S.KV<A, B>}
      +pre2 = {List.append(&2, S.KV<A, B>, pre, x <> Nil{}) : List<&2, S.KV<A, B>>}
      +ha2 = Equal.trans(List<&2, S.KV<A, B>>, all, List.append(&2, S.KV<A, B>, pre, x <> t), List.append(&2, S.KV<A, B>, pre2, t), ha, app_snoc(~A, ~B, ~le, pre, x, t))
      +hl2 = Equal.trans(Nat, List.length(&2, S.KV<A, B>, pre2), 1n+List.length(&2, S.KV<A, B>, pre), Nat.add(p, 1n+cc), len_snoc(~A, ~B, ~le, pre, x), Equal.trans(Nat, 1n+List.length(&2, S.KV<A, B>, pre), 1n+Nat.add(p, cc), Nat.add(p, 1n+cc), Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, S.KV<A, B>, pre), Nat.add(p, cc), hl), Equal.sym(Nat, Nat.add(p, 1n+cc), 1n+Nat.add(p, cc), RP.add_succ_r(p, cc))))
      +hp2 = le_snoc(~A, ~B, ~le, pre, v, x, hp, ed)
      +i1b = Equal.trans(Nat, klt(~A, ~B, ~le, pre2, v), Nat.add(klt(~A, ~B, ~le, pre, v), Laws.ind(Bool.not(le(v, w)))), Nat.add(klt(~A, ~B, ~le, pre, v), 0n), klt_snoc(~A, ~B, ~le, pre, x, v), Equal.cong(Bool, Nat, z => Nat.add(klt(~A, ~B, ~le, pre, v), Laws.ind(Bool.not(z))), le(v, w), True{}, hvw))
      +i1c = Equal.trans(Nat, klt(~A, ~B, ~le, pre2, v), Nat.add(klt(~A, ~B, ~le, pre, v), 0n), p, i1b, Equal.trans(Nat, Nat.add(klt(~A, ~B, ~le, pre, v), 0n), klt(~A, ~B, ~le, pre, v), p, RP.add_zero_r(klt(~A, ~B, ~le, pre, v)), i1))
      +i2b = Equal.trans(Nat, kle(~A, ~B, ~le, pre2, v), Nat.add(kle(~A, ~B, ~le, pre, v), Laws.ind(le(w, v))), Nat.add(kle(~A, ~B, ~le, pre, v), 1n), kle_snoc(~A, ~B, ~le, pre, x, v), Equal.cong(Bool, Nat, z => Nat.add(kle(~A, ~B, ~le, pre, v), Laws.ind(z)), le(w, v), True{}, ed))
      +i2c = Equal.trans(Nat, Nat.add(kle(~A, ~B, ~le, pre, v), 1n), Nat.add(Nat.add(p, cc), 1n), Nat.add(p, 1n+cc), Equal.cong(Nat, Nat, z => Nat.add(z, 1n), kle(~A, ~B, ~le, pre, v), Nat.add(p, cc), i2), Equal.trans(Nat, Nat.add(Nat.add(p, cc), 1n), Nat.add(p, Nat.add(cc, 1n)), Nat.add(p, 1n+cc), RP.add_assoc(p, cc, 1n), Equal.cong(Nat, Nat, z => Nat.add(p, z), Nat.add(cc, 1n), 1n+cc, RP.add_comm(cc, 1n))))
      +ih = runs_ok(~A, ~B, ~le, ~le_total, ~le_trans, ~C, ~f, c, t, all, pre2, v, p, 1n+cc, y <> ys, acc, S.nxt(~A, ~B, ~le, t, v), {==}, ha2, hl2, hp2, i1c, Equal.trans(Nat, kle(~A, ~B, ~le, pre2, v), Nat.add(kle(~A, ~B, ~le, pre, v), 1n), Nat.add(p, 1n+cc), i2b, i2c), hst, hgt)
      +ta = tot(~S.KV<B, Nat>, ~C, ~f, c, acc)
      +tv = totv(~B, ~C, ~f, c, ys, av(~A, ~B, ~le, all, v))
      +ts = tot(~S.KV<B, Nat>, ~C, ~f, c, spec1(~A, ~B, ~le, all, t))
      +fv = f(c, S.KV{y, av(~A, ~B, ~le, all, v)})
      +fw = f(c, S.KV{y, av(~A, ~B, ~le, all, w)})
      +ew = Equal.cong(Nat, Nat, z => f(c, S.KV{y, z}), av(~A, ~B, ~le, all, v), av(~A, ~B, ~le, all, w), Equal.sym(Nat, av(~A, ~B, ~le, all, w), av(~A, ~B, ~le, all, v), av_tie(~A, ~B, ~le, ~le_trans, all, w, v, ed, hvw)))
      +inner = Equal.trans(Nat, Nat.add(Nat.add(fv, tv), ts), Nat.add(fv, Nat.add(tv, ts)), Nat.add(tv, Nat.add(fw, ts)), RP.add_assoc(fv, tv, ts), Equal.trans(Nat, Nat.add(fv, Nat.add(tv, ts)), Nat.add(tv, Nat.add(fv, ts)), Nat.add(tv, Nat.add(fw, ts)), RP.add_lcomm(fv, tv, ts), Equal.cong(Nat, Nat, z => Nat.add(tv, Nat.add(z, ts)), fv, fw, ew)))
      Equal.trans(Nat, tot(~S.KV<B, Nat>, ~C, ~f, c, S.runs(~A, ~B, ~le, t, v, p, 1n+cc, y <> ys, acc, S.nxt(~A, ~B, ~le, t, v))), Nat.add(ta, Nat.add(Nat.add(fv, tv), ts)), Nat.add(ta, Nat.add(tv, Nat.add(fw, ts))), ih, Equal.cong(Nat, Nat, z => Nat.add(ta, z), Nat.add(Nat.add(fv, tv), ts), Nat.add(tv, Nat.add(fw, ts)), inner))
    case Con{S.KV{+w, +y}, +t} False{}:
      (hwt, hst) = hs
      +x = {S.KV{w, y} : S.KV<A, B>}
      +evw = le_total(w, v, ed)
      +rw = refl(~A, ~le, ~le_total, w)
      +r0 = {1n+Nat.add(Nat.add(p, p), cc) : Nat}
      +z1 = lt_zero(~A, ~B, ~le, x <> t, v, hg)
      +z2 = le_zero(~A, ~B, ~le, ~le_trans, x <> t, v, w, {(rw, hwt) : Ge(~A, ~B, ~le, w, x <> t)}, ed)
      +e0 = av_at(~A, ~B, ~le, all, pre, x <> t, v, p, cc, ha, i1, i2, z1, z2)
      +pc = {Nat.add(p, cc) : Nat}
      +pre2 = {List.append(&2, S.KV<A, B>, pre, x <> Nil{}) : List<&2, S.KV<A, B>>}
      +ha2 = Equal.trans(List<&2, S.KV<A, B>>, all, List.append(&2, S.KV<A, B>, pre, x <> t), List.append(&2, S.KV<A, B>, pre2, t), ha, app_snoc(~A, ~B, ~le, pre, x, t))
      +hl2 = Equal.trans(Nat, List.length(&2, S.KV<A, B>, pre2), 1n+List.length(&2, S.KV<A, B>, pre), Nat.add(pc, 1n), len_snoc(~A, ~B, ~le, pre, x), Equal.trans(Nat, 1n+List.length(&2, S.KV<A, B>, pre), 1n+pc, Nat.add(pc, 1n), Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, S.KV<A, B>, pre), pc, hl), RP.add_comm(1n, pc)))
      +hp2 = le_snoc(~A, ~B, ~le, pre, w, x, le_up(~A, ~B, ~le, ~le_trans, pre, v, w, hp, evw), rw)
      +lw = Equal.trans(Nat, klt(~A, ~B, ~le, pre, w), List.length(&2, S.KV<A, B>, pre), pc, lt_full(~A, ~B, ~le, ~le_trans, pre, v, w, hp, ed), hl)
      +ew = Equal.trans(Nat, kle(~A, ~B, ~le, pre, w), List.length(&2, S.KV<A, B>, pre), pc, le_full(~A, ~B, ~le, ~le_total, ~le_trans, pre, v, w, hp, ed), hl)
      +i1b = Equal.trans(Nat, klt(~A, ~B, ~le, pre2, w), Nat.add(klt(~A, ~B, ~le, pre, w), Laws.ind(Bool.not(le(w, w)))), Nat.add(klt(~A, ~B, ~le, pre, w), 0n), klt_snoc(~A, ~B, ~le, pre, x, w), Equal.cong(Bool, Nat, z => Nat.add(klt(~A, ~B, ~le, pre, w), Laws.ind(Bool.not(z))), le(w, w), True{}, rw))
      +i1c = Equal.trans(Nat, klt(~A, ~B, ~le, pre2, w), Nat.add(klt(~A, ~B, ~le, pre, w), 0n), pc, i1b, Equal.trans(Nat, Nat.add(klt(~A, ~B, ~le, pre, w), 0n), klt(~A, ~B, ~le, pre, w), pc, RP.add_zero_r(klt(~A, ~B, ~le, pre, w)), lw))
      +i2b = Equal.trans(Nat, kle(~A, ~B, ~le, pre2, w), Nat.add(kle(~A, ~B, ~le, pre, w), Laws.ind(le(w, w))), Nat.add(kle(~A, ~B, ~le, pre, w), 1n), kle_snoc(~A, ~B, ~le, pre, x, w), Equal.cong(Bool, Nat, z => Nat.add(kle(~A, ~B, ~le, pre, w), Laws.ind(z)), le(w, w), True{}, rw))
      +i2c = Equal.trans(Nat, kle(~A, ~B, ~le, pre2, w), Nat.add(kle(~A, ~B, ~le, pre, w), 1n), Nat.add(pc, 1n), i2b, Equal.cong(Nat, Nat, z => Nat.add(z, 1n), kle(~A, ~B, ~le, pre, w), pc, ew))
      +ih = runs_ok(~A, ~B, ~le, ~le_total, ~le_trans, ~C, ~f, c, t, all, pre2, w, pc, 1n, y <> Nil{}, S.emit(B, ys, r0, acc), S.nxt(~A, ~B, ~le, t, w), {==}, ha2, hl2, hp2, i1c, i2c, hst, hwt)
      +ta = tot(~S.KV<B, Nat>, ~C, ~f, c, acc)
      +tv = totv(~B, ~C, ~f, c, ys, av(~A, ~B, ~le, all, v))
      +ts = tot(~S.KV<B, Nat>, ~C, ~f, c, spec1(~A, ~B, ~le, all, t))
      +fw = f(c, S.KV{y, av(~A, ~B, ~le, all, w)})
      +em = Equal.trans(Nat, tot(~S.KV<B, Nat>, ~C, ~f, c, S.emit(B, ys, r0, acc)), Nat.add(ta, totv(~B, ~C, ~f, c, ys, r0)), Nat.add(ta, tv), emit_tot(~B, ~C, ~f, c, ys, r0, acc), Equal.cong(Nat, Nat, z => Nat.add(ta, totv(~B, ~C, ~f, c, ys, z)), r0, av(~A, ~B, ~le, all, v), Equal.sym(Nat, av(~A, ~B, ~le, all, v), r0, e0)))
      +rest = Equal.cong(Nat, Nat, z => Nat.add(z, ts), Nat.add(fw, 0n), fw, RP.add_zero_r(fw))
      Equal.trans(Nat, tot(~S.KV<B, Nat>, ~C, ~f, c, S.runs(~A, ~B, ~le, t, w, pc, 1n, y <> Nil{}, S.emit(B, ys, r0, acc), S.nxt(~A, ~B, ~le, t, w))), Nat.add(tot(~S.KV<B, Nat>, ~C, ~f, c, S.emit(B, ys, r0, acc)), Nat.add(Nat.add(fw, 0n), ts)), Nat.add(ta, Nat.add(tv, Nat.add(fw, ts))), ih, Equal.trans(Nat, Nat.add(tot(~S.KV<B, Nat>, ~C, ~f, c, S.emit(B, ys, r0, acc)), Nat.add(Nat.add(fw, 0n), ts)), Nat.add(Nat.add(ta, tv), Nat.add(fw, ts)), Nat.add(ta, Nat.add(tv, Nat.add(fw, ts))), RP.add_eq(tot(~S.KV<B, Nat>, ~C, ~f, c, S.emit(B, ys, r0, acc)), Nat.add(ta, tv), Nat.add(Nat.add(fw, 0n), ts), Nat.add(fw, ts), em, rest), RP.add_assoc(ta, tv, Nat.add(fw, ts))))

# on a sorted list, the walk's output sums like the spec
def rk_ok(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, ~C: Data, ~f: C -> S.KV<B, Nat> -> Nat, +c: C, +s: List<&2, S.KV<A, B>>, +hs: SS(~A, ~B, ~le, s)) -> {tot(~S.KV<B, Nat>, ~C, ~f, c, S.rk(~A, ~B, ~le, s)) == tot(~S.KV<B, Nat>, ~C, ~f, c, spec1(~A, ~B, ~le, s, s)) : Nat}:
  match s:
    case Nil{}:
      {==}
    case Con{S.KV{+x, +y}, +t}:
      (hxt, hst) = hs
      +rx = refl(~A, ~le, ~le_total, x)
      +pre = {S.KV{x, y} <> Nil{} : List<&2, S.KV<A, B>>}
      +i1 = {(%Equal.sym(Bool, le(x, x), True{}, rx) : {Nat.add(Laws.ind(Bool.not(_)), 0n) == 0n : Nat}
        {==}) : {klt(~A, ~B, ~le, pre, x) == 0n : Nat}}
      +i2 = {(%Equal.sym(Bool, le(x, x), True{}, rx) : {Nat.add(Laws.ind(_), 0n) == 1n : Nat}
        {==}) : {kle(~A, ~B, ~le, pre, x) == Nat.add(0n, 1n) : Nat}}
      +all = {S.KV{x, y} <> t : List<&2, S.KV<A, B>>}
      +fy = f(c, S.KV{y, av(~A, ~B, ~le, all, x)})
      +ts = tot(~S.KV<B, Nat>, ~C, ~f, c, spec1(~A, ~B, ~le, all, t))
      Equal.trans(Nat, tot(~S.KV<B, Nat>, ~C, ~f, c, S.runs(~A, ~B, ~le, t, x, 0n, 1n, y <> Nil{}, Nil{}, S.nxt(~A, ~B, ~le, t, x))), Nat.add(Nat.add(fy, 0n), ts), Nat.add(fy, ts), runs_ok(~A, ~B, ~le, ~le_total, ~le_trans, ~C, ~f, c, t, all, pre, x, 0n, 1n, y <> Nil{}, Nil{}, S.nxt(~A, ~B, ~le, t, x), {==}, {==}, {==}, {(rx, Unit{}) : Le(~A, ~B, ~le, pre, x)}, i1, i2, hst, hxt), Equal.cong(Nat, Nat, z => Nat.add(z, ts), Nat.add(fy, 0n), fy, RP.add_zero_r(fy)))

# ---- the sort keeps the ranks, and so does a step

def klt_f(~A: Data, ~B: Data, ~le: A -> A -> Bool, q: A, x: S.KV<A, B>) -> Nat:
  Laws.ind(Bool.not(le(q, S.key(A, B, x))))

def kle_f(~A: Data, ~B: Data, ~le: A -> A -> Bool, q: A, x: S.KV<A, B>) -> Nat:
  Laws.ind(le(S.key(A, B, x), q))

def klt_tot(~A: Data, ~B: Data, ~le: A -> A -> Bool, +xs: List<&2, S.KV<A, B>>, +q: A) -> {klt(~A, ~B, ~le, xs, q) == tot(~S.KV<A, B>, ~A, ~klt_f(~A, ~B, ~le), q, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.cong(Nat, Nat, z => Nat.add(Laws.ind(Bool.not(le(q, S.key(A, B, x)))), z), klt(~A, ~B, ~le, t, q), tot(~S.KV<A, B>, ~A, ~klt_f(~A, ~B, ~le), q, t), klt_tot(~A, ~B, ~le, t, q))

def kle_tot(~A: Data, ~B: Data, ~le: A -> A -> Bool, +xs: List<&2, S.KV<A, B>>, +q: A) -> {kle(~A, ~B, ~le, xs, q) == tot(~S.KV<A, B>, ~A, ~kle_f(~A, ~B, ~le), q, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.cong(Nat, Nat, z => Nat.add(Laws.ind(le(S.key(A, B, x), q)), z), kle(~A, ~B, ~le, t, q), tot(~S.KV<A, B>, ~A, ~kle_f(~A, ~B, ~le), q, t), kle_tot(~A, ~B, ~le, t, q))

# two lists with the same count sums give every key the same rank
def av_from(~A: Data, ~B: Data, ~le: A -> A -> Bool, +a1: List<&2, S.KV<A, B>>, +a2: List<&2, S.KV<A, B>>, +q: A, +elt: {tot(~S.KV<A, B>, ~A, ~klt_f(~A, ~B, ~le), q, a1) == tot(~S.KV<A, B>, ~A, ~klt_f(~A, ~B, ~le), q, a2) : Nat}, +ele: {tot(~S.KV<A, B>, ~A, ~kle_f(~A, ~B, ~le), q, a1) == tot(~S.KV<A, B>, ~A, ~kle_f(~A, ~B, ~le), q, a2) : Nat}) -> {av(~A, ~B, ~le, a1, q) == av(~A, ~B, ~le, a2, q) : Nat}:
  +lt = Equal.trans(Nat, klt(~A, ~B, ~le, a1, q), tot(~S.KV<A, B>, ~A, ~klt_f(~A, ~B, ~le), q, a1), klt(~A, ~B, ~le, a2, q), klt_tot(~A, ~B, ~le, a1, q), Equal.trans(Nat, tot(~S.KV<A, B>, ~A, ~klt_f(~A, ~B, ~le), q, a1), tot(~S.KV<A, B>, ~A, ~klt_f(~A, ~B, ~le), q, a2), klt(~A, ~B, ~le, a2, q), elt, Equal.sym(Nat, klt(~A, ~B, ~le, a2, q), tot(~S.KV<A, B>, ~A, ~klt_f(~A, ~B, ~le), q, a2), klt_tot(~A, ~B, ~le, a2, q))))
  +ge = Equal.trans(Nat, kle(~A, ~B, ~le, a1, q), tot(~S.KV<A, B>, ~A, ~kle_f(~A, ~B, ~le), q, a1), kle(~A, ~B, ~le, a2, q), kle_tot(~A, ~B, ~le, a1, q), Equal.trans(Nat, tot(~S.KV<A, B>, ~A, ~kle_f(~A, ~B, ~le), q, a1), tot(~S.KV<A, B>, ~A, ~kle_f(~A, ~B, ~le), q, a2), kle(~A, ~B, ~le, a2, q), ele, Equal.sym(Nat, kle(~A, ~B, ~le, a2, q), tot(~S.KV<A, B>, ~A, ~kle_f(~A, ~B, ~le), q, a2), kle_tot(~A, ~B, ~le, a2, q))))
  Equal.cong(Nat, Nat, z => 1n+z, Nat.add(klt(~A, ~B, ~le, a1, q), kle(~A, ~B, ~le, a1, q)), Nat.add(klt(~A, ~B, ~le, a2, q), kle(~A, ~B, ~le, a2, q)), RP.add_eq(klt(~A, ~B, ~le, a1, q), klt(~A, ~B, ~le, a2, q), kle(~A, ~B, ~le, a1, q), kle(~A, ~B, ~le, a2, q), lt, ge))

def spec1_msort(~A: Data, ~B: Data, ~le: A -> A -> Bool, +ps: List<&2, S.KV<A, B>>, +l: List<&2, S.KV<A, B>>) -> {spec1(~A, ~B, ~le, S.msort(~A, ~B, ~le, ps), l) == spec1(~A, ~B, ~le, ps, l) : List<&2, S.KV<B, Nat>>}:
  match l:
    case Nil{}:
      {==}
    case Con{S.KV{+k, +v}, +t}:
      +m = {S.msort(~A, ~B, ~le, ps) : List<&2, S.KV<A, B>>}
      +e = av_from(~A, ~B, ~le, m, ps, k, tot_msort(~A, ~B, ~le, ~A, ~klt_f(~A, ~B, ~le), k, ps), tot_msort(~A, ~B, ~le, ~A, ~kle_f(~A, ~B, ~le), k, ps))
      Equal.trans(List<&2, S.KV<B, Nat>>, S.KV{v, av(~A, ~B, ~le, m, k)} <> spec1(~A, ~B, ~le, m, t), S.KV{v, av(~A, ~B, ~le, ps, k)} <> spec1(~A, ~B, ~le, m, t), S.KV{v, av(~A, ~B, ~le, ps, k)} <> spec1(~A, ~B, ~le, ps, t), Equal.cong(Nat, List<&2, S.KV<B, Nat>>, z => S.KV{v, z} <> spec1(~A, ~B, ~le, m, t), av(~A, ~B, ~le, m, k), av(~A, ~B, ~le, ps, k), e), Equal.cong(List<&2, S.KV<B, Nat>>, List<&2, S.KV<B, Nat>>, z => S.KV{v, av(~A, ~B, ~le, ps, k)} <> z, spec1(~A, ~B, ~le, m, t), spec1(~A, ~B, ~le, ps, t), spec1_msort(~A, ~B, ~le, ps, t)))

type FG<-C: Data, -A: Data, -B: Data> is Data:
  FG{c: C, all: List<&2, S.KV<A, B>>}

# f after the spec, as one function of the input pair
def fg(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~C: Data, ~f: C -> S.KV<B, Nat> -> Nat, g: FG<C, A, B>, x: S.KV<A, B>) -> Nat:
  FG{c, all} = g
  S.KV{k, v} = x
  f(c, S.KV{v, av(~A, ~B, ~le, all, k)})

def tot_spec1(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~C: Data, ~f: C -> S.KV<B, Nat> -> Nat, +c: C, +all: List<&2, S.KV<A, B>>, +l: List<&2, S.KV<A, B>>) -> {tot(~S.KV<B, Nat>, ~C, ~f, c, spec1(~A, ~B, ~le, all, l)) == tot(~S.KV<A, B>, ~FG<C, A, B>, ~fg(~A, ~B, ~le, ~C, ~f), FG{c, all}, l) : Nat}:
  match l:
    case Nil{}:
      {==}
    case Con{S.KV{+k, +v}, +t}:
      Equal.cong(Nat, Nat, z => Nat.add(f(c, S.KV{v, av(~A, ~B, ~le, all, k)}), z), tot(~S.KV<B, Nat>, ~C, ~f, c, spec1(~A, ~B, ~le, all, t)), tot(~S.KV<A, B>, ~FG<C, A, B>, ~fg(~A, ~B, ~le, ~C, ~f), FG{c, all}, t), tot_spec1(~A, ~B, ~le, ~C, ~f, c, all, t))

# sort and rank: every sum of the output is that sum of the spec
def step_ok(~A: Data, ~B: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, ~C: Data, ~f: C -> S.KV<B, Nat> -> Nat, +c: C, +ps: List<&2, S.KV<A, B>>) -> {tot(~S.KV<B, Nat>, ~C, ~f, c, S.step(~A, ~B, ~le, ps)) == tot(~S.KV<B, Nat>, ~C, ~f, c, spec1(~A, ~B, ~le, ps, ps)) : Nat}:
  +m = {S.msort(~A, ~B, ~le, ps) : List<&2, S.KV<A, B>>}
  +e1 = rk_ok(~A, ~B, ~le, ~le_total, ~le_trans, ~C, ~f, c, m, ss_msort(~A, ~B, ~le, ~le_total, ~le_trans, ps))
  +e2 = Equal.cong(List<&2, S.KV<B, Nat>>, Nat, z => tot(~S.KV<B, Nat>, ~C, ~f, c, z), spec1(~A, ~B, ~le, m, m), spec1(~A, ~B, ~le, ps, m), spec1_msort(~A, ~B, ~le, ps, m))
  +tf = tot(~S.KV<A, B>, ~FG<C, A, B>, ~fg(~A, ~B, ~le, ~C, ~f), FG{c, ps}, m)
  +e3 = Equal.trans(Nat, tot(~S.KV<B, Nat>, ~C, ~f, c, spec1(~A, ~B, ~le, ps, m)), tf, tot(~S.KV<B, Nat>, ~C, ~f, c, spec1(~A, ~B, ~le, ps, ps)), tot_spec1(~A, ~B, ~le, ~C, ~f, c, ps, m), Equal.trans(Nat, tf, tot(~S.KV<A, B>, ~FG<C, A, B>, ~fg(~A, ~B, ~le, ~C, ~f), FG{c, ps}, ps), tot(~S.KV<B, Nat>, ~C, ~f, c, spec1(~A, ~B, ~le, ps, ps)), tot_msort(~A, ~B, ~le, ~FG<C, A, B>, ~fg(~A, ~B, ~le, ~C, ~f), FG{c, ps}, ps), Equal.sym(Nat, tot(~S.KV<B, Nat>, ~C, ~f, c, spec1(~A, ~B, ~le, ps, ps)), tot(~S.KV<A, B>, ~FG<C, A, B>, ~fg(~A, ~B, ~le, ~C, ~f), FG{c, ps}, ps), tot_spec1(~A, ~B, ~le, ~C, ~f, c, ps, ps))))
  Equal.trans(Nat, tot(~S.KV<B, Nat>, ~C, ~f, c, S.rk(~A, ~B, ~le, m)), tot(~S.KV<B, Nat>, ~C, ~f, c, spec1(~A, ~B, ~le, m, m)), tot(~S.KV<B, Nat>, ~C, ~f, c, spec1(~A, ~B, ~le, ps, ps)), e1, Equal.trans(Nat, tot(~S.KV<B, Nat>, ~C, ~f, c, spec1(~A, ~B, ~le, m, m)), tot(~S.KV<B, Nat>, ~C, ~f, c, spec1(~A, ~B, ~le, ps, m)), tot(~S.KV<B, Nat>, ~C, ~f, c, spec1(~A, ~B, ~le, ps, ps)), e2, e3))

# ---- the two steps of rank2

def pc(r: S.KV<Nat, Nat>, x: S.KV<Nat, Nat>) -> Nat:
  Laws.ind(Laws.kv_eq(x, r))

def count_tot(+xs: List<&2, S.KV<Nat, Nat>>, +r: S.KV<Nat, Nat>) -> {Laws.count(xs, r) == tot(~S.KV<Nat, Nat>, ~S.KV<Nat, Nat>, ~pc, r, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.cong(Nat, Nat, z => Nat.add(Laws.ind(Laws.kv_eq(x, r)), z), Laws.count(t, r), tot(~S.KV<Nat, Nat>, ~S.KV<Nat, Nat>, ~pc, r, t), count_tot(t, r))

def keys_spec1(~A: Data, ~B: Data, ~le: A -> A -> Bool, +all: List<&2, S.KV<A, B>>, +l: List<&2, S.KV<A, B>>) -> {Laws.keys(B, Nat, spec1(~A, ~B, ~le, all, l)) == Laws.vals(A, B, l) : List<&2, B>}:
  match l:
    case Nil{}:
      {==}
    case Con{S.KV{+k, +v}, +t}:
      Equal.cong(List<&2, B>, List<&2, B>, z => v <> z, Laws.keys(B, Nat, spec1(~A, ~B, ~le, all, t)), Laws.vals(A, B, t), keys_spec1(~A, ~B, ~le, all, t))

# after the first step, ranking among its keys is ranking among the spec's
def spec1_step(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +ps: List<&2, S.KV<A, A>>, +l: List<&2, S.KV<A, Nat>>) -> {spec1(~A, ~Nat, ~le, S.step(~A, ~A, ~le, ps), l) == spec1(~A, ~Nat, ~le, spec1(~A, ~A, ~le, ps, ps), l) : List<&2, S.KV<Nat, Nat>>}:
  match l:
    case Nil{}:
      {==}
    case Con{S.KV{+k, +v}, +t}:
      +l1 = {S.step(~A, ~A, ~le, ps) : List<&2, S.KV<A, Nat>>}
      +s1 = {spec1(~A, ~A, ~le, ps, ps) : List<&2, S.KV<A, Nat>>}
      +e = av_from(~A, ~Nat, ~le, l1, s1, k, step_ok(~A, ~A, ~le, ~le_total, ~le_trans, ~A, ~klt_f(~A, ~Nat, ~le), k, ps), step_ok(~A, ~A, ~le, ~le_total, ~le_trans, ~A, ~kle_f(~A, ~Nat, ~le), k, ps))
      Equal.trans(List<&2, S.KV<Nat, Nat>>, S.KV{v, av(~A, ~Nat, ~le, l1, k)} <> spec1(~A, ~Nat, ~le, l1, t), S.KV{v, av(~A, ~Nat, ~le, s1, k)} <> spec1(~A, ~Nat, ~le, l1, t), S.KV{v, av(~A, ~Nat, ~le, s1, k)} <> spec1(~A, ~Nat, ~le, s1, t), Equal.cong(Nat, List<&2, S.KV<Nat, Nat>>, z => S.KV{v, z} <> spec1(~A, ~Nat, ~le, l1, t), av(~A, ~Nat, ~le, l1, k), av(~A, ~Nat, ~le, s1, k), e), Equal.cong(List<&2, S.KV<Nat, Nat>>, List<&2, S.KV<Nat, Nat>>, z => S.KV{v, av(~A, ~Nat, ~le, s1, k)} <> z, spec1(~A, ~Nat, ~le, l1, t), spec1(~A, ~Nat, ~le, s1, t), spec1_step(~A, ~le, ~le_total, ~le_trans, ps, t)))

def spec_final(~A: Data, ~le: A -> A -> Bool, +ps: List<&2, S.KV<A, A>>, +l: List<&2, S.KV<A, A>>) -> {spec1(~A, ~Nat, ~le, spec1(~A, ~A, ~le, ps, ps), spec1(~A, ~A, ~le, ps, l)) == Laws.spec_pairs(~A, ~le, l, Laws.keys(A, A, ps), Laws.vals(A, A, ps)) : List<&2, S.KV<Nat, Nat>>}:
  match l:
    case Nil{}:
      {==}
    case Con{S.KV{+x, +y}, +t}:
      +s1 = {spec1(~A, ~A, ~le, ps, ps) : List<&2, S.KV<A, Nat>>}
      +ax = av(~A, ~A, ~le, ps, x)
      +vs = Laws.vals(A, A, ps)
      +rest = spec1(~A, ~Nat, ~le, s1, spec1(~A, ~A, ~le, ps, t))
      Equal.trans(List<&2, S.KV<Nat, Nat>>, S.KV{ax, Laws.avg2(~A, ~le, Laws.keys(A, Nat, s1), y)} <> rest, S.KV{ax, Laws.avg2(~A, ~le, vs, y)} <> rest, S.KV{ax, Laws.avg2(~A, ~le, vs, y)} <> Laws.spec_pairs(~A, ~le, t, Laws.keys(A, A, ps), vs), Equal.cong(List<&2, A>, List<&2, S.KV<Nat, Nat>>, z => S.KV{ax, Laws.avg2(~A, ~le, z, y)} <> rest, Laws.keys(A, Nat, s1), vs, keys_spec1(~A, ~A, ~le, ps, ps)), Equal.cong(List<&2, S.KV<Nat, Nat>>, List<&2, S.KV<Nat, Nat>>, z => S.KV{ax, Laws.avg2(~A, ~le, vs, y)} <> z, rest, Laws.spec_pairs(~A, ~le, t, Laws.keys(A, A, ps), vs), spec_final(~A, ~le, ps, t)))

def rank_pairs(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}, +ps: List<&2, S.KV<A, A>>, +r: S.KV<Nat, Nat>) -> {Laws.count(S.rank2(~A, ~le, ps), r) == Laws.count(Laws.spec_pairs(~A, ~le, ps, Laws.keys(A, A, ps), Laws.vals(A, A, ps)), r) : Nat}:
  +l1 = {S.step(~A, ~A, ~le, ps) : List<&2, S.KV<A, Nat>>}
  +s1 = {spec1(~A, ~A, ~le, ps, ps) : List<&2, S.KV<A, Nat>>}
  +sp = {Laws.spec_pairs(~A, ~le, ps, Laws.keys(A, A, ps), Laws.vals(A, A, ps)) : List<&2, S.KV<Nat, Nat>>}
  +out = {S.step(~A, ~Nat, ~le, l1) : List<&2, S.KV<Nat, Nat>>}
  +t_out = tot(~S.KV<Nat, Nat>, ~S.KV<Nat, Nat>, ~pc, r, out)
  +t_ll = tot(~S.KV<Nat, Nat>, ~S.KV<Nat, Nat>, ~pc, r, spec1(~A, ~Nat, ~le, l1, l1))
  +t_f1 = tot(~S.KV<A, Nat>, ~FG<S.KV<Nat, Nat>, A, Nat>, ~fg(~A, ~Nat, ~le, ~S.KV<Nat, Nat>, ~pc), FG{r, l1}, l1)
  +t_fs = tot(~S.KV<A, Nat>, ~FG<S.KV<Nat, Nat>, A, Nat>, ~fg(~A, ~Nat, ~le, ~S.KV<Nat, Nat>, ~pc), FG{r, l1}, s1)
  +t_ls = tot(~S.KV<Nat, Nat>, ~S.KV<Nat, Nat>, ~pc, r, spec1(~A, ~Nat, ~le, l1, s1))
  +t_ss = tot(~S.KV<Nat, Nat>, ~S.KV<Nat, Nat>, ~pc, r, spec1(~A, ~Nat, ~le, s1, s1))
  +t_sp = tot(~S.KV<Nat, Nat>, ~S.KV<Nat, Nat>, ~pc, r, sp)
  +c1 = step_ok(~A, ~Nat, ~le, ~le_total, ~le_trans, ~S.KV<Nat, Nat>, ~pc, r, l1)
  +c2 = tot_spec1(~A, ~Nat, ~le, ~S.KV<Nat, Nat>, ~pc, r, l1, l1)
  +c3 = step_ok(~A, ~A, ~le, ~le_total, ~le_trans, ~FG<S.KV<Nat, Nat>, A, Nat>, ~fg(~A, ~Nat, ~le, ~S.KV<Nat, Nat>, ~pc), FG{r, l1}, ps)
  +c4 = Equal.sym(Nat, t_ls, t_fs, tot_spec1(~A, ~Nat, ~le, ~S.KV<Nat, Nat>, ~pc, r, l1, s1))
  +c5 = Equal.cong(List<&2, S.KV<Nat, Nat>>, Nat, z => tot(~S.KV<Nat, Nat>, ~S.KV<Nat, Nat>, ~pc, r, z), spec1(~A, ~Nat, ~le, l1, s1), spec1(~A, ~Nat, ~le, s1, s1), spec1_step(~A, ~le, ~le_total, ~le_trans, ps, s1))
  +c6 = Equal.cong(List<&2, S.KV<Nat, Nat>>, Nat, z => tot(~S.KV<Nat, Nat>, ~S.KV<Nat, Nat>, ~pc, r, z), spec1(~A, ~Nat, ~le, s1, s1), sp, spec_final(~A, ~le, ps, ps))
  +c7 = Equal.sym(Nat, Laws.count(sp, r), t_sp, count_tot(sp, r))
  Equal.trans(Nat, Laws.count(out, r), t_out, Laws.count(sp, r), count_tot(out, r), Equal.trans(Nat, t_out, t_ll, Laws.count(sp, r), c1, Equal.trans(Nat, t_ll, t_f1, Laws.count(sp, r), c2, Equal.trans(Nat, t_f1, t_fs, Laws.count(sp, r), c3, Equal.trans(Nat, t_fs, t_ls, Laws.count(sp, r), c4, Equal.trans(Nat, t_ls, t_ss, Laws.count(sp, r), c5, Equal.trans(Nat, t_ss, t_sp, Laws.count(sp, r), c6, c7)))))))
