import Base
import ./LAWS.bend as Laws
import ./linalg.bend as L
import bend-mathlib@0.1.0.0/list.bend as MList

# ---------------------------------------------------------------- from_rows

def Laws.from_rows_equal():
  {==}

def Laws.from_rows_ragged():
  {==}

def Laws.from_rows_ragged_last():
  {==}

def Laws.from_rows_empty():
  {==}

def Laws.mat_ok_rect():
  {==}

def Laws.mat_ok_wrong_m():
  {==}

def Laws.mat_ok_ragged():
  {==}

# ---------------------------------------------------------------- basic helpers

def false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : Bool.pick(Type, _, Empty, Unit)
  Unit{}

def nat_zero_t(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+_:
      Empty

def zero_ne_succ(n: Nat, e: {0n == 1n+n : Nat}) -> Empty:
  %e : nat_zero_t(_)
  Unit{}

def succ_ne_zero(n: Nat, e: {1n+n == 0n : Nat}) -> Empty:
  zero_ne_succ(n, Equal.sym(Nat, 1n+n, 0n, e))

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def nat_pred_eq(+a: Nat, +b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, pred, 1n+a, 1n+b, e)

def bool_and_l(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_ne_true(h))

def bool_and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_ne_true(h))

def nat_eq_sound(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, false_ne_true(h))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, false_ne_true(h))
    case 1n+p 1n+q:
      %nat_eq_sound(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

def nat_eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat_eq_refl(p)

def len_replicate(-A: Data, n: Nat, +x: A) -> {List.length(&2, A, List.replicate(A, n, x)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %len_replicate(A, p, x) : {1n+List.length(&2, A, List.replicate(A, p, x)) == 1n+_ : Nat}
      {==}

def replicate_nil_get(n: Nat, j: Nat, i: Nat) -> {L.mat_get(List.replicate(List<&2, F32>, n, Nil{}), j, i) == None{} : Maybe<&2, F32>}:
  match n j:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      replicate_nil_get(p, q, i)

def replicate_nil_ok(n: Nat) -> {L.Mat.rows.ok(List.replicate(List<&2, F32>, n, Nil{}), 0n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      replicate_nil_ok(p)

# ---------------------------------------------------------------- parallel map

def seq2(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, two: L.Two<A>, +c: C) -> List<&2, B>:
  L.Two{l, r} = two
  List.append(&2, B, L.pseq(~A, ~B, ~C, ~f, l, c), L.pseq(~A, ~B, ~C, ~f, r, c))

def cons_seq2(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, +h: A, +two: L.Two<A>, +c: C) -> {seq2(~A, ~B, ~C, ~f, L.split.cons(A, h, two), c) == f(c, h) <> seq2(~A, ~B, ~C, ~f, two, c) : List<&2, B>}:
  match two:
    case L.Two{l, r}:
      {==}

def split_seq(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, +k: Nat, +xs: List<&2, A>, +c: C) -> {seq2(~A, ~B, ~C, ~f, L.split(A, k, xs), c) == L.pseq(~A, ~B, ~C, ~f, xs, c) : List<&2, B>}:
  match k xs:
    case 0n Nil{}:
      {==}
    case 0n Con{h, t}:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{+h, +t}:
      %split_seq(~A, ~B, ~C, ~f, p, t, c) : {seq2(~A, ~B, ~C, ~f, L.split.cons(A, h, L.split(A, p, t)), c) == f(c, h) <> _ : List<&2, B>}
      cons_seq2(~A, ~B, ~C, ~f, h, L.split(A, p, t), c)

def par_seq(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, +d: Nat, +two: L.Two<A>, +h: U32, +r: U32, +c: C) -> {L.par(~A, ~B, ~C, ~f, d, two, h, r, c) == seq2(~A, ~B, ~C, ~f, two, c) : List<&2, B>}:
  match d:
    case 0n:
      match two:
        case L.Two{l, q}:
          {==}
    case 1n+e:
      match two:
        case L.Two{+l, +q}:
          +hl = (h >> 1n : U32)
          +hr = (r >> 1n : U32)
          +pl = L.par(~A, ~B, ~C, ~f, e, L.split(A, U32.to_nat(hl), l), hl, (h - hl : U32), c)
          +pr = L.par(~A, ~B, ~C, ~f, e, L.split(A, U32.to_nat(hr), q), hr, (r - hr : U32), c)
          el = Equal.trans(List<&2, B>, pl, seq2(~A, ~B, ~C, ~f, L.split(A, U32.to_nat(hl), l), c), L.pseq(~A, ~B, ~C, ~f, l, c), par_seq(~A, ~B, ~C, ~f, e, L.split(A, U32.to_nat(hl), l), hl, (h - hl : U32), c), split_seq(~A, ~B, ~C, ~f, U32.to_nat(hl), l, c))
          er = Equal.trans(List<&2, B>, pr, seq2(~A, ~B, ~C, ~f, L.split(A, U32.to_nat(hr), q), c), L.pseq(~A, ~B, ~C, ~f, q, c), par_seq(~A, ~B, ~C, ~f, e, L.split(A, U32.to_nat(hr), q), hr, (r - hr : U32), c), split_seq(~A, ~B, ~C, ~f, U32.to_nat(hr), q, c))
          %el : {List.append(&2, B, pl, pr) == List.append(&2, B, _, L.pseq(~A, ~B, ~C, ~f, q, c)) : List<&2, B>}
          %er : {List.append(&2, B, pl, pr) == List.append(&2, B, pl, _) : List<&2, B>}
          {==}

def Laws.pmap_seq(A, B, C, f, xs, t, c):
  +k = U32.to_nat((t >> 1n : U32))
  +d = Bool.pick(Nat, U32.is_lt(t, 64), 0n, 5n)
  +sp = L.split(A, k, xs)
  Equal.trans(List<&2, B>, L.par(~A, ~B, ~C, ~f, d, sp, (t >> 1n : U32), (t - (t >> 1n : U32) : U32), c), seq2(~A, ~B, ~C, ~f, sp, c), L.pseq(~A, ~B, ~C, ~f, xs, c), par_seq(~A, ~B, ~C, ~f, d, sp, (t >> 1n : U32), (t - (t >> 1n : U32) : U32), c), split_seq(~A, ~B, ~C, ~f, k, xs, c))

def Laws.pseq_get(A, B, C, f, xs, c, i):
  match xs i:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      Laws.pseq_get(~A, ~B, ~C, ~f, t, c, p)

# ---------------------------------------------------------------- zip_cons & transpose

def zip_cons_len(r: List<&2, F32>, cols: List<&2, List<&2, F32>>, h: {List.length(&2, F32, r) == List.length(&2, List<&2, F32>, cols) : Nat}) -> {List.length(&2, List<&2, F32>, L.zip_cons(r, cols)) == List.length(&2, F32, r) : Nat}:
  match r cols:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{c, ct}:
      Empty.absurd({0n == 0n : Nat}, zero_ne_succ(List.length(&2, List<&2, F32>, ct), h))
    case Con{x, xt} Nil{}:
      Empty.absurd({0n == 1n+List.length(&2, F32, xt) : Nat}, succ_ne_zero(List.length(&2, F32, xt), h))
    case Con{x, +xt} Con{c, +ct}:
      %zip_cons_len(xt, ct, nat_pred_eq(List.length(&2, F32, xt), List.length(&2, List<&2, F32>, ct), h)) : {1n+List.length(&2, List<&2, F32>, L.zip_cons(xt, ct)) == 1n+_ : Nat}
      {==}

def Laws.transpose_len(rows, n, h):
  match rows:
    case Nil{}:
      len_replicate(List<&2, F32>, n, Nil{})
    case Con{+r, +rs}:
      +hr = nat_eq_sound(List.length(&2, F32, r), n, bool_and_l(Nat.is_eq(List.length(&2, F32, r), n), L.Mat.rows.ok(rs, n), h))
      +hrs = bool_and_r(Nat.is_eq(List.length(&2, F32, r), n), L.Mat.rows.ok(rs, n), h)
      +ih = Laws.transpose_len(rs, n, hrs)
      +eq = Equal.trans(Nat, List.length(&2, F32, r), n, List.length(&2, List<&2, F32>, L.transpose.rows(rs, n)), hr, Equal.sym(Nat, List.length(&2, List<&2, F32>, L.transpose.rows(rs, n)), n, ih))
      Equal.trans(Nat, List.length(&2, List<&2, F32>, L.zip_cons(r, L.transpose.rows(rs, n))), List.length(&2, F32, r), n, zip_cons_len(r, L.transpose.rows(rs, n), eq), hr)

def zip_cons_ok(r: List<&2, F32>, cols: List<&2, List<&2, F32>>, +m: Nat, hr: {List.length(&2, F32, r) == List.length(&2, List<&2, F32>, cols) : Nat}, +hc: {L.Mat.rows.ok(cols, m) == True{} : Bool}) -> {L.Mat.rows.ok(L.zip_cons(r, cols), 1n+m) == True{} : Bool}:
  match r cols:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{c, ct}:
      Empty.absurd({True{} == True{} : Bool}, zero_ne_succ(List.length(&2, List<&2, F32>, ct), hr))
    case Con{x, xt} Nil{}:
      Empty.absurd({True{} == True{} : Bool}, succ_ne_zero(List.length(&2, F32, xt), hr))
    case Con{x, +xt} Con{+c, +ct}:
      +hc1 = bool_and_l(Nat.is_eq(List.length(&2, F32, c), m), L.Mat.rows.ok(ct, m), hc)
      +hc2 = bool_and_r(Nat.is_eq(List.length(&2, F32, c), m), L.Mat.rows.ok(ct, m), hc)
      %Equal.sym(Bool, Nat.is_eq(List.length(&2, F32, c), m), True{}, hc1) : {Bool.and(_, L.Mat.rows.ok(L.zip_cons(xt, ct), 1n+m)) == True{} : Bool}
      zip_cons_ok(xt, ct, m, nat_pred_eq(List.length(&2, F32, xt), List.length(&2, List<&2, F32>, ct), hr), hc2)

def Laws.transpose_row_len(rows, n, h):
  match rows:
    case Nil{}:
      replicate_nil_ok(n)
    case Con{+r, +rs}:
      +hr = nat_eq_sound(List.length(&2, F32, r), n, bool_and_l(Nat.is_eq(List.length(&2, F32, r), n), L.Mat.rows.ok(rs, n), h))
      +hrs = bool_and_r(Nat.is_eq(List.length(&2, F32, r), n), L.Mat.rows.ok(rs, n), h)
      +hl = Laws.transpose_len(rs, n, hrs)
      +eq = Equal.trans(Nat, List.length(&2, F32, r), n, List.length(&2, List<&2, F32>, L.transpose.rows(rs, n)), hr, Equal.sym(Nat, List.length(&2, List<&2, F32>, L.transpose.rows(rs, n)), n, hl))
      zip_cons_ok(r, L.transpose.rows(rs, n), List.length(&2, List<&2, F32>, rs), eq, Laws.transpose_row_len(rs, n, hrs))

def zip_cons_get_zero(xs: List<&2, F32>, rows: List<&2, List<&2, F32>>, j: Nat, h: {List.length(&2, F32, xs) == List.length(&2, List<&2, F32>, rows) : Nat}) -> {L.mat_get(L.zip_cons(xs, rows), j, 0n) == List.get(&2, F32, xs, j) : Maybe<&2, F32>}:
  match xs rows j:
    case Nil{} Nil{} _:
      {==}
    case Nil{} Con{c, ct} _:
      Empty.absurd({None{} == None{} : Maybe<&2, F32>}, zero_ne_succ(List.length(&2, List<&2, F32>, ct), h))
    case Con{x, xt} Nil{} _:
      Empty.absurd({None{} == List.get(&2, F32, x <> xt, j) : Maybe<&2, F32>}, succ_ne_zero(List.length(&2, F32, xt), h))
    case Con{x, xt} Con{r, rt} 0n:
      {==}
    case Con{x, +xt} Con{r, +rt} 1n+p:
      zip_cons_get_zero(xt, rt, p, nat_pred_eq(List.length(&2, F32, xt), List.length(&2, List<&2, F32>, rt), h))

def zip_cons_get_succ(xs: List<&2, F32>, rows: List<&2, List<&2, F32>>, j: Nat, +i: Nat, h: {List.length(&2, F32, xs) == List.length(&2, List<&2, F32>, rows) : Nat}) -> {L.mat_get(L.zip_cons(xs, rows), j, 1n+i) == L.mat_get(rows, j, i) : Maybe<&2, F32>}:
  match xs rows j:
    case Nil{} Nil{} _:
      {==}
    case Nil{} Con{c, ct} _:
      Empty.absurd({None{} == L.mat_get(c <> ct, j, i) : Maybe<&2, F32>}, zero_ne_succ(List.length(&2, List<&2, F32>, ct), h))
    case Con{x, xt} Nil{} _:
      Empty.absurd({None{} == None{} : Maybe<&2, F32>}, succ_ne_zero(List.length(&2, F32, xt), h))
    case Con{x, xt} Con{r, rt} 0n:
      {==}
    case Con{x, +xt} Con{r, +rt} 1n+p:
      zip_cons_get_succ(xt, rt, p, i, nat_pred_eq(List.length(&2, F32, xt), List.length(&2, List<&2, F32>, rt), h))

def Laws.transpose_get(rows, n, i, j, h):
  match rows i:
    case Nil{} _:
      replicate_nil_get(n, j, i)
    case Con{+r, +rs} 0n:
      +hr = nat_eq_sound(List.length(&2, F32, r), n, bool_and_l(Nat.is_eq(List.length(&2, F32, r), n), L.Mat.rows.ok(rs, n), h))
      +hrs = bool_and_r(Nat.is_eq(List.length(&2, F32, r), n), L.Mat.rows.ok(rs, n), h)
      +hl = Laws.transpose_len(rs, n, hrs)
      +eq = Equal.trans(Nat, List.length(&2, F32, r), n, List.length(&2, List<&2, F32>, L.transpose.rows(rs, n)), hr, Equal.sym(Nat, List.length(&2, List<&2, F32>, L.transpose.rows(rs, n)), n, hl))
      zip_cons_get_zero(r, L.transpose.rows(rs, n), j, eq)
    case Con{+r, +rs} 1n+p:
      +hr = nat_eq_sound(List.length(&2, F32, r), n, bool_and_l(Nat.is_eq(List.length(&2, F32, r), n), L.Mat.rows.ok(rs, n), h))
      +hrs = bool_and_r(Nat.is_eq(List.length(&2, F32, r), n), L.Mat.rows.ok(rs, n), h)
      +hl = Laws.transpose_len(rs, n, hrs)
      +eq = Equal.trans(Nat, List.length(&2, F32, r), n, List.length(&2, List<&2, F32>, L.transpose.rows(rs, n)), hr, Equal.sym(Nat, List.length(&2, List<&2, F32>, L.transpose.rows(rs, n)), n, hl))
      Equal.trans(Maybe<&2, F32>, L.mat_get(L.zip_cons(r, L.transpose.rows(rs, n)), j, 1n+p), L.mat_get(L.transpose.rows(rs, n), j, p), L.mat_get(rs, p, j), zip_cons_get_succ(r, L.transpose.rows(rs, n), j, p, eq), Laws.transpose_get(rs, n, p, j, hrs))

def transpose_rep_nil(n: Nat) -> {L.transpose.rows(List.replicate(List<&2, F32>, n, Nil{}), 0n) == Nil{} : List<&2, List<&2, F32>>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def transpose_zip_cons(r: List<&2, F32>, cols: List<&2, List<&2, F32>>, +m: Nat, h: {List.length(&2, F32, r) == List.length(&2, List<&2, F32>, cols) : Nat}) -> {L.transpose.rows(L.zip_cons(r, cols), 1n+m) == r <> L.transpose.rows(cols, m) : List<&2, List<&2, F32>>}:
  match r cols:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{c, ct}:
      Empty.absurd({List.replicate(List<&2, F32>, 1n+m, Nil{}) == Nil{} <> L.transpose.rows(c <> ct, m) : List<&2, List<&2, F32>>}, zero_ne_succ(List.length(&2, List<&2, F32>, ct), h))
    case Con{x, xt} Nil{}:
      Empty.absurd({List.replicate(List<&2, F32>, 1n+m, Nil{}) == (x <> xt) <> List.replicate(List<&2, F32>, m, Nil{}) : List<&2, List<&2, F32>>}, succ_ne_zero(List.length(&2, F32, xt), h))
    case Con{+x, +xt} Con{+c, +ct}:
      %transpose_zip_cons(xt, ct, m, nat_pred_eq(List.length(&2, F32, xt), List.length(&2, List<&2, F32>, ct), h)) : {L.zip_cons(x <> c, L.transpose.rows(L.zip_cons(xt, ct), 1n+m)) == L.zip_cons(x <> c, _) : List<&2, List<&2, F32>>}
      {==}

def Laws.transpose_involutive(rows, n, h):
  match rows:
    case Nil{}:
      transpose_rep_nil(n)
    case Con{+r, +rs}:
      +hr = nat_eq_sound(List.length(&2, F32, r), n, bool_and_l(Nat.is_eq(List.length(&2, F32, r), n), L.Mat.rows.ok(rs, n), h))
      +hrs = bool_and_r(Nat.is_eq(List.length(&2, F32, r), n), L.Mat.rows.ok(rs, n), h)
      +hl = Laws.transpose_len(rs, n, hrs)
      +eq = Equal.trans(Nat, List.length(&2, F32, r), n, List.length(&2, List<&2, F32>, L.transpose.rows(rs, n)), hr, Equal.sym(Nat, List.length(&2, List<&2, F32>, L.transpose.rows(rs, n)), n, hl))
      %Equal.sym(List<&2, List<&2, F32>>, L.transpose.rows(L.zip_cons(r, L.transpose.rows(rs, n)), 1n+List.length(&2, List<&2, F32>, rs)), r <> L.transpose.rows(L.transpose.rows(rs, n), List.length(&2, List<&2, F32>, rs)), transpose_zip_cons(r, L.transpose.rows(rs, n), List.length(&2, List<&2, F32>, rs), eq)) : {_ == r <> rs : List<&2, List<&2, F32>>}
      %Laws.transpose_involutive(rs, n, hrs) : {r <> L.transpose.rows(L.transpose.rows(rs, n), List.length(&2, List<&2, F32>, rs)) == r <> _ : List<&2, List<&2, F32>>}
      {==}

def rows_ok_eq(+rows: List<&2, List<&2, F32>>, +a: Nat, +b: Nat, e: {a == b : Nat}, h: {L.Mat.rows.ok(rows, a) == True{} : Bool}) -> {L.Mat.rows.ok(rows, b) == True{} : Bool}:
  %e : {L.Mat.rows.ok(rows, _) == True{} : Bool}
  h

# Mat.ok from its two halves.
def mat_ok_intro(+m: U32, +n: U32, +rows: List<&2, List<&2, F32>>, hl: {List.length(&2, List<&2, F32>, rows) == U32.to_nat(m) : Nat}, +hr: {L.Mat.rows.ok(rows, U32.to_nat(n)) == True{} : Bool}) -> {L.Mat.ok(L.Mat{m, n, rows}) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, List<&2, F32>, rows), U32.to_nat(m), hl) : {Bool.and(Nat.is_eq(_, U32.to_nat(m)), L.Mat.rows.ok(rows, U32.to_nat(n))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(U32.to_nat(m), U32.to_nat(m)), True{}, nat_eq_refl(U32.to_nat(m))) : {Bool.and(_, L.Mat.rows.ok(rows, U32.to_nat(n))) == True{} : Bool}
  hr

def Laws.transpose_ok(a, h):
  match a:
    case L.Mat{+m, +n, +rows}:
      +nn = U32.to_nat(n)
      +hl = nat_eq_sound(List.length(&2, List<&2, F32>, rows), U32.to_nat(m), bool_and_l(Nat.is_eq(List.length(&2, List<&2, F32>, rows), U32.to_nat(m)), L.Mat.rows.ok(rows, nn), h))
      +hr = bool_and_r(Nat.is_eq(List.length(&2, List<&2, F32>, rows), U32.to_nat(m)), L.Mat.rows.ok(rows, nn), h)
      mat_ok_intro(n, m, L.transpose.rows(rows, nn), Laws.transpose_len(rows, nn, hr), rows_ok_eq(L.transpose.rows(rows, nn), List.length(&2, List<&2, F32>, rows), U32.to_nat(m), hl, Laws.transpose_row_len(rows, nn, hr)))

# ---------------------------------------------------------------- products

def pseq_len(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, xs: List<&2, A>, +c: C) -> {List.length(&2, B, L.pseq(~A, ~B, ~C, ~f, xs, c)) == List.length(&2, A, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %pseq_len(~A, ~B, ~C, ~f, t, c) : {1n+List.length(&2, B, L.pseq(~A, ~B, ~C, ~f, t, c)) == 1n+_ : Nat}
      {==}

def Laws.matvec_entry(ma, na, nx, ra, xs, i, e):
  %Equal.sym(Bool, U32.is_eq(na, nx), True{}, e) : {Laws.mv_get(L.matvec.chk(_, ma, ra, xs), i) == Laws.fmap(~List<&2, F32>, ~F32, ~List<&2, F32>, ~L.matvec.row, xs, List.get(&2, List<&2, F32>, ra, i)) : Maybe<&2, F32>}
  %Equal.sym(List<&2, F32>, L.pmap(~List<&2, F32>, ~F32, ~List<&2, F32>, ~L.matvec.row, ra, ma, xs), L.pseq(~List<&2, F32>, ~F32, ~List<&2, F32>, ~L.matvec.row, ra, xs), Laws.pmap_seq(~List<&2, F32>, ~F32, ~List<&2, F32>, ~L.matvec.row, ra, ma, xs)) : {List.get(&2, F32, _, i) == Laws.fmap(~List<&2, F32>, ~F32, ~List<&2, F32>, ~L.matvec.row, xs, List.get(&2, List<&2, F32>, ra, i)) : Maybe<&2, F32>}
  Laws.pseq_get(~List<&2, F32>, ~F32, ~List<&2, F32>, ~L.matvec.row, ra, xs, i)

def matmul_dots_get(+r: List<&2, F32>, cols: List<&2, List<&2, F32>>, j: Nat) -> {List.get(&2, F32, L.matmul.dots(r, cols), j) == Laws.opt_dot(Some{r}, List.get(&2, List<&2, F32>, cols, j)) : Maybe<&2, F32>}:
  match cols j:
    case Nil{} _:
      {==}
    case Con{c, ct} 0n:
      {==}
    case Con{c, ct} 1n+p:
      matmul_dots_get(r, ct, p)

def row_get_fmap(mr: Maybe<&2, List<&2, F32>>, +bcols: List<&2, List<&2, F32>>, +j: Nat) -> {L.row_get(Laws.fmap(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, bcols, mr), j) == Laws.opt_dot(mr, List.get(&2, List<&2, F32>, bcols, j)) : Maybe<&2, F32>}:
  match mr:
    case None{}:
      {==}
    case Some{r}:
      matmul_dots_get(r, bcols, j)

def Laws.matmul_entry(ma, na, mb, nb, ra, rb, i, j, e):
  +bcols = L.transpose.rows(rb, U32.to_nat(nb))
  %Equal.sym(Bool, U32.is_eq(na, mb), True{}, e) : {Laws.mm_get(L.matmul.chk(_, ma, nb, ra, rb), i, j) == Laws.opt_dot(List.get(&2, List<&2, F32>, ra, i), List.get(&2, List<&2, F32>, bcols, j)) : Maybe<&2, F32>}
  %Equal.sym(List<&2, List<&2, F32>>, L.pmap(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, ra, ma, bcols), L.pseq(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, ra, bcols), Laws.pmap_seq(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, ra, ma, bcols)) : {L.mat_get(_, i, j) == Laws.opt_dot(List.get(&2, List<&2, F32>, ra, i), List.get(&2, List<&2, F32>, bcols, j)) : Maybe<&2, F32>}
  %Equal.sym(Maybe<&2, List<&2, F32>>, List.get(&2, List<&2, F32>, L.pseq(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, ra, bcols), i), Laws.fmap(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, bcols, List.get(&2, List<&2, F32>, ra, i)), Laws.pseq_get(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, ra, bcols, i)) : {L.row_get(_, j) == Laws.opt_dot(List.get(&2, List<&2, F32>, ra, i), List.get(&2, List<&2, F32>, bcols, j)) : Maybe<&2, F32>}
  row_get_fmap(List.get(&2, List<&2, F32>, ra, i), bcols, j)

def Laws.matvec_ok(ma, na, nx, ra, xs, e, ha):
  %Equal.sym(Bool, U32.is_eq(na, nx), True{}, e) : {Laws.mv_ok(L.matvec.chk(_, ma, ra, xs)) == True{} : Bool}
  %Equal.sym(List<&2, F32>, L.pmap(~List<&2, F32>, ~F32, ~List<&2, F32>, ~L.matvec.row, ra, ma, xs), L.pseq(~List<&2, F32>, ~F32, ~List<&2, F32>, ~L.matvec.row, ra, xs), Laws.pmap_seq(~List<&2, F32>, ~F32, ~List<&2, F32>, ~L.matvec.row, ra, ma, xs)) : {L.Vec.ok(L.Vec{ma, _}) == True{} : Bool}
  %Equal.sym(Nat, List.length(&2, F32, L.pseq(~List<&2, F32>, ~F32, ~List<&2, F32>, ~L.matvec.row, ra, xs)), List.length(&2, List<&2, F32>, ra), pseq_len(~List<&2, F32>, ~F32, ~List<&2, F32>, ~L.matvec.row, ra, xs)) : {Nat.is_eq(_, U32.to_nat(ma)) == True{} : Bool}
  bool_and_l(Nat.is_eq(List.length(&2, List<&2, F32>, ra), U32.to_nat(ma)), L.Mat.rows.ok(ra, U32.to_nat(na)), ha)

def matmul_dots_len(+r: List<&2, F32>, cols: List<&2, List<&2, F32>>) -> {List.length(&2, F32, L.matmul.dots(r, cols)) == List.length(&2, List<&2, F32>, cols) : Nat}:
  match cols:
    case Nil{}:
      {==}
    case Con{c, ct}:
      %matmul_dots_len(r, ct) : {1n+List.length(&2, F32, L.matmul.dots(r, ct)) == 1n+_ : Nat}
      {==}

# Every row of matmul's row loop has one entry per column of B.
def mm_rows_ok(ra: List<&2, List<&2, F32>>, +bcols: List<&2, List<&2, F32>>, +n: Nat, +h: {List.length(&2, List<&2, F32>, bcols) == n : Nat}) -> {L.Mat.rows.ok(L.pseq(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, ra, bcols), n) == True{} : Bool}:
  match ra:
    case Nil{}:
      {==}
    case Con{+r, t}:
      +hl = Equal.trans(Nat, List.length(&2, F32, L.matmul.dots(r, bcols)), List.length(&2, List<&2, F32>, bcols), n, matmul_dots_len(r, bcols), h)
      %Equal.sym(Nat, List.length(&2, F32, L.matmul.dots(r, bcols)), n, hl) : {Bool.and(Nat.is_eq(_, n), L.Mat.rows.ok(L.pseq(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, t, bcols), n)) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(n, n), True{}, nat_eq_refl(n)) : {Bool.and(_, L.Mat.rows.ok(L.pseq(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, t, bcols), n)) == True{} : Bool}
      mm_rows_ok(t, bcols, n, h)

def Laws.matmul_ok(ma, na, mb, nb, ra, rb, e, ha, hb):
  +nn = U32.to_nat(nb)
  +bcols = L.transpose.rows(rb, nn)
  +rows = L.pseq(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, ra, bcols)
  %Equal.sym(Bool, U32.is_eq(na, mb), True{}, e) : {Laws.mm_ok(L.matmul.chk(_, ma, nb, ra, rb)) == True{} : Bool}
  %Equal.sym(List<&2, List<&2, F32>>, L.pmap(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, ra, ma, bcols), rows, Laws.pmap_seq(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, ra, ma, bcols)) : {L.Mat.ok(L.Mat{ma, nb, _}) == True{} : Bool}
  +hra = nat_eq_sound(List.length(&2, List<&2, F32>, ra), U32.to_nat(ma), bool_and_l(Nat.is_eq(List.length(&2, List<&2, F32>, ra), U32.to_nat(ma)), L.Mat.rows.ok(ra, U32.to_nat(na)), ha))
  +hrb = bool_and_r(Nat.is_eq(List.length(&2, List<&2, F32>, rb), U32.to_nat(mb)), L.Mat.rows.ok(rb, nn), hb)
  +hl = Equal.trans(Nat, List.length(&2, List<&2, F32>, rows), List.length(&2, List<&2, F32>, ra), U32.to_nat(ma), pseq_len(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, ra, bcols), hra)
  mat_ok_intro(ma, nb, rows, hl, mm_rows_ok(ra, bcols, nn, Laws.transpose_len(rb, nn, hrb)))

def Laws.matmul_mismatch(ma, na, mb, nb, ra, rb, e):
  %Equal.sym(Bool, U32.is_eq(na, mb), False{}, e) : {L.matmul.chk(_, ma, nb, ra, rb) == None{} : Maybe<&2, L.Mat>}
  {==}

# ---------------------------------------------------------------- Gram symmetry

def mirror_upper_len(up: List<&2, List<&2, F32>>, +n: Nat, +h: {Laws.upper_ok(up, n) == True{} : Bool}) -> {List.length(&2, List<&2, F32>, L.mirror_upper(up)) == n : Nat}:
  match up n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      Empty.absurd({0n == 1n+p : Nat}, false_ne_true(h))
    case Con{r, t} 0n:
      Empty.absurd({List.length(&2, List<&2, F32>, L.mirror_upper(r <> t)) == 0n : Nat}, false_ne_true(h))
    case Con{Nil{}, sub} 1n+p:
      Empty.absurd({1n+List.length(&2, List<&2, F32>, L.mirror_upper(sub)) == 1n+p : Nat}, false_ne_true(bool_and_l(Nat.is_eq(0n, 1n+p), Laws.upper_ok(sub, p), h)))
    case Con{Con{d, +rest}, +sub} 1n+p:
      +h1 = nat_eq_sound(List.length(&2, F32, rest), p, bool_and_l(Nat.is_eq(List.length(&2, F32, rest), p), Laws.upper_ok(sub, p), h))
      +h2 = bool_and_r(Nat.is_eq(List.length(&2, F32, rest), p), Laws.upper_ok(sub, p), h)
      +ih = mirror_upper_len(sub, p, h2)
      +eq = Equal.trans(Nat, List.length(&2, F32, rest), p, List.length(&2, List<&2, F32>, L.mirror_upper(sub)), h1, Equal.sym(Nat, List.length(&2, List<&2, F32>, L.mirror_upper(sub)), p, ih))
      +zl = Equal.trans(Nat, List.length(&2, List<&2, F32>, L.zip_cons(rest, L.mirror_upper(sub))), List.length(&2, F32, rest), p, zip_cons_len(rest, L.mirror_upper(sub), eq), h1)
      %zl : {1n+List.length(&2, List<&2, F32>, L.zip_cons(rest, L.mirror_upper(sub))) == 1n+_ : Nat}
      {==}

def mirror_upper_eq(+d: F32, +rest: List<&2, F32>, +sub: List<&2, List<&2, F32>>, +p: Nat, +h: {Laws.upper_ok((d <> rest) <> sub, 1n+p) == True{} : Bool}) -> {List.length(&2, F32, rest) == List.length(&2, List<&2, F32>, L.mirror_upper(sub)) : Nat}:
  +h1 = nat_eq_sound(List.length(&2, F32, rest), p, bool_and_l(Nat.is_eq(List.length(&2, F32, rest), p), Laws.upper_ok(sub, p), h))
  +h2 = bool_and_r(Nat.is_eq(List.length(&2, F32, rest), p), Laws.upper_ok(sub, p), h)
  +ml = mirror_upper_len(sub, p, h2)
  Equal.trans(Nat, List.length(&2, F32, rest), p, List.length(&2, List<&2, F32>, L.mirror_upper(sub)), h1, Equal.sym(Nat, List.length(&2, List<&2, F32>, L.mirror_upper(sub)), p, ml))

def Laws.mirror_upper_sym(up, n, i, j, h):
  match up n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      Empty.absurd({None{} == None{} : Maybe<&2, F32>}, false_ne_true(h))
    case Con{r, t} 0n:
      Empty.absurd({L.mat_get(L.mirror_upper(r <> t), i, j) == L.mat_get(L.mirror_upper(r <> t), j, i) : Maybe<&2, F32>}, false_ne_true(h))
    case Con{Nil{}, sub} 1n+p:
      Empty.absurd({L.mat_get(Nil{} <> L.mirror_upper(sub), i, j) == L.mat_get(Nil{} <> L.mirror_upper(sub), j, i) : Maybe<&2, F32>}, false_ne_true(bool_and_l(Nat.is_eq(0n, 1n+p), Laws.upper_ok(sub, p), h)))
    case Con{Con{+d, +rest}, +sub} 1n+p:
      match i j:
        case 0n 0n:
          {==}
        case 0n 1n+q:
          +eq = mirror_upper_eq(d, rest, sub, p, h)
          Equal.sym(Maybe<&2, F32>, L.mat_get(L.zip_cons(rest, L.mirror_upper(sub)), q, 0n), List.get(&2, F32, rest, q), zip_cons_get_zero(rest, L.mirror_upper(sub), q, eq))
        case 1n+r 0n:
          +eq = mirror_upper_eq(d, rest, sub, p, h)
          zip_cons_get_zero(rest, L.mirror_upper(sub), r, eq)
        case 1n+r 1n+q:
          +eq = mirror_upper_eq(d, rest, sub, p, h)
          +h2 = bool_and_r(Nat.is_eq(List.length(&2, F32, rest), p), Laws.upper_ok(sub, p), h)
          %Equal.sym(Maybe<&2, F32>, L.mat_get(L.zip_cons(rest, L.mirror_upper(sub)), r, 1n+q), L.mat_get(L.mirror_upper(sub), r, q), zip_cons_get_succ(rest, L.mirror_upper(sub), r, q, eq)) : {_ == L.mat_get(L.zip_cons(rest, L.mirror_upper(sub)), q, 1n+r) : Maybe<&2, F32>}
          %Equal.sym(Maybe<&2, F32>, L.mat_get(L.zip_cons(rest, L.mirror_upper(sub)), q, 1n+r), L.mat_get(L.mirror_upper(sub), q, r), zip_cons_get_succ(rest, L.mirror_upper(sub), q, r, eq)) : {L.mat_get(L.mirror_upper(sub), r, q) == _ : Maybe<&2, F32>}
          Laws.mirror_upper_sym(sub, p, r, q, h2)

# ---------------------------------------------------------------- Cholesky & solves

def add_succ_r(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ_r(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def add_zero_r(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero_r(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def sub_zero_r(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def min_add_sub(a: Nat, b: Nat) -> {Nat.add(Nat.min(a, b), Nat.sub(b, Nat.min(a, b))) == b : Nat}:
  match a b:
    case 0n _:
      sub_zero_r(b)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %min_add_sub(p, q) : {1n+Nat.add(Nat.min(p, q), Nat.sub(q, Nat.min(p, q))) == 1n+_ : Nat}
      {==}

def lt_min_left(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  match a b:
    case 0n 0n:
      Empty.absurd({0n == 0n : Nat}, false_ne_true(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({0n == 1n+p : Nat}, false_ne_true(h))
    case 1n+p 1n+q:
      %lt_min_left(p, q, h) : {1n+Nat.min(p, q) == 1n+_ : Nat}
      {==}

def lt_add_left(a: Nat, +b: Nat, c: Nat, h: {Nat.is_lt(Nat.add(a, b), c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n 0n:
      h
    case 0n 1n+_ 0n:
      h
    case 0n _ 1n+q:
      {==}
    case 1n+p _ 0n:
      Empty.absurd({False{} == True{} : Bool}, false_ne_true(h))
    case 1n+p _ 1n+q:
      lt_add_left(p, b, q, h)

def lt_sub_of_add(a: Nat, b: Nat, c: Nat, h: {Nat.is_lt(Nat.add(a, b), c) == True{} : Bool}) -> {Nat.is_lt(b, Nat.sub(c, a)) == True{} : Bool}:
  match a c:
    case 0n _:
      %Equal.sym(Nat, Nat.sub(c, 0n), c, sub_zero_r(c)) : {Nat.is_lt(b, _) == True{} : Bool}
      h
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(b, 0n) == True{} : Bool}, false_ne_true(h))
    case 1n+p 1n+q:
      lt_sub_of_add(p, b, q, h)

def replicate_get(-A: Data, n: Nat, k: Nat, +x: A, h: {Nat.is_lt(k, n) == True{} : Bool}) -> {List.get(&2, A, List.replicate(A, n, x), k) == Some{x} : Maybe<&2, A>}:
  match n k:
    case 0n 0n:
      Empty.absurd({None{} == Some{x} : Maybe<&2, A>}, false_ne_true(h))
    case 0n 1n+q:
      Empty.absurd({None{} == Some{x} : Maybe<&2, A>}, false_ne_true(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      replicate_get(A, p, q, x, h)

def some_mat_t(m: Maybe<&2, L.Mat>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{_}:
      Empty

def none_ne_some(+l: L.Mat, e: {None{} == Some{l} : Maybe<&2, L.Mat>}) -> Empty:
  %e : some_mat_t(_)
  Unit{}

def mat_or(d: L.Mat, m: Maybe<&2, L.Mat>) -> L.Mat:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def un_some_mat(+a: L.Mat, +b: L.Mat, e: {Some{a} == Some{b} : Maybe<&2, L.Mat>}) -> {a == b : L.Mat}:
  Equal.cong(Maybe<&2, L.Mat>, L.Mat, m => mat_or(a, m), Some{a}, Some{b}, e)

def lt_zero_absurd(i: Nat, h: {Nat.is_lt(i, 0n) == True{} : Bool}) -> Empty:
  match i:
    case 0n:
      false_ne_true(h)
    case 1n+p:
      false_ne_true(h)

def add_sub_of_lt(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.add(a, Nat.sub(b, a)) == b : Nat}:
  match a b:
    case 0n _:
      sub_zero_r(b)
    case 1n+p 0n:
      Empty.absurd({1n+Nat.add(p, 0n) == 0n : Nat}, false_ne_true(h))
    case 1n+p 1n+q:
      %add_sub_of_lt(p, q, h) : {1n+Nat.add(p, Nat.sub(q, p)) == 1n+_ : Nat}
      {==}

def sub_pred_of_lt(a: Nat, b: Nat, h: {Nat.is_lt(a, 1n+b) == True{} : Bool}) -> {Nat.add(a, Nat.sub(b, a)) == b : Nat}:
  match a b:
    case 0n _:
      sub_zero_r(b)
    case 1n+p 0n:
      Empty.absurd({1n+Nat.add(p, 0n) == 0n : Nat}, lt_zero_absurd(p, h))
    case 1n+p 1n+q:
      %sub_pred_of_lt(p, q, h) : {1n+Nat.add(p, Nat.sub(q, p)) == 1n+_ : Nat}
      {==}

# ---- lower_rows_loop tail & head lemmas (consume Array<F32> strictly once)

def lower_rows_loop_get_tail(+rem: Nat, r: Array<F32> & List<&2, F32>, +acc: List<&2, List<&2, F32>>, +n: Nat, +nu: U32, +d: Nat) -> {List.get(&2, List<&2, F32>, L.arr_lower_rows.fin(L.lower_rows.loop(rem, r, acc, n, nu)), 1n+Nat.add(rem, d)) == List.get(&2, List<&2, F32>, acc, d) : Maybe<&2, List<&2, F32>>}:
  match rem:
    case 0n:
      (a, +row) = r
      {==}
    case 1n+p:
      (a, +row) = r
      %add_succ_r(p, d) : {List.get(&2, List<&2, F32>, L.arr_lower_rows.fin(L.lower_rows.loop(p, L.lower_row(a, p, n, (U32.from_nat(p) * nu : U32)), row <> acc, n, nu)), 1n+_) == List.get(&2, List<&2, F32>, acc, d) : Maybe<&2, List<&2, F32>>}
      lower_rows_loop_get_tail(p, L.lower_row(a, p, n, (U32.from_nat(p) * nu : U32)), row <> acc, n, nu, 1n+d)

def lower_rows_loop_head(+rem: Nat, r: Array<F32> & List<&2, F32>, +acc: List<&2, List<&2, F32>>, +n: Nat, +nu: U32) -> {List.get(&2, List<&2, F32>, L.arr_lower_rows.fin(L.lower_rows.loop(rem, r, acc, n, nu)), rem) == Some{L.arr_to_list.fin(r)} : Maybe<&2, List<&2, F32>>}:
  match rem:
    case 0n:
      (a, +row) = r
      {==}
    case 1n+p:
      (a, +row) = r
      %add_zero_r(p) : {List.get(&2, List<&2, F32>, L.arr_lower_rows.fin(L.lower_rows.loop(p, L.lower_row(a, p, n, (U32.from_nat(p) * nu : U32)), row <> acc, n, nu)), 1n+_) == Some{row} : Maybe<&2, List<&2, F32>>}
      lower_rows_loop_get_tail(p, L.lower_row(a, p, n, (U32.from_nat(p) * nu : U32)), row <> acc, n, nu, 0n)

# ---- Cholesky shape proof (lexicographic over (outer, inner), strictly linear in Array<F32>)

def lower_shape_lex(+outer: Nat, +inner: Nat, r: Array<F32> & F32, +rd_acc: List<&2, F32>, +base: U32, +rows_acc: List<&2, List<&2, F32>>, +n: Nat, +nu: U32, +hlen: {1n+Nat.add(inner, List.length(&2, F32, rd_acc)) == n : Nat}, +ha: {L.Mat.rows.ok(rows_acc, n) == True{} : Bool}) -> {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_lower_rows.fin(L.lower_rows.loop(outer, L.read_down.loop(inner, r, rd_acc, base), rows_acc, n, nu))), 1n+Nat.add(outer, List.length(&2, List<&2, F32>, rows_acc))), L.Mat.rows.ok(L.arr_lower_rows.fin(L.lower_rows.loop(outer, L.read_down.loop(inner, r, rd_acc, base), rows_acc, n, nu)), n)) == True{} : Bool}:
  match outer inner:
    case _ 1n+q:
      (a, +v) = r
      +hlen2 = Equal.trans(Nat, 1n+Nat.add(q, 1n+List.length(&2, F32, rd_acc)), 1n+1n+Nat.add(q, List.length(&2, F32, rd_acc)), n, Equal.cong(Nat, Nat, z => 1n+z, Nat.add(q, 1n+List.length(&2, F32, rd_acc)), 1n+Nat.add(q, List.length(&2, F32, rd_acc)), add_succ_r(q, List.length(&2, F32, rd_acc))), hlen)
      lower_shape_lex(outer, q, Array.get(F32, a, (base + U32.from_nat(q) : U32)), v <> rd_acc, base, rows_acc, n, nu, hlen2, ha)
    case 0n 0n:
      (a, +v) = r
      +row = {v <> rd_acc : List<&2, F32>}
      +hrow_ok = Equal.trans(Bool, Nat.is_eq(List.length(&2, F32, row), n), Nat.is_eq(n, n), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, n), List.length(&2, F32, row), n, hlen), nat_eq_refl(n))
      +ha2 = Equal.trans(Bool, Bool.and(Nat.is_eq(List.length(&2, F32, row), n), L.Mat.rows.ok(rows_acc, n)), Bool.and(True{}, L.Mat.rows.ok(rows_acc, n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, L.Mat.rows.ok(rows_acc, n)), Nat.is_eq(List.length(&2, F32, row), n), True{}, hrow_ok), ha)
      %Equal.sym(Bool, Nat.is_eq(List.length(&2, List<&2, F32>, rows_acc), List.length(&2, List<&2, F32>, rows_acc)), True{}, nat_eq_refl(List.length(&2, List<&2, F32>, rows_acc))) : {Bool.and(_, Bool.and(Nat.is_eq(List.length(&2, F32, row), n), L.Mat.rows.ok(rows_acc, n))) == True{} : Bool}
      ha2
    case 1n+p 0n:
      (a, +v) = r
      match n:
        case 0n:
          Empty.absurd({Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_lower_rows.fin(L.lower_rows.loop(p, L.lower_row(a, p, 0n, (U32.from_nat(p) * nu : U32)), (v <> rd_acc) <> rows_acc, 0n, nu))), 1n+1n+Nat.add(p, List.length(&2, List<&2, F32>, rows_acc))), L.Mat.rows.ok(L.arr_lower_rows.fin(L.lower_rows.loop(p, L.lower_row(a, p, 0n, (U32.from_nat(p) * nu : U32)), (v <> rd_acc) <> rows_acc, 0n, nu)), 0n)) == True{} : Bool}, succ_ne_zero(List.length(&2, F32, rd_acc), hlen))
        case 1n+n1:
          +row = {v <> rd_acc : List<&2, F32>}
          +hrow_ok = Equal.trans(Bool, Nat.is_eq(List.length(&2, F32, row), 1n+n1), Nat.is_eq(1n+n1, 1n+n1), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n+n1), List.length(&2, F32, row), 1n+n1, hlen), nat_eq_refl(1n+n1))
          +ha2 = Equal.trans(Bool, Bool.and(Nat.is_eq(List.length(&2, F32, row), 1n+n1), L.Mat.rows.ok(rows_acc, 1n+n1)), Bool.and(True{}, L.Mat.rows.ok(rows_acc, 1n+n1)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, L.Mat.rows.ok(rows_acc, 1n+n1)), Nat.is_eq(List.length(&2, F32, row), 1n+n1), True{}, hrow_ok), ha)
          +t1 = Nat.min(p, n1)
          +z1 = Nat.sub(n1, t1)
          +b1 = (U32.from_nat(p) * nu : U32)
          +hlen_next = Equal.trans(Nat, 1n+Nat.add(t1, List.length(&2, F32, List.replicate(F32, z1, 0.0))), 1n+Nat.add(t1, z1), 1n+n1, Equal.cong(Nat, Nat, q => 1n+Nat.add(t1, q), List.length(&2, F32, List.replicate(F32, z1, 0.0)), z1, len_replicate(F32, z1, 0.0)), Equal.cong(Nat, Nat, q => 1n+q, Nat.add(t1, z1), n1, min_add_sub(p, n1)))
          %add_succ_r(p, List.length(&2, List<&2, F32>, rows_acc)) : {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_lower_rows.fin(L.lower_rows.loop(p, L.read_down.loop(t1, Array.get(F32, a, (b1 + U32.from_nat(t1) : U32)), List.replicate(F32, z1, 0.0), b1), row <> rows_acc, 1n+n1, nu))), 1n+_), L.Mat.rows.ok(L.arr_lower_rows.fin(L.lower_rows.loop(p, L.read_down.loop(t1, Array.get(F32, a, (b1 + U32.from_nat(t1) : U32)), List.replicate(F32, z1, 0.0), b1), row <> rows_acc, 1n+n1, nu)), 1n+n1)) == True{} : Bool}
          lower_shape_lex(p, t1, Array.get(F32, a, (b1 + U32.from_nat(t1) : U32)), List.replicate(F32, z1, 0.0), b1, row <> rows_acc, 1n+n1, nu, hlen_next, ha2)

def lower_rows_shape.go(a: Array<F32>, +nn: Nat, +n: U32) -> {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_lower_rows.fin(L.lower_rows.go(nn, a, Nil{}, nn, n))), nn), L.Mat.rows.ok(L.arr_lower_rows.fin(L.lower_rows.go(nn, a, Nil{}, nn, n)), nn)) == True{} : Bool}:
  match nn:
    case 0n:
      {==}
    case 1n+p:
      +t0 = Nat.min(p, p)
      +z0 = Nat.sub(p, t0)
      +b0 = (U32.from_nat(p) * n : U32)
      +hlen0 = Equal.trans(Nat, 1n+Nat.add(t0, List.length(&2, F32, List.replicate(F32, z0, 0.0))), 1n+Nat.add(t0, z0), 1n+p, Equal.cong(Nat, Nat, q => 1n+Nat.add(t0, q), List.length(&2, F32, List.replicate(F32, z0, 0.0)), z0, len_replicate(F32, z0, 0.0)), Equal.cong(Nat, Nat, q => 1n+q, Nat.add(t0, z0), p, min_add_sub(p, p)))
      %add_zero_r(p) : {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_lower_rows.fin(L.lower_rows.loop(p, L.read_down.loop(t0, Array.get(F32, a, (b0 + U32.from_nat(t0) : U32)), List.replicate(F32, z0, 0.0), b0), Nil{}, 1n+p, n))), 1n+_), L.Mat.rows.ok(L.arr_lower_rows.fin(L.lower_rows.loop(p, L.read_down.loop(t0, Array.get(F32, a, (b0 + U32.from_nat(t0) : U32)), List.replicate(F32, z0, 0.0), b0), Nil{}, 1n+p, n)), 1n+p)) == True{} : Bool}
      lower_shape_lex(p, t0, Array.get(F32, a, (b0 + U32.from_nat(t0) : U32)), List.replicate(F32, z0, 0.0), b0, Nil{}, 1n+p, n, hlen0, {==})

def lower_rows_shape(a: Array<F32>, +n: U32) -> {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_lower_rows(a, n)), U32.to_nat(n)), L.Mat.rows.ok(L.arr_lower_rows(a, n), U32.to_nat(n))) == True{} : Bool}:
  lower_rows_shape.go(a, U32.to_nat(n), n)

# ---- Cholesky upper-zero proof (lexicographic over (d, inner), strictly linear in Array<F32>)

def rd_head_zero(+p: Nat, +inner: Nat, r: Array<F32> & F32, +rd_acc: List<&2, F32>, +base: U32, +rows_acc: List<&2, List<&2, F32>>, +n: Nat, +nu: U32, +k: Nat) -> {L.mat_get(L.arr_lower_rows.fin(L.lower_rows.loop(p, L.read_down.loop(inner, r, rd_acc, base), rows_acc, n, nu)), p, 1n+Nat.add(inner, k)) == List.get(&2, F32, rd_acc, k) : Maybe<&2, F32>}:
  match inner:
    case 0n:
      (a, +v) = r
      %Equal.sym(Maybe<&2, List<&2, F32>>, List.get(&2, List<&2, F32>, L.arr_lower_rows.fin(L.lower_rows.loop(p, (a, v <> rd_acc), rows_acc, n, nu)), p), Some{v <> rd_acc}, lower_rows_loop_head(p, (a, v <> rd_acc), rows_acc, n, nu)) : {L.row_get(_, 1n+k) == List.get(&2, F32, rd_acc, k) : Maybe<&2, F32>}
      {==}
    case 1n+q:
      (a, +v) = r
      %add_succ_r(q, k) : {L.mat_get(L.arr_lower_rows.fin(L.lower_rows.loop(p, L.read_down.loop(q, Array.get(F32, a, (base + U32.from_nat(q) : U32)), v <> rd_acc, base), rows_acc, n, nu)), p, 1n+_) == List.get(&2, F32, rd_acc, k) : Maybe<&2, F32>}
      rd_head_zero(p, q, Array.get(F32, a, (base + U32.from_nat(q) : U32)), v <> rd_acc, base, rows_acc, n, nu, 1n+k)

def lower_uz_lex(+d: Nat, +inner: Nat, +p: Nat, r: Array<F32> & F32, +rd_acc: List<&2, F32>, +base: U32, +rows_acc: List<&2, List<&2, F32>>, +n1: Nat, +nu: U32, +i: Nat, +k: Nat, +hb: {Nat.is_lt(Nat.add(1n+i, k), 1n+n1) == True{} : Bool}, +heq: {Nat.add(i, d) == p : Nat}, hrd: {d == 0n : Nat} -> {inner == i : Nat}, hacc: {d == 0n : Nat} -> {rd_acc == List.replicate(F32, Nat.sub(n1, i), 0.0) : List<&2, F32>}) -> {L.mat_get(L.arr_lower_rows.fin(L.lower_rows.loop(p, L.read_down.loop(inner, r, rd_acc, base), rows_acc, 1n+n1, nu)), i, Nat.add(1n+i, k)) == Some{0.0} : Maybe<&2, F32>}:
  match d inner:
    case 0n _:
      +eip = Equal.trans(Nat, i, Nat.add(i, 0n), p, Equal.sym(Nat, Nat.add(i, 0n), i, add_zero_r(i)), heq)
      +eii = hrd({==})
      +eacc = hacc({==})
      %eip : {L.mat_get(L.arr_lower_rows.fin(L.lower_rows.loop(_, L.read_down.loop(inner, r, rd_acc, base), rows_acc, 1n+n1, nu)), i, Nat.add(1n+i, k)) == Some{0.0} : Maybe<&2, F32>}
      %eii : {L.mat_get(L.arr_lower_rows.fin(L.lower_rows.loop(i, L.read_down.loop(inner, r, rd_acc, base), rows_acc, 1n+n1, nu)), i, 1n+Nat.add(_, k)) == Some{0.0} : Maybe<&2, F32>}
      e1 = rd_head_zero(i, inner, r, rd_acc, base, rows_acc, 1n+n1, nu, k)
      %Equal.sym(Maybe<&2, F32>, L.mat_get(L.arr_lower_rows.fin(L.lower_rows.loop(i, L.read_down.loop(inner, r, rd_acc, base), rows_acc, 1n+n1, nu)), i, 1n+Nat.add(inner, k)), List.get(&2, F32, rd_acc, k), e1) : {_ == Some{0.0} : Maybe<&2, F32>}
      %Equal.sym(List<&2, F32>, rd_acc, List.replicate(F32, Nat.sub(n1, i), 0.0), eacc) : {List.get(&2, F32, _, k) == Some{0.0} : Maybe<&2, F32>}
      replicate_get(F32, Nat.sub(n1, i), k, 0.0, lt_sub_of_add(i, k, n1, hb))
    case 1n+dq 1n+q:
      (a, +v) = r
      lower_uz_lex(1n+dq, q, p, Array.get(F32, a, (base + U32.from_nat(q) : U32)), v <> rd_acc, base, rows_acc, n1, nu, i, k, hb, heq, e => Empty.absurd({q == i : Nat}, succ_ne_zero(dq, e)), e => Empty.absurd({v <> rd_acc == List.replicate(F32, Nat.sub(n1, i), 0.0) : List<&2, F32>}, succ_ne_zero(dq, e)))
    case 1n+dq 0n:
      match p:
        case 0n:
          (a, +v) = r
          +es = Equal.trans(Nat, 1n+Nat.add(i, dq), Nat.add(i, 1n+dq), 0n, Equal.sym(Nat, Nat.add(i, 1n+dq), 1n+Nat.add(i, dq), add_succ_r(i, dq)), heq)
          Empty.absurd({L.mat_get(L.arr_lower_rows.fin(L.lower_rows.loop(0n, (a, v <> rd_acc), rows_acc, 1n+n1, nu)), i, Nat.add(1n+i, k)) == Some{0.0} : Maybe<&2, F32>}, succ_ne_zero(Nat.add(i, dq), es))
        case 1n+p1:
          (a, +v) = r
          +heq1 = nat_pred_eq(Nat.add(i, dq), p1, Equal.trans(Nat, 1n+Nat.add(i, dq), Nat.add(i, 1n+dq), 1n+p1, Equal.sym(Nat, Nat.add(i, 1n+dq), 1n+Nat.add(i, dq), add_succ_r(i, dq)), heq))
          +t1 = Nat.min(p1, n1)
          +z1 = Nat.sub(n1, t1)
          +b1 = (U32.from_nat(p1) * nu : U32)
          +hi_lt = lt_add_left(i, k, n1, hb)
          lower_uz_lex(dq, t1, p1, Array.get(F32, a, (b1 + U32.from_nat(t1) : U32)), List.replicate(F32, z1, 0.0), b1, (v <> rd_acc) <> rows_acc, n1, nu, i, k, hb, heq1,
            e => Equal.trans(Nat, Nat.min(p1, n1), Nat.min(i, n1), i, Equal.cong(Nat, Nat, q => Nat.min(q, n1), p1, i, Equal.sym(Nat, i, p1, Equal.trans(Nat, i, Nat.add(i, 0n), p1, Equal.sym(Nat, Nat.add(i, 0n), i, add_zero_r(i)), Equal.trans(Nat, Nat.add(i, 0n), Nat.add(i, dq), p1, Equal.cong(Nat, Nat, q => Nat.add(i, q), 0n, dq, Equal.sym(Nat, dq, 0n, e)), heq1)))), lt_min_left(i, n1, hi_lt)),
            e => Equal.cong(Nat, List<&2, F32>, q => List.replicate(F32, Nat.sub(n1, q), 0.0), t1, i, Equal.trans(Nat, Nat.min(p1, n1), Nat.min(i, n1), i, Equal.cong(Nat, Nat, q => Nat.min(q, n1), p1, i, Equal.sym(Nat, i, p1, Equal.trans(Nat, i, Nat.add(i, 0n), p1, Equal.sym(Nat, Nat.add(i, 0n), i, add_zero_r(i)), Equal.trans(Nat, Nat.add(i, 0n), Nat.add(i, dq), p1, Equal.cong(Nat, Nat, q => Nat.add(i, q), 0n, dq, Equal.sym(Nat, dq, 0n, e)), heq1)))), lt_min_left(i, n1, hi_lt))))

def lower_rows_upper_zero.go(a: Array<F32>, +nn: Nat, +n: U32, +i: Nat, +k: Nat, +hb: {Nat.is_lt(Nat.add(1n+i, k), nn) == True{} : Bool}) -> {L.mat_get(L.arr_lower_rows.fin(L.lower_rows.go(nn, a, Nil{}, nn, n)), i, Nat.add(1n+i, k)) == Some{0.0} : Maybe<&2, F32>}:
  match nn:
    case 0n:
      Empty.absurd({None{} == Some{0.0} : Maybe<&2, F32>}, false_ne_true(hb))
    case 1n+n1:
      +hi_lt = lt_add_left(i, k, n1, hb)
      +d0 = Nat.sub(n1, i)
      +heq0 = add_sub_of_lt(i, n1, hi_lt)
      +t0 = Nat.min(n1, n1)
      +z0 = Nat.sub(n1, t0)
      +b0 = (U32.from_nat(n1) * n : U32)
      lower_uz_lex(d0, t0, n1, Array.get(F32, a, (b0 + U32.from_nat(t0) : U32)), List.replicate(F32, z0, 0.0), b0, Nil{}, n1, n, i, k, hb, heq0,
        e => Equal.trans(Nat, Nat.min(n1, n1), Nat.min(i, n1), i, Equal.cong(Nat, Nat, q => Nat.min(q, n1), n1, i, Equal.sym(Nat, i, n1, Equal.trans(Nat, i, Nat.add(i, 0n), n1, Equal.sym(Nat, Nat.add(i, 0n), i, add_zero_r(i)), Equal.trans(Nat, Nat.add(i, 0n), Nat.add(i, d0), n1, Equal.cong(Nat, Nat, q => Nat.add(i, q), 0n, d0, Equal.sym(Nat, d0, 0n, e)), heq0)))), lt_min_left(i, n1, hi_lt)),
        e => Equal.cong(Nat, List<&2, F32>, q => List.replicate(F32, Nat.sub(n1, q), 0.0), t0, i, Equal.trans(Nat, Nat.min(n1, n1), Nat.min(i, n1), i, Equal.cong(Nat, Nat, q => Nat.min(q, n1), n1, i, Equal.sym(Nat, i, n1, Equal.trans(Nat, i, Nat.add(i, 0n), n1, Equal.sym(Nat, Nat.add(i, 0n), i, add_zero_r(i)), Equal.trans(Nat, Nat.add(i, 0n), Nat.add(i, d0), n1, Equal.cong(Nat, Nat, q => Nat.add(i, q), 0n, d0, Equal.sym(Nat, d0, 0n, e)), heq0)))), lt_min_left(i, n1, hi_lt))))

def lower_rows_upper_zero(a: Array<F32>, +n: U32, +i: Nat, +k: Nat, +hb: {Nat.is_lt(Nat.add(1n+i, k), U32.to_nat(n)) == True{} : Bool}) -> {L.mat_get(L.arr_lower_rows(a, n), i, Nat.add(1n+i, k)) == Some{0.0} : Maybe<&2, F32>}:
  lower_rows_upper_zero.go(a, U32.to_nat(n), n, i, k, hb)

def Laws.cholesky_nonsquare(m, n, rows, e):
  %Equal.sym(Bool, U32.is_eq(m, n), False{}, e) : {L.chol.chk(_, n, rows) == None{} : Maybe<&2, L.Mat>}
  {==}

def chol_fin_shape(st: L.CSt, +n: U32, +l: L.Mat, hc: {L.chol.fin(st, n) == Some{l} : Maybe<&2, L.Mat>}) -> {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(l)), U32.to_nat(n)), L.Mat.rows.ok(Laws.mat_rows(l), U32.to_nat(n))) == True{} : Bool}:
  match st:
    case L.CSt{a0, l0, False{}}:
      Empty.absurd({Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(l)), U32.to_nat(n)), L.Mat.rows.ok(Laws.mat_rows(l), U32.to_nat(n))) == True{} : Bool}, none_ne_some(l, hc))
    case L.CSt{a0, arr, True{}}:
      %hc : {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(mat_or(l, _))), U32.to_nat(n)), L.Mat.rows.ok(Laws.mat_rows(mat_or(l, _)), U32.to_nat(n))) == True{} : Bool}
      lower_rows_shape(arr, n)

def chol_chk_shape(ok: Bool, +n: U32, +rows: List<&2, List<&2, F32>>, +l: L.Mat, hc: {L.chol.chk(ok, n, rows) == Some{l} : Maybe<&2, L.Mat>}) -> {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(l)), U32.to_nat(n)), L.Mat.rows.ok(Laws.mat_rows(l), U32.to_nat(n))) == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(l)), U32.to_nat(n)), L.Mat.rows.ok(Laws.mat_rows(l), U32.to_nat(n))) == True{} : Bool}, none_ne_some(l, hc))
    case True{}:
      chol_fin_shape(L.chol.run(n, rows), n, l, hc)

def Laws.cholesky_shape(a, l, hc):
  match a:
    case L.Mat{+m, +n, +rows}:
      chol_chk_shape(U32.is_eq(m, n), n, rows, l, hc)

def chol_fin_uz(st: L.CSt, +n: U32, +l: L.Mat, +i: Nat, +k: Nat, hc: {L.chol.fin(st, n) == Some{l} : Maybe<&2, L.Mat>}, +hb: {Nat.is_lt(Nat.add(1n+i, k), U32.to_nat(n)) == True{} : Bool}) -> {L.Mat.get(l, i, Nat.add(1n+i, k)) == Some{0.0} : Maybe<&2, F32>}:
  match st:
    case L.CSt{a0, l0, False{}}:
      Empty.absurd({L.Mat.get(l, i, Nat.add(1n+i, k)) == Some{0.0} : Maybe<&2, F32>}, none_ne_some(l, hc))
    case L.CSt{a0, arr, True{}}:
      %hc : {L.Mat.get(mat_or(l, _), i, Nat.add(1n+i, k)) == Some{0.0} : Maybe<&2, F32>}
      lower_rows_upper_zero(arr, n, i, k, hb)

def chol_chk_uz(ok: Bool, +n: U32, +rows: List<&2, List<&2, F32>>, +l: L.Mat, +i: Nat, +k: Nat, hc: {L.chol.chk(ok, n, rows) == Some{l} : Maybe<&2, L.Mat>}, +hb: {Nat.is_lt(Nat.add(1n+i, k), U32.to_nat(n)) == True{} : Bool}) -> {L.Mat.get(l, i, Nat.add(1n+i, k)) == Some{0.0} : Maybe<&2, F32>}:
  match ok:
    case False{}:
      Empty.absurd({L.Mat.get(l, i, Nat.add(1n+i, k)) == Some{0.0} : Maybe<&2, F32>}, none_ne_some(l, hc))
    case True{}:
      chol_fin_uz(L.chol.run(n, rows), n, l, i, k, hc, hb)

def Laws.cholesky_upper_zero(a, l, i, k, hc, hb):
  match a:
    case L.Mat{+m, +n, +rows}:
      chol_chk_uz(U32.is_eq(m, n), n, rows, l, i, k, hc, hb)

def Laws.solve_lower_mismatch(lm, ln, nb, lrows, bs, e):
  %Equal.sym(Bool, Bool.and(U32.is_eq(lm, ln), U32.is_eq(ln, nb)), False{}, e) : {L.solve_lower.chk(_, ln, lrows, bs) == None{} : Maybe<&2, L.Vec>}
  {==}

def Laws.solve_upper_mismatch(um, un, nb, urows, bs, e):
  %Equal.sym(Bool, Bool.and(U32.is_eq(um, un), U32.is_eq(un, nb)), False{}, e) : {L.solve_upper.chk(_, un, urows, bs) == None{} : Maybe<&2, L.Vec>}
  {==}

def Laws.woodbury_solve_mismatch(nd, nu, ku, mm, mn, nb, ds, urows, mrows, bs, e):
  %Equal.sym(Bool, Bool.and(U32.is_eq(nd, nu), Bool.and(U32.is_eq(nu, nb), Bool.and(U32.is_eq(mm, ku), U32.is_eq(mn, ku)))), False{}, e) : {L.woodbury_solve.chk(_, nu, ku, ds, L.Mat{nu, ku, urows}, L.Mat{mm, mn, mrows}, L.Vec{nb, bs}) == None{} : Maybe<&2, L.Vec>}
  {==}

# ---------------------------------------------------------------- QR & least squares

def some_qr_t(m: Maybe<&2, L.QR>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{_}:
      Empty

def none_ne_some_qr(+qr: L.QR, e: {None{} == Some{qr} : Maybe<&2, L.QR>}) -> Empty:
  %e : some_qr_t(_)
  Unit{}

def qr_or(d: L.QR, m: Maybe<&2, L.QR>) -> L.QR:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def lt_succ_self(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt_succ_self(p)

def lt_of_succ_lt(a: Nat, b: Nat, h: {Nat.is_lt(1n+a, b) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_lt(a, 0n) == True{} : Bool}, false_ne_true(h))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      lt_of_succ_lt(p, q, h)

def sub_succ_lt(a: Nat, b: Nat, h: {Nat.is_lt(a, 1n+b) == True{} : Bool}) -> {Nat.sub(1n+b, a) == 1n+Nat.sub(b, a) : Nat}:
  match a b:
    case 0n _:
      %Equal.sym(Nat, Nat.sub(b, 0n), b, sub_zero_r(b)) : {1n+b == 1n+_ : Nat}
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.sub(0n, p) == 1n+0n : Nat}, lt_zero_absurd(p, h))
    case 1n+p 1n+q:
      sub_succ_lt(p, q, h)

def len_prepend_zeros(k: Nat, +xs: List<&2, F32>) -> {List.length(&2, F32, L.prepend_zeros(k, xs)) == Nat.add(k, List.length(&2, F32, xs)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, List.length(&2, F32, L.prepend_zeros(p, xs)), Nat.add(p, List.length(&2, F32, xs)), len_prepend_zeros(p, xs)) : {1n+_ == 1n+Nat.add(p, List.length(&2, F32, xs)) : Nat}
      {==}

def prepend_zeros_get(j: Nat, +k: Nat, +xs: List<&2, F32>) -> {List.get(&2, F32, L.prepend_zeros(Nat.add(1n+j, k), xs), j) == Some{0.0} : Maybe<&2, F32>}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      prepend_zeros_get(p, k, xs)

# ---- QR Q shape proof (arr_colmajor_rows)

def cm_shape_z(+rem: Nat, a: Array<F32>, +rows_acc: List<&2, List<&2, F32>>, +m: U32, +ha: {L.Mat.rows.ok(rows_acc, 0n) == True{} : Bool}) -> {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_lower_rows.fin(L.cm_rows.loop(rem, (a, Nil{}), rows_acc, 0n, m))), 1n+Nat.add(rem, List.length(&2, List<&2, F32>, rows_acc))), L.Mat.rows.ok(L.arr_lower_rows.fin(L.cm_rows.loop(rem, (a, Nil{}), rows_acc, 0n, m)), 0n)) == True{} : Bool}:
  match rem:
    case 0n:
      %Equal.sym(Bool, Nat.is_eq(List.length(&2, List<&2, F32>, rows_acc), List.length(&2, List<&2, F32>, rows_acc)), True{}, nat_eq_refl(List.length(&2, List<&2, F32>, rows_acc))) : {Bool.and(_, L.Mat.rows.ok(rows_acc, 0n)) == True{} : Bool}
      ha
    case 1n+p:
      %add_succ_r(p, List.length(&2, List<&2, F32>, rows_acc)) : {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_lower_rows.fin(L.cm_rows.loop(p, (a, Nil{}), Nil{} <> rows_acc, 0n, m))), 1n+_), L.Mat.rows.ok(L.arr_lower_rows.fin(L.cm_rows.loop(p, (a, Nil{}), Nil{} <> rows_acc, 0n, m)), 0n)) == True{} : Bool}
      cm_shape_z(p, a, Nil{} <> rows_acc, m, ha)

def cm_shape_lex(+outer: Nat, +inner: Nat, r: Array<F32> & F32, +rd_acc: List<&2, F32>, +base: U32, +rows_acc: List<&2, List<&2, F32>>, +n1: Nat, +m: U32, +hlen: {1n+Nat.add(inner, List.length(&2, F32, rd_acc)) == 1n+n1 : Nat}, +ha: {L.Mat.rows.ok(rows_acc, 1n+n1) == True{} : Bool}) -> {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_lower_rows.fin(L.cm_rows.loop(outer, L.read_down_s.loop(inner, r, rd_acc, base, m), rows_acc, 1n+n1, m))), 1n+Nat.add(outer, List.length(&2, List<&2, F32>, rows_acc))), L.Mat.rows.ok(L.arr_lower_rows.fin(L.cm_rows.loop(outer, L.read_down_s.loop(inner, r, rd_acc, base, m), rows_acc, 1n+n1, m)), 1n+n1)) == True{} : Bool}:
  match outer inner:
    case _ 1n+q:
      (a, +v) = r
      +hlen2 = Equal.trans(Nat, 1n+Nat.add(q, 1n+List.length(&2, F32, rd_acc)), 1n+1n+Nat.add(q, List.length(&2, F32, rd_acc)), 1n+n1, Equal.cong(Nat, Nat, z => 1n+z, Nat.add(q, 1n+List.length(&2, F32, rd_acc)), 1n+Nat.add(q, List.length(&2, F32, rd_acc)), add_succ_r(q, List.length(&2, F32, rd_acc))), hlen)
      cm_shape_lex(outer, q, Array.get(F32, a, (base + (U32.from_nat(q) * m) : U32)), v <> rd_acc, base, rows_acc, n1, m, hlen2, ha)
    case 0n 0n:
      (a, +v) = r
      +row = {v <> rd_acc : List<&2, F32>}
      +hrow_ok = Equal.trans(Bool, Nat.is_eq(List.length(&2, F32, row), 1n+n1), Nat.is_eq(1n+n1, 1n+n1), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n+n1), List.length(&2, F32, row), 1n+n1, hlen), nat_eq_refl(1n+n1))
      +ha2 = Equal.trans(Bool, Bool.and(Nat.is_eq(List.length(&2, F32, row), 1n+n1), L.Mat.rows.ok(rows_acc, 1n+n1)), Bool.and(True{}, L.Mat.rows.ok(rows_acc, 1n+n1)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, L.Mat.rows.ok(rows_acc, 1n+n1)), Nat.is_eq(List.length(&2, F32, row), 1n+n1), True{}, hrow_ok), ha)
      %Equal.sym(Bool, Nat.is_eq(List.length(&2, List<&2, F32>, rows_acc), List.length(&2, List<&2, F32>, rows_acc)), True{}, nat_eq_refl(List.length(&2, List<&2, F32>, rows_acc))) : {Bool.and(_, Bool.and(Nat.is_eq(List.length(&2, F32, row), 1n+n1), L.Mat.rows.ok(rows_acc, 1n+n1))) == True{} : Bool}
      ha2
    case 1n+p 0n:
      (a, +v) = r
      +row = {v <> rd_acc : List<&2, F32>}
      +hrow_ok = Equal.trans(Bool, Nat.is_eq(List.length(&2, F32, row), 1n+n1), Nat.is_eq(1n+n1, 1n+n1), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n+n1), List.length(&2, F32, row), 1n+n1, hlen), nat_eq_refl(1n+n1))
      +ha2 = Equal.trans(Bool, Bool.and(Nat.is_eq(List.length(&2, F32, row), 1n+n1), L.Mat.rows.ok(rows_acc, 1n+n1)), Bool.and(True{}, L.Mat.rows.ok(rows_acc, 1n+n1)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, L.Mat.rows.ok(rows_acc, 1n+n1)), Nat.is_eq(List.length(&2, F32, row), 1n+n1), True{}, hrow_ok), ha)
      +b1 = U32.from_nat(p)
      +hlen_next = Equal.cong(Nat, Nat, q => 1n+q, Nat.add(n1, 0n), n1, add_zero_r(n1))
      %add_succ_r(p, List.length(&2, List<&2, F32>, rows_acc)) : {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_lower_rows.fin(L.cm_rows.loop(p, L.read_down_s.loop(n1, Array.get(F32, a, (b1 + (U32.from_nat(n1) * m) : U32)), Nil{}, b1, m), row <> rows_acc, 1n+n1, m))), 1n+_), L.Mat.rows.ok(L.arr_lower_rows.fin(L.cm_rows.loop(p, L.read_down_s.loop(n1, Array.get(F32, a, (b1 + (U32.from_nat(n1) * m) : U32)), Nil{}, b1, m), row <> rows_acc, 1n+n1, m)), 1n+n1)) == True{} : Bool}
      cm_shape_lex(p, n1, Array.get(F32, a, (b1 + (U32.from_nat(n1) * m) : U32)), Nil{}, b1, row <> rows_acc, n1, m, hlen_next, ha2)

def cm_rows_shape.go(a: Array<F32>, +mm: Nat, +nn: Nat, +m: U32) -> {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_lower_rows.fin(L.cm_rows.go(mm, a, Nil{}, nn, m))), mm), L.Mat.rows.ok(L.arr_lower_rows.fin(L.cm_rows.go(mm, a, Nil{}, nn, m)), nn)) == True{} : Bool}:
  match mm nn:
    case 0n _:
      {==}
    case 1n+p 0n:
      %add_zero_r(p) : {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_lower_rows.fin(L.cm_rows.loop(p, (a, Nil{}), Nil{}, 0n, m))), 1n+_), L.Mat.rows.ok(L.arr_lower_rows.fin(L.cm_rows.loop(p, (a, Nil{}), Nil{}, 0n, m)), 0n)) == True{} : Bool}
      cm_shape_z(p, a, Nil{}, m, {==})
    case 1n+p 1n+n1:
      +b0 = U32.from_nat(p)
      +hlen0 = Equal.cong(Nat, Nat, q => 1n+q, Nat.add(n1, 0n), n1, add_zero_r(n1))
      %add_zero_r(p) : {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_lower_rows.fin(L.cm_rows.loop(p, L.read_down_s.loop(n1, Array.get(F32, a, (b0 + (U32.from_nat(n1) * m) : U32)), Nil{}, b0, m), Nil{}, 1n+n1, m))), 1n+_), L.Mat.rows.ok(L.arr_lower_rows.fin(L.cm_rows.loop(p, L.read_down_s.loop(n1, Array.get(F32, a, (b0 + (U32.from_nat(n1) * m) : U32)), Nil{}, b0, m), Nil{}, 1n+n1, m)), 1n+n1)) == True{} : Bool}
      cm_shape_lex(p, n1, Array.get(F32, a, (b0 + (U32.from_nat(n1) * m) : U32)), Nil{}, b0, Nil{}, n1, m, hlen0, {==})

def cm_rows_shape(a: Array<F32>, +m: U32, +n: U32) -> {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_colmajor_rows(a, m, n)), U32.to_nat(m)), L.Mat.rows.ok(L.arr_colmajor_rows(a, m, n), U32.to_nat(n))) == True{} : Bool}:
  cm_rows_shape.go(a, U32.to_nat(m), U32.to_nat(n), m)

# ---- QR R shape proof (arr_upper_rows)

def upper_shape_lex(+outer: Nat, +inner: Nat, r: Array<F32> & F32, +rd_acc: List<&2, F32>, +base: U32, +rows_acc: List<&2, List<&2, F32>>, +n1: Nat, +m: U32, +hlt: {Nat.is_lt(outer, 1n+n1) == True{} : Bool}, +hlen: {Nat.add(outer, 1n+Nat.add(inner, List.length(&2, F32, rd_acc))) == 1n+n1 : Nat}, +ha: {L.Mat.rows.ok(rows_acc, 1n+n1) == True{} : Bool}) -> {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_lower_rows.fin(L.upper_rows.loop(outer, L.read_down_s.loop(inner, r, rd_acc, base, m), rows_acc, 1n+n1, m))), 1n+Nat.add(outer, List.length(&2, List<&2, F32>, rows_acc))), L.Mat.rows.ok(L.arr_lower_rows.fin(L.upper_rows.loop(outer, L.read_down_s.loop(inner, r, rd_acc, base, m), rows_acc, 1n+n1, m)), 1n+n1)) == True{} : Bool}:
  match outer inner:
    case _ 1n+q:
      (a, +v) = r
      +hlen2 = Equal.trans(Nat, Nat.add(outer, 1n+Nat.add(q, 1n+List.length(&2, F32, rd_acc))), Nat.add(outer, 1n+1n+Nat.add(q, List.length(&2, F32, rd_acc))), 1n+n1, Equal.cong(Nat, Nat, z => Nat.add(outer, 1n+z), Nat.add(q, 1n+List.length(&2, F32, rd_acc)), 1n+Nat.add(q, List.length(&2, F32, rd_acc)), add_succ_r(q, List.length(&2, F32, rd_acc))), hlen)
      upper_shape_lex(outer, q, Array.get(F32, a, (base + (U32.from_nat(q) * m) : U32)), v <> rd_acc, base, rows_acc, n1, m, hlt, hlen2, ha)
    case 0n 0n:
      (a, +v) = r
      +row = {v <> rd_acc : List<&2, F32>}
      +hrow_ok = Equal.trans(Bool, Nat.is_eq(List.length(&2, F32, row), 1n+n1), Nat.is_eq(1n+n1, 1n+n1), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n+n1), List.length(&2, F32, row), 1n+n1, hlen), nat_eq_refl(1n+n1))
      +ha2 = Equal.trans(Bool, Bool.and(Nat.is_eq(List.length(&2, F32, row), 1n+n1), L.Mat.rows.ok(rows_acc, 1n+n1)), Bool.and(True{}, L.Mat.rows.ok(rows_acc, 1n+n1)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, L.Mat.rows.ok(rows_acc, 1n+n1)), Nat.is_eq(List.length(&2, F32, row), 1n+n1), True{}, hrow_ok), ha)
      %Equal.sym(Bool, Nat.is_eq(List.length(&2, List<&2, F32>, rows_acc), List.length(&2, List<&2, F32>, rows_acc)), True{}, nat_eq_refl(List.length(&2, List<&2, F32>, rows_acc))) : {Bool.and(_, Bool.and(Nat.is_eq(List.length(&2, F32, row), 1n+n1), L.Mat.rows.ok(rows_acc, 1n+n1))) == True{} : Bool}
      ha2
    case 1n+p 0n:
      (a, +v) = r
      +hi = {v <> rd_acc : List<&2, F32>}
      +row = L.prepend_zeros(1n+p, hi)
      +hrow_len = Equal.trans(Nat, List.length(&2, F32, row), Nat.add(1n+p, List.length(&2, F32, hi)), 1n+n1, len_prepend_zeros(1n+p, hi), hlen)
      +hrow_ok = Equal.trans(Bool, Nat.is_eq(List.length(&2, F32, row), 1n+n1), Nat.is_eq(1n+n1, 1n+n1), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n+n1), List.length(&2, F32, row), 1n+n1, hrow_len), nat_eq_refl(1n+n1))
      +ha2 = Equal.trans(Bool, Bool.and(Nat.is_eq(List.length(&2, F32, row), 1n+n1), L.Mat.rows.ok(rows_acc, 1n+n1)), Bool.and(True{}, L.Mat.rows.ok(rows_acc, 1n+n1)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, L.Mat.rows.ok(rows_acc, 1n+n1)), Nat.is_eq(List.length(&2, F32, row), 1n+n1), True{}, hrow_ok), ha)
      +hlt_p = lt_of_succ_lt(p, 1n+n1, hlt)
      +esub = sub_succ_lt(p, n1, hlt_p)
      +s1 = Nat.sub(n1, p)
      +pu = U32.from_nat(p)
      +b1 = ((pu * m) + pu : U32)
      +hlen_next = Equal.trans(Nat, Nat.add(p, 1n+Nat.add(s1, 0n)), Nat.add(p, 1n+s1), 1n+n1, Equal.cong(Nat, Nat, q => Nat.add(p, 1n+q), Nat.add(s1, 0n), s1, add_zero_r(s1)), Equal.trans(Nat, Nat.add(p, 1n+s1), 1n+Nat.add(p, s1), 1n+n1, add_succ_r(p, s1), Equal.cong(Nat, Nat, q => 1n+q, Nat.add(p, s1), n1, sub_pred_of_lt(p, n1, hlt_p))))
      %Equal.sym(Nat, Nat.sub(1n+n1, p), 1n+s1, esub) : {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_lower_rows.fin(L.upper_rows.loop(p, L.read_down_s(_, a, Nil{}, b1, m), row <> rows_acc, 1n+n1, m))), 1n+1n+Nat.add(p, List.length(&2, List<&2, F32>, rows_acc))), L.Mat.rows.ok(L.arr_lower_rows.fin(L.upper_rows.loop(p, L.read_down_s(_, a, Nil{}, b1, m), row <> rows_acc, 1n+n1, m)), 1n+n1)) == True{} : Bool}
      %add_succ_r(p, List.length(&2, List<&2, F32>, rows_acc)) : {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_lower_rows.fin(L.upper_rows.loop(p, L.read_down_s.loop(s1, Array.get(F32, a, (b1 + (U32.from_nat(s1) * m) : U32)), Nil{}, b1, m), row <> rows_acc, 1n+n1, m))), 1n+_), L.Mat.rows.ok(L.arr_lower_rows.fin(L.upper_rows.loop(p, L.read_down_s.loop(s1, Array.get(F32, a, (b1 + (U32.from_nat(s1) * m) : U32)), Nil{}, b1, m), row <> rows_acc, 1n+n1, m)), 1n+n1)) == True{} : Bool}
      upper_shape_lex(p, s1, Array.get(F32, a, (b1 + (U32.from_nat(s1) * m) : U32)), Nil{}, b1, row <> rows_acc, n1, m, hlt_p, hlen_next, ha2)

def upper_rows_shape.go(a: Array<F32>, +nn: Nat, +m: U32) -> {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_lower_rows.fin(L.upper_rows.go(nn, a, Nil{}, nn, m))), nn), L.Mat.rows.ok(L.arr_lower_rows.fin(L.upper_rows.go(nn, a, Nil{}, nn, m)), nn)) == True{} : Bool}:
  match nn:
    case 0n:
      {==}
    case 1n+n1:
      +hlt0 = lt_succ_self(n1)
      +esub0 = sub_succ_lt(n1, n1, hlt0)
      +s0 = Nat.sub(n1, n1)
      +nu = U32.from_nat(n1)
      +b0 = ((nu * m) + nu : U32)
      +hlen0 = Equal.trans(Nat, Nat.add(n1, 1n+Nat.add(s0, 0n)), Nat.add(n1, 1n+s0), 1n+n1, Equal.cong(Nat, Nat, q => Nat.add(n1, 1n+q), Nat.add(s0, 0n), s0, add_zero_r(s0)), Equal.trans(Nat, Nat.add(n1, 1n+s0), 1n+Nat.add(n1, s0), 1n+n1, add_succ_r(n1, s0), Equal.cong(Nat, Nat, q => 1n+q, Nat.add(n1, s0), n1, sub_pred_of_lt(n1, n1, hlt0))))
      %Equal.sym(Nat, Nat.sub(1n+n1, n1), 1n+s0, esub0) : {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_lower_rows.fin(L.upper_rows.loop(n1, L.read_down_s(_, a, Nil{}, b0, m), Nil{}, 1n+n1, m))), 1n+n1), L.Mat.rows.ok(L.arr_lower_rows.fin(L.upper_rows.loop(n1, L.read_down_s(_, a, Nil{}, b0, m), Nil{}, 1n+n1, m)), 1n+n1)) == True{} : Bool}
      %add_zero_r(n1) : {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_lower_rows.fin(L.upper_rows.loop(n1, L.read_down_s.loop(s0, Array.get(F32, a, (b0 + (U32.from_nat(s0) * m) : U32)), Nil{}, b0, m), Nil{}, 1n+n1, m))), 1n+_), L.Mat.rows.ok(L.arr_lower_rows.fin(L.upper_rows.loop(n1, L.read_down_s.loop(s0, Array.get(F32, a, (b0 + (U32.from_nat(s0) * m) : U32)), Nil{}, b0, m), Nil{}, 1n+n1, m)), 1n+n1)) == True{} : Bool}
      upper_shape_lex(n1, s0, Array.get(F32, a, (b0 + (U32.from_nat(s0) * m) : U32)), Nil{}, b0, Nil{}, n1, m, hlt0, hlen0, {==})

def upper_rows_shape(a: Array<F32>, +m: U32, +n: U32) -> {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.arr_upper_rows(a, m, n)), U32.to_nat(n)), L.Mat.rows.ok(L.arr_upper_rows(a, m, n), U32.to_nat(n))) == True{} : Bool}:
  upper_rows_shape.go(a, U32.to_nat(n), m)

# ---- QR R lower-zero proof (exact 0.0 strictly below diagonal)

def upper_rows_loop_get_tail(+rem: Nat, r: Array<F32> & List<&2, F32>, +acc: List<&2, List<&2, F32>>, +n: Nat, +m: U32, +d: Nat) -> {List.get(&2, List<&2, F32>, L.arr_lower_rows.fin(L.upper_rows.loop(rem, r, acc, n, m)), 1n+Nat.add(rem, d)) == List.get(&2, List<&2, F32>, acc, d) : Maybe<&2, List<&2, F32>>}:
  match rem:
    case 0n:
      (a, +hi) = r
      {==}
    case 1n+p:
      (a, +hi) = r
      +pu = U32.from_nat(p)
      %add_succ_r(p, d) : {List.get(&2, List<&2, F32>, L.arr_lower_rows.fin(L.upper_rows.loop(p, L.read_down_s(Nat.sub(n, p), a, Nil{}, ((pu * m) + pu : U32), m), L.prepend_zeros(1n+p, hi) <> acc, n, m)), 1n+_) == List.get(&2, List<&2, F32>, acc, d) : Maybe<&2, List<&2, F32>>}
      upper_rows_loop_get_tail(p, L.read_down_s(Nat.sub(n, p), a, Nil{}, ((pu * m) + pu : U32), m), L.prepend_zeros(1n+p, hi) <> acc, n, m, 1n+d)

def upper_lz_go(+d: Nat, +rem: Nat, r: Array<F32> & List<&2, F32>, +acc: List<&2, List<&2, F32>>, +n: Nat, +m: U32, +j: Nat, +k: Nat, +heq: {Nat.add(Nat.add(1n+j, k), d) == rem : Nat}) -> {L.mat_get(L.arr_lower_rows.fin(L.upper_rows.loop(rem, r, acc, n, m)), Nat.add(1n+j, k), j) == Some{0.0} : Maybe<&2, F32>}:
  match d:
    case 0n:
      (a, +hi) = r
      +i = Nat.add(j, k)
      +erem = Equal.trans(Nat, 1n+i, Nat.add(1n+i, 0n), rem, Equal.sym(Nat, Nat.add(1n+i, 0n), 1n+i, add_zero_r(1n+i)), heq)
      %erem : {L.mat_get(L.arr_lower_rows.fin(L.upper_rows.loop(_, (a, hi), acc, n, m)), 1n+i, j) == Some{0.0} : Maybe<&2, F32>}
      +iu = U32.from_nat(i)
      %add_zero_r(i) : {L.mat_get(L.arr_lower_rows.fin(L.upper_rows.loop(i, L.read_down_s(Nat.sub(n, i), a, Nil{}, ((iu * m) + iu : U32), m), L.prepend_zeros(1n+i, hi) <> acc, n, m)), 1n+_, j) == Some{0.0} : Maybe<&2, F32>}
      e1 = upper_rows_loop_get_tail(i, L.read_down_s(Nat.sub(n, i), a, Nil{}, ((iu * m) + iu : U32), m), L.prepend_zeros(1n+i, hi) <> acc, n, m, 0n)
      %Equal.sym(Maybe<&2, List<&2, F32>>, List.get(&2, List<&2, F32>, L.arr_lower_rows.fin(L.upper_rows.loop(i, L.read_down_s(Nat.sub(n, i), a, Nil{}, ((iu * m) + iu : U32), m), L.prepend_zeros(1n+i, hi) <> acc, n, m)), 1n+Nat.add(i, 0n)), Some{L.prepend_zeros(1n+i, hi)}, e1) : {L.row_get(_, j) == Some{0.0} : Maybe<&2, F32>}
      prepend_zeros_get(j, k, hi)
    case 1n+dq:
      match rem:
        case 0n:
          (a, +hi) = r
          Empty.absurd({L.mat_get(L.arr_lower_rows.fin(L.upper_rows.loop(0n, (a, hi), acc, n, m)), Nat.add(1n+j, k), j) == Some{0.0} : Maybe<&2, F32>}, succ_ne_zero(Nat.add(Nat.add(j, k), 1n+dq), heq))
        case 1n+p:
          (a, +hi) = r
          +pu = U32.from_nat(p)
          +heq1 = nat_pred_eq(Nat.add(Nat.add(1n+j, k), dq), p, Equal.trans(Nat, 1n+Nat.add(Nat.add(1n+j, k), dq), Nat.add(Nat.add(1n+j, k), 1n+dq), 1n+p, Equal.sym(Nat, Nat.add(Nat.add(1n+j, k), 1n+dq), 1n+Nat.add(Nat.add(1n+j, k), dq), add_succ_r(Nat.add(1n+j, k), dq)), heq))
          upper_lz_go(dq, p, L.read_down_s(Nat.sub(n, p), a, Nil{}, ((pu * m) + pu : U32), m), L.prepend_zeros(1n+p, hi) <> acc, n, m, j, k, heq1)

def upper_rows_lower_zero.go(a: Array<F32>, +nn: Nat, +m: U32, +j: Nat, +k: Nat, +hb: {Nat.is_lt(Nat.add(1n+j, k), nn) == True{} : Bool}) -> {L.mat_get(L.arr_lower_rows.fin(L.upper_rows.go(nn, a, Nil{}, nn, m)), Nat.add(1n+j, k), j) == Some{0.0} : Maybe<&2, F32>}:
  match nn:
    case 0n:
      Empty.absurd({None{} == Some{0.0} : Maybe<&2, F32>}, false_ne_true(hb))
    case 1n+n1:
      +i = Nat.add(1n+j, k)
      +d0 = Nat.sub(n1, i)
      +heq0 = sub_pred_of_lt(i, n1, hb)
      +nu = U32.from_nat(n1)
      upper_lz_go(d0, n1, L.read_down_s(Nat.sub(1n+n1, n1), a, Nil{}, ((nu * m) + nu : U32), m), Nil{}, 1n+n1, m, j, k, heq0)

def upper_rows_lower_zero(a: Array<F32>, +m: U32, +n: U32, +j: Nat, +k: Nat, +hb: {Nat.is_lt(Nat.add(1n+j, k), U32.to_nat(n)) == True{} : Bool}) -> {L.mat_get(L.arr_upper_rows(a, m, n), Nat.add(1n+j, k), j) == Some{0.0} : Maybe<&2, F32>}:
  upper_rows_lower_zero.go(a, U32.to_nat(n), m, j, k, hb)

# ---- QR & least-squares laws

def Laws.qr_thin_wide(m, n, rows, e):
  %Equal.sym(Bool, U32.is_ge(m, n), False{}, e) : {L.qr_thin.chk(_, m, n, rows) == None{} : Maybe<&2, L.QR>}
  {==}

def qr_pair_q_shape(p: L.ArrPair, +m: U32, +n: U32, +qr: L.QR, hq: {Some{L.qr_thin.from_pair(p, m, n)} == Some{qr} : Maybe<&2, L.QR>}) -> {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(Laws.qr_q(qr))), U32.to_nat(m)), L.Mat.rows.ok(Laws.mat_rows(Laws.qr_q(qr)), U32.to_nat(n))) == True{} : Bool}:
  match p:
    case L.ArrPair{a1, q_arr}:
      %hq : {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(Laws.qr_q(qr_or(qr, _)))), U32.to_nat(m)), L.Mat.rows.ok(Laws.mat_rows(Laws.qr_q(qr_or(qr, _))), U32.to_nat(n))) == True{} : Bool}
      cm_rows_shape(q_arr, m, n)

def qr_fin_q_shape(pk: L.QRPack, +m: U32, +n: U32, +qr: L.QR, hq: {Some{L.qr_thin.fin(pk, m, n)} == Some{qr} : Maybe<&2, L.QR>}) -> {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(Laws.qr_q(qr))), U32.to_nat(m)), L.Mat.rows.ok(Laws.mat_rows(Laws.qr_q(qr)), U32.to_nat(n))) == True{} : Bool}:
  match pk:
    case L.QRPack{a, tau}:
      qr_pair_q_shape(L.qr_build_q(a, tau, m, n, n), m, n, qr, hq)

def qr_chk_q_shape(ok: Bool, +m: U32, +n: U32, +rows: List<&2, List<&2, F32>>, +qr: L.QR, hq: {L.qr_thin.chk(ok, m, n, rows) == Some{qr} : Maybe<&2, L.QR>}) -> {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(Laws.qr_q(qr))), U32.to_nat(m)), L.Mat.rows.ok(Laws.mat_rows(Laws.qr_q(qr)), U32.to_nat(n))) == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(Laws.qr_q(qr))), U32.to_nat(m)), L.Mat.rows.ok(Laws.mat_rows(Laws.qr_q(qr)), U32.to_nat(n))) == True{} : Bool}, none_ne_some_qr(qr, hq))
    case True{}:
      qr_fin_q_shape(L.qr_factor_arr(rows, m, n), m, n, qr, hq)

def Laws.qr_q_shape(a, qr, hq):
  match a:
    case L.Mat{+m, +n, +rows}:
      qr_chk_q_shape(U32.is_ge(m, n), m, n, rows, qr, hq)

def qr_pair_r_shape(p: L.ArrPair, +m: U32, +n: U32, +qr: L.QR, hq: {Some{L.qr_thin.from_pair(p, m, n)} == Some{qr} : Maybe<&2, L.QR>}) -> {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(Laws.qr_r(qr))), U32.to_nat(n)), L.Mat.rows.ok(Laws.mat_rows(Laws.qr_r(qr)), U32.to_nat(n))) == True{} : Bool}:
  match p:
    case L.ArrPair{a1, q_arr}:
      %hq : {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(Laws.qr_r(qr_or(qr, _)))), U32.to_nat(n)), L.Mat.rows.ok(Laws.mat_rows(Laws.qr_r(qr_or(qr, _))), U32.to_nat(n))) == True{} : Bool}
      upper_rows_shape(a1, m, n)

def qr_fin_r_shape(pk: L.QRPack, +m: U32, +n: U32, +qr: L.QR, hq: {Some{L.qr_thin.fin(pk, m, n)} == Some{qr} : Maybe<&2, L.QR>}) -> {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(Laws.qr_r(qr))), U32.to_nat(n)), L.Mat.rows.ok(Laws.mat_rows(Laws.qr_r(qr)), U32.to_nat(n))) == True{} : Bool}:
  match pk:
    case L.QRPack{a, tau}:
      qr_pair_r_shape(L.qr_build_q(a, tau, m, n, n), m, n, qr, hq)

def qr_chk_r_shape(ok: Bool, +m: U32, +n: U32, +rows: List<&2, List<&2, F32>>, +qr: L.QR, hq: {L.qr_thin.chk(ok, m, n, rows) == Some{qr} : Maybe<&2, L.QR>}) -> {Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(Laws.qr_r(qr))), U32.to_nat(n)), L.Mat.rows.ok(Laws.mat_rows(Laws.qr_r(qr)), U32.to_nat(n))) == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(Laws.qr_r(qr))), U32.to_nat(n)), L.Mat.rows.ok(Laws.mat_rows(Laws.qr_r(qr)), U32.to_nat(n))) == True{} : Bool}, none_ne_some_qr(qr, hq))
    case True{}:
      qr_fin_r_shape(L.qr_factor_arr(rows, m, n), m, n, qr, hq)

def Laws.qr_r_shape(a, qr, hq):
  match a:
    case L.Mat{+m, +n, +rows}:
      qr_chk_r_shape(U32.is_ge(m, n), m, n, rows, qr, hq)

def qr_pair_r_lz(p: L.ArrPair, +m: U32, +n: U32, +qr: L.QR, +j: Nat, +k: Nat, hq: {Some{L.qr_thin.from_pair(p, m, n)} == Some{qr} : Maybe<&2, L.QR>}, +hb: {Nat.is_lt(Nat.add(1n+j, k), U32.to_nat(n)) == True{} : Bool}) -> {L.Mat.get(Laws.qr_r(qr), Nat.add(1n+j, k), j) == Some{0.0} : Maybe<&2, F32>}:
  match p:
    case L.ArrPair{a1, q_arr}:
      %hq : {L.Mat.get(Laws.qr_r(qr_or(qr, _)), Nat.add(1n+j, k), j) == Some{0.0} : Maybe<&2, F32>}
      upper_rows_lower_zero(a1, m, n, j, k, hb)

def qr_fin_r_lz(pk: L.QRPack, +m: U32, +n: U32, +qr: L.QR, +j: Nat, +k: Nat, hq: {Some{L.qr_thin.fin(pk, m, n)} == Some{qr} : Maybe<&2, L.QR>}, +hb: {Nat.is_lt(Nat.add(1n+j, k), U32.to_nat(n)) == True{} : Bool}) -> {L.Mat.get(Laws.qr_r(qr), Nat.add(1n+j, k), j) == Some{0.0} : Maybe<&2, F32>}:
  match pk:
    case L.QRPack{a, tau}:
      qr_pair_r_lz(L.qr_build_q(a, tau, m, n, n), m, n, qr, j, k, hq, hb)

def qr_chk_r_lz(ok: Bool, +m: U32, +n: U32, +rows: List<&2, List<&2, F32>>, +qr: L.QR, +j: Nat, +k: Nat, hq: {L.qr_thin.chk(ok, m, n, rows) == Some{qr} : Maybe<&2, L.QR>}, +hb: {Nat.is_lt(Nat.add(1n+j, k), U32.to_nat(n)) == True{} : Bool}) -> {L.Mat.get(Laws.qr_r(qr), Nat.add(1n+j, k), j) == Some{0.0} : Maybe<&2, F32>}:
  match ok:
    case False{}:
      Empty.absurd({L.Mat.get(Laws.qr_r(qr), Nat.add(1n+j, k), j) == Some{0.0} : Maybe<&2, F32>}, none_ne_some_qr(qr, hq))
    case True{}:
      qr_fin_r_lz(L.qr_factor_arr(rows, m, n), m, n, qr, j, k, hq, hb)

def Laws.qr_r_lower_zero(a, qr, j, k, hq, hb):
  match a:
    case L.Mat{+m, +n, +rows}:
      qr_chk_r_lz(U32.is_ge(m, n), m, n, rows, qr, j, k, hq, hb)

def Laws.lstsq_mismatch(m, n, nb, rows, bs, e):
  %Equal.sym(Bool, Bool.and(U32.is_ge(m, n), U32.is_eq(m, nb)), False{}, e) : {L.lstsq.chk(_, m, n, rows, bs) == None{} : Maybe<&2, L.Vec>}
  {==}

def Laws.wlstsq_mismatch(m, n, nw, nb, rows, ws, bs, e):
  %Equal.sym(Bool, Bool.and(U32.is_ge(m, n), Bool.and(U32.is_eq(m, nw), U32.is_eq(m, nb))), False{}, e) : {L.wlstsq.chk(_, m, ws, L.Mat{m, n, rows}, L.Vec{nb, bs}) == None{} : Maybe<&2, L.Vec>}
  {==}

def Laws.lstsq_mat_mismatch(ma, na, mb, nb, arows, brows, e):
  %Equal.sym(Bool, Bool.and(U32.is_ge(ma, na), U32.is_eq(ma, mb)), False{}, e) : {L.lstsq_mat.chk(_, ma, na, nb, arows, brows) == None{} : Maybe<&2, L.Mat>}
  {==}

def Laws.project_orth_mismatch(mq, nq, nx, qrows, xs, e):
  %Equal.sym(Bool, U32.is_eq(mq, nx), False{}, e) : {L.project_orth.chk(_, L.Mat{mq, nq, qrows}, L.Vec{nx, xs}) == None{} : Maybe<&2, L.Vec>}
  {==}

def Laws.lstsq_constrained_mismatch(ma, na, nb, cm, cp, nd, arows, bs, crows, ds, e):
  %Equal.sym(Bool, Bool.and(U32.is_eq(ma, nb), Bool.and(U32.is_eq(cm, na), Bool.and(U32.is_eq(cp, nd), Bool.and(U32.is_ge(na, cp), U32.is_ge(ma, (na - cp : U32)))))), False{}, e) : {L.lstsq_c.chk(_, L.Mat{ma, na, arows}, L.Vec{nb, bs}, crows, L.Vec{nd, ds}, na, cp) == None{} : Maybe<&2, L.Vec>}
  {==}

# ---------------------------------------------------------------- Symmetric Eigen, SPD power, SVD & Procrustes

def some_eig_t(m: Maybe<&2, L.Eigen>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{_}:
      Empty

def none_ne_some_eig(+eig: L.Eigen, e: {None{} == Some{eig} : Maybe<&2, L.Eigen>}) -> Empty:
  %e : some_eig_t(_)
  Unit{}

def eig_or(d: L.Eigen, m: Maybe<&2, L.Eigen>) -> L.Eigen:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def and_left(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def and_right(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_ne_true(h))

def eig_ok(ec: List<&2, L.EigCol>, +nn: Nat) -> Bool:
  match ec:
    case Nil{}:
      True{}
    case Con{L.EigCol{_, c}, t}:
      Bool.and(Nat.is_eq(List.length(&2, F32, c), nn), eig_ok(t, nn))

def eig_ins_pick_len(ge: Bool, +x: L.EigCol, +y: L.EigCol, +t: List<&2, L.EigCol>, +rec: List<&2, L.EigCol>, hrec: {List.length(&2, L.EigCol, rec) == 1n+List.length(&2, L.EigCol, t) : Nat}) -> {List.length(&2, L.EigCol, L.eig_ins.pick(ge, x, y, t, rec)) == 1n+1n+List.length(&2, L.EigCol, t) : Nat}:
  match ge:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Nat, List.length(&2, L.EigCol, rec), 1n+List.length(&2, L.EigCol, t), hrec) : {1n+_ == 1n+1n+List.length(&2, L.EigCol, t) : Nat}
      {==}

def eig_ins_len(+x: L.EigCol, xs: List<&2, L.EigCol>) -> {List.length(&2, L.EigCol, L.eig_ins(x, xs)) == 1n+List.length(&2, L.EigCol, xs) : Nat}:
  match x xs:
    case L.EigCol{+vx, +cx} Nil{}:
      {==}
    case L.EigCol{+vx, +cx} Con{L.EigCol{+vy, +cy}, +t}:
      eig_ins_pick_len(F32.is_ge(vx, vy), L.EigCol{vx, cx}, L.EigCol{vy, cy}, t, L.eig_ins(L.EigCol{vx, cx}, t), eig_ins_len(L.EigCol{vx, cx}, t))

def eig_sort_len(xs: List<&2, L.EigCol>) -> {List.length(&2, L.EigCol, L.eig_sort(xs)) == List.length(&2, L.EigCol, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Nat, List.length(&2, L.EigCol, L.eig_ins(h, L.eig_sort(t))), 1n+List.length(&2, L.EigCol, L.eig_sort(t)), 1n+List.length(&2, L.EigCol, t), eig_ins_len(h, L.eig_sort(t)), Equal.cong(Nat, Nat, q => 1n+q, List.length(&2, L.EigCol, L.eig_sort(t)), List.length(&2, L.EigCol, t), eig_sort_len(t)))

def eig_ins_pick_ok(ge: Bool, +vx: F32, +cx: List<&2, F32>, +vy: F32, +cy: List<&2, F32>, +t: List<&2, L.EigCol>, +rec: List<&2, L.EigCol>, +nn: Nat, hx: {Nat.is_eq(List.length(&2, F32, cx), nn) == True{} : Bool}, hy: {Nat.is_eq(List.length(&2, F32, cy), nn) == True{} : Bool}, ht: {eig_ok(t, nn) == True{} : Bool}, hrec: {eig_ok(rec, nn) == True{} : Bool}) -> {eig_ok(L.eig_ins.pick(ge, L.EigCol{vx, cx}, L.EigCol{vy, cy}, t, rec), nn) == True{} : Bool}:
  match ge:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(List.length(&2, F32, cx), nn), True{}, hx) : {Bool.and(_, Bool.and(Nat.is_eq(List.length(&2, F32, cy), nn), eig_ok(t, nn))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(List.length(&2, F32, cy), nn), True{}, hy) : {Bool.and(_, eig_ok(t, nn)) == True{} : Bool}
      ht
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(List.length(&2, F32, cy), nn), True{}, hy) : {Bool.and(_, eig_ok(rec, nn)) == True{} : Bool}
      hrec

def eig_ins_ok(+x: L.EigCol, xs: List<&2, L.EigCol>, +nn: Nat, +hx: {eig_ok(x <> Nil{}, nn) == True{} : Bool}, +hxs: {eig_ok(xs, nn) == True{} : Bool}) -> {eig_ok(L.eig_ins(x, xs), nn) == True{} : Bool}:
  match x xs:
    case L.EigCol{+vx, +cx} Nil{}:
      hx
    case L.EigCol{+vx, +cx} Con{L.EigCol{+vy, +cy}, +t}:
      +hx1 = and_left(Nat.is_eq(List.length(&2, F32, cx), nn), True{}, hx)
      +hy1 = and_left(Nat.is_eq(List.length(&2, F32, cy), nn), eig_ok(t, nn), hxs)
      +ht1 = and_right(Nat.is_eq(List.length(&2, F32, cy), nn), eig_ok(t, nn), hxs)
      eig_ins_pick_ok(F32.is_ge(vx, vy), vx, cx, vy, cy, t, L.eig_ins(L.EigCol{vx, cx}, t), nn, hx1, hy1, ht1, eig_ins_ok(L.EigCol{vx, cx}, t, nn, hx, ht1))

def eig_sort_ok(xs: List<&2, L.EigCol>, +nn: Nat, +h: {eig_ok(xs, nn) == True{} : Bool}) -> {eig_ok(L.eig_sort(xs), nn) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{L.EigCol{+v, +c}, +t}:
      +hc = and_left(Nat.is_eq(List.length(&2, F32, c), nn), eig_ok(t, nn), h)
      +ht = and_right(Nat.is_eq(List.length(&2, F32, c), nn), eig_ok(t, nn), h)
      +hx = Equal.trans(Bool, Bool.and(Nat.is_eq(List.length(&2, F32, c), nn), True{}), Bool.and(True{}, True{}), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, True{}), Nat.is_eq(List.length(&2, F32, c), nn), True{}, hc), {==})
      eig_ins_ok(L.EigCol{v, c}, L.eig_sort(t), nn, hx, eig_sort_ok(t, nn, ht))

def eig_vals_len(xs: List<&2, L.EigCol>) -> {List.length(&2, F32, L.eig_vals(xs)) == List.length(&2, L.EigCol, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{L.EigCol{_, _}, +t}:
      %Equal.sym(Nat, List.length(&2, F32, L.eig_vals(t)), List.length(&2, L.EigCol, t), eig_vals_len(t)) : {1n+_ == 1n+List.length(&2, L.EigCol, t) : Nat}
      {==}

def eig_cols_len(xs: List<&2, L.EigCol>) -> {List.length(&2, List<&2, F32>, L.eig_cols(xs)) == List.length(&2, L.EigCol, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{L.EigCol{_, _}, +t}:
      %Equal.sym(Nat, List.length(&2, List<&2, F32>, L.eig_cols(t)), List.length(&2, L.EigCol, t), eig_cols_len(t)) : {1n+_ == 1n+List.length(&2, L.EigCol, t) : Nat}
      {==}

def eig_cols_ok(xs: List<&2, L.EigCol>, +nn: Nat, +h: {eig_ok(xs, nn) == True{} : Bool}) -> {L.Mat.rows.ok(L.eig_cols(xs), nn) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{L.EigCol{_, +c}, +t}:
      +hc = and_left(Nat.is_eq(List.length(&2, F32, c), nn), eig_ok(t, nn), h)
      +ht = and_right(Nat.is_eq(List.length(&2, F32, c), nn), eig_ok(t, nn), h)
      %Equal.sym(Bool, Nat.is_eq(List.length(&2, F32, c), nn), True{}, hc) : {Bool.and(_, L.Mat.rows.ok(L.eig_cols(t), nn)) == True{} : Bool}
      eig_cols_ok(t, nn, ht)

def jac_build_shape_nn(+ec: List<&2, L.EigCol>, +nn: Nat, +h: {Bool.and(Nat.is_eq(List.length(&2, L.EigCol, ec), nn), eig_ok(ec, nn)) == True{} : Bool}) -> {Bool.and(Nat.is_eq(List.length(&2, F32, L.eig_vals(L.eig_sort(ec))), nn), Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.transpose.rows(L.eig_cols(L.eig_sort(ec)), nn)), nn), L.Mat.rows.ok(L.transpose.rows(L.eig_cols(L.eig_sort(ec)), nn), nn))) == True{} : Bool}:
  +hlen_b = and_left(Nat.is_eq(List.length(&2, L.EigCol, ec), nn), eig_ok(ec, nn), h)
  +hok = and_right(Nat.is_eq(List.length(&2, L.EigCol, ec), nn), eig_ok(ec, nn), h)
  +hlen = nat_eq_sound(List.length(&2, L.EigCol, ec), nn, hlen_b)
  +sorted = L.eig_sort(ec)
  +hsort_len = Equal.trans(Nat, List.length(&2, L.EigCol, sorted), List.length(&2, L.EigCol, ec), nn, eig_sort_len(ec), hlen)
  +hsort_ok = eig_sort_ok(ec, nn, hok)
  +hvals_len = Equal.trans(Nat, List.length(&2, F32, L.eig_vals(sorted)), List.length(&2, L.EigCol, sorted), nn, eig_vals_len(sorted), hsort_len)
  +hvals_b = Equal.trans(Bool, Nat.is_eq(List.length(&2, F32, L.eig_vals(sorted)), nn), Nat.is_eq(nn, nn), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, nn), List.length(&2, F32, L.eig_vals(sorted)), nn, hvals_len), nat_eq_refl(nn))
  +hcols_ok = eig_cols_ok(sorted, nn, hsort_ok)
  +hcols_len = Equal.trans(Nat, List.length(&2, List<&2, F32>, L.eig_cols(sorted)), List.length(&2, L.EigCol, sorted), nn, eig_cols_len(sorted), hsort_len)
  +ht_len = Laws.transpose_len(L.eig_cols(sorted), nn, hcols_ok)
  +ht_len_b = Equal.trans(Bool, Nat.is_eq(List.length(&2, List<&2, F32>, L.transpose.rows(L.eig_cols(sorted), nn)), nn), Nat.is_eq(nn, nn), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, nn), List.length(&2, List<&2, F32>, L.transpose.rows(L.eig_cols(sorted), nn)), nn, ht_len), nat_eq_refl(nn))
  +ht_ok = Equal.trans(Bool, L.Mat.rows.ok(L.transpose.rows(L.eig_cols(sorted), nn), nn), L.Mat.rows.ok(L.transpose.rows(L.eig_cols(sorted), nn), List.length(&2, List<&2, F32>, L.eig_cols(sorted))), True{}, Equal.cong(Nat, Bool, z => L.Mat.rows.ok(L.transpose.rows(L.eig_cols(sorted), nn), z), nn, List.length(&2, List<&2, F32>, L.eig_cols(sorted)), Equal.sym(Nat, List.length(&2, List<&2, F32>, L.eig_cols(sorted)), nn, hcols_len)), Laws.transpose_row_len(L.eig_cols(sorted), nn, hcols_ok))
  %Equal.sym(Bool, Nat.is_eq(List.length(&2, F32, L.eig_vals(sorted)), nn), True{}, hvals_b) : {Bool.and(_, Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.transpose.rows(L.eig_cols(sorted), nn)), nn), L.Mat.rows.ok(L.transpose.rows(L.eig_cols(sorted), nn), nn))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(List.length(&2, List<&2, F32>, L.transpose.rows(L.eig_cols(sorted), nn)), nn), True{}, ht_len_b) : {Bool.and(_, L.Mat.rows.ok(L.transpose.rows(L.eig_cols(sorted), nn), nn)) == True{} : Bool}
  ht_ok

# ---- jac_extract shape proof (lexicographic over (outer, inner), strictly linear in Array<F32>)

def jac_ext_lex(+outer: Nat, +inner: Nat, ra: Array<F32> & F32, rv: Array<F32> & F32, +rd_acc: List<&2, F32>, +base: U32, +ec_acc: List<&2, L.EigCol>, +n1: Nat, +n: U32, +hcnt: {1n+Nat.add(outer, List.length(&2, L.EigCol, ec_acc)) == 1n+n1 : Nat}, +hlen: {1n+Nat.add(inner, List.length(&2, F32, rd_acc)) == 1n+n1 : Nat}, +ha: {eig_ok(ec_acc, 1n+n1) == True{} : Bool}) -> {Bool.and(Nat.is_eq(List.length(&2, F32, L.eig_vals(L.eig_sort(L.jac_extract.loop(outer, ra, L.read_down_s.loop(inner, rv, rd_acc, base, n), ec_acc, 1n+n1, n)))), 1n+n1), Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.transpose.rows(L.eig_cols(L.eig_sort(L.jac_extract.loop(outer, ra, L.read_down_s.loop(inner, rv, rd_acc, base, n), ec_acc, 1n+n1, n))), 1n+n1)), 1n+n1), L.Mat.rows.ok(L.transpose.rows(L.eig_cols(L.eig_sort(L.jac_extract.loop(outer, ra, L.read_down_s.loop(inner, rv, rd_acc, base, n), ec_acc, 1n+n1, n))), 1n+n1), 1n+n1))) == True{} : Bool}:
  match outer inner:
    case _ 1n+q:
      (v, +val) = rv
      +hlen2 = Equal.trans(Nat, 1n+Nat.add(q, 1n+List.length(&2, F32, rd_acc)), 1n+1n+Nat.add(q, List.length(&2, F32, rd_acc)), 1n+n1, Equal.cong(Nat, Nat, z => 1n+z, Nat.add(q, 1n+List.length(&2, F32, rd_acc)), 1n+Nat.add(q, List.length(&2, F32, rd_acc)), add_succ_r(q, List.length(&2, F32, rd_acc))), hlen)
      jac_ext_lex(outer, q, ra, Array.get(F32, v, (base + (U32.from_nat(q) * n) : U32)), val <> rd_acc, base, ec_acc, n1, n, hcnt, hlen2, ha)
    case 0n 0n:
      (a, +lam) = ra
      (v, +val) = rv
      +col = {val <> rd_acc : List<&2, F32>}
      +res = {L.EigCol{lam, col} <> ec_acc : List<&2, L.EigCol>}
      +hcol_ok = Equal.trans(Bool, Nat.is_eq(List.length(&2, F32, col), 1n+n1), Nat.is_eq(1n+n1, 1n+n1), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n+n1), List.length(&2, F32, col), 1n+n1, hlen), nat_eq_refl(1n+n1))
      +ha2 = Equal.trans(Bool, Bool.and(Nat.is_eq(List.length(&2, F32, col), 1n+n1), eig_ok(ec_acc, 1n+n1)), Bool.and(True{}, eig_ok(ec_acc, 1n+n1)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, eig_ok(ec_acc, 1n+n1)), Nat.is_eq(List.length(&2, F32, col), 1n+n1), True{}, hcol_ok), ha)
      +hres_len = Equal.trans(Bool, Nat.is_eq(List.length(&2, L.EigCol, res), 1n+n1), Nat.is_eq(1n+n1, 1n+n1), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n+n1), List.length(&2, L.EigCol, res), 1n+n1, hcnt), nat_eq_refl(1n+n1))
      +hres = Equal.trans(Bool, Bool.and(Nat.is_eq(List.length(&2, L.EigCol, res), 1n+n1), eig_ok(res, 1n+n1)), Bool.and(True{}, eig_ok(res, 1n+n1)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, eig_ok(res, 1n+n1)), Nat.is_eq(List.length(&2, L.EigCol, res), 1n+n1), True{}, hres_len), ha2)
      jac_build_shape_nn(res, 1n+n1, hres)
    case 1n+p 0n:
      (a, +lam) = ra
      (v, +val) = rv
      +col = {val <> rd_acc : List<&2, F32>}
      +hcol_ok = Equal.trans(Bool, Nat.is_eq(List.length(&2, F32, col), 1n+n1), Nat.is_eq(1n+n1, 1n+n1), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n+n1), List.length(&2, F32, col), 1n+n1, hlen), nat_eq_refl(1n+n1))
      +ha2 = Equal.trans(Bool, Bool.and(Nat.is_eq(List.length(&2, F32, col), 1n+n1), eig_ok(ec_acc, 1n+n1)), Bool.and(True{}, eig_ok(ec_acc, 1n+n1)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, eig_ok(ec_acc, 1n+n1)), Nat.is_eq(List.length(&2, F32, col), 1n+n1), True{}, hcol_ok), ha)
      +hcnt2 = Equal.trans(Nat, 1n+Nat.add(p, 1n+List.length(&2, L.EigCol, ec_acc)), 1n+1n+Nat.add(p, List.length(&2, L.EigCol, ec_acc)), 1n+n1, Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+List.length(&2, L.EigCol, ec_acc)), 1n+Nat.add(p, List.length(&2, L.EigCol, ec_acc)), add_succ_r(p, List.length(&2, L.EigCol, ec_acc))), hcnt)
      +pu = U32.from_nat(p)
      +hlen_next = Equal.cong(Nat, Nat, q => 1n+q, Nat.add(n1, 0n), n1, add_zero_r(n1))
      jac_ext_lex(p, n1, Array.get(F32, a, ((pu * n) + pu : U32)), Array.get(F32, v, (pu + (U32.from_nat(n1) * n) : U32)), Nil{}, pu, L.EigCol{lam, col} <> ec_acc, n1, n, hcnt2, hlen_next, ha2)

def jac_extract_shape.go(a: Array<F32>, v: Array<F32>, +nn: Nat, +n: U32) -> {Bool.and(Nat.is_eq(List.length(&2, F32, L.eig_vals(L.eig_sort(L.jac_extract.go(nn, a, v, Nil{}, nn, n)))), nn), Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, L.transpose.rows(L.eig_cols(L.eig_sort(L.jac_extract.go(nn, a, v, Nil{}, nn, n))), nn)), nn), L.Mat.rows.ok(L.transpose.rows(L.eig_cols(L.eig_sort(L.jac_extract.go(nn, a, v, Nil{}, nn, n))), nn), nn))) == True{} : Bool}:
  match nn:
    case 0n:
      {==}
    case 1n+n1:
      +nu = U32.from_nat(n1)
      +h0 = Equal.cong(Nat, Nat, q => 1n+q, Nat.add(n1, 0n), n1, add_zero_r(n1))
      jac_ext_lex(n1, n1, Array.get(F32, a, ((nu * n) + nu : U32)), Array.get(F32, v, (nu + (U32.from_nat(n1) * n) : U32)), Nil{}, nu, Nil{}, n1, n, h0, h0, {==})

def jac_fin_shape(st: L.JSt, +n: U32, +eig: L.Eigen, he: {Some{L.jac.fin(st, n)} == Some{eig} : Maybe<&2, L.Eigen>}) -> {Bool.and(Nat.is_eq(List.length(&2, F32, Laws.eig_values(eig)), U32.to_nat(n)), Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(Laws.eig_vectors(eig))), U32.to_nat(n)), L.Mat.rows.ok(Laws.mat_rows(Laws.eig_vectors(eig)), U32.to_nat(n)))) == True{} : Bool}:
  match st:
    case L.JSt{arr_a, arr_v, _}:
      %he : {Bool.and(Nat.is_eq(List.length(&2, F32, Laws.eig_values(eig_or(eig, _))), U32.to_nat(n)), Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(Laws.eig_vectors(eig_or(eig, _)))), U32.to_nat(n)), L.Mat.rows.ok(Laws.mat_rows(Laws.eig_vectors(eig_or(eig, _))), U32.to_nat(n)))) == True{} : Bool}
      jac_extract_shape.go(arr_a, arr_v, U32.to_nat(n), n)

def sym_eigen_chk_shape(ok: Bool, +n: U32, +rows: List<&2, List<&2, F32>>, +eig: L.Eigen, he: {L.sym_eigen.chk(ok, n, rows) == Some{eig} : Maybe<&2, L.Eigen>}) -> {Bool.and(Nat.is_eq(List.length(&2, F32, Laws.eig_values(eig)), U32.to_nat(n)), Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(Laws.eig_vectors(eig))), U32.to_nat(n)), L.Mat.rows.ok(Laws.mat_rows(Laws.eig_vectors(eig)), U32.to_nat(n)))) == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({Bool.and(Nat.is_eq(List.length(&2, F32, Laws.eig_values(eig)), U32.to_nat(n)), Bool.and(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(Laws.eig_vectors(eig))), U32.to_nat(n)), L.Mat.rows.ok(Laws.mat_rows(Laws.eig_vectors(eig)), U32.to_nat(n)))) == True{} : Bool}, none_ne_some_eig(eig, he))
    case True{}:
      jac_fin_shape(L.jac.run_n(U32.is_le(n, 1), n, rows), n, eig, he)

def Laws.sym_eigen_nonsquare(m, n, rows, e):
  %Equal.sym(Bool, U32.is_eq(m, n), False{}, e) : {L.sym_eigen.chk(_, n, rows) == None{} : Maybe<&2, L.Eigen>}
  {==}

def Laws.sym_eigen_shape(a, eig, he):
  match a:
    case L.Mat{+m, +n, +rows}:
      sym_eigen_chk_shape(U32.is_eq(m, n), n, rows, eig, he)

def Laws.spd_pow_nonsquare(m, n, rows, p, e):
  %Equal.sym(Bool, U32.is_eq(m, n), False{}, e) : {L.spd_pow.chk(L.sym_eigen.chk(_, n, rows), p) == None{} : Maybe<&2, L.Mat>}
  {==}

def sub_self(n: Nat) -> {Nat.sub(n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      sub_self(p)

def sub_of_succ_lt(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.sub(b, a) == 1n+Nat.sub(b, 1n+a) : Nat}:
  match a b:
    case 0n 0n:
      Empty.absurd({0n == 1n : Nat}, false_ne_true(h))
    case 0n 1n+q:
      %Equal.sym(Nat, Nat.sub(q, 0n), q, sub_zero_r(q)) : {1n+q == 1n+_ : Nat}
      {==}
    case 1n+p 0n:
      Empty.absurd({0n == 1n : Nat}, false_ne_true(h))
    case 1n+p 1n+q:
      sub_of_succ_lt(p, q, h)

def upper_tri_sym_lex(+outer: Nat, +inner: Nat, r: Array<F32> & F32, +rd_acc: List<&2, F32>, +base: U32, +rows_acc: List<&2, List<&2, F32>>, +n1: Nat, +nu: U32, +i: Nat, +j: Nat, +hlt: {Nat.is_lt(outer, 1n+n1) == True{} : Bool}, +hlen: {1n+Nat.add(inner, List.length(&2, F32, rd_acc)) == Nat.sub(1n+n1, outer) : Nat}, +ha: {Laws.upper_ok(rows_acc, Nat.sub(n1, outer)) == True{} : Bool}) -> {L.mat_get(L.mirror_upper(L.arr_lower_rows.fin(L.upper_tri.loop(outer, L.read_down.loop(inner, r, rd_acc, base), rows_acc, 1n+n1, nu))), i, j) == L.mat_get(L.mirror_upper(L.arr_lower_rows.fin(L.upper_tri.loop(outer, L.read_down.loop(inner, r, rd_acc, base), rows_acc, 1n+n1, nu))), j, i) : Maybe<&2, F32>}:
  match outer inner:
    case _ 1n+q:
      (a, +v) = r
      +hlen2 = Equal.trans(Nat, 1n+Nat.add(q, 1n+List.length(&2, F32, rd_acc)), 1n+1n+Nat.add(q, List.length(&2, F32, rd_acc)), Nat.sub(1n+n1, outer), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(q, 1n+List.length(&2, F32, rd_acc)), 1n+Nat.add(q, List.length(&2, F32, rd_acc)), add_succ_r(q, List.length(&2, F32, rd_acc))), hlen)
      upper_tri_sym_lex(outer, q, Array.get(F32, a, (base + U32.from_nat(q) : U32)), v <> rd_acc, base, rows_acc, n1, nu, i, j, hlt, hlen2, ha)
    case 0n 0n:
      (a, +v) = r
      +row = {v <> rd_acc : List<&2, F32>}
      +hrow_ok = Equal.trans(Bool, Nat.is_eq(List.length(&2, F32, row), 1n+n1), Nat.is_eq(1n+n1, 1n+n1), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n+n1), List.length(&2, F32, row), 1n+n1, hlen), nat_eq_refl(1n+n1))
      +ha0 = Equal.trans(Bool, Laws.upper_ok(rows_acc, n1), Laws.upper_ok(rows_acc, Nat.sub(n1, 0n)), True{}, Equal.cong(Nat, Bool, z => Laws.upper_ok(rows_acc, z), n1, Nat.sub(n1, 0n), Equal.sym(Nat, Nat.sub(n1, 0n), n1, sub_zero_r(n1))), ha)
      +hres = Equal.trans(Bool, Bool.and(Nat.is_eq(List.length(&2, F32, row), 1n+n1), Laws.upper_ok(rows_acc, n1)), Bool.and(True{}, Laws.upper_ok(rows_acc, n1)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Laws.upper_ok(rows_acc, n1)), Nat.is_eq(List.length(&2, F32, row), 1n+n1), True{}, hrow_ok), ha0)
      Laws.mirror_upper_sym(row <> rows_acc, 1n+n1, i, j, hres)
    case 1n+p 0n:
      (a, +v) = r
      +row = {v <> rd_acc : List<&2, F32>}
      +esub_cur = sub_of_succ_lt(p, n1, hlt)
      +s_cur = Nat.sub(n1, 1n+p)
      +hlen_cur = Equal.trans(Nat, List.length(&2, F32, row), Nat.sub(n1, p), 1n+s_cur, hlen, esub_cur)
      +hrow_ok = Equal.trans(Bool, Nat.is_eq(List.length(&2, F32, row), 1n+s_cur), Nat.is_eq(1n+s_cur, 1n+s_cur), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n+s_cur), List.length(&2, F32, row), 1n+s_cur, hlen_cur), nat_eq_refl(1n+s_cur))
      +ha2_s = Equal.trans(Bool, Bool.and(Nat.is_eq(List.length(&2, F32, row), 1n+s_cur), Laws.upper_ok(rows_acc, s_cur)), Bool.and(True{}, Laws.upper_ok(rows_acc, s_cur)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Laws.upper_ok(rows_acc, s_cur)), Nat.is_eq(List.length(&2, F32, row), 1n+s_cur), True{}, hrow_ok), ha)
      +ha2 = Equal.trans(Bool, Laws.upper_ok(row <> rows_acc, Nat.sub(n1, p)), Laws.upper_ok(row <> rows_acc, 1n+s_cur), True{}, Equal.cong(Nat, Bool, z => Laws.upper_ok(row <> rows_acc, z), Nat.sub(n1, p), 1n+s_cur, esub_cur), ha2_s)
      +hlt_p = lt_of_succ_lt(p, 1n+n1, hlt)
      +esub_next = sub_succ_lt(p, n1, hlt_p)
      +s1 = Nat.sub(n1, p)
      +pu = U32.from_nat(p)
      +b1 = ((pu * nu) + pu : U32)
      +hlen_next = Equal.trans(Nat, 1n+Nat.add(s1, 0n), 1n+s1, Nat.sub(1n+n1, p), Equal.cong(Nat, Nat, q => 1n+q, Nat.add(s1, 0n), s1, add_zero_r(s1)), Equal.sym(Nat, Nat.sub(1n+n1, p), 1n+s1, esub_next))
      %Equal.sym(Nat, Nat.sub(1n+n1, p), 1n+s1, esub_next) : {L.mat_get(L.mirror_upper(L.arr_lower_rows.fin(L.upper_tri.loop(p, L.read_down(_, a, Nil{}, b1), row <> rows_acc, 1n+n1, nu))), i, j) == L.mat_get(L.mirror_upper(L.arr_lower_rows.fin(L.upper_tri.loop(p, L.read_down(_, a, Nil{}, b1), row <> rows_acc, 1n+n1, nu))), j, i) : Maybe<&2, F32>}
      upper_tri_sym_lex(p, s1, Array.get(F32, a, (b1 + U32.from_nat(s1) : U32)), Nil{}, b1, row <> rows_acc, n1, nu, i, j, hlt_p, hlen_next, ha2)

def arr_upper_tri_sym.go(a: Array<F32>, +nn: Nat, +n: U32, +i: Nat, +j: Nat) -> {L.mat_get(L.mirror_upper(L.arr_lower_rows.fin(L.upper_tri.go(nn, a, Nil{}, nn, n))), i, j) == L.mat_get(L.mirror_upper(L.arr_lower_rows.fin(L.upper_tri.go(nn, a, Nil{}, nn, n))), j, i) : Maybe<&2, F32>}:
  match nn:
    case 0n:
      {==}
    case 1n+n1:
      +hlt0 = lt_succ_self(n1)
      +esub0 = sub_succ_lt(n1, n1, hlt0)
      +s0 = Nat.sub(n1, n1)
      +nu = U32.from_nat(n1)
      +b0 = ((nu * n) + nu : U32)
      +hlen0 = Equal.trans(Nat, 1n+Nat.add(s0, 0n), 1n+s0, Nat.sub(1n+n1, n1), Equal.cong(Nat, Nat, q => 1n+q, Nat.add(s0, 0n), s0, add_zero_r(s0)), Equal.sym(Nat, Nat.sub(1n+n1, n1), 1n+s0, esub0))
      +ha0 = Equal.cong(Nat, Bool, z => Laws.upper_ok(Nil{}, z), s0, 0n, sub_self(n1))
      %Equal.sym(Nat, Nat.sub(1n+n1, n1), 1n+s0, esub0) : {L.mat_get(L.mirror_upper(L.arr_lower_rows.fin(L.upper_tri.loop(n1, L.read_down(_, a, Nil{}, b0), Nil{}, 1n+n1, n))), i, j) == L.mat_get(L.mirror_upper(L.arr_lower_rows.fin(L.upper_tri.loop(n1, L.read_down(_, a, Nil{}, b0), Nil{}, 1n+n1, n))), j, i) : Maybe<&2, F32>}
      upper_tri_sym_lex(n1, s0, Array.get(F32, a, (b0 + U32.from_nat(s0) : U32)), Nil{}, b0, Nil{}, n1, n, i, j, hlt0, hlen0, ha0)

def arr_upper_tri_sym(a: Array<F32>, +n: U32, +i: Nat, +j: Nat) -> {L.mat_get(L.mirror_upper(L.arr_upper_tri(a, n)), i, j) == L.mat_get(L.mirror_upper(L.arr_upper_tri(a, n)), j, i) : Maybe<&2, F32>}:
  arr_upper_tri_sym.go(a, U32.to_nat(n), n, i, j)

def Laws.gram_sym(m, n, rows, i, j, h):
  arr_upper_tri_sym(L.gram_arr(rows, m, n), n, i, j)

def wgram_chk_sym(ok: Bool, +m: U32, +n: U32, +rows: List<&2, List<&2, F32>>, +ws: List<&2, F32>, +i: Nat, +j: Nat) -> {Laws.mm_get(L.wgram.chk(ok, m, n, rows, ws), i, j) == Laws.mm_get(L.wgram.chk(ok, m, n, rows, ws), j, i) : Maybe<&2, F32>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      arr_upper_tri_sym(L.wgram_arr(rows, ws, m, n), n, i, j)

def Laws.wgram_sym(m, n, nw, rows, ws, i, j, e, h):
  %Equal.sym(Bool, U32.is_eq(m, nw), True{}, e) : {Laws.mm_get(L.wgram.chk(_, m, n, rows, ws), i, j) == Laws.mm_get(L.wgram.chk(_, m, n, rows, ws), j, i) : Maybe<&2, F32>}
  arr_upper_tri_sym(L.wgram_arr(rows, ws, m, n), n, i, j)

def spd_pow_build_sym(lp: Maybe<&2, List<&2, F32>>, +n: U32, ut: L.Mat, +i: Nat, +j: Nat) -> {Laws.mm_get(L.spd_pow.build(lp, n, ut), i, j) == Laws.mm_get(L.spd_pow.build(lp, n, ut), j, i) : Maybe<&2, F32>}:
  match lp ut:
    case None{} _:
      {==}
    case Some{+lps} L.Mat{+um, +un, +urows}:
      wgram_chk_sym(U32.is_eq(um, n), um, un, urows, lps, i, j)

def spd_pow_chk_sym(me: Maybe<&2, L.Eigen>, +p: F32, +i: Nat, +j: Nat) -> {Laws.mm_get(L.spd_pow.chk(me, p), i, j) == Laws.mm_get(L.spd_pow.chk(me, p), j, i) : Maybe<&2, F32>}:
  match me:
    case None{}:
      {==}
    case Some{L.Eigen{L.Vec{+n, +lams}, +u}}:
      spd_pow_build_sym(L.pow_pos_list(lams, p), n, L.transpose(u), i, j)

def Laws.spd_pow_sym(a, p, i, j):
  spd_pow_chk_sym(L.sym_eigen(a), p, i, j)

def Laws.procrustes_mismatch(ma, na, mb, nb, arows, brows, e):
  %Equal.sym(Bool, Bool.and(U32.is_eq(ma, mb), U32.is_eq(na, nb)), False{}, e) : {L.procrustes.chk(_, L.Mat{ma, na, arows}, L.Mat{mb, nb, brows}) == None{} : Maybe<&2, L.Mat>}
  {==}

# ---------------------------------------------------------------- U32 equality soundness

def bool_cmp_eq(a: Bool, b: Bool, h: {Cmp.is_eq(Bool.cmp(a, b)) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, false_ne_true(h))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, false_ne_true(h))
    case True{} True{}:
      {==}

def cmp_fin_t(+ab: Bool, +bb: Bool, t: Cmp, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, t)) == True{} : Bool}) -> {Cmp.is_eq(t) == True{} : Bool}:
  match t:
    case LT{}:
      Empty.absurd({False{} == True{} : Bool}, false_ne_true(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, false_ne_true(h))

def cmp_fin_b(ab: Bool, bb: Bool, t: Cmp, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, t)) == True{} : Bool}) -> {ab == bb : Bool}:
  match t:
    case LT{}:
      Empty.absurd({ab == bb : Bool}, false_ne_true(h))
    case EQ{}:
      bool_cmp_eq(ab, bb, h)
    case GT{}:
      Empty.absurd({ab == bb : Bool}, false_ne_true(h))

def word_eq_sound(n: Nat, a: Word(n), b: Word(n), +h: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          +e1 = cmp_fin_b(ab, bb, Word.cmp(p, at, bt), h)
          +e2 = word_eq_sound(p, at, bt, cmp_fin_t(ab, bb, Word.cmp(p, at, bt), h))
          %e1 : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
          %e2 : {WCon{ab, at} == WCon{ab, _} : Word(1n+p)}
          {==}

def u32_eq_nat(a: U32, b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {U32.to_nat(a) == U32.to_nat(b) : Nat}:
  match a b:
    case U32{+x} U32{+y}:
      %word_eq_sound(32n, x, y, h) : {Word.to_nat(32n, x) == Word.to_nat(32n, _) : Nat}
      {==}


# ---------------------------------------------------------------- Bool conjunction helpers

def eq_true(+a: Nat, +b: Nat, e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Nat.is_eq(_, b) == True{} : Bool}
  nat_eq_refl(b)

def and2(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def and9(+c1: Bool, +c2: Bool, +c3: Bool, +c4: Bool, +c5: Bool, +c6: Bool, +c7: Bool, +c8: Bool, +c9: Bool, h1: {c1 == True{} : Bool}, h2: {c2 == True{} : Bool}, h3: {c3 == True{} : Bool}, h4: {c4 == True{} : Bool}, h5: {c5 == True{} : Bool}, h6: {c6 == True{} : Bool}, h7: {c7 == True{} : Bool}, h8: {c8 == True{} : Bool}, h9: {c9 == True{} : Bool}) -> {Bool.and(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))))) == True{} : Bool}:
  %Equal.sym(Bool, c1, True{}, h1) : {Bool.and(_, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))))) == True{} : Bool}
  %Equal.sym(Bool, c2, True{}, h2) : {Bool.and(_, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))))))) == True{} : Bool}
  %Equal.sym(Bool, c3, True{}, h3) : {Bool.and(_, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))) == True{} : Bool}
  %Equal.sym(Bool, c4, True{}, h4) : {Bool.and(_, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))))) == True{} : Bool}
  %Equal.sym(Bool, c5, True{}, h5) : {Bool.and(_, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))) == True{} : Bool}
  %Equal.sym(Bool, c6, True{}, h6) : {Bool.and(_, Bool.and(c7, Bool.and(c8, c9))) == True{} : Bool}
  %Equal.sym(Bool, c7, True{}, h7) : {Bool.and(_, Bool.and(c8, c9)) == True{} : Bool}
  %Equal.sym(Bool, c8, True{}, h8) : {Bool.and(_, c9) == True{} : Bool}
  h9

def and9_1(+c1: Bool, +c2: Bool, +c3: Bool, +c4: Bool, +c5: Bool, +c6: Bool, +c7: Bool, +c8: Bool, +c9: Bool, h: {Bool.and(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))))) == True{} : Bool}) -> {c1 == True{} : Bool}:
  bool_and_l(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))))))), h)

def and9_2(+c1: Bool, +c2: Bool, +c3: Bool, +c4: Bool, +c5: Bool, +c6: Bool, +c7: Bool, +c8: Bool, +c9: Bool, h: {Bool.and(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))))) == True{} : Bool}) -> {c2 == True{} : Bool}:
  bool_and_l(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))), bool_and_r(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))))))), h))

def and9_3(+c1: Bool, +c2: Bool, +c3: Bool, +c4: Bool, +c5: Bool, +c6: Bool, +c7: Bool, +c8: Bool, +c9: Bool, h: {Bool.and(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))))) == True{} : Bool}) -> {c3 == True{} : Bool}:
  bool_and_l(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))))), bool_and_r(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))), bool_and_r(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))))))), h)))

def and9_4(+c1: Bool, +c2: Bool, +c3: Bool, +c4: Bool, +c5: Bool, +c6: Bool, +c7: Bool, +c8: Bool, +c9: Bool, h: {Bool.and(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))))) == True{} : Bool}) -> {c4 == True{} : Bool}:
  bool_and_l(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))), bool_and_r(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))))), bool_and_r(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))), bool_and_r(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))))))), h))))

def and9_5(+c1: Bool, +c2: Bool, +c3: Bool, +c4: Bool, +c5: Bool, +c6: Bool, +c7: Bool, +c8: Bool, +c9: Bool, h: {Bool.and(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))))) == True{} : Bool}) -> {c5 == True{} : Bool}:
  bool_and_l(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))), bool_and_r(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))), bool_and_r(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))))), bool_and_r(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))), bool_and_r(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))))))), h)))))

def and9_6(+c1: Bool, +c2: Bool, +c3: Bool, +c4: Bool, +c5: Bool, +c6: Bool, +c7: Bool, +c8: Bool, +c9: Bool, h: {Bool.and(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))))) == True{} : Bool}) -> {c6 == True{} : Bool}:
  bool_and_l(c6, Bool.and(c7, Bool.and(c8, c9)), bool_and_r(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))), bool_and_r(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))), bool_and_r(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))))), bool_and_r(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))), bool_and_r(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))))))), h))))))

def and9_7(+c1: Bool, +c2: Bool, +c3: Bool, +c4: Bool, +c5: Bool, +c6: Bool, +c7: Bool, +c8: Bool, +c9: Bool, h: {Bool.and(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))))) == True{} : Bool}) -> {c7 == True{} : Bool}:
  bool_and_l(c7, Bool.and(c8, c9), bool_and_r(c6, Bool.and(c7, Bool.and(c8, c9)), bool_and_r(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))), bool_and_r(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))), bool_and_r(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))))), bool_and_r(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))), bool_and_r(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))))))), h)))))))

def and9_8(+c1: Bool, +c2: Bool, +c3: Bool, +c4: Bool, +c5: Bool, +c6: Bool, +c7: Bool, +c8: Bool, +c9: Bool, h: {Bool.and(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))))) == True{} : Bool}) -> {c8 == True{} : Bool}:
  bool_and_l(c8, c9, bool_and_r(c7, Bool.and(c8, c9), bool_and_r(c6, Bool.and(c7, Bool.and(c8, c9)), bool_and_r(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))), bool_and_r(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))), bool_and_r(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))))), bool_and_r(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))), bool_and_r(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))))))), h))))))))

def and9_9(+c1: Bool, +c2: Bool, +c3: Bool, +c4: Bool, +c5: Bool, +c6: Bool, +c7: Bool, +c8: Bool, +c9: Bool, h: {Bool.and(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))))) == True{} : Bool}) -> {c9 == True{} : Bool}:
  bool_and_r(c8, c9, bool_and_r(c7, Bool.and(c8, c9), bool_and_r(c6, Bool.and(c7, Bool.and(c8, c9)), bool_and_r(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))), bool_and_r(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))), bool_and_r(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))))), bool_and_r(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9)))))), bool_and_r(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, Bool.and(c6, Bool.and(c7, Bool.and(c8, c9))))))), h))))))))


# ---------------------------------------------------------------- SVD column lists

def svd_vok(cols: List<&2, L.SVDCol>, +nn: Nat) -> Bool:
  match cols:
    case Nil{}:
      True{}
    case Con{L.SVDCol{_, _, v}, t}:
      Bool.and(Nat.is_eq(List.length(&2, F32, v), nn), svd_vok(t, nn))

def svd_ins_pick_len(ge: Bool, +x: L.SVDCol, +y: L.SVDCol, +t: List<&2, L.SVDCol>, +rec: List<&2, L.SVDCol>, hrec: {List.length(&2, L.SVDCol, rec) == 1n+List.length(&2, L.SVDCol, t) : Nat}) -> {List.length(&2, L.SVDCol, L.svd_ins.pick(ge, x, y, t, rec)) == 1n+1n+List.length(&2, L.SVDCol, t) : Nat}:
  match ge:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Nat, List.length(&2, L.SVDCol, rec), 1n+List.length(&2, L.SVDCol, t), hrec) : {1n+_ == 1n+1n+List.length(&2, L.SVDCol, t) : Nat}
      {==}

def svd_ins_len(+x: L.SVDCol, xs: List<&2, L.SVDCol>) -> {List.length(&2, L.SVDCol, L.svd_ins(x, xs)) == 1n+List.length(&2, L.SVDCol, xs) : Nat}:
  match x xs:
    case L.SVDCol{+sx, +ux, +vx} Nil{}:
      {==}
    case L.SVDCol{+sx, +ux, +vx} Con{L.SVDCol{+sy, +uy, +vy}, +t}:
      svd_ins_pick_len(F32.is_ge(sx, sy), L.SVDCol{sx, ux, vx}, L.SVDCol{sy, uy, vy}, t, L.svd_ins(L.SVDCol{sx, ux, vx}, t), svd_ins_len(L.SVDCol{sx, ux, vx}, t))

def svd_sort_len(xs: List<&2, L.SVDCol>) -> {List.length(&2, L.SVDCol, L.svd_sort(xs)) == List.length(&2, L.SVDCol, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Nat, List.length(&2, L.SVDCol, L.svd_ins(h, L.svd_sort(t))), 1n+List.length(&2, L.SVDCol, L.svd_sort(t)), 1n+List.length(&2, L.SVDCol, t), svd_ins_len(h, L.svd_sort(t)), Equal.cong(Nat, Nat, q => 1n+q, List.length(&2, L.SVDCol, L.svd_sort(t)), List.length(&2, L.SVDCol, t), svd_sort_len(t)))

def svd_ins_pick_ok(ge: Bool, +sx: F32, +ux: List<&2, F32>, +vx: List<&2, F32>, +sy: F32, +uy: List<&2, F32>, +vy: List<&2, F32>, +t: List<&2, L.SVDCol>, +rec: List<&2, L.SVDCol>, +nn: Nat, hx: {Nat.is_eq(List.length(&2, F32, vx), nn) == True{} : Bool}, hy: {Nat.is_eq(List.length(&2, F32, vy), nn) == True{} : Bool}, ht: {svd_vok(t, nn) == True{} : Bool}, hrec: {svd_vok(rec, nn) == True{} : Bool}) -> {svd_vok(L.svd_ins.pick(ge, L.SVDCol{sx, ux, vx}, L.SVDCol{sy, uy, vy}, t, rec), nn) == True{} : Bool}:
  match ge:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(List.length(&2, F32, vx), nn), True{}, hx) : {Bool.and(_, Bool.and(Nat.is_eq(List.length(&2, F32, vy), nn), svd_vok(t, nn))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(List.length(&2, F32, vy), nn), True{}, hy) : {Bool.and(_, svd_vok(t, nn)) == True{} : Bool}
      ht
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(List.length(&2, F32, vy), nn), True{}, hy) : {Bool.and(_, svd_vok(rec, nn)) == True{} : Bool}
      hrec

def svd_ins_ok(+x: L.SVDCol, xs: List<&2, L.SVDCol>, +nn: Nat, +hx: {svd_vok(x <> Nil{}, nn) == True{} : Bool}, +hxs: {svd_vok(xs, nn) == True{} : Bool}) -> {svd_vok(L.svd_ins(x, xs), nn) == True{} : Bool}:
  match x xs:
    case L.SVDCol{+sx, +ux, +vx} Nil{}:
      hx
    case L.SVDCol{+sx, +ux, +vx} Con{L.SVDCol{+sy, +uy, +vy}, +t}:
      +hx1 = bool_and_l(Nat.is_eq(List.length(&2, F32, vx), nn), True{}, hx)
      +hy1 = bool_and_l(Nat.is_eq(List.length(&2, F32, vy), nn), svd_vok(t, nn), hxs)
      +ht1 = bool_and_r(Nat.is_eq(List.length(&2, F32, vy), nn), svd_vok(t, nn), hxs)
      svd_ins_pick_ok(F32.is_ge(sx, sy), sx, ux, vx, sy, uy, vy, t, L.svd_ins(L.SVDCol{sx, ux, vx}, t), nn, hx1, hy1, ht1, svd_ins_ok(L.SVDCol{sx, ux, vx}, t, nn, hx, ht1))

def svd_sort_ok(xs: List<&2, L.SVDCol>, +nn: Nat, +h: {svd_vok(xs, nn) == True{} : Bool}) -> {svd_vok(L.svd_sort(xs), nn) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{L.SVDCol{+s, +u, +v}, +t}:
      +hc = bool_and_l(Nat.is_eq(List.length(&2, F32, v), nn), svd_vok(t, nn), h)
      +ht = bool_and_r(Nat.is_eq(List.length(&2, F32, v), nn), svd_vok(t, nn), h)
      svd_ins_ok(L.SVDCol{s, u, v}, L.svd_sort(t), nn, and2(Nat.is_eq(List.length(&2, F32, v), nn), True{}, hc, {==}), svd_sort_ok(t, nn, ht))

def svd_sigs_len(xs: List<&2, L.SVDCol>) -> {List.length(&2, F32, L.svd_sigs(xs)) == List.length(&2, L.SVDCol, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{L.SVDCol{_, _, _}, +t}:
      %Equal.sym(Nat, List.length(&2, F32, L.svd_sigs(t)), List.length(&2, L.SVDCol, t), svd_sigs_len(t)) : {1n+_ == 1n+List.length(&2, L.SVDCol, t) : Nat}
      {==}

def svd_vrows_len(xs: List<&2, L.SVDCol>) -> {List.length(&2, List<&2, F32>, L.svd_vrows(xs)) == List.length(&2, L.SVDCol, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{L.SVDCol{_, _, _}, +t}:
      %Equal.sym(Nat, List.length(&2, List<&2, F32>, L.svd_vrows(t)), List.length(&2, L.SVDCol, t), svd_vrows_len(t)) : {1n+_ == 1n+List.length(&2, L.SVDCol, t) : Nat}
      {==}

def svd_vrows_ok(xs: List<&2, L.SVDCol>, +nn: Nat, +h: {svd_vok(xs, nn) == True{} : Bool}) -> {L.Mat.rows.ok(L.svd_vrows(xs), nn) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{L.SVDCol{_, _, +v}, +t}:
      +hc = bool_and_l(Nat.is_eq(List.length(&2, F32, v), nn), svd_vok(t, nn), h)
      +ht = bool_and_r(Nat.is_eq(List.length(&2, F32, v), nn), svd_vok(t, nn), h)
      %Equal.sym(Bool, Nat.is_eq(List.length(&2, F32, v), nn), True{}, hc) : {Bool.and(_, L.Mat.rows.ok(L.svd_vrows(t), nn)) == True{} : Bool}
      svd_vrows_ok(t, nn, ht)

def svd_build_u_len(cols: List<&2, L.SVDCol>, +basis: List<&2, List<&2, F32>>, +nn: Nat) -> {List.length(&2, List<&2, F32>, L.svd_build_u(cols, basis, nn)) == Nat.add(List.length(&2, L.SVDCol, cols), List.length(&2, List<&2, F32>, basis)) : Nat}:
  match cols:
    case Nil{}:
      MList.length_reverse(&2, List<&2, F32>, basis)
    case Con{L.SVDCol{+sig, ucol, _}, +t}:
      +u = L.svd_norm_u.pos(F32.is_gt(sig, 0.0), sig, ucol, nn, basis)
      Equal.trans(Nat, List.length(&2, List<&2, F32>, L.svd_build_u(t, u <> basis, nn)), Nat.add(List.length(&2, L.SVDCol, t), 1n+List.length(&2, List<&2, F32>, basis)), 1n+Nat.add(List.length(&2, L.SVDCol, t), List.length(&2, List<&2, F32>, basis)), svd_build_u_len(t, u <> basis, nn), add_succ_r(List.length(&2, L.SVDCol, t), List.length(&2, List<&2, F32>, basis)))

# ---------------------------------------------------------------- svd_thin shape

def svd_intro(+um: Nat, +un: Nat, +urows: List<&2, List<&2, F32>>, +k: Nat, +sigs: List<&2, F32>, +vm: Nat, +vn: Nat, +vrows: List<&2, List<&2, F32>>, +m: Nat, +n: Nat, e1: {um == m : Nat}, e2: {un == k : Nat}, e3: {vm == k : Nat}, e4: {vn == n : Nat}, e5: {List.length(&2, List<&2, F32>, urows) == m : Nat}, h6: {L.Mat.rows.ok(urows, k) == True{} : Bool}, e7: {List.length(&2, F32, sigs) == k : Nat}, e8: {List.length(&2, List<&2, F32>, vrows) == k : Nat}, h9: {L.Mat.rows.ok(vrows, n) == True{} : Bool}) -> {Laws.svd_shape(um, un, urows, k, sigs, vm, vn, vrows, m, n) == True{} : Bool}:
  and9(Nat.is_eq(um, m), Nat.is_eq(un, k), Nat.is_eq(vm, k), Nat.is_eq(vn, n), Nat.is_eq(List.length(&2, List<&2, F32>, urows), m), L.Mat.rows.ok(urows, k), Nat.is_eq(List.length(&2, F32, sigs), k), Nat.is_eq(List.length(&2, List<&2, F32>, vrows), k), L.Mat.rows.ok(vrows, n), eq_true(um, m, e1), eq_true(un, k, e2), eq_true(vm, k, e3), eq_true(vn, n, e4), eq_true(List.length(&2, List<&2, F32>, urows), m, e5), h6, eq_true(List.length(&2, F32, sigs), k, e7), eq_true(List.length(&2, List<&2, F32>, vrows), k, e8), h9)

def fin_p(cols: List<&2, L.SVDCol>, +q0: List<&2, List<&2, F32>>, +m: U32, +n: U32, +nn: Nat) -> Bool:
  +sorted = L.svd_sort(cols)
  Laws.svd_shape(U32.to_nat(m), U32.to_nat(n), L.pmap(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, q0, m, L.svd_build_u(sorted, Nil{}, nn)), U32.to_nat(n), L.svd_sigs(sorted), U32.to_nat(n), U32.to_nat(n), L.svd_vrows(sorted), U32.to_nat(m), U32.to_nat(n))

def fin_from_cols(+cols: List<&2, L.SVDCol>, +q0: List<&2, List<&2, F32>>, +m: U32, +n: U32, +nn: Nat, +hq: {List.length(&2, List<&2, F32>, q0) == U32.to_nat(m) : Nat}, +hl: {List.length(&2, L.SVDCol, cols) == nn : Nat}, +ho: {svd_vok(cols, nn) == True{} : Bool}, +hnn: {nn == U32.to_nat(n) : Nat}) -> {fin_p(cols, q0, m, n, nn) == True{} : Bool}:
  +sorted = L.svd_sort(cols)
  +ucols = L.svd_build_u(sorted, Nil{}, nn)
  +urows = L.pseq(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, q0, ucols)
  +hlen_s = Equal.trans(Nat, List.length(&2, L.SVDCol, sorted), List.length(&2, L.SVDCol, cols), U32.to_nat(n), svd_sort_len(cols), Equal.trans(Nat, List.length(&2, L.SVDCol, cols), nn, U32.to_nat(n), hl, hnn))
  +hok_s = svd_sort_ok(cols, nn, ho)
  +hlen_u = Equal.trans(Nat, List.length(&2, List<&2, F32>, ucols), Nat.add(List.length(&2, L.SVDCol, sorted), 0n), U32.to_nat(n), svd_build_u_len(sorted, Nil{}, nn), Equal.trans(Nat, Nat.add(List.length(&2, L.SVDCol, sorted), 0n), List.length(&2, L.SVDCol, sorted), U32.to_nat(n), add_zero_r(List.length(&2, L.SVDCol, sorted)), hlen_s))
  %Equal.sym(List<&2, List<&2, F32>>, L.pmap(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, q0, m, ucols), L.pseq(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, q0, ucols), Laws.pmap_seq(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, q0, m, ucols)) : {Laws.svd_shape(U32.to_nat(m), U32.to_nat(n), _, U32.to_nat(n), L.svd_sigs(sorted), U32.to_nat(n), U32.to_nat(n), L.svd_vrows(sorted), U32.to_nat(m), U32.to_nat(n)) == True{} : Bool}
  svd_intro(U32.to_nat(m), U32.to_nat(n), urows, U32.to_nat(n), L.svd_sigs(sorted), U32.to_nat(n), U32.to_nat(n), L.svd_vrows(sorted), U32.to_nat(m), U32.to_nat(n), {==}, {==}, {==}, {==}, Equal.trans(Nat, List.length(&2, List<&2, F32>, urows), List.length(&2, List<&2, F32>, q0), U32.to_nat(m), pseq_len(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, q0, ucols), hq), mm_rows_ok(q0, ucols, U32.to_nat(n), hlen_u), Equal.trans(Nat, List.length(&2, F32, L.svd_sigs(sorted)), List.length(&2, L.SVDCol, sorted), U32.to_nat(n), svd_sigs_len(sorted), hlen_s), Equal.trans(Nat, List.length(&2, List<&2, F32>, L.svd_vrows(sorted)), List.length(&2, L.SVDCol, sorted), U32.to_nat(n), svd_vrows_len(sorted), hlen_s), rows_ok_eq(L.svd_vrows(sorted), nn, U32.to_nat(n), hnn, svd_vrows_ok(sorted, nn, hok_s)))

# Walks svd_extract.loop and the read_down.loop under it together (lexicographic in
# (outer, inner)) so each Array is used once; the invariant lives on the Data lists.
def ext_lex(+outer: Nat, +inner: Nat, rb: Array<F32> & List<&2, F32>, r: Array<F32> & F32, +rd_acc: List<&2, F32>, +base: U32, +acc: List<&2, L.SVDCol>, +nn: Nat, +n: U32, +q0: List<&2, List<&2, F32>>, +m: U32, +hq: {List.length(&2, List<&2, F32>, q0) == U32.to_nat(m) : Nat}, +hlen: {1n+Nat.add(inner, List.length(&2, F32, rd_acc)) == nn : Nat}, +hcnt: {1n+Nat.add(outer, List.length(&2, L.SVDCol, acc)) == nn : Nat}, +ha: {svd_vok(acc, nn) == True{} : Bool}, +hnn: {nn == U32.to_nat(n) : Nat}) -> {fin_p(L.svd_extract.loop(outer, rb, L.read_down.loop(inner, r, rd_acc, base), acc, nn, n), q0, m, n, nn) == True{} : Bool}:
  match outer inner:
    case _ 1n+(+q):
      match r:
        case (a, +val):
          +hl2 = Equal.trans(Nat, 1n+Nat.add(q, 1n+List.length(&2, F32, rd_acc)), 1n+1n+Nat.add(q, List.length(&2, F32, rd_acc)), nn, Equal.cong(Nat, Nat, z => 1n+z, Nat.add(q, 1n+List.length(&2, F32, rd_acc)), 1n+Nat.add(q, List.length(&2, F32, rd_acc)), add_succ_r(q, List.length(&2, F32, rd_acc))), hlen)
          ext_lex(outer, q, rb, Array.get(F32, a, (base + U32.from_nat(q) : U32)), val <> rd_acc, base, acc, nn, n, q0, m, hq, hl2, hcnt, ha, hnn)
    case 0n 0n:
      match rb:
        case (_, +bcol):
          match r:
            case (a, +val):
              +col = {val <> rd_acc : List<&2, F32>}
              +cols = {L.SVDCol{F32.sqrt(L.dot_raw(bcol, bcol)), bcol, col} <> acc : List<&2, L.SVDCol>}
              fin_from_cols(cols, q0, m, n, nn, hq, hcnt, and2(Nat.is_eq(List.length(&2, F32, col), nn), svd_vok(acc, nn), eq_true(List.length(&2, F32, col), nn, hlen), ha), hnn)
    case 1n+(+p) 0n:
      match rb:
        case (b, +bcol):
          match r:
            case (a, +val):
              match nn:
                case 0n:
                  Empty.absurd({fin_p(L.svd_extract.loop(1n+p, rb, L.read_down.loop(0n, (a, val), rd_acc, base), acc, 0n, n), q0, m, n, 0n) == True{} : Bool}, succ_ne_zero(List.length(&2, F32, rd_acc), hlen))
                case 1n+(+n1):
                  +col = {val <> rd_acc : List<&2, F32>}
                  +acc2 = {L.SVDCol{F32.sqrt(L.dot_raw(bcol, bcol)), bcol, col} <> acc : List<&2, L.SVDCol>}
                  +off = (U32.from_nat(p) * n : U32)
                  +hcnt2 = Equal.trans(Nat, 1n+Nat.add(p, 1n+List.length(&2, L.SVDCol, acc)), 1n+1n+Nat.add(p, List.length(&2, L.SVDCol, acc)), 1n+n1, Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+List.length(&2, L.SVDCol, acc)), 1n+Nat.add(p, List.length(&2, L.SVDCol, acc)), add_succ_r(p, List.length(&2, L.SVDCol, acc))), hcnt)
                  +ha2 = and2(Nat.is_eq(List.length(&2, F32, col), 1n+n1), svd_vok(acc, 1n+n1), eq_true(List.length(&2, F32, col), 1n+n1, hlen), ha)
                  ext_lex(p, n1, L.read_down(1n+n1, b, Nil{}, off), Array.get(F32, a, (off + U32.from_nat(n1) : U32)), Nil{}, off, acc2, 1n+n1, n, q0, m, hq, Equal.cong(Nat, Nat, z => 1n+z, Nat.add(n1, 0n), n1, add_zero_r(n1)), hcnt2, ha2, hnn)

def ext_go_fin(+nn: Nat, b: Array<F32>, v: Array<F32>, +q0: List<&2, List<&2, F32>>, +m: U32, +n: U32, +hq: {List.length(&2, List<&2, F32>, q0) == U32.to_nat(m) : Nat}, +hnn: {nn == U32.to_nat(n) : Nat}) -> {fin_p(L.svd_extract.go(nn, b, v, Nil{}, nn, n), q0, m, n, nn) == True{} : Bool}:
  match nn:
    case 0n:
      fin_from_cols(Nil{}, q0, m, n, 0n, hq, {==}, {==}, hnn)
    case 1n+(+n1):
      +off = (U32.from_nat(n1) * n : U32)
      +h1 = Equal.cong(Nat, Nat, z => 1n+z, Nat.add(n1, 0n), n1, add_zero_r(n1))
      ext_lex(n1, n1, L.read_down(1n+n1, b, Nil{}, off), Array.get(F32, v, (off + U32.from_nat(n1) : U32)), Nil{}, off, Nil{}, 1n+n1, n, q0, m, hq, h1, h1, {==}, hnn)

def tall_fin_ok(st: L.JSt, +q0: List<&2, List<&2, F32>>, +m: U32, +n: U32, +hq: {List.length(&2, List<&2, F32>, q0) == U32.to_nat(m) : Nat}) -> {Laws.svd_ok(L.svd_tall.fin(st, q0, m, n), m, n) == True{} : Bool}:
  match st:
    case L.JSt{b, v, _}:
      ext_go_fin(U32.to_nat(n), b, v, q0, m, n, hq, {==})

def tall_qr_ok(qr: L.QR, +m: U32, +n: U32, hq: {Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(Laws.qr_q(qr))), U32.to_nat(m)) == True{} : Bool}) -> {Laws.svd_ok(L.svd_tall.from_qr(qr, m, n), m, n) == True{} : Bool}:
  match qr:
    case L.QR{L.Mat{_, _, +q0}, L.Mat{_, _, r0}}:
      +nn = U32.to_nat(n)
      tall_fin_ok(L.svd_j.sweeps(20n, L.JSt{L.mat_to_colmajor(r0, n, n), L.fill_eye_cm(nn, Array.new(F32, L.arr_depth((n * n : U32)), 0.0), 0, n), True{}}, n, nn), q0, m, n, nat_eq_sound(List.length(&2, List<&2, F32>, q0), U32.to_nat(m), hq))

def vscale_len(+s: F32, xs: List<&2, F32>) -> {List.length(&2, F32, L.vscale.go(s, xs)) == List.length(&2, F32, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      %vscale_len(s, t) : {1n+List.length(&2, F32, L.vscale.go(s, t)) == 1n+_ : Nat}
      {==}

def row_unit_len(rem: Nat, +j: Nat, +target: Nat) -> {List.length(&2, F32, L.row_unit(rem, j, target)) == rem : Nat}:
  match rem:
    case 0n:
      {==}
    case 1n+p:
      %row_unit_len(p, 1n+j, target) : {1n+List.length(&2, F32, L.row_unit(p, 1n+j, target)) == 1n+_ : Nat}
      {==}

def n1_col_len(rows: List<&2, List<&2, F32>>) -> {List.length(&2, F32, L.svd_tall.n1_col(rows)) == List.length(&2, List<&2, F32>, rows) : Nat}:
  match rows:
    case Nil{}:
      {==}
    case Con{Con{x, _}, t}:
      %n1_col_len(t) : {1n+List.length(&2, F32, L.svd_tall.n1_col(t)) == 1n+_ : Nat}
      {==}
    case Con{Nil{}, t}:
      %n1_col_len(t) : {1n+List.length(&2, F32, L.svd_tall.n1_col(t)) == 1n+_ : Nat}
      {==}

def n1_unit_len(pos: Bool, +s0: F32, +col: List<&2, F32>, +m: U32, hc: {List.length(&2, F32, col) == U32.to_nat(m) : Nat}) -> {List.length(&2, F32, L.svd_tall.n1_unit(pos, s0, col, m)) == U32.to_nat(m) : Nat}:
  match pos:
    case True{}:
      Equal.trans(Nat, List.length(&2, F32, L.vscale.go((1.0 / s0 : F32), col)), List.length(&2, F32, col), U32.to_nat(m), vscale_len((1.0 / s0 : F32), col), hc)
    case False{}:
      row_unit_len(U32.to_nat(m), 0n, 0n)

def tall_n1_ok(+rows: List<&2, List<&2, F32>>, +m: U32, +n: U32, hn: {U32.is_eq(n, 1) == True{} : Bool}, hl: {List.length(&2, List<&2, F32>, rows) == U32.to_nat(m) : Nat}) -> {Laws.svd_ok(L.svd_tall.n1(rows, m), m, n) == True{} : Bool}:
  +mm = U32.to_nat(m)
  +col = L.svd_tall.n1_col(rows)
  +s0 = F32.sqrt(L.dot_raw(col, col))
  +ucol = L.svd_tall.n1_unit(F32.is_gt(s0, 0.0), s0, col, m)
  +rep = List.replicate(List<&2, F32>, mm, Nil{})
  +hu = n1_unit_len(F32.is_gt(s0, 0.0), s0, col, m, Equal.trans(Nat, List.length(&2, F32, col), List.length(&2, List<&2, F32>, rows), mm, n1_col_len(rows), hl))
  +hz = Equal.trans(Nat, List.length(&2, F32, ucol), mm, List.length(&2, List<&2, F32>, rep), hu, Equal.sym(Nat, List.length(&2, List<&2, F32>, rep), mm, len_replicate(List<&2, F32>, mm, Nil{})))
  +e1n = Equal.sym(Nat, U32.to_nat(n), U32.to_nat(1), u32_eq_nat(n, 1, hn))
  svd_intro(mm, 1n, L.zip_cons(ucol, rep), 1n, s0 <> Nil{}, 1n, 1n, (1.0 <> Nil{}) <> Nil{}, mm, U32.to_nat(n), {==}, {==}, {==}, e1n, Equal.trans(Nat, List.length(&2, List<&2, F32>, L.zip_cons(ucol, rep)), List.length(&2, F32, ucol), mm, zip_cons_len(ucol, rep, hz), hu), zip_cons_ok(ucol, rep, 0n, hz, replicate_nil_ok(mm)), {==}, {==}, rows_ok_eq((1.0 <> Nil{}) <> Nil{}, 1n, U32.to_nat(n), e1n, {==}))

def tall_gt0_ok(+rows: List<&2, List<&2, F32>>, +m: U32, +n: U32, o: Bool, ho: {o == U32.is_eq(n, 1) : Bool}, hl: {List.length(&2, List<&2, F32>, rows) == U32.to_nat(m) : Nat}) -> {Laws.svd_ok(L.svd_tall.gt0(o, rows, m, n), m, n) == True{} : Bool}:
  match o:
    case True{}:
      tall_n1_ok(rows, m, n, Equal.sym(Bool, True{}, U32.is_eq(n, 1), ho), hl)
    case False{}:
      +qr = L.qr_thin.fin(L.qr_factor_arr(rows, m, n), m, n)
      tall_qr_ok(qr, m, n, bool_and_l(Nat.is_eq(List.length(&2, List<&2, F32>, Laws.mat_rows(Laws.qr_q(qr))), U32.to_nat(m)), L.Mat.rows.ok(Laws.mat_rows(Laws.qr_q(qr)), U32.to_nat(n)), qr_fin_q_shape(L.qr_factor_arr(rows, m, n), m, n, qr, {==})))

def tall_go_ok(+rows: List<&2, List<&2, F32>>, +m: U32, +n: U32, z: Bool, hz: {z == U32.is_eq(n, 0) : Bool}, hl: {List.length(&2, List<&2, F32>, rows) == U32.to_nat(m) : Nat}) -> {Laws.svd_ok(L.svd_tall.go(z, rows, m, n), m, n) == True{} : Bool}:
  match z:
    case True{}:
      +mm = U32.to_nat(m)
      +e0 = Equal.sym(Nat, U32.to_nat(n), U32.to_nat(0), u32_eq_nat(n, 0, Equal.sym(Bool, True{}, U32.is_eq(n, 0), hz)))
      svd_intro(mm, 0n, List.replicate(List<&2, F32>, mm, Nil{}), 0n, Nil{}, 0n, 0n, Nil{}, mm, U32.to_nat(n), {==}, {==}, {==}, e0, len_replicate(List<&2, F32>, mm, Nil{}), replicate_nil_ok(mm), {==}, {==}, {==})
    case False{}:
      tall_gt0_ok(rows, m, n, U32.is_eq(n, 1), {==}, hl)

def flip_ok(sv: L.SVD, +m: U32, +n: U32, +h: {Laws.svd_ok(sv, n, m) == True{} : Bool}) -> {Laws.svd_ok(L.svd_wide.flip(sv), m, n) == True{} : Bool}:
  match sv:
    case L.SVD{L.Mat{+um, +un, +ur}, L.Vec{+k, +s}, L.Mat{+vm, +vn, +vr}}:
      +e1 = nat_eq_sound(U32.to_nat(um), U32.to_nat(n), and9_1(Nat.is_eq(U32.to_nat(um), U32.to_nat(n)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(m)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(n)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(m)), h))
      +e2 = nat_eq_sound(U32.to_nat(un), U32.to_nat(k), and9_2(Nat.is_eq(U32.to_nat(um), U32.to_nat(n)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(m)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(n)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(m)), h))
      +e3 = nat_eq_sound(U32.to_nat(vm), U32.to_nat(k), and9_3(Nat.is_eq(U32.to_nat(um), U32.to_nat(n)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(m)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(n)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(m)), h))
      +e4 = nat_eq_sound(U32.to_nat(vn), U32.to_nat(m), and9_4(Nat.is_eq(U32.to_nat(um), U32.to_nat(n)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(m)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(n)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(m)), h))
      +e5 = nat_eq_sound(List.length(&2, List<&2, F32>, ur), U32.to_nat(n), and9_5(Nat.is_eq(U32.to_nat(um), U32.to_nat(n)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(m)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(n)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(m)), h))
      +f6 = and9_6(Nat.is_eq(U32.to_nat(um), U32.to_nat(n)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(m)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(n)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(m)), h)
      +e7 = nat_eq_sound(List.length(&2, F32, s), U32.to_nat(k), and9_7(Nat.is_eq(U32.to_nat(um), U32.to_nat(n)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(m)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(n)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(m)), h))
      +e8 = nat_eq_sound(List.length(&2, List<&2, F32>, vr), U32.to_nat(k), and9_8(Nat.is_eq(U32.to_nat(um), U32.to_nat(n)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(m)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(n)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(m)), h))
      +f9 = and9_9(Nat.is_eq(U32.to_nat(um), U32.to_nat(n)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(m)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(n)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(m)), h)
      +okvr = rows_ok_eq(vr, U32.to_nat(m), U32.to_nat(vn), Equal.sym(Nat, U32.to_nat(vn), U32.to_nat(m), e4), f9)
      +okur = rows_ok_eq(ur, U32.to_nat(k), U32.to_nat(un), Equal.sym(Nat, U32.to_nat(un), U32.to_nat(k), e2), f6)
      +t1 = L.transpose.rows(vr, U32.to_nat(vn))
      +t2 = L.transpose.rows(ur, U32.to_nat(un))
      svd_intro(U32.to_nat(vn), U32.to_nat(vm), t1, U32.to_nat(k), s, U32.to_nat(un), U32.to_nat(um), t2, U32.to_nat(m), U32.to_nat(n), e4, e3, e2, e1, Equal.trans(Nat, List.length(&2, List<&2, F32>, t1), U32.to_nat(vn), U32.to_nat(m), Laws.transpose_len(vr, U32.to_nat(vn), okvr), e4), rows_ok_eq(t1, List.length(&2, List<&2, F32>, vr), U32.to_nat(k), e8, Laws.transpose_row_len(vr, U32.to_nat(vn), okvr)), e7, Equal.trans(Nat, List.length(&2, List<&2, F32>, t2), U32.to_nat(un), U32.to_nat(k), Laws.transpose_len(ur, U32.to_nat(un), okur), e2), rows_ok_eq(t2, List.length(&2, List<&2, F32>, ur), U32.to_nat(n), e5, Laws.transpose_row_len(ur, U32.to_nat(un), okur)))

def dir_ok(t: Bool, +m: U32, +n: U32, +rows: List<&2, List<&2, F32>>, +hl: {List.length(&2, List<&2, F32>, rows) == U32.to_nat(m) : Nat}, +hr: {L.Mat.rows.ok(rows, U32.to_nat(n)) == True{} : Bool}) -> {Laws.svd_ok(L.svd_thin.dir(t, m, n, rows), m, n) == True{} : Bool}:
  match t:
    case True{}:
      tall_go_ok(rows, m, n, U32.is_eq(n, 0), {==}, hl)
    case False{}:
      +tr = L.transpose.rows(rows, U32.to_nat(n))
      flip_ok(L.svd_tall.go(U32.is_eq(m, 0), tr, n, m), m, n, tall_go_ok(tr, n, m, U32.is_eq(m, 0), {==}, Laws.transpose_len(rows, U32.to_nat(n), hr)))

def Laws.svd_thin_ok(a, h):
  match a:
    case L.Mat{+m, +n, +rows}:
      +hl = nat_eq_sound(List.length(&2, List<&2, F32>, rows), U32.to_nat(m), bool_and_l(Nat.is_eq(List.length(&2, List<&2, F32>, rows), U32.to_nat(m)), L.Mat.rows.ok(rows, U32.to_nat(n)), h))
      +hr = bool_and_r(Nat.is_eq(List.length(&2, List<&2, F32>, rows), U32.to_nat(m)), L.Mat.rows.ok(rows, U32.to_nat(n)), h)
      dir_ok(U32.is_ge(m, n), m, n, rows, hl, hr)

def inv_sigs_len(xs: List<&2, F32>, +cut: F32) -> {List.length(&2, F32, L.pinv.inv_sigs(xs, cut)) == List.length(&2, F32, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      %inv_sigs_len(t, cut) : {1n+List.length(&2, F32, L.pinv.inv_sigs(t, cut)) == 1n+_ : Nat}
      {==}

def diag_mul_len(ds: List<&2, F32>, rows: List<&2, List<&2, F32>>, h: {List.length(&2, F32, ds) == List.length(&2, List<&2, F32>, rows) : Nat}) -> {List.length(&2, List<&2, F32>, L.diag_mul.rows(ds, rows)) == List.length(&2, List<&2, F32>, rows) : Nat}:
  match ds rows:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{r, rt}:
      Empty.absurd({0n == 1n+List.length(&2, List<&2, F32>, rt) : Nat}, zero_ne_succ(List.length(&2, List<&2, F32>, rt), h))
    case Con{d, dt} Nil{}:
      Empty.absurd({0n == 0n : Nat}, succ_ne_zero(List.length(&2, F32, dt), h))
    case Con{d, +dt} Con{r, +rt}:
      %diag_mul_len(dt, rt, nat_pred_eq(List.length(&2, F32, dt), List.length(&2, List<&2, F32>, rt), h)) : {1n+List.length(&2, List<&2, F32>, L.diag_mul.rows(dt, rt)) == 1n+_ : Nat}
      {==}

def diag_mul_ok(ds: List<&2, F32>, rows: List<&2, List<&2, F32>>, +n: Nat, +h: {L.Mat.rows.ok(rows, n) == True{} : Bool}) -> {L.Mat.rows.ok(L.diag_mul.rows(ds, rows), n) == True{} : Bool}:
  match ds rows:
    case Nil{} _:
      {==}
    case Con{d, dt} Nil{}:
      {==}
    case Con{+d, dt} Con{+r, +rt}:
      +hr = bool_and_l(Nat.is_eq(List.length(&2, F32, r), n), L.Mat.rows.ok(rt, n), h)
      +ht = bool_and_r(Nat.is_eq(List.length(&2, F32, r), n), L.Mat.rows.ok(rt, n), h)
      %Equal.sym(Nat, List.length(&2, F32, L.vscale.go(d, r)), List.length(&2, F32, r), vscale_len(d, r)) : {Bool.and(Nat.is_eq(_, n), L.Mat.rows.ok(L.diag_mul.rows(dt, rt), n)) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(List.length(&2, F32, r), n), True{}, hr) : {Bool.and(_, L.Mat.rows.ok(L.diag_mul.rows(dt, rt), n)) == True{} : Bool}
      diag_mul_ok(dt, rt, n, ht)

def pinv_from_ok(sv: L.SVD, +m: U32, +n: U32, +tol: F32, +h: {Laws.svd_ok(sv, m, n) == True{} : Bool}) -> {L.Mat.ok(L.pinv.from_svd(sv, m, n, tol)) == True{} : Bool}:
  match sv:
    case L.SVD{L.Mat{+um, +un, +ur}, L.Vec{+k, +s}, L.Mat{+vm, +vn, +vr}}:
      +e5 = nat_eq_sound(List.length(&2, List<&2, F32>, ur), U32.to_nat(m), and9_5(Nat.is_eq(U32.to_nat(um), U32.to_nat(m)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(n)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(m)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(n)), h))
      +f6 = and9_6(Nat.is_eq(U32.to_nat(um), U32.to_nat(m)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(n)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(m)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(n)), h)
      +e7 = nat_eq_sound(List.length(&2, F32, s), U32.to_nat(k), and9_7(Nat.is_eq(U32.to_nat(um), U32.to_nat(m)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(n)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(m)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(n)), h))
      +e8 = nat_eq_sound(List.length(&2, List<&2, F32>, vr), U32.to_nat(k), and9_8(Nat.is_eq(U32.to_nat(um), U32.to_nat(m)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(n)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(m)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(n)), h))
      +f9 = and9_9(Nat.is_eq(U32.to_nat(um), U32.to_nat(m)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(n)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(m)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(n)), h)
      +cut = (F32.max(0.0, tol) * L.pinv.max_sig(s) : F32)
      +sinv = L.pinv.inv_sigs(s, cut)
      +vrows = L.transpose.rows(vr, U32.to_nat(n))
      +utrows = L.transpose.rows(ur, U32.to_nat(k))
      +sut_rows = L.diag_mul.rows(sinv, utrows)
      +sut_cols = L.transpose.rows(sut_rows, U32.to_nat(m))
      +hut_len = Laws.transpose_len(ur, U32.to_nat(k), f6)
      +hut_ok = rows_ok_eq(utrows, List.length(&2, List<&2, F32>, ur), U32.to_nat(m), e5, Laws.transpose_row_len(ur, U32.to_nat(k), f6))
      +hsinv = Equal.trans(Nat, List.length(&2, F32, sinv), List.length(&2, F32, s), U32.to_nat(k), inv_sigs_len(s, cut), e7)
      +hsut_ok = diag_mul_ok(sinv, utrows, U32.to_nat(m), hut_ok)
      +hcols = Laws.transpose_len(sut_rows, U32.to_nat(m), hsut_ok)
      +eps = Equal.sym(List<&2, List<&2, F32>>, L.pmap(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, vrows, n, sut_cols), L.pseq(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, vrows, sut_cols), Laws.pmap_seq(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, vrows, n, sut_cols))
      %eps : {L.Mat.ok(L.Mat{n, m, _}) == True{} : Bool}
      mat_ok_intro(n, m, L.pseq(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, vrows, sut_cols), Equal.trans(Nat, List.length(&2, List<&2, F32>, L.pseq(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, vrows, sut_cols)), List.length(&2, List<&2, F32>, vrows), U32.to_nat(n), pseq_len(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, vrows, sut_cols), Laws.transpose_len(vr, U32.to_nat(n), f9)), mm_rows_ok(vrows, sut_cols, U32.to_nat(m), hcols))

def Laws.pinv_ok(a, tol, h):
  match a:
    case L.Mat{+m, +n, +rows}:
      pinv_from_ok(L.svd_thin(L.Mat{m, n, rows}), m, n, tol, Laws.svd_thin_ok(L.Mat{m, n, rows}, h))

def mshape_eq(+x: L.Mat, +p: Nat, +p2: Nat, +q: Nat, +q2: Nat, ep: {p == p2 : Nat}, eq: {q == q2 : Nat}, h: {Laws.mshape(x, p, q) == True{} : Bool}) -> {Laws.mshape(x, p2, q2) == True{} : Bool}:
  %ep : {Laws.mshape(x, _, q2) == True{} : Bool}
  %eq : {Laws.mshape(x, p, _) == True{} : Bool}
  h

def mm_some(e: Bool, +ma: U32, +nb: U32, +ra: List<&2, List<&2, F32>>, +rb: List<&2, List<&2, F32>>, +x: L.Mat, hp: {L.matmul.chk(e, ma, nb, ra, rb) == Some{x} : Maybe<&2, L.Mat>}, +hl: {List.length(&2, List<&2, F32>, ra) == U32.to_nat(ma) : Nat}, +hb: {L.Mat.rows.ok(rb, U32.to_nat(nb)) == True{} : Bool}) -> {Laws.mshape(x, U32.to_nat(ma), U32.to_nat(nb)) == True{} : Bool}:
  match e:
    case False{}:
      Empty.absurd({Laws.mshape(x, U32.to_nat(ma), U32.to_nat(nb)) == True{} : Bool}, none_ne_some(x, hp))
    case True{}:
      +bcols = L.transpose.rows(rb, U32.to_nat(nb))
      +rows = L.pseq(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, ra, bcols)
      %un_some_mat(L.Mat{ma, nb, L.pmap(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, ra, ma, bcols)}, x, hp) : {Laws.mshape(_, U32.to_nat(ma), U32.to_nat(nb)) == True{} : Bool}
      %Equal.sym(List<&2, List<&2, F32>>, L.pmap(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, ra, ma, bcols), L.pseq(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, ra, bcols), Laws.pmap_seq(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, ra, ma, bcols)) : {Laws.mshape(L.Mat{ma, nb, _}, U32.to_nat(ma), U32.to_nat(nb)) == True{} : Bool}
      +hok = mat_ok_intro(ma, nb, rows, Equal.trans(Nat, List.length(&2, List<&2, F32>, rows), List.length(&2, List<&2, F32>, ra), U32.to_nat(ma), pseq_len(~List<&2, F32>, ~List<&2, F32>, ~List<&2, List<&2, F32>>, ~L.matmul.row, ra, bcols), hl), mm_rows_ok(ra, bcols, U32.to_nat(nb), Laws.transpose_len(rb, U32.to_nat(nb), hb)))
      and2(L.Mat.ok(L.Mat{ma, nb, rows}), Bool.and(Nat.is_eq(U32.to_nat(ma), U32.to_nat(ma)), Nat.is_eq(U32.to_nat(nb), U32.to_nat(nb))), hok, and2(Nat.is_eq(U32.to_nat(ma), U32.to_nat(ma)), Nat.is_eq(U32.to_nat(nb), U32.to_nat(nb)), nat_eq_refl(U32.to_nat(ma)), nat_eq_refl(U32.to_nat(nb))))

def proc_from(sv: L.SVD, +kk: U32, +x: L.Mat, +hs: {Laws.svd_ok(sv, kk, kk) == True{} : Bool}, hp: {L.procrustes.from_svd(sv) == Some{x} : Maybe<&2, L.Mat>}) -> {Laws.mshape(x, U32.to_nat(kk), U32.to_nat(kk)) == True{} : Bool}:
  match sv:
    case L.SVD{L.Mat{+um, +un, +ur}, L.Vec{+k, +s}, L.Mat{+vm, +vn, +vr}}:
      +e1 = nat_eq_sound(U32.to_nat(um), U32.to_nat(kk), and9_1(Nat.is_eq(U32.to_nat(um), U32.to_nat(kk)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(kk)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(kk)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(kk)), hs))
      +e2 = nat_eq_sound(U32.to_nat(un), U32.to_nat(k), and9_2(Nat.is_eq(U32.to_nat(um), U32.to_nat(kk)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(kk)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(kk)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(kk)), hs))
      +e4 = nat_eq_sound(U32.to_nat(vn), U32.to_nat(kk), and9_4(Nat.is_eq(U32.to_nat(um), U32.to_nat(kk)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(kk)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(kk)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(kk)), hs))
      +e5 = nat_eq_sound(List.length(&2, List<&2, F32>, ur), U32.to_nat(kk), and9_5(Nat.is_eq(U32.to_nat(um), U32.to_nat(kk)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(kk)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(kk)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(kk)), hs))
      +f6 = and9_6(Nat.is_eq(U32.to_nat(um), U32.to_nat(kk)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(kk)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(kk)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(kk)), hs)
      +f9 = and9_9(Nat.is_eq(U32.to_nat(um), U32.to_nat(kk)), Nat.is_eq(U32.to_nat(un), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vm), U32.to_nat(k)), Nat.is_eq(U32.to_nat(vn), U32.to_nat(kk)), Nat.is_eq(List.length(&2, List<&2, F32>, ur), U32.to_nat(kk)), L.Mat.rows.ok(ur, U32.to_nat(k)), Nat.is_eq(List.length(&2, F32, s), U32.to_nat(k)), Nat.is_eq(List.length(&2, List<&2, F32>, vr), U32.to_nat(k)), L.Mat.rows.ok(vr, U32.to_nat(kk)), hs)
      +okvr = rows_ok_eq(vr, U32.to_nat(kk), U32.to_nat(vn), Equal.sym(Nat, U32.to_nat(vn), U32.to_nat(kk), e4), f9)
      +okur = rows_ok_eq(ur, U32.to_nat(k), U32.to_nat(un), Equal.sym(Nat, U32.to_nat(un), U32.to_nat(k), e2), f6)
      +t1 = L.transpose.rows(vr, U32.to_nat(vn))
      +t2 = L.transpose.rows(ur, U32.to_nat(un))
      +hb = rows_ok_eq(t2, List.length(&2, List<&2, F32>, ur), U32.to_nat(um), Equal.trans(Nat, List.length(&2, List<&2, F32>, ur), U32.to_nat(kk), U32.to_nat(um), e5, Equal.sym(Nat, U32.to_nat(um), U32.to_nat(kk), e1)), Laws.transpose_row_len(ur, U32.to_nat(un), okur))
      mshape_eq(x, U32.to_nat(vn), U32.to_nat(kk), U32.to_nat(um), U32.to_nat(kk), e4, e1, mm_some(U32.is_eq(vm, un), vn, um, t1, t2, x, hp, Laws.transpose_len(vr, U32.to_nat(vn), okvr), hb))

def proc_chk(ok: Bool, +ma: U32, +na: U32, +ar: List<&2, List<&2, F32>>, +mb: U32, +nb: U32, +br: List<&2, List<&2, F32>>, +x: L.Mat, hp: {L.procrustes.chk(ok, L.Mat{ma, na, ar}, L.Mat{mb, nb, br}) == Some{x} : Maybe<&2, L.Mat>}) -> {Laws.mshape(x, U32.to_nat(na), U32.to_nat(na)) == True{} : Bool}:
  match ok:
    case False{}:
      Empty.absurd({Laws.mshape(x, U32.to_nat(na), U32.to_nat(na)) == True{} : Bool}, none_ne_some(x, hp))
    case True{}:
      +atb = {L.Mat{na, na, L.arr_colmajor_rows(L.wgram_arr.fin(L.atb_arr.i(U32.to_nat(na), L.WGramSt{L.mat_to_colmajor(ar, ma, na), L.mat_to_colmajor(br, ma, na), Array.new(F32, L.arr_depth((na * na : U32)), 0.0)}, 0, ma, U32.to_nat(ma), na)), na, na)} : L.Mat}
      proc_from(L.svd_thin(atb), na, x, Laws.svd_thin_ok(atb, cm_rows_shape(L.wgram_arr.fin(L.atb_arr.i(U32.to_nat(na), L.WGramSt{L.mat_to_colmajor(ar, ma, na), L.mat_to_colmajor(br, ma, na), Array.new(F32, L.arr_depth((na * na : U32)), 0.0)}, 0, ma, U32.to_nat(ma), na)), na, na)), hp)

def Laws.procrustes_shape(a, b, x, hp):
  match a b:
    case L.Mat{+ma, +na, +ar} L.Mat{+mb, +nb, +br}:
      proc_chk(Bool.and(U32.is_eq(ma, mb), U32.is_eq(na, nb)), ma, na, ar, mb, nb, br, x, hp)
