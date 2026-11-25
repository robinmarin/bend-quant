# Proofs of every law in LAWS.bend (41 laws total).
# Checked with `bend PROOF.bend --verdict` (zero @unsafe, zero IO).
import Base
import bend-quant-linalg@0.1.1.0/linalg.bend as L
import bend-quant-portfolio@0.1.1.0/portfolio.bend as P
import ./cov.bend as C
import ./risk.bend as R
import ./LAWS.bend as Laws

# ---------------------------------------------------------------- Bool & Nat helpers

def is_false_t(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def false_ne_true(h: {False{} == True{} : Bool}) -> Empty:
  %h : is_false_t(_)
  Unit{}

def bool_and_false_r(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def bool_and_false_l(+a: Bool, b: Bool, h: {a == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, h) : {Bool.and(_, b) == False{} : Bool}
  {==}

def bool_and_false_mid(a: Bool, +b: Bool, c: Bool, h: {b == False{} : Bool}) -> {Bool.and(a, Bool.and(b, c)) == False{} : Bool}:
  match a:
    case True{}:
      %Equal.sym(Bool, b, False{}, h) : {Bool.and(_, c) == False{} : Bool}
      {==}
    case False{}:
      {==}

def bool_and_l(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def bool_and_r(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_ne_true(h))

def nat_eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat_eq_refl(p)

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

def nat_pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def zero_ne_succ(n: Nat, h: {0n == 1n+n : Nat}) -> Empty:
  false_ne_true(Equal.sym(Bool, True{}, False{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), 0n, 1n+n, h)))

def succ_ne_zero(n: Nat, h: {1n+n == 0n : Nat}) -> Empty:
  false_ne_true(Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), 1n+n, 0n, h))

# ---------------------------------------------------------------- 1. Exact Structural Symmetry Proofs

def prepend_col_len(col: List<&2, F32>, rows: List<&2, List<&2, F32>>, h: {List.length(&2, F32, col) == List.length(&2, List<&2, F32>, rows) : Nat}) -> {List.length(&2, List<&2, F32>, C.prepend_col(col, rows)) == List.length(&2, List<&2, F32>, rows) : Nat}:
  match col rows:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{r, rt}:
      Empty.absurd({0n == 1n+List.length(&2, List<&2, F32>, rt) : Nat}, zero_ne_succ(List.length(&2, List<&2, F32>, rt), h))
    case Con{c, ct} Nil{}:
      Empty.absurd({0n == 0n : Nat}, succ_ne_zero(List.length(&2, F32, ct), h))
    case Con{c, ct} Con{r, rt}:
      +h1 = Equal.cong(Nat, Nat, z => nat_pred(z), 1n+List.length(&2, F32, ct), 1n+List.length(&2, List<&2, F32>, rt), h)
      %prepend_col_len(ct, rt, h1) : {1n+List.length(&2, List<&2, F32>, C.prepend_col(ct, rt)) == 1n+_ : Nat}
      {==}

def mirror_upper_len(up: List<&2, List<&2, F32>>, n: Nat, +h: {Laws.upper_ok(up, n) == True{} : Bool}) -> {List.length(&2, List<&2, F32>, C.mirror_upper(up)) == n : Nat}:
  match up n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      Empty.absurd({0n == 1n+p : Nat}, false_ne_true(h))
    case Con{r, t} 0n:
      Empty.absurd({List.length(&2, List<&2, F32>, C.mirror_upper(r <> t)) == 0n : Nat}, false_ne_true(h))
    case Con{Nil{}, sub} 1n+(+p):
      Empty.absurd({1n+List.length(&2, List<&2, F32>, C.mirror_upper(sub)) == 1n+p : Nat}, false_ne_true(bool_and_l(Nat.is_eq(0n, 1n+p), Laws.upper_ok(sub, p), h)))
    case Con{Con{d, +off}, +sub} 1n+(+p):
      +h1 = bool_and_l(Nat.is_eq(1n+List.length(&2, F32, off), 1n+p), Laws.upper_ok(sub, p), h)
      +h2 = bool_and_r(Nat.is_eq(1n+List.length(&2, F32, off), 1n+p), Laws.upper_ok(sub, p), h)
      +hoff = nat_eq_sound(List.length(&2, F32, off), p, h1)
      +hsub = mirror_upper_len(sub, p, h2)
      +heq = Equal.trans(Nat, List.length(&2, F32, off), p, List.length(&2, List<&2, F32>, C.mirror_upper(sub)), hoff, Equal.sym(Nat, List.length(&2, List<&2, F32>, C.mirror_upper(sub)), p, hsub))
      +hp = prepend_col_len(off, C.mirror_upper(sub), heq)
      +hfin = Equal.trans(Nat, List.length(&2, List<&2, F32>, C.prepend_col(off, C.mirror_upper(sub))), List.length(&2, List<&2, F32>, C.mirror_upper(sub)), p, hp, hsub)
      %hfin : {1n+List.length(&2, List<&2, F32>, C.prepend_col(off, C.mirror_upper(sub))) == 1n+_ : Nat}
      {==}

def prepend_col_get_zero(col: List<&2, F32>, rows: List<&2, List<&2, F32>>, i: Nat, h: {List.length(&2, F32, col) == List.length(&2, List<&2, F32>, rows) : Nat}) -> {L.mat_get(C.prepend_col(col, rows), i, 0n) == List.get(&2, F32, col, i) : Maybe<&2, F32>}:
  match col rows i:
    case Nil{} Nil{} 0n:
      {==}
    case Nil{} Nil{} 1n+k:
      {==}
    case Nil{} Con{r, rt} _:
      Empty.absurd({None{} == List.get(&2, F32, Nil{}, i) : Maybe<&2, F32>}, zero_ne_succ(List.length(&2, List<&2, F32>, rt), h))
    case Con{c, ct} Nil{} _:
      Empty.absurd({None{} == List.get(&2, F32, c <> ct, i) : Maybe<&2, F32>}, succ_ne_zero(List.length(&2, F32, ct), h))
    case Con{c, ct} Con{r, rt} 0n:
      {==}
    case Con{c, ct} Con{r, rt} 1n+k:
      +h1 = Equal.cong(Nat, Nat, z => nat_pred(z), 1n+List.length(&2, F32, ct), 1n+List.length(&2, List<&2, F32>, rt), h)
      prepend_col_get_zero(ct, rt, k, h1)

def prepend_col_get_succ(col: List<&2, F32>, rows: List<&2, List<&2, F32>>, i: Nat, +j: Nat, h: {List.length(&2, F32, col) == List.length(&2, List<&2, F32>, rows) : Nat}) -> {L.mat_get(C.prepend_col(col, rows), i, 1n+j) == L.mat_get(rows, i, j) : Maybe<&2, F32>}:
  match col rows i:
    case Nil{} Nil{} 0n:
      {==}
    case Nil{} Nil{} 1n+k:
      {==}
    case Nil{} Con{r, rt} _:
      Empty.absurd({None{} == L.mat_get(r <> rt, i, j) : Maybe<&2, F32>}, zero_ne_succ(List.length(&2, List<&2, F32>, rt), h))
    case Con{c, ct} Nil{} _:
      Empty.absurd({None{} == L.mat_get(Nil{}, i, j) : Maybe<&2, F32>}, succ_ne_zero(List.length(&2, F32, ct), h))
    case Con{c, ct} Con{r, rt} 0n:
      {==}
    case Con{c, ct} Con{r, rt} 1n+k:
      +h1 = Equal.cong(Nat, Nat, z => nat_pred(z), 1n+List.length(&2, F32, ct), 1n+List.length(&2, List<&2, F32>, rt), h)
      prepend_col_get_succ(ct, rt, k, j, h1)

def mirror_upper_eq(d: F32, +off: List<&2, F32>, +sub: List<&2, List<&2, F32>>, +p: Nat, +h: {Laws.upper_ok((d <> off) <> sub, 1n+p) == True{} : Bool}) -> {List.length(&2, F32, off) == List.length(&2, List<&2, F32>, C.mirror_upper(sub)) : Nat}:
  +h1 = bool_and_l(Nat.is_eq(1n+List.length(&2, F32, off), 1n+p), Laws.upper_ok(sub, p), h)
  +h2 = bool_and_r(Nat.is_eq(1n+List.length(&2, F32, off), 1n+p), Laws.upper_ok(sub, p), h)
  +hoff = nat_eq_sound(List.length(&2, F32, off), p, h1)
  +hsub = mirror_upper_len(sub, p, h2)
  Equal.trans(Nat, List.length(&2, F32, off), p, List.length(&2, List<&2, F32>, C.mirror_upper(sub)), hoff, Equal.sym(Nat, List.length(&2, List<&2, F32>, C.mirror_upper(sub)), p, hsub))

def Laws.mirror_upper_sym(up, n, i, j, h):
  match up n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      Empty.absurd({None{} == None{} : Maybe<&2, F32>}, false_ne_true(h))
    case Con{r, t} 0n:
      Empty.absurd({L.mat_get(C.mirror_upper(r <> t), i, j) == L.mat_get(C.mirror_upper(r <> t), j, i) : Maybe<&2, F32>}, false_ne_true(h))
    case Con{Nil{}, sub} 1n+(+p):
      Empty.absurd({L.mat_get(Nil{} <> C.mirror_upper(sub), i, j) == L.mat_get(Nil{} <> C.mirror_upper(sub), j, i) : Maybe<&2, F32>}, false_ne_true(bool_and_l(Nat.is_eq(0n, 1n+p), Laws.upper_ok(sub, p), h)))
    case Con{Con{+d, +off}, +sub} 1n+(+p):
      match i j:
        case 0n 0n:
          {==}
        case 0n 1n+(+q):
          +eq = mirror_upper_eq(d, off, sub, p, h)
          Equal.sym(Maybe<&2, F32>, L.mat_get(C.prepend_col(off, C.mirror_upper(sub)), q, 0n), List.get(&2, F32, off, q), prepend_col_get_zero(off, C.mirror_upper(sub), q, eq))
        case 1n+(+r) 0n:
          +eq = mirror_upper_eq(d, off, sub, p, h)
          prepend_col_get_zero(off, C.mirror_upper(sub), r, eq)
        case 1n+(+r) 1n+(+q):
          +eq = mirror_upper_eq(d, off, sub, p, h)
          +h2 = bool_and_r(Nat.is_eq(1n+List.length(&2, F32, off), 1n+p), Laws.upper_ok(sub, p), h)
          %Equal.sym(Maybe<&2, F32>, L.mat_get(C.prepend_col(off, C.mirror_upper(sub)), r, 1n+q), L.mat_get(C.mirror_upper(sub), r, q), prepend_col_get_succ(off, C.mirror_upper(sub), r, q, eq)) : {_ == L.mat_get(C.prepend_col(off, C.mirror_upper(sub)), q, 1n+r) : Maybe<&2, F32>}
          %Equal.sym(Maybe<&2, F32>, L.mat_get(C.prepend_col(off, C.mirror_upper(sub)), q, 1n+r), L.mat_get(C.mirror_upper(sub), q, r), prepend_col_get_succ(off, C.mirror_upper(sub), q, r, eq)) : {L.mat_get(C.mirror_upper(sub), r, q) == _ : Maybe<&2, F32>}
          Laws.mirror_upper_sym(sub, p, r, q, h2)

# Linear lexicographic proof that mirror_upper(sym_tri.go(...)) is bitwise symmetric!
def sym_tri_lex(
  rem_out: Nat,
  rem_in: Nat,
  p_cell: Array<F32> & F32,
  +row: List<&2, F32>,
  +upper: List<&2, List<&2, F32>>,
  +s: Nat,
  +i: U32,
  +j: U32,
  +n: U32,
  +ii: Nat,
  +jj: Nat,
  hlen: {Nat.add(rem_in, 1n+List.length(&2, F32, row)) == 1n+s : Nat},
  hup: {Laws.upper_ok(upper, s) == True{} : Bool}
) -> {L.mat_get(C.mirror_upper(C.sym_tri.go(rem_out, C.sym_tri.push(C.sym_row.go(rem_in, C.sym_row.push(p_cell, row), i, j, n), upper), 1n+(1n+s), (i - 1 : U32), n)), ii, jj) == L.mat_get(C.mirror_upper(C.sym_tri.go(rem_out, C.sym_tri.push(C.sym_row.go(rem_in, C.sym_row.push(p_cell, row), i, j, n), upper), 1n+(1n+s), (i - 1 : U32), n)), jj, ii) : Maybe<&2, F32>}:
  match rem_out rem_in:
    case 0n 0n:
      (_, v) = p_cell
      +heq = Equal.trans(Bool, Nat.is_eq(1n+List.length(&2, F32, row), 1n+s), Nat.is_eq(1n+s, 1n+s), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n+s), 1n+List.length(&2, F32, row), 1n+s, hlen), nat_eq_refl(1n+s))
      +hup1 = Equal.trans(Bool, Bool.and(Nat.is_eq(1n+List.length(&2, F32, row), 1n+s), Laws.upper_ok(upper, s)), Bool.and(True{}, Laws.upper_ok(upper, s)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Laws.upper_ok(upper, s)), Nat.is_eq(1n+List.length(&2, F32, row), 1n+s), True{}, heq), hup)
      Laws.mirror_upper_sym((v <> row) <> upper, 1n+s, ii, jj, hup1)
    case 1n+(+p) 0n:
      (a, v) = p_cell
      +heq = Equal.trans(Bool, Nat.is_eq(1n+List.length(&2, F32, row), 1n+s), Nat.is_eq(1n+s, 1n+s), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n+s), 1n+List.length(&2, F32, row), 1n+s, hlen), nat_eq_refl(1n+s))
      +hup1 = Equal.trans(Bool, Bool.and(Nat.is_eq(1n+List.length(&2, F32, row), 1n+s), Laws.upper_ok(upper, s)), Bool.and(True{}, Laws.upper_ok(upper, s)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Laws.upper_ok(upper, s)), Nat.is_eq(1n+List.length(&2, F32, row), 1n+s), True{}, heq), hup)
      +h_next_len = Equal.trans(Nat, Nat.add(1n+s, 1n), 1n+Nat.add(1n+s, 0n), 1n+(1n+s), add_succ_r(1n+s, 0n), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(1n+s, 0n), 1n+s, add_zero_r(1n+s)))
      +ni = (i - 1 : U32)
      +nj = (n - 1 : U32)
      sym_tri_lex(p, 1n+s, C.sym_cell(a, ((ni * n) + nj : U32), ((nj * n) + ni : U32)), Nil{}, (v <> row) <> upper, 1n+s, ni, (nj - 1 : U32), n, ii, jj, h_next_len, hup1)
    case _ 1n+(+q):
      (a, v) = p_cell
      +hlen1 = Equal.trans(Nat, Nat.add(q, 1n+(1n+List.length(&2, F32, row))), 1n+Nat.add(q, 1n+List.length(&2, F32, row)), 1n+s, add_succ_r(q, 1n+List.length(&2, F32, row)), hlen)
      sym_tri_lex(rem_out, q, C.sym_cell(a, ((i * n) + j : U32), ((j * n) + i : U32)), v <> row, upper, s, i, (j - 1 : U32), n, ii, jj, hlen1, hup)

def sym_tri_sym_start(nn: Nat, a: Array<F32>, +i: U32, +n: U32, +ii: Nat, +jj: Nat) -> {L.mat_get(C.mirror_upper(C.sym_tri.go(nn, C.SymTri{a, Nil{}}, 1n, i, n)), ii, jj) == L.mat_get(C.mirror_upper(C.sym_tri.go(nn, C.SymTri{a, Nil{}}, 1n, i, n)), jj, ii) : Maybe<&2, F32>}:
  match nn:
    case 0n:
      {==}
    case 1n+p:
      +nj = (n - 1 : U32)
      sym_tri_lex(p, 0n, C.sym_cell(a, ((i * n) + nj : U32), ((nj * n) + i : U32)), Nil{}, Nil{}, 0n, i, (nj - 1 : U32), n, ii, jj, {==}, {==})

def upper_sym_chk_sym(is_z: Bool, a: Array<F32>, +n: U32, +i: Nat, +j: Nat) -> {L.mat_get(C.mirror_upper(C.upper_sym_from_arr.chk(is_z, a, n)), i, j) == L.mat_get(C.mirror_upper(C.upper_sym_from_arr.chk(is_z, a, n)), j, i) : Maybe<&2, F32>}:
  match is_z:
    case True{}:
      {==}
    case False{}:
      sym_tri_sym_start(U32.to_nat(n), a, (n - 1 : U32), n, i, j)

def symmetrize_raw_sym(+n: U32, rows: List<&2, List<&2, F32>>, +i: Nat, +j: Nat) -> {L.Mat.get(C.symmetrize_raw(n, rows), i, j) == L.Mat.get(C.symmetrize_raw(n, rows), j, i) : Maybe<&2, F32>}:
  upper_sym_chk_sym(U32.is_eq(n, 0), C.mat_to_arr(rows, n, n), n, i, j)

# Linear lexicographic proof that mirror_upper(hac_tri.i(...)) is bitwise symmetric!
def hac_tri_lex(
  rem_out: Nat,
  rem_in: Nat,
  st1: C.LagAcc,
  +row: List<&2, F32>,
  +upper: List<&2, List<&2, F32>>,
  +s: Nat,
  +i: U32,
  +j: U32,
  +t: U32,
  +k: U32,
  +le: U32,
  +lm: U32,
  +nw: Bool,
  +ii: Nat,
  +jj: Nat,
  hlen: {Nat.add(rem_in, 1n+List.length(&2, F32, row)) == 1n+s : Nat},
  hup: {Laws.upper_ok(upper, s) == True{} : Bool}
) -> {L.mat_get(C.mirror_upper(C.hac_tri.i(rem_out, C.hac_tri.push(C.hac_row.j(rem_in, C.hac_row.push(st1, row), i, j, t, k, le, lm, nw), upper), 1n+(1n+s), (i - 1 : U32), t, k, le, lm, nw)), ii, jj) == L.mat_get(C.mirror_upper(C.hac_tri.i(rem_out, C.hac_tri.push(C.hac_row.j(rem_in, C.hac_row.push(st1, row), i, j, t, k, le, lm, nw), upper), 1n+(1n+s), (i - 1 : U32), t, k, le, lm, nw)), jj, ii) : Maybe<&2, F32>}:
  match rem_out rem_in:
    case 0n 0n:
      C.LagAcc{_, _, v} = st1
      +heq = Equal.trans(Bool, Nat.is_eq(1n+List.length(&2, F32, row), 1n+s), Nat.is_eq(1n+s, 1n+s), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n+s), 1n+List.length(&2, F32, row), 1n+s, hlen), nat_eq_refl(1n+s))
      +hup1 = Equal.trans(Bool, Bool.and(Nat.is_eq(1n+List.length(&2, F32, row), 1n+s), Laws.upper_ok(upper, s)), Bool.and(True{}, Laws.upper_ok(upper, s)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Laws.upper_ok(upper, s)), Nat.is_eq(1n+List.length(&2, F32, row), 1n+s), True{}, heq), hup)
      Laws.mirror_upper_sym((v <> row) <> upper, 1n+s, ii, jj, hup1)
    case 1n+(+p) 0n:
      C.LagAcc{x, w, v} = st1
      +heq = Equal.trans(Bool, Nat.is_eq(1n+List.length(&2, F32, row), 1n+s), Nat.is_eq(1n+s, 1n+s), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n+s), 1n+List.length(&2, F32, row), 1n+s, hlen), nat_eq_refl(1n+s))
      +hup1 = Equal.trans(Bool, Bool.and(Nat.is_eq(1n+List.length(&2, F32, row), 1n+s), Laws.upper_ok(upper, s)), Bool.and(True{}, Laws.upper_ok(upper, s)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Laws.upper_ok(upper, s)), Nat.is_eq(1n+List.length(&2, F32, row), 1n+s), True{}, heq), hup)
      +h_next_len = Equal.trans(Nat, Nat.add(1n+s, 1n), 1n+Nat.add(1n+s, 0n), 1n+(1n+s), add_succ_r(1n+s, 0n), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(1n+s, 0n), 1n+s, add_zero_r(1n+s)))
      +ni = (i - 1 : U32)
      +nj = (k - 1 : U32)
      st_next = C.hac_cell.lags(U32.to_nat(le), C.lag0_dot.go(U32.to_nat(t), C.LagAcc{x, w, 0.0}, 0, ni, nj, k), 1, lm, nw, t, ni, nj, k)
      hac_tri_lex(p, 1n+s, st_next, Nil{}, (v <> row) <> upper, 1n+s, ni, (nj - 1 : U32), t, k, le, lm, nw, ii, jj, h_next_len, hup1)
    case _ 1n+(+q):
      C.LagAcc{x, w, v} = st1
      +hlen1 = Equal.trans(Nat, Nat.add(q, 1n+(1n+List.length(&2, F32, row))), 1n+Nat.add(q, 1n+List.length(&2, F32, row)), 1n+s, add_succ_r(q, 1n+List.length(&2, F32, row)), hlen)
      st_next = C.hac_cell.lags(U32.to_nat(le), C.lag0_dot.go(U32.to_nat(t), C.LagAcc{x, w, 0.0}, 0, i, j, k), 1, lm, nw, t, i, j, k)
      hac_tri_lex(rem_out, q, st_next, v <> row, upper, s, i, (j - 1 : U32), t, k, le, lm, nw, ii, jj, hlen1, hup)

def hac_tri_sym_start(kn: Nat, x: Array<F32>, w: Array<F32>, +i: U32, +t: U32, +k: U32, +le: U32, +lm: U32, +nw: Bool, +ii: Nat, +jj: Nat) -> {L.mat_get(C.mirror_upper(C.hac_tri.i(kn, C.HacTri{x, w, Nil{}}, 1n, i, t, k, le, lm, nw)), ii, jj) == L.mat_get(C.mirror_upper(C.hac_tri.i(kn, C.HacTri{x, w, Nil{}}, 1n, i, t, k, le, lm, nw)), jj, ii) : Maybe<&2, F32>}:
  match kn:
    case 0n:
      {==}
    case 1n+p:
      +nj = (k - 1 : U32)
      st0 = C.hac_cell.lags(U32.to_nat(le), C.lag0_dot.go(U32.to_nat(t), C.LagAcc{x, w, 0.0}, 0, i, nj, k), 1, lm, nw, t, i, nj, k)
      hac_tri_lex(p, 0n, st0, Nil{}, Nil{}, 0n, i, (nj - 1 : U32), t, k, le, lm, nw, ii, jj, {==}, {==})

# Now all 10 covariance symmetry laws follow in a few lines each!

def Laws.symmetrize_nonsquare(m, n, rows, h):
  %Equal.sym(Bool, U32.is_eq(m, n), False{}, h) : {C.symmetrize.chk(_, n, rows) == None{} : Maybe<&2, L.Mat>}
  {==}

def symmetrize_chk_sym(ok: Bool, +n: U32, rows: List<&2, List<&2, F32>>, +i: Nat, +j: Nat) -> {Laws.mm_get(C.symmetrize.chk(ok, n, rows), i, j) == Laws.mm_get(C.symmetrize.chk(ok, n, rows), j, i) : Maybe<&2, F32>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      symmetrize_raw_sym(n, rows, i, j)

def Laws.symmetrize_sym(a, i, j):
  L.Mat{m, +n, rows} = a
  symmetrize_chk_sym(U32.is_eq(m, n), n, rows, i, j)

def sym_scale_fin_sym(m: L.Mat, +i: Nat, +j: Nat) -> {L.Mat.get(C.sym_scale.fin(m), i, j) == L.Mat.get(C.sym_scale.fin(m), j, i) : Maybe<&2, F32>}:
  L.Mat{+n, _, rows} = m
  symmetrize_raw_sym(n, rows, i, j)

def sample_cov_centered_sym(ok: Bool, +t: U32, +k: U32, +rows: List<&2, List<&2, F32>>, +i: Nat, +j: Nat) -> {Laws.mm_get(C.sample_cov.centered(ok, t, k, rows), i, j) == Laws.mm_get(C.sample_cov.centered(ok, t, k, rows), j, i) : Maybe<&2, F32>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      +ws = List.replicate(F32, U32.to_nat(t), (1.0 / U32.to_f32(t) : F32))
      +crows = C.center_rows(rows, ws, k)
      +inv = (1.0 / U32.to_f32((t - 1 : U32)) : F32)
      sym_scale_fin_sym(L.scale(inv, L.gram(L.Mat{t, k, crows})), i, j)

def sample_cov_run_sym(center: Bool, +t: U32, +k: U32, +rows: List<&2, List<&2, F32>>, +i: Nat, +j: Nat) -> {Laws.mm_get(C.sample_cov.run(center, t, k, rows), i, j) == Laws.mm_get(C.sample_cov.run(center, t, k, rows), j, i) : Maybe<&2, F32>}:
  match center:
    case False{}:
      +inv = (1.0 / U32.to_f32(t) : F32)
      sym_scale_fin_sym(L.scale(inv, L.gram(L.Mat{t, k, rows})), i, j)
    case True{}:
      sample_cov_centered_sym(U32.is_gt(t, 1), t, k, rows, i, j)

def sample_cov_chk_sym(ok: Bool, center: Bool, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>, +i: Nat, +j: Nat) -> {Laws.mm_get(C.sample_cov.chk(ok, center, t, k, rows), i, j) == Laws.mm_get(C.sample_cov.chk(ok, center, t, k, rows), j, i) : Maybe<&2, F32>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      sample_cov_run_sym(center, t, k, rows, i, j)

def Laws.sample_cov_sym(x, center, i, j):
  L.Mat{+t, +k, rows} = x
  sample_cov_chk_sym(Bool.and(U32.is_gt(t, 0), U32.is_gt(k, 0)), center, t, k, rows, i, j)

def ewma_wgram_sym(mg: Maybe<&2, L.Mat>, +sc: F32, +i: Nat, +j: Nat) -> {Laws.mm_get(C.ewma_cov.wgram_wrap(mg, sc), i, j) == Laws.mm_get(C.ewma_cov.wgram_wrap(mg, sc), j, i) : Maybe<&2, F32>}:
  match mg:
    case None{}:
      {==}
    case Some{g}:
      sym_scale_fin_sym(L.scale(sc, g), i, j)

def ewma_centered_sym(ok: Bool, +den: F32, +t: U32, +k: U32, +rows: List<&2, List<&2, F32>>, +ws: List<&2, F32>, +i: Nat, +j: Nat) -> {Laws.mm_get(C.ewma_cov.centered(ok, den, t, k, rows, ws), i, j) == Laws.mm_get(C.ewma_cov.centered(ok, den, t, k, rows, ws), j, i) : Maybe<&2, F32>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      +crows = C.center_rows(rows, ws, k)
      ewma_wgram_sym(L.wgram(L.Mat{t, k, crows}, L.Vec{t, ws}), (1.0 / den : F32), i, j)

def ewma_run_sym(center: Bool, +t: U32, +k: U32, +rows: List<&2, List<&2, F32>>, +ws: List<&2, F32>, +i: Nat, +j: Nat) -> {Laws.mm_get(C.ewma_cov.run(center, t, k, rows, ws), i, j) == Laws.mm_get(C.ewma_cov.run(center, t, k, rows, ws), j, i) : Maybe<&2, F32>}:
  match center:
    case False{}:
      ewma_wgram_sym(L.wgram(L.Mat{t, k, rows}, L.Vec{t, ws}), 1.0, i, j)
    case True{}:
      +den = (1.0 - C.list_sum_sq.go(ws, 0.0) : F32)
      ewma_centered_sym(F32.is_gt(den, 1.0e-12), den, t, k, rows, ws, i, j)

def ewma_with_w_sym(mw: Maybe<&2, L.Vec>, center: Bool, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>, +i: Nat, +j: Nat) -> {Laws.mm_get(C.ewma_cov.with_w(mw, center, t, k, rows), i, j) == Laws.mm_get(C.ewma_cov.with_w(mw, center, t, k, rows), j, i) : Maybe<&2, F32>}:
  match mw:
    case None{}:
      {==}
    case Some{L.Vec{_, ws}}:
      ewma_run_sym(center, t, k, rows, ws, i, j)

def ewma_chk_sym(ok: Bool, center: Bool, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>, +hl: F32, +i: Nat, +j: Nat) -> {Laws.mm_get(C.ewma_cov.chk(ok, center, t, k, rows, hl), i, j) == Laws.mm_get(C.ewma_cov.chk(ok, center, t, k, rows, hl), j, i) : Maybe<&2, F32>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      ewma_with_w_sym(C.ewma_weights(t, hl), center, t, k, rows, i, j)

def Laws.ewma_cov_sym(x, hl, center, i, j):
  L.Mat{+t, +k, rows} = x
  ewma_chk_sym(Bool.and(U32.is_gt(t, 0), U32.is_gt(k, 0)), center, t, k, rows, hl, i, j)

def shrink_id_tr_sym(mtr: Maybe<&2, F32>, +n: U32, rows: List<&2, List<&2, F32>>, +rho: F32, +i: Nat, +j: Nat) -> {Laws.mm_get(C.shrink_id.with_tr(mtr, n, rows, rho), i, j) == Laws.mm_get(C.shrink_id.with_tr(mtr, n, rows, rho), j, i) : Maybe<&2, F32>}:
  match mtr:
    case None{}:
      {==}
    case Some{tr}:
      +mu = (tr / U32.to_f32(n) : F32)
      +raw = C.shrink_id.rows(rows, 0n, U32.to_nat(n), (1.0 - rho : F32), (rho * mu : F32))
      symmetrize_raw_sym(n, raw, i, j)

def shrink_id_chk_sym(ok: Bool, +n: U32, +rows: List<&2, List<&2, F32>>, +rho: F32, +i: Nat, +j: Nat) -> {Laws.mm_get(C.shrink_id.chk(ok, n, rows, rho), i, j) == Laws.mm_get(C.shrink_id.chk(ok, n, rows, rho), j, i) : Maybe<&2, F32>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      shrink_id_tr_sym(L.trace(L.Mat{n, n, rows}), n, rows, rho, i, j)

def Laws.shrink_to_identity_sym(cov, rho, i, j):
  L.Mat{m, +n, rows} = cov
  +ok = Bool.and(U32.is_eq(m, n), Bool.and(U32.is_gt(n, 0), Bool.and(F32.is_ge(rho, 0.0), F32.is_le(rho, 1.0))))
  shrink_id_chk_sym(ok, n, rows, rho, i, j)

def lw_with_s_sym(+s_mat: L.Mat, +t: U32, +k: U32, xrows: List<&2, List<&2, F32>>, +i: Nat, +j: Nat) -> {Laws.ms_cov_get(R.wrap_shrink(Some{C.ledoit_wolf.with_s(s_mat, t, k, xrows)}), i, j) == Laws.ms_cov_get(R.wrap_shrink(Some{C.ledoit_wolf.with_s(s_mat, t, k, xrows)}), j, i) : Maybe<&2, F32>}:
  L.Mat{_, _, +srows} = s_mat
  +tf = U32.to_f32(t)
  +kf = U32.to_f32(k)
  +tr = C.maybe_f32(L.trace(s_mat), 0.0)
  +mu = (tr / kf : F32)
  +fr = L.frobenius(s_mat)
  +s_frob_sq = (fr * fr : F32)
  +delta_sq = C.frob_sub_mu_sq(srows, 0n, mu, 0.0)
  +s4 = C.sum_row_norm4.go(xrows, 0.0)
  +beta_bar = C.fmax(0.0, ((s4 - (tf * s_frob_sq)) / (tf * tf) : F32))
  +rho = Bool.pick(F32, F32.is_gt(delta_sq, 1.0e-30), C.fmin(1.0, (beta_bar / delta_sq : F32)), 0.0)
  +raw = C.shrink_id.rows(srows, 0n, U32.to_nat(k), (1.0 - rho : F32), (rho * mu : F32))
  symmetrize_raw_sym(k, raw, i, j)

def lw_run_sym(+t: U32, +k: U32, +xrows: List<&2, List<&2, F32>>, +i: Nat, +j: Nat) -> {Laws.ms_cov_get(R.wrap_shrink(Some{C.ledoit_wolf.run(t, k, xrows)}), i, j) == Laws.ms_cov_get(R.wrap_shrink(Some{C.ledoit_wolf.run(t, k, xrows)}), j, i) : Maybe<&2, F32>}:
  +s_mat = C.sym_scale((1.0 / U32.to_f32(t) : F32), L.gram(L.Mat{t, k, xrows}))
  lw_with_s_sym(s_mat, t, k, xrows, i, j)

def lw_prep_sym(center: Bool, +t: U32, +k: U32, +rows: List<&2, List<&2, F32>>, +i: Nat, +j: Nat) -> {Laws.ms_cov_get(R.wrap_shrink(Some{C.ledoit_wolf.prep(center, t, k, rows)}), i, j) == Laws.ms_cov_get(R.wrap_shrink(Some{C.ledoit_wolf.prep(center, t, k, rows)}), j, i) : Maybe<&2, F32>}:
  match center:
    case True{}:
      +ws = List.replicate(F32, U32.to_nat(t), (1.0 / U32.to_f32(t) : F32))
      lw_run_sym(t, k, C.center_rows(rows, ws, k), i, j)
    case False{}:
      lw_run_sym(t, k, rows, i, j)

def lw_chk_sym(ok: Bool, center: Bool, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>, +i: Nat, +j: Nat) -> {Laws.ms_cov_get(R.wrap_shrink(C.ledoit_wolf.chk(ok, center, t, k, rows)), i, j) == Laws.ms_cov_get(R.wrap_shrink(C.ledoit_wolf.chk(ok, center, t, k, rows)), j, i) : Maybe<&2, F32>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      lw_prep_sym(center, t, k, rows, i, j)

def Laws.ledoit_wolf_sym(x, center, i, j):
  L.Mat{+t, +k, rows} = x
  lw_chk_sym(Bool.and(U32.is_gt(t, 0), U32.is_gt(k, 0)), center, t, k, rows, i, j)

def psd_fin_sym(mg: Maybe<&2, L.Mat>, +i: Nat, +j: Nat) -> {Laws.mm_get(C.psd_project.fin(mg), i, j) == Laws.mm_get(C.psd_project.fin(mg), j, i) : Maybe<&2, F32>}:
  match mg:
    case None{}:
      {==}
    case Some{L.Mat{+n, _, rows}}:
      symmetrize_raw_sym(n, rows, i, j)

def psd_eig_sym(me: Maybe<&2, L.Eigen>, +fl: F32, +i: Nat, +j: Nat) -> {Laws.mm_get(C.psd_project.with_eig(me, fl), i, j) == Laws.mm_get(C.psd_project.with_eig(me, fl), j, i) : Maybe<&2, F32>}:
  match me:
    case None{}:
      {==}
    case Some{L.Eigen{L.Vec{n, vals}, vecs}}:
      psd_fin_sym(L.wgram(L.transpose(vecs), L.Vec{n, C.floor_list(vals, fl)}), i, j)

def Laws.psd_project_sym(a, fl, i, j):
  psd_eig_sym(L.sym_eigen(a), fl, i, j)

def dcc_s4_sym(m: Maybe<&2, L.Mat>, +i: Nat, +j: Nat) -> {Laws.mm_get(C.dcc_norm.s4(m), i, j) == Laws.mm_get(C.dcc_norm.s4(m), j, i) : Maybe<&2, F32>}:
  match m:
    case None{}:
      {==}
    case Some{L.Mat{+n, _, rows}}:
      symmetrize_raw_sym(n, rows, i, j)

def dcc_s3_sym(m: Maybe<&2, L.Mat>, lv: L.Vec, +i: Nat, +j: Nat) -> {Laws.mm_get(C.dcc_norm.s3(m, lv), i, j) == Laws.mm_get(C.dcc_norm.s3(m, lv), j, i) : Maybe<&2, F32>}:
  match m:
    case None{}:
      {==}
    case Some{tmp2}:
      dcc_s4_sym(L.mul_diag(tmp2, lv), i, j)

def dcc_s2_sym(m: Maybe<&2, L.Mat>, +lv: L.Vec, +i: Nat, +j: Nat) -> {Laws.mm_get(C.dcc_norm.s2(m, lv), i, j) == Laws.mm_get(C.dcc_norm.s2(m, lv), j, i) : Maybe<&2, F32>}:
  match m:
    case None{}:
      {==}
    case Some{cn}:
      dcc_s3_sym(L.diag_mul(lv, cn), lv, i, j)

def dcc_s1_sym(m: Maybe<&2, L.Mat>, inv_d: L.Vec, lv: L.Vec, +i: Nat, +j: Nat) -> {Laws.mm_get(C.dcc_norm.s1(m, inv_d, lv), i, j) == Laws.mm_get(C.dcc_norm.s1(m, inv_d, lv), j, i) : Maybe<&2, F32>}:
  match m:
    case None{}:
      {==}
    case Some{tmp1}:
      dcc_s2_sym(L.mul_diag(tmp1, inv_d), lv, i, j)

def dcc_diag1_sym(+inv_d: L.Vec, cr: L.Mat, lv: L.Vec, +i: Nat, +j: Nat) -> {Laws.mm_get(C.dcc_norm.diag1(inv_d, cr, lv), i, j) == Laws.mm_get(C.dcc_norm.diag1(inv_d, cr, lv), j, i) : Maybe<&2, F32>}:
  dcc_s1_sym(L.diag_mul(inv_d, cr), inv_d, lv, i, j)

def dcc_diag_sym(dv: L.Vec, cr: L.Mat, lv: L.Vec, +i: Nat, +j: Nat) -> {Laws.mm_get(C.dcc_norm.diag(dv, cr, lv), i, j) == Laws.mm_get(C.dcc_norm.diag(dv, cr, lv), j, i) : Maybe<&2, F32>}:
  L.Vec{k, ds} = dv
  dcc_diag1_sym(L.Vec{k, C.list_inv_sqrt(C.floor_list(ds, 1.0e-12))}, cr, lv, i, j)

def dcc_craw_sym(mc: Maybe<&2, L.Mat>, lv: L.Vec, +i: Nat, +j: Nat) -> {Laws.mm_get(C.dcc_cov.with_craw(mc, lv), i, j) == Laws.mm_get(C.dcc_cov.with_craw(mc, lv), j, i) : Maybe<&2, F32>}:
  match mc:
    case None{}:
      {==}
    case Some{+cr}:
      dcc_diag_sym(L.Mat.diag_vec(cr), cr, lv, i, j)

def dcc_wv_sym(mwv: Maybe<&2, L.Vec>, sr: C.DccScan, wc: L.Vec, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>, +i: Nat, +j: Nat) -> {Laws.mm_get(C.dcc_cov.with_wv(mwv, sr, wc, t, k, rows), i, j) == Laws.mm_get(C.dcc_cov.with_wv(mwv, sr, wc, t, k, rows), j, i) : Maybe<&2, F32>}:
  match mwv:
    case None{}:
      {==}
    case Some{L.Vec{_, wv}}:
      C.DccScan{std_rows, _} = sr
      +final_var = C.col_wsum.go(C.map_rows_sq(rows), wv, List.replicate(F32, U32.to_nat(k), 0.0))
      dcc_craw_sym(L.wgram(L.Mat{t, k, std_rows}, wc), L.Vec{k, C.list_sqrt(C.floor_list(final_var, 1.0e-12))}, i, j)

def dcc_wc_sym(mwc: Maybe<&2, L.Vec>, +t: U32, +k: U32, +rows: List<&2, List<&2, F32>>, +hlv: F32, +i: Nat, +j: Nat) -> {Laws.mm_get(C.dcc_cov.with_wc(mwc, t, k, rows, hlv), i, j) == Laws.mm_get(C.dcc_cov.with_wc(mwc, t, k, rows, hlv), j, i) : Maybe<&2, F32>}:
  match mwc:
    case None{}:
      {==}
    case Some{wc}:
      +lam_v = F32.exp((F32.neg(0.69314718) / hlv : F32))
      +a = (1.0 - lam_v : F32)
      +v0 = C.dcc_init_var(rows, k)
      +sr = C.dcc_scan.go(rows, v0, a, lam_v, Nil{})
      dcc_wv_sym(C.ewma_weights(t, hlv), sr, wc, t, k, rows, i, j)

def dcc_chk_sym(ok: Bool, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>, +hlv: F32, +hlc: F32, +i: Nat, +j: Nat) -> {Laws.mm_get(C.dcc_cov.chk(ok, t, k, rows, hlv, hlc), i, j) == Laws.mm_get(C.dcc_cov.chk(ok, t, k, rows, hlv, hlc), j, i) : Maybe<&2, F32>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      dcc_wc_sym(C.ewma_weights(t, hlc), t, k, rows, hlv, i, j)

def Laws.dcc_cov_sym(f_rets, hlv, hlc, i, j):
  L.Mat{+t, +k, rows} = f_rets
  +ok = Bool.and(U32.is_gt(t, 0), Bool.and(U32.is_gt(k, 0), Bool.and(F32.is_gt(hlv, 0.0), F32.is_gt(hlc, 0.0))))
  dcc_chk_sym(ok, t, k, rows, hlv, hlc, i, j)

def hac_with_w_sym(ws: List<&2, F32>, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>, +lm: U32, +nw: Bool, +i: Nat, +j: Nat) -> {L.Mat.get(C.hac_cov.with_w(ws, t, k, rows, lm, nw), i, j) == L.Mat.get(C.hac_cov.with_w(ws, t, k, rows, lm, nw), j, i) : Maybe<&2, F32>}:
  +le = U32.min(lm, (t - 1 : U32))
  xa = C.mat_to_arr(rows, t, k)
  wa = C.vec_to_arr(ws, t)
  hac_tri_sym_start(U32.to_nat(k), xa, wa, (k - 1 : U32), t, k, le, lm, nw, i, j)

def hac_from_mw_sym(mw: Maybe<&2, L.Vec>, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>, +lm: U32, nw: Bool, +i: Nat, +j: Nat) -> {Laws.mm_get(C.hac_cov.from_mw(mw, t, k, rows, lm, nw), i, j) == Laws.mm_get(C.hac_cov.from_mw(mw, t, k, rows, lm, nw), j, i) : Maybe<&2, F32>}:
  match mw:
    case None{}:
      {==}
    case Some{L.Vec{_, ws}}:
      hac_with_w_sym(ws, t, k, rows, lm, nw, i, j)

def hac_resolve_sym(use_ewma: Bool, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>, +lm: U32, +hl: F32, nw: Bool, +i: Nat, +j: Nat) -> {Laws.mm_get(C.hac_cov.resolve_w(use_ewma, t, k, rows, lm, hl, nw), i, j) == Laws.mm_get(C.hac_cov.resolve_w(use_ewma, t, k, rows, lm, hl, nw), j, i) : Maybe<&2, F32>}:
  match use_ewma:
    case True{}:
      hac_from_mw_sym(C.ewma_weights(t, hl), t, k, rows, lm, nw, i, j)
    case False{}:
      +ws = List.replicate(F32, U32.to_nat(t), (1.0 / U32.to_f32(t) : F32))
      hac_with_w_sym(ws, t, k, rows, lm, nw, i, j)

def hac_chk_sym(ok: Bool, +t: U32, +k: U32, rows: List<&2, List<&2, F32>>, +lm: U32, +hl: F32, nw: Bool, +i: Nat, +j: Nat) -> {Laws.mm_get(C.hac_cov.chk(ok, t, k, rows, lm, hl, nw), i, j) == Laws.mm_get(C.hac_cov.chk(ok, t, k, rows, lm, hl, nw), j, i) : Maybe<&2, F32>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      hac_resolve_sym(F32.is_gt(hl, 0.0), t, k, rows, lm, hl, nw, i, j)

def Laws.cov_newey_west_sym(x, lmax, hl, i, j):
  L.Mat{+t, +k, rows} = x
  hac_chk_sym(Bool.and(U32.is_gt(t, 0), U32.is_gt(k, 0)), t, k, rows, lmax, hl, True{}, i, j)

def Laws.cov_autocorr_cohen_sym(x, lmax, hl, i, j):
  L.Mat{+t, +k, rows} = x
  hac_chk_sym(Bool.and(U32.is_gt(t, 0), U32.is_gt(k, 0)), t, k, rows, lmax, hl, False{}, i, j)

def link_build_sym(mcs: Maybe<&2, List<&2, L.Mat>>, locs: List<&2, L.Mat>, joint: L.Mat, +kt: U32, +rho: F32, +i: Nat, +j: Nat) -> {Laws.mm_get(C.link_models_ir.build(mcs, locs, joint, kt, rho), i, j) == Laws.mm_get(C.link_models_ir.build(mcs, locs, joint, kt, rho), j, i) : Maybe<&2, F32>}:
  match mcs:
    case None{}:
      {==}
    case Some{+cs}:
      a0 = Array.new(F32, C.arr_depth((kt * kt : U32)), 0.0)
      a1 = C.place_diag_blocks(locs, a0, 0, kt)
      a2 = C.link_shrink_off.i(cs, cs, joint, a1, 0, kt, rho)
      upper_sym_chk_sym(U32.is_eq(kt, 0), a2, kt, i, j)

def link_ok_sym(ok: Bool, +locs: List<&2, L.Mat>, +joint: L.Mat, +kt: U32, +rho: F32, +i: Nat, +j: Nat) -> {Laws.mm_get(C.link_models_ir.chk_ok(ok, locs, joint, kt, rho), i, j) == Laws.mm_get(C.link_models_ir.chk_ok(ok, locs, joint, kt, rho), j, i) : Maybe<&2, F32>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      link_build_sym(C.compute_c_blocks(locs, joint, 0), locs, joint, kt, rho, i, j)

def link_sum_sym(ms: Maybe<&2, U32>, locs: List<&2, L.Mat>, +joint: L.Mat, +rho: F32, +i: Nat, +j: Nat) -> {Laws.mm_get(C.link_models_ir.chk_sum(ms, locs, joint, rho), i, j) == Laws.mm_get(C.link_models_ir.chk_sum(ms, locs, joint, rho), j, i) : Maybe<&2, F32>}:
  match ms:
    case None{}:
      {==}
    case Some{+kt}:
      L.Mat{+jm, +jn, _} = joint
      +ok = Bool.and(U32.is_eq(jm, kt), Bool.and(U32.is_eq(jn, kt), Bool.and(U32.is_gt(kt, 0), Bool.and(F32.is_ge(rho, 0.0), F32.is_le(rho, 1.0)))))
      link_ok_sym(ok, locs, joint, kt, rho, i, j)

def Laws.link_models_ir_sym(locs, joint, rho, i, j):
  link_sum_sym(C.sum_block_sizes(locs), locs, joint, rho, i, j)

# ---------------------------------------------------------------- 2. Strict Causality Proofs

def Laws.scan_causal(A, B, S, next, out, k, xs, s):
  match k xs:
    case 0n _:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{+x, t}:
      %Laws.scan_causal(~A, ~B, ~S, ~next, ~out, p, t, next(s, x)) : {out(s, x) <> R.list_take(B, p, C.scan(~A, ~B, ~S, ~next, ~out, t, next(s, x))) == out(s, x) <> _ : List<&2, B>}
      {==}

def take_idem(-A: Data, k: Nat, xs: List<&2, A>) -> {R.list_take(A, k, R.list_take(A, k, xs)) == R.list_take(A, k, xs) : List<&2, A>}:
  match k xs:
    case 0n _:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{h, t}:
      %take_idem(A, p, t) : {h <> R.list_take(A, p, R.list_take(A, p, t)) == h <> _ : List<&2, A>}
      {==}

def winsor_chk_causal.go(ok: Bool, +t: U32, +t2: U32, +n: U32, +rows: List<&2, List<&2, F32>>, +w: U32, +dmax: F32, +k: Nat, +st0: C.WinState) -> {Laws.mm_take_rows(k, C.winsorize_log_mad.chk(ok, t, n, rows, w, dmax)) == Laws.mm_take_rows(k, C.winsorize_log_mad.chk(ok, t2, n, R.list_take(List<&2, F32>, k, rows), w, dmax)) : Maybe<&2, List<&2, List<&2, F32>>>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      +init_hist = List.replicate(List<&2, F32>, U32.to_nat(n), Nil{})
      +e1 = Laws.scan_causal(~List<&2, F32>, ~List<&2, F32>, ~C.WinState, ~C.winsor_next, ~C.winsor_out, k, rows, C.WinState{U32.to_nat(w), dmax, init_hist})
      +e2 = Laws.scan_causal(~List<&2, F32>, ~List<&2, F32>, ~C.WinState, ~C.winsor_next, ~C.winsor_out, k, R.list_take(List<&2, F32>, k, rows), C.WinState{U32.to_nat(w), dmax, init_hist})
      +e3 = Equal.cong(List<&2, List<&2, F32>>, List<&2, List<&2, F32>>, z => C.scan(~List<&2, F32>, ~List<&2, F32>, ~C.WinState, ~C.winsor_next, ~C.winsor_out, z, C.WinState{U32.to_nat(w), dmax, init_hist}), R.list_take(List<&2, F32>, k, R.list_take(List<&2, F32>, k, rows)), R.list_take(List<&2, F32>, k, rows), take_idem(List<&2, F32>, k, rows))
      +e23 = Equal.trans(List<&2, List<&2, F32>>, R.list_take(List<&2, F32>, k, C.scan(~List<&2, F32>, ~List<&2, F32>, ~C.WinState, ~C.winsor_next, ~C.winsor_out, R.list_take(List<&2, F32>, k, rows), C.WinState{U32.to_nat(w), dmax, init_hist})), C.scan(~List<&2, F32>, ~List<&2, F32>, ~C.WinState, ~C.winsor_next, ~C.winsor_out, R.list_take(List<&2, F32>, k, R.list_take(List<&2, F32>, k, rows)), C.WinState{U32.to_nat(w), dmax, init_hist}), C.scan(~List<&2, F32>, ~List<&2, F32>, ~C.WinState, ~C.winsor_next, ~C.winsor_out, R.list_take(List<&2, F32>, k, rows), C.WinState{U32.to_nat(w), dmax, init_hist}), e2, e3)
      +efin = Equal.trans(List<&2, List<&2, F32>>, R.list_take(List<&2, F32>, k, C.scan(~List<&2, F32>, ~List<&2, F32>, ~C.WinState, ~C.winsor_next, ~C.winsor_out, rows, C.WinState{U32.to_nat(w), dmax, init_hist})), C.scan(~List<&2, F32>, ~List<&2, F32>, ~C.WinState, ~C.winsor_next, ~C.winsor_out, R.list_take(List<&2, F32>, k, rows), C.WinState{U32.to_nat(w), dmax, init_hist}), R.list_take(List<&2, F32>, k, C.scan(~List<&2, F32>, ~List<&2, F32>, ~C.WinState, ~C.winsor_next, ~C.winsor_out, R.list_take(List<&2, F32>, k, rows), C.WinState{U32.to_nat(w), dmax, init_hist})), e1, Equal.sym(List<&2, List<&2, F32>>, R.list_take(List<&2, F32>, k, C.scan(~List<&2, F32>, ~List<&2, F32>, ~C.WinState, ~C.winsor_next, ~C.winsor_out, R.list_take(List<&2, F32>, k, rows), C.WinState{U32.to_nat(w), dmax, init_hist})), C.scan(~List<&2, F32>, ~List<&2, F32>, ~C.WinState, ~C.winsor_next, ~C.winsor_out, R.list_take(List<&2, F32>, k, rows), C.WinState{U32.to_nat(w), dmax, init_hist}), e23))
      Equal.cong(List<&2, List<&2, F32>>, Maybe<&2, List<&2, List<&2, F32>>>, z => Some{z}, R.list_take(List<&2, F32>, k, C.scan(~List<&2, F32>, ~List<&2, F32>, ~C.WinState, ~C.winsor_next, ~C.winsor_out, rows, C.WinState{U32.to_nat(w), dmax, init_hist})), R.list_take(List<&2, F32>, k, C.scan(~List<&2, F32>, ~List<&2, F32>, ~C.WinState, ~C.winsor_next, ~C.winsor_out, R.list_take(List<&2, F32>, k, rows), C.WinState{U32.to_nat(w), dmax, init_hist})), efin)

def Laws.winsorize_log_mad_causal(t, t2, n, rows, w, dmax, k):
  +ok = Bool.and(U32.is_gt(w, 0), F32.is_gt(dmax, 0.0))
  +init_hist = List.replicate(List<&2, F32>, U32.to_nat(n), Nil{})
  winsor_chk_causal.go(ok, t, t2, n, rows, w, dmax, k, C.WinState{U32.to_nat(w), dmax, init_hist})

def take_take_add(-A: Data, k: Nat, w: Nat, xs: List<&2, A>) -> {R.list_take(A, w, R.list_take(A, Nat.add(k, w), xs)) == R.list_take(A, w, xs) : List<&2, A>}:
  match k:
    case 0n:
      take_idem(A, w, xs)
    case 1n+(+p):
      match w xs:
        case 0n _:
          {==}
        case 1n+q Nil{}:
          {==}
        case 1n+(+q) Con{h, t}:
          %Equal.sym(Nat, Nat.add(p, 1n+q), 1n+Nat.add(p, q), add_succ_r(p, q)) : {h <> R.list_take(A, q, R.list_take(A, _, t)) == h <> R.list_take(A, q, t) : List<&2, A>}
          %take_take_add(A, 1n+p, q, t) : {h <> R.list_take(A, q, R.list_take(A, Nat.add(1n+p, q), t)) == h <> _ : List<&2, A>}
          {==}

def lt_zero_absurd(i: Nat, h: {Nat.is_lt(i, 0n) == True{} : Bool}) -> Empty:
  match i:
    case 0n:
      false_ne_true(h)
    case 1n+q:
      false_ne_true(h)

def Laws.make_windows_get(A, rem, xs, w, i, h, hlen):
  match rem xs i:
    case 0n Nil{} _:
      Empty.absurd({None{} == Some{R.list_take(A, w, R.list_drop(A, i, Nil{}))} : Maybe<&2, List<&2, A>>}, lt_zero_absurd(i, h))
    case 0n Con{x, t} _:
      Empty.absurd({None{} == Some{R.list_take(A, w, R.list_drop(A, i, x <> t))} : Maybe<&2, List<&2, A>>}, lt_zero_absurd(i, h))
    case 1n+p Nil{} _:
      Empty.absurd({None{} == Some{R.list_take(A, w, R.list_drop(A, i, Nil{}))} : Maybe<&2, List<&2, A>>}, lt_zero_absurd(i, hlen))
    case 1n+p Con{x, t} 0n:
      {==}
    case 1n+p Con{x, t} 1n+q:
      Laws.make_windows_get(A, p, t, w, q, h, hlen)

def Laws.make_windows_causal(A, k, rem, xs, v):
  match k rem xs:
    case 0n _ _:
      {==}
    case 1n+kp 0n Nil{}:
      {==}
    case 1n+kp 0n Con{x, t}:
      {==}
    case 1n+kp 1n+rp Nil{}:
      {==}
    case 1n+(+kp) 1n+(+rp) Con{+x, +t}:
      +h1 = take_take_add(A, kp, v, t)
      %Equal.sym(List<&2, A>, R.list_take(A, v, R.list_take(A, Nat.add(kp, v), t)), R.list_take(A, v, t), h1) : {(x <> R.list_take(A, v, t)) <> R.list_take(List<&2, A>, kp, R.make_windows(A, rp, t, 1n+v)) == (x <> _) <> R.list_take(List<&2, A>, kp, R.make_windows(A, rp, R.list_take(A, Nat.add(kp, v), t), 1n+v)) : List<&2, List<&2, A>>}
      %Laws.make_windows_causal(A, kp, rp, t, v) : {(x <> R.list_take(A, v, t)) <> R.list_take(List<&2, A>, kp, R.make_windows(A, rp, t, 1n+v)) == (x <> R.list_take(A, v, t)) <> _ : List<&2, List<&2, A>>}
      {==}

def drop_get(-A: Data, k: Nat, xs: List<&2, A>, +i: Nat) -> {List.get(&2, A, R.list_drop(A, k, xs), i) == List.get(&2, A, xs, Nat.add(i, k)) : Maybe<&2, A>}:
  match k xs:
    case 0n _:
      %Equal.sym(Nat, Nat.add(i, 0n), i, add_zero_r(i)) : {List.get(&2, A, xs, i) == List.get(&2, A, xs, _) : Maybe<&2, A>}
      {==}
    case 1n+(+p) Nil{}:
      {==}
    case 1n+(+p) Con{h, t}:
      %Equal.sym(Nat, Nat.add(i, 1n+p), 1n+Nat.add(i, p), add_succ_r(i, p)) : {List.get(&2, A, R.list_drop(A, p, t), i) == List.get(&2, A, h <> t, _) : Maybe<&2, A>}
      drop_get(A, p, t, i)

def Laws.oos_returns_row(t, n, rows, window, v, j, hw, ok):
  %Equal.sym(Bool, Bool.and(U32.is_gt(window, 0), U32.is_ge(t, window)), True{}, ok) : {Laws.mm_row(R.oos_returns.chk(_, t, n, rows, window), 1n+j) == List.get(&2, List<&2, F32>, rows, Nat.add(1n+j, v)) : Maybe<&2, List<&2, F32>>}
  %Equal.sym(Nat, U32.to_nat(window), 1n+v, hw) : {List.get(&2, List<&2, F32>, R.list_drop(List<&2, F32>, R.oos_drop(_), rows), 1n+j) == List.get(&2, List<&2, F32>, rows, Nat.add(1n+j, v)) : Maybe<&2, List<&2, F32>>}
  drop_get(List<&2, F32>, v, rows, 1n+j)

# ---------------------------------------------------------------- 3. No-Lookahead Evaluation Proofs

def maybe_pair_fm_none_r(mf: Maybe<&2, P.FactorModel>) -> {None{} == Laws.maybe_pair_fm(mf, None{}) : Maybe<&2, R.FmRetPair>}:
  match mf:
    case None{}:
      {==}
    case Some{_}:
      {==}

def Laws.pair_oos_fm_row(fms, r0, rs, i):
  match fms rs i:
    case Nil{} _ 0n:
      {==}
    case Nil{} _ 1n+k:
      {==}
    case Con{fm, ft} Nil{} 0n:
      {==}
    case Con{fm, ft} Nil{} 1n+k:
      maybe_pair_fm_none_r(List.get(&2, P.FactorModel, ft, k))
    case Con{fm, ft} Con{r, rt} 0n:
      {==}
    case Con{fm, ft} Con{r, rt} 1n+k:
      Laws.pair_oos_fm_row(ft, r, rt, k)

def maybe_pair_fmw_none_m(mf: Maybe<&2, P.FactorModel>, mr: Maybe<&2, List<&2, F32>>) -> {None{} == Laws.maybe_pair_fmw(mf, None{}, mr) : Maybe<&2, R.FmWRet>}:
  match mf:
    case None{}:
      {==}
    case Some{_}:
      {==}

def maybe_pair_fmw_none_r(mf: Maybe<&2, P.FactorModel>, mw: Maybe<&2, List<&2, F32>>) -> {None{} == Laws.maybe_pair_fmw(mf, mw, None{}) : Maybe<&2, R.FmWRet>}:
  match mf mw:
    case None{} _:
      {==}
    case Some{_} None{}:
      {==}
    case Some{_} Some{_}:
      {==}

def Laws.pair_oos_fmw_row(fms, ws, r0, rs, i):
  match fms ws rs i:
    case Nil{} _ _ 0n:
      {==}
    case Nil{} _ _ 1n+k:
      {==}
    case Con{fm, ft} Nil{} _ 0n:
      {==}
    case Con{fm, ft} Nil{} _ 1n+k:
      maybe_pair_fmw_none_m(List.get(&2, P.FactorModel, ft, k), List.get(&2, List<&2, F32>, rs, 1n+k))
    case Con{fm, ft} Con{w, wt} Nil{} 0n:
      {==}
    case Con{fm, ft} Con{w, wt} Nil{} 1n+k:
      maybe_pair_fmw_none_r(List.get(&2, P.FactorModel, ft, k), List.get(&2, List<&2, F32>, wt, k))
    case Con{fm, ft} Con{w, wt} Con{r, rt} 0n:
      {==}
    case Con{fm, ft} Con{w, wt} Con{r, rt} 1n+k:
      Laws.pair_oos_fmw_row(ft, wt, r, rt, k)

def Laws.qdist_mismatch(fms, t, n, rows, h):
  %Equal.sym(Bool, U32.is_eq(U32.from_nat(List.length(&2, P.FactorModel, fms)), t), False{}, h) : {R.qdist.chk(Bool.and(_, Bool.and(U32.is_gt(t, 1), U32.is_gt(n, 0))), fms, rows, t, n) == None{} : Maybe<&2, R.QDistResult>}
  {==}

def Laws.mvp_test_mismatch(fms, t, n, rows, nb, bs, h):
  +e = bool_and_false_mid(U32.is_eq(U32.from_nat(List.length(&2, P.FactorModel, fms)), t), U32.is_eq(n, nb), Bool.and(U32.is_gt(t, 1), U32.is_gt(n, 0)), h)
  %Equal.sym(Bool, Bool.and(U32.is_eq(U32.from_nat(List.length(&2, P.FactorModel, fms)), t), Bool.and(U32.is_eq(n, nb), Bool.and(U32.is_gt(t, 1), U32.is_gt(n, 0)))), False{}, e) : {R.mvp.chk(_, fms, rows, L.Vec{nb, bs}, t) == None{} : Maybe<&2, R.MvpResult>}
  {==}

# ---------------------------------------------------------------- 4. Parallel Equivalence Proofs

# Clean two_append helper without field projections:
def two_append(-A: Data, two: R.Two<A>) -> List<&2, A>:
  R.Two{l, r} = two
  List.append(&2, A, l, r)

def two_append_cons(-A: Data, h: A, two: R.Two<A>) -> {two_append(A, R.split.cons(A, h, two)) == h <> two_append(A, two) : List<&2, A>}:
  R.Two{l, r} = two
  {==}

def split_rejoin(-A: Data, k: Nat, xs: List<&2, A>) -> {two_append(A, R.split(A, k, xs)) == xs : List<&2, A>}:
  match k xs:
    case 0n _:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+(+p) Con{+h, +t}:
      +e1 = two_append_cons(A, h, R.split(A, p, t))
      +e2 = Equal.cong(List<&2, A>, List<&2, A>, z => h <> z, two_append(A, R.split(A, p, t)), t, split_rejoin(A, p, t))
      Equal.trans(List<&2, A>, two_append(A, R.split.cons(A, h, R.split(A, p, t))), h <> two_append(A, R.split(A, p, t)), h <> t, e1, e2)

def pseq_append(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, xs: List<&2, A>, +ys: List<&2, A>, +c: C) -> {List.append(&2, B, R.pseq(~A, ~B, ~C, ~f, xs, c), R.pseq(~A, ~B, ~C, ~f, ys, c)) == R.pseq(~A, ~B, ~C, ~f, List.append(&2, A, xs, ys), c) : List<&2, B>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %pseq_append(~A, ~B, ~C, ~f, t, ys, c) : {f(c, h) <> List.append(&2, B, R.pseq(~A, ~B, ~C, ~f, t, c), R.pseq(~A, ~B, ~C, ~f, ys, c)) == f(c, h) <> _ : List<&2, B>}
      {==}

def par_seq(~A: Data, ~B: Data, ~C: Data, ~f: C -> A -> B, depth: Nat, two: R.Two<A>, +h: U32, +r: U32, +c: C) -> {R.par(~A, ~B, ~C, ~f, depth, two, h, r, c) == R.pseq(~A, ~B, ~C, ~f, two_append(A, two), c) : List<&2, B>}:
  match depth:
    case 0n:
      R.Two{xl, xr} = two
      pseq_append(~A, ~B, ~C, ~f, xl, xr, c)
    case 1n+(+d):
      R.Two{+xl, +xr} = two
      +hl = (h >> 1n : U32)
      +hr = (r >> 1n : U32)
      +el = Equal.trans(List<&2, B>, R.par(~A, ~B, ~C, ~f, d, R.split(A, U32.to_nat(hl), xl), hl, (h - hl : U32), c), R.pseq(~A, ~B, ~C, ~f, two_append(A, R.split(A, U32.to_nat(hl), xl)), c), R.pseq(~A, ~B, ~C, ~f, xl, c), par_seq(~A, ~B, ~C, ~f, d, R.split(A, U32.to_nat(hl), xl), hl, (h - hl : U32), c), Equal.cong(List<&2, A>, List<&2, B>, z => R.pseq(~A, ~B, ~C, ~f, z, c), two_append(A, R.split(A, U32.to_nat(hl), xl)), xl, split_rejoin(A, U32.to_nat(hl), xl)))
      +er = Equal.trans(List<&2, B>, R.par(~A, ~B, ~C, ~f, d, R.split(A, U32.to_nat(hr), xr), hr, (r - hr : U32), c), R.pseq(~A, ~B, ~C, ~f, two_append(A, R.split(A, U32.to_nat(hr), xr)), c), R.pseq(~A, ~B, ~C, ~f, xr, c), par_seq(~A, ~B, ~C, ~f, d, R.split(A, U32.to_nat(hr), xr), hr, (r - hr : U32), c), Equal.cong(List<&2, A>, List<&2, B>, z => R.pseq(~A, ~B, ~C, ~f, z, c), two_append(A, R.split(A, U32.to_nat(hr), xr)), xr, split_rejoin(A, U32.to_nat(hr), xr)))
      +eapp = Equal.trans(List<&2, B>,
        List.append(&2, B, R.par(~A, ~B, ~C, ~f, d, R.split(A, U32.to_nat(hl), xl), hl, (h - hl : U32), c), R.par(~A, ~B, ~C, ~f, d, R.split(A, U32.to_nat(hr), xr), hr, (r - hr : U32), c)),
        List.append(&2, B, R.pseq(~A, ~B, ~C, ~f, xl, c), R.par(~A, ~B, ~C, ~f, d, R.split(A, U32.to_nat(hr), xr), hr, (r - hr : U32), c)),
        List.append(&2, B, R.pseq(~A, ~B, ~C, ~f, xl, c), R.pseq(~A, ~B, ~C, ~f, xr, c)),
        Equal.cong(List<&2, B>, List<&2, B>, z => List.append(&2, B, z, R.par(~A, ~B, ~C, ~f, d, R.split(A, U32.to_nat(hr), xr), hr, (r - hr : U32), c)), R.par(~A, ~B, ~C, ~f, d, R.split(A, U32.to_nat(hl), xl), hl, (h - hl : U32), c), R.pseq(~A, ~B, ~C, ~f, xl, c), el),
        Equal.cong(List<&2, B>, List<&2, B>, z => List.append(&2, B, R.pseq(~A, ~B, ~C, ~f, xl, c), z), R.par(~A, ~B, ~C, ~f, d, R.split(A, U32.to_nat(hr), xr), hr, (r - hr : U32), c), R.pseq(~A, ~B, ~C, ~f, xr, c), er)
      )
      Equal.trans(List<&2, B>, List.append(&2, B, R.par(~A, ~B, ~C, ~f, d, R.split(A, U32.to_nat(hl), xl), hl, (h - hl : U32), c), R.par(~A, ~B, ~C, ~f, d, R.split(A, U32.to_nat(hr), xr), hr, (r - hr : U32), c)), List.append(&2, B, R.pseq(~A, ~B, ~C, ~f, xl, c), R.pseq(~A, ~B, ~C, ~f, xr, c)), R.pseq(~A, ~B, ~C, ~f, List.append(&2, A, xl, xr), c), eapp, pseq_append(~A, ~B, ~C, ~f, xl, xr, c))

def Laws.pmap_seq(A, B, C, f, xs, t, c):
  +h = (t >> 1n : U32)
  +d = Bool.pick(Nat, U32.is_lt(t, 64), 0n, 5n)
  Equal.trans(List<&2, B>,
    R.par(~A, ~B, ~C, ~f, d, R.split(A, U32.to_nat(h), xs), h, (t - h : U32), c),
    R.pseq(~A, ~B, ~C, ~f, two_append(A, R.split(A, U32.to_nat(h), xs)), c),
    R.pseq(~A, ~B, ~C, ~f, xs, c),
    par_seq(~A, ~B, ~C, ~f, d, R.split(A, U32.to_nat(h), xs), h, (t - h : U32), c),
    Equal.cong(List<&2, A>, List<&2, B>, z => R.pseq(~A, ~B, ~C, ~f, z, c), two_append(A, R.split(A, U32.to_nat(h), xs)), xs, split_rejoin(A, U32.to_nat(h), xs))
  )

def Laws.pseq_get(A, B, C, f, xs, c, i):
  match xs i:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+k:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+k:
      Laws.pseq_get(~A, ~B, ~C, ~f, t, c, k)

# ---------------------------------------------------------------- 5. Dimension & Parameter Guard Proofs

def Laws.rotate_model_mismatch(n, k, brows, cf, iv, cm, cn, crows, h):
  +e = bool_and_false_mid(R.fm_dims_ok(P.FactorModel{L.Mat{n, k, brows}, cf, iv}), U32.is_eq(k, cm), Bool.and(U32.is_eq(cm, cn), U32.is_gt(k, 0)), h)
  %Equal.sym(Bool, Bool.and(R.fm_dims_ok(P.FactorModel{L.Mat{n, k, brows}, cf, iv}), Bool.and(U32.is_eq(k, cm), Bool.and(U32.is_eq(cm, cn), U32.is_gt(k, 0)))), False{}, e) : {R.rot_mod.chk(_, L.Mat{n, k, brows}, cf, iv, L.Mat{cm, cn, crows}) == None{} : Maybe<&2, P.FactorModel>}
  {==}

def Laws.project_model_mismatch(n, k, brows, cf, iv, am, ap, arows, h):
  +e = bool_and_false_mid(R.fm_dims_ok(P.FactorModel{L.Mat{n, k, brows}, cf, iv}), U32.is_eq(n, am), Bool.and(U32.is_gt(ap, 0), U32.is_ge(n, ap)), h)
  %Equal.sym(Bool, Bool.and(R.fm_dims_ok(P.FactorModel{L.Mat{n, k, brows}, cf, iv}), Bool.and(U32.is_eq(n, am), Bool.and(U32.is_gt(ap, 0), U32.is_ge(n, ap)))), False{}, e) : {R.proj_mod.chk(_, L.Mat{n, k, brows}, cf, L.Mat{am, ap, arows}, iv) == None{} : Maybe<&2, P.FactorModel>}
  {==}

def Laws.pushout_loadings_mismatch(bm, bk, brows, am, ap, arows, iv, h):
  L.Vec{+dn, +ds} = iv
  %Equal.sym(Bool, U32.is_eq(bm, am), False{}, h) : {R.pushout_load.chk2(Bool.and(_, Bool.and(U32.is_eq(bm, dn), Bool.and(U32.is_gt(bk, 0), Bool.and(U32.is_gt(ap, 0), Bool.and(U32.is_ge(bm, bk), R.all_pos(ds)))))), bm, ap, L.Mat{bm, bk, brows}, L.Mat{am, ap, arows}, ds) == None{} : Maybe<&2, L.Mat>}
  {==}

def Laws.group_risk_mismatch(n, k, brows, cf, iv, wn, ws, groups, h):
  +g = U32.from_nat(List.length(&2, List<&2, U32>, groups))
  +e = bool_and_false_mid(R.fm_dims_ok(P.FactorModel{L.Mat{n, k, brows}, cf, iv}), U32.is_eq(n, wn), Bool.and(U32.is_gt(g, 0), R.all_groups_ok(groups, k)), h)
  %Equal.sym(Bool, Bool.and(R.fm_dims_ok(P.FactorModel{L.Mat{n, k, brows}, cf, iv}), Bool.and(U32.is_eq(n, wn), Bool.and(U32.is_gt(g, 0), R.all_groups_ok(groups, k)))), False{}, e) : {R.group_risk.chk(_, P.FactorModel{L.Mat{n, k, brows}, cf, iv}, L.Vec{wn, ws}, cf, groups, g, k) == None{} : Maybe<&2, R.GroupRisk>}
  {==}

def Laws.qlike_mismatch(nv, vs, nr, rs, h):
  %Equal.sym(Bool, U32.is_eq(nv, nr), False{}, h) : {R.qlike.chk(Bool.and(_, Bool.and(U32.is_gt(nv, 0), R.all_pos(vs))), nv, vs, rs) == None{} : Maybe<&2, F32>}
  {==}

def Laws.vol_mse_mismatch(nv, vs, nr, rs, h):
  %Equal.sym(Bool, U32.is_eq(nv, nr), False{}, h) : {R.vol_mse.chk(Bool.and(_, Bool.and(U32.is_gt(nv, 0), R.all_pos(vs))), nv, vs, rs) == None{} : Maybe<&2, F32>}
  {==}

def Laws.bias_stat_mismatch(nv, vs, nr, rs, h):
  %Equal.sym(Bool, U32.is_eq(nv, nr), False{}, h) : {R.bias_stat.chk(Bool.and(_, Bool.and(U32.is_gt(nv, 0), R.all_pos(vs))), nv, vs, rs) == None{} : Maybe<&2, F32>}
  {==}

def Laws.mahalanobis_mismatch(fms, t, n, rows, h):
  %Equal.sym(Bool, U32.is_eq(U32.from_nat(List.length(&2, P.FactorModel, fms)), t), False{}, h) : {R.mahal.chk(Bool.and(_, Bool.and(U32.is_gt(t, 1), U32.is_gt(n, 0))), fms, rows, t, n) == None{} : Maybe<&2, R.MahalanobisResult>}
  {==}

def Laws.beta_error_mismatch(fms, t, n, rows, nw, ws, hl, h):
  +nf = U32.from_nat(List.length(&2, P.FactorModel, fms))
  +e = bool_and_false_mid(U32.is_eq(nf, t), U32.is_eq(n, nw), Bool.and(U32.is_gt(t, 0), Bool.and(U32.is_gt(n, 0), F32.is_gt(hl, 0.0))), h)
  %Equal.sym(Bool, Bool.and(U32.is_eq(nf, t), Bool.and(U32.is_eq(n, nw), Bool.and(U32.is_gt(t, 0), Bool.and(U32.is_gt(n, 0), F32.is_gt(hl, 0.0))))), False{}, e) : {R.beta_err.chk(_, fms, rows, L.Vec{nw, ws}, ws, t, n, hl) == None{} : Maybe<&2, R.BetaErrResult>}
  {==}

def Laws.cs_wls_mismatch(n, k, brows, nr, rs, w, h):
  L.Vec{+nw, +ws} = w
  %Equal.sym(Bool, U32.is_eq(n, nr), False{}, h) : {R.cs_wls.chk(Bool.and(_, Bool.and(U32.is_eq(n, nw), Bool.and(U32.is_gt(k, 0), Bool.and(U32.is_ge(n, k), R.all_pos(ws))))), n, k, L.Mat{n, k, brows}, L.Vec{nw, ws}, ws, L.Vec{nr, rs}) == None{} : Maybe<&2, R.CSRegResult>}
  {==}

def Laws.cs_constrained_mismatch(n, k, brows, nr, rs, w, cons, h):
  L.Vec{+nw, +ws} = w
  R.CSConstraint{+cm, +dv} = cons
  L.Mat{+ck, +cp, _} = cm
  L.Vec{+dp, _} = dv
  %Equal.sym(Bool, U32.is_eq(n, nr), False{}, h) : {R.cs_con.chk(Bool.and(_, Bool.and(U32.is_eq(n, nw), Bool.and(U32.is_eq(k, ck), Bool.and(U32.is_eq(cp, dp), Bool.and(U32.is_gt(k, 0), R.all_pos(ws)))))), n, k, L.Mat{n, k, brows}, L.Vec{nr, rs}, ws, cm, dv) == None{} : Maybe<&2, R.CSRegResult>}
  {==}

def Laws.cs_ridge_mismatch(n, k, brows, nr, rs, w, delta, h):
  L.Vec{+nw, +ws} = w
  %Equal.sym(Bool, U32.is_eq(n, nr), False{}, h) : {R.cs_ridge.chk(Bool.and(_, Bool.and(U32.is_eq(n, nw), Bool.and(U32.is_gt(k, 0), Bool.and(F32.is_ge(delta, 0.0), R.all_pos(ws))))), n, k, delta, L.Mat{n, k, brows}, L.Vec{nr, rs}, ws) == None{} : Maybe<&2, R.CSRegResult>}
  {==}

def Laws.fit_fundamental_mismatch(t, n, rows, bs, opt_cons, cfg, h):
  %Equal.sym(Bool, U32.is_eq(U32.from_nat(List.length(&2, L.Mat, bs)), t), False{}, h) : {R.fund_fit.chk(Bool.and(_, Bool.and(U32.is_gt(t, 0), U32.is_gt(n, 0))), bs, L.Mat{t, n, rows}, opt_cons, cfg, t, n) == None{} : Maybe<&2, R.FundModelFit>}
  {==}

def Laws.rebase_currency_mismatch(n, qc, crows, cm, cn, cov_rows, target, h):
  %Equal.sym(Bool, U32.is_eq(qc, cm), False{}, h) : {R.wrap_rebase(C.rebase_currency.chk(Bool.and(_, Bool.and(U32.is_eq(cm, cn), U32.is_lt(target, qc))), L.Mat{n, qc, crows}, L.Mat{cm, cn, cov_rows}, qc, target)) == None{} : Maybe<&2, R.RebaseResult>}
  {==}

def Laws.pca_svd_zero_k(r, hl, use_sub):
  L.Mat{+t, +n, _} = r
  {==}

def Laws.eigenfactor_turnover_mismatch(m1, k1, r1, m2, k2, r2, h):
  %Equal.sym(Bool, U32.is_eq(m1, m2), False{}, h) : {R.eig_to.chk2(Bool.and(_, Bool.and(U32.is_eq(k1, k2), U32.is_gt(k1, 0))), L.Mat{m1, k1, r1}, L.Mat{m2, k2, r2}, k1) == None{} : Maybe<&2, R.EigenTurnover>}
  {==}

def Laws.align_sign_mismatch(m1, k1, r1, m2, k2, r2, h):
  %Equal.sym(Bool, U32.is_eq(m1, m2), False{}, h) : {R.align_sign.chk(Bool.and(_, Bool.and(U32.is_eq(k1, k2), U32.is_gt(k1, 0))), L.Mat{m1, k1, r1}, L.Mat{m2, k2, r2}, k1, m1) == None{} : Maybe<&2, L.Mat>}
  {==}

def Laws.subspace_distance_mismatch(m1, k1, r1, m2, k2, r2, h):
  %Equal.sym(Bool, U32.is_eq(m1, m2), False{}, h) : {R.sub_dist.chk(Bool.and(_, Bool.and(U32.is_eq(k1, k2), Bool.and(U32.is_gt(k1, 0), U32.is_ge(m1, k1)))), L.Mat{m1, k1, r1}, L.Mat{m2, k2, r2}, k1) == None{} : Maybe<&2, F32>}
  {==}

def Laws.impute_ts_mismatch(ta, ma, arows, tf, kf, frows, h):
  %Equal.sym(Bool, U32.is_eq(ta, tf), False{}, h) : {R.imp_ts.chk(Bool.and(_, Bool.and(U32.is_gt(ma, 0), Bool.and(U32.is_gt(kf, 0), U32.is_ge(tf, kf)))), L.Mat{ta, ma, arows}, L.Mat{tf, kf, frows}) == None{} : Maybe<&2, L.Mat>}
  {==}

def Laws.rolling_stat_zero_window(r, cfg, am):
  L.Mat{+t, +n, rows} = r
  {==}

# ---------------------------------------------------------------- Public evaluators run over the OOS pairs

def Laws.qdist_pairs(fms, t, n, r0, rs, h):
  +pairs = R.pair_oos_fm(fms, rs)
  +rhs = R.qdist.fin(R.seq_maybe(F32, R.pseq(~R.FmRetPair, ~Maybe<&2, F32>, ~U32, ~R.qdist_period, pairs, n)), (t - 1 : U32))
  %Equal.sym(Bool, Bool.and(U32.is_eq(U32.from_nat(List.length(&2, P.FactorModel, fms)), t), Bool.and(U32.is_gt(t, 1), U32.is_gt(n, 0))), True{}, h) : {R.qdist.chk(_, fms, r0 <> rs, t, n) == rhs : Maybe<&2, R.QDistResult>}
  %Equal.sym(List<&2, Maybe<&2, F32>>, R.pmap(~R.FmRetPair, ~Maybe<&2, F32>, ~U32, ~R.qdist_period, pairs, (t - 1 : U32), n), R.pseq(~R.FmRetPair, ~Maybe<&2, F32>, ~U32, ~R.qdist_period, pairs, n), Laws.pmap_seq(~R.FmRetPair, ~Maybe<&2, F32>, ~U32, ~R.qdist_period, pairs, (t - 1 : U32), n)) : {R.qdist.fin(R.seq_maybe(F32, _), (t - 1 : U32)) == rhs : Maybe<&2, R.QDistResult>}
  {==}

def Laws.mahalanobis_pairs(fms, t, n, r0, rs, h):
  +pairs = R.pair_oos_fm(fms, rs)
  +rhs = R.mahal.fin(R.seq_maybe(F32, R.pseq(~R.FmRetPair, ~Maybe<&2, F32>, ~U32, ~R.mahal_period, pairs, n)), (t - 1 : U32))
  %Equal.sym(Bool, Bool.and(U32.is_eq(U32.from_nat(List.length(&2, P.FactorModel, fms)), t), Bool.and(U32.is_gt(t, 1), U32.is_gt(n, 0))), True{}, h) : {R.mahal.chk(_, fms, r0 <> rs, t, n) == rhs : Maybe<&2, R.MahalanobisResult>}
  %Equal.sym(List<&2, Maybe<&2, F32>>, R.pmap(~R.FmRetPair, ~Maybe<&2, F32>, ~U32, ~R.mahal_period, pairs, (t - 1 : U32), n), R.pseq(~R.FmRetPair, ~Maybe<&2, F32>, ~U32, ~R.mahal_period, pairs, n), Laws.pmap_seq(~R.FmRetPair, ~Maybe<&2, F32>, ~U32, ~R.mahal_period, pairs, (t - 1 : U32), n)) : {R.mahal.fin(R.seq_maybe(F32, _), (t - 1 : U32)) == rhs : Maybe<&2, R.MahalanobisResult>}
  {==}

def Laws.mvp_pairs(fms, t, n, r0, rs, nb, bs, h):
  +pairs = R.pair_oos_fm(fms, rs)
  +bv = {L.Vec{nb, bs} : L.Vec}
  +rhs = R.mvp.fin(R.seq_maybe(R.MvpStep, R.pseq(~R.FmRetPair, ~Maybe<&2, R.MvpStep>, ~L.Vec, ~R.mvp_period, pairs, bv)), (t - 1 : U32))
  %Equal.sym(Bool, Bool.and(U32.is_eq(U32.from_nat(List.length(&2, P.FactorModel, fms)), t), Bool.and(U32.is_eq(n, nb), Bool.and(U32.is_gt(t, 1), U32.is_gt(n, 0)))), True{}, h) : {R.mvp.chk(_, fms, r0 <> rs, bv, t) == rhs : Maybe<&2, R.MvpResult>}
  %Equal.sym(List<&2, Maybe<&2, R.MvpStep>>, R.pmap(~R.FmRetPair, ~Maybe<&2, R.MvpStep>, ~L.Vec, ~R.mvp_period, pairs, (t - 1 : U32), bv), R.pseq(~R.FmRetPair, ~Maybe<&2, R.MvpStep>, ~L.Vec, ~R.mvp_period, pairs, bv), Laws.pmap_seq(~R.FmRetPair, ~Maybe<&2, R.MvpStep>, ~L.Vec, ~R.mvp_period, pairs, (t - 1 : U32), bv)) : {R.mvp.fin(R.seq_maybe(R.MvpStep, _), (t - 1 : U32)) == rhs : Maybe<&2, R.MvpResult>}
  {==}

def Laws.portfolio_vol_pairs(fms, tw, nw, wrows, tr, nr, r0, rs, h):
  +items = R.pair_oos_fmw(fms, wrows, rs)
  +rhs = R.pvol.fin(R.seq_maybe(R.MvpStep, R.pseq(~R.FmWRet, ~Maybe<&2, R.MvpStep>, ~U32, ~R.pvol_period, items, nr)), (tr - 1 : U32))
  %Equal.sym(Bool, Bool.and(U32.is_eq(U32.from_nat(List.length(&2, P.FactorModel, fms)), tw), Bool.and(U32.is_eq(tw, tr), Bool.and(U32.is_eq(nw, nr), Bool.and(U32.is_gt(tr, 1), U32.is_gt(nr, 0))))), True{}, h) : {R.pvol.chk(_, fms, wrows, r0 <> rs, tr, nr) == rhs : Maybe<&2, R.VolEval>}
  %Equal.sym(List<&2, Maybe<&2, R.MvpStep>>, R.pmap(~R.FmWRet, ~Maybe<&2, R.MvpStep>, ~U32, ~R.pvol_period, items, (tr - 1 : U32), nr), R.pseq(~R.FmWRet, ~Maybe<&2, R.MvpStep>, ~U32, ~R.pvol_period, items, nr), Laws.pmap_seq(~R.FmWRet, ~Maybe<&2, R.MvpStep>, ~U32, ~R.pvol_period, items, (tr - 1 : U32), nr)) : {R.pvol.fin(R.seq_maybe(R.MvpStep, _), (tr - 1 : U32)) == rhs : Maybe<&2, R.VolEval>}
  {==}
