# Laws for signal. The checker doesn't run F32 arithmetic, so IC values are
# checked against scipy in check.py. These laws cover the structure.
import Base
import bend-kit-f32array@0.2.1.0/f32array.bend as A
import ./signal.bend as S

def is_some(m: Maybe<&1, S.Panel>) -> Bool:
  match m:
    case Some{_}:
      True{}
    case None{}:
      False{}

def row(n: Nat) -> A.F32Array:
  A.from_list(List.replicate(F32, n, 1.0))

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
