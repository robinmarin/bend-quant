import Base

# Array<F32> get+set vs a List<F32> pass, 5000 passes over 1024 slots. Usage: out/access

# st = (array, value at i); write value+1 back at i, then read i+1
def pass_a(k: Nat, st: Array<F32> & F32, +i: U32) -> Array<F32>:
  match k:
    case 0n:
      (a, v) = st
      Array.set(F32, a, i, (v + 1.0 : F32))
    case 1n+p:
      (a, v) = st
      +j = (i + 1 : U32)
      pass_a(p, Array.get(F32, Array.set(F32, a, i, (v + 1.0 : F32)), j), j)

def rep_a(r: Nat, a: Array<F32>) -> Array<F32>:
  match r:
    case 0n:
      a
    case 1n+p:
      rep_a(p, pass_a(1023n, Array.get(F32, a, 0), 0))

def pass_l(xs: List<&2, F32>, acc: List<&2, F32>) -> List<&2, F32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      pass_l(t, (h + 1.0 : F32) <> acc)

def rep_l(r: Nat, xs: List<&2, F32>) -> List<&2, F32>:
  match r:
    case 0n:
      xs
    case 1n+p:
      rep_l(p, pass_l(xs, Nil{}))

def first(r: Array<F32> & F32) -> F32:
  (_, v) = r
  v

def lhead(xs: List<&2, F32>) -> F32:
  match xs:
    case Nil{}:
      0.0
    case Con{h, _}:
      h

def main() -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    IO.print(F32.show(first(Array.get(F32, rep_a(5000n, [0.0 : F32*1024n]), 3))))
    +t1 : Nat <- IO.now()
    IO.print(F32.show(lhead(rep_l(5000n, List.replicate(F32, 1024n, 0.0)))))
    t2 : Nat <- IO.now()
    IO.print("array_ms=" ++ Nat.show(Nat.sub(t1, t0)) ++ " list_ms=" ++ Nat.show(Nat.sub(t2, t1)))
