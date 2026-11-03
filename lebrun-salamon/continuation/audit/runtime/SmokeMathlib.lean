import Mathlib

example (a b : Nat) : a + b = b + a := by omega
example (x : Real) : x ^ 2 >= 0 := by positivity
