# expect: a call of a.M, a method with several values, is compiled as a call of a method of one value
# (#283, #335) The clauses after a choice whose alternatives' values are of unrelated classes, shared
# by them, call M through an operation dictionary as a method of one value, and a.M and b.M are of
# families with several values whose stubs stay in their classes: it compiled, and stopped with
# `error: user` at the call. No call of a stub may be compiled.
a := class:
    M()<transacts>:int = 1 | 2
b := class:
    M()<transacts>:int = 30 | 40
Dup(V:t where t:type):t = V | V
Main()<transacts>:void =
    for (A := (Dup(a{}) | Dup(b{})), X := A.M()) { Print("x {X}") }
