# expect: 14:13: expected a, found any (A is an any here: after the first success of the choice at 12:8
# (#283, #335) The same where the clauses after the choice are shared by its alternatives (an
# ordinary method, through an operation dictionary): A is an any after the condition, which a
# function taking an a does not take.
a := class:
    N():int = 10
b := class:
    N():int = 20
Dup(V:t where t:type):t = V | V
Need(V:a):void = Print("need")
Main()<transacts>:void =
    if (A := (Dup(a{}) | Dup(b{})), X := A.N(), X > 10):
        Print("{X}")
        Need(A)
