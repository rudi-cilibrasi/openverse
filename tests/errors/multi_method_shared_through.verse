# expect: 10:17: Twice has several values, so a call of it must be in a failure context
a := class:
    Vals()<transacts>:int = 1 | 2
b := class:
    Vals()<transacts>:int = 7
Once(B : b)<transacts>:int = B.Vals() * 2
Twice(A : a)<transacts>:int = A.Vals() * 2
Main()<transacts>:void =
    Print("{Once(b{})}")
    Print("{Twice(a{})}")
