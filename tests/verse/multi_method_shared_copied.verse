# (#283, #335) Methods of one name with several values in unrelated classes,
# called on the value of a choice whose alternatives are of those classes:
# the clauses after it are copied for each alternative, where the
# receiver's class picks the family (it compiled before, and stopped with
# `error: user` at a call of a family's stub). Also with b.M of one value,
# in the body, and with a later clause that needs each alternative's type.
a := class:
    M()<transacts>:int = 1 | 2
b := class:
    M()<transacts>:int = 30 | 40
c := class:
    M()<transacts>:int = 500
Dup(V:t where t:type):t = V | V
Tag(V:a):string = "a"
Tag(V:b):string = "b"
Main()<transacts>:void =
    for (A := (Dup(a{}) | Dup(b{})), X := A.M()) { Print("x {X}") }
    for (A := (a{} | Dup(c{})), X := A.M()) { Print("y {X}") }
    for (A := (Dup(a{}) | Dup(b{}))) { for (X := A.M()) { Print("z {X}") } }
    for (A := (Dup(a{}) | b{}), X := A.M(), T := Tag(A)) { Print("w {X} {T}") }
