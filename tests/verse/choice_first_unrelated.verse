# (#283, #335) Where the first success is taken of a choice whose values are of unrelated
# classes, and the clauses after it are copied for each alternative (a method with several
# values, an overload picked by the class): in each copy the binding has its alternative's own
# class; after the condition, what it binds has the join of its types in the copies, an any
# for unrelated classes (which a function taking an any takes), and the others keep theirs.
a := class:
    M()<transacts>:int = 1 | 2
    Q():int = 7
b := class:
    M()<transacts>:int = 30 | 40
    Q():int = 8
c := class:
    G()<transacts>:int = 5 | 6
d := class:
    G()<transacts>:string = "x" | "y"
Dup(V:t where t:type):t = V | V
Tag(V:a):string = "a"
Tag(V:b):string = "b"
Take(V:any):void = Print("took")
Main()<transacts>:void =
    # an if with an else: X an int after it, A an any
    if (A := (Dup(a{}) | Dup(b{})), X := A.M(), X > 2):
        Take(A)
        Print("if {X}")
    else:
        Print("if none")
    if (A := (Dup(a{}) | Dup(b{})), X := A.M(), X > 99) { Print("never {X}") } else { Print("else") }
    # with no else, an overload picked by the class: T a string after it
    if (A := (Dup(b{}) | Dup(a{})), T := Tag(A), X := A.M(), X < 3):
        Print("tag {T} {X}")
    # first{…} and option{…}: their value is computed in each copy, at A's own class
    if (Y := first{A := (Dup(a{}) | Dup(b{})); X := A.M(); X > 30; A.Q() * 100 + X}) then Print("first {Y}")
    O := option{A := (Dup(a{}) | Dup(b{})); A.M() > 1; Tag(A)}
    if (V := O?) then Print("option {V}")
    # not, and the left of or
    if (not block{A := (Dup(a{}) | Dup(b{})); A.M() > 50}) then Print("not none above 50")
    Z := block{A := (Dup(a{}) | Dup(b{})); X := A.M(); X > 35; X} or -1
    Print("or {Z}")
    # an if's value, with a var set in its condition (an alternative that fails is undone)
    var N:int = 0
    R := if (A := (Dup(a{}) | Dup(b{})), X := A.M(), set N += X, X > 2) then X else 0
    Print("value {R} {N}")
    # a name of an int in one copy and a string in another: an any after them
    if (C := (Dup(d{}) | Dup(c{})), W := C.G(), K := 3):
        Take(W)
        Print("k {K}")
