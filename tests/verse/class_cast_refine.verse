# Casts that hold only under a refinement of the type arguments (#243): the
# branch is typed under it (written types too), with its own effects and
# failure, nested, and one test per set of pins among the classes below.
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
dupInt := class(dup(int)):
    D:int = 9
counter := class:
    var N:int = 0
# (written types in the branch see the refinement: b is a there)
Swap(P:pair(a, b), X:a where a:type, b:type):b =
    if (D := dup[P]):
        Z:b = X
        Z
    else:
        P.B
# (a receiver that is no local; locals used inside, read only)
Make(X:t where t:type):pair(t, t) = dup(t){A := X, B := X, C := 5}
Pick(X:a, Y:b where a:type, b:type):b =
    var Seen:int = 1
    set Seen += 1
    if (D := dup[pair(a, b){A := X, B := Y}]) then (Print("seen {Seen}"); Y) else (Print("not dup, seen {Seen}"); Y)
# (a var from outside, read in the branch: its value when the cast runs)
Tally(P:pair(a, b), X:a where a:type, b:type):b =
    var Seen:int = 1
    set Seen += 1
    if (D := dup[P]) then (Print("seen {Seen}"); X) else P.B
# (effects in the branch: a var field, an allocation)
Count(P:pair(a, b), K:counter where a:type, b:type)<transacts>:int =
    if (D := dup[P]):
        set K.N += D.C
        K.N
    else:
        -1
# (a branch that fails, in a failure context)
Check(P:pair(a, b) where a:type, b:type)<decides>:int =
    if (D := dup[P]):
        D.C > 1
        D.C
    else:
        0
# (no else: a statement)
Note(P:pair(a, b) where a:type, b:type):void =
    if (D := dup[P]) { Print("dup {D.C}") }
    Print("noted")
# (a cast inside the branch of another)
Deep(P:pair(a, b), Q:pair(b, a), X:a where a:type, b:type):b =
    if (D := dup[P]):
        if (E := dup[Q]) then X else Q.A
    else:
        P.B
# (a class below with more pins: its own test)
Spec(P:pair(a, b), X:a where a:type, b:type):b =
    if (D := dup[P]) then X else P.B
Main():void =
    Print("{Swap(dup(int){A := 1, B := 2}, 10)} {Swap(pair(int, int){A := 1, B := 2}, 10)}")
    Print("{Pick(3, 4)}")
    Print("{Tally(dup(int){A := 1, B := 2}, 10)} {Swap(Make(5), 6)}")
    K := counter{}
    Print("{Count(dup(int){A := 1, B := 1, C := 3}, K)} {Count(pair(int, int){A := 1, B := 1}, K)} {K.N}")
    if (V := Check[dup(int){A := 1, B := 1, C := 3}]) then Print("check {V}")
    if (V := Check[dup(int){A := 1, B := 1, C := 1}]) then Print("check {V}") else Print("check failed")
    Note(dup(string){A := "a", B := "b", C := 7})
    Note(pair(string, int){A := "a", B := 1})
    Print("{Deep(dup(int){A := 1, B := 1}, dup(int){A := 2, B := 2}, 10)} {Deep(dup(int){A := 1, B := 1}, pair(int, int){A := 2, B := 3}, 10)}")
    Print("{Spec(dupInt{A := 1, B := 1}, 10)} {Spec(dup(int){A := 1, B := 1}, 11)}")
