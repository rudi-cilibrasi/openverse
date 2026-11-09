# Casts that refine (#243): the object's evaluation is part of the cast's
# condition (rolled back, and taking the else, when the cast fails); a type
# parameter only the branch's written types mention; the refinements of
# enclosing casts in a nested branch's written types.
pair(a:type, b:type) := class:
    A:a
    B:b
dup(a:type) := class(pair(a, a)):
    C:int = 0
Recv(P:pair(a, b) where a:type, b:type):int =
    if (D := dup[(Print("receiver"); P)]) then 1 else 2
First(Ps:[]pair(a, b) where a:type, b:type):int =
    if (D := dup[Ps[0]]) then 1 else 2
Written(P:pair(a, b), Unused:c where a:type, b:type, c:type):int =
    if (D := dup[P]):
        A:[]c = array{}
        A.Length
    else:
        2
Nested(P:pair(a, b), Q:pair(b, c), X:a where a:type, b:type, c:type):c =
    if (D := dup[P]):
        if (E := dup[Q]):
            Z:b = X
            Z
        else:
            Q.B
    else:
        Q.B
Main():void =
    Print("{Recv(pair(int, int){A := 1, B := 2})}")
    Print("{Recv(dup(int){A := 1, B := 2})}")
    E:[]pair(int, int) = array{}
    Print("{First(E)} {First(array{dup(int){A := 1, B := 1}})}")
    Print("{Written(dup(int){A := 1, B := 2}, "x")} {Written(pair(int, int){A := 1, B := 2}, "x")}")
    Print("{Nested(dup(int){A := 1, B := 2}, dup(int){A := 3, B := 4}, 7)} {Nested(dup(int){A := 1, B := 2}, pair(int, int){A := 3, B := 4}, 7)}")
