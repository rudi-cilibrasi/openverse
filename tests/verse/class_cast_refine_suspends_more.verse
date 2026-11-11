# Refining casts in <suspends> functions (#243): a branch cancelled in a race (its defer, then the
# function's), a cast that opens type arguments (#250), a cast from a reference through views (#351)
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
H(P:pair(a, b) where a:type, b:type)<suspends>:int =
    defer: Print("h defer")
    if (D := dup[P]):
        defer: Print("branch defer")
        Sleep(10.0)
        1
    else:
        0
expr(t:type) := class:
    K:int = 0
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:a
    R:b
Op(E:expr(t) where t:type)<suspends>:int =
    if (P := pairE[E]):
        Sleep(1.0)
        P.K + 100
    else:
        -1
container(t:type) := interface:
    Get():t
sink(u:type) := interface:
    Put(X:u):int
both(t:type, u:type) := class(container(t), sink(u)):
    V:t
    Get<override>():t = V
    Put<override>(X:u):int = 1
one(u:type) := class(sink(u)):
    W:u
    Put<override>(X:u):int = 100
VW(S:sink(string))<suspends>:string =
    if (O := one[S]):
        Sleep(0.5)
        "one {O.W}"
    else:
        "not one"
Main()<suspends>:void =
    R := race:
        H(dup(int){A := 1, B := 2})
        block:
            Sleep(1.0)
            2
    Print("race {R}")
    Print("op {Op(pairE(int, string){L := 1, R := "r", K := 5})} {Op(expr(int){})}")
    Print("{VW(one(string){W := "w"})} {VW(both(int, string){V := 1})}")
