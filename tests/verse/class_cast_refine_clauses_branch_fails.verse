# a refining cast with clauses after it and an else, in a <decides> function whose branch fails after the condition: the call fails (the else does not run), as a branch's failure does (#286, review)
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 2
G(P:pair(a, b), K:int, X:a where a:type, b:type)<decides>:a =
    if (D := dup[P], K > 2):
        Print("in branch")
        D.C > 3
        D.A
    else:
        Print("else")
        X
Main():void =
    if (V := G[dup(int){A := 1, B := 2}, 5, 9]) then Print("v {V}") else Print("G failed")
    if (V := G[dup(int){A := 1, B := 2}, 1, 9]) then Print("v {V}") else Print("G failed")
