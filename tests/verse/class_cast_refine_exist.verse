# Casts that refine (#243) to a class with classes below that add type
# parameters of their own: the branch needs none of those, so a test opens
# only what all of its classes add.
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
dupX(t:type, u:type) := class(dup(t)):
    Extra:u
dupA(t:type) := class<abstract>(pair(t, t)):
    C:int = 0
dupY(t:type, u:type) := class(dupA(t)):
    Extra:u
Same(P:pair(a, b), X:a where a:type, b:type):b =
    if (D := dup[P]) then X else P.B
SameA(P:pair(a, b), X:a where a:type, b:type):b =
    if (D := dupA[P]) then X else P.B
Main():void =
    Print("{Same(dupX(int, string){A := 1, B := 2, Extra := "e"}, 10)} {Same(dup(int){A := 1, B := 2}, 11)} {Same(pair(int, int){A := 1, B := 2}, 12)}")
    Print("{SameA(dupY(int, string){A := 1, B := 2, Extra := "e"}, 10)} {SameA(pair(int, int){A := 1, B := 2}, 12)}")
