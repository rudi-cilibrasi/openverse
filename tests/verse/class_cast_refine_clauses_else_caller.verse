# a refining cast as the first clause, with an else that has a refining cast of its own, sets a var from outside, or is a value: the else runs once, in the caller, not under the refinement (#286)
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
opp(t:type, u:type) := class(pair(t, u)):
    D:int = 1
F(P:pair(a, b), K:int where a:type, b:type):int =
    if (D := dup[P], K > 3) then 1 else if (E := opp[P]) then 2 else 3
G(P:pair(a, b), K:int where a:type, b:type):int =
    var Seen:int = 0
    if (D := dup[P], K > 3) then Print("dup branch") else set Seen = 2
    Seen
H(P:pair(a, b), K:int where a:type, b:type):string =
    if (D := dup[P], K > 3) then "dup" else "other"
Main():void =
    Print("{F(dup(int){A := 1, B := 2}, 5)} {F(dup(int){A := 1, B := 2}, 1)} {F(opp(int, string){A := 1, B := "x"}, 5)} {F(pair(int, int){A := 1, B := 2}, 5)}")
    Print("{G(dup(int){A := 1, B := 2}, 5)} {G(dup(int){A := 1, B := 2}, 1)}")
    Print("{H(dup(int){A := 1, B := 2}, 5)} {H(dup(int){A := 1, B := 2}, 0)}")
