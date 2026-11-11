# The final set gives a value. A void else makes the if a statement.
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 7
Update(P:pair(a, b) where a:type, b:type):int =
    var Value:int = 1
    if (D := dup[P]):
        set Value = D.C
    else:
        set Value = 2
        Print("miss")
    Value
TryUpdate(P:pair(a, b), Index:int where a:type, b:type)<transacts><decides>:int =
    var Values:[]int = array{3}
    if (D := dup[P]):
        set Values[Index] = D.C
    else:
        Print("no update")
    Values[0]
Main():void =
    Match := dup(int){A := 1, B := 2}
    Miss := pair(int, string){A := 1, B := "b"}
    Print("match {Update(Match)}")
    Print("miss {Update(Miss)}")
    if (V := TryUpdate[Match, 0]) then Print("index {V}")
    if (V := TryUpdate[Match, 1]) then Print("unexpected {V}") else Print("index failed")
    if (V := TryUpdate[Miss, 1]) then Print("untouched {V}")
