# Parametric interfaces (#53): an interface's type arguments are those of
# its references; a class implements one at its own Verse Core type
# arguments, so dispatch and casts through the interface recover them.

container(t:type) := interface:
    Get():t
    Describe():string = "a container"
box(t:type) := class(container(t)):
    var Value:t
    Get<override>():t = Value
pair(t:type) := class(container(t)):
    First:t
    Second:t
    Get<override>():t = Second
    Describe<override>():string = "a pair"
All(Cs:[]container(t) where t:type):[]t = for (C : Cs) { C.Get() }
Main():void =
    Cs:[]container(int) = array{box(int){Value := 1}, pair(int){First := 2, Second := 3}}
    for (C : Cs) { Print("{C.Get()} {C.Describe()}") }
    Xs := All(Cs)
    Print("{Xs.Length}")
    Ss:[]container(string) = array{box(string){Value := "s"}}
    for (X : All(Ss)) { Print(X) }
    if (B := box[Cs[0]]):
        set B.Value = 7
        for (C : Cs) { Print("{C.Get()}") }
