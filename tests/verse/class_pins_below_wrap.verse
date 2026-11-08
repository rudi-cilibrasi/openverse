# classes below one that fixes or repeats type arguments, which wrap their
# own type parameter: they take its pins where theirs would relate their
# arguments to one past their parent's (#209)
pair(t:type, u:type) := class:
    A:t
    B:u
    Get():t = A
    Name():string = "pair"
pint(u:type) := class(pair(int, u)):
    Name<override>():string = "pint {A}"
wrapint(w:type) := class(pint([]w)):
    C:w
dup(t:type) := class(pair(t, t)):
    Get<override>():t = B
optdup(u:type) := class(dup(?u)):
    C:u
arrdup(u:type) := class(dup([]u)):
    C:u
Show(P:pair(t, u) where t:type, u:type):string = P.Name()
First(P:pair(t, u) where t:type, u:type):t = P.Get()
Last(Ps:[]pair(int, []string)):string =
    var Cur:?pair(int, []string) = false
    for (P : Ps) { set Cur = option{P} }
    if (C := Cur?) then C.Name() else "none"
Main():void =
    Print(Show(wrapint(string){A := 1, B := array{"x"}, C := "c"}))
    Print(Show(pint(int){A := 2, B := 3}))
    Print(Last(array{wrapint(string){A := 4, B := array{"y"}, C := "d"}}))
    if (X := First(optdup(int){A := false, B := option{5}, C := 1})?) then Print("{X}")
    Print("{First(arrdup(int){A := array{1}, B := array{2, 3}, C := 1}).Length}")
