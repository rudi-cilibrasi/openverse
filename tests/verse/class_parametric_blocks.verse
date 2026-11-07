# block: clauses of parametric classes (#39): generic, run at the new
# object's type arguments, those of the classes above first.

counter(t:type) := class:
    Label:t
    var Hits:int = 0
    block:
        set Hits = 1
        Print("made a counter")
sub(t:type) := class(counter(t)):
    block:
        set Hits += 10
intsub := class(sub(int)):
    block:
        set Hits += 100
Make(L:t where t:type):counter(t) = counter(t){Label := L}
Main():void =
    C := counter(string){Label := "a"}
    Print("{C.Hits}")
    S := sub(int){Label := 5}
    Print("{S.Hits} {S.Label}")
    I := intsub{Label := 6}
    Print("{I.Hits}")
    M := Make("m")
    Print("{M.Hits} {M.Label}")
