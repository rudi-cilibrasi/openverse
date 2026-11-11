# A failed return operand keeps its effects and runs neither cleanup.
pair(a:type,b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t,t)):
    C:int = 4
counter := class:
    var N:int = 0
Operand(H:counter,V:int)<transacts><decides>:int =
    set H.N += V
    Print("operand {V} {H.N}")
    false?
    V
Run(P:pair(a,b),H:counter where a:type,b:type)<transacts><decides>:int =
    defer: Print("unexpected source cleanup")
    for (V := if (D := dup[P]) then (D.C | D.C + 1) else 0):
        defer: Print("unexpected body cleanup")
        Print("body {V}")
        return Operand[H,V]
    -1
Main()<transacts><decides>:void =
    Print("result {Run[dup(int){A:=1,B:=2},counter{}]}")
