# Calls through function values of a function with named parameters (#503):
# the explicit arguments run in the order written, then each omitted default
# once, at the call, in declaration order and in the function's scope (a
# module-level definition, earlier parameters), anew at every call.
log := class:
    var N:int = 0
    Next(What:string)<transacts>:int =
        set N += 1
        Print("{What} {N}")
        N
Base:int = 100
Steps(L:log, A:int, ?B:int = L.Next("default B"), ?C:int = B + Base, ?D:int = L.Next("default D")):string =
    "{A} {B} {C} {D}"
Main():void =
    L := log{}
    F:type{_(:log, :int, ?D:int, ?B:int):string} = Steps
    Print(F(L, L.Next("A"), ?D := L.Next("D"), ?B := L.Next("B")))
    G:type{_(:log, :int):string} = Steps
    Print("made")
    Print(G(L, L.Next("A")))
    Print(G(L, L.Next("A")))
    H:type{_(:log, :int, ?C:int):string} = Steps
    Print(H(L, 0, ?C := L.Next("C")))
