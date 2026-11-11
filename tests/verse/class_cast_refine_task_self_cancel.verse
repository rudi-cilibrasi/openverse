# A task started by the helper can cancel its running source owner at once.
pair(a:type, b:type) := class {}
dup(t:type) := class(pair(t, t)) {}
Run(P:pair(a, b), Me:event(task(int)) where a:type, b:type)<suspends>:int =
    var X:int = 0
    defer: Print("self source defer {X}")
    T := Me.Await()
    if (D := dup[P]):
        defer: Print("self cast defer {X}")
        branch:
            defer: Print("self child defer {X}")
            T.Cancel()
            Print("self requested")
            Sleep(0.5)
            Print("unreachable child")
        set X = 7
        Print("self helper continues")
        Sleep(1.0)
        Print("unreachable helper")
    0
Main()<suspends>:void =
    Me := event(task(int)){}
    T := spawn{Run(dup(int){}, Me)}
    Me.Signal(T)
    Sleep(2.0)
    T.Cancel()
    Print("self end")
