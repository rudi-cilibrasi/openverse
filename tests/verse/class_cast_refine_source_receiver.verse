# An aliased receiver is evaluated before an argument which may suspend.
pair(a:type, b:type) := class:
    A:a
    B:b
    Read(N:int)<suspends>:int = N + 1
dup(t:type) := class(pair(t, t)):
    Read<override>(N:int)<suspends>:int = N + 2
Arg()<suspends>:int =
    Sleep(1.0)
    10
Run(P:pair(a, b), Replacement:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type)<suspends>:void =
    var R:pair(a, b) = P
    branch:
        Sleep(0.5)
        set R = Replacement
    if (E := dup[Q]):
        Print("receiver {R.Read(Arg())}")
Main()<suspends>:void =
    Run(dup(int){A := 1, B := 2}, pair(int, int){A := 3, B := 4}, dup(string){A := "a", B := "b"})
