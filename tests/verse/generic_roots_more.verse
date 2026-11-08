# specialising: through generic callers, recursion at the same type, a
# generic method with a branch, spawning a dispatch in generic code, and a
# generic function never called (#174)
box(t:type) := class:
    V:t
    Get()<suspends>:t =
        Sleep(1.0)
        V
    Watch(N:int)<suspends>:t =
        branch:
            Sleep(0.5)
            Print("box watch")
        Sleep(1.0 * N)
        V
sub(t:type) := class(box(t)):
    Get<override>()<suspends>:t =
        Sleep(2.0)
        Print("sub get")
        V
Outer(X:t, N:int where t:type)<suspends>:t =
    if (N > 0) then Outer(X, N - 1) else Inner(X)
Inner(X:t where t:type)<suspends>:t =
    branch:
        Sleep(0.1)
        Print("inner branch")
    Sleep(0.5)
    X
SpawnGet(B:box(t) where t:type)<suspends>:t =
    T := spawn{B.Get()}
    T.Await()
Never(X:t where t:type)<suspends>:t =
    branch:
        Sleep(1.0)
    X
Main()<suspends>:void =
    Print("{Outer(1, 3)}")
    Print("{Outer("x", 1)}")
    Print("{Inner(2.5)}")
    Print("{box(int){V := 7}.Watch(1)}")
    Print("{SpawnGet(sub(string){V := "s"})}")
    Print("{SpawnGet(box(int){V := 3})}")
