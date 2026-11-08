# a copy of a generic immediate method whose spawn is a dispatch (#174)
box(t:type) := class:
    V:t
    Get()<suspends>:t =
        Sleep(1.0)
        V
    Kick():task(t) = spawn{Get()}
sub(t:type) := class(box(t)):
    Get<override>()<suspends>:t =
        Sleep(2.0)
        Print("sub get")
        V
Main()<suspends>:void =
    B:box(int) = sub(int){V := 9}
    T4 := B.Kick()
    Print("{T4.Await()}")
