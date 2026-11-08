# spawning a method whose implementations are generic, below and above the
# receiver's class, and one of a class that fixes the type argument (#173)
box(t:type) := class:
    V:t
    Get()<suspends>:t =
        Sleep(1.0)
        V
sub(t:type) := class(box(t)):
    Get<override>()<suspends>:t =
        Sleep(2.0)
        Print("sub get")
        V
int_box := class(box(int)):
    Get<override>()<suspends>:int = V + 100
Main()<suspends>:void =
    B:box(string) = sub(string){V := "s"}
    T := spawn{B.Get()}
    C:box(int) = box(int){V := 3}
    U := spawn{C.Get()}
    D:box(int) = int_box{V := 3}
    W := spawn{D.Get()}
    Print("{W.Await()} {U.Await()} {T.Await()}")
