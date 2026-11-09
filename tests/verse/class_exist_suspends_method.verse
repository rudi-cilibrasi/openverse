# a <suspends> method of a class with a type parameter of its own, which
# overrides nothing: called as any method (#209)
base(t:type) := class:
    V:t
sub(t:type, u:type) := class(base(t)):
    W:u
    Run()<suspends>:u =
        Sleep(1.0)
        W
Main()<suspends>:void =
    B := sub(int, string){V := 1, W := "w"}
    Print(B.Run())
