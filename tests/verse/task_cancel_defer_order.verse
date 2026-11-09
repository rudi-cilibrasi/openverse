# Defers of a task cancelled at its first wait, inside calls and blocks:
# innermost first. Expected: H inner / H defer / G defer / F defer /
# main goes on / Main defer
W()<suspends>:int =
    Sleep(9.0)
    1
H(T:task(int))<suspends>:int =
    defer:
        Print("H defer")
    block:
        defer:
            Print("H inner")
        T.Await()
G(T:task(int))<suspends>:int =
    defer:
        Print("G defer")
    H(T) + 1
F()<suspends>:int =
    defer:
        Print("F defer")
    T := spawn{W()}
    T.Cancel()
    G(T)
Main()<suspends>:void =
    defer:
        Print("Main defer")
    spawn{F()}
    Sleep(0.1)
    Print("main goes on")
