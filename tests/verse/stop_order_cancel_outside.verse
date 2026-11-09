# exit by cancellation from outside: a task cancelled while its function has (#254, from the review of #258)
# live nested branches (and while it waits in a rush whose arm started one)
F()<suspends>:int =
    defer:
        Print("F defer")
    branch:
        defer:
            Print("A defer")
        Sleep(0.1)
        branch:
            defer:
                Print("A.1 defer")
            Sleep(5.0)
        Sleep(5.0)
    branch:
        defer:
            Print("B defer")
        Sleep(5.0)
    Sleep(5.0)
    0
G()<suspends>:int =
    defer:
        Print("G defer")
    branch:
        defer:
            Print("A defer")
        Sleep(0.1)
        branch:
            defer:
                Print("A.1 defer")
            Sleep(5.0)
        Sleep(5.0)
    X := rush:
        block:
            defer:
                Print("r1 defer")
            branch:
                defer:
                    Print("r1.b defer")
                Sleep(5.0)
            Sleep(5.0)
            1
        block:
            defer:
                Print("r2 defer")
            Sleep(5.0)
            2
    X
H()<suspends>:int =
    defer:
        Print("H defer")
    G()
Main()<suspends>:void =
    T := spawn{F()}
    Sleep(1.0)
    T.Cancel()
    Print("cancelled F")
    U := spawn{H()}
    Sleep(1.0)
    U.Cancel()
    Print("cancelled H")
