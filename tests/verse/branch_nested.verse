# a branch inside a branch: each wrapper drives its own arm (#156)
Outer()<suspends>:void =
    branch:
        branch:
            loop:
                Sleep(1.0)
                Print("inner tick")
        loop:
            Sleep(1.5)
            Print("outer tick")
    Sleep(3.2)
    Print("outer exits")
Main()<suspends>:void =
    Outer()
    Sleep(2.0)
    Print("end")
