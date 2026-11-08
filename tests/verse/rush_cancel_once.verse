# a rush's running arm is unwound once when its function is cancelled,
# by a race or by T.Cancel(), and when another arm returns from the
# function (#181)
F()<suspends>:int =
    rush:
        block:
            Sleep(1.0)
            1
        block:
            defer:
                Print("loser unwound")
            Sleep(3.0)
            2
R()<suspends>:int =
    rush:
        block:
            Sleep(0.5)
            return 7
        block:
            defer:
                Print("other unwound")
            Sleep(3.0)
            2
    0
Main()<suspends>:void =
    Z := race:
        F()
        block:
            Sleep(0.5)
            3
    Print("{Z}")
    T := spawn{F()}
    Sleep(0.5)
    T.Cancel()
    Print("cancelled")
    Print("{R()}")
    Sleep(4.0)
    Print("end")
