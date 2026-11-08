# an else: that starts a line belongs to the if whose line has its indentation (#159)
F2(A:int):int =
    if (A < 3):
        Print("a")
        if (A > 1):
            Print("b")
    else:
        Print("c")
    A
G(A:int):int =
    X := if (A > 0):
        1
    else:
        2
    Y := if (A > 5) then 10 else if (A > 0) then 5 else 0
    if (A > 100):
        Print("big")
    else if (A > 10):
        Print("medium")
        if (A > 50):
            Print("over fifty")
        else:
            Print("at most fifty")
    else:
        Print("small")
    X + Y
Main():void =
    Print("{F2(1)} {F2(2)} {F2(5)}")
    Print("{G(1)} {G(60)} {G(20)} {G(-1)}")
