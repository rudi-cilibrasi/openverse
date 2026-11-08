# a branching function called again through a reused frame, a branch ending on its own, and one stopped by a cancelled caller (#156)
Pulse(Tag:string, N:int)<suspends>:void =
    var Seen:int = 0
    branch:
        loop:
            Sleep(0.4)
            set Seen += 1
            Print("{Tag} pulse {Seen}")
    branch:
        Sleep(0.1)
        Print("{Tag} short branch done")
    Sleep(N * 1.0)
    Print("{Tag} exits after {Seen}")
Main()<suspends>:void =
    # the same call site three times: one frame, reset each time
    for (I := 1..3):
        Pulse("p{I}", 1)
    # a branching function in a race arm that loses
    R := race:
        block:
            Pulse("loser", 5)
            "loser"
        block:
            Sleep(1.0)
            "winner"
    Print(R)
    Sleep(2.0)
    Print("end")
