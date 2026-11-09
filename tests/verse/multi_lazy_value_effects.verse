# values that print, rejected by a for's filter and an if's clause: what they print is undone with them, as for a choice (#246)
Show(N:int)<computes>:int =
    Print("show {N}")
    N
Count(N:int)<computes><decides>:int =
    N > 0
    Show(N) | Count[N - 1]
Main():void =
    for (X := Count[3], X > 1):
        Print("for {X}")
    if (X := Count[3], X < 3):
        Print("if {X}")
