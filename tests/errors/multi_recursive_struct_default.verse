# expect: 4:0: Count has several values and is recursive, or called by a recursive one, and it may print
pt := struct:
    X:int = (Print("struct field"); 0)
Count(N:int)<computes><decides>:int =
    N > 0
    pt{}.X + N | Count[N - 1]
Main():void = if (X := Count[3], X < 3) then Print("first {X}")
