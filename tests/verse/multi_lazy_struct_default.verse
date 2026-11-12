# a value that prints through a struct field's default, rejected by the if's next clause: undone with it (#246)
pt := struct<computes>:
    X:int = (Print("struct field"); 0)
Count(N:int)<computes><decides>:int =
    N > 0
    pt{}.X + N | Count[N - 1]
Main():void = if (X := Count[3], X < 3) then Print("first {X}")
