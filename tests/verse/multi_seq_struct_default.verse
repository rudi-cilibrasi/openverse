# (#283) Choice points in sequence: a choice after its call of itself, in a <computes> function that prints (a struct's field default): taken lazily.
pt := struct<computes>:
    X:int = (Print("struct field"); 0)
Count(N:int)<computes><decides>:int =
    N > 0
    pt{}.X + N | Count[N - 1] + (0 | 1)
Main():void = if (X := Count[3], X < 3) then Print("first {X}")
