# expect: 'P' is not a var
vector2 := struct<computes>:
    X:int = 0
holder := struct<computes>:
    V:vector2 = vector2{}
Main():void =
    P:holder = holder{}
    set P.V.X = 1
