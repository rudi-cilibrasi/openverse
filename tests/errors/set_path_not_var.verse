# expect: 'P' is not a var
vector2 := struct:
    X:int = 0
holder := struct:
    V:vector2 = vector2{}
Main():void =
    P:holder = holder{}
    set P.V.X = 1
