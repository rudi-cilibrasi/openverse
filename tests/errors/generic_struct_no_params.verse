# expect: struct point takes no type arguments
point := struct:
    X:int = 0

Main():void =
    P := point(int){}
