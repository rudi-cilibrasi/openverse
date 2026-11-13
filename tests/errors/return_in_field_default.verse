# expect: return is not allowed in a field's default (of 'X' in point)
# (it would leave the function that constructs the object)
point := struct:
    X:int = return 0
F():int =
    P := point{}
    7
Main():void = Print("{F()}")
