# expect: castable_subtype(C): C is not <castable>
C := class{}
X:castable_subtype(C) = C
Main():void = {}
