# expect: ToDiagnostic of a float (the shortest decimal that reads back is a Verse Core primitive not written yet) is not supported yet: a value of type point is converted to any, which holds a value of type float, in a program that calls ToDiagnostic
# A struct printed field by field: a float field is refused as a float is.
point := struct:
    X:int
    Y:float
Main():void =
    Print(ToDiagnostic(point{X := 1, Y := 2.0}).String)
