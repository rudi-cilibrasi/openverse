# expect: 6:9: struct point has no field 'Z'
# A parenthesized type's construction checks its fields as any other does.
point := struct:
    X:int = 1
Main():void =
    P := (point){Z := 2}
