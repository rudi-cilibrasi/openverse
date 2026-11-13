# expect: <internal> is not allowed on a struct's field: a struct's fields are public
# (Book of Verse ch. 9: "All struct fields are public"; v1-PublicStructFields: 3594)
point := struct:
    X<internal>:int = 0
Main():void = Print("{point{}.X}")
