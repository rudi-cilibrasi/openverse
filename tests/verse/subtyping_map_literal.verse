# map literals join their values, as array literals do (#67 review)
shape := class<abstract>:
    Area():int
square := class(shape):
    S:int
    Area<override>():int = S * S
circle := class(shape):
    R:int
    Area<override>():int = 3 * R * R
Main():void =
    M := map{1 => square{S := 2}, 2 => circle{R := 1}}
    for (K -> V : M) { Print("{K} {V.Area()}") }
