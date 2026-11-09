# A method with several values of a class in a module (#283)
geo := module:
    pt<public> := class:
        X<public> : int
        Near<public>()<transacts>:int = X - 1 | X + 1
Main()<transacts>:void =
    P := geo.pt{X := 10}
    for (V := P.Near()):
        Print("{V}")
