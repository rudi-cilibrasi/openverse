# Methods with several values of one name in a module's classes and the
# program's (#283): each class's own family, picked by the receiver's class,
# the module's line.Near an ordinary method.
geo := module:
    pt<public> := class:
        X<public> : int
        Near<public>()<transacts>:int = X - 1 | X + 1
    line<public> := class:
        Near<public>()<transacts>:int = 0
plain := class:
    Near()<transacts>:int = 5 | 6
Main()<transacts>:void =
    P := geo.pt{X := 10}
    for (V := P.Near()):
        Print("{V}")
    Print("{geo.line{}.Near()}")
    for (V := plain{}.Near(), W := P.Near()):
        Print("p {V} {W}")
