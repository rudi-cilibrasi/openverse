# Initial values of class variables (#37): one prototype per class, made
# once before Main, in an order where each refers only to earlier ones
# (`wheel` before `car`, though `car` comes first), and a variable of a
# class type starts as a reference to one: no allocation per call.

car := class:
    Front:wheel
    Back:wheel
    var Miles:int = 0
wheel := class:
    Size:int

Drive(C:car, N:int):int =
    # `D` is a car variable, which starts as the prototype car
    var D:car = C
    for (I := 1..N) { set D.Miles += I }
    D.Miles

Main():void =
    C := car{Front := wheel{Size := 16}, Back := wheel{Size := 17}}
    var Total:int = 0
    for (K := 1..1000) { set Total += Drive(C, 3) }
    Print("{C.Miles} {Total} {C.Front.Size + C.Back.Size}")
