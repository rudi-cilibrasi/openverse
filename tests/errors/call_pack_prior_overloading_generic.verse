# expect: parameters a call cannot tell apart
# generic overloads: a type parameter overlaps every type, so a generic
# overload is told apart by its number of parameters

Describe(X:t where t:type):string = "one value"
Describe(X:int, Y:int):string = "two ints {X + Y}"
Describe():string = "nothing"

Wrap(X:t where t:type):?t = option{X}
Wrap(X:t, Times:int where t:type):[]t =
    var R:[]t = array{}
    for (I := 1..Times) { set R = R + array{X} }
    R

Main():void =
    Print(Describe(3))
    Print(Describe("s"))
    Print(Describe(1, 2))
    Print(Describe())
    if (V := Wrap(5)?) then Print("{V}")
    Print("{Wrap("a", 3).Length}")
