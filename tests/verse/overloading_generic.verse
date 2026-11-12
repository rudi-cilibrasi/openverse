# A bare generic parameter also accepts argument tuples. Required names
# distinguish it from fixed positional overloads (#501).

Describe(?X:t where t:type):string = "one value"
Describe(X:int, Y:int):string = "two ints {X + Y}"
Describe():string = "nothing"

Wrap(?X:t where t:type):?t = option{X}
Wrap(X:t, Times:int where t:type):[]t =
    var R:[]t = array{}
    for (I := 1..Times) { set R = R + array{X} }
    R

Main():void =
    Print(Describe(?X:=3))
    Print(Describe(?X:="s"))
    Print(Describe(1, 2))
    Print(Describe())
    if (V := Wrap(?X:=5)?) then Print("{V}")
    Print("{Wrap("a", 3).Length}")
