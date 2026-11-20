# A parametric class: instances at two types, a method using the type
# parameter, and a var field of the parameter's type.
# Tests LANGUAGE.md, Supported, Classes: "name(t:type) := class:".
# OpenVerse prints (Lean and C agree):
#   2 1 4 x
holder(t:type) := class:
    var Items:[]t = array{}
    Add(X:t)<transacts>:void =
        set Items += array{X}
    Count()<reads>:int = Items.Length

Main():void =
    I := holder(int){}
    S := holder(string){}
    I.Add(3)
    I.Add(4)
    S.Add("x")
    if (Second := I.Items[1], First := S.Items[0]):
        Print("OVPROBE {I.Count()} {S.Count()} {Second} {First}")
