# regression test from the #39 review (p08_default_names)
stack(t:type) := class:
    var Items:[]t = array{}
    Size():int = Items.Length
base(t:type) := class:
    var S:stack(t) = stack(t){}
    var O:?t = false
sub(u:type) := class(base(u)):
    Extra:int = 0
Main():void =
    X := sub(int){}
    set X.S = stack(int){Items := array{1, 2}}
    Print("{X.S.Size()}")
    Y := sub(string){}
    Print("{Y.S.Size()}")
