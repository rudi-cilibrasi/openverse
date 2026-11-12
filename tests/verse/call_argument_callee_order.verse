# Snapshot callable values before a tuple producer can replace them.
Zero():int=block{Print("zero");7}
One():int=block{Print("one");8}
Get():type{_():int}=block{Print("callee");Zero}
Unit():tuple()=Print("unit")
holder:=class:
    var F:type{_():int}=Zero
Change(H:holder):tuple()=
    Print("change")
    set H.F=One
Main():void=
    Print("{Get()(Unit())}")
    H:=holder{}
    Print("{H.F(Change(H))}")
    Print("{H.F()}")
