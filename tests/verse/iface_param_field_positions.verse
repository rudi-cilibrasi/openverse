# regression test from the #53 review (p24c)
holder(t:type) := interface:
    Item:t
base := class:
    X:int = 9
sub(t:type) := class(base, holder(t)):
    Y:int = 1
Show(H:holder(t) where t:type):t = H.Item
Main():void =
    Print(Show(sub(string){Item := "a"}))
