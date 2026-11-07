# regression test from the #53 review (p27)
holder(t:type) := interface:
    Item:t
    Peek():t = Item
base := class:
    X:int = 9
sub(t:type) := class(base, holder(t)):
    Y:int = 1
Main():void =
    H := sub(string){Item := "a"}
    Print(H.Peek())
