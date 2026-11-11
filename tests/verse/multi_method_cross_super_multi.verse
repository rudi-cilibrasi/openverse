# The other multi-value family calls its inherited implementation directly.
base := class:
    Other()<transacts>:int = 3|4
    Values()<transacts>:int = 1|2
child := class(base):
    Other<override>()<transacts>:int = 30|40
    Values<override>()<transacts>:int = (super:)Other()|9
leaf := class(child) {}
Main():void =
    for(V:=leaf{}.Values()): Print("value {V}")
    for(V:=leaf{}.Other()): Print("virtual {V}")
    if(V:=first{W:=leaf{}.Values(),W=4,W})then Print("first {V}")
