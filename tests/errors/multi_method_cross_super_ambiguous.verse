# expect: (super:)Other is ambiguous here: base.(left:)Other and base.(right:)Other
left := interface:
    Other()<transacts>:int=1
right := interface:
    Other()<transacts>:int=2
base := class(left,right):
    (left:)Other<override>()<transacts>:int=1
    (right:)Other<override>()<transacts>:int=2
child := class(base):
    Values()<transacts>:int=(super:)Other()|3
Main():void=for(V:=child{}.Values()):Print("{V}")
