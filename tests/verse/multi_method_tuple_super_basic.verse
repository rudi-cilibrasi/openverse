# Renaming a class parameter does not leak the root name into a super tuple.
box(t:type) := class:
    Both(X:t,Y:t)<transacts>:t = X | Y
child(u:type) := class(box(u)):
    Both<override>(X:u,Y:u)<transacts>:u = (super:)Both((X,Y))
Main()<transacts>:void = for(V:=child(int){}.Both(3,4)){Print("{V}")}
