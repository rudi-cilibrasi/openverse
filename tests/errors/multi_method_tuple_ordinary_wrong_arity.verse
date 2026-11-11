# expect: expected tuple(int, int), found tuple(int, int, int)
box(t:type) := class:
    Both(X:t,Y:t)<transacts>:t = X | Y
hidden(v:type) := class<abstract>(box(v)):
    Both<override>(X:v,Y:v)<transacts>:v
Main()<transacts>:void = for(V:=box(int){}.Both((1,2,3))){Print("{V}")}
