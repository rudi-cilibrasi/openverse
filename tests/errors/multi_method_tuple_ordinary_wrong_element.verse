# expect: expected tuple(string, string), found tuple(int, string)
box(t:type) := class:
    Both(X:t,Y:t)<transacts>:t = X | Y
hidden(v:type) := class<abstract>(box(v)):
    Both<override>(X:v,Y:v)<transacts>:v
Main()<transacts>:void = for(V:=box(string){}.Both((1,"s"))){Print("{V}")}
