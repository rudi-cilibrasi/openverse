# Tuple calls preserve instantiated parameter types and call boundaries (#448).
box(t:type) := class:
    Both(X:t,Y:t)<transacts>:t = X | Y
hidden(v:type) := class<abstract>(box(v)):
    Both<override>(X:v,Y:v)<transacts>:v
Run(P:box(u),X:u,Y:u where u:type)<transacts>:[]u = for(V:=P.Both((X,Y))){V}
Main()<transacts>:void = for(V:Run(box(int){},3,4)){Print("{V}")}
