# Tuple calls preserve instantiated parameter types and call boundaries (#448).
Note(N:int)<transacts>:int =
    Print("default")
    N
box(t:type) := class:
    Both(X:t,Y:?t,?K:int=Note(5))<transacts>:int = K | K+1
hidden(v:type) := class<abstract>(box(v)):
    Both<override>(X:v,Y:?v,?K:int=Note(9))<transacts>:int
Run(P:box(u),X:u where u:type)<transacts>:void = for(V:=P.Both((X,false))){Print("{V}")}
Main()<transacts>:void = Run(box(string){},"s")
