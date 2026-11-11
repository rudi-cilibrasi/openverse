# Tuple calls preserve instantiated parameter types and call boundaries (#448).
Note(S:string,N:int)<transacts>:int =
    Print(S)
    N
base(t:type) := class:
    Pick(X:t,Y:?t,?K:int=Note("root",1))<transacts>:int = K | K+1
mid(u:type) := class(base(u)):
    Pick<override>(X:u,Y:?u,?K:int=Note("mid",5))<transacts>:int = K+10 | K+20
leaf(v:type) := class(mid(v)):
    Pick<override>(X:v,Y:?v,?K:int=Note("leaf",9))<transacts>:int = (super:)Pick((X,false))
Main()<transacts>:void =
    for(N:=leaf(int){}.Pick(7,false)){Print("{N}")}
    for(N:=leaf(int){}.Pick(7,false,?K:=99)){Print("named {N}")}