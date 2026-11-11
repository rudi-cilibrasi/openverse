# Tuple calls preserve instantiated parameter types and call boundaries (#448).
base(a:type,b:type) := interface:
    Pick(X:a,Y:b)<transacts>:int = 1 | 2
deep(u:type,v:type) := interface(base(v,u)):
    Pick<override>(X:v,Y:u)<transacts>:int = 30 | 40
parent(x:type,y:type) := class(base(y,x)):
    Pick<override>(X:y,Y:x)<transacts>:int = 10 | 20
leaf(p:type,q:type) := class(parent(p,q),deep(p,q)):
    Pick<override>(X:q,Y:p)<transacts>:int = (super:)Pick((X,Y))
Main()<transacts>:void = for(N:=leaf(int,string){}.Pick("s",7)){Print("{N}")}