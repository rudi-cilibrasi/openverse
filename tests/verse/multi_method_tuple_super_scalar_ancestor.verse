# Tuple calls preserve instantiated parameter types and call boundaries (#448).
base(t:type) := class:
    Pick(X:t,Y:t):int = 1 | 2
mid(u:type) := class(base(u)):
    Pick<override>(X:u,Y:u):int = 9
leaf(v:type) := class(mid(v)):
    Pick<override>(X:v,Y:v):int = (super:)Pick((X,Y))
Main():void = for(N:=leaf(int){}.Pick(1,2)){Print("{N}")}