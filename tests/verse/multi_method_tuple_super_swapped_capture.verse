# Tuple calls preserve instantiated parameter types and call boundaries (#448).
base(a:type,b:type) := class:
    Pair(X:a,Y:b):tuple(a,b) = (X,Y) | (X,Y)
mid(x:type,y:type) := class(base(y,x)):
    Pair<override>(X:y,Y:x):tuple(y,x) = (X,Y) | (X,Y)
leaf(a:type,b:type) := class(mid(a,b)):
    Pair<override>(X:b,Y:a):tuple(b,a) = (super:)Pair((X,Y))
Main():void = for(P:=leaf(int,string){}.Pair("s",7)){Print("{P(0)} {P(1)}")}