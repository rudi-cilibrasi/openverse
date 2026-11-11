# Tuple calls preserve instantiated parameter types and call boundaries (#448).
base(a:type,b:type) := class:
    Count(X:[]a,Y:?b):int = X.Length | (if(V:=Y?) then 7 else 9)
mid(t:type) := class(base(t,t)):
    Count<override>(X:[]t,Y:?t):int = X.Length | (if(V:=Y?) then 7 else 9)
leaf(u:type) := class(mid(u)):
    Count<override>(X:[]u,Y:?u):int = (super:)Count((array{},false))
Main():void =
    for(N:=leaf(int){}.Count(array{},false)){Print("i {N}")}
    for(N:=leaf(string){}.Count(array{},false)){Print("s {N}")}