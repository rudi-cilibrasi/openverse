# Tuple calls preserve instantiated parameter types and call boundaries (#448).
base(t:type) := class:
    Count(X:[int][]t,Y:?t):int = X.Length | (if(V:=Y?) then 10 else 20)
mid(u:type) := class(base(u)):
    Count<override>(X:[int][]u,Y:?u):int = (super:)Count((map{},false)) + 100
Main():void = for(N:=mid(string){}.Count(map{},false)){Print("{N}")}