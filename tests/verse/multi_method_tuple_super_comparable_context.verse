# Tuple calls preserve instantiated parameter types and call boundaries (#448).
base(t:subtype(comparable)) := class:
    Count(M:[t]t,O:?t):int = M.Length | (if(V:=O?) then 10 else 20)
mid(u:subtype(comparable)) := class(base(u)):
    Count<override>(M:[u]u,O:?u):int = (super:)Count((map{},false))
Main():void = for(N:=mid(int){}.Count(map{},false)){Print("{N}")}