# Tuple calls preserve instantiated parameter types and call boundaries (#448).
base(t:type) := class:
    Count(X:t,Y:[]t):int = Y.Length | Y.Length+1
mid(u:type) := class(base(int)):
    Count<override>(X:int,Y:[]int):int = X+Y.Length | X+Y.Length+10
leaf(t:type) := class(mid(t)):
    Count<override>(X:int,Y:[]int):int = (super:)Count((X,array{}))
Main():void = for(N:=leaf(string){}.Count(3,array{})){Print("{N}")}