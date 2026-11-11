# Tuple calls preserve instantiated parameter types and call boundaries (#448).
cell(t:type) := struct { V:t }
base(t:type) := class:
    Count(X:t,Y:[]t):int = Y.Length | Y.Length+1
mid(u:type) := class(base(tuple(int,cell(u)))):
    Count<override>(X:tuple(int,cell(u)),Y:[]tuple(int,cell(u))):int = X(0)+Y.Length | X(0)+Y.Length+1
leaf(v:type) := class(mid(v)):
    Count<override>(X:tuple(int,cell(v)),Y:[]tuple(int,cell(v))):int = (super:)Count((X,array{}))
Main():void = for(N:=leaf(string){}.Count((7,cell(string){V:="s"}),array{})){Print("{N}")}