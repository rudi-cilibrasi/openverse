pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)):
    C:int=0
box:=class:
    Value:int
Emit(E:event(int),N:int):int={E.Signal(N);N}
Select(X:int,?Index:int=0)<transacts>:int=Index
Constructor(P:pair(a,b),E:event(int) where a:type,b:type):[]int=
    for(X:array{1}){if(B:=box{Value:=dup[P].C})then Emit(E,B.Value)else 0}
Named(P:pair(a,b),E:event(int) where a:type,b:type):[]int=
    for(X:array{1}){if(Y:=Select(0,?Index:=dup[P].C))then Emit(E,Y)else 0}
Setter(P:pair(a,b),E:event(int) where a:type,b:type):[]int=
    var A:[]int=array{0}
    for(X:array{1}){if(Y:=set A[dup[P].C]=7)then Emit(E,Y)else 0}
Main()<suspends>:void=
    E:=event(int){}
    C:=Constructor(dup(int){},E)
    for(N:C){Print("constructor {N}")}
    M:=Named(dup(int){},E)
    for(N:M){Print("named {N}")}
    S:=Setter(dup(int){},E)
    for(N:S){Print("setter {N}")}
