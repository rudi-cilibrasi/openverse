# expect: this call may signal an event
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)):
    C:int=0
box:=class:
    Value:int
Emit(E:event(int),N:int)<transacts>:int={E.Signal(N);N}
Select(X:int,?Index:int=0)<transacts>:int=Index
Values(P:pair(a,b),E:event(int) where a:type,b:type):[]int=
    var A:[]int=array{0}
    for(X:array{1},Y:=Select(0,?Index:=Emit(E,dup[P].C))){Y}
Main()<suspends>:void=
    E:=event(int){}
    Now:=Values(dup(int){},E)
    for(N:Now){Print("{N}")}
