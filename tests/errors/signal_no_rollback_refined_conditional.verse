# expect: this call may signal an event
# Refining helpers retain the surrounding rollback context even for a nonfailing body.
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)):
    Items:[]int=array{1,2}
    C:int=3
Emit(E:event(int),N:int)<transacts>:int=
    E.Signal(N)
    N
Values(P:pair(a,b),E:event(int),N:int where a:type,b:type):[]int=
    for(D:=dup[P],X:D.Items,Y:=(if(N>0)then(Emit(E,D.C)|D.C)else 0)){Y}
Main()<suspends>:void=
    E:=event(int){}
    ValuesNow:=Values(dup(int){},E,1)
    for(V:ValuesNow){Print("{V}")}
