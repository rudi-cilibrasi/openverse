# The selected branch of a refining if stays outside its condition's failure context.
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=3}
Emit(E:event(int),N:int):int={E.Signal(N);N}
Value(P:pair(a,b),E:event(int) where a:type,b:type):int=
    if(D:=dup[P])then Emit(E,D.C)else 0
Main()<suspends>:void=
    E:=event(int){}
    V:=Value(dup(int){},E)
    Print("{V}")
