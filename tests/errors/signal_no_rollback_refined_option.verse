# expect: this call may signal an event
# Refining helpers retain the surrounding rollback context even for a nonfailing body.
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=3}
Emit(E:event(int),N:int):int={E.Signal(N);N}
F(P:pair(a,b),E:event(int) where a:type,b:type):?int=option{D:=dup[P];Emit(E,D.C)}
Main()<suspends>:void={}
