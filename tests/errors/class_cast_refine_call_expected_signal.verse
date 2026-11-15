# expect: this call may signal an event
# Expected-result recovery must retain the no-rollback admission boundary
# when the discovered cast moves the remaining call operands into its branch.
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){}
Echo(X:t,?Other:t=X where t:type):t=Other
Keep(X:t,N:int where t:type):t=X
Emit(E:event(int)):int={E.Signal(1);0}
Bad(P:pair(a,b),E:event(int) where a:type,b:type)<decides>:b=
    Echo(P.A,?Other:=Keep(dup[P].B,Emit(E)))
Main():void={}
