# expect: this call may signal an event
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){}
Echo(X:t,?Other:t=X where t:type):t=Other
Key(E:event(int),?Default:?t=false where t:type):?t={E.Signal(1);Default}
Build(P:pair(a,b),E:event(int) where a:type,b:type)<decides>:[?int]b=map{Key(E)=>Echo(P.A,?Other:=dup[P].B)}
Main():void={}
