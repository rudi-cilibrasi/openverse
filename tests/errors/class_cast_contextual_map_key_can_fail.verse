# expect: a map literal's key cannot fail
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){}
Echo(X:t,?Other:t=X where t:type):t=Other
Key(N:int,?Default:?t=false where t:type)<decides>:?t={N>0;Default}
Bad(P:pair(a,b) where a:type,b:type)<decides>:[?int]b=map{Key[1,?Default:=option{0}]=>Echo(P.A,?Other:=dup[P].B)}
Main():void={}
