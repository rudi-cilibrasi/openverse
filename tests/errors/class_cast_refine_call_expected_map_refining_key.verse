# expect: a map literal's key cannot fail
# A second independent refinement in the value must not hide the earlier
# key's failure when ordered call operands are lifted together.
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){}
animal:=class<abstract><unique>{}
dog:=class(animal){}
Echo(X:t,?Other:t=X where t:type):t=Other
Choose(X:t,Y:t,Other:u,Values:[dog]u where t:type,u:type):t=Y
Bad(P:pair(a,b),Q:pair(c,d),A:animal where a:type,b:type,c:type,d:type)<decides>:b=
    Choose(P.A,dup[P].B,Q.B,map{dog[A]=>Echo(Q.A,?Other:=dup[Q].B)})
Main():void={}
