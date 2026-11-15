# expect: a map literal's key cannot fail
# Grouping valid argument casts must not hoist a later failable map key
# out of its literal and turn that forbidden key into an ordinary local.
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){}
animal:=class<abstract><unique>{}
dog:=class(animal){}
Choose(X:t,Y:t,Values:[dog]int where t:type):t=Y
Bad(P:pair(a,b),A:animal where a:type,b:type)<decides>:b=
    Choose(P.A,dup[P].B,map{dog[A]=>1})
Main():void={}
