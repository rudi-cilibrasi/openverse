# expect: a map literal's key cannot fail
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){}
Key(N:int,?Default:?t=false where t:type)<decides>:?t={N>0;Default}
Choose(M:[?int]t,Other:t where t:type):t=Other
Bad(P:pair(a,b) where a:type,b:type)<decides>:b=
    Choose(map{Key[1]=>P.A},dup[P].B)
Main():void={}
