# expect: which a cast gives only as a clause of a failure context
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){}
Empty(?Default:?t=false where t:type):?t=Default
Bad(P:pair(a,b) where a:type,b:type):[?int]b=map{Empty()=>dup[P].B}
Main():void={}
