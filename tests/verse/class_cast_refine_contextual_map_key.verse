# Generic empty keys keep the literal's expected key type through value casts.
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){}
Echo(X:t,?Other:t=X where t:type):t=Other
Empty(?Default:?t=false where t:type):?t=Default
reader:=class{Pick(?Default:?t=false where t:type):?t=Default}
holder(t:type):=struct{M:[?int]t}
Direct(P:pair(a,b) where a:type,b:type)<decides>:[?int]b=map{Empty()=>Echo(P.A,?Other:=dup[P].B)}
Bound(P:pair(a,b) where a:type,b:type)<decides>:[?int]b=
    M:[?int]b=map{Empty()=>Echo(P.A,?Other:=dup[P].B)}
    M
Use(M:[?int]t where t:type)<decides>:t=M[false]
Call(P:pair(a,b) where a:type,b:type)<decides>:b=Use[map{Empty()=>Echo(P.A,?Other:=dup[P].B)}]
Method(P:pair(a,b) where a:type,b:type)<decides>:[?int]b=map{reader{}.Pick()=>Echo(P.A,?Other:=dup[P].B)}
Field(P:pair(a,b) where a:type,b:type)<decides>:holder(b)=holder(b){M:=map{Empty()=>Echo(P.A,?Other:=dup[P].B)}}
Nested(P:pair(a,b) where a:type,b:type)<decides>:[?int][?string]b=map{Empty()=>map{Empty()=>Echo(P.A,?Other:=dup[P].B)}}
TupleKey(P:pair(a,b) where a:type,b:type)<decides>:[tuple(?int,int)]b=map{(Empty(),0)=>Echo(P.A,?Other:=dup[P].B)}
Weak(P:pair(a,b) where a:type,b:type)<decides>:weak_map(?int,b)=map{Empty()=>Echo(P.A,?Other:=dup[P].B)}
Main():void=
    P:=dup(int){A:=7,B:=9}
    if(M:=Direct[P],V:=M[false])then Print("direct {V}")else Print("wrong")
    if(M:=Bound[P],V:=M[false])then Print("bound {V}")else Print("wrong")
    if(V:=Call[P])then Print("call {V}")else Print("wrong")
    if(M:=Method[P],V:=M[false])then Print("method {V}")else Print("wrong")
    if(H:=Field[P],V:=H.M[false])then Print("field {V}")else Print("wrong")
    if(M:=Nested[P],N:=M[false],V:=N[false])then Print("nested {V}")else Print("wrong")
    if(M:=TupleKey[P],V:=M[(false,0)])then Print("tuple {V}")else Print("wrong")
    if(M:=Weak[P],V:=M[false])then Print("weak {V}")else Print("wrong")
    if(M:=Direct[pair(int,string){A:=7,B:="other"}])then Print("wrong")else Print("missing")
