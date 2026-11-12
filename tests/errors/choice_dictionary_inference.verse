# expect: expected type{_(:rational)<computes>:int}
# Inference differs by receiver: CB infers rational from its result.
# A shared int instantiation must not admit IntOnly for that alternative.
IntOnly(X:int)<computes>:int=11
ca:=class<unique>:
    M(X:u,F:type{_(:u)<computes>:int} where u:type)<computes>:tuple(ca,u)=block{Print("{F(X)}");(Self,X)}
cb:=class<unique>:
    M(X:u,F:type{_(:u)<computes>:int} where u:type)<computes>:tuple(any,u)=block{Print("{F(X)}");(Self,X)}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),B:=(Dup(1)|Dup("s"))):
        V:tuple(any,rational)=A.M(1,IntOnly)
        V(1)
    Print("{Rows.Length}")
