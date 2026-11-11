Keep(X:t,Y:t where t:subtype(comparable))<computes><decides>:t=block{X=Y;X}
Id(X:t where t:subtype(comparable))<computes>:t=X
Bind(X:t where t:subtype(comparable))<computes>:type{_(:tuple(t,t))<computes><decides>:t}=Keep
Build(X:t,Y:u where t:subtype(comparable),u:subtype(comparable))<computes>:tuple(t,u)=
    F:type{_(:t,:u)<computes>:tuple(t,u)}=Id
    F(X,Y)
token:=class<unique>{N:int}
Main():void=
    A:=token{N:=3}
    B:=token{N:=3}
    F:=Bind(A)
    if(R:=F[(A,A)])then Print("same {R.N}")
    if(F[(A,B)])then Print("wrong")else Print("different")
    P:=Build(A,7)
    Print("pair {P(0).N} {P(1)}")
