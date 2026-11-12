ca:=class{var Data:tuple(int,int)=(1,2)}
cb:=class{var Data:tuple(int,int)=(3,4)}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    P:=ca{}
    Q:=cb{}
    Rows:=for(A:=(Dup(P)|Dup(Q)),set A.Data=(7,8)):0
    Print("{Rows.Length}")
    if(P.Data(0)=7,P.Data(1)=8,Q.Data(0)=7,Q.Data(1)=8)then Print("state ok") else Print("bad state")
