# Method parameters are inferred at each call, after later choices.
ca:=class:
    K:int=1
    Id(X:u where u:type)<computes>:u=X
    Pair(X:u where u:type)<computes>:tuple(int,u)=(K,X)
    Echo(X:?u where u:type)<computes>:?u=X
    Array(X:u where u:type)<computes>:[]u=array{X}
    Same(X:u,Y:u where u:subtype(comparable))<computes>:int=if(X=Y)then K else 0
cb:=class:
    K:int=2
    Id(X:v where v:type)<computes>:v=X
    Pair(X:v where v:type)<computes>:tuple(int,v)=(K,X)
    Echo(X:?v where v:type)<computes>:?v=X
    Array(X:v where v:type)<computes>:[]v=array{X}
    Same(X:v,Y:v where v:subtype(comparable))<computes>:int=if(X=Y)then K else 0
Dup(X:t where t:type)<computes>:t=X|X
Equal(X:t,Y:t where t:subtype(comparable))<computes>:int=if(X=Y)then 1 else 0
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),B:=(Dup(1)|Dup("s"))):
        None:?int=A.Echo(false)
        Numeric:[]rational=A.Array(1)
        Empty:=if(None?)then 0 else 1
        Converted:=if(Numeric[0]=1)then 1 else 0
        Equal(A.Id(B),B)+Equal(A.Pair(B)(1),B)+A.Same(B,B)+Empty+Converted
    var Sum:int=0
    for(Row:Rows):set Sum+=Row
    Print("{Rows.Length} {Sum}")
