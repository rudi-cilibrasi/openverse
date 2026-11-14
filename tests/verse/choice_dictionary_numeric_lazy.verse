ca:=class{var K:int=1}
cb:=class{var K:rational=1}
Dup(X:t where t:type)<computes>:t=X|X
Iter(N:int)<computes>:int=if(N>0)then(N|Iter(N-1))else 0
Default(?X:t=if(I:=Iter(2),V:t=3,I=1)then V else 4 where t:type)<computes>:t=X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{}))):
        R:=set A.K=Default()
        0
    Print("{Rows.Length}")
