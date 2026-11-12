ca:=class{var K:int=1}
cb:=class{var K:rational=1/1}
Dup(X:t where t:type)<computes>:t=X|X
Default(?X:t=block{Rows:=for(I:=(Dup(1)|Dup(2)),J:=(Dup(3)|Dup(4))):block{V:t=3;I+J};3} where t:type)<computes>:t=X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{}))):
        R:=set A.K=Default()
        0
    Print("{Rows.Length}")
