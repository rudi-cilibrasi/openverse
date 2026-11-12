ca:=class{M(A:[]u,B:?u,C:u,?Z:int=3 where u:type)<computes>:int=A.Length+Z}
cb:=class{M(A:[]u,B:?u,C:u,?Z:int=4 where u:type)<computes>:int=A.Length+Z}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),V:=A.M((array{},false,7))):V
    for(V:Rows):Print("{V}")
