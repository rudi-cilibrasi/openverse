ca:=class{Data:[]int=array{0}}
cb:=class{Data:[]int=array{0}}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),set A.Data[0]+=7):0
    Print("{Rows.Length}")
