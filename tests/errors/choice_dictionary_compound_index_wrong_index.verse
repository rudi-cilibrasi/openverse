ca:=class{var Data:[]int=array{0}}
cb:=class{var Data:[]int=array{0}}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),set A.Data["bad"]+=7):0
    Print("{Rows.Length}")
