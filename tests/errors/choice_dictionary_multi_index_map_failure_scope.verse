ca:=class{var Data:[int][int]int=map{0=>map{}}}
cb:=class{var Data:[int][int]int=map{0=>map{}}}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{}))):set A.Data[0][1]=7
    Print("{Rows.Length}")
