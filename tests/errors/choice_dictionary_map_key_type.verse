ca:=class{var Data:[int]int=map{0=>1}}
cb:=class{var Data:[int]int=map{0=>1}}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{}))):set A.Data["bad"]=7
    Print("{Rows.Length}")
