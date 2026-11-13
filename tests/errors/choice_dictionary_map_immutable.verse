# expect: field 'Data' of class ca is not a var
ca:=class{Data:[int]int=map{0=>1}}
cb:=class{Data:[int]int=map{0=>1}}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),set A.Data[0]=7):0
    Print("{Rows.Length}")
