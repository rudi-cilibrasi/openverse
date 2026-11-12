# An expected result may supply a type the omitted empty default cannot infer.
# Such a call retains ordinary result-directed binding rather than fixing it early.
Dup(X:t where t:type)<computes>:t=X|X
ca:=class{M(?X:[]u=array{} where u:type)<computes>:[]u=X}
cb:=class{M(?X:[]u=array{} where u:type)<computes>:[]u=X}
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),B:[]int=A.M()):B.Length
    for(V:Rows):Print("{V}")
