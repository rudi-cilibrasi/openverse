# expect: unknown identifier 'Hidden'
# Conversion evidence retains no caller source locals in a callee's default.
ca:=class{var K:int=1}
cb:=class{var K:rational=1}
Dup(X:t where t:type)<computes>:t=X|X
Default(?X:t=Hidden where t:type)<computes>:t=X
Main():void=
    Hidden:=3
    Rows:=for(A:=(Dup(ca{})|Dup(cb{}))):set A.K=Default()
    Print("{Rows.Length}")
