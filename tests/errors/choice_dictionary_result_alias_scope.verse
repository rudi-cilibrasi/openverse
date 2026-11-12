# expect: unknown identifier 'B'
# A block-local alias must not be available in its sibling expression.
ca:=class{K:int=1;Me()<computes>:ca=Self}
cb:=class{K:int=2;Me()<computes>:cb=Self}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{}))):
        N:=block{B:=A.Me();B.K}
        B.K+N
    Print("{Rows.Length}")
