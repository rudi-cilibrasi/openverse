# expect: not through a tuple element or a call result
# A checked getter must not admit source assignment through a call result.
leaf:=class{var K:int=1}
ca:=class{C:leaf;Get()<computes>:leaf=C}
cb:=class{C:leaf;Get()<computes>:leaf=C}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    Rows:=for(A:=(Dup(ca{C:=leaf{}})|Dup(cb{C:=leaf{}}))):set A.Get().K=3
    Print("{Rows.Length}")
