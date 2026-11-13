# Capture the terminal object before the RHS replaces its parent field; read its field after the RHS.
leaf:=class{var K:int}
base:=class:
    var C:leaf
    Change()<transacts>:int=
        Old:=C
        set C=leaf{K:=100}
        set Old.K=50
        3
ca:=class(base){}
cb:=class(base){}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    OldP:=leaf{K:=1}
    OldQ:=leaf{K:=2}
    P:=ca{C:=OldP}
    Q:=cb{C:=OldQ}
    Rows:=for(A:=(Dup(P)|Dup(Q))):
        R:=set A.C.K+=A.Change()
        Print("{R} {A.C.K}")
        R
    Print("{OldP.K} {OldQ.K} {Rows.Length}")
