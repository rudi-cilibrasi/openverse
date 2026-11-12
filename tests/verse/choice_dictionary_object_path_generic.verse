leaf(t:type):=class{var Data:?[]t}
ca(t:type):=class{Items:[]leaf(t)}
cb(t:type):=class{Items:[]leaf(t)}
Dup(X:t where t:type)<computes>:t=X|X
Run(X:t where t:subtype(comparable))<suspends>:int=
    P:=ca(t){Items:=array{leaf(t){Data:=option{array{X}}}}}
    Q:=cb(t){Items:=array{leaf(t){Data:=option{array{X}}}}}
    Rows:=for(A:=(Dup(P)|Dup(Q)),B:=A):
        if(set B.Items[0].Data?[0]=X):{}
        Sleep(0.01)
        0
    if(P.Items[0].Data?[0]=X,Q.Items[0].Data?[0]=X)then Rows.Length else -1
Main()<suspends>:void=
    Print("{Run(7)}")
    TextCount:=Run("s")
    Print("{TextCount}")
