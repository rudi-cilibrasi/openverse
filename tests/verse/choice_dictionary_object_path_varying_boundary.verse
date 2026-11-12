cell:=class{var N:int=0}
sa:=struct{X:int;Tail:int}
sb:=class{var X:rational}
ca:=class:
    H:cell
    var Data:sa
    RHS()<transacts>:int=block{Print("rhs a");set H.N+=10;set Data=sa{X:=100,Tail:=200};7}
cb:=class:
    H:cell
    var Data:sb
    var Prev:sb
    RHS()<transacts>:int=block{Print("rhs b");set H.N+=10;set Prev=Data;set Data=sb{X:=100};7}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    if(Half:=1/2):
        H:=cell{}
        P:=ca{H:=H,Data:=sa{X:=1,Tail:=2}}
        Old:=sb{X:=Half}
        Q:=cb{H:=H,Data:=Old,Prev:=Old}
        Rows:=for(A:=(Dup(P)|Dup(Q)),set A.Data.X+=A.RHS()):block{Print("body {H.N}");0}
        Print("done {Rows.Length} {H.N}")
        if(P.Data.X=15,P.Data.Tail=200,Old.X=15/2,Q.Prev.X=107,Q.Data.X=100)then Print("state ok") else Print("bad state")
