cell:=class{var N:int=0}
sa:=struct{X:int;Tail:int}
sb:=struct{X:rational;Tail:int}
ca:=class:
    H:cell
    var State:sa
    RHS()<transacts>:int=block{Print("rhs a");set H.N+=10;set State=sa{X:=100,Tail:=200};7}
cb:=class:
    H:cell
    var State:sb
    RHS()<transacts>:int=block{Print("rhs b");set H.N+=10;set State=sb{X:=100,Tail:=200};7}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    if(Half:=1/2):
        H:=cell{}
        P:=ca{H:=H,State:=sa{X:=1,Tail:=2}}
        Q:=cb{H:=H,State:=sb{X:=Half,Tail:=2}}
        Rows:=for(A:=(Dup(P)|Dup(Q)),set A.State.X+=A.RHS()):block{Print("body {H.N}");0}
        Print("done {Rows.Length} {H.N}")
        if(P.State.X=15,P.State.Tail=200,Q.State.X=29/2,Q.State.Tail=200)then Print("state ok") else Print("bad state")
