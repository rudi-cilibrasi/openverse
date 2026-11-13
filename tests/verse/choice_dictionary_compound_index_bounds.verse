# set A.Data[K] op= e: the key, then e (which replaces Data), then the old value read from the new
# Data; a key out of its range then fails the clause, e's effects rolled back with it
cell:=class{var N:int=0}
ca:=class:
    H:cell
    I:int
    var Data:[]int=array{0}
    Key()<transacts>:int=block{Print("key a");set H.N+=1;I}
    RHS()<transacts>:int=block{Print("rhs a");set H.N+=10;set Data=array{100};7}
cb:=class:
    H:cell
    I:int
    var Data:[]int=array{0}
    Key()<transacts>:int=block{Print("key b");set H.N+=1;I}
    RHS()<transacts>:int=block{Print("rhs b");set H.N+=10;set Data=array{100};7}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    H:=cell{}
    P:=ca{H:=H,I:=0}
    Q:=cb{H:=H,I:=2}
    Rows:=for(A:=(Dup(P)|Dup(Q)),R:=set A.Data[A.Key()]+=A.RHS()):block{Print("body {R}");R}
    Print("done {Rows.Length} {H.N}")
    if(P.Data[0]=107,Q.Data[0]=0)then Print("state ok") else Print("bad state")
