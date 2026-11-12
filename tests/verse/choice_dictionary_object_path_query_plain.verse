cell:=class{var N:int=0}
ca:=class:
    H:cell
    var Data:?[]int=option{array{1,2}}
    Key()<transacts>:int=block{Print("key a");set H.N+=1;0}
    RHS()<transacts>:int=block{Print("rhs a");set H.N+=10;set Data=option{array{30,40}};7}
cb:=class:
    H:cell
    var Data:?[]int=option{array{10,2}}
    Key()<transacts>:int=block{Print("key b");set H.N+=1;0}
    RHS()<transacts>:int=block{Print("rhs b");set H.N+=10;set Data=option{array{30,40}};7}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    H:=cell{}
    P:=ca{H:=H}
    Q:=cb{H:=H}
    Rows:=for(A:=(Dup(P)|Dup(Q)),V:=set A.Data?[A.Key()]=A.RHS()):block{Print("body {V} {H.N}");V}
    Print("done {Rows.Length} {H.N}")
    if(P.Data?[0]=7,Q.Data?[0]=7,P.Data?[1]=40,Q.Data?[1]=40)then Print("state ok") else Print("bad state")
