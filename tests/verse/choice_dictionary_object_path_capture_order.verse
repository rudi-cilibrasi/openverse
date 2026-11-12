cell:=class{var N:int=0}
leafa:=class{var Data:[]int=array{0,0}}
leafb:=class{var Data:[]rational=array{0,0}}
ca:=class:
    H:cell
    Original:leafa
    Other:leafa
    Last:leafa
    var Items:[]leafa
    Outer()<transacts>:int=block{Print("outer a");set H.N+=1;set Items=array{Other};0}
    Inner()<transacts>:int=block{Print("inner a");set H.N+=2;set Items=array{Last};0}
    RHS()<transacts>:int=block{Print("rhs a");set H.N+=10;set Last.Data=array{300,400};set Items=array{Original};7}
cb:=class:
    H:cell
    Original:leafb
    Other:leafb
    Last:leafb
    var Items:[string]leafb
    Outer()<transacts>:string=block{Print("outer b");set H.N+=1;set Items=map{"k"=>Other};"k"}
    Inner()<transacts>:int=block{Print("inner b");set H.N+=2;set Items=map{"k"=>Last};0}
    RHS()<transacts>:int=block{Print("rhs b");set H.N+=10;set Last.Data=array{300,400};set Items=map{"k"=>Original};7}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    if(Half:=1/2):
        H:=cell{}
        P0:=leafa{}
        P1:=leafa{}
        P2:=leafa{Data:=array{50,60}}
        Q0:=leafb{}
        Q1:=leafb{}
        Q2:=leafb{Data:=array{Half,Half}}
        P:=ca{H:=H,Original:=P0,Other:=P1,Last:=P2,Items:=array{P0}}
        Q:=cb{H:=H,Original:=Q0,Other:=Q1,Last:=Q2,Items:=map{"k"=>Q0}}
        Rows:=for(A:=(Dup(P)|Dup(Q)),set A.Items[A.Outer()].Data[A.Inner()]+=A.RHS()):block{Print("body {H.N}");0}
        Print("done {Rows.Length} {H.N}")
        if(P2.Data[0]=64,P2.Data[1]=400,Q2.Data[0]=29/2,Q2.Data[1]=400,P0.Data[0]=0,P1.Data[0]=0,Q0.Data[0]=0,Q1.Data[0]=0)then Print("state ok") else Print("bad state")
