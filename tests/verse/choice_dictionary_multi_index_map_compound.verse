# set A.Data[A.Outer()][A.Key()] += A.RHS() on maps of maps: the keys, then RHS, which replaces the
# maps, then the old value read from the new ones
cell:=class{var N:int=0}
ca:=class:
    H:cell
    var Data:[int][int]int=map{0=>map{7=>1,9=>90}}
    Outer()<transacts>:int=block{Print("outer a");0}
    Key()<transacts>:int=
        Print("key a")
        set H.N+=1
        7
    RHS()<transacts>:int=
        Print("rhs a")
        set H.N+=10
        set Data=map{0=>map{9=>900,7=>4}}
        3
cb:=class:
    H:cell
    var Data:[string][string]int=map{"o"=>map{"k"=>10,"z"=>90}}
    Outer()<transacts>:string=block{Print("outer b");"o"}
    Key()<transacts>:string=
        Print("key b")
        set H.N+=1
        "k"
    RHS()<transacts>:int=
        Print("rhs b")
        set H.N+=10
        set Data=map{"o"=>map{"z"=>900,"k"=>13}}
        3
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    H:=cell{}
    P:=ca{H:=H}
    Q:=cb{H:=H}
    Rows:=for(A:=(Dup(P)|Dup(Q)),V:=set A.Data[A.Outer()][A.Key()]+=A.RHS()):block{Print("body {V} {H.N}");V}
    Print("done {Rows.Length} {H.N}")
    if(P.Data[0][7]=7,P.Data[0][9]=900,Q.Data["o"]["k"]=16,Q.Data["o"]["z"]=900)then Print("state ok") else Print("bad state")
