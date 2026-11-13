# set A.Data[A.Key()] += A.RHS() on maps: the key, then RHS, which replaces the map, then the old
# value read from the new map
cell:=class{var N:int=0}
ca:=class:
    H:cell
    var Data:[int]int=map{7=>1,9=>90}
    Key()<transacts>:int=
        Print("key a")
        set H.N+=1
        7
    RHS()<transacts>:int=
        Print("rhs a")
        set H.N+=10
        set Data=map{9=>900,7=>4}
        3
cb:=class:
    H:cell
    var Data:[string]int=map{"k"=>10,"z"=>90}
    Key()<transacts>:string=
        Print("key b")
        set H.N+=1
        "k"
    RHS()<transacts>:int=
        Print("rhs b")
        set H.N+=10
        set Data=map{"z"=>900,"k"=>13}
        3
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    H:=cell{}
    P:=ca{H:=H}
    Q:=cb{H:=H}
    Rows:=for(A:=(Dup(P)|Dup(Q)),V:=set A.Data[A.Key()]+=A.RHS()):block{Print("body {V} {H.N}");V}
    Print("done {Rows.Length} {H.N}")
    if(P.Data[7]=7,P.Data[9]=900,Q.Data["k"]=16,Q.Data["z"]=900)then Print("state ok") else Print("bad state")
