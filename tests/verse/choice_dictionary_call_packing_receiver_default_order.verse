cell:=class{var N:int=0}
ma:=class:
    H:cell
    Tag:string
    var Count:int
    Stamp()<transacts>:int=block{Print("default {Tag} {Count}");set H.N+=10;Count}
    M(X:int,Y:int,?Z:int=Stamp())<transacts>:int=
        Print("method {Tag} {X} {Y} {Z}")
        set H.N+=100
        set Count+=1
        X+Y+Z
mb:=class:
    H:cell
    Tag:string
    var Count:int
    Stamp()<transacts>:int=block{Print("default {Tag} {Count}");set H.N+=10;Count}
    M(X:int,Y:int,?Z:int=Stamp())<transacts>:int=
        Print("method {Tag} {X} {Y} {Z}")
        set H.N+=100
        set Count+=1
        X+Y+Z
ca:=class:
    H:cell
    var Child:ma
    Original:ma
    Other:ma
    Args()<transacts>:tuple(int,int)=
        Print("args a")
        set H.N+=1
        set Original.Count=30
        set Child=Other
        (1,2)
cb:=class:
    H:cell
    var Child:mb
    Original:mb
    Other:mb
    Args()<transacts>:tuple(int,int)=
        Print("args b")
        set H.N+=1
        set Original.Count=50
        set Child=Other
        (4,5)
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    H:=cell{}
    P0:=ma{H:=H,Tag:="a0",Count:=10}
    P1:=ma{H:=H,Tag:="a1",Count:=20}
    Q0:=mb{H:=H,Tag:="b0",Count:=40}
    Q1:=mb{H:=H,Tag:="b1",Count:=40}
    P:=ca{H:=H,Child:=P0,Original:=P0,Other:=P1}
    Q:=cb{H:=H,Child:=Q0,Original:=Q0,Other:=Q1}
    Rows:=for(A:=(Dup(P)|Dup(Q))):
        V:=A.Child.M(A.Args())
        Print("row {V} {H.N}")
        V
    Print("done {Rows.Length} {H.N}")
    if(P0.Count=30,P1.Count=21,Q0.Count=50,Q1.Count=41)then Print("state ok") else Print("bad state")
