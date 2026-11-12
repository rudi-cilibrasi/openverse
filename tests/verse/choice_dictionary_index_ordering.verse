leaf:=class{var Data:[]int=array{0,0}}
ca:=class:
    var Child:leaf
    Original:leaf
    Other:leaf
    Last:leaf
    Key()<transacts>:int=
        Print("key a")
        set Child=Other
        0
    RHS()<transacts>:int=
        Print("rhs a")
        set Original.Data=array{10,20}
        set Other.Data=array{30,40}
        set Child=Last
        7
cb:=class:
    var Child:leaf
    Original:leaf
    Other:leaf
    Last:leaf
    Key()<transacts>:int=
        Print("key b")
        set Child=Other
        0
    RHS()<transacts>:int=
        Print("rhs b")
        set Original.Data=array{10,20}
        set Other.Data=array{30,40}
        set Child=Last
        7
Dup(X:t where t:type)<computes>:t=X|X
Dump(L:leaf)<reads>:void=if(X:=L.Data[0],Y:=L.Data[1]):Print("{X} {Y}")
Main():void=
    P0:=leaf{}
    P1:=leaf{}
    P2:=leaf{Data:=array{50,60}}
    Q0:=leaf{}
    Q1:=leaf{}
    Q2:=leaf{Data:=array{50,60}}
    P:=ca{Child:=P0,Original:=P0,Other:=P1,Last:=P2}
    Q:=cb{Child:=Q0,Original:=Q0,Other:=Q1,Last:=Q2}
    Rows:=for(A:=(Dup(P)|Dup(Q)),R:=set A.Child.Data[A.Key()]=A.RHS()):R
    Print("rows {Rows.Length}")
    Dump(P0)
    Dump(P1)
    Dump(P2)
    Dump(P.Child)
    Dump(Q0)
    Dump(Q1)
    Dump(Q2)
    Dump(Q.Child)
