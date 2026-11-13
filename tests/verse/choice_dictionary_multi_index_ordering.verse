# set A.Child.Data[A.Key()][A.Key2()] += A.RHS(): the keys (which move Child), then the object Child
# names, then RHS (which replaces the leaves' Data and moves Child again), then the old value read
# from the captured object's new Data
leaf:=class{var Data:[][]int=array{array{0,0},array{70,80}}}
ca:=class:
    var Child:leaf
    Original:leaf
    Other:leaf
    Last:leaf
    Key()<transacts>:int=
        Print("key a")
        set Child=Other
        0
    Key2()<transacts>:int=
        Print("key2 a")
        set Child=Last
        1
    RHS()<transacts>:int=
        Print("rhs a")
        set Original.Data=array{array{10,20},array{70,80}}
        set Other.Data=array{array{30,40},array{70,80}}
        set Last.Data=array{array{300,400},array{700,800}}
        set Child=Original
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
    Key2()<transacts>:int=
        Print("key2 b")
        set Child=Last
        1
    RHS()<transacts>:int=
        Print("rhs b")
        set Original.Data=array{array{10,20},array{70,80}}
        set Other.Data=array{array{30,40},array{70,80}}
        set Last.Data=array{array{300,400},array{700,800}}
        set Child=Original
        7
Dup(X:t where t:type)<computes>:t=X|X
Dump(L:leaf)<reads>:void=if(X:=L.Data[0][0],Y:=L.Data[0][1],Z:=L.Data[1][0],W:=L.Data[1][1]):Print("{X} {Y} {Z} {W}")
Main():void=
    P0:=leaf{}
    P1:=leaf{}
    P2:=leaf{Data:=array{array{50,60},array{70,80}}}
    Q0:=leaf{}
    Q1:=leaf{}
    Q2:=leaf{Data:=array{array{50,60},array{70,80}}}
    P:=ca{Child:=P0,Original:=P0,Other:=P1,Last:=P2}
    Q:=cb{Child:=Q0,Original:=Q0,Other:=Q1,Last:=Q2}
    Rows:=for(A:=(Dup(P)|Dup(Q)),R:=set A.Child.Data[A.Key()][A.Key2()]+=A.RHS()):R
    Print("rows {Rows.Length}")
    Dump(P0)
    Dump(P1)
    Dump(P2)
    Dump(P.Child)
    Dump(Q0)
    Dump(Q1)
    Dump(Q2)
    Dump(Q.Child)
