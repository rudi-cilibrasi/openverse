pair(a:type,b:type) := class { A:a; B:b }
dup(t:type) := class(pair(t,t)) { C:int=3 }
Walk(X:t,N:int where t:type)<transacts><decides>:t =
    N>0
    Print("walk {N}")
    X | Walk[X,N-1]
base(t:subtype(comparable)) := class:
    V:t
    Pick(X:t,?Y:t=X)<computes>:t=Y
    Label(N:int)<computes>:string="int {N}"
    Label(S:string)<computes>:string="str {S}"
mid(u:subtype(comparable)) := class(base(u)):
    Pick<override>(X:u,?Y:u=V)<computes>:u=V
    Bridge(X:u,?Y:u=X)<computes>:u=(super:)Pick(X,?Y:=Y)
    LabelBridge(N:int)<computes>:string=(super:)Label(N)
    StrLabelBridge(S:string)<computes>:string=(super:)Label(S)
    First(X:u)<transacts>:u=if(Y:=Walk[X,2],Y=(super:)Pick(X)) then Y else V
    Get(P:pair(a,b),X:a where a:type,b:type)<transacts>:b=
        if(D:=dup[P]):
            Print((super:)Label((super:)Label(1)))
            if(Y:=Walk[X,2],E:[]b=array{Y}):
                Print((super:)Label(D.C))
            X
        else P.B
Main()<transacts>:void=
    M:=mid(int){V:=99}
    Print("{M.First(7)}")
    Print("{M.Get(dup(int){A:=1,B:=2},8)}")
    Print(M.Get(pair(int,string){A:=1,B:="s"},8))
