pair(a:type,b:type) := class { A:a; B:b }
dup(t:type) := class(pair(t,t)) { C:int=3 }
Walk(X:t,N:int where t:type)<transacts><decides>:t =
    N>0
    Print("walk {N}")
    X | Walk[X,N-1]
base(t:subtype(comparable)) := class:
    V:t
    Pick(X:t,?Y:t=X)<transacts>:t=Y
    Label(N:int)<computes>:string="int {N}"
    Label(S:string)<computes>:string="str {S}"
    # ((super:)M is only in an override of M, the Book's rule: the methods
    # that call it are overloads of M that override these)
    Label(P:pair(a,b),X:a where a:type,b:type)<transacts>:b=P.B
mid(u:subtype(comparable)) := class(base(u)):
    # (given its X again as Y: the inherited Pick, after a first success)
    Pick<override>(X:u,?Y:u=V)<transacts>:u=
        if(X=Y) then (if(Z:=Walk[X,2],Z=(super:)Pick(X)) then Z else V) else V
    Label<override>(P:pair(a,b),X:a where a:type,b:type)<transacts>:b=
        if(D:=dup[P]):
            Print((super:)Label((super:)Label(1)))
            if(Y:=Walk[X,2],E:[]b=array{Y}):
                Print((super:)Label(D.C))
            X
        else P.B
Main()<transacts>:void=
    M:=mid(int){V:=99}
    Print("{M.Pick(7,?Y:=7)}")
    Print("{M.Label(dup(int){A:=1,B:=2},8)}")
    Print(M.Label(pair(int,string){A:=1,B:="s"},8))
