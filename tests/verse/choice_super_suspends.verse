pair(a:type,b:type) := class { A:a; B:b }
dup(t:type) := class(pair(t,t)) { C:int=3 }
base := class:
    Read(N:int)<suspends>:string=
        Print("before int")
        Sleep(0.01)
        "int {N}"
    Read(S:string)<suspends>:string=
        Print("before str")
        Sleep(0.01)
        "str {S}"
sub := class(base):
    Read<override>(N:int)<suspends>:string="wrong"
    Get(P:pair(a,b) where a:type,b:type)<suspends>:string=
        if(D:=dup[P]) then (super:)Read(D.C) else "no"
    Text(P:pair(a,b) where a:type,b:type)<suspends>:string=
        if(D:=dup[P]) then (super:)Read("{D.C}") else "no"
Main()<suspends>:void=
    S:=sub{}
    Print(S.Get(dup(int){A:=1,B:=2}))
    Print(S.Text(dup(int){A:=1,B:=2}))
    Print(S.Get(pair(int,string){A:=1,B:="s"}))
