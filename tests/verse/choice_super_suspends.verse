pair(a:type,b:type) := class { A:a; B:b }
dup(t:type) := class(pair(t,t)) { C:int=3 }
text_probe := struct{}
base := class:
    Read(N:int)<suspends>:string=
        Print("before int")
        Sleep(0.01)
        "int {N}"
    Read(S:string)<suspends>:string=
        Print("before str")
        Sleep(0.01)
        "str {S}"
    # ((super:)M is only in an override of M, the Book's rule: the methods
    # that call it are overloads of M that override these)
    Read(P:pair(a,b) where a:type,b:type)<suspends>:string="no"
    Read(T:text_probe,P:pair(a,b) where a:type,b:type)<suspends>:string="no"
sub := class(base):
    Read<override>(N:int)<suspends>:string="wrong"
    Read<override>(P:pair(a,b) where a:type,b:type)<suspends>:string=
        if(D:=dup[P]) then (super:)Read(D.C) else "no"
    Read<override>(T:text_probe,P:pair(a,b) where a:type,b:type)<suspends>:string=
        if(D:=dup[P]) then (super:)Read("{D.C}") else "no"
Main()<suspends>:void=
    S:=sub{}
    Print(S.Read(dup(int){A:=1,B:=2}))
    Print(S.Read(text_probe{},dup(int){A:=1,B:=2}))
    Print(S.Read(pair(int,string){A:=1,B:="s"}))
