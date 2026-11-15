# A refining cast branch may return from its enclosing function while its normal result is inferred.
# Each line compares inference with an explicit b annotation.
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
Inferred(P:pair(a, b) where a:type, b:type):b =
    X := if (D := dup[P]):
        if (D.C > 0) then return D.A
        D.A
    else:
        P.B
    X
Explicit(P:pair(a, b) where a:type, b:type):b =
    X:b = if (D := dup[P]):
        if (D.C > 0) then return D.A
        D.A
    else:
        P.B
    X
Main():void =
    Print("{Inferred(dup(int){A:=7,B:=9,C:=1})} {Explicit(dup(int){A:=7,B:=9,C:=1})}")
    Print("{Inferred(dup(int){A:=7,B:=9,C:=0})} {Explicit(dup(int){A:=7,B:=9,C:=0})}")
    Print("{Inferred(pair(string,int){A:="a",B:=9})} {Explicit(pair(string,int){A:="a",B:=9})}")
    Print("{Inferred(dup(string){A:="left",B:="right",C:=1})} {Explicit(dup(string){A:="left",B:="right",C:=1})}")
    Print("{Inferred(dup(string){A:="left",B:="right",C:=0})} {Explicit(dup(string){A:="left",B:="right",C:=0})}")
