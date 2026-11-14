pair(a:type,b:type) := class { A:a; B:b }
dup(t:type) := class(pair(t,t)) { C:int=3 }
base := class:
    Wait(N:int)<suspends>:int=
        Sleep(0.01)
        N
    # ((super:)M is only in an override of M, the Book's rule: the methods
    # that call it are overloads of M that override these)
    Wait(P:pair(a,b) where a:type,b:type)<suspends>:void={}
sub := class(base):
    Wait<override>(P:pair(a,b) where a:type,b:type)<suspends>:void=
        for(X:=if(D:=dup[P]) then(D.C|D.C+1) else 0):
            Print("{(super:)Wait(X)}")
Main()<suspends>:void=sub{}.Wait(dup(int){A:=1,B:=2})
