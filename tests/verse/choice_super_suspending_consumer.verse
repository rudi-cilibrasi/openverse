Two(N:int):int=N|N+1
pair(a:type,b:type) := class { A:a; B:b }
dup(t:type) := class(pair(t,t)) { C:int=3 }
base := class:
    Limit(N:int)<computes>:int=N+1
    Limit(S:string)<computes>:int=1
    Wait(N:int)<suspends>:int=
        Sleep(0.01)
        N
sub := class(base):
    Limit<override>(N:int)<computes>:int=999
    Run()<suspends>:void=
        var Total:int=0
        branch:
            Sleep(0.1)
            Print("observe {Total}")
        Sleep(0.0)
        for(A:=Two(0)|Two(2),B:=Two(0)|Two(2)):
            set Total+=1
            Print("{A}{B}:{(super:)Limit(A)}")
        Sleep(0.2)
        for(A:=Two(0)|Two(2),B:=Two(0)|Two(2)):
            set Total+=1
            Print("wait {A}{B}:{(super:)Wait(A)}")
        Print("done {Total}")
    Get(P:pair(a,b) where a:type,b:type)<suspends>:void=
        for(X:=if(D:=dup[P]) then(D.C|D.C+1) else 0):
            Print("refined {X}:{(super:)Limit(X)}")
Main()<suspends>:void=
    S:=sub{}
    S.Run()
    S.Get(dup(int){A:=1,B:=2})
    S.Get(pair(int,string){A:=1,B:="s"})
