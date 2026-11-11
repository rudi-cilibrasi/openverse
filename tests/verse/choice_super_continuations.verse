Nat(N:int)<transacts><decides>:int =
    Print("visit {N}")
    N | Nat[N+1]
Two(N:int):int = N | N+1
base := class:
    var Calls:int=0
    Cut(N:int,?Plus:int=1)<transacts>:int =
        set Calls+=1
        Print("cut {N} {Plus} {Calls}")
        N+Plus
    Cut(S:string)<transacts>:int =
        set Calls+=1
        Print("str {S} {Calls}")
        1
mid := class(base):
    Cut<override>(N:int,?Plus:int=100)<transacts>:int = 1000
    Bridge(N:int,?Plus:int=1)<transacts>:int = (super:)Cut(N,?Plus:=Plus)
    StrBridge(S:string)<transacts>:int = (super:)Cut(S)
    Find()<transacts>:int =
        var Seen:int=0
        R:=if(X:=Nat[0],set Seen+=1,X>(super:)Cut(0),X>(super:)Cut("x")) then X else -1
        Print("first {R} {Seen} {Calls}")
        R
    First()<transacts>:void =
        var Seen:int=0
        if(A:=Two(0)|Two(2),B:=Two(0)|Two(2),set Seen+=1,A+B>(super:)Cut(0)):
            Print("composed {A} {B} {Seen} {Calls}")
    All()<transacts>:void =
        for(A:=Two(0)|Two(2),B:=Two(0)|Two(2),A+B>(super:)Cut(0)):
            Print("all {A} {B}")
    Body()<transacts>:void =
        for(A:=Two(0)|Two(2),B:=Two(0)|Two(2)):
            Print("body {A} {B} {(super:)Cut(0)}")
leaf := class(mid):
    Cut<override>(N:int,?Plus:int=200)<transacts>:int = 2000
Main()<transacts>:void =
    L:=leaf{}
    Print("found {L.Find()}")
    L.First()
    L.All()
    L.Body()
