Nat(N:int)<transacts><decides>:int =
    Print("visit {N}")
    N | Nat[N+1]
Two(N:int):int = N | N+1
first_probe := struct{}
all_probe := struct{}
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
    # (the methods below that call (super:)Cut are overloads of Cut that
    # override these: (super:)Cut is only in an override of Cut, the Book's)
    Cut(N:int,Bridge:logic,Plus:int)<transacts>:int = 0
    Cut(S:string,Bridge:logic)<transacts>:int = 0
    Cut(Find:float)<transacts>:int = 0
    Cut(First:first_probe)<transacts>:void = {}
    Cut(All:all_probe)<transacts>:void = {}
    Cut()<transacts>:void = {}
mid := class(base):
    Cut<override>(N:int,?Plus:int=100)<transacts>:int = 1000
    Cut<override>(N:int,Bridge:logic,Plus:int)<transacts>:int = (super:)Cut(N,?Plus:=Plus)
    Cut<override>(S:string,Bridge:logic)<transacts>:int = (super:)Cut(S)
    Cut<override>(Find:float)<transacts>:int =
        var Seen:int=0
        R:=if(X:=Nat[0],set Seen+=1,X>(super:)Cut(0),X>(super:)Cut("x")) then X else -1
        Print("first {R} {Seen} {Calls}")
        R
    Cut<override>(First:first_probe)<transacts>:void =
        var Seen:int=0
        if(A:=Two(0)|Two(2),B:=Two(0)|Two(2),set Seen+=1,A+B>(super:)Cut(0)):
            Print("composed {A} {B} {Seen} {Calls}")
    Cut<override>(All:all_probe)<transacts>:void =
        for(A:=Two(0)|Two(2),B:=Two(0)|Two(2),A+B>(super:)Cut(0)):
            Print("all {A} {B}")
    Cut<override>()<transacts>:void =
        for(A:=Two(0)|Two(2),B:=Two(0)|Two(2)):
            Print("body {A} {B} {(super:)Cut(0)}")
leaf := class(mid):
    Cut<override>(N:int,?Plus:int=200)<transacts>:int = 2000
Main()<transacts>:void =
    L:=leaf{}
    Print("found {L.Cut(0.0)}")
    L.Cut(first_probe{})
    L.Cut(all_probe{})
    L.Cut()
