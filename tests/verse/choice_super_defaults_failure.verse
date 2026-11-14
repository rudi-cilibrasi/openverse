Nat(N:int)<transacts><decides>:int =
    N<4
    Print("visit {N}")
    N | Nat[N+1]
Note(N:int)<transacts>:int =
    Print("default {N}")
    N
run_probe := struct{}
base := class:
    var Seen:int=0
    Test(N:int,?Low:int=Note(1))<transacts><decides>:int=
        set Seen+=1
        Print("test {N} {Low} {Seen}")
        N>Low
        N
    # ((super:)M is only in an override of M, the Book's rule: the methods
    # that call it are overloads of M that override these)
    Test(Probe:run_probe,N:int,?Low:int=Note(1))<transacts><decides>:int=N
    Test(Probe:run_probe)<transacts>:void={}
sub := class(base):
    Test<override>(Probe:run_probe,N:int,?Low:int=Note(1))<transacts><decides>:int=(super:)Test[N,?Low:=Low]
    Test<override>(Probe:run_probe)<transacts>:void=
        if(X:=Nat[0],Y:=(super:)Test[X]): Print("got {Y} {Seen}")
        Print("kept {Seen}")
        if(X:=Nat[0],Y:=(super:)Test[X,?Low:=Note(9)]): Print("bad")
        Print("after {Seen}")
Main()<transacts>:void=sub{}.Test(run_probe{})
