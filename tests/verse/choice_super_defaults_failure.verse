Nat(N:int)<transacts><decides>:int =
    N<4
    Print("visit {N}")
    N | Nat[N+1]
Note(N:int)<transacts>:int =
    Print("default {N}")
    N
base := class:
    var Seen:int=0
    Test(N:int,?Low:int=Note(1))<transacts><decides>:int=
        set Seen+=1
        Print("test {N} {Low} {Seen}")
        N>Low
        N
sub := class(base):
    Bridge(N:int,?Low:int=Note(1))<transacts><decides>:int=(super:)Test[N,?Low:=Low]
    Run()<transacts>:void=
        if(X:=Nat[0],Y:=(super:)Test[X]): Print("got {Y} {Seen}")
        Print("kept {Seen}")
        if(X:=Nat[0],Y:=(super:)Test[X,?Low:=Note(9)]): Print("bad")
        Print("after {Seen}")
Main()<transacts>:void=sub{}.Run()
