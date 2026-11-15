One()<computes>:int=1
Two()<computes>:int=2
Dup(N:int)<computes>:int=N|N
Read(E:event(int))<suspends>:void=
    var Stored:type{_()<computes>:int}=Two
    branch:
        Values:=for(A:=(Dup(1)|Dup(2)),B:=(Dup(1)|Dup(2))):
            E.Await()
            Print("borrowed read {Stored()}")
    set Stored=One
    E.Signal(0)
    Print("owner continues")
Main()<suspends>:void=Read(event(int){})
