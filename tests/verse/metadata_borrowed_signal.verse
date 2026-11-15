One()<computes>:int=1
Two()<computes>:int=2
Dup(N:int)<computes>:int=N|N
Digit(N:int)<computes>:int=if(N>0)then (Digit(N-1)|N)else 0
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){}
Read(E:event(int))<suspends>:void=
    var Stored:type{_()<computes>:int}=Two
    branch:
        Values:=for(A:=(Dup(1)|Dup(2)),B:=(Dup(1)|Dup(2))):
            E.Await()
            Print("borrowed read {Stored()}")
    set Stored=One
    E.Signal(0)
    Print("owner continues")
Write(E:event(int))<suspends>:int=
    var Stored:type{_()<computes>:int}=Two
    branch:
        Values:=for(A:=(Digit(1)|Digit(1)),B:=(Digit(1)|Digit(1))):
            E.Await()
            set Stored=Two
            0
    set Stored=One
    E.Signal(0)
    Stored()

ScopedRead(P:pair(a,b),E:event(int),Initial:type{_()<computes>:int},Replacement:type{_()<computes>:int},Label:string where a:type,b:type)<suspends>:void=
    var Stored:type{_()<computes>:int}=Initial
    branch:
        if(D:=dup[P]):
            E.Await()
            Print("frame {Label} {Stored()}")
    set Stored=Replacement
    E.Signal(0)

Main()<suspends>:void=
    Read(event(int){})
    Print("recursive write {Write(event(int){})}")
    ScopedRead(dup(int){},event(int){},Two,One,"first")
    ScopedRead(dup(int){},event(int){},One,Two,"second")
