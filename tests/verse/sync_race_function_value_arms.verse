# The arms of sync and race that call a suspending function value can
# suspend, also where the classes of the value's type are made in a later
# elaboration: a method value converted with variance and returned by a
# generic function (the arms of a race must all be able to suspend, the
# Book's tests, Concurrency.versetest; sync needs two)
cell:=class{var N:int=0}
box(t:type):=class:
    V:t
    C:cell
    Later(X:int)<suspends>:tuple(t,int)=
        set C.N+=1
        Print("begin {C.N} {X}")
        defer: Print("cleanup {X}")
        Sleep(1.0)
        Print("end {C.N} {X}")
        (V,C.N)
Bind(B:box(t) where t:type)<computes>:type{_(:int)<suspends>:tuple(t,rational)}=B.Later
Main()<suspends>:void=
    B:=box(string){V:="value",C:=cell{}}
    F:=Bind(B)
    R:=sync:
        F(1)
        F(2)
    Print("sync {R(0)(0)} {Floor(R(0)(1))} {Floor(R(1)(1))}")
    race:
        F(3)
        block:
            Sleep(0.5)
            Print("timeout")
    Print("finished {B.C.N}")
