# (#53, #351) casts to an interface beside the object's type, or that open
# its type arguments, in the contexts refining casts work in
base(t:type) := interface:
    Id():t
i1(t:type) := interface(base(t)):
    A():int
i2(t:type) := interface(base(t)):
    B():int
c(t:type) := class(i1(t), i2(t)):
    V:t
    Id<override>():t = V
    A<override>():int = 1
    B<override>():int = 2
k := class(i1(string), i2(string)):
    Id<override>():string = "k"
    A<override>():int = 10
    B<override>():int = 20
only2(t:type) := class(i2(t)):
    V:t
    Id<override>():t = V
    B<override>():int = 3
cell := class:
    var N:int = 0
# the interfaces above both relate them: J is an i1(u), so J.Id() a u
Swap(I:i2(u) where u:type):?u =
    if (J := i1[I]) then option{J.Id()} else false
# in a <decides> body, after a write the failure undoes
Sum(H:cell, I:i2(u) where u:type)<transacts><decides>:int =
    set H.N += 1
    J := i1[I]
    J.A() + I.B()
# a return and a set of an outside var in the branch
Find(Is:[]i2(u) where u:type):int =
    var Seen:int = 0
    for (I : Is):
        if (J := i1[I]) then:
            set Seen += 1
            if (J.A() > 5) then return 100 + Seen
    Seen
# not, option{} and first{}
Count(Is:[]i2(u) where u:type):tuple(int, int) =
    var N:int = 0
    var M:int = 0
    for (I : Is):
        if (not i1[I]) then set N += 1
        if (V := option{i1[I].A()}?) then set M += V
    (N, M)
# suspending in the branch
Wait(I:i2(u) where u:type)<suspends>:int =
    if (J := i1[I]) then:
        Sleep(0.01)
        J.A() * 7
    else 0
# a method, whose branch names Self's members bare
holder := class:
    Tag:string = "h"
    Show(I:i2(int)):string =
        if (J := i1[I]) then "{Tag} {J.Id()}" else "{Tag} none"
Main()<suspends>:void =
    if (X := Swap(c(int){V := 5})?) then Print("swap {X}")
    if (X := Swap(only2(int){V := 5})?) then Print("no") else Print("swap none")
    if (X := Swap(k{})?) then Print("swap {X}")
    H := cell{}
    if (S := Sum[H, c(int){V := 1}]) then Print("sum {S} {H.N}")
    if (S := Sum[H, only2(int){V := 1}]) then Print("no") else Print("sum none {H.N}")
    Is:[]i2(int) = array{c(int){V := 1}, only2(int){V := 2}, c(int){V := 3}}
    Print("find {Find(Is)}")
    Ks:[]i2(string) = array{only2(string){V := "a"}, k{}, c(string){V := "b"}}
    Print("find {Find(Ks)}")
    C := Count(Is)
    Print("count {C(0)} {C(1)}")
    Print("wait {Wait(k{})} {Wait(only2(string){V := "x"})}")
    Print(holder{}.Show(c(int){V := 9}))
    Print(holder{}.Show(only2(int){V := 9}))
