# Rejected searches undo both cleanup effects and output.
# (The return is in tail position, a branch of the body's last if: the function
# is <decides>, Return.versetest:157; the late defer: is the else's.)
cell := class { var N:int=0 }
Values(H:cell,Mode:int)<transacts><decides>:int =
    Print("entry {Mode}")
    defer:
        Print("outer {H.N}")
        set H.N+=100
    if(Mode=0):return 9|10
    else:
        defer:
            Print("late {H.N}")
            set H.N+=10
        1|2
Main():void =
    A:=cell{}
    if(V:=Values[A,1],V=2)then Print("first {V} {A.N}")
    B:=cell{}
    if(V:=Values[B,1],V>2)then Print("unreachable")else Print("none {B.N}")
    C:=cell{}
    if(V:=Values[C,0],V=10)then Print("return {V} {C.N}")
    D:=cell{}
    for(V:=Values[D,1]):Print("all {V} {D.N}")
