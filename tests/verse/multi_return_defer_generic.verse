# Bound condition names and independently generic class/method results survive cleanup.
box(a:type) := class:
    Anchor:a
    Pick(X:b,Y:b,Mode:?int where b:type)<transacts>:tuple(a,b,?b) =
        defer:Print("outer")
        if(N:=Mode?):
            defer:Print("branch {N}")
            if(N=0):return (Anchor,X,false)|(Anchor,Y,option{Y})
            Print("fall")
        defer:Print("late")
        (Anchor,X,false)|(Anchor,Y,false)
All(C:box(t),X:u,Y:u,Mode:?int where t:type,u:type):[]tuple(t,u,?u) =
    for(V:=C.Pick(X,Y,Mode)):V
Main():void =
    for(Mode:array{option{0},option{1},false}):
        Print("case")
        for(V:All(box(int){Anchor:=7},"x","y",Mode)):
            Flag:=if(P:=V(2)?)then 1 else 0
            Print("value {V(0)} {V(1)} {Flag}")
