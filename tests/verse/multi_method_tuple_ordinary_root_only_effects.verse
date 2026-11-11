# Tuple calls preserve instantiated parameter types and call boundaries (#448).
meter := class { var N:int=0 }
box(t:type) := class:
    Both(X:t,Y:t)<transacts>:t =
        Print("body")
        X | Y
hidden(v:type) := class<abstract>(box(v)):
    Both<override>(X:v,Y:v)<transacts>:v
Recv(H:meter,P:box(u) where u:type)<transacts>:box(u) =
    set H.N+=1
    Print("recv {H.N}")
    P
Touch(H:meter,V:u where u:type)<transacts>:u =
    set H.N+=1
    Print("arg {H.N}")
    V
Main()<transacts>:void =
    H:=meter{}
    P:=box(int){}
    for(V:=Recv(H,P).Both((Touch(H,3),Touch(H,4)))){Print("v {V}")}
    Print("end {H.N}")
    if(V:=Recv(H,P).Both((Touch(H,3),Touch(H,4))),V=99) then Print("bad") else Print("none {H.N}")
