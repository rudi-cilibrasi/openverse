# Tuple calls preserve instantiated parameter types and call boundaries (#448).
meter := class { var N:int=0 }
Touch(H:meter,V:t where t:type)<transacts>:t =
    set H.N+=1
    Print("arg {H.N}")
    V
base(t:type) := class:
    Pick(X:t,Y:t,H:meter)<transacts>:int =
        Print("body {H.N}")
        1 | 2
mid(u:type) := class(base(u)):
    Pick<override>(X:u,Y:u,H:meter)<transacts>:int = (super:)Pick((Touch(H,X),Touch(H,Y),H))
Recv(H:meter,K:mid(int))<transacts>:mid(int) =
    set H.N+=1
    Print("recv {H.N}")
    K
Main()<transacts>:void =
    H:=meter{}
    K:=mid(int){}
    if(N:=Recv(H,K).Pick(3,4,H),N=2) then Print("win {N} {H.N}")
    if(N:=Recv(H,K).Pick(3,4,H),N=99) then Print("bad") else Print("none {H.N}")