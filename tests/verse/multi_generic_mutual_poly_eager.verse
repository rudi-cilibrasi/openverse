# Type-changing recursion keeps the previously accepted eager route.
A(X:t,N:int where t:type)<computes>:int =
    if(N>0)then(N|B(array{X},N-1))else 0
B(X:u,N:int where u:type)<computes>:int =
    if(N>0)then(N|A(array{X},N-1))else 0
Main():void =
    for(V:=A(7,2)): Print("{V}")
    if(V:=B("s",3),V=1)then Print("first {V}")
