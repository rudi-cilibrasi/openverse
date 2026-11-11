# The eager compatibility path still reaches errors after an earlier value.
A(X:t,N:int where t:type)<computes>:int =
    if(N>0)then(7|B(array{X},N-1))else 9223372036854775807+1
B(X:u,N:int where u:type)<computes>:int =
    if(N>0)then(7|A(array{X},N-1))else 9223372036854775807+1
Main():void =
    Print("start")
    if(V:=A(7,1))then Print("unexpected")
